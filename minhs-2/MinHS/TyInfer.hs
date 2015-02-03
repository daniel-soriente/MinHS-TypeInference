

module MinHS.TyInfer where

import qualified MinHS.Env as E
import MinHS.Syntax
import MinHS.Subst
import MinHS.TCMonad

import Data.Monoid (Monoid (..), (<>))
import Data.Foldable (foldMap)
import Data.List (nub, union, (\\))

primOpType :: Op -> QType
primOpType Gt   = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Ge   = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Lt   = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Le   = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Eq   = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Ne   = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Neg  = Ty $ Base Int `Arrow` Base Int
primOpType Fst  = Forall "a" $ Forall "b" $ Ty $ (TypeVar "a" `Prod` TypeVar "b") `Arrow` TypeVar "a"
primOpType Snd  = Forall "a" $ Forall "b" $ Ty $ (TypeVar "a" `Prod` TypeVar "b") `Arrow` TypeVar "b"
primOpType _    = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Int)

constType :: Id -> Maybe QType
constType "True"  = Just $ Ty $ Base Bool
constType "False" = Just $ Ty $ Base Bool
constType "()"    = Just $ Ty $ Base Unit
constType "Pair"  = Just
                  $ Forall "a"
                  $ Forall "b"
                  $ Ty
                  $ TypeVar "a" `Arrow` (TypeVar "b" `Arrow` (TypeVar "a" `Prod` TypeVar "b"))
constType "Inl"   = Just
                  $ Forall "a"
                  $ Forall "b"
                  $ Ty
                  $ TypeVar "a" `Arrow` (TypeVar "a" `Sum` TypeVar "b")
constType "Inr"   = Just
                  $ Forall "a"
                  $ Forall "b"
                  $ Ty
                  $ TypeVar "b" `Arrow` (TypeVar "a" `Sum` TypeVar "b")
constType _       = Nothing

type Gamma = E.Env QType

initialGamma :: Gamma
initialGamma = E.empty

tv :: Type -> [Id]
tv = tv'
 where
   tv' (TypeVar x) = [x]
   tv' (Prod  a b) = tv a `union` tv b
   tv' (Sum   a b) = tv a `union` tv b
   tv' (Arrow a b) = tv a `union` tv b
   tv' (Base c   ) = []

tvQ :: QType -> [Id]
tvQ (Forall x t) = filter (/= x) $ tvQ t
tvQ (Ty t) = tv t

tvGamma :: Gamma -> [Id]
tvGamma = nub . foldMap tvQ

infer :: Program -> Either TypeError Program
infer program = do (p',tau, s) <- runTC $ inferProgram initialGamma program
                   return p'

unquantify :: QType -> TC Type
{-
Normally this implementation would be possible:

unquantify (Ty t) = return t
unquantify (Forall x t) = do x' <- fresh
                             unquantify (substQType (x =:x') t)

However as our "fresh" names are not checked for collisions with names bound in the type
we avoid capture entirely by first replacing each bound
variable with a guaranteed non-colliding variable with a numeric name,
and then substituting those numeric names for our normal fresh variables
-}

unquantify = unquantify' 0 emptySubst
unquantify' :: Int -> Subst -> QType -> TC Type
unquantify' i s (Ty t) = return $ substitute s t
unquantify' i s (Forall x t) = do x' <- fresh
                                  unquantify' (i + 1)
                                              ((show i =: x') <> s)
                                              (substQType (x =:TypeVar (show i)) t)

unify :: Type -> Type -> TC Subst
unify t1@(TypeVar v1) t2@(TypeVar v2) | v1 == v2  = return emptySubst
                                      | otherwise =  return $ v1 =: t2
unify t1@(Base b1) t2@(Base b2) | b1 == b2  = return emptySubst
                                | otherwise = typeError $ TypeMismatch t1 t2
unify (Prod  t11 t12) (Prod  t21 t22) = unify' t11 t12 t21 t22
unify (Arrow t11 t12) (Arrow t21 t22) = unify' t11 t12 t21 t22
unify (Sum   t11 t12) (Sum   t21 t22) = unify' t11 t12 t21 t22
unify (TypeVar v1) t2 | v1 `elem` tv t2 = typeError $ OccursCheckFailed v1 t2
                      | otherwise       = return $ v1 =: t2
unify t2 t1@(TypeVar v1) = unify t1 t2
unify t1 t2 = typeError $ TypeMismatch t1 t2

--Saves space on typing it out again
unify' :: Type -> Type -> Type -> Type -> TC Subst
unify' t11 t12 t21 t22 = t11 `unify` t21 >>= \u1 ->
                         (substitute u1 t12) `unify` (substitute u1 t22) >>= \u2 ->
                         return $ u1 `mappend` u2

generalise :: Gamma -> Type -> QType
generalise g t = case (tv t) \\ (tvGamma g) of (x:xs) -> generalise' (x:xs) t
                                                  where
                                                       generalise' :: [Id] -> Type -> QType
                                                       generalise' []     t = Ty t
                                                       generalise' (x:xs) t = Forall x $ generalise' xs t
                                               [] -> Ty t

inferProgram :: Gamma -> Program -> TC (Program, Type, Subst)
inferProgram env ([Bind main typ args e]) = inferExp env e >>= \(e', t, s) ->
                                            return ([allTypesBind (substQType s) (Bind main (Just (generalise env t)) args e')], t, s)
inferProgram env bs = error "implement me! don't forget to run the result substitution on the"
                            "entire expression using allTypes from Syntax.hs"

inferExp :: Gamma -> Exp -> TC (Exp, Type, Subst)
inferExp g e@(Var id) = case E.lookup g id of Just qt -> unquantify qt >>= \t ->
                                                         return (e, t, emptySubst)
                                              Nothing -> typeError $ NoSuchVariable id
inferExp g e@(Prim op) = unquantify (primOpType op) >>= \t ->
                         return (e, t, emptySubst)
inferExp g e@(Con id) = case constType id of Just qt -> unquantify qt >>= \t ->
                                                        return (e, t, emptySubst)
                                             Nothing -> typeError $ NoSuchConstructor id
inferExp g e@(Num int) = return (e, Base Int, emptySubst)
inferExp g (App e1 e2) = inferExp g e1 >>= \(e1', t1, s) ->
                         inferExp (s `substGamma` g) e2 >>= \(e2', t2, s') ->
                         fresh >>= \a ->
                         unify (substitute s' t1) (Arrow t2 a) >>= \u ->
                         return (App e1' e2', substitute u a, u `mappend` s' `mappend` s)
inferExp g (If e e1 e2) = inferExp g e >>= \(e', t, s) ->
                          unify t (Base Bool) >>= \u ->
                          inferExp (u `mappend` s `substGamma` g) e1 >>= \(e1', t1, s1) ->
                          inferExp (s1 `mappend` u `mappend` s `substGamma` g) e2 >>= \(e2', t2, s2) ->
                          unify (substitute s2 t1) t2 >>= \u' ->
                          return (If e' e1' e2', substitute u' t2, u' `mappend` s2 `mappend` s1 `mappend` u `mappend` s)
inferExp g (Let [Bind x typ ids e1] e2) = inferExp g e1 >>= \(e1', t, s) ->
                                          let 
                                             g' = s `substGamma` E.add g (x, generalise (s `substGamma` g) t)
                                          in
                                            inferExp g' e2 >>= \(e2', t', s') ->
                                            return (Let [Bind x (Just (generalise g' t)) ids e1'] e2', t', s' `mappend` s)
inferExp g (Let binds e2) = inferBinds g binds >>= \(g', s, binds') ->
                            inferExp g' e2 >>= \(e2', t', s') ->
                            return (Let binds' e2', t', s' `mappend` s)
inferExp g (Letfun (Bind f typ args e)) = bindTVFresh args >>= \l ->
                                          fresh >>= \a1 ->
                                          inferExp (E.addAll g ([(f, Ty a1)] ++ l)) e >>= \(e', t, s) ->
                                          funcTyp s t l >>= \p ->
                                          unify (substitute s a1) p >>= \u ->
                                          let
                                             t' = substitute u p
                                          in 
                                             return (Letfun (Bind f (Just (Ty t')) args e'), t', u `mappend` s)
inferExp g (Case e [Alt "Inl" [x] e1, Alt "Inr" [y] e2]) = 
   inferExp g e >>= \(e', t, s) ->
   fresh >>= \al ->
   inferExp (s `substGamma` (E.add g (x, Ty al))) e1 >>= \(e1', tl, s1) ->
   fresh >>= \ar ->
   inferExp (s1 `mappend` s `substGamma` (E.add g (y, Ty ar))) e2 >>= \(e2', tr, s2) ->
   unify (substitute (s2 `mappend` s1 `mappend` s) (Sum al ar)) (substitute (s2 `mappend` s1) t) >>= \u ->
   unify (substitute (u `mappend` s2) tl) (substitute u tr) >>= \u' ->
   let
      exp = Case e' [Alt "Inl" [x] e1', Alt "Inr" [y] e2']
      t'  = substitute (u' `mappend` u) tr
      s'  = u' `mappend` u `mappend` s2 `mappend` s1 `mappend` s
   in
     return (exp, t', s')
inferExp g (Case e _) = typeError MalformedAlternatives
inferExp g e = error $ "Implement me! " ++ (show e)
-- -- Note: this is the only case you need to handle for case expressions
-- inferExp g (Case e [Alt "Inl" [x] e1, Alt "Inr" [y] e2])
-- inferExp g (Case e _) = typeError MalformedAlternatives

--Handles multiple let binds
--Infer the type of each binding
inferBinds :: Gamma -> [Bind] -> TC (Gamma, Subst, [Bind])
inferBinds g [] = return (g, emptySubst, [])
inferBinds g ((Bind x typ ids e1):bs) = inferExp g e1 >>= \(e1', t, s) ->
                                        inferBinds (s `substGamma` E.add g (x, generalise (s `substGamma` g) t)) bs >>= \(g', s', bs') ->
                                        return (g', s' `mappend` s, [Bind x (Just (generalise g' t)) ids e1'] ++ bs')

--Used for functions that taken in parameters
--Binds tv to fresh type
--Does Γ ∪ {x : α 1 } of letfun rule
bindTVFresh :: [Id] -> TC [(Id, QType)]
bindTVFresh [] = return []
bindTVFresh (x:xs) = fresh >>= \f ->
                     bindTVFresh xs >>= \cons ->
                     return $ [(x, Ty f)] ++ cons

--Creates type of function
--Creates Tα1 -> τ of letfun rule
funcTyp :: Subst -> Type -> [(Id, QType)] -> TC Type
funcTyp s t [] = return t
funcTyp s t ((x, qt):xs) = unquantify qt >>= \t' ->
                           funcTyp s t xs >>= \cons ->
                           return (Arrow (substitute s t') cons) 
