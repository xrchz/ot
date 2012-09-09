-- |Derived inference rules.
module OpenTheory.Rule (trans,sym,spec,proveHyp,subs) where
import Data.Map (singleton,empty)
import OpenTheory.Type (alpha_nm)
import OpenTheory.Term (Term(AppTerm),rator,rand,typeOf)
import OpenTheory.Equality (rhs)
import OpenTheory.Proof (Proof(..),axiom,concl)
import OpenTheory.Bool (true,forall_def)

-- |Substitute for an operand on the right hand side of an equation.
-- Assumes @x@ is the @n@th operand of @r@.
subs
  :: Int    -- ^ n
  -> Proof  -- ^ x = y
  -> Proof  -- ^ H |- l = r[x]
  -> Proof  -- ^ H |- l = r[y]
subs n eq th = trans th (build n (rhs (concl th))) where
  build 0 _ = eq
  build m (AppTerm f x) = AppThm (Refl f) (build (m-1) x)
  build _ _ = error "subs"

-- |Transitivity of equality.
trans
  :: Proof -- ^ H1 |- x = y
  -> Proof -- ^ H2 |- y = z
  -> Proof -- ^ H1 u H2 |- x = z
trans th1 th2 = EqMp (AppThm (Refl t) th2) th1
  where t = rator (concl th1)

-- |Symmetry of equality.
sym
  :: Proof -- ^ H |- x = y
  -> Proof -- ^ H |- y = x
sym th = EqMp lel_rel lel
  where
    lel_rel = AppThm le_re lel
    lel = Refl l
    le_re = AppThm (Refl e) ler
    AppTerm (AppTerm e l) _ = concl th
    ler = th

-- |Specialise a universally quantified theorem.
spec
  :: Term  -- ^ t
  -> Proof -- ^ H |- !x. P[x]
  -> Proof -- ^ H |- P[t]
spec tm th = EqMp (sym pv_T) (axiom true)
  where
    pv_T = trans pv_lxPxv (trans lxPxv_lxTv lxTv_T)
    pv_lxPxv = sym (BetaConv lxPxv) -- P[v] = (\x. P[x]) v
    lxTv_T = BetaConv lxTv -- (\x. T) v = T
    AppTerm (AppTerm _ lxPxv) lxTv = concl lxPxv_lxTv
    lxPxv_lxTv = AppThm lxPx_lxT (Refl v) -- (\x. P[x]) v = (\x. T) v
    lxPx_lxT = EqMp bc lPP_lxTlxPx    -- (\x. P[x]) = (\x. T)
    bc = BetaConv (concl lPP_lxTlxPx) -- (\P. P = (\x. T)) (\x. P[x]) = (\x. P[x]) = (\x. T)
    lPP_lxTlxPx = EqMp faxPx_ fa_lxPx -- (\P. P = (\x. T)) (\x. P[x])
    faxPx_ = (AppThm fa_lPP_lxT (Refl lxPx)) -- (!x. P[x]) = (\P. P = (\x. T)) (\x. P[x])
    lxPx = rand (concl th)            -- (\x. P[x])
    fa_lPP_lxT = Subst (singleton alpha_nm ty,empty) forall_def  -- (!) = (\P. P = (\x. T))
    fa_lxPx = th                      -- !x. P[x]
    ty = typeOf v
    v = tm

-- |Remove a hypothesis.
proveHyp
  :: Proof -- ^ H1 |- P
  -> Proof -- ^ H2 |- Q
  -> Proof -- ^ H1 u (H2 / {P}) |- Q
proveHyp h th = EqMp (DeductAntisym h th) h
