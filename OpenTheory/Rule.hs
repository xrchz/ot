module OpenTheory.Rule (trans,sym,spec,proveHyp,subs) where
import Data.Map (singleton,empty)
import OpenTheory.Type (alpha_nm)
import OpenTheory.Term (Term(AppTerm),rator,rand,typeOf)
import OpenTheory.Equality (rhs)
import OpenTheory.Proof (Proof(..),axiom,concl)
import OpenTheory.Bool (truth,forall_def)

-- subs n (x = y) (|- l = r[x]) = |- l = r[y]
-- assumes x is the nth operand of r
subs n eq th = trans th (build n (rhs (concl th))) where
  build 0 _ = eq
  build n (AppTerm f x) = AppThm (Refl f) (build (n-1) x)
  build _ _ = error "subs"

trans th1 th2 = EqMp (AppThm (Refl t) th2) th1
  where t = rator (concl th1)

sym th = EqMp lel_rel lel
  where
    lel_rel = AppThm le_re lel
    lel = Refl l
    le_re = AppThm (Refl e) ler
    AppTerm (AppTerm e l) _ = concl th
    ler = th

spec tm th = EqMp (sym pv_T) (axiom truth)
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

proveHyp h th = EqMp (DeductAntisym h th) h
