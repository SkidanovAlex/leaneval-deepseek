import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.PhiStar.Honesty.CptApp.EstDefs
import Submission.Work.FTS.PhiStar.Honesty.CptApp.EstAux.SmoothErr
import Submission.Work.FTS.EllipticEst.SmoothOpenAdd
import Submission.Work.FTS.OpenPkg.ProdOpen.leibniz_open_mixed
import Submission.Work.FTS.EllipticEst.DzIter_mul_of_radial
import Submission.Work.Coercivity.CommutZ_mult

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty.CptApp.Est.Pieces

set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped Real Topology
open Set Filter

/-! ## The multiplier `(χ n · ζ n − 1)` is smooth on the open quadrant -/

private theorem chiZeta_sub_one_smoothOpen (n : ℕ) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ =>
      Work.FTS.PhiStar.Honesty.CptApp.chiR n z
        * Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ - 1) := by
  refine (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mpr fun k => ?_
  have h1 : ContDiffOn ℝ k
      (fun p : ℝ × ℝ => Work.FTS.PhiStar.Honesty.CptApp.chiR n p.1)
      Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.PhiStar.Honesty.CptApp.contDiff_chiR n k).contDiffOn.comp contDiffOn_fst
      (fun p _ => Set.mem_univ p.1)
  have h2 : ContDiffOn ℝ k
      (fun p : ℝ × ℝ => Work.FTS.PhiStar.Honesty.CptApp.zetaR n p.2)
      Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.PhiStar.Honesty.CptApp.contDiff_zetaR n k).contDiffOn.comp contDiffOn_snd
      (fun p _ => Set.mem_univ p.2)
  exact (h1.mul h2).sub contDiffOn_const

/-! ## Oddness of the iterated operators (unconditional) -/

private theorem dz_neg_local (f : ℝ → ℝ → ℝ) :
    Work.Spaces.Dz (fun z θ => - f z θ) = fun z θ => - Work.Spaces.Dz f z θ := by
  funext z θ
  show z * deriv (fun z' => - f z' θ) z = - (z * deriv (fun z' => f z' θ) z)
  rw [show (fun z' => - f z' θ) = fun z' => (-1 : ℝ) * f z' θ from by funext z'; ring,
    deriv_const_mul_field]
  ring

private theorem dth_neg_local (f : ℝ → ℝ → ℝ) :
    Work.Spaces.Dth (fun z θ => - f z θ) = fun z θ => - Work.Spaces.Dth f z θ := by
  funext z θ
  show Real.sin (2 * θ) * deriv (fun θ' => - f z θ') θ
    = - (Real.sin (2 * θ) * deriv (fun θ' => f z θ') θ)
  rw [show (fun θ' => - f z θ') = fun θ' => (-1 : ℝ) * f z θ' from by funext θ'; ring,
    deriv_const_mul_field]
  ring

private theorem dzIter_neg_local (k : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.DzIter k (fun z θ => - f z θ)
      = fun z θ => - Work.Spaces.DzIter k f z θ := by
  induction k with
  | zero => rfl
  | succ n ih =>
      rw [Work.Spaces.DzIter_succ, ih, Work.Spaces.DzIter_succ, dz_neg_local]

private theorem dthIter_neg_local (k : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.DthIter k (fun z θ => - f z θ)
      = fun z θ => - Work.Spaces.DthIter k f z θ := by
  induction k with
  | zero => rfl
  | succ n ih =>
      rw [Work.Spaces.DthIter_succ, ih, Work.Spaces.DthIter_succ, dth_neg_local]

private theorem mixed_neg_local (j i : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.mixed j i (fun z θ => - f z θ)
      = fun z θ => - Work.Spaces.mixed j i f z θ := by
  simp only [Work.Spaces.mixed]
  rw [dthIter_neg_local, dzIter_neg_local]

private theorem mixed_neg_apply (j i : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.mixed j i (fun z θ => - f z θ) z θ
      = - Work.Spaces.mixed j i f z θ := by
  have h := congrFun (congrFun (mixed_neg_local j i f) z) θ
  simpa using h

/-! ## A function of `θ` alone has `D_θ`-iterates independent of `z` -/

private theorem DthIter_z_indep (i : ℕ) (u : ℝ → ℝ) :
    ∀ z θ, Work.Spaces.DthIter i (fun _ (θ' : ℝ) => u θ') z θ
      = Work.Spaces.DthIter i (fun _ (θ' : ℝ) => u θ') 0 θ := by
  induction i with
  | zero => intro z θ; rfl
  | succ i ih =>
      intro z θ
      simp only [Work.Spaces.DthIter_succ, Work.Spaces.Dth, Work.Spaces.pth]
      have hfun : (fun θ' => Work.Spaces.DthIter i (fun _ (θ' : ℝ) => u θ') z θ')
          = (fun θ' => Work.Spaces.DthIter i (fun _ (θ' : ℝ) => u θ') 0 θ') :=
        funext fun θ' => ih z θ'
      rw [hfun]

/-! ## `rDzIter` is the iterate of `Zop` -/

private theorem rDzIter_eq_iterate (j : ℕ) (m : ℝ → ℝ) :
    Work.FTS.EllipticEst.rDzIter j m = Work.Spaces.Zop^[j] m := by
  induction j with
  | zero => rfl
  | succ n ih =>
      rw [Work.FTS.EllipticEst.rDzIter_succ, ih, Function.iterate_succ_apply']
      rfl

/-! ## The separated (radial × angular) product -/

private theorem mixed_sep (j i : ℕ) (m u : ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.mixed j i (fun z θ => m z * u θ) z θ
      = Work.Spaces.DzIter j (fun z _ : ℝ => m z) z 0
        * Work.Spaces.DthIter i (fun _ (θ' : ℝ) => u θ') 0 θ := by
  have hcomm : Work.Spaces.DthIter i (fun z θ => m z * u θ)
      = fun z θ => m z * (Work.Spaces.DthIter i (fun _ (θ' : ℝ) => u θ') 0 θ) := by
    have h := Work.Coercivity.DthIter_mulZm i m (fun _ (θ' : ℝ) => u θ')
    rw [h]
    funext z θ
    rw [DthIter_z_indep i u z θ]
  have hslice := congrFun (Work.Spaces.Zop_slice j (fun z _ : ℝ => m z) 0) z
  rw [Work.Spaces.mixed, hcomm,
    Work.FTS.EllipticEst.DzIter_mul_of_radial j m
      (fun θ' => Work.Spaces.DthIter i (fun _ (θ' : ℝ) => u θ') 0 θ') z θ,
    rDzIter_eq_iterate j m, hslice]

/-! ## The expansion of the error -/

theorem err_expansion (n : ℕ) (hn : 2 ≤ n) {F : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (j i : ℕ) (z θ : ℝ)
    (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    Work.Spaces.mixed j i (Work.FTS.PhiStar.Honesty.CptApp.err n F) z θ
      = (∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
            ((i.choose a : ℝ) * (j.choose b : ℝ))
              * (Work.Spaces.mixed b a
                    (fun z θ => Work.FTS.PhiStar.Honesty.CptApp.chiR n z
                      * Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ - 1) z θ
                 * Work.Spaces.mixed (j - b) (i - a) F z θ))
        - Work.Spaces.DzIter j
            (fun z _ : ℝ => Work.FTS.PhiStar.Honesty.CptApp.mu n F z) z 0
          * Work.Spaces.DthIter i
            (fun _ θ : ℝ => Work.FTS.PhiStar.Honesty.CptApp.rho θ) 0 θ := by
  have hn1 : 1 ≤ n := by omega
  -- the pointwise decomposition of the error
  have herr : Work.FTS.PhiStar.Honesty.CptApp.err n F
      = fun z θ =>
          (Work.FTS.PhiStar.Honesty.CptApp.chiR n z
              * Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ - 1) * F z θ
            + -(Work.FTS.PhiStar.Honesty.CptApp.mu n F z
                * Work.FTS.PhiStar.Honesty.CptApp.rho θ) := by
    funext z' θ'
    rw [Work.FTS.PhiStar.Honesty.CptApp.err, Work.FTS.PhiStar.Honesty.CptApp.approx,
      Work.FTS.PhiStar.Honesty.CptApp.mu]
    ring
  have hA : Work.FTS.EllipticEst.SmoothOpen (fun z θ =>
      (Work.FTS.PhiStar.Honesty.CptApp.chiR n z
          * Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ - 1) * F z θ) :=
    Work.FTS.PhiStar.Honesty.CptApp.EstAux.smoothOpen_chiZeta_sub_one hF n
  have hB : Work.FTS.EllipticEst.SmoothOpen (fun z θ =>
      -(Work.FTS.PhiStar.Honesty.CptApp.mu n F z
        * Work.FTS.PhiStar.Honesty.CptApp.rho θ)) :=
    (Work.FTS.PhiStar.Honesty.CptApp.EstAux.smoothOpen_muRho hF hn1).neg
  rw [herr, Work.FTS.EllipticEst.SmoothOpen.mixed_add hA hB j i z θ hz hθ0 hθ1,
    mixed_neg_apply j i (fun z θ => Work.FTS.PhiStar.Honesty.CptApp.mu n F z
      * Work.FTS.PhiStar.Honesty.CptApp.rho θ) z θ,
    Work.FTS.OpenPkg.ProdOpen.leibniz_open_mixed j i
      (fun z θ => Work.FTS.PhiStar.Honesty.CptApp.chiR n z
        * Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ - 1) F
      (chiZeta_sub_one_smoothOpen n) hF z θ hz hθ0 hθ1,
    mixed_sep j i (fun z => Work.FTS.PhiStar.Honesty.CptApp.mu n F z)
      Work.FTS.PhiStar.Honesty.CptApp.rho z θ]
  ring

end Work.FTS.PhiStar.Honesty.CptApp.Est.Pieces
