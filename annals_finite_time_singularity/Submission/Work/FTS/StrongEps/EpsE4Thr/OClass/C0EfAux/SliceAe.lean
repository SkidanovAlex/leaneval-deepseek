/-
# Angular slices of an open-quadrant datum: a.e. strong measurability and integrability

The radial integration of the `C₀`-coercivity estimate (`C0_sq_le_Ef_O`) needs two facts about
the angular slices `θ ↦ f z θ` of a datum `f` of the *open-quadrant* class
`Work.FTS.EllipticEst.SmoothOpen` (C^∞ on `(0,∞) × (0,π/2)`):

* they are a.e. strongly measurable for `volume.restrict Iθ` — continuity on the open interval
  `(0,π/2)` suffices, since its two endpoints are null (`aesm_slice_theta_O`);
* they are a.e. (in `z`) integrable, which follows from the `IntPkgO` integrability certificates
  (`f² · w² sin^{-η}` and `(D_θf)² · w² sin^{-γ}` integrable over the product) together with the
  elementary bound `1 ≤ sin^{-η}` / `1 ≤ sin^{-γ}` on the open interval
  (`ae_integrableOn_slice_f_O`, `ae_integrableOn_slice_Dth_O`).

These are the open-class analogues of `Work.FTS.CoercivityFix.Coer1T.aesm_slice_theta_Q`,
`…ae_integrableOn_slice_f` and `…ae_integrableOn_slice_Dth` (which are stated for the frozen
class `SmoothQuad`).

Everything here is `sorry`-free.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongEps.EpsE4Thr.OpenClass
import Submission.Work.FTS.StrongEps.EpsE4Thr.IntPkgO
import Submission.Work.FTS.CoercivityFix.Coer1T.slotDz_LGammaT

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.OClass.C0EfAux

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## The angular slice of a `SmoothOpen` datum -/

/-- The angular slice of a `SmoothOpen` datum is a.e. strongly measurable: it is continuous on
the open interval `(0, π/2)`, which is conull in `Iθ`.  (The open-class analogue of
`Work.FTS.CoercivityFix.Coer1T.aesm_slice_theta_Q`.) -/
theorem aesm_slice_theta_O {g : Fn} (hso : Work.FTS.EllipticEst.SmoothOpen g) {s : ℝ}
    (hs : 0 < s) :
    MeasureTheory.AEStronglyMeasurable (fun θ => g s θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
  Work.Spaces.aesm_slice_of_continuousOn_Qd (fun p : ℝ × ℝ => g p.1 p.2) hso.continuousOn hs

/-- A.e. in `z`, the angular slice `θ ↦ f z θ` is integrable, for open-class data satisfying the
`IntPkgO` integrability certificate.  (The open-class analogue of
`Work.FTS.CoercivityFix.Coer1T.ae_integrableOn_slice_f`.) -/
theorem ae_integrableOn_slice_f_O (α : ℝ) {f : Fn}
    (hso : Work.FTS.EllipticEst.SmoothOpen f)
    (hIP : Work.FTS.StrongEps.EpsE4Thr.IntPkgO α f) :
    ∀ᵐ s ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.IntegrableOn (fun θ => f s θ) Work.Spaces.Iθ := by
  have hP0 : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      f p.1 p.2 ^ 2 * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [Work.FTS.CoercivityFix.Coer1.iz_prod_restrict]
    exact hIP.sqDzEta 0 (by norm_num)
  filter_upwards [hP0.prod_right_ae, Work.FTS.CoercivityFix.Coer1.ae_restrict_Iz_pos]
    with s hs hspos
  have hRho : (fun θ => f s θ ^ 2 * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta s θ)
      = fun θ => Work.Spaces.w s ^ 2
          * (f s θ ^ 2 * Work.FTS.CoercivityFix.Coer1.sig Work.Spaces.eta θ) := by
    funext θ
    simp only [Work.FTS.CoercivityFix.Coer1.Rho]
    ring
  rw [hRho] at hs
  have hwpos : (0 : ℝ) < Work.Spaces.w s := by rw [Work.Spaces.w]; positivity
  have hwne : Work.Spaces.w s ^ 2 ≠ 0 := by positivity
  have hs2 : MeasureTheory.Integrable
      (fun θ => f s θ ^ 2 * Work.FTS.CoercivityFix.Coer1.sig Work.Spaces.eta θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    (MeasureTheory.integrable_const_mul_iff (isUnit_iff_ne_zero.mpr hwne) _).mp hs
  have hs3 : MeasureTheory.Integrable (fun θ => f s θ ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    refine MeasureTheory.Integrable.mono' hs2
      ((aesm_slice_theta_O hso hspos).pow 2) ?_
    filter_upwards [Work.FTS.CoercivityFix.Coer1.ae_restrict_Iθ_mem_Ioo] with θ hθ
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h1 : 1 ≤ Work.FTS.CoercivityFix.Coer1.sig Work.Spaces.eta θ :=
      Work.FTS.CoercivityFix.Coer1.one_le_sig_eta hθ
    nlinarith [sq_nonneg (f s θ)]
  have h4 : MeasureTheory.Integrable (fun θ => (1 : ℝ) / 2 + (1 / 2) * f s θ ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    (MeasureTheory.integrable_const _).add (hs3.const_mul (1 / 2))
  refine h4.mono' (aesm_slice_theta_O hso hspos) ?_
  filter_upwards with θ
  rw [Real.norm_eq_abs]
  nlinarith [sq_nonneg (|f s θ| - 1), sq_abs (f s θ)]

/-- A.e. in `z`, the angular slice `θ ↦ D_θ f z θ` is integrable, for open-class data satisfying
the `IntPkgO` integrability certificate.  (The open-class analogue of
`Work.FTS.CoercivityFix.Coer1T.ae_integrableOn_slice_Dth`.) -/
theorem ae_integrableOn_slice_Dth_O (α : ℝ) (hα : 0 < α) {f : Fn}
    (hso : Work.FTS.EllipticEst.SmoothOpen f)
    (hIP : Work.FTS.StrongEps.EpsE4Thr.IntPkgO α f) :
    ∀ᵐ s ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.IntegrableOn (fun θ => Work.Spaces.Dth f s θ) Work.Spaces.Iθ := by
  have hP2 : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      Work.Spaces.Dth f p.1 p.2 ^ 2 * Work.FTS.CoercivityFix.Coer1.Rho
        (Work.Spaces.gam α) p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [Work.FTS.CoercivityFix.Coer1.iz_prod_restrict]
    refine (hIP.sqMixedGam 1 0 (by norm_num) (by norm_num)).congr ?_
    filter_upwards [MeasureTheory.ae_restrict_mem
      (measurableSet_Ici.prod measurableSet_Icc)] with p hp'
    rcases p with ⟨z, θ⟩
    simp only [Function.uncurry_apply_pair, Work.Spaces.mixed, Work.Spaces.DzIter_zero,
      Work.Spaces.DthIter_succ, Work.Spaces.DthIter_zero]
  filter_upwards [hP2.prod_right_ae, Work.FTS.CoercivityFix.Coer1.ae_restrict_Iz_pos]
    with s hs hspos
  have hRho : (fun θ => Work.Spaces.Dth f s θ ^ 2
        * Work.FTS.CoercivityFix.Coer1.Rho (Work.Spaces.gam α) s θ)
      = fun θ => Work.Spaces.w s ^ 2
          * (Work.Spaces.Dth f s θ ^ 2 * Work.FTS.CoercivityFix.Coer1.sig
              (Work.Spaces.gam α) θ) := by
    funext θ
    simp only [Work.FTS.CoercivityFix.Coer1.Rho]
    ring
  rw [hRho] at hs
  have hwpos : (0 : ℝ) < Work.Spaces.w s := by rw [Work.Spaces.w]; positivity
  have hwne : Work.Spaces.w s ^ 2 ≠ 0 := by positivity
  have hs2 : MeasureTheory.Integrable
      (fun θ => Work.Spaces.Dth f s θ ^ 2 * Work.FTS.CoercivityFix.Coer1.sig
        (Work.Spaces.gam α) θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    (MeasureTheory.integrable_const_mul_iff (isUnit_iff_ne_zero.mpr hwne) _).mp hs
  have hs3 : MeasureTheory.Integrable (fun θ => Work.Spaces.Dth f s θ ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    refine MeasureTheory.Integrable.mono' hs2
      ((aesm_slice_theta_O hso.Dth hspos).pow 2) ?_
    filter_upwards [Work.FTS.CoercivityFix.Coer1.ae_restrict_Iθ_mem_Ioo] with θ hθ
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hγ : 0 ≤ Work.Spaces.gam α := by rw [Work.Spaces.gam]; positivity
    have hsin1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
    have hsin0 : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
    have hs1 : 1 ≤ Work.FTS.CoercivityFix.Coer1.sig (Work.Spaces.gam α) θ := by
      have h1 := Real.rpow_le_rpow_of_exponent_ge hsin0 hsin1
        (show -(Work.Spaces.gam α) ≤ -(0 : ℝ) by linarith [hγ])
      rw [neg_zero, Real.rpow_zero] at h1
      simpa only [Work.FTS.CoercivityFix.Coer1.sig] using h1
    nlinarith [sq_nonneg (Work.Spaces.Dth f s θ)]
  have h4 : MeasureTheory.Integrable
      (fun θ => (1 : ℝ) / 2 + (1 / 2) * Work.Spaces.Dth f s θ ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    (MeasureTheory.integrable_const _).add (hs3.const_mul (1 / 2))
  refine h4.mono' (aesm_slice_theta_O hso.Dth hspos) ?_
  filter_upwards with θ
  rw [Real.norm_eq_abs]
  nlinarith [sq_nonneg (|Work.Spaces.Dth f s θ| - 1), sq_abs (Work.Spaces.Dth f s θ)]

end Work.FTS.StrongEps.EpsE4Thr.OClass.C0EfAux
