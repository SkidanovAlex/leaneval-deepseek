import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.EllipticEst.Mine.SlotDefs
import Submission.Work.FTS.EllipticEst.Mine.FSlotsTwoD
import Submission.Work.FTS.EllipticEst.H2W.slot11_aux
import Submission.Work.Spaces.HkSq_terms

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.TT.Slot11

/-- **Integrability of `(∂_θ³(D_zΨ))² · sin(2θ)^{2-gam α}` on the angular slice.**

For `0 < α ≤ 1/4`, a datum `h : TT.EllWeakPos α 2 F Ψ` of the weak elliptic class and every
`z > 0`, the first `IntegrableOn` hypothesis of the PROVED one-dimensional Step-4 estimate
`Work.H2W.sliceStep4Uniform` holds at the shifted slice `u = θ ↦ D_zΨ(z,θ)`, i.e. the
`(i,j) = (1,1)` mixed slot of `HkMem α 2 (∂_θ²Ψ)` is honest after division by `w²`.

Route.  `H2W/slot11_aux.slot11_mixed_eq` (PROVED) gives, for `z > 0` and `θ ∈ Ioo 0 (π/2)`,
`mixed 1 1 (pthIter 2 Ψ) z θ = sin(2θ) · pthIter 3 (DzIter 1 Ψ) z θ`; with
`Wt² = w²·sin(2θ)^{-gam α}` (`Mine.FSlotsTwoD.Wt_sq`), the slot inequality
`(mixed 1 1 f · Wt)² ≤ HkIntegrand α 2 f` (`Spaces.sq_le_HkIntegrand_mixed`) becomes
`w²·(pthIter 3 (DzIter 1 Ψ))²·sin(2θ)^{2-gam α} ≤ HkIntegrand α 2 (pthIter 2 Ψ)` on the open
interval (the `rpow` algebra needs `sin(2θ) > 0`); dividing by `w² ≥ 1` gives the pointwise bound
`(pthIter 3 (DzIter 1 Ψ) z θ)²·sin(2θ)^{2-gam α} ≤ HkIntegrand α 2 (pthIter 2 Ψ) z θ`.
`Integrable.mono'` against `h.memB.1 z hz` (which gives `θ`-integrability of `HkIntegrand α 2
(pthIter 2 Ψ) z ·` for `z ∈ Iz`) closes the claim; the a.e. strong measurability of the left-hand
side is `measurable_deriv`-based (`pthIter` is a total `deriv`), and the pointwise bound is needed
only a.e. on `Iθ` (`Ioo 0 (π/2)` differs from `Iθ` by two points). -/
theorem shiftThirdInt (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.pthIter 3 (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (2 - Work.Spaces.gam α)) Work.Spaces.Iθ := by
  -- The angular slices of `Ψ` are `C^∞` on the open quadrant.
  have hSO : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  -- `HkIntegrand α 2 (∂_θ²Ψ) z ·` is `θ`-integrable on `Iθ` (`z ≥ 0`), the dominating function.
  have hmem : MeasureTheory.Integrable
      (fun θ => Work.Spaces.HkIntegrand α 2 (Work.Spaces.pthIter 2 Ψ) z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := h.memB.1 z (Set.mem_Ici.mpr hz.le)
  -- `w z ≥ 1`, hence `(w z)² ≥ 1`: this is what lets us divide the slot inequality by `w²`.
  have hwpos : 1 ≤ Work.Spaces.w z := by
    rw [Work.Spaces.w, le_div_iff₀ (by positivity : (0 : ℝ) < z ^ 2)]
    nlinarith [hz]
  have hw1 : 1 ≤ (Work.Spaces.w z) ^ 2 := by nlinarith [hwpos]
  -- Almost every point of `Iθ` is an interior point, where `sin (2θ) > 0`.
  have hae : ∀ᵐ θ ∂(MeasureTheory.volume : Measure ℝ).restrict Work.Spaces.Iθ,
      θ ∈ Set.Ioo 0 (Real.pi / 2) := by
    have h' : Set.Icc (0 : ℝ) (Real.pi / 2) =ᵐ[MeasureTheory.volume] Set.Ioo 0 (Real.pi / 2) :=
      (MeasureTheory.Ioo_ae_eq_Icc (μ := (MeasureTheory.volume : Measure ℝ))).symm
    have hIθ : Work.Spaces.Iθ = Set.Icc (0 : ℝ) (Real.pi / 2) := rfl
    rw [hIθ, MeasureTheory.Measure.restrict_congr_set h']
    exact MeasureTheory.ae_restrict_mem measurableSet_Ioo
  refine hmem.mono' ?_ ?_
  · -- a.e. strong measurability: `pthIter` is a total `deriv`, and the angular weight is measurable
    have h1 : Measurable
        (fun θ : ℝ => Work.Spaces.pthIter 3 (Work.Spaces.DzIter 1 Ψ) z θ) := by
      have heq : (fun θ : ℝ => Work.Spaces.pthIter 3 (Work.Spaces.DzIter 1 Ψ) z θ)
          = deriv (fun t : ℝ => Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ) z t) := by
        funext θ; rfl
      rw [heq]; exact measurable_deriv _
    have h2 : Measurable
        (fun θ : ℝ => Work.Spaces.pthIter 3 (Work.Spaces.DzIter 1 Ψ) z θ ^ 2) :=
      h1.pow_const (2 : ℕ)
    have h3 : Measurable
        (fun θ : ℝ => Real.rpow (Real.sin (2 * θ)) (2 - Work.Spaces.gam α)) := by
      have hs : Measurable (fun θ : ℝ => Real.sin (2 * θ)) :=
        Real.measurable_sin.comp (measurable_const.mul measurable_id)
      exact hs.pow_const (2 - Work.Spaces.gam α)
    exact (h2.mul h3).aestronglyMeasurable
  · -- the pointwise bound, only needed on the open interval
    filter_upwards [hae] with θ hθ
    have hs : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
    have hgnn : 0 ≤ (Work.Spaces.pthIter 3 (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (2 - Work.Spaces.gam α) :=
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs.le _)
    rw [Real.norm_eq_abs, abs_of_nonneg hgnn]
    -- the slot inequality, transported to the shifted slice
    have hsq := Work.FTS.EllipticEst.H2W.slot11_sq_eq (α := α) hSO z θ hz hθ.1 hθ.2
    have hle := Work.Spaces.sq_le_HkIntegrand_mixed α 2 (Work.Spaces.pthIter 2 Ψ) z θ 1 1
      (by norm_num) (by norm_num)
    have hb : (Work.Spaces.w z) ^ 2 * ((Work.Spaces.pthIter 3 (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (2 - Work.Spaces.gam α))
        ≤ Work.Spaces.HkIntegrand α 2 (Work.Spaces.pthIter 2 Ψ) z θ := by
      rw [← mul_assoc, ← hsq]
      exact hle
    calc (Work.Spaces.pthIter 3 (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (2 - Work.Spaces.gam α)
        = 1 * ((Work.Spaces.pthIter 3 (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2
            * Real.rpow (Real.sin (2 * θ)) (2 - Work.Spaces.gam α)) := by ring
      _ ≤ (Work.Spaces.w z) ^ 2 * ((Work.Spaces.pthIter 3 (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2
            * Real.rpow (Real.sin (2 * θ)) (2 - Work.Spaces.gam α)) :=
          mul_le_mul_of_nonneg_right hw1 hgnn
      _ ≤ Work.Spaces.HkIntegrand α 2 (Work.Spaces.pthIter 2 Ψ) z θ := hb

end Work.FTS.EllipticEst.TT.Slot11
