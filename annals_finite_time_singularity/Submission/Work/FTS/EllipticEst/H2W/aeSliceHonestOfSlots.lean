import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.H2W.pzIterBoxIntegrable
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.H2W.PropH2Base
import Submission.Work.FTS.EllipticEst.Honest.slice_bdd_of_sq_mul_sEta
import Submission.Work.FTS.EllipticEst.mul_w_sin_rpow_sq
import Submission.Work.FTS.EllipticEst.abs_mul_sinCos2_le_weighted

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `H2W.aeSliceHonestOfSlots`

For a datum `(F, Ψ)` of the weak class `Work.FTS.EllipticEst.WeakPos2 α F Ψ` (`0 < α ≤ 1/4`)
whose *slots* are honest — the second angular derivative of each of the slices
`Ψ, ∂_zΨ, ∂_z²Ψ` is `ℋ⁰`-honest (`hθ`), and so is `z²∂_z³Ψ` (`hr`) — almost every angular
slice `θ ↦ ∂_z^jΨ(z,θ)`, `j ≤ 3`, is integrable against `sinθcos²θ` on `Iθ = [0,π/2]`.

The proof works *for every* `z > 0` (the first conjunct of `Work.Spaces.HkMem` holds at every
`z ∈ Iz`), so the almost-everywhere statement is immediate.

* `j ≤ 2`: `HkMem α 0 (∂_θ²(∂_z^jΨ))` gives, on each slice, the integrability of
  `(∂_θ²u)²σ` (`σ = sin(2θ)^{-η}`), since the radial weight is a nonzero constant in `θ`.
  The one-variable theorem `Honest.slice_bdd_of_sq_mul_sEta` then bounds the slice `u` on
  the open interval, and a bounded function is `sinθcos²θ`-integrable there.
* `j = 3`: `hr` gives the `σ`-square-integrability of the slice itself, and
  `abs_mul_sinCos2_le_weighted` absorbs `|u·sinθcos²θ|` into the weighted square
  `(u·w(z)/sin(2θ)^{η/2})² + 1`.
-/

namespace Work.FTS.EllipticEst.H2W

open scoped Real Topology
open MeasureTheory Set Filter

/-! ## Elementary facts about the angular profile `sinθcos²θ` -/

private theorem aeh_sinCos2_zero_left : Work.Elliptic.sinCos2 0 = 0 := by
  simp [Work.Elliptic.sinCos2]

private theorem aeh_sinCos2_zero_right : Work.Elliptic.sinCos2 (Real.pi / 2) = 0 := by
  simp [Work.Elliptic.sinCos2, Real.cos_pi_div_two]

private theorem aeh_continuous_sinCos2 : Continuous Work.Elliptic.sinCos2 := by
  unfold Work.Elliptic.sinCos2
  fun_prop

private theorem aeh_volume_Iθ_lt_top : (volume : Measure ℝ) Work.Spaces.Iθ < ⊤ := by
  rw [Work.Spaces.Iθ, Real.volume_Icc]
  exact ENNReal.ofReal_lt_top

/-! ## The level-`0` integrand, and the `σ`-weighted square of a slice -/

/-- At level `0` the `HkIntegrand` is the single weighted square `(g · w/sin^{η/2})²`. -/
private theorem aeh_HkIntegrand_zero (α : ℝ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 g z θ
      = (g z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  simp [Work.Spaces.HkIntegrand]

/-- `HkMem α 0 g` gives the slicewise `σ`-weighted square-integrability `∫_θ g²σ < ∞` at every
`z > 0` (the square of the radial weight is a nonzero constant in `θ`). -/
private theorem aeh_sq_mul_sEta_of_HkMem {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hm : Work.Spaces.HkMem α 0 g) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => (g z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ := by
  have h1 : MeasureTheory.IntegrableOn (fun θ : ℝ => Work.Spaces.HkIntegrand α 0 g z θ)
      Work.Spaces.Iθ := hm.1 z (le_of_lt hz)
  have h2 : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (g z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ :=
    h1.congr_fun (fun θ hθ => by
      show Work.Spaces.HkIntegrand α 0 g z θ
        = (g z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ
      rw [aeh_HkIntegrand_zero]
      exact Work.FTS.EllipticEst.mul_w_sin_rpow_sq (g z θ) (Work.Spaces.w z) hθ)
      measurableSet_Icc
  have hw : Work.Spaces.w z ≠ 0 := by
    rw [Work.Spaces.w]
    exact div_ne_zero (pow_ne_zero _ (by linarith)) (pow_ne_zero _ (ne_of_gt hz))
  have hw2 : (Work.Spaces.w z) ^ 2 ≠ 0 := pow_ne_zero _ hw
  have h3 : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (g z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ
        * ((Work.Spaces.w z) ^ 2)⁻¹) Work.Spaces.Iθ :=
    h2.mul_const ((Work.Spaces.w z) ^ 2)⁻¹
  exact h3.congr_fun (fun θ _ => by
    show (g z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ
        * ((Work.Spaces.w z) ^ 2)⁻¹ = (g z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
    have hstep : (g z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ
          * ((Work.Spaces.w z) ^ 2)⁻¹
        = (g z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
          * ((Work.Spaces.w z) ^ 2 * ((Work.Spaces.w z) ^ 2)⁻¹) := by ring
    rw [hstep, mul_inv_cancel₀ hw2, mul_one]) measurableSet_Icc

/-! ## The two slices of `pthIter 2` -/

/-- `pthIter 2` of a slice is the second derivative of the slice. -/
private theorem aeh_pthIter_two_eq {v : ℝ → ℝ → ℝ} (z θ : ℝ) :
    Work.Spaces.pthIter 2 v z θ = deriv (fun t : ℝ => deriv (fun t' : ℝ => v z t') t) θ := by
  simp only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero, Work.Spaces.pth]

/-! ## The target -/

theorem aeSliceHonestOfSlots {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (h : Work.FTS.EllipticEst.WeakPos2 α F Ψ)
    (hθ : ∀ j : ℕ, j ≤ 2 →
      Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 (Work.Spaces.pzIter j Ψ)))
    (hr : Work.Spaces.HkMem α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 3 Ψ z θ)) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)), ∀ j : ℕ, j ≤ 3 →
      MeasureTheory.IntegrableOn
        (fun θ : ℝ => Work.Spaces.pzIter j Ψ z θ * Work.Elliptic.sinCos2 θ)
        Work.Spaces.Iθ := by
  have hQ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.2.2.2.2.2.2.1
  filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with z hzmem
  have hz : 0 < z := hzmem
  intro j hj
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => Work.Spaces.pzIter j Ψ z θ * Work.Elliptic.sinCos2 θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    ((hQ.aesm_slice_pzIter j hz)).mul
      aeh_continuous_sinCos2.measurable.aestronglyMeasurable
  by_cases hj2 : j ≤ 2
  · -- ## the case `j ≤ 2`: the second angular derivative forces boundedness of the slice
    have hslice : ContDiffOn ℝ 2 (fun θ : ℝ => Work.Spaces.pzIter j Ψ z θ)
        (Set.Ioo 0 (Real.pi / 2)) :=
      contDiffOn_iff_forall_nat_le.mp ((hQ.pzIter j).curry_θ hz) 2 le_top
    have hint : MeasureTheory.IntegrableOn
        (fun θ : ℝ => (Work.Spaces.pthIter 2 (Work.Spaces.pzIter j Ψ) z θ) ^ 2
          * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ :=
      aeh_sq_mul_sEta_of_HkMem (hθ j hj2) hz
    have hint' : MeasureTheory.IntegrableOn
        (fun θ : ℝ => deriv (fun t : ℝ =>
            deriv (fun t' : ℝ => Work.Spaces.pzIter j Ψ z t') t) θ ^ 2
          * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ :=
      hint.congr_fun (fun θ _ => by
        show Work.Spaces.pthIter 2 (Work.Spaces.pzIter j Ψ) z θ ^ 2
            * Work.FTS.EllipticEst.sEta θ
          = deriv (fun t : ℝ => deriv (fun t' : ℝ => Work.Spaces.pzIter j Ψ z t') t) θ ^ 2
            * Work.FTS.EllipticEst.sEta θ
        rw [aeh_pthIter_two_eq]) measurableSet_Icc
    obtain ⟨C, hC0, hC⟩ :=
      Work.FTS.EllipticEst.Honest.slice_bdd_of_sq_mul_sEta hslice hint'
    rw [MeasureTheory.IntegrableOn]
    refine Integrable.mono' (MeasureTheory.integrableOn_const (s := Work.Spaces.Iθ) (C := C)
      (ne_of_lt aeh_volume_Iθ_lt_top)) haesm ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
    rcases lt_or_eq_of_le hθ.1 with h0 | h0
    · rcases lt_or_eq_of_le hθ.2 with h1 | h1
      · rw [Real.norm_eq_abs, abs_mul]
        calc |Work.Spaces.pzIter j Ψ z θ| * |Work.Elliptic.sinCos2 θ|
            ≤ C * 1 := mul_le_mul (hC θ ⟨h0, h1⟩).1
                (Work.FTS.EllipticEst.abs_sinCos2_le_one hθ) (abs_nonneg _) hC0
          _ = C := by ring
      · rw [h1, aeh_sinCos2_zero_right, mul_zero, norm_zero]
        exact hC0
    · rw [← h0, aeh_sinCos2_zero_left, mul_zero, norm_zero]
      exact hC0
  · -- ## the case `j = 3`: only the `η`-weighted square of the slice is available
    have hj3 : j = 3 := by omega
    subst hj3
    have hW : MeasureTheory.IntegrableOn
        (fun θ : ℝ => (Work.Spaces.pzIter 3 Ψ z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        Work.Spaces.Iθ := by
      have h1 : MeasureTheory.IntegrableOn
          (fun θ : ℝ => Work.Spaces.HkIntegrand α 0
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 3 Ψ z θ) z θ) Work.Spaces.Iθ :=
        hr.1 z (le_of_lt hz)
      have h2 : MeasureTheory.IntegrableOn
          (fun θ : ℝ => ((z ^ 2 * Work.Spaces.pzIter 3 Ψ z θ)
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          Work.Spaces.Iθ :=
        h1.congr_fun
          (fun θ _ => aeh_HkIntegrand_zero α (fun z θ => z ^ 2 * Work.Spaces.pzIter 3 Ψ z θ)
            z θ) measurableSet_Icc
      have hz4 : ((z : ℝ) ^ 2) ^ 2 ≠ 0 := pow_ne_zero _ (pow_ne_zero _ (ne_of_gt hz))
      have h3 : MeasureTheory.IntegrableOn
          (fun θ : ℝ => ((z ^ 2 * Work.Spaces.pzIter 3 Ψ z θ)
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
            * (((z : ℝ) ^ 2) ^ 2)⁻¹) Work.Spaces.Iθ :=
        h2.mul_const (((z : ℝ) ^ 2) ^ 2)⁻¹
      exact h3.congr_fun (fun θ _ => by
        show ((z ^ 2 * Work.Spaces.pzIter 3 Ψ z θ)
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
            * (((z : ℝ) ^ 2) ^ 2)⁻¹
          = (Work.Spaces.pzIter 3 Ψ z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        have hstep : ((z ^ 2 * Work.Spaces.pzIter 3 Ψ z θ)
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
              * (((z : ℝ) ^ 2) ^ 2)⁻¹
            = (Work.Spaces.pzIter 3 Ψ z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
              * (((z : ℝ) ^ 2) ^ 2 * (((z : ℝ) ^ 2) ^ 2)⁻¹) := by ring
        rw [hstep, mul_inv_cancel₀ hz4, mul_one]) measurableSet_Icc
    have hmaj : MeasureTheory.IntegrableOn
        (fun θ : ℝ => (Work.Spaces.pzIter 3 Ψ z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 + 1)
        Work.Spaces.Iθ :=
      hW.add (MeasureTheory.integrableOn_const (s := Work.Spaces.Iθ) (C := (1 : ℝ))
        (ne_of_lt aeh_volume_Iθ_lt_top))
    rw [MeasureTheory.IntegrableOn]
    refine Integrable.mono' hmaj haesm ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
    rcases lt_or_eq_of_le hθ.1 with h0 | h0
    · rcases lt_or_eq_of_le hθ.2 with h1 | h1
      · simpa only [Real.norm_eq_abs] using
          Work.FTS.EllipticEst.abs_mul_sinCos2_le_weighted
            (f := fun θ : ℝ => Work.Spaces.pzIter 3 Ψ z θ) hz hθ
      · rw [h1, aeh_sinCos2_zero_right, mul_zero, norm_zero]
        positivity
    · rw [← h0, aeh_sinCos2_zero_left, mul_zero, norm_zero]
      positivity

end Work.FTS.EllipticEst.H2W
