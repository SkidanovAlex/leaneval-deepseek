import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB3.CS.ae_eval_mem_interior_acube
import Submission.Work.BoseFixB3.CS.fourierInv_fourier_eq_zero_of_not_integrable
import Submission.Work.BoseFixB3.CS.lowMult_eq_fourierInv_re
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB3.CS.highSlot_sq_le_of_nonpos`

For `κ ≤ 0` the low-momentum cut-off symbol `p ↦ f(‖p‖/κ)` is identically `1` (`fc.one`,
since `‖p‖/κ ≤ 0 ≤ 1`), so the multiplier `f_L(√−Δ) = lowMult fc κ ℓ` is the *identity*
multiplier on the box: by Fourier inversion (`lowMult_eq_fourierInv_re` +
`Integrable.fourierInv_fourier_eq`) its value at a point of continuity `y` of the box
extension of `ψ` is `ψ y`, and when the Fourier transform is not `L¹` the Bochner integral
evaluates to `0` (`fourierInv_fourier_eq_zero_of_not_integrable`).  Hence

  `lowMult fc κ ℓ ψ y = ψ y ∨ lowMult fc κ ℓ ψ y = 0`

at every `y ∈ interior (acube ℓ)`, and therefore the complementary multiplier
`highSlot = (1 − f_L)` satisfies `highSlot² ≤ 4 Ψ²`.  The passage from this pointwise
statement to the almost-everywhere statement on the box uses that a.e. point of the box
lies in the interior of the cube (`ae_eval_mem_interior_acube`), while for `ℓ ≤ 0` the box
carries no volume at all.
-/

noncomputable section

open MeasureTheory Filter
open scoped Topology Real BigOperators

namespace Work.BoseFixB3.CS

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The centred cube `acube ℓ` is compact, for every side length `ℓ`. -/
lemma acube_compact_of_any (ℓ : ℝ) : IsCompact (Submission.BoseGases.acube ℓ) := by
  have h : Submission.BoseGases.acube ℓ
      = WithLp.toLp 2 '' Submission.BoseGases.acubeF ℓ := by
    rw [Submission.BoseGases.acube_eq_image]
    rfl
  rw [h, Submission.BoseGases.acubeF_eq_pi ℓ]
  exact (isCompact_univ_pi (fun _ : Fin 3 => isCompact_Icc)).image (by fun_prop)

/-- **The one-slot dichotomy.**  For `κ ≤ 0` the low-momentum multiplier `f_L(√−Δ)` of the
box extension of `ψ` returns either `ψ y` (the non-degenerate case, Fourier inversion) or
`0` (the Fourier transform of the box extension fails to be `L¹`, so the Bochner integral
defining the multiplier is `0`), at every point of continuity `y ∈ interior (acube ℓ)` of
the box extension. -/
lemma lowMult_eq_self_or_eq_zero_of_nonpos {fc : Work.BoseBoxFix.LowCut} {κ ℓ : ℝ}
    (hκ : κ ≤ 0) (hℓ : 0 < ℓ) {ψ : E3 → ℝ} (hψc : Continuous ψ) {y : E3}
    (hy : y ∈ interior (Submission.BoseGases.acube ℓ)) :
    Work.BoseBoxFix.lowMult fc κ ℓ ψ y = ψ y
      ∨ Work.BoseBoxFix.lowMult fc κ ℓ ψ y = 0 := by
  classical
  set g : E3 → ℂ := fun z => (((Submission.BoseGases.acube ℓ).indicator ψ z : ℝ) : ℂ) with hg
  have hkey : Work.BoseBoxFix.lowMult fc κ ℓ ψ y
      = (FourierTransformInv.fourierInv (FourierTransform.fourier g) y).re := by
    have h := lowMult_eq_fourierInv_re (fc := fc) (κ := κ) (ℓ := ℓ) hκ ψ y
    simpa only [hg] using h
  have hψC : Continuous (fun z : E3 => (ψ z : ℂ)) := Complex.continuous_ofReal.comp hψc
  by_cases hint : Integrable (FourierTransform.fourier g) volume
  · left
    have hgon : IntegrableOn (fun z : E3 => (ψ z : ℂ)) (Submission.BoseGases.acube ℓ) volume :=
      ContinuousOn.integrableOn_compact (acube_compact_of_any ℓ) hψC.continuousOn
    have hgt : Integrable g volume := by
      have heq : (Submission.BoseGases.acube ℓ).indicator (fun z : E3 => (ψ z : ℂ)) = g := by
        rw [hg]
        funext z
        by_cases hz : z ∈ Submission.BoseGases.acube ℓ
        · simp [Set.indicator_of_mem hz]
        · simp [Set.indicator_of_notMem hz, Complex.ofReal_zero]
      rw [← heq]
      exact hgon.integrable_indicator (Submission.BoseGases.acube_measurable ℓ)
    have hca : ContinuousAt g y := by
      have hmem : ∀ᶠ z in 𝓝 y, z ∈ Submission.BoseGases.acube ℓ :=
        Filter.mem_of_superset (isOpen_interior.mem_nhds hy) interior_subset
      have hev : g =ᶠ[𝓝 y] fun z => (ψ z : ℂ) := by
        filter_upwards [hmem] with z hz
        simp [hg, Set.indicator_of_mem hz]
      exact (continuousAt_congr hev).mpr hψC.continuousAt
    rw [hkey, Integrable.fourierInv_fourier_eq hgt hint hca]
    simp [hg, Set.indicator_of_mem (interior_subset hy), Complex.ofReal_re]
  · right
    rw [hkey, fourierInv_fourier_eq_zero_of_not_integrable hint]
    simp

/-- **The pointwise bound.**  At every `x` whose `j`-th coordinate lies in the interior of
the cube, the complementary multiplier `1 − f_L` obeys `highSlot² ≤ 4 Ψ²`: the slot-`j`
fibre of `Ψ` is continuous, so the dichotomy applies to its box extension. -/
lemma highSlot_sq_le_of_mem_interior {fc : Work.BoseBoxFix.LowCut} {κ ℓ : ℝ} (hκ : κ ≤ 0)
    (hℓ : 0 < ℓ) {n : ℕ} (j : Fin n) {Ψ : Submission.BoseGases.X n → ℝ}
    (hΨ : Continuous Ψ) {x : Submission.BoseGases.X n}
    (hint : x j ∈ interior (Submission.BoseGases.acube ℓ)) :
    (Work.BoseFixB3.highSlot fc κ ℓ j Ψ x) ^ 2 ≤ 4 * (Ψ x) ^ 2 := by
  have hupd : Continuous (fun z : E3 => Function.update x j z) :=
    continuous_const.update j continuous_id
  have hψc : Continuous (fun z : E3 => Ψ (Function.update x j z)) := hΨ.comp hupd
  have hdich :=
    lowMult_eq_self_or_eq_zero_of_nonpos (fc := fc) (κ := κ) (ℓ := ℓ) hκ hℓ hψc hint
  have hself : Ψ (Function.update x j (x j)) = Ψ x := by
    simp [Function.update_eq_self]
  have hsplit : Work.BoseFixB3.highSlot fc κ ℓ j Ψ x
      = Ψ x - Work.BoseBoxFix.lowMult fc κ ℓ (fun z : E3 => Ψ (Function.update x j z))
          (x j) := rfl
  rcases hdich with hval | hval
  · rw [hsplit, hval, hself, sub_self]
    nlinarith [sq_nonneg (Ψ x)]
  · rw [hsplit, hval, sub_zero]
    nlinarith [sq_nonneg (Ψ x)]

theorem highSlot_sq_le_of_nonpos {fc : Work.BoseBoxFix.LowCut} {κ ℓ : ℝ} (hκ : κ ≤ 0)
    {n : ℕ} (j : Fin n) {Ψ : Submission.BoseGases.X n → ℝ} (hΨ : Continuous Ψ) :
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)),
      (Work.BoseFixB3.highSlot fc κ ℓ j Ψ x) ^ 2 ≤ 4 * (Ψ x) ^ 2 := by
  rcases n with _ | m
  · exact Fin.elim0 j
  · by_cases hℓ : 0 < ℓ
    · have hae : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox (m + 1) ℓ)),
          x j ∈ interior (Submission.BoseGases.acube ℓ) :=
        ae_eval_mem_interior_acube j hℓ
      filter_upwards [hae] with x hx
      exact highSlot_sq_le_of_mem_interior hκ hℓ j hΨ hx
    · have hℓnn : ℓ ≤ 0 := le_of_not_gt hℓ
      have hvol : (MeasureTheory.volume : MeasureTheory.Measure E3)
          (Submission.BoseGases.acube ℓ) = 0 := by
        refine measure_mono_null ?_ (by simpa using Submission.BoseGases.acube_volume (0 : ℝ) le_rfl)
        intro y hy mm
        have hh := (Submission.BoseGases.mem_acube_iff ℓ y).mp hy mm
        simp only [Set.mem_Icc] at hh ⊢
        exact ⟨by linarith [hh.1], by linarith [hh.2, hℓnn]⟩
      have hpi : (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X (m + 1)))
          (Function.eval (0 : Fin (m + 1)) ⁻¹' Submission.BoseGases.acube ℓ) = 0 :=
        MeasureTheory.Measure.pi_eval_preimage_null
          (fun _ : Fin (m + 1) => (MeasureTheory.volume : MeasureTheory.Measure E3))
          (i := (0 : Fin (m + 1))) hvol
      have hbox : (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X (m + 1)))
          (Submission.BoseGases.abox (m + 1) ℓ) = 0 :=
        measure_mono_null (fun x hx => hx (0 : Fin (m + 1))) hpi
      rw [MeasureTheory.Measure.restrict_eq_zero.mpr hbox, MeasureTheory.ae_zero]
      exact Filter.eventually_bot

end Work.BoseFixB3.CS
