import Mathlib
import Submission.Work.GM.Affine.FarMass_defs
import Submission.Work.GM.Affine.region_II_vocab
import Submission.Work.GM.Affine.region_II_defs
import Submission.Work.GM.Affine.fine_setup
import Submission.Work.GM.Affine.psi1hat_decay
import Submission.Work.GM.Affine.far_weight_le_pf

/-!
# The far mass is bounded by the `L²`-mass of `Bsum`

`FarMass K f M₂ M₃ = Σ'_ℓ ∫_{|τ|>2} ‖Bsum f M₂ (ℓ+τ/M₃)‖² ‖ψ̂₁ τ‖² dτ`.

Substituting `u = ℓ + τ/M₃` in the `ℓ`-th term and interchanging sum and integral (all terms
non-negative) gives `FarMass = M₃ ∫_ℝ ‖Bsum f M₂ u‖² G_F u du` with the `1`-periodic weight
`G_F u = Σ'_ℓ [|u-ℓ| > 2/M₃] ‖ψ̂₁ (M₃ (u-ℓ))‖²`, which is uniformly bounded by a constant
depending only on `K`.  Hence `FarMass ≤ C M₃ ∫_ℝ ‖Bsum f M₂‖²`.
-/

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.GM.Affine

noncomputable section

/-- The "far" set in the `τ`-variable is `{τ | 2 < |τ|}`. -/
lemma far_set_eq : (Set.Ioi (2:ℝ) ∪ Set.Iio (-2)) = {τ : ℝ | 2 < |τ|} := by
  ext τ
  simp only [Set.mem_union, Set.mem_Ioi, Set.mem_Iio, Set.mem_ofPred_eq]
  constructor
  · rintro (h | h)
    · rw [abs_of_pos (by linarith)]; exact h
    · rw [abs_of_neg (by linarith)]; linarith
  · intro h
    by_cases hτ : 0 ≤ τ
    · left; rwa [abs_of_nonneg hτ] at h
    · right; rw [abs_of_neg (not_le.mp hτ)] at h; linarith

/-- The far set is measurable. -/
lemma far_set_measurable : MeasurableSet (Set.Ioi (2:ℝ) ∪ Set.Iio (-2)) :=
  measurableSet_Ioi.union measurableSet_Iio

/-- `{x | 2/M₃ < |x|}` is the preimage of the far set under `x ↦ M₃ * x` (`M₃ > 0`). -/
lemma preimage_far_set {M₃ : ℝ} (hM₃ : 0 < M₃) :
    (fun x : ℝ => M₃ * x) ⁻¹' (Set.Ioi (2:ℝ) ∪ Set.Iio (-2)) = {x : ℝ | 2 / M₃ < |x|} := by
  ext x
  rw [Set.mem_preimage, far_set_eq, Set.mem_ofPred_eq, Set.mem_ofPred_eq, abs_mul,
      abs_of_pos hM₃, div_lt_iff₀ hM₃]
  constructor <;> intro h <;> nlinarith [abs_nonneg x]

/-- Change of variables for a set integral under `x ↦ c * x` (`c > 0`), for a measurable set and
a measurable `g`. -/
lemma setIntegral_comp_mul_left {c : ℝ} (hc : 0 < c) {g : ℝ → ℝ} (hg : Measurable g)
    {s : Set ℝ} (hs : MeasurableSet s) :
    ∫ y in s, g y = c * ∫ x in (fun x : ℝ => c * x) ⁻¹' s, g (c * x) := by
  have hcne : c ≠ 0 := hc.ne'
  have hFmeas : AEStronglyMeasurable (s.indicator g)
      (Measure.map (fun x : ℝ => c * x) (volume : Measure ℝ)) :=
    (hg.indicator hs).aestronglyMeasurable
  have h1 : ∫ x : ℝ, (s.indicator g) (c * x)
      = ∫ y : ℝ, (s.indicator g) y ∂(Measure.map (fun x : ℝ => c * x) (volume : Measure ℝ)) :=
    (integral_map (φ := fun x : ℝ => c * x) (f := s.indicator g) (by fun_prop) hFmeas).symm
  have hmap : Measure.map (fun x : ℝ => c * x) (volume : Measure ℝ)
      = ENNReal.ofReal c⁻¹ • (volume : Measure ℝ) := by
    rw [Real.map_volume_mul_left hcne, abs_of_pos (inv_pos.mpr hc)]
  rw [hmap, integral_smul_measure, ENNReal.toReal_ofReal (by positivity), smul_eq_mul] at h1
  have h3 : ∫ x in (fun x : ℝ => c * x) ⁻¹' s, g (c * x)
      = ∫ x : ℝ, (s.indicator g) (c * x) := by
    have key : ∀ x : ℝ, ((fun x : ℝ => c * x) ⁻¹' s).indicator (fun x => g (c * x)) x
        = (s.indicator g) (c * x) := by
      intro x
      by_cases h : c * x ∈ s
      · rw [Set.indicator_of_mem (show x ∈ (fun x : ℝ => c * x) ⁻¹' s from h),
            Set.indicator_of_mem h]
      · rw [Set.indicator_of_notMem (show x ∉ (fun x : ℝ => c * x) ⁻¹' s from h),
            Set.indicator_of_notMem h]
    rw [← integral_indicator (s := (fun x : ℝ => c * x) ⁻¹' s)
      (f := fun x => g (c * x)) (hs.preimage (by fun_prop))]
    exact integral_congr_ae (Filter.Eventually.of_forall key)
  have h2 : ∫ y in s, g y = ∫ y : ℝ, (s.indicator g) y :=
    (integral_indicator (s := s) (f := g) hs).symm
  rw [h3, h2]
  have hBB : c * (c⁻¹ * ∫ y : ℝ, (s.indicator g) y) = ∫ y : ℝ, (s.indicator g) y := by
    rw [← mul_assoc, mul_inv_cancel₀ hcne, one_mul]
  rw [← hBB, h1]


/-- The far weight `W u = Σ'_ℓ [|u-ℓ| > 2/M₃] ‖ψ̂₁ (M₃(u-ℓ))‖²` is uniformly bounded, for
`M₃ ≥ 1`, by a constant depending only on `K`. -/
lemma far_weight_le {K M₃ : ℝ} (hK : 0 < K) (hM₃ : 1 ≤ M₃) (u : ℝ) :
    (∑' ℓ : ℤ, (if 2 / M₃ < |u - (ℓ : ℝ)| then ‖psi1hat K (M₃ * (u - (ℓ : ℝ)))‖ ^ 2
      else 0)) ≤ (2 * 3 ^ (-(2:ℤ)) + 2 * (∑' j : ℕ, (1 + (j:ℝ)) ^ (-(4:ℤ))) + 1)
        * (Classical.choose (psi1hat_decay K hK 2)) ^ 2 :=
  far_weight_le_pf hK hM₃ u

end

end Work.GM.Affine
