import Mathlib
import Submission.Work.GM.Affine.WinMass_basic
import Submission.Work.GM.Affine.setup
import Submission.Work.GM.Affine.fine_setup

/-!
# `Work.GM.Affine.Hprof_sq_integral_le`

The crude diagonal (Cauchy–Schwarz) bound for the `m₂`-profile

  `Hprof f M₂ u = Σ_{m₂ ∈ R2 M₂} f (u / m₂)`:

  `∫ u, (Hprof f M₂ u)² ≤ 8 (max M₂ 1)³ ∫ u, (f u)²`.

Proof.  Pointwise Cauchy–Schwarz in the finite sum `R2 M₂ = (M₂, 2M₂] ∩ ℤ` gives
`(Σ_{m₂} f (u/m₂))² ≤ #(R2 M₂) · Σ_{m₂} f (u/m₂)²`; each summand is integrable (continuous with
compact support, dominated by `supf f · f`), the finite sum is pulled out of the integral
(Fubini for a finite sum), and the substitution `u = m₂ v` (`Measure.integral_comp_div`) turns
each summand integral into `m₂ ∫ f²`.  Finally `#(R2 M₂) ≤ 2 M₂` and
`Σ_{m₂ ∈ R2 M₂} m₂ ≤ 4 M₂²`, giving `8 M₂³ ∫ f² ≤ 8 (max M₂ 1)³ ∫ f²`.

No hypothesis on the Fourier decay of `f` is used: this is the crude bound that replaces the
`winMass_crude` route in `WinMass_core`.
-/

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform

set_option autoImplicit false
-- `hC₀` is part of the (fixed) statement but is not needed for this crude bound.
set_option linter.unusedVariables false

noncomputable section

namespace Work.GM.Affine

/-- `#(R2 M₂) ≤ 2 M₂` for `M₂ > 0`. -/
lemma R2_card_le_two {M₂ : ℝ} (hM₂ : 0 < M₂) : ((R2 M₂).card : ℝ) ≤ 2 * M₂ := by
  have h1 : (R2 M₂).card ≤ (Finset.Icc (1 : ℤ) ⌊2 * M₂⌋).card :=
    Finset.card_le_card (fun m hm => (Finset.mem_filter.mp hm).1)
  have h2 : ((Finset.Icc (1 : ℤ) ⌊2 * M₂⌋).card : ℝ) ≤ 2 * M₂ := by
    rw [Int.card_Icc]
    have h3 : ⌊2 * M₂⌋ + 1 - 1 = ⌊2 * M₂⌋ := by ring
    rw [h3]
    have h4 : (0 : ℤ) ≤ ⌊2 * M₂⌋ := Int.floor_nonneg.mpr (by linarith)
    have h5 : ((⌊2 * M₂⌋).toNat : ℤ) ≤ 2 * M₂ := by
      rw [Int.toNat_of_nonneg h4]; exact Int.floor_le _
    exact_mod_cast h5
  exact le_trans (by exact_mod_cast h1) h2

/-- `Σ_{m ∈ R2 M₂} m ≤ 4 M₂²` for `M₂ > 0`. -/
lemma R2_sum_le {M₂ : ℝ} (hM₂ : 0 < M₂) :
    (∑ m ∈ R2 M₂, (m : ℝ)) ≤ 4 * M₂ ^ 2 := by
  have hterm : ∀ m ∈ R2 M₂, (m : ℝ) ≤ 2 * M₂ := by
    intro m hm
    have h1 : (m : ℤ) ≤ ⌊2 * M₂⌋ := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).2
    have h2 : ((m : ℤ) : ℝ) ≤ ((⌊2 * M₂⌋ : ℤ) : ℝ) := by exact_mod_cast h1
    have h3 : ((⌊2 * M₂⌋ : ℤ) : ℝ) ≤ 2 * M₂ := Int.floor_le _
    linarith
  calc (∑ m ∈ R2 M₂, (m : ℝ)) ≤ ∑ m ∈ R2 M₂, (2 * M₂) := Finset.sum_le_sum hterm
    _ = ((R2 M₂).card : ℝ) * (2 * M₂) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * M₂) * (2 * M₂) :=
        mul_le_mul_of_nonneg_right (R2_card_le_two hM₂) (by linarith)
    _ = 4 * M₂ ^ 2 := by ring

theorem Hprof_sq_integral_le {C₀ : ℝ} (hC₀ : 1 ≤ C₀) {M₂ : ℝ} (hM₂ : 0 < M₂) {f : ℝ → ℝ}
    (hf : Continuous f) (hfnn : ∀ u, 0 ≤ f u) (hSupp : SuppHyp C₀ f) :
    (∫ v, (Hprof f M₂ v) ^ 2) ≤ 8 * (max M₂ 1) ^ 3 * ∫ v, (f v) ^ 2 := by
  -- `f` is continuous with compact support (its support is contained in `[1/C₀, C₀]`),
  -- hence integrable
  have hcs : HasCompactSupport f :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc (fun u hu => hSupp u hu)
  have hfint : Integrable f := hf.integrable_of_hasCompactSupport hcs
  -- every `m ∈ R2 M₂` is positive
  have hm_pos : ∀ m ∈ R2 M₂, (0 : ℝ) < (m : ℝ) := by
    intro m hm
    have h : M₂ < (m : ℝ) := (Finset.mem_filter.mp hm).2
    linarith
  -- integrability of the dilated squares `u ↦ f (u/m)²`
  have hInt_sq : ∀ m ∈ R2 M₂, Integrable (fun u : ℝ => (f (u / (m : ℝ))) ^ 2) := by
    intro m hm
    have hInt_div : Integrable (fun u : ℝ => f (u / (m : ℝ))) :=
      (integrable_comp_div_iff f (ne_of_gt (hm_pos m hm))).2 hfint
    have hb : ∀ u : ℝ, (f (u / (m : ℝ))) ^ 2 ≤ supf f * f (u / (m : ℝ)) := by
      intro u
      have h1 : f (u / (m : ℝ)) ≤ supf f := le_supf hf hcs _
      have h0 : 0 ≤ f (u / (m : ℝ)) := hfnn _
      calc (f (u / (m : ℝ))) ^ 2 = f (u / (m : ℝ)) * f (u / (m : ℝ)) := by ring
        _ ≤ supf f * f (u / (m : ℝ)) := mul_le_mul_of_nonneg_right h1 h0
    refine Integrable.mono' (hInt_div.const_mul (supf f)) ?_ ?_
    · exact ((hf.comp (continuous_id.div_const (m : ℝ))).pow 2).aestronglyMeasurable
    · filter_upwards with u
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact hb u
  -- integrability of the dominating function
  have hInt_G : Integrable (fun u : ℝ => ((R2 M₂).card : ℝ) *
      ∑ m ∈ R2 M₂, (f (u / (m : ℝ))) ^ 2) :=
    (integrable_finsetSum (R2 M₂) (fun m hm => hInt_sq m hm)).const_mul _
  -- step 1: pointwise Cauchy–Schwarz, integrated
  have hstep1 : (∫ u, (Hprof f M₂ u) ^ 2)
      ≤ ∫ u, ((R2 M₂).card : ℝ) * ∑ m ∈ R2 M₂, (f (u / (m : ℝ))) ^ 2 :=
    integral_mono_of_nonneg (Filter.Eventually.of_forall (fun u => sq_nonneg _)) hInt_G
      (Filter.Eventually.of_forall (fun u => by
        simp only [Hprof]
        exact sq_sum_le_card_mul_sum_sq (s := R2 M₂) (f := fun m => f (u / (m : ℝ)))))
  -- step 2: pull the finite sum out of the integral
  have hstep2 : (∫ u, ((R2 M₂).card : ℝ) * ∑ m ∈ R2 M₂, (f (u / (m : ℝ))) ^ 2)
      = ((R2 M₂).card : ℝ) * ∑ m ∈ R2 M₂, ∫ u, (f (u / (m : ℝ))) ^ 2 := by
    rw [MeasureTheory.integral_const_mul]
    congr 1
    exact integral_finsetSum (R2 M₂) (fun m hm => hInt_sq m hm)
  -- step 3: substitute `u = m v` in each summand integral
  have hstep3 : ∀ m ∈ R2 M₂, (∫ u, (f (u / (m : ℝ))) ^ 2) = (m : ℝ) * ∫ u, (f u) ^ 2 := by
    intro m hm
    rw [Measure.integral_comp_div (fun v : ℝ => (f v) ^ 2) (m : ℝ),
      abs_of_pos (hm_pos m hm), smul_eq_mul]
  -- nonnegativity of the two factors used at the end
  have hX : 0 ≤ ∫ u, (f u) ^ 2 := integral_nonneg (fun u => sq_nonneg _)
  have hsum_nonneg : 0 ≤ ∑ m ∈ R2 M₂, (m : ℝ) :=
    Finset.sum_nonneg (fun m hm => (hm_pos m hm).le)
  calc (∫ v, (Hprof f M₂ v) ^ 2)
      ≤ ∫ u, ((R2 M₂).card : ℝ) * ∑ m ∈ R2 M₂, (f (u / (m : ℝ))) ^ 2 := hstep1
    _ = ((R2 M₂).card : ℝ) * ∑ m ∈ R2 M₂, ∫ u, (f (u / (m : ℝ))) ^ 2 := hstep2
    _ = ((R2 M₂).card : ℝ) * ∑ m ∈ R2 M₂, (m : ℝ) * ∫ u, (f u) ^ 2 :=
        congrArg _ (Finset.sum_congr rfl (fun m hm => hstep3 m hm))
    _ = ((R2 M₂).card : ℝ) * (∑ m ∈ R2 M₂, (m : ℝ)) * ∫ u, (f u) ^ 2 := by
        rw [← Finset.sum_mul]; ring
    _ ≤ (2 * M₂) * (4 * M₂ ^ 2) * ∫ u, (f u) ^ 2 := by
        have h3 : ((R2 M₂).card : ℝ) * (∑ m ∈ R2 M₂, (m : ℝ)) ≤ (2 * M₂) * (4 * M₂ ^ 2) :=
          mul_le_mul (R2_card_le_two hM₂) (R2_sum_le hM₂) hsum_nonneg (by linarith)
        exact mul_le_mul_of_nonneg_right h3 hX
    _ = 8 * M₂ ^ 3 * ∫ u, (f u) ^ 2 := by ring
    _ ≤ 8 * (max M₂ 1) ^ 3 * ∫ u, (f u) ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ hX
        have h6 : M₂ ^ 3 ≤ (max M₂ 1) ^ 3 := pow_le_pow_left₀ hM₂.le (le_max_left _ _) 3
        linarith

end Work.GM.Affine
