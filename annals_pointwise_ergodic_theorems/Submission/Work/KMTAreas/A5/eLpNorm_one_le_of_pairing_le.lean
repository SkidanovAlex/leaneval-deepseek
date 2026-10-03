import Mathlib
import Submission.Work.KMTAreas.A5.Basic
import Submission.Port.Aesm

namespace Work.KMTAreas.A5

open MeasureTheory
open scoped ENNReal NNReal BigOperators

/-!
# The `ℓ¹` norm against the `ℓ^∞` unit ball

For `X : ℤ → ℂ` the `ℒ¹` seminorm with respect to the counting measure is the supremum of the
absolute values of the pairings `∑ x, X x * φ x` over all test functions `φ` with `‖φ x‖ ≤ 1`
everywhere.  This is the elementary duality `(ℓ¹)' = ℓ^∞`: the pairing against the "phase" function
`φ x = conj (X x) / ‖X x‖` realises the whole mass of `X` on any finite set at once.

The lemma is stated with the Bochner integral against the counting measure, which for a finitely
supported integrand is the honest finite sum; the hypothesis is applied to a test function
supported on a finite set, so no junk value of the integral intervenes.
-/

/-- The phase of a complex number realises its modulus in the pairing `z * w`. -/
lemma kmtPhase_mul (z : ℂ) : z * (starRingEnd ℂ z / (‖z‖ : ℂ)) = (‖z‖ : ℂ) := by
  have h1 : z * (starRingEnd ℂ z) = (‖z‖ : ℂ) * (‖z‖ : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, ← Complex.ofReal_mul]
    exact congrArg ((↑) : ℝ → ℂ) (by ring)
  calc z * (starRingEnd ℂ z / (‖z‖ : ℂ))
      = z * (starRingEnd ℂ z) / (‖z‖ : ℂ) := by rw [mul_div_assoc]
    _ = ((‖z‖ : ℂ) * (‖z‖ : ℂ)) / (‖z‖ : ℂ) := by rw [h1]
    _ = (‖z‖ : ℂ) := mul_self_div_self _

/-- The phase of a complex number has modulus at most `1`. -/
lemma kmtPhase_norm_le_one (z : ℂ) : ‖starRingEnd ℂ z / (‖z‖ : ℂ)‖ ≤ 1 := by
  rw [norm_div, Complex.norm_conj]
  have h : ‖(↑(‖z‖) : ℂ)‖ = ‖z‖ := by simp
  rw [h]
  exact div_self_le_one _

/-- The Bochner integral against the counting measure of a function supported on a finite set is
the corresponding finite sum. -/
lemma kmt_integral_count_eq_finset_sum (f : ℤ → ℂ) (F : Finset ℤ) (hF : ∀ x, x ∉ F → f x = 0) :
    ∫ x, f x ∂MeasureTheory.Measure.count = ∑ x ∈ F, f x := by
  have hsum : Summable (fun x : ℤ => ‖f x‖) :=
    summable_of_ne_finset_zero (s := F) (fun b hb => by rw [hF b hb, norm_zero])
  have hint : MeasureTheory.Integrable f MeasureTheory.Measure.count :=
    MeasureTheory.integrable_count_iff.mpr hsum
  rw [MeasureTheory.integral_countable hint]
  have hreal : ∀ x : ℤ, (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ).real {x} = 1 := by
    intro x
    rw [MeasureTheory.Measure.real_def]
    simp
  simp_rw [hreal, one_smul]
  exact tsum_eq_sum (s := F) (fun b hb => hF b hb)

/-- The `ℓ^∞` test function which is the phase of `X` on the finite set `F` and vanishes off it. -/
noncomputable def kmtPhaseTest (X : ℤ → ℂ) (F : Finset ℤ) : ℤ → ℂ :=
  fun x => if x ∈ F then starRingEnd ℂ (X x) / (‖X x‖ : ℂ) else 0

lemma kmtPhaseTest_norm_le_one (X : ℤ → ℂ) (F : Finset ℤ) : ∀ x, ‖kmtPhaseTest X F x‖ ≤ 1 := by
  intro x
  rw [kmtPhaseTest]
  by_cases hx : x ∈ F
  · rw [if_pos hx]; exact kmtPhase_norm_le_one (X x)
  · rw [if_neg hx, norm_zero]; norm_num

lemma kmtPhaseTest_mul (X : ℤ → ℂ) (F : Finset ℤ) (x : ℤ) :
    X x * kmtPhaseTest X F x = (if x ∈ F then ((‖X x‖ : ℝ) : ℂ) else 0) := by
  rw [kmtPhaseTest]
  by_cases hx : x ∈ F
  · rw [if_pos hx, if_pos hx]; exact kmtPhase_mul (X x)
  · rw [if_neg hx, if_neg hx, mul_zero]

theorem eLpNorm_one_le_of_pairing_le (X : ℤ → ℂ) (C : ℝ≥0∞)
    (h : ∀ φ : ℤ → ℂ, (∀ x : ℤ, ‖φ x‖ ≤ 1) →
      ‖∫ x, X x * φ x ∂MeasureTheory.Measure.count‖ₑ ≤ C) :
    MeasureTheory.eLpNorm X 1 MeasureTheory.Measure.count ≤ C := by
  have hbound : ∀ F : Finset ℤ, ∑ x ∈ F, ‖X x‖ₑ ≤ C := by
    intro F
    have hint : ‖∫ x, X x * kmtPhaseTest X F x ∂MeasureTheory.Measure.count‖ₑ ≤ C :=
      h (kmtPhaseTest X F) (kmtPhaseTest_norm_le_one X F)
    have hFint : ∫ x, X x * kmtPhaseTest X F x ∂MeasureTheory.Measure.count
        = ∑ x ∈ F, ((‖X x‖ : ℝ) : ℂ) := by
      rw [kmt_integral_count_eq_finset_sum (fun x => X x * kmtPhaseTest X F x) F
        (fun x hx => by rw [kmtPhaseTest_mul, if_neg hx])]
      exact Finset.sum_congr rfl fun x hx => by rw [kmtPhaseTest_mul, if_pos hx]
    have hnorm : ‖∑ x ∈ F, ((‖X x‖ : ℝ) : ℂ)‖ = ∑ x ∈ F, ‖X x‖ := by
      rw [← Complex.ofReal_sum]
      have h : ‖(↑(∑ x ∈ F, ‖X x‖) : ℂ)‖ = |∑ x ∈ F, ‖X x‖| := RCLike.norm_ofReal _
      rw [h, abs_of_nonneg (Finset.sum_nonneg fun i _ => norm_nonneg _)]
    calc ∑ x ∈ F, ‖X x‖ₑ = ∑ x ∈ F, ENNReal.ofReal ‖X x‖ :=
          Finset.sum_congr rfl fun x _ => (ofReal_norm (X x)).symm
      _ = ENNReal.ofReal (∑ x ∈ F, ‖X x‖) :=
          (ENNReal.ofReal_sum_of_nonneg (fun i _ => norm_nonneg _)).symm
      _ = ‖∑ x ∈ F, ((‖X x‖ : ℝ) : ℂ)‖ₑ := by rw [← ofReal_norm, hnorm]
      _ = ‖∫ x, X x * kmtPhaseTest X F x ∂MeasureTheory.Measure.count‖ₑ := by rw [hFint]
      _ ≤ C := hint
  rw [MeasureTheory.eLpNorm_one_eq_lintegral_enorm (hf := by pw_aesm), MeasureTheory.lintegral_count,
    ENNReal.tsum_eq_iSup_sum]
  exact iSup_le hbound

end Work.KMTAreas.A5
