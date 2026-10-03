import Mathlib
import Submission.Work.KMTPlan.A6.FkrStep
import Submission.Work.KMTPlan.A6.fkrW_zero_varPart

namespace Work.KMTPlan.A6

open MeasureTheory ENNReal
open scoped ENNReal BigOperators

variable {X : Type*} [MeasurableSpace X]

/-- ENNReal: `(∑ (c x_i)^R)^{1/R} = c (∑ x_i^R)^{1/R}`. -/
lemma bfkr_rpow_sum_mul_rpow {R : ℝ} (hR : 0 < R) {ι : Type*} (s : Finset ι)
    (c : ℝ≥0∞) (x : ι → ℝ≥0∞) :
    (∑ i ∈ s, (c * x i) ^ R) ^ (1 / R) = c * (∑ i ∈ s, x i ^ R) ^ (1 / R) := by
  have h1 : ∀ i, (c * x i) ^ R = c ^ R * x i ^ R :=
    fun i => ENNReal.mul_rpow_of_nonneg _ _ hR.le
  have h3 : (c ^ R) ^ (1 / R) = c := by
    rw [← ENNReal.rpow_mul, mul_one_div_cancel hR.ne', ENNReal.rpow_one]
  calc (∑ i ∈ s, (c * x i) ^ R) ^ (1 / R)
      = (∑ i ∈ s, c ^ R * x i ^ R) ^ (1 / R) := by rw [Finset.sum_congr rfl (fun i _ => h1 i)]
    _ = (c ^ R * ∑ i ∈ s, x i ^ R) ^ (1 / R) := by rw [Finset.mul_sum]
    _ = (c ^ R) ^ (1 / R) * (∑ i ∈ s, x i ^ R) ^ (1 / R) :=
        ENNReal.mul_rpow_of_nonneg _ _ (le_of_lt (one_div_pos.mpr hR))
    _ = c * (∑ i ∈ s, x i ^ R) ^ (1 / R) := by rw [h3]

lemma bfkr_mul_le_right (c : ℝ≥0∞) {a b : ℝ≥0∞} (h : a ≤ b) : c * a ≤ c * b := by
  exact mul_le_mul_right h c

lemma bfkr_mul_le_left (c : ℝ≥0∞) {a b : ℝ≥0∞} (h : a ≤ b) : a * c ≤ b * c := by
  exact mul_le_mul_left h c

lemma bfkr_ennreal_add_mul_le (a b c d : ℝ≥0∞) : c * b + a * d ≤ (a + b) * (c + d) := by
  calc c * b + a * d ≤ (a * c + b * c) + (a * d + b * d) := by
        refine add_le_add ?_ ?_
        · rw [mul_comm c b]
          exact le_add_of_nonneg_left (a := b * c) (b := a * c) bot_le
        · exact le_add_of_nonneg_right (a := a * d) (b := b * d) bot_le
    _ = (a + b) * (c + d) := by rw [← add_mul, ← add_mul, ← mul_add]

lemma bfkr_ennreal_lp_weight_le {R : ℝ} (hR : 1 ≤ R) {ι : Type*} (s : Finset ι)
    (c : ℝ≥0∞) (x y : ι → ℝ≥0∞) :
    (∑ i ∈ s, (c * x i * y i) ^ R) ^ (1 / R)
      ≤ c * (⨆ i, y i) * (∑ i ∈ s, x i ^ R) ^ (1 / R) := by
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  set Z : ℝ≥0∞ := ⨆ i, y i with hZ
  have hZle : ∀ i, y i ≤ Z := fun i => by rw [hZ]; exact le_iSup (fun i => y i) i
  have key : ∀ i ∈ s, (c * x i * y i) ^ R ≤ ((c * Z) * x i) ^ R := by
    intro i _
    calc (c * x i * y i) ^ R = c ^ R * x i ^ R * y i ^ R := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hR0.le, ENNReal.mul_rpow_of_nonneg _ _ hR0.le]
      _ ≤ c ^ R * x i ^ R * Z ^ R :=
          bfkr_mul_le_right (c ^ R * x i ^ R) (ENNReal.rpow_le_rpow (hZle i) hR0.le)
      _ = ((c * Z) * x i) ^ R := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hR0.le, ENNReal.mul_rpow_of_nonneg _ _ hR0.le]
          ring
  calc (∑ i ∈ s, (c * x i * y i) ^ R) ^ (1 / R)
      ≤ (∑ i ∈ s, ((c * Z) * x i) ^ R) ^ (1 / R) :=
        ENNReal.rpow_le_rpow (Finset.sum_le_sum key) (le_of_lt (one_div_pos.mpr hR0))
    _ = (c * Z) * (∑ i ∈ s, x i ^ R) ^ (1 / R) := bfkr_rpow_sum_mul_rpow hR0 s (c * Z) x
    _ = c * (⨆ i, y i) * (∑ i ∈ s, x i ^ R) ^ (1 / R) := by rw [hZ]

lemma bfkr_bilinear_increment_decomp {X E F : Type*} [AddCommGroup E] [AddCommGroup F]
    (B : E → F → X → ℂ)
    (h1 : ∀ e e' f, B (e + e') f = B e f + B e' f)
    (h2 : ∀ e f f', B e (f + f') = B e f + B e f')
    (u : ℕ → E) (v : ℕ → F) (m n : ℕ) :
    (fun x => B (u n) (v n) x - B (u m) (v m) x)
      = (fun x => B (u n - u m) (v n) x) + (fun x => B (u m) (v n - v m) x) := by
  funext x
  have h1x : B (u n) (v n) x = B (u m) (v n) x + B (u n - u m) (v n) x := by
    have hh := congr_fun (h1 (u m) (u n - u m) (v n)) x
    rw [show u m + (u n - u m) = u n from by abel] at hh
    exact hh
  have h2x : B (u m) (v n) x = B (u m) (v m) x + B (u m) (v n - v m) x := by
    have hh := congr_fun (h2 (u m) (v m) (v n - v m)) x
    rw [show v m + (v n - v m) = v n from by abel] at hh
    exact hh
  show B (u n) (v n) x - B (u m) (v m) x = B (u n - u m) (v n) x + B (u m) (v n - v m) x
  rw [h1x, h2x]
  ring


end Work.KMTPlan.A6
