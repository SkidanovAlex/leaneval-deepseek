import Submission.Work.ConeSwitch.MathlibNoHG

namespace Work.Deep.Reed.Prob.Certified

/-- Assembly of a single nibble/colouring step: if `Pb` is a positive lower
threshold, `Pa ≥ 0` is a lower bound for the weighted average `∑ w i * π i`
of the `π`, and each `I i` satisfies the pointwise bound
`Pb * I i ≤ 2 - π i / Pb`, then `Pa * ∑ w i * I i ≤ 1`.

The proof clears the denominator in the pointwise bound, weights it by the
probability weights `w`, multiplies by `Pa`, and uses the elementary
inequality `2 a b - a Π ≤ b²` valid for `0 ≤ a ≤ Π`. -/
theorem assembly_sum {ι : Type*} [Fintype ι] (w π I : ι → ℝ) (Pb Pa : ℝ)
    (hw : ∀ i, 0 ≤ w i) (h1 : ∑ i, w i = 1) (hPb : 0 < Pb) (hPa0 : 0 ≤ Pa)
    (hPa : Pa ≤ ∑ i, w i * π i) (hper : ∀ i, Pb * I i ≤ 2 - π i / Pb) :
    Pa * ∑ i, w i * I i ≤ 1 := by
  -- Pointwise bound with the denominator cleared: `Pb * Pb * I i ≤ 2 * Pb - π i`.
  have hI2 : ∀ i, Pb * Pb * I i ≤ 2 * Pb - π i := by
    intro i
    have h := mul_le_mul_of_nonneg_left (hper i) hPb.le
    have e : Pb * (2 - π i / Pb) = 2 * Pb - π i := by field_simp
    rw [← mul_assoc, e] at h
    exact h
  -- Weight by `w i ≥ 0` and sum, using `∑ i, w i = 1`.
  have hA : Pb * Pb * ∑ i, w i * I i ≤ 2 * Pb - ∑ i, w i * π i := by
    calc Pb * Pb * ∑ i, w i * I i
        = ∑ i, Pb * Pb * (w i * I i) := by rw [Finset.mul_sum]
      _ = ∑ i, w i * (Pb * Pb * I i) := Finset.sum_congr rfl fun i _ => by ring
      _ ≤ ∑ i, w i * (2 * Pb - π i) :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hI2 i) (hw i)
      _ = 2 * Pb - ∑ i, w i * π i := by
          simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, h1]
          ring
  -- Elementary inequality: `2 * Pa * Pb - Pa * Π ≤ Pb * Pb` for `0 ≤ Pa ≤ Π`.
  have hC : Pa * (2 * Pb - ∑ i, w i * π i) ≤ Pb * Pb := by
    have hpaπ : Pa * Pa ≤ Pa * (∑ i, w i * π i) := mul_le_mul_of_nonneg_left hPa hPa0
    have hsq : 0 ≤ Pa * Pa - 2 * Pa * Pb + Pb * Pb := by
      have h : 0 ≤ (Pa - Pb) * (Pa - Pb) := mul_self_nonneg _
      have e : (Pa - Pb) * (Pa - Pb) = Pa * Pa - 2 * Pa * Pb + Pb * Pb := by ring
      rwa [e] at h
    have hgoal : Pa * (2 * Pb - ∑ i, w i * π i) = 2 * Pa * Pb - Pa * (∑ i, w i * π i) := by
      ring
    rw [hgoal]
    linarith
  -- Combine and cancel the positive factor `Pb * Pb`.
  have hB : Pa * (Pb * Pb * ∑ i, w i * I i) ≤ Pa * (2 * Pb - ∑ i, w i * π i) :=
    mul_le_mul_of_nonneg_left hA hPa0
  have e2 : Pa * (Pb * Pb * ∑ i, w i * I i) = Pb * Pb * (Pa * ∑ i, w i * I i) := by ring
  rw [e2] at hB
  by_contra hcon
  have hcon' : 1 < Pa * ∑ i, w i * I i := not_le.mp hcon
  have hlt : Pb * Pb * 1 < Pb * Pb * (Pa * ∑ i, w i * I i) :=
    mul_lt_mul_of_pos_left hcon' (mul_pos hPb hPb)
  rw [mul_one] at hlt
  linarith

end Work.Deep.Reed.Prob.Certified
