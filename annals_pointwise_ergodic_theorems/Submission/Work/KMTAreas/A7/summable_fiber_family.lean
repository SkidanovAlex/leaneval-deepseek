import Mathlib
import Submission.Work.KMTAreas.A7.LargeInterface

namespace Work.KMTAreas.A7

open Work.Analysis.IonescuWainger

/-- **The arithmetic character factor is bounded by the number of arithmetic frequencies.**
`arithChar ρ l y = ∑_{α ∈ (ℚ/ℤ)_{≤l}} e(α y)` is a finite sum of `#(ℚ/ℤ)_{≤l}` complex numbers of
modulus one, so its modulus is at most the cardinality of the frequency set.  This is the uniform
(in `y`) bound that makes every fiber kernel absolutely summable. -/
lemma arithChar_norm_le (ρ : ℝ) (l : ℕ) (y : ℤ) :
    ‖arithChar ρ l y‖ ≤ ((iwArithFreqs ρ l).card : ℝ) := by
  rw [arithChar]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ α ∈ iwArithFreqs ρ l, ‖fourier (T := 1) y α‖ = 1 := by
    intro α _
    rw [fourier_apply]
    exact Circle.norm_coe _
  have hsum : (∑ α ∈ iwArithFreqs ρ l, ‖fourier (T := 1) y α‖)
      = ∑ _α ∈ iwArithFreqs ρ l, (1 : ℝ) := Finset.sum_congr rfl hterm
  rw [hsum, Finset.sum_const, nsmul_eq_mul, mul_one]

/-- **The model decay of the lattice `ℤ`.**  The sequence `j ↦ (1 + |j|)⁻²` is summable on `ℤ`.
This is the comparison series for the decay hypothesis on the kernel `cw m`. -/
lemma summable_inv_one_add_abs_sq : Summable (fun j : ℤ => ((1 + |(j : ℝ)|)^2)⁻¹) := by
  have hbase : Summable (fun n : ℕ => ((n : ℝ)^2)⁻¹) :=
    Real.summable_nat_pow_inv.mpr (by norm_num)
  refine Summable.of_nat_of_neg_add_one ?_ ?_
  · refine ((summable_nat_add_iff (f := fun n : ℕ => ((n : ℝ)^2)⁻¹) 1).mpr hbase).congr ?_
    intro n
    have hcast : ((n : ℤ) : ℝ) = (n : ℝ) := by simp
    rw [hcast, abs_of_nonneg (Nat.cast_nonneg n)]
    congr 1
    push_cast
    ring
  · refine ((summable_nat_add_iff (f := fun n : ℕ => ((n : ℝ)^2)⁻¹) 2).mpr hbase).congr ?_
    intro n
    have hcast : ((-(↑n + 1) : ℤ) : ℝ) = -((n : ℝ) + 1) := by push_cast; ring
    rw [hcast, abs_neg, abs_of_nonneg (by positivity)]
    congr 1
    push_cast
    ring

/-- **The fibers of the twisted projection are absolutely summable.**  The kernel
`j ↦ arithChar ρ l (y-j) · cw m j` of the fiber operator is the product of a uniformly bounded
factor (`arithChar_norm_le`) and a factor decaying like `|j|⁻²`; the third factor `h (x-j)` is
bounded by hypothesis.  Hence every fiber of the family is summable. -/
theorem summable_fiber_family (ρ : ℝ) (l : ℕ) (m : ℝ → ℂ) (h : ℤ → ℂ) (x : ℤ)
    (hdec : ∃ Cd : ℝ, ∀ j : ℤ, ‖Work.KMTAreas.A7.cw m j‖ ≤ Cd / (1 + |(j : ℝ)|)^2)
    (hb : ∃ Ch : ℝ, ∀ y : ℤ, ‖h y‖ ≤ Ch) :
    ∀ y : ℤ, Summable (fun j : ℤ =>
      Work.KMTAreas.A7.arithChar ρ l (y - j) * Work.KMTAreas.A7.cw m j * h (x - j)) := by
  obtain ⟨Cd, hCd⟩ := hdec
  obtain ⟨Ch, hCh⟩ := hb
  -- replace the constants by their nonnegative parts, so that all bounds are nonnegative
  let Cd' : ℝ := max Cd 0
  let Ch' : ℝ := max Ch 0
  have hCd_le : ∀ j : ℤ, ‖cw m j‖ ≤ Cd' / (1 + |(j : ℝ)|)^2 := fun j =>
    (hCd j).trans (div_le_div_of_nonneg_right (le_max_left Cd 0) (by positivity))
  have hCh_le : ∀ y : ℤ, ‖h y‖ ≤ Ch' := fun y => (hCh y).trans (le_max_left Ch 0)
  have hCd0 : 0 ≤ Cd' := le_max_right Cd 0
  have hCh0 : 0 ≤ Ch' := le_max_right Ch 0
  intro y
  have hsum : Summable (fun j : ℤ =>
      ((iwArithFreqs ρ l).card : ℝ) * (Cd' * Ch') * ((1 + |(j : ℝ)|)^2)⁻¹) :=
    summable_inv_one_add_abs_sq.mul_left (((iwArithFreqs ρ l).card : ℝ) * (Cd' * Ch'))
  refine hsum.of_norm_bounded (fun j => ?_)
  have hA := arithChar_norm_le ρ l (y - j)
  have hB := hCd_le j
  have hC := hCh_le (x - j)
  have hA0 : 0 ≤ ‖arithChar ρ l (y - j)‖ := norm_nonneg _
  have hB0 : 0 ≤ ‖cw m j‖ := norm_nonneg _
  have hcard0 : 0 ≤ ((iwArithFreqs ρ l).card : ℝ) := Nat.cast_nonneg _
  calc ‖arithChar ρ l (y - j) * cw m j * h (x - j)‖
      = ‖arithChar ρ l (y - j)‖ * ‖cw m j‖ * ‖h (x - j)‖ := by rw [norm_mul, norm_mul]
    _ ≤ ((iwArithFreqs ρ l).card : ℝ) * (Cd' / (1 + |(j : ℝ)|)^2) * Ch' := by
        refine mul_le_mul (mul_le_mul hA hB hB0 hcard0) hC (norm_nonneg _) ?_
        exact mul_nonneg hcard0 (div_nonneg hCd0 (by positivity))
    _ = ((iwArithFreqs ρ l).card : ℝ) * (Cd' * Ch') * ((1 + |(j : ℝ)|)^2)⁻¹ := by
        rw [div_eq_mul_inv]
        ring

end Work.KMTAreas.A7
