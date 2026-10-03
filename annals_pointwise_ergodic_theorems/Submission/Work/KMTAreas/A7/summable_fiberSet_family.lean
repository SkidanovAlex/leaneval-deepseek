import Mathlib
import Submission.Work.KMTAreas.A7.FiberGeneral
import Submission.Work.KMTAreas.A7.summable_fiber_family

namespace Work.KMTAreas.A7

/-- **The fibers with an arbitrary arithmetic frequency set are absolutely summable.**
The kernel `j ↦ arithCharSet A (y-j) · cw m j` of the fiber operator is the product of a
uniformly bounded factor (the hypothesis `hC` on `arithCharSet A`) and a factor decaying like
`|j|⁻²` (the hypothesis `hdec` on `cw m`); the third factor `h (x-j)` is bounded by `hb`.
Hence every fiber of the family is summable.  This is the `A`-general version of
`summable_fiber_family`, needed for the exact-height frequency sets `iwArithFreqsNew`. -/
theorem summable_fiberSet_family (A : Finset Work.Analysis.IonescuWainger.Circle)
    (m : ℝ → ℂ) (h : ℤ → ℂ) (x : ℤ)
    (hdec : ∃ Cd : ℝ, ∀ j : ℤ, ‖Work.KMTAreas.A7.cw m j‖ ≤ Cd / (1 + |(j : ℝ)|)^2)
    (hC : ∃ Ca : ℝ, ∀ y : ℤ, ‖Work.KMTAreas.A7.arithCharSet A y‖ ≤ Ca)
    (hb : ∃ Ch : ℝ, ∀ y : ℤ, ‖h y‖ ≤ Ch) :
    ∀ y : ℤ, Summable (fun j : ℤ =>
      Work.KMTAreas.A7.arithCharSet A (y - j) * Work.KMTAreas.A7.cw m j * h (x - j)) := by
  obtain ⟨Cd, hCd⟩ := hdec
  obtain ⟨Ca, hCa⟩ := hC
  obtain ⟨Ch, hCh⟩ := hb
  -- replace the constants by their nonnegative parts, so that all bounds are nonnegative
  let Cd' : ℝ := max Cd 0
  let Ca' : ℝ := max Ca 0
  let Ch' : ℝ := max Ch 0
  have hCd_le : ∀ j : ℤ, ‖cw m j‖ ≤ Cd' / (1 + |(j : ℝ)|)^2 := fun j =>
    (hCd j).trans (div_le_div_of_nonneg_right (le_max_left Cd 0) (by positivity))
  have hCa_le : ∀ y : ℤ, ‖arithCharSet A y‖ ≤ Ca' := fun y =>
    (hCa y).trans (le_max_left Ca 0)
  have hCh_le : ∀ y : ℤ, ‖h y‖ ≤ Ch' := fun y => (hCh y).trans (le_max_left Ch 0)
  have hCd0 : 0 ≤ Cd' := le_max_right Cd 0
  have hCa0 : 0 ≤ Ca' := le_max_right Ca 0
  have hCh0 : 0 ≤ Ch' := le_max_right Ch 0
  intro y
  have hsum : Summable (fun j : ℤ =>
      Ca' * (Cd' * Ch') * ((1 + |(j : ℝ)|)^2)⁻¹) :=
    summable_inv_one_add_abs_sq.mul_left (Ca' * (Cd' * Ch'))
  refine hsum.of_norm_bounded (fun j => ?_)
  have hA := hCa_le (y - j)
  have hB := hCd_le j
  have hCb := hCh_le (x - j)
  have hA0 : 0 ≤ ‖arithCharSet A (y - j)‖ := norm_nonneg _
  have hB0 : 0 ≤ ‖cw m j‖ := norm_nonneg _
  calc ‖arithCharSet A (y - j) * cw m j * h (x - j)‖
      = ‖arithCharSet A (y - j)‖ * ‖cw m j‖ * ‖h (x - j)‖ := by rw [norm_mul, norm_mul]
    _ ≤ Ca' * (Cd' / (1 + |(j : ℝ)|)^2) * Ch' := by
        refine mul_le_mul (mul_le_mul hA hB hB0 hCa0) hCb (norm_nonneg _) ?_
        exact mul_nonneg hCa0 (div_nonneg hCd0 (by positivity))
    _ = Ca' * (Cd' * Ch') * ((1 + |(j : ℝ)|)^2)⁻¹ := by
        rw [div_eq_mul_inv]
        ring

end Work.KMTAreas.A7
