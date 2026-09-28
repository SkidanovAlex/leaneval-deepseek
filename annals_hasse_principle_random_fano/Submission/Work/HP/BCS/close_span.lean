import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.MMDefs
import Submission.Work.HP.BCS.Setup

namespace Work.HP.BCS

/-! ## Rounding and integer combinations

The covering-radius statement `close_span` below rests on two elementary facts:
integer linear combinations of vectors commute with the coercion `toEr`, and every real
number is within `1/2` of the nearest integer `⌊t + 1/2⌋`. -/

/-- `toEr` commutes with finite integer linear combinations. -/
theorem toEr_sum_zsmul {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*} [Fintype κ]
    (n : κ → ℤ) (v : κ → ι → ℤ) :
    toEr (∑ j, n j • v j) = ∑ j, (n j : ℝ) • toEr (v j) := by
  rw [← toErLin_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul, toErLin_apply]
  exact (Int.cast_smul_eq_zsmul ℝ (n j) (toEr (v j))).symm

/-- Rounding a real number to the nearest integer: `|t - ⌊t + 1/2⌋| ≤ 1/2`. -/
theorem abs_sub_floor_half_le (t : ℝ) : |t - ((⌊t + 1/2⌋ : ℤ) : ℝ)| ≤ 1 / 2 := by
  have h1 := Int.floor_le (t + 1/2)
  have h2 := Int.lt_floor_add_one (t + 1/2)
  rw [abs_le]
  constructor <;> linarith

/-- Every point `x` of the real span of `L` is within `(1/2) * ∑ j, ‖f j‖` of some point of `L`,
provided the `f j ∈ L` have Euclidean images spanning that real span. -/
theorem close_span {ι : Type*} [Fintype ι] [DecidableEq ι] (L : Submodule ℤ (ι → ℤ)) {k : ℕ}
    (f : Fin k → ι → ℤ) (hfL : ∀ j, f j ∈ L)
    (hspan : spanE L = Submodule.span ℝ (Set.range (fun j => toEr (f j)))) :
    ∀ x ∈ spanE L, ∃ a ∈ L, ‖x - toEr a‖ ≤ (1 / 2) * ∑ j, eNorm (f j) := by
  intro x hx
  -- `x` is a real linear combination of the `toEr (f j)`.
  rw [hspan, Submodule.mem_span_range_iff_exists_fun ℝ] at hx
  obtain ⟨c, hc⟩ := hx
  -- Round each coefficient to the nearest integer and take the resulting integer combination.
  refine ⟨∑ j, (⌊c j + 1/2⌋ : ℤ) • f j, ?_, ?_⟩
  · exact Submodule.sum_mem L fun j _ => Submodule.smul_mem L _ (hfL j)
  · have htoEr : toEr (∑ j, (⌊c j + 1/2⌋ : ℤ) • f j)
        = ∑ j, ((⌊c j + 1/2⌋ : ℤ) : ℝ) • toEr (f j) := toEr_sum_zsmul _ _
    rw [htoEr, ← hc, ← Finset.sum_sub_distrib]
    calc ‖∑ j, (c j • toEr (f j) - ((⌊c j + 1/2⌋ : ℤ) : ℝ) • toEr (f j))‖
        = ‖∑ j, (c j - ((⌊c j + 1/2⌋ : ℤ) : ℝ)) • toEr (f j)‖ := by
          congr 1
          exact Finset.sum_congr rfl fun j _ => by rw [sub_smul]
      _ ≤ ∑ j, ‖(c j - ((⌊c j + 1/2⌋ : ℤ) : ℝ)) • toEr (f j)‖ := norm_sum_le _ _
      _ = ∑ j, |c j - ((⌊c j + 1/2⌋ : ℤ) : ℝ)| * eNorm (f j) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [norm_smul, Real.norm_eq_abs, norm_toEr]
      _ ≤ ∑ j, (1 / 2) * eNorm (f j) := by
          refine Finset.sum_le_sum fun j _ => ?_
          exact mul_le_mul_of_nonneg_right (abs_sub_floor_half_le (c j)) (eNorm_nonneg _)
      _ = (1 / 2) * ∑ j, eNorm (f j) := by rw [Finset.mul_sum]

end Work.HP.BCS
