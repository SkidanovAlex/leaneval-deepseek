import Mathlib
import Submission.Work.LinnikAreas.Density4.SelbergDefs

namespace Work.LinnikAreas.Density4

open scoped BigOperators
open Finset

/-- **Reindexing the `l`-divisible part of the Selberg sum.**  Writing `d = l·m`, the sum of the
Selberg weights `λ_d/d = μ(d)log(z/d)/d` over the `d ≤ z` divisible by `l` becomes `(1/l)` times the
sum over `m ≤ z/l` of `μ(l·m)log(z/(l·m))/m`. -/
theorem selLam_div_sum_reindex (z l : ℕ) (hl : 1 ≤ l) :
    (∑ d ∈ (Finset.Icc 1 z).filter (fun d => l ∣ d),
        Work.LinnikAreas.Density4.selLam z d / (d : ℝ))
      = (1 / (l : ℝ)) *
          ∑ m ∈ Finset.Icc 1 (z / l),
            (ArithmeticFunction.moebius (l * m) : ℝ) *
              Real.log ((z : ℝ) / ((l * m : ℕ) : ℝ)) / (m : ℝ) := by
  have hl0 : 0 < l := by omega
  have hset : (Finset.Icc 1 z).filter (fun d => l ∣ d)
      = (Finset.Icc 1 (z / l)).image (fun m => l * m) := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨hd1, hdz⟩, ⟨m, rfl⟩⟩
      refine ⟨m, ⟨?_, ?_⟩, rfl⟩
      · rcases Nat.eq_zero_or_pos m with hm | hm
        · subst hm; simp at hd1
        · exact hm
      · rw [Nat.le_div_iff_mul_le hl0]
        exact Nat.mul_comm m l ▸ hdz
    · rintro ⟨m, ⟨hm1, hmz⟩, rfl⟩
      refine ⟨⟨?_, ?_⟩, m, rfl⟩
      · simpa using Nat.mul_le_mul hl hm1
      · rw [Nat.le_div_iff_mul_le hl0] at hmz
        exact Nat.mul_comm l m ▸ hmz
  rw [hset, Finset.sum_image (by
    intro a _ b _ h
    exact Nat.mul_left_cancel hl0 h)]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro m hm
  have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
  have hl0' : (l : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
    linarith
  have hm0 : (m : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
    linarith
  simp only [selLam]
  rw [Nat.cast_mul]
  field_simp

end Work.LinnikAreas.Density4
