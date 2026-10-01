import Mathlib
import Submission.Work.ZeroDensity.Jutila.mixedSelbergDefs

namespace Work.ZeroDensity.Jutila

open Finset

/-- **Real-cutoff reindexing of the `l`-divisible part of the Selberg sum.**  For `1 ≤ l`, writing
`d = l·m`, the sum of the real-cutoff Selberg weights `selW w d / d = μ(d)·log(w/d)/d` over the
`1 ≤ d ≤ ⌊w⌋₊` divisible by `l` becomes `1/l` times the sum over `m ≤ ⌊w⌋₊/l` of
`μ(l·m)·log(w/(l·m))/m`; here `selW w d = μ(d)·log(w/d)`.  This is a verbatim adaptation of
`Work.LinnikAreas.Density4.selLam_div_sum_reindex` (same file layout, `Submission/Work/LinnikAreas/Density4/selLam_div_sum_reindex.lean`)
to the real cutoff `w`. -/
theorem selW_div_sum_reindex (w : ℝ) (l : ℕ) (hl : 1 ≤ l) :
    (∑ d ∈ (Finset.Icc 1 ⌊w⌋₊).filter (fun d => l ∣ d), Work.ZeroDensity.Jutila.selW w d / (d : ℝ))
      = (1 / (l : ℝ)) *
          ∑ m ∈ Finset.Icc 1 (⌊w⌋₊ / l),
            (ArithmeticFunction.moebius (l * m) : ℝ) *
              Real.log (w / ((l * m : ℕ) : ℝ)) / (m : ℝ) := by
  have hl0 : 0 < l := by omega
  have hset : (Finset.Icc 1 ⌊w⌋₊).filter (fun d => l ∣ d)
      = (Finset.Icc 1 (⌊w⌋₊ / l)).image (fun m => l * m) := by
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
  simp only [selW]
  rw [Nat.cast_mul]
  field_simp

end Work.ZeroDensity.Jutila
