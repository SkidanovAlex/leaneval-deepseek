import Mathlib
import Submission.Work.ORHughesFree.SylvesterRank

universe u

namespace Work.Section3

open Work.ORHughesFree

/-- `oneByOne` is multiplicative: it is the `1 × 1` matrix representation of the ring. -/
theorem oneByOne_mul {S : Type u} [Semiring S] (x y : S) :
    oneByOne (x * y) = oneByOne x * oneByOne y := by
  ext i j
  simp [oneByOne, Matrix.mul_apply]

theorem rank_oneByOne_eq_of_span_eq {S : Type u} [Ring S] {s e : S}
    (hspan : Submodule.span S ({s} : Set S) = Submodule.span S ({e} : Set S))
    (ρ : Work.ORHughesFree.SylvesterRank S) :
    ρ.rk 1 1 (Work.ORHughesFree.oneByOne s) = ρ.rk 1 1 (Work.ORHughesFree.oneByOne e) := by
  have hmem_s : s ∈ Submodule.span S ({e} : Set S) := by
    rw [← hspan]; exact Submodule.subset_span (Set.mem_singleton s)
  have hmem_e : e ∈ Submodule.span S ({s} : Set S) := by
    rw [hspan]; exact Submodule.subset_span (Set.mem_singleton e)
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hmem_s
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp hmem_e
  have ha' : a * e = s := by simpa using ha
  have hb' : b * s = e := by simpa using hb
  refine le_antisymm ?_ ?_
  · calc ρ.rk 1 1 (oneByOne s) = ρ.rk 1 1 (oneByOne (a * e)) := by rw [ha']
      _ = ρ.rk 1 1 (oneByOne a * oneByOne e) := by rw [oneByOne_mul]
      _ ≤ ρ.rk 1 1 (oneByOne e) := ρ.rk_mul_le_right _ _
  · calc ρ.rk 1 1 (oneByOne e) = ρ.rk 1 1 (oneByOne (b * s)) := by rw [hb']
      _ = ρ.rk 1 1 (oneByOne b * oneByOne s) := by rw [oneByOne_mul]
      _ ≤ ρ.rk 1 1 (oneByOne s) := ρ.rk_mul_le_right _ _

end Work.Section3
