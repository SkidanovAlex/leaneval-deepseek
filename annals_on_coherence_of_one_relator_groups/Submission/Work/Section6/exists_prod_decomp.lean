import Mathlib
import Submission.Work.ORHughesFree.Section6.Reduce

namespace Work.Section6

/-- If every `h : H` factors as `n * t ^ k` with `n ∈ N`, then the same holds, componentwise, for
the product group `Kˣ × H`, with the subgroup played by `unitsTimesSubgroup N`. -/
theorem exists_prod_decomp {K : Type} [Monoid K] {H : Type} [Group H] (N : Subgroup H) (t : H)
    (hdecomp : ∀ h : H, ∃ (n : N) (k : ℤ), h = (n : H) * t ^ k)
    (u : Kˣ × H) :
    ∃ (n : Kˣ × H) (k : ℤ),
      n ∈ Work.ORHughesFree.unitsTimesSubgroup (K := K) N ∧
        u = n * (((1 : Kˣ), t) : Kˣ × H) ^ k := by
  obtain ⟨a, b⟩ := u
  obtain ⟨n, k, hk⟩ := hdecomp b
  refine ⟨(a, (n : H)), k, ?_, ?_⟩
  · rw [Work.ORHughesFree.mem_unitsTimesSubgroup]
    exact n.2
  · rw [hk]
    simp

end Work.Section6
