import Mathlib
import Submission.Work.EKLComp.FinPartLevel

namespace Work.EKLComp

open Set

/-- The `m`-th cell `levelCell e U C m` is precisely the set of `x ∈ U (e.symm m)` that belong to
no earlier `U`; choosing `m` minimal among the indices `i` with `x ∈ U i` exhibits every point of
`⋃ i, U i` as an element of one of the cells.  Combined with the trivial case `x ∈ ⋂ i, C i`,
this gives the covering. -/
theorem levelCell_cover {X ι : Type*} [Fintype ι] (e : ι ≃ Fin (Fintype.card ι))
    (U C : ι → Set X) (hUC : ∀ i, C i = (U i)ᶜ) (x : X) :
    x ∈ Work.EKLComp.levelCore C ∨
      ∃ m : Fin (Fintype.card ι), x ∈ Work.EKLComp.levelCell e U C m := by
  classical
  by_cases h : x ∈ Work.EKLComp.levelCore C
  · exact Or.inl h
  · right
    rw [Work.EKLComp.levelCore, Set.mem_iInter] at h
    push Not at h
    obtain ⟨i, hi⟩ := h
    -- `x ∉ C i` means `x ∈ U i`, since `C i` is the complement of `U i`.
    have hiU : x ∈ U i := by
      have hc := hUC i
      rw [hc] at hi
      simpa using hi
    -- The (finite, nonempty) set of indices `m` with `x ∈ U (e.symm m)`.
    let S : Finset (Fin (Fintype.card ι)) := Finset.univ.filter (fun m => x ∈ U (e.symm m))
    have hSne : S.Nonempty := ⟨e i, by simp [S, hiU]⟩
    refine ⟨S.min' hSne, ?_⟩
    rw [Work.EKLComp.levelCell, Set.mem_inter_iff, Set.mem_iInter]
    constructor
    · -- `x ∈ U (e.symm m)` for the minimal `m`.
      have hm := Finset.min'_mem S hSne
      simpa [S] using hm
    · -- every earlier index `j < m` fails to be in `S`, i.e. `x ∉ U (e.symm j)`, i.e. `x ∈ C ...`
      intro j
      have hjS : j.1 ∉ S := by
        intro hjs
        exact absurd (Finset.min'_le S j.1 hjs) (not_le.mpr j.2)
      have hjU : x ∉ U (e.symm j.1) := fun hju => hjS (by simp [S, hju])
      have hc : C (e.symm j.1) = (U (e.symm j.1))ᶜ := hUC _
      rw [hc]
      simpa using hjU

end Work.EKLComp
