import Mathlib
import Submission.Work.WilE7.DecompDefs
import Submission.Work.CoreStep.preconnectedSpace_closed_cover

set_option linter.style.haveILetI false

namespace Work.CoreStep

open Set

/-- If finitely many continuous level functions cover a preconnected set, and any two of them
which take the value `v` at a common point agree with the value `v` at that point, then one of
the functions is constantly equal to `v` on the set.

The level sets `{x ∈ C | s j x (last m) = v}` are closed in `C` (continuity), cover `C` (by
`hcov`), and any two that meet are equal (by `hdich`); the connectedness argument reducing this
finite closed cover to a single member is `preconnectedSpace_closed_cover`. -/
theorem level_eq_const_of_cover {n m k : ℕ} {C : Set (Fin n → ℝ)}
    {s : Fin k → (Fin n → ℝ) → (Fin (m + 1) → ℝ)} (hk : 0 < k)
    (hCpre : IsPreconnected C) (hcont : ∀ j, ContinuousOn (s j) C)
    (hdich : ∀ j j' : Fin k,
      (∃ x ∈ C, (s j x) (Fin.last m) = (s j' x) (Fin.last m)) →
      ∀ x ∈ C, (s j x) (Fin.last m) = (s j' x) (Fin.last m))
    {v : ℝ} (hcov : ∀ x ∈ C, ∃ j : Fin k, (s j x) (Fin.last m) = v) :
    ∃ j : Fin k, ∀ x ∈ C, (s j x) (Fin.last m) = v := by
  by_cases hCne : C.Nonempty
  · obtain ⟨x0, hx0⟩ := hCne
    haveI : PreconnectedSpace C := isPreconnected_iff_preconnectedSpace.mp hCpre
    haveI : Nonempty C := ⟨⟨x0, hx0⟩⟩
    -- The level sets, as subsets of the subspace `C`.
    have hcl : ∀ j : Fin k, IsClosed {x : C | (s j x.1) (Fin.last m) = v} := by
      intro j
      have hj : Continuous (fun x : C => (s j x.1) (Fin.last m)) :=
        (continuous_apply (Fin.last m)).comp (hcont j).domRestrict
      exact isClosed_eq hj continuous_const
    have hmeet : ∀ j j' : Fin k,
        ({x : C | (s j x.1) (Fin.last m) = v} ∩ {x : C | (s j' x.1) (Fin.last m) = v}).Nonempty →
        {x : C | (s j x.1) (Fin.last m) = v} = {x : C | (s j' x.1) (Fin.last m) = v} := by
      intro j j' h
      obtain ⟨y, hyj, hyj'⟩ := h
      have hd := hdich j j' ⟨y.1, y.2, by rw [hyj, hyj']⟩
      ext x
      change (s j x.1) (Fin.last m) = v ↔ (s j' x.1) (Fin.last m) = v
      constructor <;> intro hx
      · rw [← hd x.1 x.2]; exact hx
      · rw [hd x.1 x.2]; exact hx
    have hcovU : (⋃ j : Fin k, {x : C | (s j x.1) (Fin.last m) = v}) = univ := by
      ext x
      simp only [Set.mem_iUnion, Set.mem_univ]
      constructor
      · intro _; trivial
      · intro _
        obtain ⟨j, hj⟩ := hcov x.1 x.2
        exact ⟨j, hj⟩
    obtain ⟨j, hj⟩ := preconnectedSpace_closed_cover
      (U := fun j : Fin k => {x : C | (s j x.1) (Fin.last m) = v}) hcl hmeet hcovU
    refine ⟨j, fun x hx => ?_⟩
    have hxU : (⟨x, hx⟩ : C) ∈ {y : C | (s j y.1) (Fin.last m) = v} := by
      rw [hj]; trivial
    exact hxU
  · -- `C` is empty: the conclusion is vacuous, and `Fin k` is inhabited since `k > 0`.
    refine ⟨⟨0, hk⟩, ?_⟩
    intro x hx
    exact absurd ⟨x, hx⟩ hCne

end Work.CoreStep
