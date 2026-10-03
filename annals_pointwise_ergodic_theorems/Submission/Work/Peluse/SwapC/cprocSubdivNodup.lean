import Mathlib
import Submission.Work.Peluse.SwapC.agreeExistsMemChildren
import Submission.Work.Peluse.SwapC.pairDisjSplit
import Submission.Work.Peluse.SwapC.csplitFirstEqOfForall
import Submission.Work.Peluse.SwapC.isSubdivIffCoversPairDisj

namespace Work.Peluse.SwapC

set_option autoImplicit false
set_option maxHeartbeats 1000000

variable {s : ℕ}

/-! ## Splitting the first leaf of depth `< s` preserves the subdivision

The work is in `isSubdiv_split`: replacing a leaf `m` of a `Nodup` subdivision by its two children
keeps the list a subdivision.  Writing `IsSubdiv = Covers ∧ PairDisj`
(`isSubdivIffCoversPairDisj`), the cover half is `covers_csplit` (a point of the cell of `m` lies
in the cell of one of its children, `agreeExistsMemChildren`; the other cells are unchanged) and
the disjointness half is `pairDisjSplit` (the two children have cells inside the cell of `m`, and
`m` does not occur in the two tails thanks to `Nodup`). -/

/-- A point of `{0,1}^s` lying in a cell of `P ++ m :: Q` lies in a cell of `P ++ m.children h ++ Q`. -/
theorem covers_csplit {P Q : List (CLeaf s)} {m : CLeaf s} (hm : m.dep < s)
    (hc : Covers (P ++ m :: Q)) : Covers (P ++ m.children hm ++ Q) := by
  intro x
  obtain ⟨l, hl, hx⟩ := hc x
  rcases List.mem_append.mp hl with hlP | hl
  · exact ⟨l, List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hlP))), hx⟩
  · rcases List.mem_cons.mp hl with rfl | hlQ
    · obtain ⟨a, ha, hxa⟩ := agreeExistsMemChildren (h := hm) hx
      exact ⟨a, List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr ha))), hxa⟩
    · exact ⟨l, List.mem_append.mpr (Or.inr hlQ), hx⟩

/-- **Splitting a leaf of depth `< s` in a subdivision without repetitions gives a subdivision.** -/
theorem isSubdiv_split {P Q : List (CLeaf s)} {m : CLeaf s} (hm : m.dep < s)
    (hsub : IsSubdiv (P ++ m :: Q)) (hnod : (P ++ m :: Q).Nodup) :
    IsSubdiv (P ++ m.children hm ++ Q) := by
  obtain ⟨hP, hQ, hdisj⟩ := List.nodup_append.mp hnod
  obtain ⟨hmQ, -⟩ := List.nodup_cons.mp hQ
  have hmP : m ∉ P := fun hmem => (hdisj m hmem m (List.mem_cons_self ..)) rfl
  refine isSubdivIffCoversPairDisj.mpr
    ⟨covers_csplit hm (isSubdivIffCoversPairDisj.mp hsub).1,
      pairDisjSplit hm hmP hmQ (pairDisj_of_isSubdiv hsub)⟩

/-! ## The decomposition at the first splittable leaf -/

/-- If `Λ` has a leaf of depth `< s`, then it is `P ++ m :: Q` with `m` the first such leaf
(`m.dep < s` and every leaf of `P` of depth `s`). -/
theorem exists_split_decomp : ∀ (Λ : List (CLeaf s)), HasSplit Λ →
    ∃ (P : List (CLeaf s)) (m : CLeaf s) (Q : List (CLeaf s)) (hm : m.dep < s),
      Λ = P ++ m :: Q ∧ (∀ a ∈ P, ¬ a.dep < s) := by
  intro Λ
  induction Λ with
  | nil => intro h; rw [HasSplit] at h; simp at h
  | cons a rest ih =>
    intro h
    by_cases ha : a.dep < s
    · exact ⟨[], a, rest, ha, rfl, by simp⟩
    · have h' : HasSplit rest := by
        rcases h with ⟨l, hl, hld⟩
        rcases List.mem_cons.mp hl with rfl | hl
        · exact absurd hld ha
        · exact ⟨l, hl, hld⟩
      obtain ⟨P, m, Q, hm, hdec, hP⟩ := ih h'
      refine ⟨a :: P, m, Q, hm, ?_, ?_⟩
      · rw [hdec]; rfl
      · intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · exact ha
        · exact hP b hb

/-- If no leaf of `Λ` has depth `< s` then `csplitFirst` leaves `Λ` unchanged. -/
theorem csplitFirst_eq_self_of_not_hasSplit : ∀ (Λ : List (CLeaf s)),
    ¬ HasSplit Λ → csplitFirst Λ = Λ := by
  intro Λ
  induction Λ with
  | nil => intro _; rfl
  | cons a rest ih =>
    intro h
    have ha : ¬ a.dep < s := fun hlt => h ⟨a, List.mem_cons_self .., hlt⟩
    have h' : ¬ HasSplit rest := fun hr => h (by
      rcases hr with ⟨l, hl, hld⟩
      exact ⟨l, List.mem_cons_of_mem a hl, hld⟩)
    rw [csplitFirst.eq_2, dif_neg ha, ih h']

/-! ## The step and the induction -/

/-- One application of `csplitFirst` to a `Nodup` subdivision is again a subdivision. -/
theorem isSubdiv_csplitFirst {Λ : List (CLeaf s)} (hsub : IsSubdiv Λ) (hnod : Λ.Nodup) :
    IsSubdiv (csplitFirst Λ) := by
  by_cases hsp : HasSplit Λ
  · obtain ⟨P, m, Q, hm, hdec, hP⟩ := exists_split_decomp Λ hsp
    rw [hdec, csplitFirstEqOfForall hP hm]
    exact isSubdiv_split hm (by rw [← hdec]; exact hsub) (by rw [← hdec]; exact hnod)
  · rw [csplitFirst_eq_self_of_not_hasSplit Λ hsp]
    exact hsub

/-- The one-leaf list at the root is a subdivision of `{0,1}^s`. -/
theorem isSubdiv_cproc_zero (s : ℕ) : IsSubdiv (cproc s 0) := by
  rw [cproc.eq_1]
  intro x
  refine ⟨_, ⟨List.mem_singleton_self _, fun i hi => ?_⟩, ?_⟩
  · exact absurd hi (by simp)
  · intro y hy
    rw [List.mem_singleton] at hy
    exact hy.1

/-- Every stage of the depth-first refinement process `cproc s ·` is a subdivision of `{0,1}^s`
(`IsSubdiv`: the cells of the leaves, `{x | x = str on the first dep coordinates}`, partition
`{0,1}^s`) and its leaf list has no repeated leaves.

Route: `cproc s 0` is the one-leaf list at the root (cell = everything, no duplicates); and if `Λ`
is a subdivision without duplicates and `csplitFirst Λ` replaces the first leaf `l` with `l.dep < s`
by its two children (whose cells partition `cell l`, `cell l = {x | x agrees with l.str below
l.dep}`, the two children differing at coordinate `l.dep`), then the result is again a subdivision
without duplicates — the children are not equal to each other and are not elements of `rest` (their
cells are nonempty subsets of `cell l`, and `cell l` meets no cell of `rest` in the `∃!`-sense).
This is most easily done with the relative invariant `Cover Λ U`: `∀ x ∈ U, ∃! l ∈ Λ, x ∈ cell l`,
`∀ l ∈ Λ, cell l ⊆ U`, `Λ.Nodup`, which is preserved by `csplitFirst` (in the `l.dep ≥ s` branch
`rest` satisfies `Cover rest (U \ cell l)`). -/
theorem cprocSubdivNodup (s k : ℕ) :
    Work.Peluse.SwapC.IsSubdiv (Work.Peluse.SwapC.cproc s k) ∧
      (Work.Peluse.SwapC.cproc s k).Nodup := by
  induction k with
  | zero =>
    refine ⟨isSubdiv_cproc_zero s, ?_⟩
    rw [cproc.eq_1]
    simp
  | succ k ih =>
    rw [cproc.eq_2]
    exact ⟨isSubdiv_csplitFirst ih.1 ih.2,
      nodup_csplitFirst ih.2 (pairDisj_of_isSubdiv ih.1)⟩

end Work.Peluse.SwapC
