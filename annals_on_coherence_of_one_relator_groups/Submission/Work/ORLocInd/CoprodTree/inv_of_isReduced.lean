import Mathlib
import Submission.Work.ORLocInd.CoprodTree.StarTreePath
import Submission.Work.ORLocInd.CoprodTree.inv_structural

set_option linter.unusedVariables false

universe u

namespace Work.ORLocInd.CoprodTree

open Quiver

/-! ## Arrows whose (co)domain is given by an equation

The lemmas `arrow_some_left`, `arrow_to_some`, `arrow_none_left`, `arrow_to_none` of
`StarTreeDefs` describe an arrow whose source (resp. target) is *syntactically* of the form
`vtx (some i) g` (resp. `vtx none g`).  Here we record the same description when the relevant
endpoint is only *equal* to such a vertex. -/

private theorem arrow_some_left_of_eq {ι : Type u} {M : ι → Type u} [∀ i, Group (M i)]
    {x y : Vertex M} {i : ι} {g : Monoid.CoprodI M} (e : x ⟶ y)
    (hx : x = vtx (some i) g) :
    e.idx = i ∧ (∃ m : M i, e.lbl = g * Monoid.CoprodI.of m) ∧ y = vtx none e.lbl := by
  subst hx
  exact arrow_some_left e

private theorem arrow_to_some_of_eq {ι : Type u} {M : ι → Type u} [∀ i, Group (M i)]
    {x y : Vertex M} {i : ι} {g : Monoid.CoprodI M} (e : x ⟶ y)
    (hy : y = vtx (some i) g) :
    e.idx = i ∧ (∃ m : M i, e.lbl = g * Monoid.CoprodI.of m) ∧ x = vtx none e.lbl := by
  subst hy
  exact arrow_to_some e

private theorem arrow_none_left_of_eq {ι : Type u} {M : ι → Type u} [∀ i, Group (M i)]
    {x y : Vertex M} {g : Monoid.CoprodI M} (e : x ⟶ y) (hx : x = vtx none g) :
    e.lbl = g ∧ y = vtx (some e.idx) e.lbl := by
  subst hx
  exact arrow_none_left e

private theorem arrow_to_none_of_eq {ι : Type u} {M : ι → Type u} [∀ i, Group (M i)]
    {x y : Vertex M} {g : Monoid.CoprodI M} (e : x ⟶ y) (hy : y = vtx none g) :
    e.lbl = g ∧ x = vtx (some e.idx) e.lbl := by
  subst hy
  exact arrow_to_none e

/-! ## The reduction-dependent part of the invariant

`inv_structural` (in `Submission.Work.ORLocInd.CoprodTree.inv_structural`) supplies, for *every*
path, the parts of `Inv` that do not use reducedness.  What remains are the four conditions that
do use it: consecutive letters lie in different factors, all letters of a path starting at a
central vertex are non-trivial, only the first letter can be trivial, and the last letter is
never the step of the last arrow when the endpoint is a leaf.  These are established here for a
path of the form `q.cons e` by induction on `q`; the last arrow `e'` of `q` is available
explicitly in the inductive step, which is what the reducedness of `q.cons e` is needed for. -/

private theorem inv_reduced_cons {ι : Type u} {M : ι → Type u} [∀ i, Group (M i)] {k : Option ι}
    {g : Monoid.CoprodI M} {x : Vertex M} (q : Quiver.Path (vtx k g) x) :
    ∀ {y : Vertex M} (e : x ⟶ y), (q.cons e).IsReduced →
      (letters k g (q.cons e)).IsChain (fun a b => a.1 ≠ b.1) ∧
      (k = none → ∀ z ∈ letters k g (q.cons e), z.2 ≠ 1) ∧
      (∀ z ∈ (letters k g (q.cons e)).tail, z.2 ≠ 1) ∧
      (isLeafSide k (q.cons e).length = true → (q.cons e).length ≠ 0 →
        llidx k g (q.cons e) ≠ lidx k g (q.cons e)) := by
  induction q with
  | nil =>
    intro y e hred
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- consecutive letters of a single arrow have different indices
      cases k with
      | none =>
        rw [letters_cons, dif_neg (by simp [isLeafSide]), letters_nil, List.nil_append]
        exact List.isChain_nil
      | some i =>
        rw [letters_cons, dif_pos (by simp [isLeafSide]), letters_nil, List.nil_append]
        exact List.isChain_singleton _
    · -- no letter of a path starting at the centre is trivial
      intro hk
      cases k with
      | none =>
        rw [letters_cons, dif_neg (by simp [isLeafSide]), letters_nil, List.nil_append]
        intro z hz
        simp at hz
      | some i => exact absurd hk (by simp)
    · -- only the first letter can be trivial
      intro z hz
      cases k with
      | none =>
        rw [letters_cons, dif_neg (by simp [isLeafSide]), letters_nil, List.nil_append] at hz
        simp at hz
      | some i =>
        rw [letters_cons, dif_pos (by simp [isLeafSide]), letters_nil, List.nil_append] at hz
        simp at hz
    · -- at a leaf endpoint the last letter is not the last arrow
      intro hb hlen
      cases k with
      | none =>
        rw [llidx_cons, dif_neg (by simp [isLeafSide]), llidx_nil, lidx_cons]
        simp
      | some i =>
        exfalso
        have h1 : ((Quiver.Path.nil : Quiver.Path (vtx (some i) g) (vtx (some i) g)).cons e).length
            = 1 := rfl
        rw [h1] at hb
        exact absurd hb (by simp [isLeafSide])
  | cons q' e' ih =>
    intro y e hred
    have hred' : (q'.cons e').IsReduced := by
      have h := hred
      rw [← Quiver.Path.comp_toPath_eq_cons (q'.cons e') e] at h
      exact Quiver.Path.IsReduced.of_comp h
    have hp := ih e' hred'
    have hne : e.1 ≠ e'.1 := fun h => not_isReduced_of_data_eq q' e' e h hred
    have hst := inv_structural (q'.cons e')
    by_cases hb : isLeafSide k (q'.cons e').length = true
    · -- the last arrow runs from a leaf to a central vertex
      obtain ⟨⟨i, hx⟩, -⟩ := hst.1 hb
      obtain ⟨hidx, ⟨m, hlbl⟩, -⟩ := arrow_some_left_of_eq e hx
      obtain ⟨hidx', -, -⟩ := arrow_to_some_of_eq e' hx
      have hofm_ne : Monoid.CoprodI.of m ≠ 1 := by
        intro h1
        apply hne
        apply Prod.ext
        · show e.idx = e'.idx
          rw [hidx, hidx']
        · show e.lbl = e'.lbl
          rw [hlbl, h1, mul_one]
          rfl
      have hnew : (stt k g (q'.cons e'))⁻¹ * e.lbl = Monoid.CoprodI.of m := by
        rw [hlbl, ← mul_assoc, inv_mul_cancel, one_mul]
      refine ⟨?_, ?_, ?_, ?_⟩
      · -- the new letter is preceded by a letter of a different index
        rw [letters_cons, dif_pos hb]
        refine List.isChain_append.2 ⟨hp.1, List.isChain_singleton _, ?_⟩
        intro z hz y' hy'
        have hy'' : (e.idx, (stt k g (q'.cons e'))⁻¹ * e.lbl) = y' := by
          simpa [Option.mem_def] using hy'
        subst hy''
        show z.1 ≠ e.idx
        intro hcon
        have hll : llidx k g (q'.cons e') = some z.1 := by
          have h := llidx_eq_getLast k g (q'.cons e')
          have hz' : (letters k g (q'.cons e')).getLast? = some z := by
            simpa [Option.mem_def] using hz
          rw [hz'] at h
          exact h.symm
        have hne_ll := hp.2.2.2 hb (by simp)
        have hlidx : lidx k g (q'.cons e') = some e.idx := by rw [lidx_cons, hidx', hidx]
        rw [hlidx] at hne_ll
        exact hne_ll (hll.trans (congrArg some hcon))
      · -- the new letter is non-trivial
        intro hk
        rw [letters_cons, dif_pos hb]
        intro z hz
        rcases List.mem_append.mp hz with hz | hz
        · exact hp.2.1 hk z hz
        · simp only [List.mem_singleton] at hz
          subst hz
          show (stt k g (q'.cons e'))⁻¹ * e.lbl ≠ 1
          rw [hnew]
          exact hofm_ne
      · -- so is every later letter
        rw [letters_cons, dif_pos hb]
        by_cases hl : letters k g (q'.cons e') = []
        · simp [hl]
        · rw [List.tail_append_singleton_of_ne_nil hl]
          intro z hz
          rcases List.mem_append.mp hz with hz | hz
          · exact hp.2.2.1 z hz
          · simp only [List.mem_singleton] at hz
            subst hz
            show (stt k g (q'.cons e'))⁻¹ * e.lbl ≠ 1
            rw [hnew]
            exact hofm_ne
      · -- the endpoint is central, so this condition is vacuous
        intro hb2 _
        exact absurd hb2 (by
          have h1 : isLeafSide k ((q'.cons e').length + 1) = !isLeafSide k (q'.cons e').length :=
            isLeafSide_succ k (q'.cons e').length
          rw [Quiver.Path.length_cons, h1, hb]
          simp)
    · -- the last arrow runs from a central vertex to a leaf
      have hbf : isLeafSide k (q'.cons e').length = false := by
        cases hh : isLeafSide k (q'.cons e').length <;> simp_all
      have hx := hst.2.1 hbf
      obtain ⟨hel, hy⟩ := arrow_none_left_of_eq e hx
      obtain ⟨hel', -⟩ := arrow_to_none_of_eq e' hx
      have hidx_ne : e.idx ≠ e'.idx := by
        intro hcontra
        apply hne
        apply Prod.ext
        · show e.idx = e'.idx
          exact hcontra
        · show e.lbl = e'.lbl
          rw [hel, hel']
      refine ⟨?_, ?_, ?_, ?_⟩
      · -- no letter is added
        rw [letters_cons, dif_neg hb, List.append_nil]; exact hp.1
      · rw [letters_cons, dif_neg hb, List.append_nil]; exact hp.2.1
      · intro z hz
        rw [letters_cons, dif_neg hb, List.append_nil] at hz
        exact hp.2.2.1 z hz
      · -- the last letter is the step of the previous arrow, of different index
        intro hb2 hlen
        rw [llidx_cons, dif_neg hb, lidx_cons]
        have hll := hst.2.2.2.2 hbf
        rw [hll, lidx_cons]
        intro hcontra
        exact hidx_ne (Option.some.inj hcontra).symm

/-- **The invariant holds for every reduced path.** -/
theorem inv_of_isReduced {ι : Type u} {M : ι → Type u} [∀ i, Group (M i)] {k : Option ι} {g : Monoid.CoprodI M} {y : Work.ORLocInd.CoprodTree.Vertex M} (p : Quiver.Path (Work.ORLocInd.CoprodTree.vtx k g) y) (hp : p.IsReduced) : Work.ORLocInd.CoprodTree.Inv k g p := by
  obtain ⟨h_end, h_endnone, h_prod, h_mem, h_llidx_eq⟩ := inv_structural p
  by_cases hlen : p.length = 0
  · -- the empty path
    have hy : vtx k g = y := Quiver.Path.eq_of_length_zero p hlen
    subst hy
    have hnil : p = Quiver.Path.nil := Quiver.Path.eq_nil_of_length_zero p hlen
    subst hnil
    refine ⟨h_end, h_endnone, h_prod, ?_, h_mem, ?_, ?_, h_llidx_eq, ?_⟩
    · exact List.isChain_nil
    · intro hk z hz; simp at hz
    · intro z hz; simp at hz
    · intro _ hlen0; exact absurd rfl hlen0
  · -- a non-empty path is a `cons`
    obtain ⟨xc, q, e, rfl⟩ := (Quiver.Path.length_ne_zero_iff_eq_cons p).mp hlen
    obtain ⟨hchain, hne1, hne2, hllidxne⟩ := inv_reduced_cons q e hp
    exact ⟨h_end, h_endnone, h_prod, hchain, h_mem, hne1, hne2, h_llidx_eq, hllidxne⟩

end Work.ORLocInd.CoprodTree
