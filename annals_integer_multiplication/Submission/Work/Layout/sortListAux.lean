import Mathlib
import Submission.Work.Layout.SortDefs
import Submission.Work.Layout.SortSpecs
import Submission.Work.Layout.Base
import Submission.Work.Layout.Move

namespace Work.Layout

open HvdH

/-! ## Helper lemmas (pure list arithmetic)

These are the small unconditional facts the three parts of `sortListAux` rest on. -/

/-- A permutation preserves `Σ vsz + length` (both are additive over the multiset of elements). -/
lemma sortListAux_perm_vsz_len {l₁ l₂ : List Val} (h : l₁.Perm l₂) :
    (l₁.map vsz).sum + l₁.length = (l₂.map vsz).sum + l₂.length := by
  have h1 : (l₁.map vsz).sum = (l₂.map vsz).sum := (h.map vsz).sum_eq
  have h2 : l₁.length = l₂.length := h.length_eq
  omega

/-- `vsz (ofList xs) = Σ vsz + length + 1` (each `cons` contributes exactly one glyph, and the
final `nil` one more). -/
lemma sortListAux_vsz_ofList_eq (xs : List Val) :
    vsz (ofList xs) = (xs.map vsz).sum + xs.length + 1 := by
  induction xs with
  | nil => simp [ofList, vsz, Val.enc]
  | cons x xs ih =>
      have h : ofList (x :: xs) = Val.cons x (ofList xs) := rfl
      rw [h]
      simp only [vsz, Val.enc, List.length_cons, List.length_append]
      rw [show (ofList xs).enc.length = vsz (ofList xs) from rfl, ih]
      simp only [List.map_cons, List.sum_cons, vsz]
      ring

/-- `encs` of a nonempty run is nonempty. -/
lemma sortListAux_encs_ne_nil {r : List Val} (hr : r ≠ []) : encs r ≠ [] := by
  cases r with
  | nil => exact absurd rfl hr
  | cons v vs =>
      intro h
      have hv : v.enc ≠ [] := by cases v <;> simp [Val.enc]
      have : encs (v :: vs) = v.enc ++ encs vs := rfl
      rw [this] at h
      exact hv (List.eq_nil_of_append_eq_nil h).1

/-- If every element of the nonempty run `r` is a `cons`-value, then `encs r` starts with the
`Glyph.cons` constructor. -/
lemma sortListAux_encs_head_cons {r : List Val} (hr : r ≠ [])
    (hall : ∀ v ∈ r, ∃ a b, v = Val.cons a b) :
    (encs r).headD Glyph.eos = Glyph.cons := by
  obtain ⟨v, vs, rfl⟩ := List.exists_cons_of_ne_nil hr
  obtain ⟨a, b, rfl⟩ := hall v (by simp)
  simp [encs, Val.enc]

/-- `headD` of a concatenation whose left factor is nonempty. -/
lemma sortListAux_headD_append_of_ne_nil {A B : List Glyph} {x : Glyph} (hA : A ≠ []) :
    (A ++ B).headD x = A.headD x := by
  cases A with
  | nil => exact absurd rfl hA
  | cons a t => rfl

/-- The head of `runEncB []` is the boundary marker (not `Glyph.cons`). -/
lemma sortListAux_runEncB_nil_head (J : List Glyph) :
    (Sk.runEncB ([] : List (List Val)) ++ J).headD Glyph.eos = Sk.gBnd := rfl

/-- One `runEncB` step: the run marker `gMark` (not the boundary `gBnd`) follows the first run. -/
lemma sortListAux_runEncB_cons (r : List Val) (rs : List (List Val)) :
    Sk.runEncB (r :: rs) = encs r ++ gMark :: Sk.runEncB rs := by
  simp [Sk.runEncB, Sk.runEnc, List.flatten_cons, List.append_assoc]

/-- Three elementary facts used by the top-level assembly of `sortByKey` (pure list arithmetic; the
first uses `hLists`, the other two are unconditional):
(a) the two `altSplit` components together carry at most the size of `ofList xs` (in fact
`totR c.1 + totR c.2 = (xs.map vsz).sum + xs.length` and `vsz (ofList xs) = … + 1`);
(b) if `(ps ++ qs).flatten` is a permutation of `xs` then the size-contribution of `ps.flatten`
(sum of `vsz` plus length) is at most that of `xs`;
(c) the head of `runEncB rs ++ J` is `Glyph.cons` exactly when `rs` is nonempty, provided every run is
nonempty and every element is a `cons`-value (this is the loop-flag test of `sortProg`). -/
theorem sortListAux (hLists : Work.Layout.Sk.ListsSpec) :
    (∀ xs : List HvdH.Val,
      Work.Layout.Sk.totR (Work.Layout.Sk.altSplit xs).1 +
        Work.Layout.Sk.totR (Work.Layout.Sk.altSplit xs).2 ≤ HvdH.vsz (HvdH.ofList xs)) ∧
    (∀ (xs : List HvdH.Val) (ps qs : List (List HvdH.Val)),
      (ps ++ qs).flatten.Perm xs →
      (ps.flatten.map HvdH.vsz).sum + ps.flatten.length ≤ (xs.map HvdH.vsz).sum + xs.length) ∧
    (∀ (rs : List (List HvdH.Val)) (J : List HvdH.Glyph),
      (∀ r ∈ rs, r ≠ []) → (∀ v ∈ rs.flatten, ∃ (a b : HvdH.Val), v = HvdH.Val.cons a b) →
      ((Work.Layout.Sk.runEncB rs ++ J).headD HvdH.Glyph.eos = HvdH.Glyph.cons ↔ rs ≠ [])) := by
  refine ⟨?_, ?_, ?_⟩
  · -- (a): `altSplit` splits the multiset of `xs` into runs of length one, so the total size
    -- contribution is exactly that of `xs`, and `ofList xs` adds one `nil` glyph.
    intro xs
    obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,hazp,_⟩ := hLists
    have hsplit : ((Sk.altSplit xs).1.flatten ++ (Sk.altSplit xs).2.flatten).Perm xs := by
      have h := hazp xs
      rwa [List.flatten_append] at h
    have hval := sortListAux_perm_vsz_len hsplit
    simp only [List.map_append, List.sum_append, List.length_append] at hval
    rw [Sk.totR, Sk.totR, sortListAux_vsz_ofList_eq]
    omega
  · -- (b): a sub-multiset has no larger `Σ vsz + length`.
    intro xs ps qs h
    have heq : ((ps.flatten ++ qs.flatten).map vsz).sum + (ps.flatten ++ qs.flatten).length
        = (xs.map vsz).sum + xs.length := by
      have h' : (ps.flatten ++ qs.flatten).Perm xs := by rwa [List.flatten_append] at h
      simpa using sortListAux_perm_vsz_len h'
    have hle : (ps.flatten.map vsz).sum + ps.flatten.length
        ≤ ((ps.flatten ++ qs.flatten).map vsz).sum + (ps.flatten ++ qs.flatten).length := by
      simp only [List.map_append, List.sum_append, List.length_append]
      omega
    omega
  · -- (c): the loop flag of `sortProg` reads the head of the run stack.
    intro rs J hrs hall
    constructor
    · intro h hnil
      subst hnil
      rw [sortListAux_runEncB_nil_head] at h
      exact absurd h (by decide)
    · intro hrsne
      obtain ⟨r, rs', rfl⟩ := List.exists_cons_of_ne_nil hrsne
      have hr : r ≠ [] := hrs r (by simp)
      rw [sortListAux_runEncB_cons, List.append_assoc,
        sortListAux_headD_append_of_ne_nil (sortListAux_encs_ne_nil hr)]
      exact sortListAux_encs_head_cons hr (fun v hv => hall v (by simp [hv]))

end Work.Layout
