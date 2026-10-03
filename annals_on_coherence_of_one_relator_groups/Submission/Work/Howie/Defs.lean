/-
# Shared vocabulary for the "forest relator" lemma (Howie's Case 2, step L5c)

This file collects the definitions and the elementary lemmas on which
`Work.Howie.edgeCount_eq_one_of_forest` (L5c of `N4_LOCIND_LEAD.md`) and its auxiliary lemmas
are phrased.

Fix a groupoid presentation `P` of a graph `Γ` (a quiver with an involutive reversal of arrows)
and an arrow `e` of `Γ`, with code `c = P.edgeOf e`.  The graph `Γ ∖ e` is obtained by deleting
all arrows whose code is `c`; in the formalisation it is `DelV (P.keepCode c)`, and its paths are
spelled `dpath (P.keepCode c) a b` (`Defs2.lean`), with the `Quiver` instance *pinned* so that no
vertex cast ever occurs.

* `EFree P c p` : `p` is a path of `Γ ∖ e` (all of its arrows have code different from `c`);
* `strip_efree_decomp` : every path is an `e`-free path, followed by one arrow of code `c`,
  followed by an arbitrary path;
* `closed_efree_isReduced_eq_nil` : if `Γ ∖ e` is a forest — the hypothesis `hfor` of L5c, which
  says that every reduced closed path of `Γ ∖ e` is empty — then there is no nonempty reduced
  closed path of `Γ ∖ e`;
* `dpath_isReduced_eq_of_same_ends` : consequently two reduced paths of `Γ ∖ e` with the same
  endpoints are equal (uniqueness of reduced paths in a forest);
* `isReduced_wrap_of_isCyclicallyReduced` : for `r = A₀ · E · A₁` cyclically reduced, the
  wrap-around `A₁ · A₀` is reduced.
-/
import Mathlib
import Submission.Work.ORLocInd.Howie.Defs2
import Submission.Work.ORLocInd.Howie.Relator
import Submission.Work.ORLocInd.Howie.Basic
import Submission.Work.ORLocInd.Howie.Delete
import Submission.Work.ORLocInd.Howie.PathReduced
import Submission.Work.ORLocInd.Howie.isReduced_comp
import Submission.Work.ORLocInd.Howie.isReduced_comp_of_decomp

set_option autoImplicit false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false

universe u

namespace Work.Howie

open Quiver

variable {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V]

/-! ## The arrow list of a composite path -/

/-- The arrow list of a composite path is the concatenation of the arrow lists. -/
theorem arrowList_comp {a b c : V} (p : Quiver.Path a b) (q : Quiver.Path b c) :
    (p.comp q).arrowList = p.arrowList ++ q.arrowList := by
  induction q with
  | nil => simp
  | cons q e ih =>
    rw [Quiver.Path.comp_cons, Quiver.Path.arrowList_cons, ih, Quiver.Path.arrowList_cons,
      List.append_assoc]

/-- The codes of the arrows of a composite path. -/
theorem map_arrowList_comp {α : Type u} (ω : Quiver.Total V → α) {a b c : V}
    (p : Quiver.Path a b) (q : Quiver.Path b c) :
    ((p.comp q).arrowList.map ω) = (p.arrowList.map ω) ++ (q.arrowList.map ω) := by
  rw [arrowList_comp, List.map_append]

/-- The arrow list of a single-arrow path. -/
theorem arrowList_toPath {a b : V} (E : a ⟶ b) :
    E.toPath.arrowList = [Quiver.Total.mk a b E] := rfl

/-! ## `e`-free paths -/

/-- `EFree P c p`: every arrow of the path `p` has code different from `c`, i.e. `p` is a path of
the graph `Γ ∖ e` obtained from `Γ` by deleting the arrows of code `c`. -/
def EFree (P : Work.ORLocInd.Howie.Presentation V) (c : P.α) {a b : V}
    (p : Quiver.Path a b) : Prop :=
  ∀ g ∈ p.arrowList, (P.keepCode c).pred g

theorem EFree_iff {P : Work.ORLocInd.Howie.Presentation V} {c : P.α} {a b : V}
    {p : Quiver.Path a b} :
    EFree P c p ↔ ∀ g ∈ p.arrowList, P.edgeOf g ≠ c :=
  Iff.rfl

@[simp] theorem EFree_nil (P : Work.ORLocInd.Howie.Presentation V) (c : P.α) (a : V) :
    EFree P c (Quiver.Path.nil : Quiver.Path a a) := by
  intro g hg
  simp at hg

theorem EFree_cons {P : Work.ORLocInd.Howie.Presentation V} {c : P.α} {a b d : V}
    {p : Quiver.Path a b} {E : b ⟶ d} :
    EFree P c (p.cons E) ↔ EFree P c p ∧ P.edgeOf (Quiver.Total.mk b d E) ≠ c := by
  constructor
  · intro h
    refine ⟨fun g hg => h g (by rw [Quiver.Path.arrowList_cons]; exact List.mem_append.mpr (Or.inl hg)),
      h _ (by rw [Quiver.Path.arrowList_cons]; exact List.mem_append.mpr (Or.inr (by simp)))⟩
  · rintro ⟨hp, hE⟩ g hg
    rw [Quiver.Path.arrowList_cons] at hg
    rcases List.mem_append.mp hg with hg | hg
    · exact hp g hg
    · rw [List.mem_singleton] at hg
      subst hg
      exact hE

theorem EFree.of_comp {P : Work.ORLocInd.Howie.Presentation V} {c : P.α} {a b d : V}
    {p : Quiver.Path a b} {q : Quiver.Path b d} (h : EFree P c (p.comp q)) :
    EFree P c p ∧ EFree P c q := by
  constructor
  · intro g hg
    exact h g (by rw [arrowList_comp]; exact List.mem_append.mpr (Or.inl hg))
  · intro g hg
    exact h g (by rw [arrowList_comp]; exact List.mem_append.mpr (Or.inr hg))

theorem EFree.comp {P : Work.ORLocInd.Howie.Presentation V} {c : P.α} {a b d : V}
    {p : Quiver.Path a b} {q : Quiver.Path b d} (hp : EFree P c p) (hq : EFree P c q) :
    EFree P c (p.comp q) := by
  intro g hg
  rw [arrowList_comp] at hg
  rcases List.mem_append.mp hg with hg | hg
  · exact hp g hg
  · exact hq g hg

/-! ## The codes of an `e`-free path -/

/-- The code `c` does not occur among the codes of an `e`-free path. -/
theorem EFree.codes_ne {P : Work.ORLocInd.Howie.Presentation V} {c : P.α} {a b : V}
    {p : Quiver.Path a b} (h : EFree P c p) : c ∉ p.arrowList.map P.edgeOf := by
  intro hc
  obtain ⟨g, hg, hge⟩ := List.mem_map.mp hc
  exact h g hg hge

/-! ## Reducedness of factors -/

/-- The right factor of a reduced path is reduced. -/
theorem isReduced_of_comp_right {a b c : V} {p : Quiver.Path a b} {q : Quiver.Path b c}
    (h : (p.comp q).IsReduced) : q.IsReduced := by
  have h2 : (q.reverse.comp p.reverse).IsReduced := by
    rw [← Quiver.Path.reverse_comp]
    exact h.reverse
  have h3 : q.reverse.IsReduced := Quiver.Path.IsReduced.of_comp h2
  have h4 : q.reverse.reverse.IsReduced := h3.reverse
  rwa [Quiver.Path.reverse_reverse] at h4

/-- A prefix of a reduced path is reduced. -/
theorem isReduced_of_comp_left {a b c : V} {p : Quiver.Path a b} {q : Quiver.Path b c}
    (h : (p.comp q).IsReduced) : p.IsReduced :=
  h.of_comp

/-! ## The length of paths of `Γ ∖ e` -/

/-- The erasure of a path of `DelV K` to a path of `V` preserves the length. -/
theorem length_erasePath (K : Work.ORLocInd.Howie.Keep V) {a b : V}
    (p : Work.ORLocInd.Howie.dpath K a b) :
    (Work.ORLocInd.Howie.DelV.erasePath K a p).length = p.length := by
  induction p with
  | nil => rfl
  | cons p e ih =>
    rw [Work.ORLocInd.Howie.DelV.erasePath_cons]
    simp only [Quiver.Path.length_cons, ih]

/-- The lift of a path of `V` to `DelV K` preserves the length. -/
theorem length_liftPath (K : Work.ORLocInd.Howie.Keep V) {a b : V} (p : Quiver.Path a b)
    (h : ∀ g ∈ p.arrowList, K.pred g) :
    (Work.ORLocInd.Howie.DelV.liftPath K a p h).length = p.length := by
  have h1 := length_erasePath K (Work.ORLocInd.Howie.DelV.liftPath K a p h)
  rw [Work.ORLocInd.Howie.DelV.erasePath_liftPath] at h1
  exact h1.symm

/-! ## `Γ ∖ e` is a forest -/

/-- **The forest hypothesis, in the form used by the L5c argument.**  If every reduced closed path
of `Γ ∖ e` is empty (`hfor`), then every closed reduced path of `V` avoiding the code `c` is
empty.  (The path is first lifted to `Γ ∖ e`, where `hfor` applies, and the lift has the same
length; `liftPath` also preserves reducedness.) -/
theorem closed_efree_isReduced_eq_nil (P : Work.ORLocInd.Howie.Presentation V) (c : P.α)
    (hfor : ∀ (y : V) (q : Work.ORLocInd.Howie.dpath (P.keepCode c) y y),
      q.IsReduced → q.length = 0)
    {y : V} {q : Quiver.Path y y} (hq : q.IsReduced) (hf : EFree P c q) :
    q = Quiver.Path.nil := by
  have hlen := length_liftPath (P.keepCode c) q hf
  have hred : (Work.ORLocInd.Howie.DelV.liftPath (P.keepCode c) y q hf).IsReduced :=
    (Work.ORLocInd.Howie.DelV.isReduced_liftPath (P.keepCode c) q hf).mpr hq
  have h0 : (Work.ORLocInd.Howie.DelV.liftPath (P.keepCode c) y q hf).length = 0 :=
    hfor y _ hred
  rw [hlen] at h0
  exact Quiver.Path.eq_nil_of_length_zero q h0

/-- **Uniqueness of reduced paths in the forest `Γ ∖ e`.**  Two reduced paths of `Γ ∖ e` with the
same endpoints are equal. -/
theorem dpath_isReduced_eq_of_same_ends (P : Work.ORLocInd.Howie.Presentation V) (c : P.α)
    (hfor : ∀ (y : V) (q : Work.ORLocInd.Howie.dpath (P.keepCode c) y y),
      q.IsReduced → q.length = 0)
    {a b : V} {p q : Work.ORLocInd.Howie.dpath (P.keepCode c) a b}
    (hp : p.IsReduced) (hq : q.IsReduced) : p = q := by
  have hnil : Work.ORLocInd.Howie.pmul p q.reverse = Quiver.Path.nil := by
    refine Quiver.Path.eq_nil_of_length_zero _ ?_
    exact hfor a _ (Work.ORLocInd.Howie.pmul_isReduced p q.reverse)
  have h1 : Work.ORLocInd.Howie.pmul
      (Quiver.Path.nil : Work.ORLocInd.Howie.dpath (P.keepCode c) a a) q = q := by
    rw [Work.ORLocInd.Howie.pmul_nil_left q, Work.ORLocInd.Howie.red_eq_self hq]
  have h3 : Work.ORLocInd.Howie.pmul q.reverse q = Quiver.Path.nil :=
    Work.ORLocInd.Howie.pmul_reverse_left q
  have h4 : Work.ORLocInd.Howie.pmul p
      (Quiver.Path.nil : Work.ORLocInd.Howie.dpath (P.keepCode c) b b) = p := by
    rw [Work.ORLocInd.Howie.pmul_nil_right p, Work.ORLocInd.Howie.red_eq_self hp]
  have h5 := Work.ORLocInd.Howie.pmul_assoc p q.reverse q
  rw [← h1, ← hnil, h5, h3, h4]

/-- **Uniqueness of reduced paths of `Γ ∖ e` in `V`.**  If `Γ ∖ e` is a forest, then two reduced
paths of `V` avoiding the code `c` and with the same endpoints are equal.  (Both are lifted to
`Γ ∖ e`, where `dpath_isReduced_eq_of_same_ends` applies.) -/
theorem efree_isReduced_eq_of_same_ends (P : Work.ORLocInd.Howie.Presentation V) (c : P.α)
    (hfor : ∀ (y : V) (q : Work.ORLocInd.Howie.dpath (P.keepCode c) y y),
      q.IsReduced → q.length = 0)
    {a b : V} {p q : Quiver.Path a b} (hp : p.IsReduced) (hq : q.IsReduced)
    (hpfree : EFree P c p) (hqfree : EFree P c q) : p = q := by
  have hlift : Work.ORLocInd.Howie.DelV.liftPath (P.keepCode c) a p hpfree =
      Work.ORLocInd.Howie.DelV.liftPath (P.keepCode c) a q hqfree :=
    dpath_isReduced_eq_of_same_ends P c hfor
      ((Work.ORLocInd.Howie.DelV.isReduced_liftPath (P.keepCode c) p hpfree).mpr hp)
      ((Work.ORLocInd.Howie.DelV.isReduced_liftPath (P.keepCode c) q hqfree).mpr hq)
  have h2 := congrArg (Work.ORLocInd.Howie.DelV.erasePath (P.keepCode c) a) hlift
  rwa [Work.ORLocInd.Howie.DelV.erasePath_liftPath, Work.ORLocInd.Howie.DelV.erasePath_liftPath]
    at h2

/-! ## Splitting a path at its first arrow of code `c` -/

/-- **Splitting a path at an arrow of code `c`.**  Every path `p` either avoids the code `c`
throughout, or splits as `p = A · E · p'` where `A` avoids the code `c` and the single arrow `E`
has code `c`. -/
theorem strip_efree_decomp (P : Work.ORLocInd.Howie.Presentation V) (c : P.α) {a b : V}
    (p : Quiver.Path a b) :
    EFree P c p ∨
      ∃ (d d' : V) (A : Quiver.Path a d) (E : d ⟶ d') (p' : Quiver.Path d' b),
        EFree P c A ∧ P.edgeOf (Quiver.Total.mk d d' E) = c ∧
          p = A.comp (E.toPath.comp p') := by
  induction p with
  | nil => exact Or.inl (EFree_nil P c _)
  | cons p e ih =>
    rcases ih with hp | ⟨d, d', A, E, p', hA, hE, hp⟩
    · by_cases hc : P.edgeOf (Quiver.Total.mk _ _ e) = c
      · refine Or.inr ⟨_, _, p, e, Quiver.Path.nil, hp, hc, ?_⟩
        rw [Quiver.Path.comp_nil, Quiver.Path.cons_eq_comp_toPath]
      · refine Or.inl ?_
        rw [EFree_cons]
        exact ⟨hp, hc⟩
    · refine Or.inr ⟨d, d', A, E, p'.cons e, hA, hE, ?_⟩
      rw [hp, Quiver.Path.comp_cons, Quiver.Path.comp_cons, Quiver.Path.cons_eq_comp_toPath]

/-! ## The wrap-around of a cyclically reduced path -/

/-- **The wrap-around of a cyclically reduced closed path is reduced.**  If `r = A₀ · E · A₁` is
reduced and cyclically reduced, then reading `r` cyclically (i.e. going from the end back to the
beginning) gives the reduced path `A₁ · A₀`. -/
theorem isReduced_wrap_of_isCyclicallyReduced {w u v : V} (A₀ : Quiver.Path w u)
    (E : u ⟶ v) (A₁ : Quiver.Path v w)
    (hr : (A₀.comp (E.toPath.comp A₁)).IsReduced)
    (hcr : Work.ORLocInd.Howie.IsCyclicallyReduced (A₀.comp (E.toPath.comp A₁))) :
    (A₁.comp A₀).IsReduced :=
  Work.ORLocInd.Howie.isReduced_comp_of_decomp (Quiver.Total.mk u v E) A₀ A₁ hr hcr

end Work.Howie
