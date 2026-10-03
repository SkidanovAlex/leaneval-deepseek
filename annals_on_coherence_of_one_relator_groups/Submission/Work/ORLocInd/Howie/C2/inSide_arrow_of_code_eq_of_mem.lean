/-
# Arrows of a path meeting a given code lie in the two sides of the bridge

Let `P` be a graph presentation whose edge code separates the unoriented edges
(`P.CodeSeparates`), let `e` be an arrow of `Γ` and let `q` be a path of `Γ` one of whose arrows `g₀`
carries the code of `e`.  Then *every* arrow of `q` has both endpoints inside one of the two sides of
the unoriented edge `{e, e⁻¹}`, i.e. in the component of `Γ ∖ e` of `e.left` or of `e.right`
(`Work.ORLocInd.Howie.InSide`).

The mathematical content is entirely the following consequence of `CodeSeparates`: an arrow whose
code is the code of `e` *is* `e` or `e⁻¹`.  Hence

* if `y` is a vertex of a side and `f : x ⟶ y` is *any* arrow, then `x` is a vertex of a side
  (`inSide_left_of_inSide_right`): either `f` avoids the code of `e`, and a path of `Γ ∖ e` to `y`
  extends by the reverse of `f` to a path of `Γ ∖ e` to `x`, or `f` is `e` or `e⁻¹` and `x` is
  `e.left` or `e.right`;
* symmetrically, if `x` is a vertex of a side and `f : x ⟶ y`, then so is `y`
  (`inSide_right_of_inSide_left`).

It follows by induction on the path that *all* the vertices of a path whose source (or whose target)
lies in a side lie in a side (`allInSide_of_inSide_left`), and the theorem is proved by splitting `q`
at the arrow `g₀`: the subpath before `g₀` ends at `g₀.left` and the subpath after `g₀` starts at
`g₀.right`, both of which are endpoints of an arrow of the code of `e`.
-/
import Mathlib
import Submission.Work.ORLocInd.Howie.Case2Bridge

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ORLocInd.Howie.C2

/-! ## Single arrows -/

/-- An arrow whose code is the code of `e` is `e` or `e⁻¹` (by `CodeSeparates`), so both of its
endpoints lie in a side of the bridge. -/
theorem inSide_of_code_eq {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V]
    (P : Presentation V) (hsep : P.CodeSeparates) (e g : Quiver.Total V)
    (hg : P.edgeOf g = P.edgeOf e) : InSide P e g.left ∧ InSide P e g.right := by
  rcases hsep g e hg with heq | heq
  · rw [heq]
    exact ⟨Or.inr ⟨Quiver.Path.nil, avoids_nil P e⟩, Or.inl ⟨Quiver.Path.nil, avoids_nil P e⟩⟩
  · rw [heq]
    simp only [Quiver.totalReverse_left, Quiver.totalReverse_right]
    exact ⟨Or.inl ⟨Quiver.Path.nil, avoids_nil P e⟩, Or.inr ⟨Quiver.Path.nil, avoids_nil P e⟩⟩

/-- If the source of an arrow lies in a side of the bridge, so does its target. -/
theorem inSide_right_of_inSide_left {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V]
    (P : Presentation V) (hsep : P.CodeSeparates) (e : Quiver.Total V) {x y : V} (f : x ⟶ y)
    (h : InSide P e x) : InSide P e y := by
  by_cases hf : P.edgeOf (Quiver.Total.mk x y f) = P.edgeOf e
  · -- the arrow itself has the code of `e`, so it is `e` or `e⁻¹`
    rcases hsep (Quiver.Total.mk x y f) e hf with heq | heq
    · have hy : y = e.right := congrArg Quiver.Total.right heq
      rw [hy]; exact Or.inl ⟨Quiver.Path.nil, avoids_nil P e⟩
    · have hy : y = e.left := by
        have h' := congrArg Quiver.Total.right heq
        simpa [Quiver.totalReverse_right] using h'
      rw [hy]; exact Or.inr ⟨Quiver.Path.nil, avoids_nil P e⟩
  · rcases h with ⟨α, hα⟩ | ⟨α, hα⟩
    · exact Or.inl ⟨α.cons f, (avoids_cons_iff P e α f).mpr ⟨hα, hf⟩⟩
    · exact Or.inr ⟨α.cons f, (avoids_cons_iff P e α f).mpr ⟨hα, hf⟩⟩

/-- If the target of an arrow lies in a side of the bridge, so does its source. -/
theorem inSide_left_of_inSide_right {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V]
    (P : Presentation V) (hsep : P.CodeSeparates) (e : Quiver.Total V) {x y : V} (f : x ⟶ y)
    (h : InSide P e y) : InSide P e x := by
  by_cases hf : P.edgeOf (Quiver.Total.mk x y f) = P.edgeOf e
  · rcases hsep (Quiver.Total.mk x y f) e hf with heq | heq
    · have hx : x = e.left := congrArg Quiver.Total.left heq
      rw [hx]; exact Or.inr ⟨Quiver.Path.nil, avoids_nil P e⟩
    · have hx : x = e.right := by
        have h' := congrArg Quiver.Total.left heq
        simpa [Quiver.totalReverse_left] using h'
      rw [hx]; exact Or.inl ⟨Quiver.Path.nil, avoids_nil P e⟩
  · rcases h with ⟨α, hα⟩ | ⟨α, hα⟩
    · refine Or.inl ⟨α.cons (Quiver.reverse f), ?_⟩
      rw [avoids_cons_iff]
      exact ⟨hα, (edgeOf_reverse_mk_ne P e f).mpr hf⟩
    · refine Or.inr ⟨α.cons (Quiver.reverse f), ?_⟩
      rw [avoids_cons_iff]
      exact ⟨hα, (edgeOf_reverse_mk_ne P e f).mpr hf⟩

/-! ## Whole paths -/

/-- If the source of a path lies in a side of the bridge, then so does every endpoint of every arrow
of the path. -/
theorem allInSide_of_inSide_left {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V]
    (P : Presentation V) (hsep : P.CodeSeparates) (e : Quiver.Total V) :
    ∀ {x y : V} (q : Quiver.Path x y), InSide P e x →
      (∀ g ∈ q.arrowList, InSide P e g.left ∧ InSide P e g.right) ∧ InSide P e y := by
  intro x y q
  induction q with
  | nil => intro h; exact ⟨fun g hg => by simp at hg, h⟩
  | cons p f ih =>
    intro h
    obtain ⟨goodp, hb'⟩ := ih h
    have hb : InSide P e _ := inSide_right_of_inSide_left P hsep e f hb'
    refine ⟨?_, hb⟩
    rw [Quiver.Path.arrowList_cons]
    intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact goodp g hg
    · simp at hg
      subst hg
      exact ⟨hb', hb⟩

/-- If the target of a path lies in a side of the bridge, then so does every endpoint of every arrow
of the path. -/
theorem allInSide_of_inSide_right {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V]
    (P : Presentation V) (hsep : P.CodeSeparates) (e : Quiver.Total V) :
    ∀ {x y : V} (q : Quiver.Path x y), InSide P e y →
      (∀ g ∈ q.arrowList, InSide P e g.left ∧ InSide P e g.right) ∧ InSide P e x := by
  intro x y q
  induction q with
  | nil => intro h; exact ⟨fun g hg => by simp at hg, h⟩
  | cons p f ih =>
    intro h
    have hb' : InSide P e _ := inSide_left_of_inSide_right P hsep e f h
    obtain ⟨goodp, hx⟩ := ih hb'
    refine ⟨?_, hx⟩
    rw [Quiver.Path.arrowList_cons]
    intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact goodp g hg
    · simp at hg
      subst hg
      exact ⟨hb', h⟩

/-- The form of the theorem with the separating arrow `g₀` given as an existential hypothesis on the
arrow list: the target of `q` also lies in a side of the bridge (this is what makes the induction go
through). -/
theorem allInSide_of_exists_code_eq {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V]
    (P : Presentation V) (hsep : P.CodeSeparates) (e : Quiver.Total V) :
    ∀ {a b : V} (q : Quiver.Path a b),
      (∃ g ∈ q.arrowList, P.edgeOf g = P.edgeOf e) →
      (∀ g ∈ q.arrowList, InSide P e g.left ∧ InSide P e g.right) ∧ InSide P e b := by
  intro a b q
  induction q with
  | nil => rintro ⟨g, hg, _⟩; simp at hg
  | cons p f ih =>
    intro h
    rw [Quiver.Path.arrowList_cons] at h
    by_cases hpe : ∃ g ∈ p.arrowList, P.edgeOf g = P.edgeOf e
    · -- the separating arrow already occurs in the prefix: the induction hypothesis applies,
      -- and the last arrow keeps us inside the side
      obtain ⟨goodp, hb'⟩ := ih hpe
      have hb : InSide P e _ := inSide_right_of_inSide_left P hsep e f hb'
      refine ⟨?_, hb⟩
      rw [Quiver.Path.arrowList_cons]
      intro g hg
      rcases List.mem_append.mp hg with hg | hg
      · exact goodp g hg
      · simp at hg
        subst hg
        exact ⟨hb', hb⟩
    · -- the last arrow carries the code of `e`: its endpoints are `e.left`/`e.right`, and the
      -- prefix lies in a side by `allInSide_of_inSide_right`
      have hf : P.edgeOf (Quiver.Total.mk _ _ f) = P.edgeOf e := by
        rcases h with ⟨g, hg, hcg⟩
        rcases List.mem_append.mp hg with hg | hg
        · exact absurd ⟨g, hg, hcg⟩ hpe
        · simp at hg
          subst hg
          exact hcg
      obtain ⟨hfl, hfr⟩ := inSide_of_code_eq P hsep e _ hf
      obtain ⟨goodp, _⟩ := allInSide_of_inSide_right P hsep e p hfl
      refine ⟨?_, hfr⟩
      rw [Quiver.Path.arrowList_cons]
      intro g hg
      rcases List.mem_append.mp hg with hg | hg
      · exact goodp g hg
      · simp at hg
        subst hg
        exact ⟨hfl, hfr⟩

/-- **Every arrow of a path containing an arrow of the code of `e` has both endpoints in a side of
the bridge.** -/
theorem inSide_arrow_of_code_eq_of_mem {V : Type*} [Quiver V]
    [Quiver.HasInvolutiveReverse V] (P : Work.ORLocInd.Howie.Presentation V)
    (hsep : P.CodeSeparates) (e : Quiver.Total V) {a b : V} (q : Quiver.Path a b)
    {g₀ : Quiver.Total V} (hg₀ : g₀ ∈ q.arrowList) (hcg : P.edgeOf g₀ = P.edgeOf e) :
    ∀ g ∈ q.arrowList, Work.ORLocInd.Howie.InSide P e g.left ∧
      Work.ORLocInd.Howie.InSide P e g.right :=
  (allInSide_of_exists_code_eq P hsep e q ⟨g₀, hg₀, hcg⟩).1

end Work.ORLocInd.Howie.C2
