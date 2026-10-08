import Mathlib
import Submission.Work.ZassenhausTwoGroup.Defs
import Submission.Work.ZassenhausTwoGroup.isTI_Q
import Submission.Work.ZassenhausTwoGroup.normalizer_Q_eq
import Submission.Work.ZassenhausTwoGroup.conj_mem_Q_iff

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ZassenhausTwoGroup.card_classes_meeting_Q`

The number of `G`-conjugacy classes meeting `Q ∖ 1` equals the number of `H`-conjugacy classes
inside `Q ∖ 1`, for the rank-one Zassenhaus data `H = Q ⋊ D` (`IsSplitRankOne H Q t`,
`IsZassenhaus H`).

This is the class-count bridge **B1** of `NOTES_LEAD_probe2245.md`: the `G`-classes meeting
`Q ∖ 1` are in bijection with the `H`-classes inside `Q ∖ 1`.

The mathematics is the standard fusion argument, and uses only that `Q` is T.I. in `G`
(`conj_mem_Q_iff`, proved in this area from the free action of `Q` on `Ω ∖ {∞}`):

* if `x ∈ Q ∖ 1` and `g x g⁻¹ ∈ Q` then `g ∈ H`; consequently two elements of `Q ∖ 1` which are
  conjugate in `G` are already conjugate in `H`, and the map `[x]_G ↦ [x]_H` (for `x ∈ Q ∖ 1`)
  is well defined (`toHClass`);
* conversely every `H`-class in `Q ∖ 1` maps back to its `G`-class (`toGClass`), and the two
  maps are mutually inverse (`conjClassesMeetingQEquiv`), whence the equality of `Nat.card`s.

The Zassenhaus hypothesis is not used: T.I.-ness of `Q` already gives the fusion statement.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open Classical
open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.ZassenhausTwoGroup

section Aux

variable {G : Type} [Group G] [Finite G]

/-- An element of `H` is non-trivial in `H` if and only if its image in `G` is non-trivial. -/
lemma subtype_ne_one_iff {H : Subgroup G} {x : G} (hx : x ∈ H) :
    (⟨x, hx⟩ : H) ≠ 1 ↔ x ≠ 1 := by
  constructor
  · intro h h2; exact h (Subtype.ext h2)
  · intro h h2; exact h (congrArg (fun z : H => (z : G)) h2)

/-- **The fusion fact.**  In the split rank-one set-up, two elements of `Q ∖ 1` which are
conjugate in `G` are already conjugate in `H`.  Indeed, if `g x g⁻¹ = y ∈ Q` with `x ∈ Q ∖ 1`,
then `g ∈ H` (this is `conj_mem_Q_iff`, i.e. `Q` T.I. in `G`). -/
lemma isConj_subtype_of_isConj {H Q : Subgroup G} {t : G} (h : IsSplitRankOne H Q t)
    {x y : G} (hxQ : x ∈ Q) (hx1 : x ≠ 1) (hyQ : y ∈ Q) (hxy : IsConj x y) :
    IsConj (⟨x, h.le hxQ⟩ : H) (⟨y, h.le hyQ⟩ : H) := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hxy
  have hgQ : g * x * g⁻¹ ∈ Q := by rw [hg]; exact hyQ
  have hgH : g ∈ H := conj_mem_Q_iff h hxQ hx1 g hgQ
  exact isConj_iff.mpr ⟨⟨g, hgH⟩, Subtype.ext hg⟩

/-- The `G`-conjugacy classes meeting `Q ∖ 1`. -/
abbrev ClassesMeetingQ (Q : Subgroup G) : Type :=
  {c : ConjClasses G // ∃ x ∈ c.carrier, x ∈ Q ∧ x ≠ 1}

/-- The `H`-conjugacy classes meeting `Q ∖ 1` (inside `H`). -/
abbrev HClassesMeetingQ (H Q : Subgroup G) : Type :=
  {c : ConjClasses H // ∃ x ∈ c.carrier, (x : G) ∈ Q ∧ x ≠ 1}

/-- Pick a representative `x ∈ Q ∖ 1` of a `G`-class meeting `Q ∖ 1` and take its `H`-class. -/
noncomputable def toHClass {H Q : Subgroup G} {t : G} (h : IsSplitRankOne H Q t) :
    ClassesMeetingQ Q → HClassesMeetingQ H Q :=
  fun c =>
    ⟨ConjClasses.mk (⟨c.2.choose, h.le c.2.choose_spec.2.1⟩ : H),
     ⟨⟨c.2.choose, h.le c.2.choose_spec.2.1⟩, ConjClasses.mem_carrier_mk,
      c.2.choose_spec.2.1,
      (subtype_ne_one_iff (h.le c.2.choose_spec.2.1)).mpr c.2.choose_spec.2.2⟩⟩

/-- The `G`-class of a representative of an `H`-class meeting `Q ∖ 1`. -/
noncomputable def toGClass {H Q : Subgroup G} : HClassesMeetingQ H Q → ClassesMeetingQ Q :=
  fun d =>
    ⟨ConjClasses.mk (d.2.choose : G),
     ⟨(d.2.choose : G), ConjClasses.mem_carrier_mk, d.2.choose_spec.2.1,
      (subtype_ne_one_iff d.2.choose.2).mp d.2.choose_spec.2.2⟩⟩

/-- **The bijection behind B1.**  `G`-classes meeting `Q ∖ 1` correspond to `H`-classes inside
`Q ∖ 1`, both directions being "take the class of a chosen representative of the non-trivial part
in `Q`"; the fusion fact `isConj_subtype_of_isConj` is what makes the two composites the
identities. -/
noncomputable def conjClassesMeetingQEquiv {H Q : Subgroup G} {t : G}
    (h : IsSplitRankOne H Q t) : ClassesMeetingQ Q ≃ HClassesMeetingQ H Q where
  toFun := toHClass h
  invFun := toGClass
  left_inv c := by
    apply Subtype.ext
    change ConjClasses.mk (((toHClass h c).2.choose : H) : G) = c.1
    have hxc : c.2.choose ∈ c.1.carrier := c.2.choose_spec.1
    have hzc : (toHClass h c).2.choose ∈ (toHClass h c).1.carrier :=
      (toHClass h c).2.choose_spec.1
    have h1 : ConjClasses.mk ((toHClass h c).2.choose) =
        ConjClasses.mk (⟨c.2.choose, h.le c.2.choose_spec.2.1⟩ : H) :=
      ConjClasses.mem_carrier_iff_mk_eq.mp hzc
    have h2 : IsConj (((toHClass h c).2.choose : H) : G) (c.2.choose : G) :=
      (Subgroup.subtype H).map_isConj (ConjClasses.mk_eq_mk_iff_isConj.mp h1)
    rw [ConjClasses.mk_eq_mk_iff_isConj.mpr h2]
    exact ConjClasses.mem_carrier_iff_mk_eq.mp hxc
  right_inv d := by
    apply Subtype.ext
    change ConjClasses.mk (⟨(toGClass d).2.choose, h.le (toGClass d).2.choose_spec.2.1⟩ : H) =
      d.1
    have hyc : d.2.choose ∈ d.1.carrier := d.2.choose_spec.1
    have hyQ : (d.2.choose : G) ∈ Q := d.2.choose_spec.2.1
    have hy1 : (d.2.choose : G) ≠ 1 :=
      (subtype_ne_one_iff d.2.choose.2).mp d.2.choose_spec.2.2
    have hwc : (toGClass d).2.choose ∈ (toGClass d).1.carrier :=
      (toGClass d).2.choose_spec.1
    have hwQ : (toGClass d).2.choose ∈ Q := (toGClass d).2.choose_spec.2.1
    have h1 : ConjClasses.mk ((toGClass d).2.choose) = ConjClasses.mk (d.2.choose : G) :=
      ConjClasses.mem_carrier_iff_mk_eq.mp hwc
    have h2 : IsConj ((toGClass d).2.choose) (d.2.choose : G) :=
      ConjClasses.mk_eq_mk_iff_isConj.mp h1
    obtain ⟨g, hg⟩ := isConj_iff.mp h2.symm
    have hgQ : g * (d.2.choose : G) * g⁻¹ ∈ Q := by rw [hg]; exact hwQ
    have hgH : g ∈ H := conj_mem_Q_iff h hyQ hy1 g hgQ
    have hconj : ConjClasses.mk (d.2.choose) =
        ConjClasses.mk (⟨(toGClass d).2.choose, h.le hwQ⟩ : H) := by
      rw [ConjClasses.mk_eq_mk_iff_isConj]
      refine isConj_iff.mpr ⟨⟨g, hgH⟩, ?_⟩
      apply Subtype.ext
      simpa using hg
    rw [← hconj]
    exact ConjClasses.mem_carrier_iff_mk_eq.mp hyc

end Aux

/-- **B1 of the (21)–(24) route.**  In the rank-one Zassenhaus set-up the `G`-conjugacy classes
meeting `Q ∖ 1` are in bijection with the `H`-conjugacy classes inside `Q ∖ 1`, by the T.I.
property of `Q` (`conj_mem_Q_iff`): a `G`-conjugate of `x ∈ Q ∖ 1` which lies again in `Q` is
already an `H`-conjugate. -/
theorem card_classes_meeting_Q {G : Type} [Group G] [Fintype G] (H Q : Subgroup G) (t : G)
    (h : Submission.Blueprint.IsSplitRankOne H Q t) (hZ : Submission.Blueprint.IsZassenhaus H) :
    Nat.card {c : ConjClasses G // ∃ x ∈ c.carrier, x ∈ Q ∧ x ≠ 1} =
      Nat.card {c : ConjClasses H // ∃ x ∈ c.carrier, (x : G) ∈ Q ∧ x ≠ 1} :=
  Nat.card_congr (conjClassesMeetingQEquiv h)

end Work.ZassenhausTwoGroup
