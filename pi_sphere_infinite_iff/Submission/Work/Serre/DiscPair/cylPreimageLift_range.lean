import Mathlib
import Submission.Work.Serre.DiscPair.cylPreimageDefs

/-!
# The bottom copy of the source in a preimage mapping cylinder

`Work.Serre.DiscPair.cylPreimageLift q S` identifies the mapping cylinder of the restricted map
`q|_S : q ⁻¹' S → S` with the part `(cylRetract q) ⁻¹' S` of the mapping cylinder of `q`.  Here we
show that this identification is *faithful on the bottom copies*: the image of a point of
`cyl (q|_S)` under `cylPreimageLift q S` lies in the bottom copy `range (cylIncl q)` of `cyl q` if
and only if that point already lay in the bottom copy `range (cylIncl (q|_S))`.

The point is that in the mapping cylinder every point of the cylinder `P × I` with `t ≠ 1` is the
sole member of its class, so the only classes which meet the bottom circle `P × {0}` are the
classes of the bottom points themselves; the target copy `X` is disjoint from it.  This is
`Work.Serre.eqvGen_eq_inl` of `C1Cyl.lean`.
-/

open scoped Topology unitInterval

namespace Work.Serre.DiscPair

noncomputable section

variable {X Γ' : Type} [TopologicalSpace X] [TopologicalSpace Γ']

/-! ## The bottom copy of a mapping cylinder -/

/-- **A class of the mapping cylinder is a bottom point iff its representative is.**  This holds
for an arbitrary `f : C(P,Q)`: the class of `b` lies in `range (cylIncl f)` exactly when `b` is one
of the points `inl (p,0)` of the bottom circle. -/
lemma mem_range_cylIncl_iff {P Q : Type} [TopologicalSpace P] [TopologicalSpace Q]
    (f : C(P, Q)) (b : (P × unitInterval) ⊕ Q) :
    Work.Serre.cylMk f b ∈ Set.range (Work.Serre.cylIncl f) ↔
      ∃ p : P, b = Sum.inl (p, 0) := by
  constructor
  · rintro ⟨p, hp⟩
    have h : Relation.EqvGen (Work.Serre.cylRel f) b (Sum.inl (p, 0)) := by
      have hp' : (Quotient.mk'' b : Work.Serre.cyl f) = Quotient.mk'' (Sum.inl (p, 0)) :=
        hp.symm
      exact Quotient.exact hp'
    exact ⟨p, Work.Serre.eqvGen_eq_inl (f := f) (p := p) (t := 0) zero_ne_one h⟩
  · rintro ⟨p, rfl⟩
    exact ⟨p, rfl⟩

/-- Two elements of a disjoint union are both of the form `inl (_,0)` or both not. -/
lemma exists_inl_eq_inl_zero {Y Z : Type} (z : Y × unitInterval) :
    (∃ y : Y, (Sum.inl z : (Y × unitInterval) ⊕ Z) = Sum.inl (y, 0)) ↔ z.2 = 0 := by
  constructor
  · rintro ⟨y, hy⟩
    exact congrArg Prod.snd (Sum.inl.inj hy)
  · intro hz
    exact ⟨z.1, congrArg Sum.inl (Prod.ext rfl hz)⟩

/-! ## The comparison of the two cylinders -/

/-- The composite of `cylPreimageLift` with the inclusion into `cyl q` is, on the level of the
presenting disjoint unions, the map induced by `cylEmb`. -/
lemma coe_cylPreimageLift_cylMk (q : C(X, Γ')) (S : Set Γ')
    (b : (↥(q ⁻¹' S) × unitInterval) ⊕ ↥S) :
    ((cylPreimageLift q S (Work.Serre.cylMk (qS q S) b) :
        ↥((Work.Serre.cylRetract q) ⁻¹' S)) : Work.Serre.cyl q)
      = Work.Serre.cylMk q (cylEmb q S b) := by
  rw [cylPreimageLift_cylMk]
  cases b with
  | inl z => exact congrArg Subtype.val (cylPreimageFun_inl q S z)
  | inr y => exact congrArg Subtype.val (cylPreimageFun_inr q S y)

/-- **The main computation**, on the level of the presenting disjoint unions: the image of a class
of `cyl (qS q S)` in `cyl q` is a bottom point iff the class was one. -/
lemma range_cylMk_iff (q : C(X, Γ')) (S : Set Γ')
    (b : (↥(q ⁻¹' S) × unitInterval) ⊕ ↥S) :
    ((cylPreimageLift q S (Work.Serre.cylMk (qS q S) b) :
        ↥((Work.Serre.cylRetract q) ⁻¹' S)) : Work.Serre.cyl q)
        ∈ Set.range (Work.Serre.cylIncl q) ↔
      Work.Serre.cylMk (qS q S) b ∈ Set.range (Work.Serre.cylIncl (qS q S)) := by
  have hcoe : ((cylPreimageLift q S (Work.Serre.cylMk (qS q S) b) :
        ↥((Work.Serre.cylRetract q) ⁻¹' S)) : Work.Serre.cyl q)
      = Work.Serre.cylMk q (cylEmb q S b) :=
    coe_cylPreimageLift_cylMk q S b
  rw [hcoe]
  have h₁ : Work.Serre.cylMk q (cylEmb q S b) ∈ Set.range (Work.Serre.cylIncl q) ↔
      ∃ a : X, cylEmb q S b = Sum.inl (a, 0) :=
    mem_range_cylIncl_iff q (cylEmb q S b)
  have h₂ : Work.Serre.cylMk (qS q S) b ∈ Set.range (Work.Serre.cylIncl (qS q S)) ↔
      ∃ p : ↥(q ⁻¹' S), b = Sum.inl (p, 0) :=
    mem_range_cylIncl_iff (qS q S) b
  rw [h₁, h₂]
  cases b with
  | inl z =>
      rw [cylEmb_inl,
        exists_inl_eq_inl_zero (Y := X) (Z := Γ') (z := (z.1.1, z.2)),
        exists_inl_eq_inl_zero (Y := ↥(q ⁻¹' S)) (Z := ↥S) (z := z)]
  | inr y => simp [cylEmb_inr]

/-! ## The target -/

theorem cylPreimageLift_range {X Γ' : Type} [TopologicalSpace X] [TopologicalSpace Γ']
    (q : C(X, Γ')) (S : Set Γ') (x : Work.Serre.cyl (Work.Serre.DiscPair.qS q S)) :
    ((Work.Serre.DiscPair.cylPreimageLift q S x : ↥((Work.Serre.cylRetract q) ⁻¹' S)) : Work.Serre.cyl q)
        ∈ Set.range (Work.Serre.cylIncl q) ↔
      x ∈ Set.range (Work.Serre.cylIncl (Work.Serre.DiscPair.qS q S)) := by
  revert x
  refine Quotient.ind ?_
  intro b
  exact range_cylMk_iff q S b

end

end Work.Serre.DiscPair
