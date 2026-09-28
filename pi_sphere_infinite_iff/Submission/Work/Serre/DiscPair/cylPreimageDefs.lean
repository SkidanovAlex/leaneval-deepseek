import Mathlib
import Submission.Work.Serre.C1Cyl

/-!
# Base change for the mapping cylinder along a preimage

For `q : C(X, Γ')` and `S ⊆ Γ'` we compare the relative chain complex of the pair
`((cylRetract q) ⁻¹' S , (cylIncl q) '' (q ⁻¹' S))` inside the mapping cylinder `cyl q` with the
relative chain complex of the disc pair `(cyl (q|_S), (cylIncl (q|_S)) '' q⁻¹S)` of the restricted
map `q|_S : q⁻¹S → S`.  The two spaces are the same quotient (of the same presenting disjoint
union) and `Work.Serre.DiscPair.cylPreimageRelIso` records that their relative *homology* agrees.

The mathematical content is the topological statement that the restriction of the quotient map
defining `cyl q` to the preimage of `W := (cylRetract q) ⁻¹' S` is again a quotient map: this holds
because the equivalence relation of the mapping cylinder has finite classes and `W` is saturated.
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open scoped Topology unitInterval

namespace Work.Serre.DiscPair

noncomputable section

variable {X Γ' : Type} [TopologicalSpace X] [TopologicalSpace Γ']

/-! ## Elementary computations in the mapping cylinder -/

@[simp] lemma cylRetract_cylMk {P Q : Type} [TopologicalSpace P] [TopologicalSpace Q]
    (f : C(P, Q)) (a : (P × unitInterval) ⊕ Q) :
    Work.Serre.cylRetract f (Work.Serre.cylMk f a) = Work.Serre.cylRetractFun f a := rfl

@[simp] lemma cylRetractFun_inl {P Q : Type} [TopologicalSpace P] [TopologicalSpace Q]
    (f : C(P, Q)) (a : P) (t : unitInterval) :
    Work.Serre.cylRetractFun f (Sum.inl (a, t)) = f a := rfl

@[simp] lemma cylRetractFun_inr {P Q : Type} [TopologicalSpace P] [TopologicalSpace Q]
    (f : C(P, Q)) (x : Q) : Work.Serre.cylRetractFun f (Sum.inr x) = x := rfl

/-- The restriction of `q` to `q ⁻¹' S`, as a map onto `S`. -/
def qS (q : C(X, Γ')) (S : Set Γ') : C(↥(q ⁻¹' S), ↥S) :=
  ⟨fun x => ⟨q x.1, x.2⟩, by fun_prop⟩

@[simp] lemma qS_apply (q : C(X, Γ')) (S : Set Γ') (x : ↥(q ⁻¹' S)) :
    (qS q S) x = ⟨q x.1, x.2⟩ := rfl

lemma qS_coe (q : C(X, Γ')) (S : Set Γ') (x : ↥(q ⁻¹' S)) :
    ((qS q S) x : Γ') = q x.1 := rfl

/-- The inclusion of the presenting disjoint union of `cyl (qS q S)` into that of `cyl q`. -/
def cylEmb (q : C(X, Γ')) (S : Set Γ') :
    (↥(q ⁻¹' S) × unitInterval) ⊕ ↥S → (X × unitInterval) ⊕ Γ' :=
  Sum.elim (fun z => Sum.inl (z.1.1, z.2)) (fun y => Sum.inr y.1)

@[simp] lemma cylEmb_inl (q : C(X, Γ')) (S : Set Γ') (z : ↥(q ⁻¹' S) × unitInterval) :
    cylEmb q S (Sum.inl z) = Sum.inl (z.1.1, z.2) := rfl

@[simp] lemma cylEmb_inr (q : C(X, Γ')) (S : Set Γ') (y : ↥S) :
    cylEmb q S (Sum.inr y) = Sum.inr y.1 := rfl

/-- The map on the level of the presenting disjoint unions: the identity on
`q⁻¹S × I` and on `S`, read in `cyl q`. -/
def cylPreimageFun (q : C(X, Γ')) (S : Set Γ') :
    (↥(q ⁻¹' S) × unitInterval) ⊕ ↥S → ↥((Work.Serre.cylRetract q) ⁻¹' S) :=
  Sum.elim
    (fun z => ⟨Work.Serre.cylMk q (Sum.inl (z.1.1, z.2)), by
      show Work.Serre.cylRetract q (Work.Serre.cylMk q (Sum.inl (z.1.1, z.2))) ∈ S
      rw [cylRetract_cylMk, cylRetractFun_inl]
      exact z.1.2⟩)
    (fun y => ⟨Work.Serre.cylInr q y.1, by
      show Work.Serre.cylRetract q (Work.Serre.cylInr q y.1) ∈ S
      have h : Work.Serre.cylInr q y.1 = Work.Serre.cylMk q (Sum.inr y.1) := rfl
      rw [h, cylRetract_cylMk, cylRetractFun_inr]
      exact y.2⟩)

@[simp] lemma cylPreimageFun_inl (q : C(X, Γ')) (S : Set Γ')
    (z : ↥(q ⁻¹' S) × unitInterval) :
    cylPreimageFun q S (Sum.inl z)
      = ⟨Work.Serre.cylMk q (Sum.inl (z.1.1, z.2)), by
          show Work.Serre.cylRetract q (Work.Serre.cylMk q (Sum.inl (z.1.1, z.2))) ∈ S
          rw [cylRetract_cylMk, cylRetractFun_inl]
          exact z.1.2⟩ := rfl

@[simp] lemma cylPreimageFun_inr (q : C(X, Γ')) (S : Set Γ') (y : ↥S) :
    cylPreimageFun q S (Sum.inr y)
      = ⟨Work.Serre.cylInr q y.1, by
          show Work.Serre.cylRetract q (Work.Serre.cylInr q y.1) ∈ S
          have h : Work.Serre.cylInr q y.1 = Work.Serre.cylMk q (Sum.inr y.1) := rfl
          rw [h, cylRetract_cylMk, cylRetractFun_inr]
          exact y.2⟩ := rfl

/-- The value of `cylPreimageFun` only depends on the class in `cyl (qS q S)`. -/
lemma cylPreimageFun_rel (q : C(X, Γ')) (S : Set Γ') :
    ∀ a b, Relation.EqvGen (Work.Serre.cylRel (qS q S)) a b →
      cylPreimageFun q S a = cylPreimageFun q S b := by
  have hgen : ∀ a b, Work.Serre.cylRel (qS q S) a b →
      cylPreimageFun q S a = cylPreimageFun q S b := by
    rintro a b ⟨p, rfl, rfl⟩
    apply Subtype.ext
    show Work.Serre.cylMk q (Sum.inl (p.1, (1 : unitInterval)))
      = Work.Serre.cylInr q (q p.1)
    exact Work.Serre.cyl_mk_inl_one q p.1
  intro a b hab
  induction hab with
  | rel x y h => exact hgen x y h
  | refl x => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2

/-- The set presenting the preimage of `(cylRetract q) ⁻¹' S` in the disjoint union. -/
def cylPreSet (q : C(X, Γ')) (S : Set Γ') : Set ((X × unitInterval) ⊕ Γ') :=
  Work.Serre.cylMk q ⁻¹' ((Work.Serre.cylRetract q) ⁻¹' S)

lemma mem_cylPreSet (q : C(X, Γ')) (S : Set Γ') (a : (X × unitInterval) ⊕ Γ') :
    a ∈ cylPreSet q S ↔ Work.Serre.cylRetractFun q a ∈ S := by
  rw [cylPreSet, Set.mem_preimage, Set.mem_preimage, cylRetract_cylMk]

lemma mem_cylPreSet_inl (q : C(X, Γ')) (S : Set Γ') (a : X) (t : unitInterval) :
    Sum.inl (a, t) ∈ cylPreSet q S ↔ q a ∈ S := by
  rw [mem_cylPreSet, cylRetractFun_inl]

lemma mem_cylPreSet_inr (q : C(X, Γ')) (S : Set Γ') (y : Γ') :
    Sum.inr y ∈ cylPreSet q S ↔ y ∈ S := by
  rw [mem_cylPreSet, cylRetractFun_inr]

/-- The preimage of `S` under the retraction, presented as `cylPreSet`. -/
lemma restrictPreimage_cylPreSet (q : C(X, Γ')) (S : Set Γ') :
    ((Work.Serre.cylRetract q) ⁻¹' S).restrictPreimage (Work.Serre.cylMk q)
      = fun a : ↥(cylPreSet q S) => ⟨Work.Serre.cylMk q a.1, a.2⟩ := rfl

lemma continuous_cylPreimageFun (q : C(X, Γ')) (S : Set Γ') :
    Continuous (cylPreimageFun q S) := by
  rw [cylPreimageFun]
  apply Continuous.sumElim
  · refine Continuous.subtype_mk ?_ _
    exact (continuous_quotient_mk').comp
      (continuous_inl.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd))
  · refine Continuous.subtype_mk ?_ _
    exact (continuous_quotient_mk').comp (continuous_inr.comp continuous_subtype_val)

/-- The map `cyl (qS q S) → (cylRetract q) ⁻¹' S` induced by the identity on the presenting
disjoint unions. -/
def cylPreimageLift (q : C(X, Γ')) (S : Set Γ') :
    Work.Serre.cyl (qS q S) → ↥((Work.Serre.cylRetract q) ⁻¹' S) :=
  Quotient.lift (cylPreimageFun q S) (cylPreimageFun_rel q S)

lemma cylPreimageLift_mk (q : C(X, Γ')) (S : Set Γ')
    (a : (↥(q ⁻¹' S) × unitInterval) ⊕ ↥S) :
    cylPreimageLift q S (Quotient.mk'' a) = cylPreimageFun q S a :=
  @Quotient.lift_mk _ _ (Relation.EqvGen.setoid (Work.Serre.cylRel (qS q S)))
    (cylPreimageFun q S) (cylPreimageFun_rel q S) a

@[simp] lemma cylPreimageLift_cylMk (q : C(X, Γ')) (S : Set Γ')
    (a : (↥(q ⁻¹' S) × unitInterval) ⊕ ↥S) :
    cylPreimageLift q S (Work.Serre.cylMk (qS q S) a) = cylPreimageFun q S a :=
  @Quotient.lift_mk _ _ (Relation.EqvGen.setoid (Work.Serre.cylRel (qS q S)))
    (cylPreimageFun q S) (cylPreimageFun_rel q S) a

lemma continuous_cylPreimageLift (q : C(X, Γ')) (S : Set Γ') :
    Continuous (cylPreimageLift q S) :=
  Continuous.quotient_lift (continuous_cylPreimageFun q S) (cylPreimageFun_rel q S)

lemma mem_cylPreSet_emb (q : C(X, Γ')) (S : Set Γ')
    (a : (↥(q ⁻¹' S) × unitInterval) ⊕ ↥S) : cylEmb q S a ∈ cylPreSet q S := by
  rcases a with ⟨u, t⟩ | y
  · rw [cylEmb_inl, mem_cylPreSet_inl]; exact u.2
  · rw [cylEmb_inr, mem_cylPreSet_inr]; exact y.2

/-- The restriction of the quotient map `cylMk q` to the preimage of `(cylRetract q) ⁻¹' S`. -/
def cylPreSetRestrict (q : C(X, Γ')) (S : Set Γ') :
    ↥(cylPreSet q S) → ↥((Work.Serre.cylRetract q) ⁻¹' S) :=
  fun a => ⟨Work.Serre.cylMk q a.1, a.2⟩



/-! ## The comparison map and its bijectivity -/


end

end Work.Serre.DiscPair
