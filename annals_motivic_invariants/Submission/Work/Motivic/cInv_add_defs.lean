import Mathlib
import Submission.Work.Motivic.Defs

set_option linter.unusedVariables false -- v435-speed

/-!
# Infrastructure for the additivity of the Lin–Shinder invariant

This file collects the definitions and elementary lemmas the proof of
`Work.Motivic.cInv_add` is phrased with:

* `wgt 𝕜 w A` — the number of points of `A` whose residue field is isomorphic, as a `𝕜`-algebra,
  to the residue field of `w`.  By definition `excCount 𝕜 w φ = wgt 𝕜 w (exDiv φ)`.
* `phiPt φ p` — for a birational map `φ : X ⤏ Y` and a point `x` at which `φ` is an isomorphism,
  the image `φ x ∈ Y`, obtained by evaluating a partial isomorphism representing `φ.hom` at `x`.
* `ResEquiv` is an equivalence relation (`ResEquiv.refl`, `.symm`, `.trans`).
* `wgt` is unchanged by a bijection that matches residue fields (`wgt_eq_of_bijection`) and is
  additive over a disjoint partition of a finite set (`wgt_inter_add_wgt_sdiff`).
-/

namespace Work.Motivic

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme MotivicInvariants Order

/-- The weight of a set of points with respect to a base point `w`: the number of points of the
set whose residue field is `𝕜`-isomorphic to `κ(w)`. -/
noncomputable def wgt (𝕜 : Type) [Field 𝕜] {X W : Scheme.{0}} [X.Over (Spec (.of 𝕜))]
    [W.Over (Spec (.of 𝕜))] (w : W) (A : Set X) : ℕ :=
  (A ∩ {x | ResEquiv 𝕜 x w}).ncard

/-- `excCount` is the weight of the exceptional divisor set. -/
lemma excCount_eq_wgt (𝕜 : Type) [Field 𝕜] {X Y Z : Scheme.{0}} [IrreducibleSpace X]
    [IrreducibleSpace Y] [X.Over (Spec (.of 𝕜))] [Z.Over (Spec (.of 𝕜))] (z : Z)
    (φ : X.BirationalMap Y) : excCount 𝕜 z φ = wgt 𝕜 z (exDiv φ) := rfl

lemma wgt_congr {𝕜 : Type} [Field 𝕜] {X W : Scheme.{0}} [X.Over (Spec (.of 𝕜))]
    [W.Over (Spec (.of 𝕜))] (w : W) {A B : Set X} (h : A = B) : wgt 𝕜 w A = wgt 𝕜 w B := by
  rw [h]

@[simp]
lemma wgt_empty {𝕜 : Type} [Field 𝕜] {X W : Scheme.{0}} [X.Over (Spec (.of 𝕜))]
    [W.Over (Spec (.of 𝕜))] (w : W) : wgt 𝕜 w (∅ : Set X) = 0 := by
  simp [wgt]

/-- `ResEquiv` is reflexive. -/
lemma ResEquiv.refl (𝕜 : Type) [Field 𝕜] {X : Scheme.{0}} [X.Over (Spec (.of 𝕜))] (x : X) :
    ResEquiv 𝕜 x x :=
  ⟨RingEquiv.refl _, by ext a; rfl⟩

/-- `ResEquiv` is symmetric. -/
lemma ResEquiv.symm {𝕜 : Type} [Field 𝕜] {X Z : Scheme.{0}} [X.Over (Spec (.of 𝕜))]
    [Z.Over (Spec (.of 𝕜))] {x : X} {z : Z} (h : ResEquiv 𝕜 x z) : ResEquiv 𝕜 z x := by
  obtain ⟨e, he⟩ := h
  refine ⟨e.symm, ?_⟩
  rw [← he, ← RingHom.comp_assoc]
  simp [RingEquiv.toRingHom_eq_coe]

/-- `ResEquiv` is transitive. -/
lemma ResEquiv.trans {𝕜 : Type} [Field 𝕜] {X Y Z : Scheme.{0}} [X.Over (Spec (.of 𝕜))]
    [Y.Over (Spec (.of 𝕜))] [Z.Over (Spec (.of 𝕜))] {x : X} {y : Y} {z : Z}
    (h₁ : ResEquiv 𝕜 x y) (h₂ : ResEquiv 𝕜 y z) : ResEquiv 𝕜 x z := by
  obtain ⟨e₁, he₁⟩ := h₁
  obtain ⟨e₂, he₂⟩ := h₂
  refine ⟨e₁.trans e₂, ?_⟩
  rw [show (e₁.trans e₂).toRingHom = e₂.toRingHom.comp e₁.toRingHom from rfl]
  rw [RingHom.comp_assoc, he₁, he₂]

/-- For a birational map `φ : X ⤏ Y` and a point `x` at which `φ` is an isomorphism, `φ x`:
choose a partial isomorphism `i` representing `φ.hom` with `x` in its source and evaluate `i`
at `x`. -/
noncomputable def phiPt {X Y : Scheme.{0}} [IrreducibleSpace X] [IrreducibleSpace Y]
    (φ : X.BirationalMap Y) (p : {x : X // IsIsoAt φ x}) : Y :=
  (p.2.choose.target.ι) (p.2.choose.iso.hom ⟨p.1, p.2.choose_spec.1⟩)

/-- The weight of a *finite* set is additive over a disjoint partition. -/
lemma wgt_inter_add_wgt_sdiff {𝕜 : Type} [Field 𝕜] {X W : Scheme.{0}} [X.Over (Spec (.of 𝕜))]
    [W.Over (Spec (.of 𝕜))] (w : W) {A B : Set X} (hA : A.Finite) :
    wgt 𝕜 w A = wgt 𝕜 w (A ∩ B) + wgt 𝕜 w (A \ B) := by
  have hmem : A ∩ {x | ResEquiv 𝕜 x w} =
      ((A ∩ B) ∩ {x | ResEquiv 𝕜 x w}) ∪ ((A \ B) ∩ {x | ResEquiv 𝕜 x w}) := by
    rw [← Set.union_inter_distrib_right, Set.inter_union_sdiff]
  have hdisj : Disjoint ((A ∩ B) ∩ {x | ResEquiv 𝕜 x w}) ((A \ B) ∩ {x | ResEquiv 𝕜 x w}) := by
    rw [Set.disjoint_left]; intro x h1 h2; exact h2.1.2 h1.1.2
  have hfin : (A ∩ {x | ResEquiv 𝕜 x w}).Finite := hA.subset Set.inter_subset_left
  have hfinL : (((A ∩ B) ∩ {x | ResEquiv 𝕜 x w}).Finite) :=
    hfin.subset fun x hx => ⟨hx.1.1, hx.2⟩
  have hfinR : (((A \ B) ∩ {x | ResEquiv 𝕜 x w}).Finite) :=
    hfin.subset fun x hx => ⟨hx.1.1, hx.2⟩
  have h := Set.ncard_union_eq hdisj hfinL hfinR
  simp only [wgt]
  rw [hmem, h]

/-- A bijection between two sets of points that matches residue fields in the sense of
`ResEquiv` preserves the weight. -/
lemma wgt_eq_of_bijection {𝕜 : Type} [Field 𝕜] {X Y W : Scheme.{0}} [X.Over (Spec (.of 𝕜))]
    [Y.Over (Spec (.of 𝕜))] [W.Over (Spec (.of 𝕜))] (w : W) {A : Set X} {B : Set Y}
    (e : A ≃ B) (h : ∀ a : A, ResEquiv 𝕜 a.1 (e a).1) : wgt 𝕜 w A = wgt 𝕜 w B := by
  refine Set.ncard_congr (fun a ha => (e ⟨a, ha.1⟩).1) ?_ ?_ ?_
  · rintro a ⟨haA, haw⟩
    exact ⟨(e ⟨a, haA⟩).2, ResEquiv.trans (ResEquiv.symm (h ⟨a, haA⟩)) haw⟩
  · rintro a b ⟨haA, _⟩ ⟨hbA, _⟩ hab
    have : (e ⟨a, haA⟩) = (e ⟨b, hbA⟩) := Subtype.ext hab
    exact congrArg Subtype.val (e.injective this)
  · rintro b ⟨hbB, hbw⟩
    refine ⟨(e.symm ⟨b, hbB⟩).1, ⟨(e.symm ⟨b, hbB⟩).2, ?_⟩, ?_⟩
    · have h1 : ResEquiv 𝕜 ((e.symm ⟨b, hbB⟩) : A).1 b := by
        simpa using h (e.symm ⟨b, hbB⟩)
      exact ResEquiv.trans h1 hbw
    · simp

/-- For a variety over `𝕜` the structure morphism to `Spec 𝕜` is separated. -/
instance variety_isSeparated (𝕜 : Type) [Field 𝕜] {X : Scheme.{0}} [Variety 𝕜 X] :
    IsSeparated (X ↘ Spec (.of 𝕜)) :=
  Variety.isSeparated

/-- A variety over `𝕜` is a Noetherian topological space. -/
lemma variety_noetherianSpace (𝕜 : Type) [Field 𝕜] {X : Scheme.{0}} [Variety 𝕜 X] :
    TopologicalSpace.NoetherianSpace X := by
  haveI h1 : LocallyOfFiniteType (X ↘ Spec (.of 𝕜)) := Variety.locallyOfFiniteType
  haveI h2 : QuasiCompact (X ↘ Spec (.of 𝕜)) := Variety.quasicompact
  haveI h3 : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (Y := Spec (.of 𝕜)) (X ↘ Spec (.of 𝕜))
  haveI h4 : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of 𝕜))
  haveI h5 : IsNoetherian X := AlgebraicGeometry.IsNoetherian.mk
  exact IsNoetherian.noetherianSpace

end Work.Motivic
