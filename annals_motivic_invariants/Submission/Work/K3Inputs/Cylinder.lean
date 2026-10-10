import Submission.Work.K3Inputs.Defs

set_option linter.unusedVariables false -- v435-speed

set_option synthInstance.maxHeartbeats 400000 -- v435-synth

/-!
# `Work.K3Inputs.Cylinder` — the cylinder-field layer: (F1), (F2) and the `S × ℙ¹ ≁ S' × ℙ¹`

The two named clauses of the ℙ¹-bundle bridge (`Work.K3Inputs.Defs`) are

* **(F1)** `IsP1BundleOver 𝕜 p X`: the point `p` has function field `κ(X)(t)`;
* **(F2)** `CylinderRigid 𝕜 X Y`: `κ(X)(t) ≅ κ(Y)(t)` descends to a birational map
  `X × ℙ¹ ⤏ Y × ℙ¹` (the paper's Lemma `lem-stbirCY` at `W = ℙ¹`).

This file provides the elementary calculus of these two notions:

* `SameCylinderField` is an equivalence relation (`refl`, `symm`, `trans`);
* (F1) depends only on the *birational class* of the point (`IsP1BundleOver_resEquiv`) and on the
  cylinder field of the model (`Work.K3Inputs.IsP1BundleOver_congr`);
* **`not_sameCylinderField_of_cylinderRigid`** — the *sharp* form of the distinguishing used by
  the `cInv` count: if `X` and `Y` are not stably birational, then their cylinder function fields
  are not isomorphic, i.e. `κ(S)(t) ≇ κ(S')(t)` for the two centres of the K3 link.  This is the
  statement `¬ ResEquiv 𝕜 y x` of the link, at the level of the function fields of the two
  exceptional divisors (`thm:K3`, "Since `S_𝕜` and `S'_𝕜` are non-isomorphic K3 surfaces
  because `S_ℂ ≄ S'_ℂ`, they are not stably birational.  Hence `c(ψ_𝕜) ≠ 0`").
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
attribute [instance] MotivicInvariants.Variety.over MotivicInvariants.Variety.isIntegral

namespace Work.K3Inputs

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
  MotivicInvariants Order

noncomputable section

variable {𝕜 : Type} [Field 𝕜]

/-! ## 1. `SameCylinderField` is an equivalence relation -/

/-- `κ(X)(t) ≅ κ(X)(t)`. -/
theorem SameCylinderField_refl (X : Scheme.{0}) [IsIntegral X] [X.Over (Spec (.of 𝕜))] :
    SameCylinderField 𝕜 X X :=
  ⟨RingEquiv.refl _, rfl⟩

/-- Symmetry of the cylinder-field isomorphism. -/
theorem SameCylinderField_symm {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    [X.Over (Spec (.of 𝕜))] [Y.Over (Spec (.of 𝕜))] (h : SameCylinderField 𝕜 X Y) :
    SameCylinderField 𝕜 Y X := by
  obtain ⟨e, he⟩ := h
  refine ⟨e.symm, ?_⟩
  rw [← he]
  ext a
  simp

/-- Transitivity of the cylinder-field isomorphism. -/
theorem SameCylinderField_trans {X Y Z : Scheme.{0}} [IsIntegral X] [IsIntegral Y] [IsIntegral Z]
    [X.Over (Spec (.of 𝕜))] [Y.Over (Spec (.of 𝕜))] [Z.Over (Spec (.of 𝕜))]
    (h₁ : SameCylinderField 𝕜 X Y) (h₂ : SameCylinderField 𝕜 Y Z) :
    SameCylinderField 𝕜 X Z := by
  obtain ⟨e₁, he₁⟩ := h₁
  obtain ⟨e₂, he₂⟩ := h₂
  refine ⟨e₁.trans e₂, ?_⟩
  rw [RingEquiv.toRingHom_trans', RingHom.comp_assoc, he₁, he₂]

/-! ## 2. (F1) depends only on the birational class of the point -/

/-- **(F1) is invariant under `ResEquiv` of the point.**  If `p` and `p'` have isomorphic residue
fields over `𝕜` and `p` has the cylinder field of `X` as its function field, then so does `p'`.
This is what allows the clause (F1) to be stated for an arbitrary point of the divisor (the model
of the exceptional divisor) rather than for its generic point. -/
theorem IsP1BundleOver_resEquiv {P X : Scheme.{0}} [P.Over (Spec (.of 𝕜))] [IsIntegral X]
    [X.Over (Spec (.of 𝕜))] {p p' : P} (h : ResEquiv 𝕜 p p')
    (hp : IsP1BundleOver 𝕜 p X) : IsP1BundleOver 𝕜 p' X := by
  obtain ⟨e₁, he₁⟩ := hp
  obtain ⟨e, he⟩ := h
  refine ⟨e.symm.trans e₁, ?_⟩
  rw [RingEquiv.toRingHom_trans', RingHom.comp_assoc]
  have h1 : e.symm.toRingHom.comp (resMap 𝕜 P p') = resMap 𝕜 P p := by
    rw [← he]
    ext a
    simp
  rw [h1, he₁]

/-! ## 3. The distinguishing `κ(S)(t) ≇ κ(S')(t)` -/

/-- **The `S × ℙ¹ ≁ S' × ℙ¹` statement, at the function-field level.**

If the cylinder rigidity (F2) holds for `X`, `Y` and `X`, `Y` are *not* stably birational, then
their cylinder function fields are not isomorphic.  Concretely: (F2) would turn a
`𝕜`-isomorphism `κ(X)(t) ≅ κ(Y)(t)` into a birational map `X × ℙ¹ ⤏ Y × ℙ¹`, i.e. into
`StablyBirat 𝕜 X Y` with exponents `(1,1)`.

For the two centres `S`, `S'` of the K3 L-link this is exactly `κ(S)(t) ≇ κ(S')(t)`, the input
`¬ ResEquiv 𝕜 y x` of the link (the two exceptional divisors are `ℙ¹`-bundles over `S` and `S'`),
which is what makes the `[κ(S)(t)]`-coefficient of `c(ψ)` equal to `1`. -/
theorem not_sameCylinderField_of_cylinderRigid {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    [X.Over (Spec (.of 𝕜))] [Y.Over (Spec (.of 𝕜))] (hrigid : CylinderRigid 𝕜 X Y)
    (h : ¬ StablyBirat 𝕜 X Y) : ¬ SameCylinderField 𝕜 X Y := fun hsc =>
  h ⟨1, 1, hrigid hsc⟩

/-- **(F2) in the sharp form**: the descent of `lem-stbirCY` yields a partial isomorphism of the
cylinders *over* `Spec 𝕜` (the paper's construction is over the base field).  This is the form in
which (F2) interacts with `SameCylinderField`, whose isomorphism is `𝕜`-linear — see
`Work.K3Inputs.sameCylinderField_iff_cyl_birational`. -/
def CylinderRigidOver (𝕜 : Type) [Field 𝕜] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y]
    [X.Over (Spec (.of 𝕜))] [Y.Over (Spec (.of 𝕜))] : Prop :=
  SameCylinderField 𝕜 X Y →
    ∃ i : (Cyl 𝕜 X).PartialIso (Cyl 𝕜 Y),
      i.IsOver (Cyl 𝕜 X ↘ Spec (.of 𝕜)) (Cyl 𝕜 Y ↘ Spec (.of 𝕜))

/-- The sharp form of (F2) implies (F2). -/
theorem CylinderRigidOver.toCylinderRigid {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    [X.Over (Spec (.of 𝕜))] [Y.Over (Spec (.of 𝕜))] (h : CylinderRigidOver 𝕜 X Y) :
    CylinderRigid 𝕜 X Y :=
  fun hsc => ⟨(h hsc).choose⟩

/-- The contrapositive, in the form in which the link consumes it: a `ResEquiv` of the two
exceptional divisors (i.e. `κ(y) ≅ κ(x)`) forces the two centres to be stably birational. -/
theorem stablyBirat_of_resEquiv_of_cylinders {P S S' : Scheme.{0}} [IsIntegral S]
    [IsIntegral S'] [P.Over (Spec (.of 𝕜))] [S.Over (Spec (.of 𝕜))] [S'.Over (Spec (.of 𝕜))]
    {y x : P} (hy : IsP1BundleOver 𝕜 y S) (hx : IsP1BundleOver 𝕜 x S')
    (hrigid : CylinderRigid 𝕜 S S') (hres : ResEquiv 𝕜 y x) : StablyBirat 𝕜 S S' :=
  bridge_of_clauses hy hx hrigid hres

end

end Work.K3Inputs
