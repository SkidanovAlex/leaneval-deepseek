import Mathlib
import Submission.Work.K3.Main
import Submission.Work.CrauderKatz.functionField_prod_affineLine
import Submission.Work.Motivic.exists_partialIso_toBirationalMap

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.K3Inputs.Defs` — vocabulary for the K3-INPUTS area

This area supplies the *named inputs* of the K3 chapter `Submission/Work/K3`
(`Work.K3.TerasomaInput`, `Work.K3.HassettLaiTheorem`, `Work.K3.TotaroInput`,
`Work.K3.K3Stabilisation`) — the `n ≥ 4` case of Theorem 1.2 (2) of the challenge, i.e. the
(1_2_2) chain — decomposed into the paper's own numbered statements (Lin–Shinder, *Motivic
invariants of birational maps*, Annals **199** (1), 2024, § *K3 surfaces of degree 12*,
tex 2186–2404), together with everything that can be **proved** about them:

* the ℙ¹-bundle bridge of Lemma `lemma:L-link` (2) — the field `Work.K3.K3Data.bridge` is here
  *derived* from the two geometric clauses (F1) (the exceptional divisors have function field
  `κ(S)(t)`, `κ(S')(t)`) and (F2) (the cylinder rigidity `lem-stbirCY` at `W = ℙ¹`);
* the calculus of stable birationality (`StablyBirat` below, and
  `Work.K3Inputs.stablyBirational_iff` identifying it with `Work.K3.StablyBirational`);
* the descent of Terasoma's input from `ℚ` to `𝕜 ⊆ ℂ`;
* Totaro's `cor-CYnSB` and the `K3 → K3 × ℙ¹` distinguishing used by the `cInv` count.

## Conventions

* `𝕜` is a field; `Spec (.of 𝕜)` is the base; `𝔸(Fin n; Spec (.of 𝕜))` is affine `n`-space;
* **`ℙ¹` is modelled by `𝔸¹`** throughout (`Affine1`), since only the birational class matters: the
  new notion is `Cyl X = X × 𝔸¹`, the *cylinder* of `X`.  (Mathlib has no projective space.)
* The *cylinder function field* `κ(X)(t)` is the model `RatFunc κ(X)` of `κ(X × ℙ¹)`; the
  identification with the function field of the honest fibre product is
  `Work.CrauderKatz.functionField_prod_affineLine` (proved in the sibling area).
* `Scheme.Birational X Y := Nonempty (X.PartialIso Y)` is Mathlib's birationality; for
  irreducible `X`, `Y` it agrees with `Nonempty (X.BirationalMap Y)`
  (`Work.Motivic.exists_partialIso_toBirationalMap` and `PartialIso.toBirationalMap`).
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

/-! ## 1. The cylinder `X × 𝔸¹` and affine `n`-space -/

/-- The affine line `𝔸¹_𝕜` — our model of `ℙ¹` (only the birational class matters). -/
abbrev Affine1 (𝕜 : Type) [Field 𝕜] : Scheme.{0} := 𝔸(Fin 1; Spec (.of 𝕜))

/-- Affine `n`-space over `𝕜` in the exponent form used by `Work.K3.StablyBirational`. -/
abbrev AffineN (𝕜 : Type) [Field 𝕜] (n : ℕ) : Scheme.{0} := 𝔸(Fin n; Spec (.of 𝕜))

/-- **The cylinder of `X`**: the fibre product `X ×_{Spec 𝕜} 𝔸¹_𝕜`, our model of `X × ℙ¹`. -/
abbrev Cyl (𝕜 : Type) [Field 𝕜] (X : Scheme.{0}) [X.Over (Spec (.of 𝕜))] : Scheme.{0} :=
  Work.K3.prodOver 𝕜 X (Affine1 𝕜)

instance cylOver (X : Scheme.{0}) [X.Over (Spec (.of 𝕜))] :
    (Cyl 𝕜 X).Over (Spec (.of 𝕜)) :=
  Work.K3.prodOverOver X (Affine1 𝕜)

/-- The cylinder is the `n = 1` case of the exponent family of `Work.K3.StablyBirational`. -/
theorem cyl_eq_prodOver (X : Scheme.{0}) [X.Over (Spec (.of 𝕜))] :
    Cyl 𝕜 X = Work.K3.prodOver 𝕜 X (AffineN 𝕜 1) := rfl

/-! ## 2. Stable birationality without `Variety` instances

`Work.K3.StablyBirational` binds a `Variety` instance for each of the two products inside its
existential, so *producing* a term of it requires exhibiting those instances.  For the algebra of
this area we use the same relation stated with Mathlib's `Scheme.Birational`
(`= Nonempty (PartialIso _ _)`, which needs no instance); the two agree on varieties
(`Work.K3Inputs.stablyBirational_iff`). -/

/-- **Stable birationality** over `𝕜`: `X × 𝔸ⁿ` is birational to `Y × 𝔸ᵐ` for some `n, m`.

This is `Work.K3.StablyBirational` with Mathlib's `Scheme.Birational` in place of
`Nonempty (BirationalMap _ _)` and without the `Variety` instance arguments. -/
def StablyBirat (𝕜 : Type) [Field 𝕜] (X Y : Scheme.{0}) [X.Over (Spec (.of 𝕜))]
    [Y.Over (Spec (.of 𝕜))] : Prop :=
  ∃ n m : ℕ, Scheme.Birational (Work.K3.prodOver 𝕜 X (AffineN 𝕜 n))
    (Work.K3.prodOver 𝕜 Y (AffineN 𝕜 m))

/-! ## 3. The cylinder function field `κ(X)(t)` -/

/-- The function field `κ(X)` of an integral scheme, as a type. -/
abbrev funField (X : Scheme.{0}) [IsIntegral X] : Type := (X.functionField : Type)

/-- **The cylinder function field** `κ(X)(t) = RatFunc κ(X)`, the function field of `X × ℙ¹`. -/
abbrev cylField (𝕜 : Type) [Field 𝕜] (X : Scheme.{0}) [IsIntegral X] : Type :=
  RatFunc (funField X)

/-- The structure map `𝕜 → κ(X)(t)` (the constants). -/
def cylResMap (𝕜 : Type) [Field 𝕜] (X : Scheme.{0}) [IsIntegral X]
    [X.Over (Spec (.of 𝕜))] : 𝕜 →+* RatFunc (funField X) :=
  (algebraMap (funField X) (RatFunc (funField X))).comp
    (Work.CrauderKatz.functionFieldResMap 𝕜 X)

/-- **The two cylinder function fields agree.**  `κ(X)(t) ≅ κ(Y)(t)` as `𝕜`-extensions; this is
the hypothesis of the cylinder-rigidity clause (F2). -/
def SameCylinderField (𝕜 : Type) [Field 𝕜] (X Y : Scheme.{0}) [IsIntegral X]
    [IsIntegral Y] [X.Over (Spec (.of 𝕜))] [Y.Over (Spec (.of 𝕜))] : Prop :=
  ∃ e : RatFunc (funField X) ≃+* RatFunc (funField Y),
    e.toRingHom.comp (cylResMap 𝕜 X) = cylResMap 𝕜 Y

/-! ## 4. The two named geometric clauses of the ℙ¹-bundle bridge -/

/-- **(F1) of `lemma:L-link` (2)**: the point `p` (an exceptional divisor of the link) is
birational to `X × ℙ¹`, i.e. its function field is `κ(X)(t)`.

This is exactly the paper's "the exceptional divisor of `Bl_{S_0}` is birational to
`S_0 × ℙ¹`, which is further birational to `S × ℙ¹`", at the level of function fields.  It is a
named clause in the K3 chapter's vocabulary: Mathlib has no blow-ups (`Bl_{S_0}ℙ⁴`), no
normalisation and no `ℙ⁴`. -/
def IsP1BundleOver (𝕜 : Type) [Field 𝕜] {P : Scheme.{0}} [P.Over (Spec (.of 𝕜))] (p : P)
    (X : Scheme.{0}) [IsIntegral X] [X.Over (Spec (.of 𝕜))] : Prop :=
  ∃ e : P.residueField p ≃+* RatFunc (funField X),
    e.toRingHom.comp (resMap 𝕜 P p) = cylResMap 𝕜 X

/-- **(F2): the cylinder rigidity of Lemma `lem-stbirCY` at `W = ℙ¹`.**  An isomorphism
`κ(X)(t) ≅ κ(Y)(t)` of cylinder fields descends: the cylinder `X × ℙ¹` is birational to
`Y × ℙ¹`.

The paper's `lem-stbirCY`: for smooth projective `Z`, `Z'` of the same dimension which are not
separably uniruled, every birational map `Z × W ⤏ Z' × W` (with `W` separably rationally
connected, e.g. `W = ℙ¹`) comes from a birational map `Z ⤏ Z'`.  K3 surfaces are not separably
uniruled, so for `X`, `Y` K3 surfaces this clause holds; the *proof* of it needs separably uniruled
varieties, and is recorded as a named clause, as in the sibling area `Submission/Work/CrauderKatz`
(the field `CylinderDetectsCurve`). -/
def CylinderRigid (𝕜 : Type) [Field 𝕜] (X Y : Scheme.{0}) [IsIntegral X]
    [IsIntegral Y] [X.Over (Spec (.of 𝕜))] [Y.Over (Spec (.of 𝕜))] : Prop :=
  SameCylinderField 𝕜 X Y → Scheme.Birational (Cyl 𝕜 X) (Cyl 𝕜 Y)

/-- **The cylinder rigidity gives stable birationality.**  An isomorphism of the cylinder function
fields of `X` and `Y` yields a birational map `X × ℙ¹ ⤏ Y × ℙ¹` by (F2), i.e. `StablyBirat 𝕜 X Y`
with exponents `1, 1`.

This is stated as a separate result (rather than inlined) so that the `Over`-instance arguments of
`StablyBirat` and of `CylinderRigid` are unified with *each other's* (both are the implicit
`Over`-instance arguments of this statement), rather than with instances synthesized at the call
site. -/
theorem stablyBirat_of_cylinderRigid {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    [X.Over (Spec (.of 𝕜))] [Y.Over (Spec (.of 𝕜))] (hrigid : CylinderRigid 𝕜 X Y)
    (h : SameCylinderField 𝕜 X Y) : StablyBirat 𝕜 X Y :=
  ⟨1, 1, hrigid h⟩

/-- **The ℙ¹-bundle bridge, proved.**  If the two exceptional divisors `y`, `x` of the link have
cylinder function fields `κ(S)(t)`, `κ(S')(t)` (F1), and the cylinder rigidity (F2) holds for
`S`, `S'`, then an isomorphism `κ(y) ≅ κ(x)` of their function fields makes `S` and `S'` stably
birational.  This is precisely the field `bridge` of `Work.K3.K3Data`, *derived* from (F1) and
(F2) instead of assumed. -/
theorem bridge_of_clauses {P S S' : Scheme.{0}} [IsIntegral S] [IsIntegral S']
    [P.Over (Spec (.of 𝕜))] [S.Over (Spec (.of 𝕜))] [S'.Over (Spec (.of 𝕜))]
    {y x : P} (hy : IsP1BundleOver 𝕜 y S) (hx : IsP1BundleOver 𝕜 x S')
    (hrigid : CylinderRigid 𝕜 S S') (hres : ResEquiv 𝕜 y x) : StablyBirat 𝕜 S S' := by
  obtain ⟨ey, hey⟩ := hy
  obtain ⟨ex, hex⟩ := hx
  obtain ⟨e, he⟩ := hres
  have hcomp : ((ey.symm.trans (e.trans ex)).toRingHom).comp (cylResMap 𝕜 S) =
      cylResMap 𝕜 S' := by
    ext a
    have h1 : ey.symm (cylResMap 𝕜 S a) = resMap 𝕜 P y a := by
      have h := RingHom.congr_fun hey a
      simp only [RingHom.comp_apply] at h
      rw [← h]
      exact RingEquiv.symm_apply_apply ey (resMap 𝕜 P y a)
    have h2 : e (resMap 𝕜 P y a) = resMap 𝕜 P x a := RingHom.congr_fun he a
    have h3 : ex (resMap 𝕜 P x a) = cylResMap 𝕜 S' a := RingHom.congr_fun hex a
    change (ey.symm.trans (e.trans ex)) (cylResMap 𝕜 S a) = cylResMap 𝕜 S' a
    rw [RingEquiv.trans_apply, RingEquiv.trans_apply, h1, h2, h3]
  have hSame : SameCylinderField 𝕜 S S' := ⟨ey.symm.trans (e.trans ex), hcomp⟩
  exact ⟨1, 1, hrigid hSame⟩

end

end Work.K3Inputs
