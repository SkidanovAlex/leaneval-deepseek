import Mathlib
import Submission.Work.Twist.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Twist

open CategoryTheory AlgebraicGeometry
open Work.Twist

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

/-!
## The transport of the twist datum along an isomorphism of the extensions

`PointlessOf C₅ L` is `QuinticTwist.Pointless (quinticTwistOf C₅ L)`, and
`QuinticTwist.Pointless D` is the non-vanishing of the class of the cocycle `σ ↦ P` in
`H¹(ℤ/5, E(L)) = ker N/(σ - 1)E(L)`.  The *element-level* form of that class being zero is
`∃ R ∈ E(L), σ R - R = P` (`pointless_iff_not_exists_shift`), and it is this form that is
transported along an isomorphism `e : L ≃ₐ[𝕜] L'` of the two models of the extension: the
`AddMonoidHom` `E(L) →+ E(L')` induced by `e` carries coboundaries to coboundaries, and the marked
point `P` to the marked point `P` (`Point.map_baseChange`).

The only subtlety is a formal one: `quinticTwistOf C₅ L` hides the field `L.L` behind a `def`, so
the type `(quinticTwistOf C₅ L).LPoints` is only *definitionally* equal to `E(L)`, and type class
resolution cannot see through it.  We therefore introduce the unfolded predicate
`HasCoboundary E P L`, prove that `PointlessOf C₅ L` is its negation
(`pointlessOf_iff_not_hasCoboundary`), and do all the transport on it, where every type is written
out in the open.
-/

/-- The marked point `P ∈ E(𝕜)` of a `FiveTorsionCurve`, with its type written as the `𝕜`-points
of the base change `E ⁄ 𝕜` of `E`.  The point itself is `C₅.P`; the point of the declaration is
that `C₅.P : E(𝕜)` is only *definitionally* an `(E ⁄ 𝕜)`-point, and the rewriting machinery
re-checks goals at a transparency level (`implicit`) at which that definitional equality is
invisible.  Naming the coercion makes it syntactically available. -/
def markedPoint {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜] (C₅ : FiveTorsionCurve 𝕜) :
    WeierstrassCurve.Affine.Point (C₅.E.baseChange 𝕜) :=
  C₅.P

/-- **The coboundary condition, in unfolded form.**  `HasCoboundary E P L` says that the marked
point `P ∈ E(𝕜)` is a coboundary for the Galois action of the chosen generator of `Gal(L/𝕜)`:
there is `R ∈ E(L)` with `σ R - R = P`.

This is the element-level form of `¬ QuinticTwist.Pointless` (`pointless_iff_not_exists_shift`),
written directly on the curve `E`, the point `P` and the extension `L`; it mentions no
`QuinticTwist`, so that an isomorphism of the extensions acts on it syntactically.

The instance `DecidableEq L.L` is an instance argument of the definition: `L.L` carries no
canonical `DecidableEq` (the group law on `Point` is defined by a case distinction on the
coordinates and needs one), but a caller who knows which instance the surrounding twist data uses
can supply it, and then the unfolded condition is *syntactically* the one of that twist data. -/
def HasCoboundary {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜] (E : WeierstrassCurve 𝕜)
    (P : WeierstrassCurve.Affine.Point (E.baseChange 𝕜)) (L : CyclicExtension 𝕜 5)
    [DecidableEq L.L] : Prop :=
  ∃ R : WeierstrassCurve.Affine.Point (E.baseChange L.L),
    WeierstrassCurve.Affine.Point.map (W' := E) (L.gen : L.L →ₐ[𝕜] L.L) R - R =
      WeierstrassCurve.Affine.Point.baseChange (W' := E) 𝕜 L.L P

/-- **`PointlessOf` is the negation of the unfolded coboundary condition.**  Both sides are the
element-level criterion of `pointless_iff_not_exists_shift`, read off for the twist data
`quinticTwistOf C₅ L`; the two propositions are definitionally equal.  The `change` is needed only
because `PointlessOf` is a `def` hidden from the rewrite `rw` (which matches at reducible
transparency). -/
theorem pointlessOf_iff_not_hasCoboundary {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]
    (C₅ : FiveTorsionCurve 𝕜) (L : CyclicExtension 𝕜 5) :
    PointlessOf C₅ L ↔ ¬ @HasCoboundary 𝕜 _ _ C₅.E (markedPoint C₅) L (Classical.decEq L.L) := by
  change (quinticTwistOf C₅ L).Pointless ↔
    ¬ @HasCoboundary 𝕜 _ _ C₅.E (markedPoint C₅) L (Classical.decEq L.L)
  rw [Work.PointlessIndexFive.pointless_iff_not_exists_shift]
  exact Iff.rfl

/-! ## The additive map `E(L) →+ E(L')` induced by an isomorphism of the extensions -/

/-- The `AddMonoidHom` `E(L) →+ E(L')` induced by a `𝕜`-algebra homomorphism `e : L → L'` of the
two fields over which the curve `E/𝕜` is base changed.  It is `Point.map e` with every implicit
argument (in particular the base field and the `DecidableEq` instances, which are needed because
the group law on `Point` is defined by a case distinction on the coordinates) exposed. -/
noncomputable def gMap {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜] (E : WeierstrassCurve 𝕜)
    (L L' : CyclicExtension 𝕜 5) [DecidableEq L.L] [DecidableEq L'.L] (e : L.L →ₐ[𝕜] L'.L) :
    WeierstrassCurve.Affine.Point (E.baseChange L.L) →+
      WeierstrassCurve.Affine.Point (E.baseChange L'.L) :=
  WeierstrassCurve.Affine.Point.map (W' := E) e

/-- **`gMap` commutes with the two Galois actions.**  An isomorphism `e : L ≃ₐ[𝕜] L'` carrying the
chosen generator of `Gal(L/𝕜)` to the chosen generator of `Gal(L'/𝕜)` intertwines `σ` acting on
`E(L)` and `σ'` acting on `E(L')`:

  `e (σ R) = σ' (e R)`.

This is `Point.map_map` together with `e ∘ σ = σ' ∘ e`, i.e. `AlgHom.ext hgen`. -/
theorem gMap_gen {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜] (E : WeierstrassCurve 𝕜)
    {L L' : CyclicExtension 𝕜 5} [DecidableEq L.L] [DecidableEq L'.L]
    (e : L.L →ₐ[𝕜] L'.L) (hgen : ∀ x : L.L, e (L.gen x) = L'.gen (e x))
    (R : WeierstrassCurve.Affine.Point (E.baseChange L.L)) :
    gMap E L L' e (WeierstrassCurve.Affine.Point.map (W' := E) (L.gen : L.L →ₐ[𝕜] L.L) R) =
      WeierstrassCurve.Affine.Point.map (W' := E) (L'.gen : L'.L →ₐ[𝕜] L'.L) (gMap E L L' e R) := by
  simp only [gMap]
  rw [WeierstrassCurve.Affine.Point.map_map, WeierstrassCurve.Affine.Point.map_map,
    show e.comp (L.gen : L.L →ₐ[𝕜] L.L) = (L'.gen : L'.L →ₐ[𝕜] L'.L).comp e
      from AlgHom.ext hgen]

/-- **`gMap` carries the marked point `P` to the marked point `P`**: `P` comes from `E(𝕜)`, where
both Galois actions are the identity.  This is `Point.map_baseChange`. -/
theorem gMap_baseChange {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜] (E : WeierstrassCurve 𝕜)
    {L L' : CyclicExtension 𝕜 5} [DecidableEq L.L] [DecidableEq L'.L] (e : L.L →ₐ[𝕜] L'.L)
    (P : WeierstrassCurve.Affine.Point (E.baseChange 𝕜)) :
    gMap E L L' e (WeierstrassCurve.Affine.Point.baseChange (W' := E) 𝕜 L.L P) =
      WeierstrassCurve.Affine.Point.baseChange (W' := E) 𝕜 L'.L P :=
  WeierstrassCurve.Affine.Point.map_baseChange (W' := E) e P

/-! ## The inverse of an `ExtIso` -/

/-- **The inverse of an `ExtIso` is an `ExtIso`**: `e.symm` also carries the chosen generator to
the chosen generator.  Indeed `e (L.gen (e.symm y)) = L'.gen y`, and applying `e.symm` gives
`L.gen (e.symm y) = e.symm (L'.gen y)`. -/
theorem extIso_symm_gen_eq {𝕜 : Type} [Field 𝕜] {L L' : CyclicExtension 𝕜 5} (e : ExtIso L L') :
    ∀ x : L'.L, e.toAlgEquiv.symm (L'.gen x) = L.gen (e.toAlgEquiv.symm x) := by
  intro x
  have h := e.gen_eq (e.toAlgEquiv.symm x)
  rw [AlgEquiv.apply_symm_apply] at h
  rw [← h, AlgEquiv.symm_apply_apply]

/-! ## The transport of the coboundary condition -/

/-- **The coboundary condition does not depend on the model of the extension.**  If `e : L ≃ₐ[𝕜] L'`
is an isomorphism of two models of the cyclic quintic extension carrying the chosen generator of
`Gal(L/𝕜)` to the chosen generator of `Gal(L'/𝕜)`, then `P` is a coboundary for the first action
if and only if it is a coboundary for the second.

`⇒` is `R ↦ e R` (`gMap_gen`, `gMap_baseChange`), `⇐` is the same argument for `e.symm`
(`extIso_symm_gen_eq`); additivity of `gMap` (`map_sub`) turns the coboundary `σ R - R` into
`σ' (e R) - e R`. -/
theorem hasCoboundary_iff_of_extIso {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]
    (C₅ : FiveTorsionCurve 𝕜) {L L' : CyclicExtension 𝕜 5} [DecidableEq L.L] [DecidableEq L'.L]
    (e : ExtIso L L') :
    HasCoboundary C₅.E (markedPoint C₅) L ↔ HasCoboundary C₅.E (markedPoint C₅) L' := by
  constructor
  · rintro ⟨R, hR⟩
    refine ⟨gMap C₅.E L L' (e.toAlgEquiv : L.L →ₐ[𝕜] L'.L) R, ?_⟩
    rw [← gMap_gen C₅.E (e.toAlgEquiv : L.L →ₐ[𝕜] L'.L) (fun x => e.gen_eq x) R,
      ← AddMonoidHom.map_sub, hR, gMap_baseChange]
  · rintro ⟨R, hR⟩
    refine ⟨gMap C₅.E L' L (e.toAlgEquiv.symm : L'.L →ₐ[𝕜] L.L) R, ?_⟩
    rw [← gMap_gen C₅.E (e.toAlgEquiv.symm : L'.L →ₐ[𝕜] L.L) (extIso_symm_gen_eq e) R,
      ← AddMonoidHom.map_sub, hR, gMap_baseChange]

/-- **The pointlessness of a quintic twist does not depend on the model of the cyclic extension.**
If `L` and `L'` are two models of the same cyclic quintic extension of `𝕜`, related by an
isomorphism carrying the chosen generator to the chosen generator (`ExtIso L L'`,
`Submission/Work/Twist/Defs.lean`), then the twist of a fixed `FiveTorsionCurve C₅` by `L` is
pointless if and only if the twist by `L'` is.

The isomorphism `e : L ≃ₐ[𝕜] L'` induces `Point.map e : E(L) →+ E(L')`, which commutes with the two
Galois actions (`Point.map_map` with `ExtIso.gen_eq`), hence carries `ker N` to `ker N`,
coboundaries to coboundaries, and the marked point `PL = baseChange P` to `PL`
(`WeierstrassCurve.Affine.Point.map_baseChange`).  So it induces an isomorphism of the two twist
groups `H¹(ℤ/5, E(L))` carrying the class of `σ ↦ P` to the class of `σ' ↦ P`, and `Pointless`
is that class being non-zero.

This is the well-posedness of the arithmetic residual with respect to the *choice of the
extension*; for the choice of generator inside a fixed extension see `pointless_pow_iff`. -/
theorem pointless_iff_of_extIso {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]
    (C₅ : FiveTorsionCurve 𝕜) {L L' : CyclicExtension 𝕜 5} (e : ExtIso L L') :
    PointlessOf C₅ L ↔ PointlessOf C₅ L' := by
  rw [pointlessOf_iff_not_hasCoboundary C₅ L, pointlessOf_iff_not_hasCoboundary C₅ L']
  exact not_congr
    (@hasCoboundary_iff_of_extIso 𝕜 _ _ C₅ L L' (Classical.decEq L.L) (Classical.decEq L'.L) e)

end

end Work.Twist
