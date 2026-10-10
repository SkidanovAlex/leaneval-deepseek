/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.Twist
-/
import Mathlib
import Submission.Work.Twist.Defs
import Submission.Work.Twist.Assembly
import Submission.Work.Twist.nsmul_cls_eq_zero_iff

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Transporting the twist along an isomorphism of the cyclic extension

An isomorphism `e : ExtIso L L'` of two models of the cyclic quintic extension of `𝕜` carries the
chosen generator `σ` of `Gal(L/𝕜)` to the chosen generator `σ'` of `Gal(L'/𝕜)`.  It therefore
induces an additive map `algMap E L L' e : E(L) →+ E(L')` on the points of a curve `E/𝕜`
base-changed to the two fields, which carries `𝕜`-rational points to `𝕜`-rational points
(`algMap_baseChange`) and intertwines the two Galois actions (`algMap_gen`).  Consequently it
carries the coboundary condition `∃ R, σ R - R = n • Q` for a `𝕜`-rational point `Q` to the same
condition for `σ'` (`hasCoboundaryMul_iff_of_extIso`), and by `ExtIso.symm` the equivalence is
two-sided.

Everything here is written with its types and its `DecidableEq` instances *exposed*: the predicate
`HasCoboundaryMul` speaks about `WeierstrassCurve.Affine.Point (E.baseChange L.L)` and takes the
`DecidableEq L.L` instance as an ordinary (instance-implicit) argument.  This is essential, because
`(quinticTwistOf C₅ L).LPoints` is only *definitionally* the type `(C₅.E.baseChange L.L).Point`
and the rewriting machinery re-checks goals at a transparency level at which the `def`
`quinticTwistOf` is invisible.  The transfer between the two presentations is therefore done once,
by definitional equality (`Iff.rfl` and `exact`), and never by `rw`.

## The two bridges to the twist

`QuinticTwist.cls D` is the class of the cocycle `σ ↦ P` in `H¹(ℤ/5, E(L)) = ker N/(σ - 1)E(L)`,
realised as `ker N / (σ - 1)E(L)` (`Submission/Work/TorsorExistence/Twist.lean`).  Its
element-level criterion is `Work.Twist.quot_mk_eq_zero_iff`, and for the two classes of interest
(`HasPoint` and `DivisorOfDegree n` of `TwistCurveModel`) it reads

* `D.cls = 0 ↔ ∃ R, D.shift R = D.PL` (`Work.TorsorExistence.cls_eq_zero_iff`);
* `n • D.cls = 0 ↔ ∃ R, D.shift R = n • D.PL` (`Work.Twist.nsmul_cls_eq_zero_iff`).

Both right-hand sides are *definitionally* the unfolded coboundary condition `HasCoboundaryMul`,
which is what allows the class of the twist to be transported along the isomorphism of the
extensions by `rw`-free reasoning.  The results are `hasPoint_iff_of_extIso` and
`divisorOfDegree_iff_of_extIso`.

All definitions and lemmas of this file live in the namespace `Work.Twist.ExtIsoTransport`, except
`ExtIso.symm`, so as not to collide with the sibling file `pointless_iff_of_extIso.lean`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open CategoryTheory AlgebraicGeometry
open Work.Twist

namespace Work.Twist

noncomputable section

/-- **The inverse of an isomorphism of cyclic extensions.**  If `e` carries the chosen generator
`σ` of `Gal(L/𝕜)` to the chosen generator `σ'` of `Gal(L'/𝕜)`, then `e⁻¹` carries `σ'` back to
`σ`: applying `e⁻¹` to both sides of `e (σ x) = σ' (e x)` gives `σ (e⁻¹ y) = e⁻¹ (σ' y)`. -/
def ExtIso.symm {𝕜 : Type} [Field 𝕜] {L L' : CyclicExtension 𝕜 5} (e : ExtIso L L') :
    ExtIso L' L where
  toAlgEquiv := e.toAlgEquiv.symm
  gen_eq := fun x => by
    have h : e.toAlgEquiv (L.gen (e.toAlgEquiv.symm x)) = L'.gen x := by
      simpa using e.gen_eq (e.toAlgEquiv.symm x)
    have h2 := congrArg e.toAlgEquiv.symm h
    simpa using h2.symm

end

end Work.Twist

namespace Work.Twist.ExtIsoTransport

noncomputable section

variable {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]

/-- The marked point `P` of a `FiveTorsionCurve`, with its type written as a `𝕜`-point of the base
change `E ⁄ 𝕜`.  Naming the coercion `C₅.P : E(𝕜)` makes it syntactically available to the
rewriting machinery. -/
def markedPoint (C₅ : FiveTorsionCurve 𝕜) : WeierstrassCurve.Affine.Point (C₅.E.baseChange 𝕜) :=
  C₅.P

/-- **The coboundary condition, in unfolded form.**  For a `𝕜`-rational point `Q` of `E`, this
says that `n • Q` is a coboundary for the action of the chosen generator of `Gal(L/𝕜)`:
`∃ R ∈ E(L), σ R - R = n • Q`.  For `n = 1` this is the element-level form of `cls = 0` in
`H¹(ℤ/5, E(L)) = ker N/(σ - 1)E(L)`; for general `n` it is the form that the divisor condition
`n • cls = 0` takes (`Work.Twist.nsmul_cls_eq_zero_iff`). -/
def HasCoboundaryMul (E : WeierstrassCurve 𝕜)
    (Q : WeierstrassCurve.Affine.Point (E.baseChange 𝕜)) (L : CyclicExtension 𝕜 5)
    [DecidableEq L.L] (n : ℕ) : Prop :=
  ∃ R : WeierstrassCurve.Affine.Point (E.baseChange L.L),
    WeierstrassCurve.Affine.Point.map (W' := E) (L.gen : L.L →ₐ[𝕜] L.L) R - R =
      (n : ℕ) • WeierstrassCurve.Affine.Point.baseChange (W' := E) 𝕜 L.L Q

/-- The additive map `E(L) →+ E(L')` induced by a `𝕜`-algebra homomorphism of the two top
fields: `WeierstrassCurve.Affine.Point.map` with its implicit arguments exposed. -/
def algMap (E : WeierstrassCurve 𝕜) (L L' : CyclicExtension 𝕜 5)
    [DecidableEq L.L] [DecidableEq L'.L] (e : L.L →ₐ[𝕜] L'.L) :
    WeierstrassCurve.Affine.Point (E.baseChange L.L) →+
      WeierstrassCurve.Affine.Point (E.baseChange L'.L) :=
  WeierstrassCurve.Affine.Point.map (W' := E) e

/-- **`algMap` intertwines the two Galois actions.**  If `e` carries the chosen generator of
`Gal(L/𝕜)` to the chosen generator of `Gal(L'/𝕜)`, then `e (σ R) = σ' (e R)`; this is
`WeierstrassCurve.Affine.Point.map_map` together with `AlgHom.ext hgen`. -/
theorem algMap_gen (E : WeierstrassCurve 𝕜) {L L' : CyclicExtension 𝕜 5}
    [DecidableEq L.L] [DecidableEq L'.L] (e : L.L →ₐ[𝕜] L'.L)
    (hgen : ∀ x : L.L, e (L.gen x) = L'.gen (e x))
    (R : WeierstrassCurve.Affine.Point (E.baseChange L.L)) :
    algMap E L L' e (WeierstrassCurve.Affine.Point.map (W' := E) (L.gen : L.L →ₐ[𝕜] L.L) R) =
      WeierstrassCurve.Affine.Point.map (W' := E) (L'.gen : L'.L →ₐ[𝕜] L'.L)
        (algMap E L L' e R) := by
  simp only [algMap]
  rw [WeierstrassCurve.Affine.Point.map_map, WeierstrassCurve.Affine.Point.map_map,
    show e.comp (L.gen : L.L →ₐ[𝕜] L.L) = (L'.gen : L'.L →ₐ[𝕜] L'.L).comp e
      from AlgHom.ext hgen]

/-- **`algMap` carries `𝕜`-rational points to `𝕜`-rational points**: such a point is fixed by
both Galois actions.  This is `WeierstrassCurve.Affine.Point.map_baseChange`. -/
theorem algMap_baseChange (E : WeierstrassCurve 𝕜) {L L' : CyclicExtension 𝕜 5}
    [DecidableEq L.L] [DecidableEq L'.L] (e : L.L →ₐ[𝕜] L'.L)
    (Q : WeierstrassCurve.Affine.Point (E.baseChange 𝕜)) :
    algMap E L L' e (WeierstrassCurve.Affine.Point.baseChange (W' := E) 𝕜 L.L Q) =
      WeierstrassCurve.Affine.Point.baseChange (W' := E) 𝕜 L'.L Q :=
  WeierstrassCurve.Affine.Point.map_baseChange (W' := E) e Q

/-- **The inverse map intertwines the Galois actions too.**  This is `ExtIso.gen_eq` for `e⁻¹`,
obtained by applying `e⁻¹` to `e (σ x) = σ' (e x)`; it is what makes the transport of the
coboundary condition two-sided. -/
theorem extIso_symm_gen_eq {L L' : CyclicExtension 𝕜 5} (e : ExtIso L L') :
    ∀ x : L'.L, e.toAlgEquiv.symm (L'.gen x) = L.gen (e.toAlgEquiv.symm x) := by
  intro x
  have h := e.gen_eq (e.toAlgEquiv.symm x)
  rw [AlgEquiv.apply_symm_apply] at h
  rw [← h, AlgEquiv.symm_apply_apply]

/-- **The coboundary condition is independent of the model of the extension.**  For a
`𝕜`-rational point `Q` of `E` and `n : ℕ`, `n • Q` is a `(σ - 1)`-coboundary on `E(L)` if and
only if it is a `(σ' - 1)`-coboundary on `E(L')`.

`⇒` is `R ↦ algMap e R` (`algMap_gen`, `map_nsmul`, `algMap_baseChange`); `⇐` is the same
argument for `e⁻¹` (`extIso_symm_gen_eq`). -/
theorem hasCoboundaryMul_iff_of_extIso (E : WeierstrassCurve 𝕜)
    (Q : WeierstrassCurve.Affine.Point (E.baseChange 𝕜)) {L L' : CyclicExtension 𝕜 5}
    [DecidableEq L.L] [DecidableEq L'.L] (e : ExtIso L L') (n : ℕ) :
    HasCoboundaryMul E Q L n ↔ HasCoboundaryMul E Q L' n := by
  constructor
  · rintro ⟨R, hR⟩
    refine ⟨algMap E L L' (e.toAlgEquiv : L.L →ₐ[𝕜] L'.L) R, ?_⟩
    rw [← algMap_gen E (e.toAlgEquiv : L.L →ₐ[𝕜] L'.L) (fun x => e.gen_eq x) R,
      ← AddMonoidHom.map_sub, hR, map_nsmul, algMap_baseChange]
  · rintro ⟨R, hR⟩
    refine ⟨algMap E L' L (e.toAlgEquiv.symm : L'.L →ₐ[𝕜] L.L) R, ?_⟩
    rw [← algMap_gen E (e.toAlgEquiv.symm : L'.L →ₐ[𝕜] L.L) (extIso_symm_gen_eq e) R,
      ← AddMonoidHom.map_sub, hR, map_nsmul, algMap_baseChange]

/-! ## The two bridges to the twist -/

/-- **The `HasPoint` bridge.**  The class of the twist vanishes iff the marked point is a
coboundary; this is `Work.TorsorExistence.cls_eq_zero_iff`, read off in the unfolded
presentation. -/
theorem cls_eq_zero_iff_hasCoboundaryMul (C₅ : FiveTorsionCurve 𝕜) (L : CyclicExtension 𝕜 5) :
    (quinticTwistOf C₅ L).cls = 0 ↔
      @HasCoboundaryMul 𝕜 _ _ C₅.E (markedPoint C₅) L (Classical.decEq L.L) 1 := by
  rw [Work.TorsorExistence.cls_eq_zero_iff]
  exact Iff.rfl

/-- **The divisor-degree bridge.**  `n • cls = 0` iff `n • P` is a coboundary; this is
`Work.Twist.nsmul_cls_eq_zero_iff`, read off in the unfolded presentation. -/
theorem nsmul_cls_eq_zero_iff_hasCoboundaryMul (C₅ : FiveTorsionCurve 𝕜)
    (L : CyclicExtension 𝕜 5) (n : ℕ) :
    (n : ℕ) • (quinticTwistOf C₅ L).cls = 0 ↔
      @HasCoboundaryMul 𝕜 _ _ C₅.E (markedPoint C₅) L (Classical.decEq L.L) n := by
  rw [Work.Twist.nsmul_cls_eq_zero_iff]
  exact Iff.rfl

/-- **The rational-point condition of the twist does not depend on the model of the extension.**
`D.toTorsor.HasPoint` is `cls = 0` in `H¹(ℤ/5, E(L))`, and the coboundary condition
`∃ R, σ R - R = P` is transported along `ExtIso` by `hasCoboundaryMul_iff_of_extIso`. -/
theorem hasPoint_iff_of_extIso {C₅ : FiveTorsionCurve 𝕜} {L L' : CyclicExtension 𝕜 5}
    (e : ExtIso L L') :
    (quinticTwistOf C₅ L).toTorsor.HasPoint ↔ (quinticTwistOf C₅ L').toTorsor.HasPoint := by
  have h₁ : (quinticTwistOf C₅ L).toTorsor.HasPoint ↔
      @HasCoboundaryMul 𝕜 _ _ C₅.E (markedPoint C₅) L (Classical.decEq L.L) 1 :=
    ofAdd_eq_one.trans (cls_eq_zero_iff_hasCoboundaryMul C₅ L)
  have h₂ : (quinticTwistOf C₅ L').toTorsor.HasPoint ↔
      @HasCoboundaryMul 𝕜 _ _ C₅.E (markedPoint C₅) L' (Classical.decEq L'.L) 1 :=
    ofAdd_eq_one.trans (cls_eq_zero_iff_hasCoboundaryMul C₅ L')
  rw [h₁, h₂]
  exact @hasCoboundaryMul_iff_of_extIso 𝕜 _ _ C₅.E (markedPoint C₅) L L'
    (Classical.decEq L.L) (Classical.decEq L'.L) e 1

/-- **The divisor-degree condition of the twist does not depend on the model of the extension.**
`D.toTorsor.DivisorOfDegree n` is `n • cls = 0`, and the coboundary condition
`∃ R, σ R - R = n • P` is transported along `ExtIso` by `hasCoboundaryMul_iff_of_extIso`. -/
theorem divisorOfDegree_iff_of_extIso {C₅ : FiveTorsionCurve 𝕜} {L L' : CyclicExtension 𝕜 5}
    (e : ExtIso L L') (n : ℕ) :
    (quinticTwistOf C₅ L).toTorsor.DivisorOfDegree n ↔
      (quinticTwistOf C₅ L').toTorsor.DivisorOfDegree n := by
  have h₁ : (quinticTwistOf C₅ L).toTorsor.DivisorOfDegree n ↔
      @HasCoboundaryMul 𝕜 _ _ C₅.E (markedPoint C₅) L (Classical.decEq L.L) n :=
    (Work.PointlessIndexFive.toTorsor_divisorOfDegree_iff _ n).trans
      (nsmul_cls_eq_zero_iff_hasCoboundaryMul C₅ L n)
  have h₂ : (quinticTwistOf C₅ L').toTorsor.DivisorOfDegree n ↔
      @HasCoboundaryMul 𝕜 _ _ C₅.E (markedPoint C₅) L' (Classical.decEq L'.L) n :=
    (Work.PointlessIndexFive.toTorsor_divisorOfDegree_iff _ n).trans
      (nsmul_cls_eq_zero_iff_hasCoboundaryMul C₅ L' n)
  rw [h₁, h₂]
  exact @hasCoboundaryMul_iff_of_extIso 𝕜 _ _ C₅.E (markedPoint C₅) L L'
    (Classical.decEq L.L) (Classical.decEq L'.L) e n

end

end Work.Twist.ExtIsoTransport
