import Submission.Work.CY3.Main
import Submission.Work.K3.BaseChangeVariety
import Submission.Work.K3.BaseChangeBirational

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.G2.Defs` — the `ℤ`-model vocabulary of the `G₂`-Grassmannian L-link

This is the base module of the **`G₂`-area** of `annals_motivic_invariants`: the *producer* layer
under the CY3 chapter (`Submission/Work/CY3`), i.e. the construction of the geometric datum
`Work.CY3.CY3Data 𝕜` (the `G₂`-Grassmannian L-link of Ito–Miura–Okawa–Ueda as extended by
Lin–Shinder to an arbitrary infinite field).

The source is H.-Y. Lin, E. Shinder, *Motivic invariants of birational maps*,
Annals of Math. **199** (1), 2024, § *`K`-trivial threefolds* (`thm:CY3` and its proof), together
with the appendix (`thm:BurtCY`, `cor-CYnSB`).

## The point of this module: uniformity in the field

The paper's construction is **uniform over `ℤ`**:

> Let `G` be the connected and simply connected split simple group scheme of type `G₂` over `ℤ`.
> Let `B ⊂ G` be the Borel subgroup, and `P, P' ⊊ G` the two maximal parabolic subgroups of `G`
> containing `B`.  The quotients `G/B`, `G/P`, `G/P'` are smooth and projective over `ℤ` by
> [Milne, Thm 13.33] and [SGA3, Cor. XXII.5.8.5]. …

Everything in the construction is a `Spec ℤ`-statement, hence available over **every** field `𝕜` by
base change along `Spec 𝕜 ⟶ Spec ℤ` — this is the paper's argument that `thm:CY3` holds over an
arbitrary infinite field (the only step needing `Infinite 𝕜` is Bertini).  This module builds that
base change:

* `specMapZ 𝕜 : Spec 𝕜 ⟶ Spec ℤ` and `baseChangeZ 𝕜 X := X ×_{Spec ℤ} Spec 𝕜`, together with the
  projection `baseChangeZProj` (re-using the general base change of `Work.K3.BaseChangeBirational`,
  which is stated for an arbitrary morphism of schemes);
* `baseChangeZMap` — the base change of a `Spec ℤ`-morphism, with `IsOver`-ness
  (`baseChangeZMap_isOver`) and stability of smoothness (`smooth_baseChangeZMap`) *proved*;
* `instVarietyZ` — the base change of a geometrically integral `Spec ℤ`-scheme whose
  structure morphism is separated / locally of finite type / quasicompact is a `𝕜`-variety,
  *proved*: this is what turns the `ℤ`-models of the later layers into `𝕜`-varieties;
* `CubicSelfIntersection` and `CubicInput` — the lineage of the `c₁`-discriminant
  `c₁(M|_Z)³ = 14 ≠ 42 = c₁(M'|_{Z'})³` of `lem-nSBG2`, and the *proof* that it distinguishes the
  two centres (`not_isoOver_of_cubic`), i.e. the `notIso` input of `Work.CY3.CY3Input`.

## Conventions

* `ℤ` is the base ring; `Spec (.of ℤ)` the base scheme of the `ℤ`-models.
* `baseChangeZ 𝕜 X` is only defined for `X` with an `Over (Spec ℤ)` structure; the base change is a
  `𝕜`-scheme by `baseChangeZOver`.
* The predicates `IsG2Grassmannian`, `HasCyLineBundle`, `IsGeneralSectionZeroLocus`,
  `IsBlowUpAlong`, `IsStronglyRational`, `IsKTrivial`, `PicardRankOne` are those of the CY3
  chapter (`Submission/Work/CY3`); nothing is redefined here.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
attribute [instance] MotivicInvariants.Variety.over MotivicInvariants.Variety.isIntegral

namespace Work.G2

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
  MotivicInvariants Order

noncomputable section

/-! ## 1. Base change along `Spec 𝕜 ⟶ Spec ℤ` -/

/-- The structure morphism `Spec 𝕜 ⟶ Spec ℤ` of the base change from the `ℤ`-models of the `G₂`
construction to a field `𝕜`. -/
noncomputable def specMapZ (𝕜 : Type) [Field 𝕜] : Spec (.of 𝕜) ⟶ Spec (.of ℤ) :=
  Spec.map (CommRingCat.ofHom (algebraMap ℤ 𝕜))

/-- **Base change of a `Spec ℤ`-scheme to `𝕜`**: the fibred product `X ×_{Spec ℤ} Spec 𝕜`.  This is
the operation that turns every `ℤ`-model of the `G₂`-Grassmannian construction (the group scheme
`G`, the Borel, the two parabolics, the quotients `G/B`, `G/P`, `G/P'`, the centres `Z`, `Z'`, the
zero locus `X` of the general section) into its `𝕜`-counterpart. -/
noncomputable abbrev baseChangeZ (𝕜 : Type) [Field 𝕜] (X : Scheme.{0})
    [X.Over (Spec (.of ℤ))] : Scheme.{0} :=
  Work.K3.baseChangeAlong (specMapZ 𝕜) X

/-- The structure morphism `X ×_{Spec ℤ} Spec 𝕜 ⟶ Spec 𝕜` of a base change, i.e. the first
projection of the fibred product.  This is the value of the `over` field of the `Variety` instance
`Work.G2.instVarietyZ` below; there is deliberately no separate instance, so that the `Over`-data
of a base change is always the one coming from its `Variety` structure. -/
noncomputable abbrev baseChangeZ_over (𝕜 : Type) [Field 𝕜] (X : Scheme.{0})
    [X.Over (Spec (.of ℤ))] : (baseChangeZ 𝕜 X).Over (Spec (.of 𝕜)) :=
  ⟨pullback.fst (specMapZ 𝕜) (X ↘ Spec (.of ℤ))⟩

/-- The projection `X ×_{Spec ℤ} Spec 𝕜 ⟶ X` of the base change. -/
noncomputable abbrev baseChangeZProj (𝕜 : Type) [Field 𝕜] (X : Scheme.{0})
    [X.Over (Spec (.of ℤ))] : baseChangeZ 𝕜 X ⟶ X :=
  Work.K3.baseChangeAlongProj (specMapZ 𝕜) X

/-- The base change `X ×_{Spec ℤ} Spec 𝕜` is also a `Spec ℤ`-scheme, through its projection to
`X`: this is what makes its projection a morphism over `Spec ℤ`.  (Unlike the case of `Spec 𝕜`,
this `Over`-structure is *not* determined by the `Variety` structure of the base change, since a
`Variety` is only defined over a field.) -/
noncomputable instance baseChangeZOverZ (𝕜 : Type) [Field 𝕜] (X : Scheme.{0})
    [X.Over (Spec (.of ℤ))] : (baseChangeZ 𝕜 X).Over (Spec (.of ℤ)) :=
  ⟨baseChangeZProj 𝕜 X ≫ (X ↘ Spec (.of ℤ))⟩

/-- The defining square of the base change `X ×_{Spec ℤ} Spec 𝕜` is cartesian. -/
theorem baseChangeZ_isPullback (𝕜 : Type) [Field 𝕜] (X : Scheme.{0})
    [X.Over (Spec (.of ℤ))] :
    IsPullback (pullback.fst (specMapZ 𝕜) (X ↘ Spec (.of ℤ)))
      (pullback.snd (specMapZ 𝕜) (X ↘ Spec (.of ℤ))) (specMapZ 𝕜) (X ↘ Spec (.of ℤ)) :=
  .of_hasPullback _ _

/-- **Base change of a `Spec ℤ`-morphism**: the induced morphism `X_𝕜 ⟶ Y_𝕜` between the base
changes.  This is how the `ℤ`-level projections `G/B → G/P`, `G/B → G/P'` and the morphisms
`Z ⟶ G/P`, `Z' ⟶ G/P'`, `X ⟶ G/B`, `X ⟶ G/P`, `X ⟶ G/P'` of the construction become their
`𝕜`-counterparts. -/
noncomputable def baseChangeZMap (𝕜 : Type) [Field 𝕜] {X Y : Scheme.{0}} [X.Over (Spec (.of ℤ))]
    [Y.Over (Spec (.of ℤ))] (f : X ⟶ Y) [f.IsOver (Spec (.of ℤ))] :
    baseChangeZ 𝕜 X ⟶ baseChangeZ 𝕜 Y :=
  pullback.map (specMapZ 𝕜) (X ↘ Spec (.of ℤ)) (specMapZ 𝕜) (Y ↘ Spec (.of ℤ))
    (𝟙 _) f (𝟙 _)
    (by rw [Category.comp_id, Category.id_comp])
    (by
      rw [Category.comp_id]
      exact ((Hom.isOver_iff (S := Spec (.of ℤ))).mp ‹f.IsOver (Spec (.of ℤ))›).symm)

/-- The first component of the base-changed morphism. -/
theorem baseChangeZMap_fst (𝕜 : Type) [Field 𝕜] {X Y : Scheme.{0}} [X.Over (Spec (.of ℤ))]
    [Y.Over (Spec (.of ℤ))] (f : X ⟶ Y) [f.IsOver (Spec (.of ℤ))] :
    baseChangeZMap 𝕜 f ≫ pullback.fst (specMapZ 𝕜) (Y ↘ Spec (.of ℤ)) =
      pullback.fst (specMapZ 𝕜) (X ↘ Spec (.of ℤ)) := by
  unfold baseChangeZMap pullback.map
  rw [pullback.lift_fst, Category.comp_id]

/-- The second component of the base-changed morphism. -/
theorem baseChangeZMap_snd (𝕜 : Type) [Field 𝕜] {X Y : Scheme.{0}} [X.Over (Spec (.of ℤ))]
    [Y.Over (Spec (.of ℤ))] (f : X ⟶ Y) [f.IsOver (Spec (.of ℤ))] :
    baseChangeZMap 𝕜 f ≫ pullback.snd (specMapZ 𝕜) (Y ↘ Spec (.of ℤ)) =
      pullback.snd (specMapZ 𝕜) (X ↘ Spec (.of ℤ)) ≫ f := by
  unfold baseChangeZMap pullback.map
  rw [pullback.lift_snd]

/-- The base change of a morphism over `Spec ℤ` is a morphism over `Spec 𝕜`.

The `Over`-data of the base changes are those of their `Variety` structures
(`Work.G2.instVarietyZ`), which is why the geometric-integrality and
separated/locally-of-finite-type/quasicompact data of `X` and `Y` appear as instance arguments. -/
theorem baseChangeZMap_isOver (𝕜 : Type) [Field 𝕜] {X Y : Scheme.{0}} [X.Over (Spec (.of ℤ))]
    [Y.Over (Spec (.of ℤ))] [GeometricallyIntegral (X ↘ Spec (.of ℤ))]
    [IsSeparated (X ↘ Spec (.of ℤ))] [LocallyOfFiniteType (X ↘ Spec (.of ℤ))]
    [QuasiCompact (X ↘ Spec (.of ℤ))] [GeometricallyIntegral (Y ↘ Spec (.of ℤ))]
    [IsSeparated (Y ↘ Spec (.of ℤ))] [LocallyOfFiniteType (Y ↘ Spec (.of ℤ))]
    [QuasiCompact (Y ↘ Spec (.of ℤ))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of ℤ))] :
    (baseChangeZMap 𝕜 f).IsOver (Spec (.of 𝕜)) := by
  refine ⟨?_⟩
  show baseChangeZMap 𝕜 f ≫ (baseChangeZ 𝕜 Y ↘ Spec (.of 𝕜)) = (baseChangeZ 𝕜 X ↘ Spec (.of 𝕜))
  rw [show (baseChangeZ 𝕜 Y ↘ Spec (.of 𝕜)) = pullback.fst (specMapZ 𝕜) (Y ↘ Spec (.of ℤ))
        from rfl,
    show (baseChangeZ 𝕜 X ↘ Spec (.of 𝕜)) = pullback.fst (specMapZ 𝕜) (X ↘ Spec (.of ℤ))
        from rfl]
  exact baseChangeZMap_fst 𝕜 f

/-- **The base-change square of a morphism is cartesian**: this exhibits `baseChangeZMap 𝕜 f` as
the base change of `f` along the projection of `Y_𝕜`. -/
theorem baseChangeZMap_isPullback (𝕜 : Type) [Field 𝕜] {X Y : Scheme.{0}} [X.Over (Spec (.of ℤ))]
    [Y.Over (Spec (.of ℤ))] (f : X ⟶ Y) [f.IsOver (Spec (.of ℤ))] :
    IsPullback (baseChangeZMap 𝕜 f) (baseChangeZProj 𝕜 X) (baseChangeZProj 𝕜 Y) f := by
  have hf : f ≫ (Y ↘ Spec (.of ℤ)) = (X ↘ Spec (.of ℤ)) :=
    (Hom.isOver_iff (S := Spec (.of ℤ))).mp inferInstance
  refine IsPullback.of_right
    (X₁₁ := baseChangeZ 𝕜 X) (X₁₂ := baseChangeZ 𝕜 Y) (X₁₃ := Spec (.of 𝕜))
    (X₂₁ := X) (X₂₂ := Y) (X₂₃ := Spec (.of ℤ))
    (h₁₁ := baseChangeZMap 𝕜 f) (h₁₂ := pullback.fst (specMapZ 𝕜) (Y ↘ Spec (.of ℤ)))
    (h₂₁ := f) (h₂₂ := (Y ↘ Spec (.of ℤ)))
    (v₁₁ := pullback.snd (specMapZ 𝕜) (X ↘ Spec (.of ℤ)))
    (v₁₂ := pullback.snd (specMapZ 𝕜) (Y ↘ Spec (.of ℤ))) (v₁₃ := specMapZ 𝕜) ?_ ?_
    (baseChangeZ_isPullback 𝕜 Y)
  · rw [baseChangeZMap_fst, hf]; exact baseChangeZ_isPullback 𝕜 X
  · exact baseChangeZMap_snd 𝕜 f

/-- **Base change preserves smoothness.**  If a `Spec ℤ`-morphism is smooth, so is its base change
to every field: smoothness is stable under base change.  This is the *proved* half of "the
projections `p : G/B → G/P`, `p' : G/B → G/P'` are smooth" of the paper — the `ℤ`-level input is
`smooth_p`, its `𝕜`-counterpart is derived here. -/
theorem smooth_baseChangeZMap (𝕜 : Type) [Field 𝕜] {X Y : Scheme.{0}} [X.Over (Spec (.of ℤ))]
    [Y.Over (Spec (.of ℤ))] (f : X ⟶ Y) [f.IsOver (Spec (.of ℤ))] [Smooth f] :
    Smooth (baseChangeZMap 𝕜 f) :=
  MorphismProperty.of_isPullback (baseChangeZMap_isPullback 𝕜 f).flip ‹Smooth f›

/-! ## 2. The base change is a variety

A `Spec ℤ`-scheme whose structure morphism is geometrically integral, separated, locally of finite
type and quasicompact — exactly what the paper's `G₂`-quotients are (`Milne` Thm 13.33, `SGA3`
Cor. XXII.5.8.5) — has a `𝕜`-variety as its base change to any field `𝕜`: integrality is
`pullback_of_geometrically'`, and the remaining three components are base-change stability of
`IsSeparated`, `LocallyOfFiniteType` and `QuasiCompact`.  *Proved*, not assumed. -/

/-- **The base change of a `ℤ`-scheme to `𝕜` is a `𝕜`-variety.** -/
noncomputable instance instVarietyZ (𝕜 : Type) [Field 𝕜] (X : Scheme.{0}) [X.Over (Spec (.of ℤ))]
    [GeometricallyIntegral (X ↘ Spec (.of ℤ))] [IsSeparated (X ↘ Spec (.of ℤ))]
    [LocallyOfFiniteType (X ↘ Spec (.of ℤ))] [QuasiCompact (X ↘ Spec (.of ℤ))] :
    Variety 𝕜 (baseChangeZ 𝕜 X) where
  «over» := baseChangeZ_over 𝕜 X
  isIntegral :=
    pullback_of_geometrically' (GeometricallyIntegral.geometrically_isIntegral
      (f := X ↘ Spec (.of ℤ))) 𝕜 (specMapZ 𝕜)
  isSeparated := by
    show IsSeparated (pullback.fst (specMapZ 𝕜) (X ↘ Spec (.of ℤ)))
    infer_instance
  locallyOfFiniteType := by
    show LocallyOfFiniteType (pullback.fst (specMapZ 𝕜) (X ↘ Spec (.of ℤ)))
    infer_instance
  quasicompact := by
    show QuasiCompact (pullback.fst (specMapZ 𝕜) (X ↘ Spec (.of ℤ)))
    infer_instance

/-! ## 3. The `c₁`-discriminant `c₁(M|_Z)³ = 14 ≠ 42 = c₁(M'|_{Z'})³`

Paper `lem-nSBG2`: the two centres `Z_𝕜`, `Z'_𝕜` of the CY3 link are `K`-trivial threefolds of
Picard rank one, and they are *not* isomorphic because the cubic self-intersection of the ample
generator of their (rank one) Néron–Severi group takes the two distinct values computed by
Ito–Miura–Okawa–Ueda:

```
c₁(M_𝕜|_Z)³  = c₁(M_ℤ)³ · Z_ℤ = 14 ,      c₁(M'_𝕜|_{Z'})³ = c₁(M'_ℤ)³ · Z'_ℤ = 42
```

(the middle equalities are the base-change uniformity of the intersection numbers, and the numbers
are those of `IMOUG2`).  Mathlib has no Picard group, no Chern classes and no intersection theory,
so we record the *value* of this intersection number as the named predicate
`CubicSelfIntersection`, and its two properties that make it an invariant — well-definedness and
invariance under `𝕜`-isomorphisms — as the named input `CubicInput`.  Theorems of this module then
turn them into the `notIso` field of `Work.CY3.CY3Input`, through the arithmetic `14 ≠ 42`. -/

/-- **Named geometric predicate: the cubic self-intersection of the ample generator.**

`CubicSelfIntersection 𝕜 X n` says that `X` is a smooth projective `𝕜`-variety of Picard rank one
(its Néron–Severi group has rank one), with ample generator `M`, and that
`c₁(M)³ = n ∈ ℤ`, where the cube is the degree of the intersection product, computed with respect
to the (integral) Néron–Severi group.  For the two centres of the CY3 link this is the paper's
`c₁(M_𝕜|_Z)³ = 14` (resp. `42` for `Z'` and `M'`).

Mathlib has no Néron–Severi group, no Chern classes and no intersection numbers, so this is a named
hypothesis.  Its two structural properties (`CubicInput`) are exactly what `lem-nSBG2` uses. -/
class CubicSelfIntersection (𝕜 : Type) [Field 𝕜] (X : Scheme.{0}) [Variety 𝕜 X] (n : ℤ) : Prop

/-- **Named input (`IMOUG2` + `lem-nSBG2`): the cubic self-intersection, as a function of the
variety, is an isomorphism invariant.**

`CubicInput 𝕜` supplies the invariant that `lem-nSBG2` uses to distinguish the two centres of the
CY3 link: the *function* `X ↦ c₁(M|_X)³` (the cubic self-intersection of the ample generator of the
rank-one Néron–Severi group of `X`), together with its **invariance under isomorphism over `𝕜`**
(an isomorphism `X ≅ Y` over `𝕜` carries the ample generator of `X` to that of `Y`, hence preserves
`c₁(M|_X)³`).  Both are standard facts of intersection theory (the pullback of a cycle class along
an isomorphism is an inverse isomorphism of the intersection rings; and `NS(X) ≅ NS(Y)` in a way
that preserves the intersection product), not available in Mathlib.

The two *values* `c₁(M|_Z)³ = 14` and `c₁(M'|_{Z'})³ = 42` computed by Ito–Miura–Okawa–Ueda are
*not* part of this structure but are hypotheses about it at the two centres of a model
(`Work.G2.CY3DatumZ.cubic_Z`, `cubic_Z'`), because they are computations in the intersection theory
of the individual varieties.

**Why the function and not a predicate.**  An earlier version of this interface introduced the
*fieldless* class `CubicSelfIntersection 𝕜 X n` (still present above, kept only for the record) and
asserted the well-definedness of the value as a predicate: `∀ X n m, CubicSelfIntersection 𝕜 X n →
CubicSelfIntersection 𝕜 X m → n = m`.  Since a class with no fields is inhabited at *every* `n`,
that clause reduced to `n = m` for arbitrary `n m : ℤ`, hence to `0 = 1`: the old `CubicInput` was
*refutable* (`Work.Wire123.not_cubicInput_legacy`), and every reduction taking it as a hypothesis
was uninstantiable, whatever geometry was built.  An input that asserts the well-definedness of a
function must *supply the function*; that is what `cubic` and `cubic_iso` below do. -/
structure CubicInput (𝕜 : Type) [Field 𝕜] where
  /-- the cubic self-intersection `c₁(M|_X)³` of the ample generator of the rank-one Néron–Severi
  group of `X`, as a function of the variety -/
  cubic : (X : Scheme.{0}) → [Variety 𝕜 X] → ℤ
  /-- `c₁(M)³` is invariant under isomorphisms over `𝕜` -/
  cubic_iso : ∀ {X Y : Scheme.{0}} [Variety 𝕜 X] [Variety 𝕜 Y],
    Work.CY3.IsoOver 𝕜 X Y → cubic X = cubic Y

variable {𝕜 : Type} [Field 𝕜]

/-- **`14 ≠ 42`**: the two values of the cubic self-intersection computed by Ito–Miura–Okawa–Ueda
for the two centres of the CY3 link.  This is the arithmetic heart of `lem-nSBG2`; in the paper's
`proof` it is the sentence "As `c₁(M_𝕜|_Z)³ = c₁(M_ℤ)³·Z_ℤ` and `c₁(M'_𝕜|_{Z'})³ = c₁(M'_ℤ)³·Z'_{ℤ}`
are distinct and equal to `14` or `42` by `IMOUG2`, necessarily `Z_𝕜` is not isomorphic to
`Z'_𝕜`." -/
theorem fourteen_ne_fortyTwo : (14 : ℤ) ≠ 42 := by norm_num

/-- **The `notIso` input of `lem-nSBG2`.**  Two varieties at which the cubic self-intersection takes
the values `14` and `42` are not isomorphic over `𝕜`: an isomorphism would transport the invariant
(`cubic_iso`) and force `14 = 42`. -/
theorem not_isoOver_of_cubic (C : CubicInput 𝕜) {X Y : Scheme.{0}} [Variety 𝕜 X] [Variety 𝕜 Y]
    (hX : C.cubic X = 14) (hY : C.cubic Y = 42) :
    ¬ Work.CY3.IsoOver 𝕜 X Y := fun h =>
  fourteen_ne_fortyTwo (hX.symm.trans ((C.cubic_iso h).trans hY))

/-- The same statement with the two values exchanged: the order in which the two centres are
compared does not matter (`Work.CY3.IsoOver` is symmetric). -/
theorem not_isoOver_of_cubic' (C : CubicInput 𝕜) {X Y : Scheme.{0}} [Variety 𝕜 X] [Variety 𝕜 Y]
    (hX : C.cubic X = 42) (hY : C.cubic Y = 14) :
    ¬ Work.CY3.IsoOver 𝕜 X Y := fun h =>
  not_isoOver_of_cubic C hY hX (Work.CY3.IsoOver.symm h)

/-- The cubic self-intersection is an isomorphism invariant (the `cubic_iso` field, renamed). -/
theorem cubic_iff_of_isoOver (C : CubicInput 𝕜) {X Y : Scheme.{0}} [Variety 𝕜 X]
    [Variety 𝕜 Y] (h : Work.CY3.IsoOver 𝕜 X Y) : C.cubic X = C.cubic Y :=
  C.cubic_iso h

end

end Work.G2
