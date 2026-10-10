import Mathlib
import Submission.Work.K3.BaseChange

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.K3.BaseChangeBirational` — base change of partial maps (start of the birational base
change)

The descent step of `thm:K3` (see `Work.K3.Descent`) needs the L-link over `𝕜 ⊆ ℂ` to be the base
change of the `ℚ`-model of the link.  `Submission/Work/K3/BaseChange.lean` base changes *schemes*
and *morphisms* (`baseChange`, `baseChangeMap`, …); this file starts the base change of the
birational geometry itself:

* `Work.K3.baseChangeAlong f X` — the base change `X ×_S T` of an `S`-scheme `X` along an arbitrary
  morphism `f : T ⟶ S`, with its `T`-structure and projection (the specialisation to a field
  extension is `Work.K3.baseChange`);
* `Work.K3.Dense.preimage_of_isOpenMap` — the preimage of a dense open under a surjective open map
  is dense; this is the topological input making the base change of *partial* maps well defined;
* `Work.K3.PartialMap.baseChangeAlong` — the base change of a partial map `X.PartialMap Y` along
  `f` (a partial map `(X ×_S T).PartialMap (Y ×_S T)`), built from Mathlib's restriction API
  (`AlgebraicGeometry.Scheme.morphismRestrict` and `isPullback_morphismRestrict` from
  `Mathlib/AlgebraicGeometry/Restrict.lean`).

The base change of `PartialIso`, `RationalMap` and `BirationalMap` — and with it the
scheme-theoretic part of the descent — is stated in the companion files
`Submission/Work/K3/partialIso_baseChangeAlong.lean`,
`Submission/Work/K3/rationalMap_baseChangeAlong.lean` and
`Submission/Work/K3/birationalMap_baseChangeAlong.lean`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Work.K3

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Order

/-! ## 1. The topology of dense preimages -/

/-- **The preimage of a dense open under a surjective open map is dense.**  Continuity alone gives
`closure (p ⁻¹' U) ⊆ p ⁻¹' closure U`; the converse needs openness of `p` (`IsOpenMap` commutes
closures with preimages) and surjectivity of `p`. -/
theorem Dense.preimage_of_isOpenMap {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {p : X → Y} (hop : IsOpenMap p) (hcont : Continuous p) {U : Set Y}
    (hU : Dense U) : Dense (p ⁻¹' U) := by
  rw [dense_iff_closure_eq] at hU ⊢
  rw [← hop.preimage_closure_eq_closure_preimage hcont U, hU, Set.preimage_univ]

/-! ## 2. Base change of schemes along an arbitrary morphism -/

section Along

variable {S T : Scheme.{0}} (f : T ⟶ S)

/-- **Base change of an `S`-scheme along `f : T ⟶ S`**: the fibred product `X ×_S T`. -/
noncomputable abbrev baseChangeAlong (X : Scheme.{0}) [X.Over S] : Scheme.{0} :=
  pullback f (X ↘ S)

/-- The base change of an `S`-scheme along `f` is a `T`-scheme. -/
noncomputable abbrev baseChangeAlongOver (X : Scheme.{0}) [X.Over S] :
    (baseChangeAlong f X).Over T :=
  ⟨pullback.fst f (X ↘ S)⟩

attribute [instance] baseChangeAlongOver

/-- The projection `X ×_S T ⟶ X` of a base change. -/
noncomputable abbrev baseChangeAlongProj (X : Scheme.{0}) [X.Over S] :
    baseChangeAlong f X ⟶ X :=
  pullback.snd f (X ↘ S)

/-- The projection of a base change is surjective when `f` is. -/
instance baseChangeAlongProj_surjective (X : Scheme.{0}) [X.Over S] [Surjective f] :
    Surjective (baseChangeAlongProj f X) :=
  show Surjective (pullback.snd f (X ↘ S)) from inferInstance

/-- The projection of a base change is universally open when `f` is. -/
instance baseChangeAlongProj_universallyOpen (X : Scheme.{0}) [X.Over S] [UniversallyOpen f] :
    UniversallyOpen (baseChangeAlongProj f X) :=
  show UniversallyOpen (pullback.snd f (X ↘ S)) from UniversallyOpen.snd f (X ↘ S)

/-- The projection of a base change is open when `f` is universally open. -/
theorem baseChangeAlongProj_isOpenMap (X : Scheme.{0}) [X.Over S] [UniversallyOpen f] :
    IsOpenMap (baseChangeAlongProj f X) :=
  Scheme.Hom.isOpenMap _

/-- **The preimage of a dense open under the projection of a base change is dense**, whenever `f`
is surjective and universally open (e.g. `f = Work.K3.specMap K L` for a field extension). -/
theorem Dense.preimage_baseChangeAlongProj (X : Scheme.{0}) [X.Over S] [Surjective f]
    [UniversallyOpen f] {U : X.Opens} (hU : Dense (U : Set X)) :
    Dense (((baseChangeAlongProj f X) ⁻¹ᵁ U) : Set (baseChangeAlong f X)) :=
  Dense.preimage_of_isOpenMap (baseChangeAlongProj_isOpenMap f X)
    ((baseChangeAlongProj f X).continuous) hU

/-! ## 3. Base change of a partial map -/

variable {X Y : Scheme.{0}} [X.Over S] [Y.Over S]

/-- **Base change of a partial map** `g : X.PartialMap Y` along `f : T ⟶ S`: the partial map
`X ×_S T ⟶ Y ×_S T` whose domain is the preimage of the domain of `g`.  It is well defined
because the preimage of a dense open is dense (`Dense.preimage_baseChangeAlongProj`); the
underlying morphism is `pullback.lift` of `g` and of the projection to `T`. -/
noncomputable def PartialMap.baseChangeAlong (g : X.PartialMap Y) [g.IsOver S]
    [Surjective f] [UniversallyOpen f] :
    (baseChangeAlong f X).PartialMap (baseChangeAlong f Y) where
  domain := (baseChangeAlongProj f X) ⁻¹ᵁ g.domain
  dense_domain := Dense.preimage_baseChangeAlongProj f X g.dense_domain
  hom := pullback.lift (((baseChangeAlongProj f X) ⁻¹ᵁ g.domain).ι ≫ pullback.fst f (X ↘ S))
    ((baseChangeAlongProj f X) ∣_ g.domain ≫ g.hom)
    (by
      have hg : g.hom ≫ (Y ↘ S) = g.domain.ι ≫ (X ↘ S) :=
        (Hom.isOver_iff (S := S)).mp ‹g.IsOver S›
      have hc : pullback.fst f (X ↘ S) ≫ f = pullback.snd f (X ↘ S) ≫ (X ↘ S) :=
        pullback.condition
      have hmr : (baseChangeAlongProj f X) ∣_ g.domain ≫ g.domain.ι =
          ((baseChangeAlongProj f X) ⁻¹ᵁ g.domain).ι ≫ baseChangeAlongProj f X :=
        morphismRestrict_ι _ _
      calc (((baseChangeAlongProj f X) ⁻¹ᵁ g.domain).ι ≫ pullback.fst f (X ↘ S)) ≫ f
          = ((baseChangeAlongProj f X) ⁻¹ᵁ g.domain).ι ≫ (pullback.fst f (X ↘ S) ≫ f) :=
            Category.assoc _ _ _
        _ = ((baseChangeAlongProj f X) ⁻¹ᵁ g.domain).ι ≫ (baseChangeAlongProj f X ≫ (X ↘ S)) := by
            rw [hc]
        _ = (((baseChangeAlongProj f X) ⁻¹ᵁ g.domain).ι ≫ baseChangeAlongProj f X) ≫ (X ↘ S) :=
            (Category.assoc _ _ _).symm
        _ = ((baseChangeAlongProj f X) ∣_ g.domain ≫ g.domain.ι) ≫ (X ↘ S) := by rw [← hmr]
        _ = (baseChangeAlongProj f X ∣_ g.domain) ≫ (g.domain.ι ≫ (X ↘ S)) :=
            Category.assoc _ _ _
        _ = (baseChangeAlongProj f X ∣_ g.domain) ≫ (g.hom ≫ (Y ↘ S)) := by rw [← hg]
        _ = ((baseChangeAlongProj f X) ∣_ g.domain ≫ g.hom) ≫ (Y ↘ S) :=
            (Category.assoc _ _ _).symm)

/-- The domain of a base change is the preimage of the domain. -/
@[simp]
theorem PartialMap.baseChangeAlong_domain (g : X.PartialMap Y) [g.IsOver S]
    [Surjective f] [UniversallyOpen f] :
    (PartialMap.baseChangeAlong f g).domain = (baseChangeAlongProj f X) ⁻¹ᵁ g.domain := rfl

/-- The base-changed partial map is over the new base `T`. -/
theorem PartialMap.baseChangeAlong_isOver (g : X.PartialMap Y) [g.IsOver S]
    [Surjective f] [UniversallyOpen f] : (PartialMap.baseChangeAlong f g).IsOver T := by
  change ((PartialMap.baseChangeAlong f g).hom).IsOver T
  rw [Hom.isOver_iff]
  show pullback.lift (((baseChangeAlongProj f X) ⁻¹ᵁ g.domain).ι ≫ pullback.fst f (X ↘ S))
      ((baseChangeAlongProj f X) ∣_ g.domain ≫ g.hom) _ ≫ pullback.fst f (Y ↘ S) =
    ((baseChangeAlongProj f X) ⁻¹ᵁ g.domain).ι ≫ pullback.fst f (X ↘ S)
  rw [pullback.lift_fst]


/-! ## 4. The two components of the base-changed partial map, and a bookkeeping lemma about
inclusions of an open in itself

These are the workhorses of the companion files (base change of partial isomorphisms and of
birational maps).  They are stated once and for all here so that the companion files can import
them instead of redeclaring them. -/

/-- The canonical morphism of an inclusion of an open in itself is the identity. -/
lemma Scheme.homOfLE_self {X : Scheme.{0}} (U : X.Opens) (h : U ≤ U) : X.homOfLE h = 𝟙 _ := by
  rw [← cancel_mono U.ι, Scheme.homOfLE_ι, Category.id_comp]

/-- The `T`-component of the morphism underlying the base change of a partial map. -/
lemma PartialMap.baseChangeAlong_hom_fst {S T X Y : Scheme.{0}} (f : T ⟶ S) [X.Over S]
    [Y.Over S] [Surjective f] [UniversallyOpen f] (g : X.PartialMap Y) [g.IsOver S] :
    (PartialMap.baseChangeAlong f g).hom ≫ pullback.fst f (Y ↘ S) =
      (((Work.K3.baseChangeAlongProj f X) ⁻¹ᵁ g.domain) :
          (Work.K3.baseChangeAlong f X).Opens).ι ≫ pullback.fst f (X ↘ S) := by
  dsimp only [PartialMap.baseChangeAlong]
  rw [pullback.lift_fst]

/-- The `Y`-component of the morphism underlying the base change of a partial map: it is the
restriction of the underlying morphism of `g` to the preimage of the domain of `g`. -/
lemma PartialMap.baseChangeAlong_hom_snd {S T X Y : Scheme.{0}} (f : T ⟶ S) [X.Over S]
    [Y.Over S] [Surjective f] [UniversallyOpen f] (g : X.PartialMap Y) [g.IsOver S] :
    (PartialMap.baseChangeAlong f g).hom ≫ pullback.snd f (Y ↘ S) =
      (Work.K3.baseChangeAlongProj f X ∣_ g.domain) ≫ g.hom := by
  dsimp only [PartialMap.baseChangeAlong]
  rw [pullback.lift_snd]

end Along

end Work.K3
