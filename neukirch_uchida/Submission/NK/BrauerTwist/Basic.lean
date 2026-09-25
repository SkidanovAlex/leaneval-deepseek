/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The cyclotomic twist: `μ_p`-coefficients for the Brauer / Hasse / Neukirch chain

This is the coefficient layer of `Submission/Work/BrauerTwist/`.  The sibling area
`Submission/Work/BrauerHasse/` develops the Brauer / Hasse-principle / Neukirch-criterion chain with
the **trivial** coefficient module `NK.BrauerHasse.Coeff p = Z/p`, i.e. it computes
`H²(G_κ, Z/p)`.  The classical input of the classical proof of Neukirch–Uchida is however

  `H²(G_κ, μ_p) = Br(κ)[p] ≅ Z/p`,

with `μ_p = Z/p(1)` the module of `p`-th roots of unity, on which `G_κ` acts through the cyclotomic
character.  The two differ: with trivial coefficients local Tate duality gives
`H²(G_κ, Z/p) ≅ Hom(μ_p(κ), Q/Z)`, which *vanishes* whenever `μ_p ⊄ κ` — e.g. for `κ = Q_p`,
`p` odd.  See `Submission/Work/LocalCFT/README.md` §11 and
`Submission/Work/LocalCFT/Brauer/Twist.lean`.  This file replaces the coefficient module by the
correct one.

## Contents

* `NK.BrauerTwist.CoeffInt` — the coefficient ring: `Z` lifted into the universe of the fields
  (Mathlib's group cohomology requires the coefficient ring and the group to live in the same
  universe).  `Z` is the right ring here because the `p`-th roots of unity form a cyclic group of
  order `p`, hence are a `Z`-module *canonically* (`n • x = x ^ n`), with no choice of generator.
* `NK.BrauerTwist.muLevel p L` — for a finite Galois level `L` of `K'/K`, the `p`-th roots of
  unity in `L`, realised inside `rootsOfUnity p K'` as the fixed points of `Gal(K'/L)`, together
  with the coefficients inclusions `muIncl`, `muInclAddHom`, `muInclLinearMap`, `muIncl_smul`.
* `NK.BrauerTwist.muRep p L` — the representation of the level group
  `Gal(K'/K) ⧸ Gal(K'/L) = Gal(L/K)` on `μ_p(L)`; this is the cyclotomic twist `Z/p(1)`.
* `NK.BrauerTwist.levelGroupHom`, `NK.BrauerTwist.levelRep p U L`, `LevelH2 p U L` — the level
  cohomology `H²(U ⧸ (U ∩ Gal(K'/L)), μ_p(L))` of a closed subgroup `U ≤ Gal(K'/K)`.
* `NK.BrauerTwist.levelMap` — the transition (inflation + coefficient inclusion) between levels,
  with its computation rule `levelMap_apply`.
* `NK.BrauerTwist.localLevelRep`, `LocalLevelH2`, `locCoeff`, `locLevel`, `localLevelMap` — the
  local level cohomology at a place and the level-wise localisation map.

## Conventions

* `K'` is a separable closure of `K`; every intermediate field considered is a
  `FiniteGaloisIntermediateField K K'`, i.e. finite Galois over `K`.  These are directed under
  inclusion (`⊔`), which is what makes the filtered colimit of `Profinite.lean` work.
* For a level `L`, `N_L := L.fixingSubgroup = Gal(K'/L) ◁ Gal(K'/K)`, and
  `NK.BrauerHasse.LevelGroup U L = U ⧸ (N_L.subgroupOf U)` is the *level group* of `U`.
* The coefficient module at level `L` is `muLevel p L`, the *fixed points* of `N_L` acting on
  `rootsOfUnity p K'`.  Since `L/K` is Galois, `N_L` is normal, so `muLevel p L` is a
  `Gal(K'/K)`-submodule of `μ_p(K')`; it is (canonically) the group of `p`-th roots of unity
  *of `L`*.  For `L ≤ L'` we have `N_{L'} ≤ N_L`, hence `muLevel p L ≤ muLevel p L'`, and since
  `N_L` acts trivially, `muLevel p L` is a module for the level group.
* **The level cohomology is the cohomology of the level *group*, not of the profinite group `U`:**

  `LevelH2 p U L = H²(LevelGroup U L, μ_p(L))`.

  This is the classical presentation of the continuous cohomology as
  `H²(U, μ_p) = colim_L H²(U ⧸ (U ∩ Gal(K'/L)), μ_p(L))` (Serre, *Galois Cohomology*, I.2.2,
  Prop. 8).  Taking instead `H²(U, μ_p(L))` — the abstract cohomology of the profinite group `U` —
  would be *wrong*: for `U = Z_p` and `p` odd the abstract `H²(U, Z/p)` vanishes while the
  continuous group is `Z/p`.  See `README.md` §1.
* The group-level maps (`LevelGroup`, `levelQuotHom`, `localInclHom`, `localLevelQuotHom`,
  `LocalLevelGroup`) are coefficient-generic and are reused from
  `Submission/Work/BrauerHasse/Profinite.lean`.
-/

import Mathlib
import Mathlib.FieldTheory.Galois.GaloisClosure
import Submission.NK.BrauerHasse.Profinite

open CategoryTheory Representation
open scoped Pointwise

set_option autoImplicit false

universe u

namespace NK.BrauerTwist

/-- The coefficient ring of the twisted theory: `Z`, lifted into the universe of the fields, so
that Mathlib's `groupCohomology` (which requires the coefficient ring and the group to live in the
same universe) applies.

`Z` rather than `Z/p` because the `p`-th roots of unity form a cyclic group of order `p`, and hence
are canonically a `Z`-module (`n • x = x ^ n`); using `Z` avoids choosing a generator of `μ_p`.
The resulting cohomology groups are the usual `H^n(G, μ_p)`. -/
abbrev CoeffInt : Type u := ULift.{u} ℤ

section RootsOfUnity

variable {K K' : Type u} [Field K] [Field K'] [Algebra K K']

/-- The `p`-th roots of unity of `K'` are preserved by every `K`-algebra automorphism of `K'`. -/
lemma smul_mem_rootsOfUnity (p : ℕ) (σ : K' ≃ₐ[K] K') {x : (K')ˣ}
    (hx : x ∈ rootsOfUnity p K') : σ • x ∈ rootsOfUnity p K' := by
  rw [mem_rootsOfUnity] at hx ⊢
  rw [← smul_pow', hx, smul_one]

/-- **The cyclotomic module.**  The `p`-th roots of unity of `K'`, with the natural action of
`Gal(K'/K)`: this is the module `μ_p = Z/p(1)` of the twisted theory. -/
noncomputable instance instMulDistribMulActionRoots (p : ℕ) :
    MulDistribMulAction Gal(K'/K) (rootsOfUnity p K') where
  smul σ x := ⟨σ • (x : (K')ˣ), smul_mem_rootsOfUnity p σ x.2⟩
  one_smul x := Subtype.ext (one_smul _ (x : (K')ˣ))
  mul_smul a b x := Subtype.ext (mul_smul a b (x : (K')ˣ))
  smul_mul a x y := Subtype.ext (smul_mul' a (x : (K')ˣ) (y : (K')ˣ))
  smul_one a := Subtype.ext (smul_one a)

@[simp]
lemma coe_smul_rootsOfUnity (p : ℕ) (σ : Gal(K'/K)) (x : rootsOfUnity p K') :
    ((σ • x : rootsOfUnity p K') : (K')ˣ) = σ • (x : (K')ˣ) := rfl

/-- The action of `Gal(K'/K)` on `μ_p(K')`, transported to the `Additive` wrapper. -/
instance instDistribMulActionAdditive {G A : Type*} [Monoid G] [CommGroup A]
    [MulDistribMulAction G A] : DistribMulAction G (Additive A) where
  smul g x := Additive.ofMul (g • Additive.toMul x)
  one_smul x := congrArg Additive.ofMul (one_smul G (Additive.toMul x))
  mul_smul g h x := congrArg Additive.ofMul (mul_smul g h (Additive.toMul x))
  smul_zero g := congrArg Additive.ofMul (smul_one g)
  smul_add g x y := congrArg Additive.ofMul (smul_mul' g (Additive.toMul x) (Additive.toMul y))

/-- **`Rep.res` is associative**: restricting a restricted representation is restriction along the
composite of the group homomorphisms. -/
lemma res_res {k : Type*} [Semiring k] {G H L : Type*} [Monoid G] [Monoid H] [Monoid L]
    (f : H →* G) (g : L →* H) (X : Rep k G) :
    Rep.res g (Rep.res f X) = Rep.res (f.comp g) X := by
  simp only [Rep.res, Rep.resFunctor, MonoidHom.comp_assoc]

/-- The scalar action of `ULift R` commutes with any action commuting with the `R`-action. -/
instance instSMulCommClassULift (M R A : Type*) [SMul R A] [SMul M A] [SMulCommClass M R A] :
    SMulCommClass M (ULift R) A where
  smul_comm m n x := by
    show m • (n.down • x) = n.down • (m • x)
    exact SMulCommClass.smul_comm m n.down x

end RootsOfUnity

section RepAPI

/-- The restriction of the identity is the identity. -/
lemma resMap_id {k : Type*} [Semiring k] {G H : Type*} [Monoid G] [Monoid H]
    (f : H →* G) (X : Rep k G) : Rep.resMap f (𝟙 X) = 𝟙 (Rep.res f X) :=
  (Rep.resFunctor f).map_id X

/-- Restriction is functorial: the restriction of a composition is the composition of the
restrictions. -/
lemma resMap_comp {k : Type*} [Semiring k] {G H : Type*} [Monoid G] [Monoid H]
    (f : H →* G) {X Y Z : Rep k G} (p : X ⟶ Y) (q : Y ⟶ Z) :
    Rep.resMap f (p ≫ q) = Rep.resMap f p ≫ Rep.resMap f q :=
  (Rep.resFunctor f).map_comp p q

end RepAPI

section Level

variable {K K' : Type u} [Field K] [Field K'] [Algebra K K'] [IsSepClosure K K']

/-- The `G`-action on the fixed points of a *normal* subgroup `N ≤ G` in a commutative group `A`
with a multiplicative distributive action: `N` being normal, its fixed points are `G`-stable.
(For the quotient by `N` see Mathlib's `MulDistribMulAction (G ⧸ H) (FixedPoints.subgroup H A)`.) -/
instance instMulDistribMulActionFixedPoints {G A : Type*} [Group G] [CommGroup A]
    [MulDistribMulAction G A] (N : Subgroup G) [N.Normal] :
    MulDistribMulAction G (FixedPoints.subgroup N A) where
  smul g x := ⟨g • (x : A), by
    intro n
    have hmem : g⁻¹ * (n : G) * g ∈ N :=
      (inferInstance : N.Normal).conj_mem' (n : G) n.2 g
    have hx : (g⁻¹ * (n : G) * g) • (x : A) = (x : A) :=
      x.2 ⟨g⁻¹ * (n : G) * g, hmem⟩
    calc n • (g • (x : A)) = ((n : G) * g) • (x : A) := (mul_smul _ _ _).symm
      _ = (g * (g⁻¹ * (n : G) * g)) • (x : A) :=
          congrArg (fun y : G => y • (x : A)) (by group)
      _ = g • ((g⁻¹ * (n : G) * g) • (x : A)) := mul_smul _ _ _
      _ = g • (x : A) := by rw [hx]⟩
  one_smul x := Subtype.ext (one_smul G (x : A))
  mul_smul g h x := Subtype.ext (mul_smul g h (x : A))
  smul_mul g x y := Subtype.ext (smul_mul' g (x : A) (y : A))
  smul_one g := Subtype.ext (smul_one g)

@[simp]
lemma coe_smul_fixedPoints {G A : Type*} [Group G] [CommGroup A] [MulDistribMulAction G A]
    (N : Subgroup G) [N.Normal] (g : G) (x : FixedPoints.subgroup N A) :
    ((g • x : FixedPoints.subgroup N A) : A) = g • (x : A) := rfl


/-- **The level module `μ_p(L)`.**  For a finite Galois intermediate field `L` of `K'/K`, the
`p`-th roots of unity in `K'` fixed by `Gal(K'/L)` — canonically the group of `p`-th roots of unity
of `L`, realised inside the ambient group `(K')ˣ` so that inclusions of levels become literal
inclusions of subgroups.

Since `L/K` is Galois, `Gal(K'/L) ◁ Gal(K'/K)` and `μ_p(L)` is a `Gal(K'/K)`-submodule of `μ_p(K')`.
-/
noncomputable abbrev muLevel (p : ℕ) (L : FiniteGaloisIntermediateField K K') :
    Subgroup (rootsOfUnity p K') :=
  FixedPoints.subgroup (L.fixingSubgroup : Subgroup Gal(K'/K)) (rootsOfUnity p K')

omit [IsSepClosure K K'] in
/-- Membership in the level module, unwound. -/
@[simp]
lemma mem_muLevel {p : ℕ} (L : FiniteGaloisIntermediateField K K') (x : rootsOfUnity p K') :
    x ∈ muLevel p L ↔ ∀ σ : L.fixingSubgroup, σ • x = x := Iff.rfl

/-- The action of `Gal(K'/K)` on `μ_p(L)` is the restriction of the action on `μ_p(K')`. -/
@[simp]
lemma coe_smul_muLevel (p : ℕ) (L : FiniteGaloisIntermediateField K K')
    (σ : Gal(K'/K)) (x : ↥(muLevel p L)) :
    ((σ • x : ↥(muLevel p L)) : rootsOfUnity p K') = σ • (x : rootsOfUnity p K') := rfl

/-- **Monotonicity of the level modules.**  For `L ≤ L'` the module `μ_p(L)` is contained in
`μ_p(L')`. -/
lemma muLevel_mono {p : ℕ} {L L' : FiniteGaloisIntermediateField K K'} (h : L ≤ L')
    {x : rootsOfUnity p K'} (hx : x ∈ muLevel p L) : x ∈ muLevel p L' := by
  rw [mem_muLevel] at hx ⊢
  intro σ
  exact hx ⟨σ.1, IntermediateField.fixingSubgroup_le h σ.2⟩

/-- The canonical inclusion of level modules. -/
noncomputable def muIncl {p : ℕ} {L L' : FiniteGaloisIntermediateField K K'} (h : L ≤ L') :
    ↥(muLevel p L) → ↥(muLevel p L') :=
  fun x => ⟨x.1, muLevel_mono h x.2⟩

@[simp]
lemma muIncl_coe {p : ℕ} {L L' : FiniteGaloisIntermediateField K K'} (h : L ≤ L')
    (x : ↥(muLevel p L)) :
    ((muIncl h x : ↥(muLevel p L')) : rootsOfUnity p K') = x.1 := rfl

/-- The additive form of the coefficient inclusion. -/
noncomputable def muInclAddHom {p : ℕ} {L L' : FiniteGaloisIntermediateField K K'}
    (h : L ≤ L') : Additive ↥(muLevel p L) →+ Additive ↥(muLevel p L') where
  toFun x := muIncl h x
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp]
lemma muInclAddHom_apply {p : ℕ} {L L' : FiniteGaloisIntermediateField K K'} (h : L ≤ L')
    (x : Additive ↥(muLevel p L)) :
    (muInclAddHom h x : ↥(muLevel p L')) = muIncl h (Additive.toMul x) := rfl

/-- The coefficient inclusion is `Gal(K'/K)`-equivariant for the ambient actions. -/
lemma muIncl_smul {p : ℕ} {L L' : FiniteGaloisIntermediateField K K'} (h : L ≤ L')
    (σ : Gal(K'/K)) (x : Additive ↥(muLevel p L)) :
    muInclAddHom h (σ • x) = σ • (muInclAddHom h x) := by
  apply Additive.toMul.injective
  apply Subtype.ext
  rfl

/-- The `Z`-linear form of the coefficient inclusion. -/
noncomputable def muInclLinearMap {p : ℕ} {L L' : FiniteGaloisIntermediateField K K'} (h : L ≤ L') :
    Additive ↥(muLevel p L) →ₗ[CoeffInt] Additive ↥(muLevel p L') where
  toFun := muInclAddHom h
  map_add' := map_add _
  map_smul' n x := by
    change muInclAddHom h (n.down • x) = n.down • muInclAddHom h x
    exact map_zsmul (muInclAddHom h) n.down x

@[simp]
lemma muInclLinearMap_apply {p : ℕ} {L L' : FiniteGaloisIntermediateField K K'} (h : L ≤ L')
    (x : Additive ↥(muLevel p L)) : muInclLinearMap h x = muInclAddHom h x := rfl

/-! ## The level cohomology of a closed subgroup

The level cohomology of `U ≤ Gal(K'/K)` at the level `L` is the cohomology of the *level group*
`U ⧸ (Gal(K'/L) ⊓ U)` with coefficients in the level module `μ_p(L)`:

`NK.BrauerTwist.LevelH2 p U L = H²(U ⧸ (Gal(K'/L) ⊓ U), μ_p(L))`.

This is the classical "continuous cohomology" presentation (Serre, *Galois Cohomology* I.2.2
Prop. 8): `H²(G_κ, μ_p) = colim_L H²(Gal(L/κ), μ_p(L))`.  It matters that the cohomology is taken
over the *level group* and not over the ambient profinite group `U`: for a profinite group the
abstract group cohomology with finite coefficients can differ from the continuous one (e.g. for
`U = Z_p`, `p` odd, the abstract `H²(U, Z/p)` vanishes while the continuous one is `Z/p`), so the
level-group colimit is the coefficient-correct object.
-/

/-- **The representation of the level group on the level module.**  The quotient group
`Gal(K'/K) ⧸ Gal(K'/L) = Gal(L/K)` acts on the `p`-th roots of unity `μ_p(L)`: this is the
cyclotomic twist `Z/p(1)` at the level `L`. -/
noncomputable def muRep (p : ℕ) (L : FiniteGaloisIntermediateField K K') :
    Rep CoeffInt (Gal(K'/K) ⧸ L.fixingSubgroup) :=
  Rep.ofDistribMulAction CoeffInt _ (Additive ↥(muLevel p L))

/-- The action of the level group on `μ_p(L)`, computed at the class of an element. -/
@[simp]
lemma muRep_ρ_apply (p : ℕ) (L : FiniteGaloisIntermediateField K K') (σ : Gal(K'/K))
    (x : Additive ↥(muLevel p L)) :
    (muRep p L).ρ (σ : Gal(K'/K) ⧸ L.fixingSubgroup) x = σ • x := rfl

/-- The quotient map `U ⧸ (Gal(K'/L) ⊓ U) →* Gal(K'/K) ⧸ Gal(K'/L)` induced by the inclusion
`U ≤ Gal(K'/K)`. -/
noncomputable def levelGroupHom (U : Subgroup Gal(K'/K))
    (L : FiniteGaloisIntermediateField K K') :
    NK.BrauerHasse.LevelGroup U L →* Gal(K'/K) ⧸ L.fixingSubgroup :=
  QuotientGroup.map (L.fixingSubgroup.subgroupOf U) L.fixingSubgroup U.subtype le_rfl

@[simp]
lemma levelGroupHom_mk (U : Subgroup Gal(K'/K))
    (L : FiniteGaloisIntermediateField K K') (u : U) :
    levelGroupHom U L (QuotientGroup.mk u) =
      ((u : Gal(K'/K)) : Gal(K'/K) ⧸ L.fixingSubgroup) := rfl

/-- **The level representation of a closed subgroup.** -/
noncomputable abbrev levelRep (p : ℕ) (U : Subgroup Gal(K'/K))
    (L : FiniteGaloisIntermediateField K K') : Rep CoeffInt (NK.BrauerHasse.LevelGroup U L) :=
  Rep.res (levelGroupHom U L) (muRep p L)

/-- The action of the level group on `μ_p(L)` for an arbitrary closed subgroup, computed at the
class of an element of `U`. -/
@[simp]
lemma levelRep_ρ_apply (p : ℕ) (U : Subgroup Gal(K'/K))
    (L : FiniteGaloisIntermediateField K K') (u : U) (x : Additive ↥(muLevel p L)) :
    (levelRep p U L).ρ (QuotientGroup.mk u) x = (u : Gal(K'/K)) • x := rfl

/-- **The level cohomology `H²(U ⧸ (Gal(K'/L) ⊓ U), μ_p(L))`** of the cyclotomic twist at the
level `L`. -/
noncomputable abbrev LevelH2 (p : ℕ) (U : Subgroup Gal(K'/K))
    (L : FiniteGaloisIntermediateField K K') : ModuleCat CoeffInt :=
  groupCohomology (levelRep p U L) 2

/-- **The coefficient morphism of the transition map**: the inclusion `μ_p(L) ↪ μ_p(L')` as a map
from the restriction of the level-`L` representation to the level-`L'` representation. -/
noncomputable def levelMapCoeff (p : ℕ) (U : Subgroup Gal(K'/K))
    {L L' : FiniteGaloisIntermediateField K K'} (h : L ≤ L') :
    Rep.res (NK.BrauerHasse.levelQuotHom (U := U) h) (levelRep p U L) ⟶ levelRep p U L' :=
  Rep.ofHom (LinearMap.intertwiningMap_of_isIntertwiningMap
    (ρ := (Rep.res (NK.BrauerHasse.levelQuotHom (U := U) h) (levelRep p U L)).ρ)
    (σ := (levelRep p U L').ρ) (f := muInclLinearMap h)
    (fun q x => by
      induction q using QuotientGroup.induction_on with
      | H u =>
        simp only [NK.BrauerHasse.levelQuotHom, QuotientGroup.map_mk, MonoidHom.id_apply,
          Rep.coe_res_obj_ρ', levelRep_ρ_apply, muInclLinearMap_apply]
        exact muIncl_smul h (u : Gal(K'/K)) x))

/-- The morphism `levelMapCoeff` acts by the coefficient inclusion. -/
lemma levelMapCoeff_apply (p : ℕ) (U : Subgroup Gal(K'/K))
    {L L' : FiniteGaloisIntermediateField K K'} (h : L ≤ L')
    (x : (Rep.res (NK.BrauerHasse.levelQuotHom (U := U) h) (levelRep p U L)).V) :
    (levelMapCoeff p U h).hom.toLinearMap x = muInclLinearMap h x := rfl

/-- **The transition map between levels**: inflation along `U ⧸ (Gal(K'/L') ⊓ U) →*
U ⧸ (Gal(K'/L) ⊓ U)` together with the coefficient inclusion `μ_p(L) ↪ μ_p(L')`. -/
noncomputable def levelMap (p : ℕ) (U : Subgroup Gal(K'/K))
    {L L' : FiniteGaloisIntermediateField K K'} (h : L ≤ L') :
    LevelH2 p U L ⟶ LevelH2 p U L' :=
  groupCohomology.map (NK.BrauerHasse.levelQuotHom (U := U) h) (levelMapCoeff p U h) 2

/-- The computation rule for the transition map. -/
lemma levelMap_apply (p : ℕ) (U : Subgroup Gal(K'/K))
    {L L' : FiniteGaloisIntermediateField K K'} (h : L ≤ L') (x : LevelH2 p U L) :
    (levelMap p U h).hom x =
      (groupCohomology.map (NK.BrauerHasse.levelQuotHom (U := U) h) (levelMapCoeff p U h)
        2).hom x := rfl

-- The coherence laws of the level system, `NK.BrauerTwist.levelMap_refl` and
-- `NK.BrauerTwist.levelMap_comp`, are proved in
-- `Submission/Work/BrauerTwist/levelMap_refl.lean` and
-- `Submission/Work/BrauerTwist/levelMap_comp.lean`; they enter only through the filtered-colimit
-- bookkeeping of `Submission/Work/BrauerTwist/Profinite.lean`.

/-! ## The local cohomology at a place and the localisation map -/

/-- The **decomposition group** of a place `A` of `K'`: the stabiliser of `A` in `Gal(K'/K)`. -/
noncomputable abbrev stabSubgroup (A : ValuationSubring K') : Subgroup Gal(K'/K) :=
  MulAction.stabilizer Gal(K'/K) A

/-- The local level representation: the level group of the decomposition group `U ⊓ D_A` acting on
`μ_p(L)`. -/
noncomputable abbrev localLevelRep (p : ℕ) (U : Subgroup Gal(K'/K)) (A : ValuationSubring K')
    (L : FiniteGaloisIntermediateField K K') :
    Rep CoeffInt (NK.BrauerHasse.LocalLevelGroup U A L) :=
  Rep.res (levelGroupHom (U ⊓ stabSubgroup A) L) (muRep p L)

/-- **The local level cohomology `H²((U ⊓ D_A) ⧸ ((U ⊓ D_A) ⊓ Gal(K'/L)), μ_p(L))`.** -/
noncomputable abbrev LocalLevelH2 (p : ℕ) (U : Subgroup Gal(K'/K)) (A : ValuationSubring K')
    (L : FiniteGaloisIntermediateField K K') : ModuleCat CoeffInt :=
  groupCohomology (localLevelRep p U A L) 2

/-- **The level-wise localisation map**: restriction from the level group of `U` to the level group
of the decomposition group `U ⊓ D_A`, with the same coefficient module `μ_p(L)`. -/
noncomputable def locCoeff (p : ℕ) (U : Subgroup Gal(K'/K)) (A : ValuationSubring K')
    (L : FiniteGaloisIntermediateField K K') :
    Rep.res (NK.BrauerHasse.localInclHom U A L) (levelRep p U L) ⟶ localLevelRep p U A L :=
  Rep.ofHom (LinearMap.intertwiningMap_of_isIntertwiningMap
    (ρ := (Rep.res (NK.BrauerHasse.localInclHom U A L) (levelRep p U L)).ρ)
    (σ := (localLevelRep p U A L).ρ) (f := muInclLinearMap (le_refl L))
    (fun q x => by
      induction q using QuotientGroup.induction_on with
      | H u =>
        simp only [NK.BrauerHasse.localInclHom, QuotientGroup.map_mk, MonoidHom.id_apply,
          Rep.coe_res_obj_ρ', levelRep_ρ_apply, levelGroupHom_mk, muInclLinearMap_apply]
        rfl))

/-- **The level-wise localisation map.** -/
noncomputable def locLevel (p : ℕ) (U : Subgroup Gal(K'/K)) (A : ValuationSubring K')
    (L : FiniteGaloisIntermediateField K K') : LevelH2 p U L ⟶ LocalLevelH2 p U A L :=
  groupCohomology.map (NK.BrauerHasse.localInclHom U A L) (locCoeff p U A L) 2

/-- **Inflation between levels, locally at a place.** -/
noncomputable def localLevelMapCoeff (p : ℕ) (U : Subgroup Gal(K'/K)) (A : ValuationSubring K')
    {L L' : FiniteGaloisIntermediateField K K'} (h : L ≤ L') :
    Rep.res (NK.BrauerHasse.localLevelQuotHom U A h) (localLevelRep p U A L) ⟶
      localLevelRep p U A L' :=
  Rep.ofHom (LinearMap.intertwiningMap_of_isIntertwiningMap
    (ρ := (Rep.res (NK.BrauerHasse.localLevelQuotHom U A h) (localLevelRep p U A L)).ρ)
    (σ := (localLevelRep p U A L').ρ) (f := muInclLinearMap h)
    (fun q x => by
      induction q using QuotientGroup.induction_on with
      | H u =>
        simp only [NK.BrauerHasse.localLevelQuotHom, QuotientGroup.map_mk, MonoidHom.id_apply,
          Rep.coe_res_obj_ρ', levelRep_ρ_apply, muInclLinearMap_apply]
        exact muIncl_smul h (u : Gal(K'/K)) x))

/-- **Inflation between levels, locally at a place.** -/
noncomputable def localLevelMap (p : ℕ) (U : Subgroup Gal(K'/K)) (A : ValuationSubring K')
    {L L' : FiniteGaloisIntermediateField K K'} (h : L ≤ L') :
    LocalLevelH2 p U A L ⟶ LocalLevelH2 p U A L' :=
  groupCohomology.map (NK.BrauerHasse.localLevelQuotHom U A h) (localLevelMapCoeff p U A h) 2

-- The local coherence laws `NK.BrauerTwist.localLevelMap_refl` and
-- `NK.BrauerTwist.localLevelMap_comp` are proved in
-- `Submission/Work/BrauerTwist/localLevelMap_comp.lean`.

end Level

end NK.BrauerTwist
