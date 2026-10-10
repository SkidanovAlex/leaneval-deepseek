import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.Analysis.Normed.Field.Basic
import Submission.Work.SSGRoute.E9cConj
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

noncomputable section

namespace Work.SSGRoute

open CategoryTheory SSGRoute.PTExt

section ConjLocalUnits

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K]
  [Algebra k K] [FiniteDimensional k K] [IsGalois k K]

/-- **The compatibility of `Place.localRingEquiv` with `localAut` under conjugation.**

For `h ∈ D_v` the diagram
`K_v --localAut v h--> K_v`, `K_{σ v} --localAut (σ v) (σ h σ⁻¹)--> K_{σ v}` commutes with the
canonical isomorphism `Place.localRingEquiv σ v : K_v ≃+* K_{σ v}`.  Both composites are continuous
maps out of the local field `K_v` agreeing on the dense image of `K`, so it suffices to check the
identity on `algebraMap K _ x`, where both sides reduce to `algebraMap K (K_{σ v}) (σ (h x))`. -/
theorem localAut_conjStab_localRingEquiv (σ : K ≃ₐ[k] K) (v : NK.GlobalCFT.Place K)
    (h : decompK (k := k) v) (y : NK.GlobalCFT.Place.localField K v) :
    NK.HassePrinciple.localAut (σ • v) (conjStabHom k K σ v h)
        (NK.GlobalCFT.Place.localRingEquiv σ v y)
      = NK.GlobalCFT.Place.localRingEquiv σ v (NK.HassePrinciple.localAut v h y) := by
  have hdense : DenseRange (algebraMap K (NK.GlobalCFT.Place.localField K v)) :=
    NK.GlobalCFT.Galois.denseRange_algebraMap_localField v
  have hcont₁ : Continuous (fun z : NK.GlobalCFT.Place.localField K v =>
      NK.HassePrinciple.localAut (σ • v) (conjStabHom k K σ v h)
        (NK.GlobalCFT.Place.localRingEquiv σ v z)) :=
    (NK.HassePrinciple.localAut_continuous (σ • v) (conjStabHom k K σ v h)).comp
      (NK.GlobalCFT.Galois.continuous_localRingEquiv σ v)
  have hcont₂ : Continuous (fun z : NK.GlobalCFT.Place.localField K v =>
      NK.GlobalCFT.Place.localRingEquiv σ v (NK.HassePrinciple.localAut v h z)) :=
    (NK.GlobalCFT.Galois.continuous_localRingEquiv σ v).comp
      (NK.HassePrinciple.localAut_continuous v h)
  have hfun : (fun z : NK.GlobalCFT.Place.localField K v =>
      NK.HassePrinciple.localAut (σ • v) (conjStabHom k K σ v h)
        (NK.GlobalCFT.Place.localRingEquiv σ v z))
      = fun z => NK.GlobalCFT.Place.localRingEquiv σ v (NK.HassePrinciple.localAut v h z) := by
    refine DenseRange.equalizer hdense hcont₁ hcont₂ ?_
    funext x
    simp only [Function.comp_apply]
    rw [NK.HassePrinciple.localAut_algebraMap, NK.GlobalCFT.Place.localRingEquiv_algebraMap,
      NK.HassePrinciple.localAut_algebraMap, NK.GlobalCFT.Place.localRingEquiv_algebraMap]
    simp [conjStabHom]
  exact congrFun hfun y

/-- **The compatibility of the local actions under conjugation**, at the level of local units:
transporting a local unit along `Place.localRingEquiv σ v` intertwines the action of `h ∈ D_v` on
`K_vˣ` with the action of `σ h σ⁻¹ ∈ D_{σ v}` on `K_{σ v}ˣ`. -/
theorem actVal_localUnitsEquiv_conjStab (σ : K ≃ₐ[k] K) (v : NK.GlobalCFT.Place K)
    (h : decompK (k := k) v) (u : (NK.GlobalCFT.Place.localField K v)ˣ) :
    NK.HassePrinciple.actVal σ v (NK.HassePrinciple.localUnitsEquiv (K := k) v h u)
      = NK.HassePrinciple.localUnitsEquiv (K := k) (σ • v)
          (conjStabHom k K σ v h) (NK.HassePrinciple.actVal σ v u) := by
  refine Units.ext ?_
  show (NK.GlobalCFT.Place.localRingEquiv σ v)
      ((NK.HassePrinciple.localUnitsEquiv (K := k) v h u : (NK.GlobalCFT.Place.localField K v)ˣ) :
        NK.GlobalCFT.Place.localField K v)
    = NK.HassePrinciple.localAut (σ • v) (conjStabHom k K σ v h)
      ((NK.GlobalCFT.Place.localRingEquiv σ v) (u : NK.GlobalCFT.Place.localField K v))
  rw [NK.HassePrinciple.coe_localUnitsEquiv]
  exact (localAut_conjStab_localRingEquiv σ v h (u : NK.GlobalCFT.Place.localField K v)).symm

/-- The monoid homomorphism `K_vˣ →* K_{σ v}ˣ` induced by `Place.localRingEquiv σ v`; its
underlying function is `NK.HassePrinciple.actVal σ v`. -/
noncomputable def actValMonoidHom (σ : K ≃ₐ[k] K) (v : NK.GlobalCFT.Place K) :
    (NK.GlobalCFT.Place.localField K v)ˣ →* (NK.GlobalCFT.Place.localField K (σ • v))ˣ :=
  Units.map (NK.GlobalCFT.Place.localRingEquiv σ v).toMonoidHom

theorem actValMonoidHom_apply (σ : K ≃ₐ[k] K) (v : NK.GlobalCFT.Place K)
    (u : (NK.GlobalCFT.Place.localField K v)ˣ) :
    actValMonoidHom σ v u = NK.HassePrinciple.actVal σ v u := rfl

/-- The `Coeff`-linear map underlying the conjugation morphism: on `Additive (K_v)ˣ` it is the
additive map induced by `actVal σ v`. -/
noncomputable def localUnitsConjLM (σ : K ≃ₐ[k] K) (v : NK.GlobalCFT.Place K) :
    Additive (NK.GlobalCFT.Place.localField K v)ˣ →ₗ[Coeff]
      Additive (NK.GlobalCFT.Place.localField K (σ • v))ˣ where
  toFun := ⇑(actValMonoidHom σ v).toAdditive
  map_add' x y := map_add _ x y
  map_smul' n x := by
    obtain ⟨z⟩ := n
    exact AddMonoidHom.map_zsmul (actValMonoidHom σ v).toAdditive z x

@[simp]
theorem localUnitsConjLM_apply (σ : K ≃ₐ[k] K) (v : NK.GlobalCFT.Place K)
    (u : (NK.GlobalCFT.Place.localField K v)ˣ) :
    localUnitsConjLM σ v (Additive.ofMul u)
      = Additive.ofMul (NK.HassePrinciple.actVal σ v u) := rfl

@[simp]
theorem localUnitsK_rho_apply (v : NK.GlobalCFT.Place K) (h : decompK (k := k) v)
    (u : (NK.GlobalCFT.Place.localField K v)ˣ) :
    (localUnitsK (k := k) (K := K) v).ρ h (Additive.ofMul u)
      = Additive.ofMul (NK.HassePrinciple.localUnitsEquiv (K := k) v h u) := rfl

@[simp]
private theorem ideleToLocalUnits_apply (w : NK.GlobalCFT.Place K) (y : NK.GlobalCFT.Idele K) :
    (NK.HassePrinciple.ideleToLocalUnits k K w) (Additive.ofMul y)
      = Additive.ofMul (y w) := rfl

/-- **The intertwining identity for the conjugation map**: `localUnitsConjLM σ v` is `D_v`-equivariant
for the conjugation isomorphism `D_v →* D_{σ v}`.  It is the units-level form of
`actVal_localUnitsEquiv_conjStab`. -/
theorem localUnitsConjLM_intertwining (σ : K ≃ₐ[k] K) (v : NK.GlobalCFT.Place K)
    (h : decompK (k := k) v) (x : (localUnitsK (k := k) (K := K) v).V) :
    localUnitsConjLM σ v ((localUnitsK (k := k) (K := K) v).ρ h x)
      = (Rep.res (conjStabHom k K σ v) (localUnitsK (k := k) (K := K) (σ • v))).ρ h
          (localUnitsConjLM σ v x) := by
  have hx : x = Additive.ofMul (Additive.toMul x) := rfl
  rw [hx]
  exact congrArg Additive.ofMul (actVal_localUnitsEquiv_conjStab σ v h (Additive.toMul x))

/-- **The conjugation morphism of `D_v`-representations** `K_vˣ ⟶ res (conjStabHom σ v) K_{σ v}ˣ`:
the map on units is `NK.HassePrinciple.actVal σ v`. -/
noncomputable def localUnitsConjHom (σ : K ≃ₐ[k] K) (v : NK.GlobalCFT.Place K) :
    localUnitsK (k := k) (K := K) v ⟶
      Rep.res (conjStabHom k K σ v) (localUnitsK (k := k) (K := K) (σ • v)) :=
  Rep.ofHom
    { toLinearMap := localUnitsConjLM σ v
      isIntertwining' := fun h => by
        apply LinearMap.ext
        intro x
        exact localUnitsConjLM_intertwining σ v h x }

@[simp]
theorem localUnitsConjHom_apply (σ : K ≃ₐ[k] K) (v : NK.GlobalCFT.Place K)
    (x : (localUnitsK (k := k) (K := K) v).V) :
    localUnitsConjHom σ v x = localUnitsConjLM σ v x := rfl

/-- **The square commutes** (elementwise form): the `(σ • v)`-component of the idèle `σ • y` is the
image under `actVal σ v` of the `v`-component of `y` (`NK.HassePrinciple.smul_apply_smul_place`). -/
theorem localUnitsConj_square_apply (σ : K ≃ₐ[k] K) (v : NK.GlobalCFT.Place K)
    (y : NK.GlobalCFT.Idele K) :
    ((Rep.resMap (decompK (k := k) v).subtype ((conjTwist σ).app (idelesRepP k K))) ≫
        (Rep.resMap (conjStabHom k K σ v)
          (NK.HassePrinciple.ideleToLocalUnits k K (σ • v))))
        (Additive.ofMul y)
      = ((NK.HassePrinciple.ideleToLocalUnits k K v) ≫ localUnitsConjHom σ v)
        (Additive.ofMul y) := by
  exact congrArg Additive.ofMul (NK.HassePrinciple.smul_apply_smul_place σ v y)

/-- **The square commutes** on all elements of `𝕀_K`, as a statement about functions. -/
theorem localUnitsConj_square_apply_all (σ : K ≃ₐ[k] K) (v : NK.GlobalCFT.Place K)
    (x : (Rep.res (decompK (k := k) v).subtype (idelesRepP k K)).V) :
    ((Rep.resMap (decompK (k := k) v).subtype ((conjTwist σ).app (idelesRepP k K))) ≫
        (Rep.resMap (conjStabHom k K σ v)
          (NK.HassePrinciple.ideleToLocalUnits k K (σ • v)))) x
      = ((NK.HassePrinciple.ideleToLocalUnits k K v) ≫ localUnitsConjHom σ v) x := by
  have hx : x = Additive.ofMul (Additive.toMul x) := rfl
  rw [hx]
  exact localUnitsConj_square_apply σ v (Additive.toMul x)

/-- **The square of `D_v`-modules commutes.** -/
theorem localUnitsConj_square (σ : K ≃ₐ[k] K) (v : NK.GlobalCFT.Place K) :
    (Rep.resMap (decompK (k := k) v).subtype ((conjTwist σ).app (idelesRepP k K))) ≫
        (Rep.resMap (conjStabHom k K σ v)
          (NK.HassePrinciple.ideleToLocalUnits k K (σ • v)))
      = (NK.HassePrinciple.ideleToLocalUnits k K v) ≫ localUnitsConjHom σ v := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  exact localUnitsConj_square_apply_all σ v x

end ConjLocalUnits

/-- **Conjugation of the local-units coefficient maps.**

Let `σ : K ≃ₐ[k] K` be a Galois automorphism and `v` a place of `K`.  `conjStabHom k K σ v` is the
conjugation isomorphism `D_v →* D_{σ v}` between the decomposition groups
(`Submission/Work/SSGRoute/E9cConj.lean`), and `conjTwist σ` is the natural isomorphism
`X ⟶ Rep.res (MulAut.conj σ) X` given by `x ↦ σ • x` on a `Gal(K/k)`-module `X`.

The claim: there is a morphism of `D_v`-representations
`Θ : localUnitsK v ⟶ Rep.res (conjStabHom k K σ v) (localUnitsK (σ • v))` whose underlying map on
units is `NK.HassePrinciple.actVal σ v : (K_v)ˣ → (K_{σ v})ˣ`, making the square of `D_v`-modules
`res D_v 𝕀_K --resMap (conjTwist σ)--> res (MulAut.conj σ) 𝕀_K`,
`localUnitsK v --Θ--> res (conjStabHom σ v) (localUnitsK (σ • v))` commute with the two
evaluations `ι_v` and `resMap (conjStabHom σ v) ι_{σ v}`, where
`ι_w = NK.HassePrinciple.ideleToLocalUnits k K w` is evaluation at `w`.

Elementwise the square is `NK.HassePrinciple.smul_apply_smul_place`: the `(σ • v)`-component of
`σ • x` is `actVal σ v` applied to the `v`-component of `x`.  The linearity of `Θ` (i.e. its
intertwining with the `D_v`-actions `localUnitsEquiv`) reduces to the compatibility of
`Place.localRingEquiv σ v` with `localAut`: for `h ∈ D_v`, the square
`K_v --localAut v h--> K_v`, `K_{σ v} --localAut (σ v) (σ h σ⁻¹)--> K_{σ v}` commutes with
`Place.localRingEquiv σ v`; this follows from `NK.GlobalCFT.Galois.globalCFT_localRingEquiv_comp`
and can be checked on the dense image of `K` there. -/
theorem e9c_localUnits_conj {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K] (σ : K ≃ₐ[k] K)
    (v : NK.GlobalCFT.Place K) :
    ∃ Θ : SSGRoute.PTExt.localUnitsK (k := k) (K := K) v ⟶
        Rep.res (Work.SSGRoute.conjStabHom k K σ v)
          (SSGRoute.PTExt.localUnitsK (k := k) (K := K) (σ • v)),
      (∀ u : (NK.GlobalCFT.Place.localField K v)ˣ,
        (Additive.toMul (Θ (Additive.ofMul u)) : (NK.GlobalCFT.Place.localField K (σ • v))ˣ)
          = NK.HassePrinciple.actVal σ v u) ∧
      (Rep.resMap (SSGRoute.PTExt.decompK (k := k) v).subtype
          ((Work.SSGRoute.conjTwist σ).app (Work.SSGRoute.idelesRepP k K))) ≫
        (Rep.resMap (Work.SSGRoute.conjStabHom k K σ v)
          (NK.HassePrinciple.ideleToLocalUnits k K (σ • v)))
      = (NK.HassePrinciple.ideleToLocalUnits k K v) ≫ Θ := by
  refine ⟨localUnitsConjHom σ v, ?_, ?_⟩
  · intro u
    rfl
  · exact localUnitsConj_square σ v

end Work.SSGRoute
