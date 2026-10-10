import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Submission.Work.SSGRoute.PTDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PT

open CategoryTheory SSGRoute.PTExt

attribute [local instance 10000] Rep.hV2 Rep.hV1 Submodule.module
set_option backward.isDefEq.respectTransparency false

/-- **The `𝔽_p`-decomposition data of a trivial finite `ZMod p`-module `V` at a level.**  Let `w` be
an infinite place of `K` and `u | w` a place of `L`, and suppose the decomposition group `D_w` acts
trivially on `V` (`htriv`).  Then the `D_w`-module
`X := Rep.res (decompK w).subtype (modRep (↥K ≃ₐ[k] ↥K) V)` admits `n : ℕ`,
`he : Fin n → (P ⟶ X)`, `pr : Fin n → (X ⟶ P)` with `∑ i, pr i ≫ he i = 𝟙 X`, where
`P := Rep.trivial Coeff ↥(decompK (k := k) w) (ZMod p)` is the trivial `𝔽_p`-module.

Construction (both reviewers elaborated the statement and confirmed it; the working preamble in a
file with this instance list is `open CategoryTheory SSGRoute.PTExt` +
`attribute [local instance 10000] Rep.hV2 Rep.hV1 Submodule.module` +
`set_option backward.isDefEq.respectTransparency false`): `V` is a finite `ZMod p`-module, so it has
a `ZMod p`-basis `b : Fin n → V` (`Module.finBasis`); `he i` is the `Rep`-map `𝔽_p ⟶ V`,
`t ↦ t • b i` (`Coeff`-linear and `D_w`-equivariant because the action on `V` is trivial by `htriv`,
together with `SMulCommClass Gal (ZMod p) V`), and `pr i` is the `i`-th coordinate functional
`V ⟶ 𝔽_p` with respect to `b`; the identity is pointwise `∑ i, (coordinate i of v) • b i = v`.  Only
the one-sided identity `∑ pr ≫ he = 𝟙` is needed. -/
theorem archLevelPair_decomposition (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K L : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [FiniteDimensional k L] [IsGalois k L] [NumberField ↥L]
    [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω]
    (V : Type) [AddCommGroup V] [Module (ZMod p) V] [DistribMulAction (↥K ≃ₐ[k] ↥K) V]
    [SMulCommClass (↥K ≃ₐ[k] ↥K) (ZMod p) V] [Finite V]
    (w : NK.GlobalCFT.Place ↥K)
    (hw : ∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K),
      w ≠ NK.GlobalCFT.Place.ofFinite q)
    (u : NK.GlobalCFT.Place ↥L) (hu : NK.GlobalCFT.Place.LiesOver u w)
    (htriv : ∀ (σ : ↥K ≃ₐ[k] ↥K), σ ∈ SSGRoute.PTExt.decompK (k := k) w →
      ∀ v : V, σ • v = v) :
    ∃ (n : ℕ)
      (he : Fin n → (Rep.trivial Coeff ↥(SSGRoute.PTExt.decompK (k := k) w) (ZMod p) ⟶
        Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype
          (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) V)))
      (pr : Fin n → (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype
          (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) V) ⟶
        Rep.trivial Coeff ↥(SSGRoute.PTExt.decompK (k := k) w) (ZMod p))),
      (∑ i : Fin n, pr i ≫ he i)
        = 𝟙 (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype
            (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) V)) := by
  classical
  -- Put the module into the `Rep.of` form: this makes the underlying type of the `Rep`-object
  -- syntactically reducible to `V`, which is what keeps the pointwise computation transparent.
  have hmod : (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) V)
      = Rep.of (Representation.ofDistribMulAction Coeff (↥K ≃ₐ[k] ↥K) V) := rfl
  rw [hmod]
  -- `V` is a finite `ZMod p`-module, hence free of finite rank over the field `ZMod p`.
  have hfin : Module.Finite (ZMod p) V := Module.finite_iff_finite.mpr inferInstance
  let n := Module.finrank (ZMod p) V
  let b : Module.Basis (Fin n) (ZMod p) V := Module.finBasis (ZMod p) V
  -- Pointwise form of the two equivariance conditions (the action on `V` is trivial by `htriv`).
  have h1 : ∀ (i : Fin n) (g : ↥(SSGRoute.PTExt.decompK (k := k) w)) (t : ZMod p),
      t • b i = (g : ↥K ≃ₐ[k] ↥K) • (t • b i) := by
    intro i g t
    rw [smul_comm (g : ↥K ≃ₐ[k] ↥K) t (b i), htriv (g : ↥K ≃ₐ[k] ↥K) g.2 (b i)]
  have h2 : ∀ (i : Fin n) (g : ↥(SSGRoute.PTExt.decompK (k := k) w)) (v : V),
      (b.coord i) ((g : ↥K ≃ₐ[k] ↥K) • v) = (b.coord i) v := by
    intro i g v
    rw [htriv (g : ↥K ≃ₐ[k] ↥K) g.2 v]
  -- The `i`-th inclusion `𝔽_p → V`, `t ↦ t • b i`, as a `Coeff`-linear map.
  let linH : Fin n → (ZMod p →ₗ[Coeff] V) := fun i =>
    { toFun := fun t => t • b i
      map_add' := fun s t => add_smul s t (b i)
      map_smul' := fun c t => smul_assoc c t (b i) }
  -- The `i`-th coordinate functional `V → 𝔽_p` with respect to the basis `b`.
  let linP : Fin n → (V →ₗ[Coeff] ZMod p) := fun i =>
    { toFun := fun v => b.coord i v
      map_add' := fun x y => (b.coord i).map_add x y
      map_smul' := fun c v => by simp only [ULift.smul_def, RingHom.id_apply]; simp [map_zsmul] }
  let heF : Fin n → (Rep.trivial Coeff ↥(SSGRoute.PTExt.decompK (k := k) w) (ZMod p) ⟶
      Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype
        (Rep.of (Representation.ofDistribMulAction Coeff (↥K ≃ₐ[k] ↥K) V))) := fun i =>
    Rep.ofHom
      { toLinearMap := linH i
        isIntertwining' := by
          intro g
          apply LinearMap.ext
          intro t
          simp only [LinearMap.comp_apply, MonoidHom.comp_apply,
            Representation.ofDistribMulAction_apply_apply, Representation.trivial_apply,
            LinearMap.coe_mk, AddHom.coe_mk, linH]
          exact h1 i g t }
  let prF : Fin n → (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype
        (Rep.of (Representation.ofDistribMulAction Coeff (↥K ≃ₐ[k] ↥K) V)) ⟶
      Rep.trivial Coeff ↥(SSGRoute.PTExt.decompK (k := k) w) (ZMod p)) := fun i =>
    Rep.ofHom
      { toLinearMap := linP i
        isIntertwining' := by
          intro g
          apply LinearMap.ext
          intro v
          simp only [LinearMap.comp_apply, MonoidHom.comp_apply,
            Representation.ofDistribMulAction_apply_apply, Representation.trivial_apply,
            LinearMap.coe_mk, AddHom.coe_mk, linP]
          exact h2 i g v }
  refine ⟨n, heF, prF, ?_⟩
  -- The identity `∑ i, pr i ≫ he i = 𝟙` is pointwise `∑ i, (coord i of v) • b i = v`.
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro v
  simp only [Rep.sum_hom]
  rw [Representation.IntertwiningMap.toLinearMap_sum, LinearMap.sum_apply]
  simp only [Rep.hom_comp, Rep.hom_id, heF, prF, linH, linP, LinearMap.coe_mk, AddHom.coe_mk,
    LinearMap.comp_apply, Representation.IntertwiningMap.id_apply]
  simp only [Representation.IntertwiningMap.comp_toLinearMap, LinearMap.comp_apply,
    Representation.IntertwiningMap.toLinearMap_id, LinearMap.id_coe, id_eq,
    Representation.IntertwiningMap.toLinearMap_apply, LinearMap.coe_mk, AddHom.coe_mk]
  simp only [Rep.hom_ofHom, Representation.IntertwiningMap.coe_mk,
    Representation.IntertwiningMap.toLinearMap_mk, LinearMap.coe_mk, AddHom.coe_mk]
  simpa [Module.Basis.coord_apply] using b.sum_repr v

end Work.SSGRoute.PT
