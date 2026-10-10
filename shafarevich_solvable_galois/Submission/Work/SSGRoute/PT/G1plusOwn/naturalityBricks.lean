import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.PT.G1plusOwn.levelFree
import Submission.Work.SSGRoute.PTdualControl.g5Assembly
import Submission.Work.SSGRoute.local_duality_ext_detect_h
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Clause (5) of `G1⁺`'s finite half: the naturality *bricks*

Clause (5) of `H1Pair.PairClauses` (`hnat` of `G1⁺`) says, at `H = decomp k A`,

    g1FinHalf … M₂ (decomp k A) (fun σ => f (a σ)) b
      = g1FinHalf … M (decomp k A) a (fun σ => f' (b σ))

for an equivariant `f : M →ₗ M₂` and its transpose `f'` (`hff'`).

Unfolding `g1FinHalf` through `finAtValue_eq_finAtLevel` at a common admissible level, both sides are
`χ L hKL (ι_w (levelPair (finZF) (finZI) β [b]))`, and the identity is assembled from

* **(A) the dictionary's naturality** — `PT.finZB_natural` (node 0), which needs the coefficient
  morphism `F' : modRep (K ≃ₐ[k] K) (DualMod p (M₂ ⊗ T)) ⟶ modRep (K ≃ₐ[k] K) (DualMod p (M ⊗ T))`
  with `F'.hom = f'`.  This file *builds* `F'` from `(f', hff')`: the only input is the equivariance
  of `f'`, which follows from `hff'`, the equivariance `hf` of `f` and the fact that the action on
  `M ⊗ T` is the diagonal one (`Work.Shrinking.diagTensor_smul_tmul`; the same computation as
  `Work.SSGRoute.E7Fin.pairOfInv_natural`'s `hf'eq`);
* **(B) the level-class naturality** — `finZH_natural_coeff` below, which is the coefficient
  naturality of `finLevelClass` = the class of the factorised cocycle under
  `ExtH1.gammaHom`.  It is the remaining open brick; the delicate point is that `finLevelClass`
  builds its `↥(decompK w)`-action *locally* (`DistribMulAction.compHom`, which is not an instance),
  so `Work.SSGRoute.gammaHom_natural_coeff` has to be applied inside the unfolded definition rather
  than at the level of `finZH`;
* **(C) the Yoneda naturality** — `PT.levelPair_coeff_naturality` (proved), which moves `mk₀ π` from
  the `Ext¹`-slot to the `H¹`-slot.
-/

open scoped TensorProduct Pointwise
open SSGRoute.PTExt CategoryTheory

noncomputable section

namespace Work.SSGRoute.PT.G1pOwn

set_option maxHeartbeats 800000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
  (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]

/-- **The transpose of an equivariant map is equivariant.**  For `f : M →ₗ M₂` equivariant and
`f' : DualMod p (M₂ ⊗ T) →ₗ DualMod p (M ⊗ T)` with the transpose relation `hff'`, the map `f'`
commutes with the `Gal(K/k)`-action.  The proof is the pointwise computation: at a pure tensor
`e ⊗ t` both sides equal `φ (f (g⁻¹ • e) ⊗ (g⁻¹ • t))`, using the diagonal action on `M ⊗ T`
(`Work.Shrinking.diagTensor_smul_tmul`) and `DualMod.dualSMul_apply`. -/
theorem transpose_equivariant
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (M₂ : Type) [AddCommGroup M₂] [Module (ZMod p) M₂] [DistribMulAction (K ≃ₐ[k] K) M₂]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M₂]
    (f : M →ₗ[ZMod p] M₂) (hf : ∀ (g : K ≃ₐ[k] K) (e : M), f (g • e) = g • f e)
    (f' : DualMod p (M₂ ⊗[ZMod p] T) →ₗ[ZMod p] DualMod p (M ⊗[ZMod p] T))
    (hff' : ∀ (φ : DualMod p (M₂ ⊗[ZMod p] T)) (e : M) (t : T),
      f' φ (TensorProduct.tmul (ZMod p) e t) = φ (TensorProduct.tmul (ZMod p) (f e) t)) :
    ∀ (g : K ≃ₐ[k] K) (φ : DualMod p (M₂ ⊗[ZMod p] T)), f' (g • φ) = g • f' φ := by
  intro g φ
  apply TensorProduct.ext'
  intro e t
  show (f' (g • φ)) (TensorProduct.tmul (ZMod p) e t)
      = (g • f' φ) (TensorProduct.tmul (ZMod p) e t)
  rw [hff' (g • φ) e t, DualMod.dualSMul_apply]
  rw [Work.Shrinking.diagTensor_smul_tmul]
  rw [← hf g⁻¹ e]
  rw [← hff' φ (g⁻¹ • e) (g⁻¹ • t)]
  rw [← Work.Shrinking.diagTensor_smul_tmul]
  rw [← DualMod.dualSMul_apply]

/-- **The coefficient morphism attached to the transpose.**  From `(f, hf, f', hff')` one gets a
morphism of `Gal(K/k)`-representations `modRep … (DualMod p (M₂ ⊗ T)) ⟶ modRep … (DualMod p (M ⊗ T))`
whose underlying map is `f'` and whose transpose relation is `hff'` — the interface consumed by
`PT.finZB_natural`. -/
theorem exists_repMap_of_transpose
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (M₂ : Type) [AddCommGroup M₂] [Module (ZMod p) M₂] [DistribMulAction (K ≃ₐ[k] K) M₂]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M₂]
    (f : M →ₗ[ZMod p] M₂) (hf : ∀ (g : K ≃ₐ[k] K) (e : M), f (g • e) = g • f e)
    (f' : DualMod p (M₂ ⊗[ZMod p] T) →ₗ[ZMod p] DualMod p (M ⊗[ZMod p] T))
    (hff' : ∀ (φ : DualMod p (M₂ ⊗[ZMod p] T)) (e : M) (t : T),
      f' φ (TensorProduct.tmul (ZMod p) e t) = φ (TensorProduct.tmul (ZMod p) (f e) t)) :
    ∃ F' : modRep (K ≃ₐ[k] K) (DualMod p (M₂ ⊗[ZMod p] T)) ⟶
        modRep (K ≃ₐ[k] K) (DualMod p (M ⊗[ZMod p] T)),
      (∀ (φ : DualMod p (M₂ ⊗[ZMod p] T)), F'.hom φ = f' φ) ∧
      (∀ (φ : DualMod p (M₂ ⊗[ZMod p] T)) (e : M) (t : T),
        (show DualMod p (M ⊗[ZMod p] T) from F'.hom φ) (TensorProduct.tmul (ZMod p) e t)
          = φ (TensorProduct.tmul (ZMod p) (f e) t)) :=
  ⟨PTdualControl.modRepMap f' (transpose_equivariant p k Ω K T M M₂ f hf f' hff'),
   fun φ => PTdualControl.modRepMap_hom f' _ φ,
   fun φ e t => by
     rw [PTdualControl.modRepMap_hom]
     exact hff' φ e t⟩


/-- **Coefficient naturality of the level class `PT.levelClass`.**

At a fixed level `L` and place `A`, the level class of the factorised crossed homomorphism is
natural in the coefficient module: replacing the coefficient `DualMod p (M ⊗ T)` by
`DualMod p (M₂ ⊗ T)` along an equivariant `f'` is the same as post-composing the class with the
`Ext`-class of the induced morphism of representations.  This is
`Work.SSGRoute.ExtH1.gammaZ1_natural` (the cocycle-level form of
`Work.SSGRoute.gammaHom_natural_coeff`), transported from the `modRep ↥(decompK w)`-spelling of
`gammaZ1` to the `Rep.res`-spelling in which the level class is stated. -/
theorem levelClass_natural_coeff
    (L : IntermediateField k Ω) [FiniteDimensional k L] [IsGalois k L] (hKL : K ≤ L)
    [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K))
    (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L))
    (f : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite w)) →*
      ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)))
    (hf : ∀ σ : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite w)),
      ((f σ : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q))) : ↥K ≃ₐ[k] ↥K)
        = SSGRoute.PTExt.galRes k (↥K) (↥L) (σ : ↥L ≃ₐ[k] ↥L))
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (M₂ : Type) [AddCommGroup M₂] [Module (ZMod p) M₂] [DistribMulAction (K ≃ₐ[k] K) M₂]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M₂]
    (f' : DualMod p (M₂ ⊗[ZMod p] T) →ₗ[ZMod p] DualMod p (M ⊗[ZMod p] T))
    (hf' : ∀ (g : K ≃ₐ[k] K) (φ : DualMod p (M₂ ⊗[ZMod p] T)), f' (g • φ) = g • f' φ)
    (b₀ : (↥L ≃ₐ[k] ↥L) → DualMod p (M₂ ⊗[ZMod p] T))
    (h₁ : ∀ g h : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite w)),
      b₀ (↑(g * h) : ↥L ≃ₐ[k] ↥L) = b₀ (g : ↥L ≃ₐ[k] ↥L)
        + (SSGRoute.PTExt.galRes k (↥K) (↥L) (g : ↥L ≃ₐ[k] ↥L)) • b₀ (h : ↥L ≃ₐ[k] ↥L))
    (h₂ : ∀ g h : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite w)),
      (fun τ => f' (b₀ τ)) (↑(g * h) : ↥L ≃ₐ[k] ↥L) = (fun τ => f' (b₀ τ)) (g : ↥L ≃ₐ[k] ↥L)
        + (SSGRoute.PTExt.galRes k (↥K) (↥L) (g : ↥L ≃ₐ[k] ↥L)) • (fun τ => f' (b₀ τ))
            (h : ↥L ≃ₐ[k] ↥L)) :
    Work.SSGRoute.PT.levelClass p k Ω K L hKL q w f hf M T (fun τ => f' (b₀ τ)) h₂
      = (Work.SSGRoute.PT.levelClass p k Ω K L hKL q w f hf M₂ T b₀ h₁).comp
          (CategoryTheory.Abelian.Ext.mk₀
            (Rep.resMap f (Rep.resMap (SSGRoute.PTExt.decompK (k := k)
              (NK.GlobalCFT.Place.ofFinite q)).subtype (PTdualControl.modRepMap f' hf'))))
          (add_zero 1) := by
  classical
  -- the `Gal(K/k)`-commutation of the `ℤ`- and `Coeff`-actions (not Mathlib instances), as in
  -- `PT.finLevelClass`
  haveI hCommZ₂ : SMulCommClass (↥K ≃ₐ[k] ↥K) ℤ (DualMod p (M₂ ⊗[ZMod p] T)) :=
    ⟨fun g n m => map_zsmul (AddMonoidHom.mk' (fun m => g • m) (fun a b => smul_add g a b)) n m⟩
  haveI hCommC₂ : SMulCommClass (↥K ≃ₐ[k] ↥K) Coeff (DualMod p (M₂ ⊗[ZMod p] T)) :=
    ⟨fun g c m => smul_comm g c.down m⟩
  haveI hCommZ₁ : SMulCommClass (↥K ≃ₐ[k] ↥K) ℤ (DualMod p (M ⊗[ZMod p] T)) :=
    ⟨fun g n m => map_zsmul (AddMonoidHom.mk' (fun m => g • m) (fun a b => smul_add g a b)) n m⟩
  haveI hCommC₁ : SMulCommClass (↥K ≃ₐ[k] ↥K) Coeff (DualMod p (M ⊗[ZMod p] T)) :=
    ⟨fun g c m => smul_comm g c.down m⟩
  -- the `D_w`-action on the two coefficients, pulled back along the place glue, and its
  -- `ℤ`/`Coeff`-commutation
  let φ₀ : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite w)) →*
      (↥K ≃ₐ[k] ↥K) :=
    (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype.comp f
  letI hAct₂ : DistribMulAction ↥(SSGRoute.PTExt.decompK (k := k)
      (NK.GlobalCFT.Place.ofFinite w)) (DualMod p (M₂ ⊗[ZMod p] T)) :=
    DistribMulAction.compHom _ φ₀
  letI hAct₁ : DistribMulAction ↥(SSGRoute.PTExt.decompK (k := k)
      (NK.GlobalCFT.Place.ofFinite w)) (DualMod p (M ⊗[ZMod p] T)) :=
    DistribMulAction.compHom _ φ₀
  haveI hCommZp₂ : SMulCommClass ↥(SSGRoute.PTExt.decompK (k := k)
      (NK.GlobalCFT.Place.ofFinite w)) (ZMod p) (DualMod p (M₂ ⊗[ZMod p] T)) :=
    ⟨fun g c m => smul_comm (φ₀ g) c m⟩
  haveI hCommCp₂ : SMulCommClass ↥(SSGRoute.PTExt.decompK (k := k)
      (NK.GlobalCFT.Place.ofFinite w)) Coeff (DualMod p (M₂ ⊗[ZMod p] T)) :=
    ⟨fun g c m => smul_comm (φ₀ g) c m⟩
  haveI hCommZp₁ : SMulCommClass ↥(SSGRoute.PTExt.decompK (k := k)
      (NK.GlobalCFT.Place.ofFinite w)) (ZMod p) (DualMod p (M ⊗[ZMod p] T)) :=
    ⟨fun g c m => smul_comm (φ₀ g) c m⟩
  haveI hCommCp₁ : SMulCommClass ↥(SSGRoute.PTExt.decompK (k := k)
      (NK.GlobalCFT.Place.ofFinite w)) Coeff (DualMod p (M ⊗[ZMod p] T)) :=
    ⟨fun g c m => smul_comm (φ₀ g) c m⟩
  have hf'Dw : ∀ (g : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite w)))
      (φ : DualMod p (M₂ ⊗[ZMod p] T)), f' (g • φ) = g • f' φ := by
    intro g φ
    exact hf' (φ₀ g) φ
  -- the crossed-homomorphism membership of `b₀|D_w`
  have hmem : (fun g : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite w)) =>
      b₀ (g : ↥L ≃ₐ[k] ↥L)) ∈
      Work.GroupCohomology.Z1 ↥(SSGRoute.PTExt.decompK (k := k)
        (NK.GlobalCFT.Place.ofFinite w)) (DualMod p (M₂ ⊗[ZMod p] T)) := by
    rw [Work.GroupCohomology.mem_Z1_iff]
    intro g h
    show b₀ (↑(g * h) : ↥L ≃ₐ[k] ↥L)
      = ((f g : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q))) :
          ↥K ≃ₐ[k] ↥K) • b₀ (h : ↥L ≃ₐ[k] ↥L) + b₀ (g : ↥L ≃ₐ[k] ↥L)
    rw [h₁ g h, add_comm, hf g]
  -- unfold both level classes to `gammaZ1` and apply the cocycle-level naturality
  simp only [Work.SSGRoute.PT.levelClass]
  exact Work.SSGRoute.ExtH1.gammaZ1_natural
    (G := ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite w)))
    (M := DualMod p (M₂ ⊗[ZMod p] T)) (N := DualMod p (M ⊗[ZMod p] T))
    (Work.SSGRoute.augSES_shortExact _) f'.toAddMonoidHom hf'Dw
    (PTdualControl.modRepMap f' hf'Dw) (fun m => PTdualControl.modRepMap_hom f' hf'Dw m)
    ⟨fun g => b₀ (g : ↥L ≃ₐ[k] ↥L), hmem⟩


/-- **Coefficient naturality of the level class `PT.finZH`.**

`finZH … b hb b₀ hb₀` is the class of the factorisation `b₀` of `b|_H` through `Gal(L/k)`
(`PT.finLevelClass`, i.e. the transported `ExtH1.gammaHom (H1π b₀)`).  Naturality in the
coefficient module is the naturality of `PT.levelClass` along the coefficient morphism induced by
`f'`, transported through the `finLevelClass`/`levelClass` identification (the `Rep`-transport in
`finLevelClass` is along a definitional equality — the same computation as `finLevelClass_add`). -/
theorem finZH_natural_coeff
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (M₂ : Type) [AddCommGroup M₂] [Module (ZMod p) M₂] [DistribMulAction (K ≃ₐ[k] K) M₂]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M₂] [Finite M₂]
    (f' : DualMod p (M₂ ⊗[ZMod p] T) →ₗ[ZMod p] DualMod p (M ⊗[ZMod p] T))
    (hf' : ∀ (g : K ≃ₐ[k] K) (φ : DualMod p (M₂ ⊗[ZMod p] T)), f' (g • φ) = g • f' φ)
    (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
    (hKL : K ≤ L) [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (b : (Ω ≃ₐ[k] Ω) → DualMod p (M₂ ⊗[ZMod p] T))
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b)
    (b₀ : (↥L ≃ₐ[k] ↥L) → DualMod p (M₂ ⊗[ZMod p] T))
    (hb₀ : ∀ σ ∈ SSGRoute.decomp k A, b σ = b₀ (AlgEquiv.restrictNormalHom L σ))
    (hb' : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A)
      (fun σ => f' (b σ)))
    (hb₀' : ∀ σ ∈ SSGRoute.decomp k A,
      f' (b σ) = f' (b₀ (AlgEquiv.restrictNormalHom L σ))) :
    finZH p K T M L hKL A hA (fun σ => f' (b σ)) hb' (fun τ => f' (b₀ τ)) hb₀'
      = (finZH p K T M₂ L hKL A hA b hb b₀ hb₀).comp
          (CategoryTheory.Abelian.Ext.mk₀ (Rep.resMap (finZF hKL A hA)
            (Rep.resMap (SSGRoute.PTExt.decompK (k := k)
              (NK.GlobalCFT.Place.ofFinite (finQ K A hA))).subtype
              (PTdualControl.modRepMap f' hf'))))
          (add_zero 1) := by
  classical
  let hcr₂ := factorised_isCrossedHom p k Ω K L hKL A hA (finQ K A hA)
    (fun x => finQ_spec K A hA x) (finQW L A hA) (fun y => finQW_spec L A hA y)
    (finQW_glue L A hA) (DualMod p (M ⊗[ZMod p] T)) (fun σ => f' (b σ)) hb'
    (fun τ => f' (b₀ τ)) hb₀'
  let hcr₁ := factorised_isCrossedHom p k Ω K L hKL A hA (finQ K A hA)
    (fun x => finQ_spec K A hA x) (finQW L A hA) (fun y => finQW_spec L A hA y)
    (finQW_glue L A hA) (DualMod p (M₂ ⊗[ZMod p] T)) b hb b₀ hb₀
  have e1 : finZH p K T M L hKL A hA (fun σ => f' (b σ)) hb' (fun τ => f' (b₀ τ)) hb₀'
      = Work.SSGRoute.PT.levelClass p k Ω K L hKL (finQ K A hA) (finQW L A hA)
          (finZF hKL A hA) (finZF_spec hKL A hA) M T (fun τ => f' (b₀ τ)) hcr₂ := by
    simp only [finZH, finLevelClass, Work.SSGRoute.PT.levelClass]
    rw [Work.SSGRoute.ExtH1.gammaHom_H1π]
  have e2 : finZH p K T M₂ L hKL A hA b hb b₀ hb₀
      = Work.SSGRoute.PT.levelClass p k Ω K L hKL (finQ K A hA) (finQW L A hA)
          (finZF hKL A hA) (finZF_spec hKL A hA) M₂ T b₀ hcr₁ := by
    simp only [finZH, finLevelClass, Work.SSGRoute.PT.levelClass]
    rw [Work.SSGRoute.ExtH1.gammaHom_H1π]
  rw [e1, e2]
  exact levelClass_natural_coeff p k Ω K T L hKL (finQ K A hA) (finQW L A hA) (finZF hKL A hA)
    (finZF_spec hKL A hA) M M₂ f' hf' b₀ hcr₁ hcr₂


/-- **Clause (5) of `G1⁺`'s finite half** (`hnat` of the target file): naturality of `g1FinHalf` in
the coefficient module.

Assembled from `PT.finZB_natural` (first variable, node 0), `PT.levelPair_coeff_naturality`
(moving `mk₀ π` from the `Ext¹`-slot to the `H¹`-slot), `finZH_natural_coeff` (second variable) and
`finAtValue_eq_finAtLevel` (whose `hχ` relocates both values to the common admissible level
produced by `PT.exists_level_factors_locConstOnTwo` for `b` and `f' ∘ b`). -/
theorem g1FinHalf_natural
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (χ : ChiK p k Ω K T)
    (hχ : ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
        (hKL : K ≤ L) (L' : IntermediateField k Ω) [NumberField L']
        [FiniteDimensional k L'] [IsGalois k L'] (hKL' : K ≤ L') (hLL : L ≤ L')
        (u : extH (classesK k L) 2),
        p • u = 0 → χ L' hKL' (inflLevel L L' hLL u) = χ L hKL u)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (M₂ : Type) [AddCommGroup M₂] [Module (ZMod p) M₂] [DistribMulAction (K ≃ₐ[k] K) M₂]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M₂] [Finite M₂]
    (f : M →ₗ[ZMod p] M₂) (hf : ∀ (g : K ≃ₐ[k] K) (e : M), f (g • e) = g • f e)
    (f' : DualMod p (M₂ ⊗[ZMod p] T) →ₗ[ZMod p] DualMod p (M ⊗[ZMod p] T))
    (hff' : ∀ (φ : DualMod p (M₂ ⊗[ZMod p] T)) (e : M) (t : T),
      f' φ (TensorProduct.tmul (ZMod p) e t) = φ (TensorProduct.tmul (ZMod p) (f e) t))
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (a : (Ω ≃ₐ[k] Ω) → M) (b : (Ω ≃ₐ[k] Ω) → DualMod p (M₂ ⊗[ZMod p] T))
    (ha : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) a ∧
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a)
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b ∧
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b) :
    g1FinHalf p k Ω K ζ hζ hζK T hT χ M₂ (SSGRoute.decomp k A) (fun σ => f (a σ)) b
      = g1FinHalf p k Ω K ζ hζ hζK T hT χ M (SSGRoute.decomp k A) a (fun σ => f' (b σ)) := by
  classical
  have hf'eq := transpose_equivariant p k Ω K T M M₂ f hf f' hff'
  -- cocycle/loc-constancy of the two transformed data
  have hfac : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) (fun σ => f (a σ)) := by
    intro g hg h hh
    show f (a (g * h)) = f (a g) + SSGRoute.res k K g • f (a h)
    rw [ha.1 g hg h hh, map_add, hf]
  have hfac_l : SSGRoute.IsLocConstOn (SSGRoute.decomp k A) (fun σ => f (a σ)) := by
    obtain ⟨U, hU, hfU⟩ := ha.2
    exact ⟨U, hU, fun g hg u hu huH => by
      show f (a (g * u)) = f (a g)
      rw [hfU g hg u hu huH]⟩
  have hfbc : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A)
      (fun σ => f' (b σ)) := by
    intro g hg h hh
    show f' (b (g * h)) = f' (b g) + SSGRoute.res k K g • f' (b h)
    rw [hb.1 g hg h hh, map_add, hf'eq]
  have hfbc_l : SSGRoute.IsLocConstOn (SSGRoute.decomp k A) (fun σ => f' (b σ)) := by
    obtain ⟨U, hU, hfU⟩ := hb.2
    exact ⟨U, hU, fun g hg u hu huH => by
      show f' (b (g * u)) = f' (b g)
      rw [hfU g hg u hu huH]⟩
  -- the guard witness
  let hw : ∃ A' : ValuationSubring Ω, SSGRoute.IsFinPlace k A' ∧
      SSGRoute.decomp k A = SSGRoute.decomp k A' := ⟨A, hA, rfl⟩
  rw [g1FinHalf_eq_of_guard p k Ω K ζ hζ hζK T hT χ M₂ (SSGRoute.decomp k A)
        (fun σ => f (a σ)) b hw ⟨hfac_l, hb.2⟩,
      g1FinHalf_eq_of_guard p k Ω K ζ hζ hζK T hT χ M (SSGRoute.decomp k A)
        a (fun σ => f' (b σ)) hw ⟨ha.2, hfbc_l⟩]
  -- a common admissible level for `b` and `f' ∘ b`
  obtain ⟨L, hLfin, hLnorm, hKL, b₀, b₀', hb₀, hb₀'⟩ :=
    exists_level_factors_locConstOnTwo k Ω K (SSGRoute.decomp k hw.choose) b (fun σ => f' (b σ))
      (hw.choose_spec.2 ▸ hb.2) (hw.choose_spec.2 ▸ hfbc_l)
  letI : FiniteDimensional k L := hLfin
  letI : Normal k L := hLnorm
  letI : IsGalois k L := inferInstance
  letI : NumberField L := inferInstance
  letI : Algebra ↥K ↥L := (IntermediateField.inclusion hKL).toAlgebra
  haveI : IsScalarTower k ↥K ↥L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower ↥K ↥L Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  -- the correct factorisation of `f' ∘ b` through `f' ∘ b₀`
  have hb₀f' : ∀ σ ∈ SSGRoute.decomp k hw.choose,
      f' (b σ) = f' (b₀ (AlgEquiv.restrictNormalHom L σ)) := by
    intro σ hσ
    rw [hb₀ σ hσ]
  -- rewrite both values at the level `L` and unfold
  rw [finAtValue_eq_finAtLevel p k Ω K ζ hζ hζK T hT χ hχ M₂ hw.choose hw.choose_spec.1
        (fun σ => f (a σ)) b (hw.choose_spec.2 ▸ hfac_l) (hw.choose_spec.2 ▸ hb.2)
        (hw.choose_spec.2 ▸ hb.1) L hKL b₀ hb₀,
      finAtValue_eq_finAtLevel p k Ω K ζ hζ hζK T hT χ hχ M hw.choose hw.choose_spec.1
        a (fun σ => f' (b σ)) (hw.choose_spec.2 ▸ ha.2) (hw.choose_spec.2 ▸ hfbc_l)
        (hw.choose_spec.2 ▸ hfbc) L hKL (fun τ => f' (b₀ τ)) hb₀f']
  simp only [finAtLevel, finZZ]
  -- the three naturalities
  rw [finZB_natural p k Ω K ζ hζ hζK T hT M hw.choose hw.choose_spec.1 M₂ f hf
        (PTdualControl.modRepMap f' hf'eq)
        (fun φ e t => by rw [PTdualControl.modRepMap_hom]; exact hff' φ e t)
        a (hw.choose_spec.2 ▸ ha.1) (hw.choose_spec.2 ▸ ha.2),
      levelPair_coeff_naturality (f := finZF hKL hw.choose hw.choose_spec.1)
        (ι := finZI hKL hw.choose hw.choose_spec.1)
        (π := Rep.resMap (SSGRoute.PTExt.decompK (k := k)
          (NK.GlobalCFT.Place.ofFinite (finQ K hw.choose hw.choose_spec.1))).subtype
          (PTdualControl.modRepMap f' hf'eq))
        (y := finZB p K ζ hζ hζK T hT M hw.choose hw.choose_spec.1 a)
        (h := finZH p K T M₂ L hKL hw.choose hw.choose_spec.1 b
          (hw.choose_spec.2 ▸ hb.1) b₀ hb₀)]
  -- the second-variable naturality, in the `b₀'` spelling
  rw [← finZH_natural_coeff p k Ω K T M M₂ f' hf'eq L hKL hw.choose hw.choose_spec.1
        b (hw.choose_spec.2 ▸ hb.1) b₀ hb₀ (hw.choose_spec.2 ▸ hfbc) hb₀f']

end Work.SSGRoute.PT.G1pOwn
