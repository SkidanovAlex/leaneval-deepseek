import Mathlib.GroupTheory.Nilpotent
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.ZMod
import Mathlib.LinearAlgebra.PerfectPairing.Basic
import Submission.Work.CohomologicalShrinking.shiftH2Family
import Submission.Work.SSGRoute.TateDual.NatPrep
import Submission.Work.SSGRoute.TateDual.pairQ_isPerfPair
import Submission.Work.SSGRoute.TateDual.pairQ_natural
import Submission.Work.SSGRoute.tateDuality_hm2_dual
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Naturality of the degree `-2` Tate duality `Ĥ⁻²(G, M^∨) ≅ H¹(G, M)^∨`

The isomorphism of `Work.SSGRoute.tateDuality_hm2_dual` is assembled from the degree-`0`
duality pairing (`Work.SSGRoute.TateDual.tateDuality_degree_zero`), the duality of the shift
sequence (`dual_coindUp_coindShift`) and the dimension shift `H¹ ≅ Ĥ⁰` of the shift.  Here the
*same* chain is assembled out of the **canonical** maps, so that every stage is natural in the
coefficient and the resulting family

`dualE p G M : Ĥ⁻²(G, M^∨) ≃+ H¹(G, M)^∨`

is natural in `M`: for `f : M → M₂` `G`-equivariant, the square

`Ĥ⁻²(G, M₂^∨) --dualE_{M₂}--> H¹(G, M₂)^∨`
`     | Hm2Map f^∨                       | (·) ∘ mapH1 f`
`Ĥ⁻²(G, M^∨)  --dualE_M ---->  H¹(G, M)^∨`

commutes (`dualE_natural`).

The three stages, each proved natural separately:

* `tateDualHm1Iso p G A : Ĥ⁻¹(G, A) ≃+ (Ĥ⁰(G, A^∨))^∨`, the degree-`0` evaluation pairing,
  natural in `A` (`tateDualHm1Iso_natural`, from `TateDual.pairQ_natural`);
* `tateDualH0Iso p G M : Ĥ⁰(G, (coindUp G (M^∨))^∨) ≃+ Ĥ⁰(G, coindShift G M)`, induced by the
  canonical shift pairing `TateDual.shiftDual` (natural in `M` by `TateDual.shiftDual_natural`);
* `Work.Tate.dimensionShiftH1H0Symm G M : Ĥ⁰(G, coindShift G M) ≃+ H¹(G, M)`, the connecting
  map of the shift sequence (natural in `M` by
  `Work.CohomologicalShrinking.tate.dimensionShiftH1H0_natural`).
-/

namespace Work.SSGRoute

open scoped BigOperators

variable (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [Fintype G]

/-- Forgetting linearity, as an additive equivalence `(X →ₗ 𝔽_p) ≃+ (X →+ 𝔽_p)`. -/
noncomputable def linToAddEquiv (X : Type) [AddCommGroup X] [Module (ZMod p) X] :
    (X →ₗ[ZMod p] ZMod p) ≃+ (X →+ ZMod p) where
  toFun φ := φ.toAddMonoidHom
  invFun ψ := ψ.toZModLinearMap p
  left_inv ψ := by ext x; rfl
  right_inv φ := by ext x; rfl
  map_add' φ ψ := by ext x; rfl

/-! ## The induced map on the `I_G`-twists of the duals -/

/-- The map `coindUp G (M₂^∨) →ₗ coindUp G (M^∨)` induced by a `G`-equivariant
`f : M → M₂` (the transpose of `f` on the dual coefficients, transported to the `I_G`-twists).
This is the map whose induced map on `Ĥ⁻¹` is `Work.Tate.Hm2Map f.dualMap`. -/
noncomputable def dualCoindUpMapLin
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction G M]
    [SMulCommClass G (ZMod p) M]
    (M₂ : Type) [AddCommGroup M₂] [Module (ZMod p) M₂] [DistribMulAction G M₂]
    [SMulCommClass G (ZMod p) M₂]
    (f : M →ₗ[ZMod p] M₂) (hf : ∀ (g : G) (m : M), f (g • m) = g • f m) :
    ↥(Work.Tate.coindUp G (DualMod p M₂)) →ₗ[ZMod p]
      ↥(Work.Tate.coindUp G (DualMod p M)) :=
  TateDual.coindUpMapLin p G f.dualMap
    (fun g z => by
      show f.dualMap (g • z) = g • f.dualMap z
      ext m
      simp only [LinearMap.dualMap_apply, DualMod.dualSMul_apply, hf])

/-- `dualCoindUpMapLin` is `G`-equivariant. -/
theorem dualCoindUpMapLin_equiv
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction G M]
    [SMulCommClass G (ZMod p) M]
    (M₂ : Type) [AddCommGroup M₂] [Module (ZMod p) M₂] [DistribMulAction G M₂]
    [SMulCommClass G (ZMod p) M₂]
    (f : M →ₗ[ZMod p] M₂) (hf : ∀ (g : G) (m : M), f (g • m) = g • f m)
    (γ : G) (x : ↥(Work.Tate.coindUp G (DualMod p M₂))) :
    dualCoindUpMapLin p G M M₂ f hf (γ • x) = γ • dualCoindUpMapLin p G M M₂ f hf x := by
  apply Subtype.ext
  funext γ'
  simp only [dualCoindUpMapLin, TateDual.coindUpMapLin_apply, Work.Tate.coe_smul_coindUp,
    Work.Tate.coind_smul_eq]

/-! ## Stage 1: the degree-`0` evaluation pairing -/

/-- **The degree-`0` Tate duality**, as an isomorphism: the evaluation pairing
`Ĥ⁻¹(G, A) × Ĥ⁰(G, A^∨) → 𝔽_p` is perfect (`TateDual.pairQ_isPerfPair`). -/
noncomputable def tateDualHm1Iso (A : Type) [AddCommGroup A] [Module (ZMod p) A]
    [DistribMulAction G A] [SMulCommClass G (ZMod p) A] [FiniteDimensional (ZMod p) A] :
    Work.Tate.Hm1 G A ≃+ (Work.Tate.H0 G (DualMod p A) →+ ZMod p) := by
  haveI := TateDual.pairQ_isPerfPair p G A
  exact ((LinearMap.toPerfPair (TateDual.pairQ p G A)).toAddEquiv).trans
    (linToAddEquiv p (↥(TateDual.fixSub p G A) ⧸ TateDual.V0 p G A))

theorem tateDualHm1Iso_apply (A : Type) [AddCommGroup A] [Module (ZMod p) A]
    [DistribMulAction G A] [SMulCommClass G (ZMod p) A] [FiniteDimensional (ZMod p) A]
    (x : Work.Tate.Hm1 G A) (φ : Work.Tate.H0 G (DualMod p A)) :
    tateDualHm1Iso p G A x φ = TateDual.pairQ p G A x φ := by
  simp only [tateDualHm1Iso, LinearMap.toPerfPair_apply, linToAddEquiv]
  rfl

/-- Naturality of the degree-`0` Tate duality in the coefficient. -/
theorem tateDualHm1Iso_natural (A : Type) [AddCommGroup A] [Module (ZMod p) A]
    [DistribMulAction G A] [SMulCommClass G (ZMod p) A] [FiniteDimensional (ZMod p) A]
    (B : Type) [AddCommGroup B] [Module (ZMod p) B] [DistribMulAction G B]
    [SMulCommClass G (ZMod p) B] [FiniteDimensional (ZMod p) B]
    (u : A →ₗ[ZMod p] B) (hu : ∀ (g : G) (a : A), u (g • a) = g • u a)
    (x : Work.Tate.Hm1 G A) (φ : Work.Tate.H0 G (DualMod p B)) :
    tateDualHm1Iso p G B (Work.Tate.Hm1Map G A B u.toAddMonoidHom hu x) φ
      = tateDualHm1Iso p G A x
          (Work.Tate.H0Map G (DualMod p B) (DualMod p A) u.dualMap.toAddMonoidHom
            (TateDual.dualMap_equiv_of p G u hu) φ) := by
  rw [tateDualHm1Iso_apply, tateDualHm1Iso_apply]
  exact TateDual.pairQ_natural p G A B u hu (TateDual.dualMap_equiv_of p G u hu) x φ

/-! ## Stage 2: the shift pairing -/

/-- The canonical shift pairing `Coind(M)/M ≃+ Dual(coindUp G (M^∨))`, bundled. -/
noncomputable def shiftDualEquiv (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction G M] [SMulCommClass G (ZMod p) M] [Finite M] :
    Work.Tate.coindShift G M ≃+ DualMod p ↥(Work.Tate.coindUp G (DualMod p M)) :=
  AddEquiv.ofBijective (TateDual.shiftDual p G M).toAddMonoidHom
    (TateDual.shiftDual_bijective p G M)

theorem shiftDualEquiv_apply (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction G M] [SMulCommClass G (ZMod p) M] [Finite M]
    (y : Work.Tate.coindShift G M) :
    shiftDualEquiv p G M y = TateDual.shiftDual p G M y := rfl

theorem shiftDualEquiv_equiv (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction G M] [SMulCommClass G (ZMod p) M] [Finite M]
    (γ : G) (y : Work.Tate.coindShift G M) :
    shiftDualEquiv p G M (γ • y) = γ • shiftDualEquiv p G M y := by
  rw [shiftDualEquiv_apply, shiftDualEquiv_apply]
  exact TateDual.shiftDual_equiv p G M γ y

theorem shiftDualEquiv_symm_equiv (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction G M] [SMulCommClass G (ZMod p) M] [Finite M]
    (γ : G) (z : DualMod p ↥(Work.Tate.coindUp G (DualMod p M))) :
    (shiftDualEquiv p G M).symm (γ • z) = γ • (shiftDualEquiv p G M).symm z := by
  have h := shiftDualEquiv_equiv p G M γ ((shiftDualEquiv p G M).symm z)
  simp only [AddEquiv.apply_symm_apply] at h
  exact (shiftDualEquiv p G M).injective (by rw [AddEquiv.apply_symm_apply, h])

/-- Naturality of the canonical shift pairing, as an identity of additive homomorphisms. -/
theorem shiftDualEquiv_natural
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction G M]
    [SMulCommClass G (ZMod p) M] [Finite M]
    (M₂ : Type) [AddCommGroup M₂] [Module (ZMod p) M₂] [DistribMulAction G M₂]
    [SMulCommClass G (ZMod p) M₂] [Finite M₂]
    (f : M →ₗ[ZMod p] M₂) (hf : ∀ (g : G) (m : M), f (g • m) = g • f m) :
    (shiftDualEquiv p G M₂).toAddMonoidHom.comp
        (Work.CohomologicalShrinking.coindShiftMap f.toAddMonoidHom hf)
      = (LinearMap.dualMap (dualCoindUpMapLin p G M M₂ f hf)).toAddMonoidHom.comp
          (shiftDualEquiv p G M).toAddMonoidHom := by
  apply AddMonoidHom.ext
  intro y
  rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply]
  show shiftDualEquiv p G M₂
      (Work.CohomologicalShrinking.coindShiftMap f.toAddMonoidHom hf y)
    = (LinearMap.dualMap (dualCoindUpMapLin p G M M₂ f hf)) (shiftDualEquiv p G M y)
  rw [shiftDualEquiv_apply, shiftDualEquiv_apply]
  exact TateDual.shiftDual_natural p G M M₂ f hf
    (Work.CohomologicalShrinking.coindShiftMap f.toAddMonoidHom hf)
    (fun x => Work.CohomologicalShrinking.coindShiftMap_proj f.toAddMonoidHom hf x) y

/-! ## Stage 3: transport of `Ĥ⁰` along the shift pairing -/

/-- **The shift isomorphisms on `Ĥ⁰`**: `Ĥ⁰(G, (coindUp G (M^∨))^∨) ≃+ Ĥ⁰(G, coindShift G M)`. -/
noncomputable def tateDualH0Iso (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction G M] [SMulCommClass G (ZMod p) M] [Finite M] :
    Work.Tate.H0 G (DualMod p ↥(Work.Tate.coindUp G (DualMod p M))) ≃+
      Work.Tate.H0 G (Work.Tate.coindShift G M) :=
  Work.Tate.H0Equiv (shiftDualEquiv p G M).symm.toAddMonoidHom
    (shiftDualEquiv_symm_equiv p G M) (shiftDualEquiv p G M).symm.bijective

theorem tateDualH0Iso_apply (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction G M] [SMulCommClass G (ZMod p) M] [Finite M]
    (x : Work.Tate.H0 G (DualMod p ↥(Work.Tate.coindUp G (DualMod p M)))) :
    tateDualH0Iso p G M x =
      Work.Tate.H0Map G (DualMod p ↥(Work.Tate.coindUp G (DualMod p M)))
        (Work.Tate.coindShift G M) (shiftDualEquiv p G M).symm.toAddMonoidHom
        (shiftDualEquiv_symm_equiv p G M) x := rfl

/-- Naturality of `tateDualH0Iso` in the coefficient `M`, in the spelling of `H0Map`. -/
theorem tateDualH0Iso_natural_aux
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction G M]
    [SMulCommClass G (ZMod p) M] [Finite M]
    (M₂ : Type) [AddCommGroup M₂] [Module (ZMod p) M₂] [DistribMulAction G M₂]
    [SMulCommClass G (ZMod p) M₂] [Finite M₂]
    (f : M →ₗ[ZMod p] M₂) (hf : ∀ (g : G) (m : M), f (g • m) = g • f m) :
    (Work.Tate.H0Map G (DualMod p ↥(Work.Tate.coindUp G (DualMod p M₂)))
        (Work.Tate.coindShift G M₂) (shiftDualEquiv p G M₂).symm.toAddMonoidHom
        (shiftDualEquiv_symm_equiv p G M₂)).comp
      (Work.Tate.H0Map G (DualMod p ↥(Work.Tate.coindUp G (DualMod p M)))
        (DualMod p ↥(Work.Tate.coindUp G (DualMod p M₂)))
        (dualCoindUpMapLin p G M M₂ f hf).dualMap.toAddMonoidHom
        (TateDual.dualMap_equiv_of p G (dualCoindUpMapLin p G M M₂ f hf)
          (dualCoindUpMapLin_equiv p G M M₂ f hf)))
      = (Work.Tate.H0Map G (Work.Tate.coindShift G M) (Work.Tate.coindShift G M₂)
          (Work.CohomologicalShrinking.coindShiftMap f.toAddMonoidHom hf)
          (Work.CohomologicalShrinking.coindShiftMap_equiv f.toAddMonoidHom hf)).comp
        (Work.Tate.H0Map G (DualMod p ↥(Work.Tate.coindUp G (DualMod p M)))
          (Work.Tate.coindShift G M) (shiftDualEquiv p G M).symm.toAddMonoidHom
          (shiftDualEquiv_symm_equiv p G M)) := by
  -- The two coefficient maps agree after the shift isomorphisms.
  have hnat := shiftDualEquiv_natural p G M M₂ f hf
  have key : (shiftDualEquiv p G M₂).symm.toAddMonoidHom.comp
        (LinearMap.dualMap (dualCoindUpMapLin p G M M₂ f hf)).toAddMonoidHom
      = (Work.CohomologicalShrinking.coindShiftMap f.toAddMonoidHom hf).comp
          (shiftDualEquiv p G M).symm.toAddMonoidHom :=
    Work.CohomologicalShrinking.symm_paste (shiftDualEquiv p G M) (shiftDualEquiv p G M₂)
      (Work.CohomologicalShrinking.coindShiftMap f.toAddMonoidHom hf)
      (LinearMap.dualMap (dualCoindUpMapLin p G M M₂ f hf)).toAddMonoidHom hnat.symm
  rw [← Work.CohomologicalShrinking.H0Map_comp
        (e := (dualCoindUpMapLin p G M M₂ f hf).dualMap.toAddMonoidHom)
        (f := (shiftDualEquiv p G M₂).symm.toAddMonoidHom)
        (he := TateDual.dualMap_equiv_of p G (dualCoindUpMapLin p G M M₂ f hf)
          (dualCoindUpMapLin_equiv p G M M₂ f hf))
        (hf := shiftDualEquiv_symm_equiv p G M₂)
        (hfe := Work.CohomologicalShrinking.IsEquivariant.comp'
          (dualCoindUpMapLin p G M M₂ f hf).dualMap.toAddMonoidHom
          (TateDual.dualMap_equiv_of p G (dualCoindUpMapLin p G M M₂ f hf)
            (dualCoindUpMapLin_equiv p G M M₂ f hf))
          (shiftDualEquiv p G M₂).symm.toAddMonoidHom
          (shiftDualEquiv_symm_equiv p G M₂)),
      ← Work.CohomologicalShrinking.H0Map_comp
        (e := (shiftDualEquiv p G M).symm.toAddMonoidHom)
        (f := Work.CohomologicalShrinking.coindShiftMap f.toAddMonoidHom hf)
        (he := shiftDualEquiv_symm_equiv p G M)
        (hf := Work.CohomologicalShrinking.coindShiftMap_equiv f.toAddMonoidHom hf)
        (hfe := Work.CohomologicalShrinking.IsEquivariant.comp'
          (shiftDualEquiv p G M).symm.toAddMonoidHom (shiftDualEquiv_symm_equiv p G M)
          (Work.CohomologicalShrinking.coindShiftMap f.toAddMonoidHom hf)
          (Work.CohomologicalShrinking.coindShiftMap_equiv f.toAddMonoidHom hf))]
  exact Work.CohomologicalShrinking.H0Map_congr _ _ key

/-- Naturality of `tateDualH0Iso` in the coefficient `M`. -/
theorem tateDualH0Iso_natural
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction G M]
    [SMulCommClass G (ZMod p) M] [Finite M]
    (M₂ : Type) [AddCommGroup M₂] [Module (ZMod p) M₂] [DistribMulAction G M₂]
    [SMulCommClass G (ZMod p) M₂] [Finite M₂]
    (f : M →ₗ[ZMod p] M₂) (hf : ∀ (g : G) (m : M), f (g • m) = g • f m) :
    (tateDualH0Iso p G M₂).toAddMonoidHom.comp
        (Work.Tate.H0Map G (DualMod p ↥(Work.Tate.coindUp G (DualMod p M)))
          (DualMod p ↥(Work.Tate.coindUp G (DualMod p M₂)))
          (dualCoindUpMapLin p G M M₂ f hf).dualMap.toAddMonoidHom
          (TateDual.dualMap_equiv_of p G (dualCoindUpMapLin p G M M₂ f hf)
            (dualCoindUpMapLin_equiv p G M M₂ f hf)))
      = (Work.Tate.H0Map G (Work.Tate.coindShift G M) (Work.Tate.coindShift G M₂)
          (Work.CohomologicalShrinking.coindShiftMap f.toAddMonoidHom hf)
          (Work.CohomologicalShrinking.coindShiftMap_equiv f.toAddMonoidHom hf)).comp
        (tateDualH0Iso p G M).toAddMonoidHom :=
  tateDualH0Iso_natural_aux p G M M₂ f hf


/-! ## Stage 4: the dimension shift `Ĥ⁰(G, coindShift G M) ≅ H¹(G, M)` -/

/-- Naturality of the connecting map of the shift sequence in the coefficient `M`
(this is `Work.CohomologicalShrinking.tate.dimensionShiftH1H0_natural` instantiated at the
canonical map `coindShiftMap f`). -/
theorem dimensionShiftH1H0Symm_natural
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction G M]
    [SMulCommClass G (ZMod p) M]
    (M₂ : Type) [AddCommGroup M₂] [Module (ZMod p) M₂] [DistribMulAction G M₂]
    [SMulCommClass G (ZMod p) M₂]
    (f : M →ₗ[ZMod p] M₂) (hf : ∀ (g : G) (m : M), f (g • m) = g • f m) :
    (Work.GroupCohomology.mapH1 G f.toAddMonoidHom hf).comp
        (Work.Tate.dimensionShiftH1H0Symm G M).toAddMonoidHom
      = (Work.Tate.dimensionShiftH1H0Symm G M₂).toAddMonoidHom.comp
          (Work.Tate.H0Map G (Work.Tate.coindShift G M) (Work.Tate.coindShift G M₂)
            (Work.CohomologicalShrinking.coindShiftMap f.toAddMonoidHom hf)
            (Work.CohomologicalShrinking.coindShiftMap_equiv f.toAddMonoidHom hf)) :=
  Work.CohomologicalShrinking.tate.dimensionShiftH1H0_natural (p := p) (G := G) (A := M) (B := M₂)
    f hf (Work.CohomologicalShrinking.coindShiftMap f.toAddMonoidHom hf)
    (fun x => Work.CohomologicalShrinking.coindShiftMap_proj f.toAddMonoidHom hf x)
    (Work.CohomologicalShrinking.coindShiftMap_equiv f.toAddMonoidHom hf)

/-! ## The three-stage composite and its naturality -/

/-- Precomposition by a fixed additive homomorphism, as an additive homomorphism. -/
def precompHom {D B C : Type} [AddCommGroup D] [AddCommGroup B] [AddCommGroup C]
    (g : B →+ C) : (C →+ D) →+ (B →+ D) where
  toFun φ := φ.comp g
  map_zero' := by ext x; rfl
  map_add' φ ψ := by ext x; rfl

/-- The composite of the last two stages: `Ĥ⁰(G, (coindUp G (M^∨))^∨) ≃+ H¹(G, M)`. -/
noncomputable def dualH0H1Iso (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction G M] [SMulCommClass G (ZMod p) M] [Finite M] :
    Work.Tate.H0 G (DualMod p ↥(Work.Tate.coindUp G (DualMod p M))) ≃+
      Work.GroupCohomology.H1 G M :=
  (tateDualH0Iso p G M).trans (Work.Tate.dimensionShiftH1H0Symm G M)

theorem dualH0H1Iso_toAddMonoidHom (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction G M] [SMulCommClass G (ZMod p) M] [Finite M] :
    (dualH0H1Iso p G M).toAddMonoidHom
      = (Work.Tate.dimensionShiftH1H0Symm G M).toAddMonoidHom.comp
          (tateDualH0Iso p G M).toAddMonoidHom := rfl

/-- Naturality of the composite `dualH0H1Iso`. -/
theorem dualH0H1Iso_natural
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction G M]
    [SMulCommClass G (ZMod p) M] [Finite M]
    (M₂ : Type) [AddCommGroup M₂] [Module (ZMod p) M₂] [DistribMulAction G M₂]
    [SMulCommClass G (ZMod p) M₂] [Finite M₂]
    (f : M →ₗ[ZMod p] M₂) (hf : ∀ (g : G) (m : M), f (g • m) = g • f m) :
    (dualH0H1Iso p G M₂).toAddMonoidHom.comp
        (Work.Tate.H0Map G (DualMod p ↥(Work.Tate.coindUp G (DualMod p M)))
          (DualMod p ↥(Work.Tate.coindUp G (DualMod p M₂)))
          (dualCoindUpMapLin p G M M₂ f hf).dualMap.toAddMonoidHom
          (TateDual.dualMap_equiv_of p G (dualCoindUpMapLin p G M M₂ f hf)
            (dualCoindUpMapLin_equiv p G M M₂ f hf)))
      = (Work.GroupCohomology.mapH1 G f.toAddMonoidHom hf).comp
          (dualH0H1Iso p G M).toAddMonoidHom := by
  have h2 := tateDualH0Iso_natural p G M M₂ f hf
  have h3 := dimensionShiftH1H0Symm_natural p G M M₂ f hf
  calc (dualH0H1Iso p G M₂).toAddMonoidHom.comp
        (Work.Tate.H0Map G (DualMod p ↥(Work.Tate.coindUp G (DualMod p M)))
          (DualMod p ↥(Work.Tate.coindUp G (DualMod p M₂)))
          (dualCoindUpMapLin p G M M₂ f hf).dualMap.toAddMonoidHom
          (TateDual.dualMap_equiv_of p G (dualCoindUpMapLin p G M M₂ f hf)
            (dualCoindUpMapLin_equiv p G M M₂ f hf)))
      = ((Work.Tate.dimensionShiftH1H0Symm G M₂).toAddMonoidHom.comp
            (tateDualH0Iso p G M₂).toAddMonoidHom).comp
          (Work.Tate.H0Map G (DualMod p ↥(Work.Tate.coindUp G (DualMod p M)))
            (DualMod p ↥(Work.Tate.coindUp G (DualMod p M₂)))
            (dualCoindUpMapLin p G M M₂ f hf).dualMap.toAddMonoidHom
            (TateDual.dualMap_equiv_of p G (dualCoindUpMapLin p G M M₂ f hf)
              (dualCoindUpMapLin_equiv p G M M₂ f hf))) := by
        rw [dualH0H1Iso_toAddMonoidHom]
    _ = (Work.Tate.dimensionShiftH1H0Symm G M₂).toAddMonoidHom.comp
          ((tateDualH0Iso p G M₂).toAddMonoidHom.comp
            (Work.Tate.H0Map G (DualMod p ↥(Work.Tate.coindUp G (DualMod p M)))
              (DualMod p ↥(Work.Tate.coindUp G (DualMod p M₂)))
              (dualCoindUpMapLin p G M M₂ f hf).dualMap.toAddMonoidHom
              (TateDual.dualMap_equiv_of p G (dualCoindUpMapLin p G M M₂ f hf)
                (dualCoindUpMapLin_equiv p G M M₂ f hf)))) := by
        rw [AddMonoidHom.comp_assoc]
    _ = (Work.Tate.dimensionShiftH1H0Symm G M₂).toAddMonoidHom.comp
          ((Work.Tate.H0Map G (Work.Tate.coindShift G M) (Work.Tate.coindShift G M₂)
              (Work.CohomologicalShrinking.coindShiftMap f.toAddMonoidHom hf)
              (Work.CohomologicalShrinking.coindShiftMap_equiv f.toAddMonoidHom hf)).comp
            (tateDualH0Iso p G M).toAddMonoidHom) := by
        rw [h2]
    _ = ((Work.Tate.dimensionShiftH1H0Symm G M₂).toAddMonoidHom.comp
          (Work.Tate.H0Map G (Work.Tate.coindShift G M) (Work.Tate.coindShift G M₂)
            (Work.CohomologicalShrinking.coindShiftMap f.toAddMonoidHom hf)
            (Work.CohomologicalShrinking.coindShiftMap_equiv f.toAddMonoidHom hf))).comp
          (tateDualH0Iso p G M).toAddMonoidHom := by
        rw [AddMonoidHom.comp_assoc]
    _ = ((Work.GroupCohomology.mapH1 G f.toAddMonoidHom hf).comp
          (Work.Tate.dimensionShiftH1H0Symm G M).toAddMonoidHom).comp
          (tateDualH0Iso p G M).toAddMonoidHom := by
        rw [← h3]
    _ = (Work.GroupCohomology.mapH1 G f.toAddMonoidHom hf).comp
          ((Work.Tate.dimensionShiftH1H0Symm G M).toAddMonoidHom.comp
            (tateDualH0Iso p G M).toAddMonoidHom) := by
        rw [AddMonoidHom.comp_assoc]
    _ = (Work.GroupCohomology.mapH1 G f.toAddMonoidHom hf).comp
          (dualH0H1Iso p G M).toAddMonoidHom := by
        rw [dualH0H1Iso_toAddMonoidHom]

/-! ## The family `dualE` and its naturality -/

/-- **The natural degree-`(-2)` Tate duality** `Ĥ⁻²(G, M^∨) ≃+ H¹(G, M)^∨` in the models of
`Submission/Work/Tate`: the composite of the degree-`0` evaluation pairing
(`tateDualHm1Iso`), the shift pairing on `Ĥ⁰` (`dualH0H1Iso`) and the transport of functionals
along it. -/
noncomputable def dualE (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction G M] [SMulCommClass G (ZMod p) M] [Finite M] :
    Work.Tate.Hm2 G (DualMod p M) ≃+ (Work.GroupCohomology.H1 G M →+ ZMod p) :=
  (tateDualHm1Iso p G ↥(Work.Tate.coindUp G (DualMod p M))).trans
    (addHomCongrRight (dualH0H1Iso p G M))

theorem dualE_apply (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction G M] [SMulCommClass G (ZMod p) M] [Finite M]
    (z : Work.Tate.Hm2 G (DualMod p M)) (c : Work.GroupCohomology.H1 G M) :
    dualE p G M z c = tateDualHm1Iso p G ↥(Work.Tate.coindUp G (DualMod p M)) z
      ((dualH0H1Iso p G M).symm c) := by
  simp only [dualE, AddEquiv.trans_apply, addHomCongrRight, AddEquiv.coe_toAddMonoidHom]
  rfl

/-- Naturality of the degree-`0` pairing isomorphism, as an identity of additive
homomorphisms. -/
theorem tateDualHm1Iso_natural_hom
    (A : Type) [AddCommGroup A] [Module (ZMod p) A] [DistribMulAction G A]
    [SMulCommClass G (ZMod p) A] [FiniteDimensional (ZMod p) A]
    (B : Type) [AddCommGroup B] [Module (ZMod p) B] [DistribMulAction G B]
    [SMulCommClass G (ZMod p) B] [FiniteDimensional (ZMod p) B]
    (u : A →ₗ[ZMod p] B) (hu : ∀ (g : G) (a : A), u (g • a) = g • u a) :
    (tateDualHm1Iso p G B).toAddMonoidHom.comp
        (Work.Tate.Hm1Map G A B u.toAddMonoidHom hu)
      = (precompHom (Work.Tate.H0Map G (DualMod p B) (DualMod p A)
            u.dualMap.toAddMonoidHom (TateDual.dualMap_equiv_of p G u hu))).comp
          (tateDualHm1Iso p G A).toAddMonoidHom := by
  apply AddMonoidHom.ext
  intro x
  ext φ
  rw [AddMonoidHom.comp_apply, precompHom, AddMonoidHom.comp_apply]
  exact tateDualHm1Iso_natural p G A B u hu x φ

/-! ## Naturality of `dualE`, and the theorem -/

/-- Naturality of the family `dualE`. -/
theorem dualE_natural
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction G M]
    [SMulCommClass G (ZMod p) M] [Finite M]
    (M₂ : Type) [AddCommGroup M₂] [Module (ZMod p) M₂] [DistribMulAction G M₂]
    [SMulCommClass G (ZMod p) M₂] [Finite M₂]
    (f : M →ₗ[ZMod p] M₂) (hf : ∀ (g : G) (m : M), f (g • m) = g • f m)
    (y : Work.Tate.Hm2 G (DualMod p M₂)) :
    dualE p G M (Work.Tate.Hm2Map f.dualMap.toAddMonoidHom
        (fun g z => by
          show f.dualMap (g • z) = g • f.dualMap z
          ext m
          simp only [LinearMap.dualMap_apply, DualMod.dualSMul_apply, hf]) y)
      = (dualE p G M₂ y).comp (Work.GroupCohomology.mapH1 G f.toAddMonoidHom hf) := by
  -- `Hm2Map f^∨` is `Hm1Map` of the induced map on the `I_G`-twists.
  have hF : Work.Tate.Hm2Map (A := DualMod p M₂) (B := DualMod p M)
        f.dualMap.toAddMonoidHom
        (fun g z => by
          show f.dualMap (g • z) = g • f.dualMap z
          ext m
          simp only [LinearMap.dualMap_apply, DualMod.dualSMul_apply, hf])
      = Work.Tate.Hm1Map G ↥(Work.Tate.coindUp G (DualMod p M₂))
          ↥(Work.Tate.coindUp G (DualMod p M))
          (dualCoindUpMapLin p G M M₂ f hf).toAddMonoidHom
          (dualCoindUpMapLin_equiv p G M M₂ f hf) := by
    unfold Work.Tate.Hm2Map
    refine Work.CohomologicalShrinking.Hm1Map_congr _ _ ?_
    exact (TateDual.coindUpMapLin_toAddMonoidHom p G f.dualMap _).symm
  -- the two composite maps agree after the shift isomorphisms
  have hd := dualH0H1Iso_natural p G M M₂ f hf
  have key : (dualH0H1Iso p G M₂).symm.toAddMonoidHom.comp
        (Work.GroupCohomology.mapH1 G f.toAddMonoidHom hf)
      = (Work.Tate.H0Map G (DualMod p ↥(Work.Tate.coindUp G (DualMod p M)))
            (DualMod p ↥(Work.Tate.coindUp G (DualMod p M₂)))
            (dualCoindUpMapLin p G M M₂ f hf).dualMap.toAddMonoidHom
            (TateDual.dualMap_equiv_of p G (dualCoindUpMapLin p G M M₂ f hf)
              (dualCoindUpMapLin_equiv p G M M₂ f hf))).comp
          (dualH0H1Iso p G M).symm.toAddMonoidHom :=
    Work.CohomologicalShrinking.symm_paste (dualH0H1Iso p G M) (dualH0H1Iso p G M₂)
      (Work.Tate.H0Map G (DualMod p ↥(Work.Tate.coindUp G (DualMod p M)))
        (DualMod p ↥(Work.Tate.coindUp G (DualMod p M₂)))
        (dualCoindUpMapLin p G M M₂ f hf).dualMap.toAddMonoidHom
        (TateDual.dualMap_equiv_of p G (dualCoindUpMapLin p G M M₂ f hf)
          (dualCoindUpMapLin_equiv p G M M₂ f hf)))
      (Work.GroupCohomology.mapH1 G f.toAddMonoidHom hf) hd.symm
  apply AddMonoidHom.ext
  intro c
  rw [AddMonoidHom.comp_apply, dualE_apply, hF, dualE_apply]
  rw [tateDualHm1Iso_natural p G ↥(Work.Tate.coindUp G (DualMod p M₂))
        ↥(Work.Tate.coindUp G (DualMod p M)) (dualCoindUpMapLin p G M M₂ f hf)
        (dualCoindUpMapLin_equiv p G M M₂ f hf) y ((dualH0H1Iso p G M).symm c)]
  congr 1
  have hcw := DFunLike.congr_fun key.symm c
  simp only [AddMonoidHom.comp_apply] at hcw
  exact hcw

theorem tateDuality_hm2_dual_natural (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [Fintype G] :
    ∃ e : ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction G M]
        [SMulCommClass G (ZMod p) M] [Finite M],
        Work.Tate.Hm2 G (Work.SSGRoute.DualMod p M) ≃+
          (Work.GroupCohomology.H1 G M →+ ZMod p),
      (∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction G M]
        [SMulCommClass G (ZMod p) M] [Finite M]
        (M₂ : Type) [AddCommGroup M₂] [Module (ZMod p) M₂] [DistribMulAction G M₂]
        [SMulCommClass G (ZMod p) M₂] [Finite M₂]
        (f : M →ₗ[ZMod p] M₂) (hf : ∀ (g : G) (m : M), f (g • m) = g • f m)
        (y : Work.Tate.Hm2 G (Work.SSGRoute.DualMod p M₂)),
        e M (Work.Tate.Hm2Map f.dualMap.toAddMonoidHom
              (fun g z => by
                show f.dualMap (g • z) = g • f.dualMap z
                ext m
                simp only [LinearMap.dualMap_apply, Work.SSGRoute.DualMod.dualSMul_apply, hf])
              y)
          = (e M₂ y).comp (Work.GroupCohomology.mapH1 G f.toAddMonoidHom hf)) := by
  refine ⟨dualE p G, ?_⟩
  intro M _ _ _ _ _ M₂ _ _ _ _ _ f hf y
  exact dualE_natural p G M M₂ f hf y

end Work.SSGRoute
