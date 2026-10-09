import Mathlib
import Submission.Work.SSGRoute.PTdualControl.extExact
import Submission.Work.SSGRoute.E1cGeneric.Canonical
import Submission.Work.SSGRoute.ExtChain.ChainGamma
import Submission.Work.SSGRoute.SSGStage.e1aLandingFinCompat
import Submission.Work.SSGRoute.ExtChain.extLoc_extToIdeles_e1aSyzShift_eq_zero_imp
import Submission.Work.SSGRoute.ExtChain.shift_symm_extToIdeles_eq_zero_gen
import Submission.Work.SSGRoute.ExtChain.freeCoverSES_lattice
import Submission.Work.SSGRoute.ExtChain.resH2_zpowers_e1aChainH_eq_zero_of_extRes_zpowers_eq_zero
import Submission.Work.SSGRoute.ExtChain.hasseExt1_C2_lattice_general
import Submission.Work.SSGRoute.ExtChain.subsingleton_H2_zpowers_homCoind_odd
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ExtChain

open CategoryTheory SSGRoute.PTExt
open scoped TensorProduct

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 2000000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency.types false

/-! ## Status of this file (session of 2026-10-02, evening)

The target `Work.SSGRoute.ExtChain.himgIdelesInput_inf` is proved below from a single residual
input, `himg_involution_input_two` (`p = 2` case only): the `p ≠ 2` case is
`himg_involution_input_odd`, discharged by the `Subsingleton (H²(⟨σ⟩, homCoind …))` of
`ExtChain.subsingleton_H2_zpowers_homCoind_odd`.  By `NOTE_himgIdelesInput_inf_reduction.md` §9.1
that residual is *the same statement* as the `p = 2` branch of `ExtChain.himgExtDeltaInput_inf`
(the hypothesis `hy` puts the class in the image of the connecting map `extDelta`, and the two
connecting maps commute), and §9.2 of that note records that the archimedean local Tate duality
needed for it is on disk and sorry-free (`Work.SSGRoute.local_tate_duality_archimedean`, the
`E7Arch`/`H1Pair` lanes), the missing pieces being the finite-place clause bundle, the global
reciprocity law for the local invariants, and `pt_selmer_relaxed` with its counting identity. -/

/-! ## The formal reduction of the involution input to the `H²`-side

The conclusion is a vanishing in `H¹(⟨σ⟩, Hom_ℤ(R,Ωˣ))`, where `R = ker (freeCover N)` is the
canonical syzygy.  Restricting the *connecting map* `δ` of the dualised canonical resolution
`e1aSES N : 0 → Hom(N,Ωˣ) → Hom(F,Ωˣ) → Hom(R,Ωˣ) → 0` to the ⟨σ⟩-part of the total long exact
sequence (`deltaH2_restriction`) turns the target into the vanishing of the corresponding class on
the `H²`-side, `resH2_{⟨σ⟩} (e1aChainH N y) = 0` with `y = e1aSyzShift N z`; the passage back uses
the injectivity of the restricted connecting map (`deltaH2_restrictSES_e1aSES_injective'`, whose
kernel is `H¹(⟨σ⟩, Hom_ℤ(ℤ[G]^n,Ωˣ)) = 0`).  This is a purely formal reduction: it uses only the
definitions of `e1aDelta`, `e1cMap`, `e1aSyzShift` and `e1aChainH` and no arithmetic. -/

/-- **The formal reduction of the involution input.**  If the `H²`-side chain class restricts to
zero at `⟨σ⟩` (`σ² = 1`), then so does the `H¹`-side `E1c` class of the syzygy-shift of `z`. -/
theorem resH1_zpowers_e1cMap_eq_zero_of_resH2_e1aChainH_eq_zero {k : Type} [Field k]
    [NumberField k] {Ω : Type} [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField K]
    (N : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Finite N.V]
    [Module.Finite ℤ ↥(CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N))]
    (σ : Ω ≃ₐ[k] Ω) (hσ : σ ^ 2 = 1)
    (z : CategoryTheory.Abelian.Ext.{0}
      (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N)) (SSGRoute.PTExt.unitsK k K) 1)
    (h : Work.SSGRoute.PT.resH2 (Subgroup.zpowers σ)
      (Work.SSGRoute.PT.e1aChainH (k := k) (Ω := Ω) (K := K) N
        (Work.SSGRoute.ExtChain.e1aSyzShift (k := k) (K := K) N z)) = 0) :
    Work.SSGRoute.PT.H2Fin.resH1 (Subgroup.zpowers σ)
      (Work.SSGRoute.homCoind k Ω K
        (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N)))
      (Work.SSGRoute.ExtChain.e1cMap (k := k) (Ω := Ω) (K := K)
        (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N)) z) = 0 := by
  have hcl : IsClosed ((Subgroup.zpowers σ : Subgroup (Ω ≃ₐ[k] Ω)) : Set (Ω ≃ₐ[k] Ω)) := by
    refine Set.Finite.isClosed (Set.Finite.subset
      (Set.Finite.insert σ (Set.finite_singleton (1 : Ω ≃ₐ[k] Ω))) ?_)
    intro x hx
    rw [Set.mem_insert_iff, Set.mem_singleton_iff]
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have h1 : σ ^ m = σ ^ (m % ((2 : ℕ) : ℤ)) :=
      zpow_eq_zpow_emod m (show σ ^ (((2 : ℕ) : ℤ)) = 1 by rw [zpow_natCast]; exact hσ)
    rw [h1]
    rcases (by omega : m % ((2 : ℕ) : ℤ) = 0 ∨ m % ((2 : ℕ) : ℤ) = 1) with hh | hh
    · right; rw [hh, zpow_zero]
    · left; rw [hh, zpow_one]
  have hInj := Work.SSGRoute.ExtChain.deltaH2_restrictSES_e1aSES_injective'
    (k := k) (Ω := Ω) (K := K) N (Subgroup.zpowers σ) hcl
  have key : (Work.SSGRoute.ExtChain.restrictSES (Work.SSGRoute.ExtChain.e1aSES N)
      (Subgroup.zpowers σ)).deltaH2
      (Work.SSGRoute.PT.H2Fin.resH1 (Subgroup.zpowers σ)
        (Work.SSGRoute.homCoind k Ω K
          (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N)))
        (Work.SSGRoute.ExtChain.e1cMap (k := k) (Ω := Ω) (K := K)
          (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N)) z)) = 0 := by
    rw [← Work.SSGRoute.ExtChain.deltaH2_restriction (Work.SSGRoute.ExtChain.e1aSES N)
      (Subgroup.zpowers σ)
      (Work.SSGRoute.ExtChain.e1cMap (k := k) (Ω := Ω) (K := K)
        (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N)) z)]
    have hH : (Work.SSGRoute.ExtChain.e1aSES N).deltaH2
        (Work.SSGRoute.ExtChain.e1cMap (k := k) (Ω := Ω) (K := K)
          (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N)) z)
        = Work.SSGRoute.PT.e1aChainH (k := k) (Ω := Ω) (K := K) N
            (Work.SSGRoute.ExtChain.e1aSyzShift (k := k) (K := K) N z) := by
      rw [Work.SSGRoute.PT.e1aChainH_apply (k := k) (Ω := Ω) (K := K) N
        (Work.SSGRoute.ExtChain.e1aSyzShift (k := k) (K := K) N z),
        AddEquiv.symm_apply_apply]
      rfl
    rw [hH]
    exact h
  exact hInj (by rw [key, map_zero])

/-- **Restriction commutes with a change of coefficients.**  For an equivariant additive map
`f : M →+ N` of discrete `G`-modules and a subgroup `U ≤ G`, restricting the `H²`-class
`mapH2 f _ x` to `U` is the same as applying `mapH2 f` to the restriction of `x` (with `f` read as a
`↥U`-equivariant map).  This is the `H²`-analogue of `AbsoluteKummer.akRes_mapH2`, transported
along `SSGStage.akRes_eq_resH2`. -/
theorem resH2_mapH2 {G : Type} [TopologicalSpace G] [Group G]
    {M N : Type} [AddCommGroup M] [AddCommGroup N] [DistribMulAction G M] [DistribMulAction G N]
    (f : M →+ N) (hf : Work.GroupCohomology.IsEquivariant G f)
    (U : Subgroup G) (x : Work.AbsoluteKummer.H2 G M) :
    Work.SSGRoute.PT.resH2 U (Work.AbsoluteKummer.mapH2 f hf x) =
      Work.AbsoluteKummer.mapH2 f (fun (h : ↥U) (m : M) => hf (h : G) m)
        (Work.SSGRoute.PT.resH2 U x) := by
  rw [← Work.SSGRoute.SSGStage.akRes_eq_resH2 U N (Work.AbsoluteKummer.mapH2 f hf x),
    ← Work.SSGRoute.SSGStage.akRes_eq_resH2 U M x,
    Work.AbsoluteKummer.akRes_mapH2 U f hf x]

/-- **L1, the naturality backbone of the dévissage in `E`.**  For a morphism `F : N₂ ⟶ N₁` of
coefficients and `σ² = 1`: the vanishing of the restricted chain class at `N₁` implies the
vanishing of the restricted chain class at `N₂` for every class pushed forward along `F`.  Proof:
`e1aChainH_natural` writes the second chain class as `mapH2 (precomp F) _` of the first, and
`resH2_mapH2` commutes `resH2` with that coefficient map. -/
theorem resH2_zpowers_e1aChainH_eq_zero_of_map_eq_zero
    {k : Type} [Field k] [NumberField k] {Ω : Type} [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField K]
    (N₁ N₂ : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Finite N₁.V] [Finite N₂.V]
    (F : N₂ ⟶ N₁)
    (σ : Ω ≃ₐ[k] Ω) (hσ : σ ^ 2 = 1)
    (y : CategoryTheory.Abelian.Ext.{0} N₁ (SSGRoute.PTExt.unitsK k K) 2)
    (h : Work.SSGRoute.PT.resH2 (Subgroup.zpowers σ)
      (Work.SSGRoute.PT.e1aChainH (k := k) (Ω := Ω) (K := K) N₁ y) = 0) :
    Work.SSGRoute.PT.resH2 (Subgroup.zpowers σ)
      (Work.SSGRoute.PT.e1aChainH (k := k) (Ω := Ω) (K := K) N₂
        ((CategoryTheory.Abelian.Ext.mk₀ F).comp y (zero_add 2))) = 0 := by
  rw [Work.SSGRoute.PT.e1aChainH_natural (k := k) (Ω := Ω) (K := K) N₁ N₂ F y]
  rw [resH2_mapH2]
  rw [h, map_zero]

/-- **`mapH2` does not depend on the proof of equivariance.**  The `H²`-analogue of
`E1cGeneric.mapH0_proof_irrel`; it is what lets a chain identity derived with the equivariance
proof produced by the definition of `e1aChainC` be applied at the subgroup level, where the
equivariance proof is the restricted lambda. -/
theorem mapH2_proof_irrel {G : Type} [TopologicalSpace G] [Group G]
    {M N : Type} [AddCommGroup M] [DistribMulAction G M] [AddCommGroup N] [DistribMulAction G N]
    (f : M →+ N) (h₁ h₂ : Work.GroupCohomology.IsEquivariant G f) :
    Work.AbsoluteKummer.mapH2 f h₁ = Work.AbsoluteKummer.mapH2 f h₂ := by
  ext x
  exact Work.AbsoluteKummer.SES.H2_induction_on
    (C := fun y => Work.AbsoluteKummer.mapH2 f h₁ y = Work.AbsoluteKummer.mapH2 f h₂ y) x
    (fun c => by
      -- `mapH2`'s value on the class of `c` is the class of `mapZ2 f _ c`, and the two `Z2`-elements
      -- differ only in their `Prop`-valued proof components (kernel proof irrelevance), so this one
      -- rewrite closes the goal
      rw [Work.AbsoluteKummer.mapH2_H2π f h₁ c])

/-- **The converse transfer: the `E`-form of the chain vanishes whenever the `Hom`-side class
does.**  Same template as the doorway below, in the easy direction: `e1aChainC` *is* `mapH2` of
`e1aChainH` along `e1aCoeffNat` (definitionally), and `resH2` commutes with `mapH2`, so the
vanishing transfers by `rw`.  Together with the doorway this makes the input an *equivalence*
between its `Hom`-side form (in which the goal `himg_involution_input` is stated) and its
`E`-form (in which the dévissage in `E` is to be run — see §6ter of
`NOTE_himgIdelesInput_inf_reduction.md`); this is the coefficient-iso half of the seam between the
two forms. -/
theorem resH2_zpowers_e1aChainC_eq_zero_of_e1aChainH_eq_zero
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [NumberField K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    [hNfin : Finite (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E).V]
    (σ : Ω ≃ₐ[k] Ω) (hσ : σ ^ 2 = 1)
    (y : CategoryTheory.Abelian.Ext.{0} (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E)
      (SSGRoute.PTExt.unitsK k K) 2)
    (h : Work.SSGRoute.PT.resH2 (Subgroup.zpowers σ)
      (Work.SSGRoute.PT.e1aChainH (k := k) (Ω := Ω) (K := K)
        (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E) y) = 0) :
    @Work.SSGRoute.PT.resH2 (Ω ≃ₐ[k] Ω) _ _ (Subgroup.zpowers σ) E _
      (DistribMulAction.compHom E (SSGRoute.res k K))
      (Work.SSGRoute.PT.e1aChainC p k Ω K ζ hζ hζK T hT E y) = 0 := by
  haveI : Finite T := Work.SSGRoute.ExtChain.e1aFiniteT p k Ω K ζ T hT
  letI : DistribMulAction (Ω ≃ₐ[k] Ω) E := DistribMulAction.compHom E (SSGRoute.res k K)
  let phi : Work.SSGRoute.homCoind k Ω K (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E) →+ E :=
    ((Work.SSGRoute.ExtChain.e1aCoeffNat p k Ω K ζ hζ hζK T hT E).symm :
      Work.SSGRoute.homCoind k Ω K (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E) →+ E)
  let hfG : Work.GroupCohomology.IsEquivariant (Ω ≃ₐ[k] Ω) phi :=
    fun σ n => Work.SSGRoute.ExtChain.e1aCoeffNat_symm_equivariant p k Ω K ζ hζ hζK T hT E σ n
  -- the goal is `resH2 ⟨σ⟩ (e1aChainC … y) = 0`; rewrite the chain class to its definitional
  -- `mapH2`-form and push the restriction through the coefficient map
  rw [show Work.SSGRoute.PT.e1aChainC p k Ω K ζ hζ hζK T hT E y
      = Work.AbsoluteKummer.mapH2 (G := Ω ≃ₐ[k] Ω) phi hfG
          (Work.SSGRoute.PT.e1aChainH (k := k) (Ω := Ω) (K := K)
            (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E) y) from rfl]
  rw [resH2_mapH2 (G := Ω ≃ₐ[k] Ω)
    (M := Work.SSGRoute.homCoind k Ω K (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E)) (N := E)
    (f := phi) (hf := hfG) (U := Subgroup.zpowers σ)
    (x := Work.SSGRoute.PT.e1aChainH (k := k) (Ω := Ω) (K := K)
      (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E) y)]
  rw [h, map_zero]

/-- **The goal in the `E`-form (the doorway to the dévissage).**  If the restricted *canonical
chain* class with `E`-coefficients, `e1aChainC p k Ω K ζ hζ hζK T hT E y ∈ H²(Γ,E)`, vanishes, then
so does the restricted `Hom`-side chain class `e1aChainH (e1aN0 …) y`.  Indeed `e1aChainC` *is*
`mapH2` of `e1aChainH` along the coefficient equivalence `e1aCoeffNat` (`rfl`), the restriction
commutes with `mapH2` (`resH2_mapH2`), and `mapH2` of an additive equivalence is injective
(`sha2_coeff.mapH2_injective_of_addEquiv`).  This is the step that moves the degree-two input into
the form in which the dévissage in `E` can be run (Shapiro applies to `Hⁱ(G,E)`, not to the twisted
dual `N_E`). -/
theorem resH2_zpowers_e1aChainH_eq_zero_of_e1aChainC_eq_zero
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [NumberField K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    [hNfin : Finite (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E).V]
    (σ : Ω ≃ₐ[k] Ω) (hσ : σ ^ 2 = 1)
    (y : CategoryTheory.Abelian.Ext.{0} (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E)
      (SSGRoute.PTExt.unitsK k K) 2)
    (h : @Work.SSGRoute.PT.resH2 (Ω ≃ₐ[k] Ω) _ _ (Subgroup.zpowers σ) E _
      (DistribMulAction.compHom E (SSGRoute.res k K))
      (Work.SSGRoute.PT.e1aChainC p k Ω K ζ hζ hζK T hT E y) = 0) :
    Work.SSGRoute.PT.resH2 (Subgroup.zpowers σ)
      (Work.SSGRoute.PT.e1aChainH (k := k) (Ω := Ω) (K := K)
        (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E) y) = 0 := by
  haveI : Finite T := Work.SSGRoute.ExtChain.e1aFiniteT p k Ω K ζ T hT
  letI : DistribMulAction (Ω ≃ₐ[k] Ω) E := DistribMulAction.compHom E (SSGRoute.res k K)
  -- the coefficient map (and its equivariance proofs) bound by `let`, so that the spellings of the
  -- equation below and of the injectivity lemma's application coincide
  let phi : Work.SSGRoute.homCoind k Ω K (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E) →+ E :=
    ((Work.SSGRoute.ExtChain.e1aCoeffNat p k Ω K ζ hζ hζK T hT E).symm :
      Work.SSGRoute.homCoind k Ω K (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E) →+ E)
  let hfG : Work.GroupCohomology.IsEquivariant (Ω ≃ₐ[k] Ω) phi :=
    fun σ n => Work.SSGRoute.ExtChain.e1aCoeffNat_symm_equivariant p k Ω K ζ hζ hζK T hT E σ n
  let hfU : Work.GroupCohomology.IsEquivariant ↥(Subgroup.zpowers σ) phi :=
    fun u n => hfG (u : Ω ≃ₐ[k] Ω) n
  -- `e1aChainC … y` is *definitionally* `mapH2 phi hfG` of `e1aChainH … y`
  have h' : Work.SSGRoute.PT.resH2 (Subgroup.zpowers σ)
      (Work.AbsoluteKummer.mapH2 (G := Ω ≃ₐ[k] Ω) phi hfG
        (Work.SSGRoute.PT.e1aChainH (k := k) (Ω := Ω) (K := K)
          (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E) y)) = 0 := h
  rw [resH2_mapH2 (G := Ω ≃ₐ[k] Ω)
    (M := Work.SSGRoute.homCoind k Ω K (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E)) (N := E)
    (f := phi) (hf := hfG) (U := Subgroup.zpowers σ)
    (x := Work.SSGRoute.PT.e1aChainH (k := k) (Ω := Ω) (K := K)
      (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E) y)] at h'
  -- `h'` is now `mapH2 phi hfU (resH2 ⟨σ⟩ (e1aChainH … y)) = 0`; restrict the coefficient map away
  -- (`mapH2` of an additive equivalence is injective) and rewrite `f 0 = 0`
  exact (Work.SSGRoute.sha2_coeff.mapH2_injective_of_addEquiv
      (M := Work.SSGRoute.homCoind k Ω K (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E)) (N := E)
      ((Work.SSGRoute.ExtChain.e1aCoeffNat p k Ω K ζ hζ hζK T hT E).symm)
      hfU
      (fun u e => Work.SSGRoute.ExtChain.e1aCoeffNat_equivariant
        p k Ω K ζ hζ hζK T hT E (u : Ω ≃ₐ[k] Ω) e))
    (h'.trans (map_zero (Work.AbsoluteKummer.mapH2 (G := ↥(Subgroup.zpowers σ))
      (M := Work.SSGRoute.homCoind k Ω K (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E)) (N := E)
      phi hfU)).symm)

/-! ## The reduction of the involution input to the quadratic Hasse principle

`e1aChainH N` is the composite `δ ∘ e1cMap ∘ (e1aSyzShift)⁻¹`, and `δ = e1aDelta` is the connecting
map of the dualised canonical resolution; every factor commutes with the restriction of `Ext` to a
subgroup (functoriality in the coefficient variable), so the Γ-level input is *equivalent* to the
`G`-side statement `extRes ⟨σ̄⟩ y = 0` — this is the (now proved) restriction square
`resH2_zpowers_e1aChainH_eq_zero_of_extRes_zpowers_eq_zero`.  The `G`-side statement is, by the long
exact sequence of the class formation `0 → Kˣ → 𝕀_K → C_K → 0` in the *second* variable, the
statement that the connecting map `extDelta : Ext¹_G(N,C_K) → Ext²_G(N,Kˣ)` vanishes on
`Ext¹_H(N, C_K)` (`H = ⟨σ̄⟩ ≤ G`), i.e. that `Ext²_H(N,Kˣ) → Ext²_H(N,𝕀_K)` is injective: the
**quadratic Hasse principle at the involutive subgroup**, with coefficients in the finite module
`N`.  The two formal ingredients of that reduction — naturality of `extDelta` under restriction and
`extToIdeles ∘ extDelta = 0` — are proved here; the Hasse input itself is
`ExtChain.hbnC2_quadratic_finiteCoefficients`. -/

/-- **Naturality of the connecting map `extDelta` under restriction to a subgroup `H ≤ Gal(K/k)`.**
Both `extRes H.subtype` (which is `Abelian.Ext.mapExactFunctor (Rep.resFunctor H.subtype)`) and
`extDelta` (Yoneda product with the class formation's `extClass`) are functorial, so restriction
carries `extDelta` to the connecting class of the restricted class formation. -/
theorem extRes_subtype_extDelta {k : Type} [Field k] [NumberField k] {Ω : Type} [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] {K : IntermediateField k Ω} [FiniteDimensional k K]
    [IsGalois k K] [NumberField K]
    {M : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)} {r : ℕ}
    (H : Subgroup (K ≃ₐ[k] K))
    (x : CategoryTheory.Abelian.Ext.{0} M (SSGRoute.PTExt.classesK k ↥K) r) :
    SSGRoute.PTExt.extRes H.subtype (SSGRoute.PTExt.extDelta (k := k) (K := ↥K) x) =
      (SSGRoute.PTExt.extRes H.subtype x).comp
        (CategoryTheory.Abelian.Ext.mapExactFunctor (Rep.resFunctor H.subtype)
          (NK.HassePrinciple.ideleShortComplex_shortExact k ↥K).extClass) rfl := by
  show CategoryTheory.Abelian.Ext.mapExactFunctor (Rep.resFunctor H.subtype)
      (x.comp (NK.HassePrinciple.ideleShortComplex_shortExact k ↥K).extClass rfl) = _
  rw [CategoryTheory.Abelian.Ext.mapExactFunctor_comp (Rep.resFunctor H.subtype)
      (α := x) (β := (NK.HassePrinciple.ideleShortComplex_shortExact k ↥K).extClass) rfl]
  rfl

/-- **`extToIdeles ∘ extDelta = 0`**: the connecting class of the class formation is killed by the
diagonal embedding of the principal idèles — the pullback of `0 → Kˣ → 𝕀_K → C_K → 0` along `Kˣ ↪ 𝕀_K`
splits (`Abelian.Ext.mk₀` of the composite is `mk₀ Kˣ → 𝕀_K`, and `extClass` followed by the first
map of its own short complex is zero). -/
theorem extToIdeles_extDelta_eq_zero {k : Type} [Field k] [NumberField k] {Ω : Type} [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] {K : IntermediateField k Ω} [FiniteDimensional k K]
    [IsGalois k K] [NumberField K]
    {M : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)} {r : ℕ}
    (x : CategoryTheory.Abelian.Ext.{0} M ((SSGRoute.PTExt.sesK k ↥K).X₃) r) :
    SSGRoute.PTExt.extToIdeles (k := k)
      (SSGRoute.PTExt.extDelta (k := k) (K := ↥K) x) = 0 := by
  have hS : (SSGRoute.PTExt.sesK k ↥K).ShortExact :=
    NK.HassePrinciple.ideleShortComplex_shortExact k ↥K
  show (x.comp hS.extClass (rfl : r + 1 = r + 1)).comp
      (CategoryTheory.Abelian.Ext.mk₀ (SSGRoute.PTExt.sesK k ↥K).f)
      (add_zero (r + 1)) = 0
  rw [CategoryTheory.Abelian.Ext.comp_assoc_of_third_deg_zero
    (α := x) (β := hS.extClass)
    (γ := CategoryTheory.Abelian.Ext.mk₀ (SSGRoute.PTExt.sesK k ↥K).f)]
  rw [ShortComplex.ShortExact.extClass_comp hS]
  simp

/-- **The involution input on the `G`-side, from the quadratic Hasse principle at `H = ⟨σ̄⟩`.**

`hy : extToIdeles y = 0` puts `y` in the image of the connecting map
(`PTdualControl.exists_extDelta_eq_of_extToIdeles_eq_zero`, the long exact sequence of the class
formation), say `y = extDelta x`; restricting to `H` and using naturality writes
`extRes_H y = (extRes_H x).comp (extClass of the restricted formation)`, and the composite with the
idèle embedding is zero; the Hasse input `hH` (injectivity of `Ext²_H(N,Kˣ) → Ext²_H(N,𝕀_K)`) then
gives `extRes_H y = 0`. -/
theorem extRes_zpowers_eq_zero_of_quadraticHasse {k : Type} [Field k] [NumberField k]
    {Ω : Type} [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] {K : IntermediateField k Ω}
    [FiniteDimensional k K] [IsGalois k K] [NumberField K]
    (N : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Finite N.V]
    (σ : Ω ≃ₐ[k] Ω) (hσ : σ ^ 2 = 1) (hnt : SSGRoute.res k K σ ≠ 1)
    (hH : ∀ z : CategoryTheory.Abelian.Ext.{0}
        (Rep.res (Subgroup.zpowers (SSGRoute.res k K σ)).subtype N)
        (Rep.res (Subgroup.zpowers (SSGRoute.res k K σ)).subtype (SSGRoute.PTExt.unitsK k ↥K)) 2,
      z.comp (CategoryTheory.Abelian.Ext.mk₀
          (Rep.resMap (Subgroup.zpowers (SSGRoute.res k K σ)).subtype
            (NK.HassePrinciple.ideleIncl k ↥K))) (add_zero 2) = 0 → z = 0)
    (y : CategoryTheory.Abelian.Ext.{0} N (SSGRoute.PTExt.unitsK k ↥K) 2)
    (hy : SSGRoute.PTExt.extToIdeles (k := k) y = 0) :
    SSGRoute.PTExt.extRes (Subgroup.zpowers (SSGRoute.res k K σ)).subtype y = 0 := by
  refine hH _ ?_
  show (CategoryTheory.Abelian.Ext.mapExactFunctor
      (Rep.resFunctor (Subgroup.zpowers (SSGRoute.res k K σ)).subtype) y).comp
    (CategoryTheory.Abelian.Ext.mk₀
      (Rep.resMap (Subgroup.zpowers (SSGRoute.res k K σ)).subtype
        (NK.HassePrinciple.ideleIncl k ↥K))) (add_zero 2) = 0
  rw [← CategoryTheory.Abelian.Ext.mapExactFunctor_mk₀
    (F := Rep.resFunctor (Subgroup.zpowers (SSGRoute.res k K σ)).subtype)
    (f := NK.HassePrinciple.ideleIncl k ↥K)]
  rw [← CategoryTheory.Abelian.Ext.mapExactFunctor_comp
    (F := Rep.resFunctor (Subgroup.zpowers (SSGRoute.res k K σ)).subtype)
    (α := y) (β := CategoryTheory.Abelian.Ext.mk₀ (NK.HassePrinciple.ideleIncl k ↥K))
    (add_zero 2)]
  rw [show y.comp (CategoryTheory.Abelian.Ext.mk₀ (NK.HassePrinciple.ideleIncl k ↥K))
        (add_zero 2) = 0 from hy]
  simp

/-- **The quadratic Hasse principle from the degree-one Hasse principle for the canonical syzygy.**

This is the "start on `N₁ = ker (freeCover N)`" step: it shows that the degree-one Hasse statement
for the syzygy lattice alone implies the (`Ext²`, `N`-coefficient) quadratic Hasse principle, so that
the involution half of `himg` is *equivalent* to that single degree-one statement
(`ExtChain.hasseExt1_syzygy_lattice`, and its general form
`ExtChain.hasseExt1_C2_lattice_general`).  The passage is formal: `S = (freeCoverSES N).map F` is the
restriction to `H = ⟨σ̄⟩` of the canonical presentation `0 → N₁ → F → N → 0` (short exact, with
projective middle term because `F` is free over `ℤ[G]`), the syzygy shift
`e1aShiftEquiv S hS` identifies `Ext²_H(N,·)` with `Ext¹_H(N₁,·)`, and the coefficient-naturality of
the shift (`ExtChain.e1aShiftEquiv_natural_coeff`) carries the idèle-localisation vanishing across
that identification in both directions. -/
theorem hbnC2_of_hasseExt1_syzygy {k : Type} [Field k] [NumberField k] {Ω : Type} [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] {K : IntermediateField k Ω} [FiniteDimensional k K]
    [IsGalois k K] [NumberField K]
    (N : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Finite N.V]
    (σ : Ω ≃ₐ[k] Ω) (hσ : σ ^ 2 = 1) (hnt : SSGRoute.res k K σ ≠ 1)
    (h : ∀ z : CategoryTheory.Abelian.Ext.{0}
        (Rep.res (Subgroup.zpowers (SSGRoute.res k K σ)).subtype
          (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N)))
        (Rep.res (Subgroup.zpowers (SSGRoute.res k K σ)).subtype
          (SSGRoute.PTExt.unitsK k ↥K)) 1,
      z.comp (CategoryTheory.Abelian.Ext.mk₀
          (Rep.resMap (Subgroup.zpowers (SSGRoute.res k K σ)).subtype
            (NK.HassePrinciple.ideleIncl k ↥K))) (add_zero 1) = 0 → z = 0)
    (z : CategoryTheory.Abelian.Ext.{0}
        (Rep.res (Subgroup.zpowers (SSGRoute.res k K σ)).subtype N)
        (Rep.res (Subgroup.zpowers (SSGRoute.res k K σ)).subtype
          (SSGRoute.PTExt.unitsK k ↥K)) 2)
    (hz : z.comp (CategoryTheory.Abelian.Ext.mk₀
          (Rep.resMap (Subgroup.zpowers (SSGRoute.res k K σ)).subtype
            (NK.HassePrinciple.ideleIncl k ↥K))) (add_zero 2) = 0) :
    z = 0 := by
  classical
  let F : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) ⥤
      Rep.{0} SSGRoute.PTExt.Coeff ↥(Subgroup.zpowers (SSGRoute.res k K σ)) :=
    Rep.resFunctor (Subgroup.zpowers (SSGRoute.res k K σ)).subtype
  have hS : ((Work.SSGRoute.freeCoverSES N).map F).ShortExact :=
    (Work.SSGRoute.freeCoverSES_shortExact N).map_of_exact F
  haveI : CategoryTheory.Projective ((Work.SSGRoute.freeCoverSES N).map F).X₂ :=
    Work.SSGRoute.res_free_rep_projective (Subgroup.zpowers (SSGRoute.res k K σ)) N.V
  set w : CategoryTheory.Abelian.Ext.{0} ((Work.SSGRoute.freeCoverSES N).map F).X₁
      (Rep.res (Subgroup.zpowers (SSGRoute.res k K σ)).subtype (SSGRoute.PTExt.unitsK k ↥K)) 1 :=
    (Work.SSGRoute.PT.e1aShiftEquiv ((Work.SSGRoute.freeCoverSES N).map F) hS
      (Rep.res (Subgroup.zpowers (SSGRoute.res k K σ)).subtype (SSGRoute.PTExt.unitsK k ↥K))
      1 (le_refl 1)).symm z with hw
  have hzw : Work.SSGRoute.PT.e1aShiftEquiv ((Work.SSGRoute.freeCoverSES N).map F) hS
      (Rep.res (Subgroup.zpowers (SSGRoute.res k K σ)).subtype (SSGRoute.PTExt.unitsK k ↥K))
      1 (le_refl 1) w = z := by
    rw [hw]
    exact AddEquiv.apply_symm_apply _ z
  have key := Work.SSGRoute.ExtChain.e1aShiftEquiv_natural_coeff hS
    (Rep.res (Subgroup.zpowers (SSGRoute.res k K σ)).subtype (SSGRoute.PTExt.unitsK k ↥K))
    (Rep.res (Subgroup.zpowers (SSGRoute.res k K σ)).subtype (SSGRoute.PTExt.idelesK k ↥K))
    (Rep.resMap (Subgroup.zpowers (SSGRoute.res k K σ)).subtype
      (NK.HassePrinciple.ideleIncl k ↥K)) 1 (le_refl 1) w
  rw [hzw] at key
  have hkey : (Work.SSGRoute.PT.e1aShiftEquiv ((Work.SSGRoute.freeCoverSES N).map F) hS
      (Rep.res (Subgroup.zpowers (SSGRoute.res k K σ)).subtype (SSGRoute.PTExt.idelesK k ↥K))
      1 (le_refl 1)) (w.comp (CategoryTheory.Abelian.Ext.mk₀
        (Rep.resMap (Subgroup.zpowers (SSGRoute.res k K σ)).subtype
          (NK.HassePrinciple.ideleIncl k ↥K))) (add_zero 1)) = 0 := key.symm.trans hz
  have hw1 : w.comp (CategoryTheory.Abelian.Ext.mk₀
        (Rep.resMap (Subgroup.zpowers (SSGRoute.res k K σ)).subtype
          (NK.HassePrinciple.ideleIncl k ↥K))) (add_zero 1) = 0 :=
    (Work.SSGRoute.PT.e1aShiftEquiv ((Work.SSGRoute.freeCoverSES N).map F) hS
      (Rep.res (Subgroup.zpowers (SSGRoute.res k K σ)).subtype (SSGRoute.PTExt.idelesK k ↥K))
      1 (le_refl 1)).injective (by rw [hkey, map_zero])
  have hw0 : w = 0 := h w hw1
  rw [← hzw, hw0]
  exact map_zero _

/-- **The quadratic Hasse principle from the general degree-one Hasse principle for `ℤ`-lattices.**
The canonical syzygy `N₁ = ker (freeCover N)` is a `ℤ`-lattice (`ExtChain.freeCoverSES_lattice`,
`Work.SSGRoute.freeCoverSES_finite`, both available for `N = e1aN0 …`), so
`ExtChain.hasseExt1_C2_lattice_general` covers it and
`ExtChain.hbnC2_of_hasseExt1_syzygy` finishes.  This is the exact seam between the fleet's general
lattice delegation and the involution half. -/
theorem hbnC2_of_hasseExt1_lattice {k : Type} [Field k] [NumberField k] {Ω : Type} [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] {K : IntermediateField k Ω} [FiniteDimensional k K]
    [IsGalois k K] [NumberField K]
    (N : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Finite N.V]
    (σ : Ω ≃ₐ[k] Ω) (hσ : σ ^ 2 = 1) (hnt : SSGRoute.res k K σ ≠ 1)
    (h : ∀ (M : Rep.{0} SSGRoute.PTExt.Coeff ↥(Subgroup.zpowers (SSGRoute.res k K σ)))
        [Module.Finite ℤ M.V] [Module.Free ℤ M.V],
      ∀ z : CategoryTheory.Abelian.Ext.{0} M
        (Rep.res (Subgroup.zpowers (SSGRoute.res k K σ)).subtype
          (SSGRoute.PTExt.unitsK k ↥K)) 1,
      z.comp (CategoryTheory.Abelian.Ext.mk₀
          (Rep.resMap (Subgroup.zpowers (SSGRoute.res k K σ)).subtype
            (NK.HassePrinciple.ideleIncl k ↥K))) (add_zero 1) = 0 → z = 0)
    (z : CategoryTheory.Abelian.Ext.{0}
        (Rep.res (Subgroup.zpowers (SSGRoute.res k K σ)).subtype N)
        (Rep.res (Subgroup.zpowers (SSGRoute.res k K σ)).subtype
          (SSGRoute.PTExt.unitsK k ↥K)) 2)
    (hz : z.comp (CategoryTheory.Abelian.Ext.mk₀
          (Rep.resMap (Subgroup.zpowers (SSGRoute.res k K σ)).subtype
            (NK.HassePrinciple.ideleIncl k ↥K))) (add_zero 2) = 0) :
    z = 0 := by
  classical
  haveI : Fintype (K ≃ₐ[k] K) := inferInstance
  haveI hfin : Module.Finite ℤ (Rep.res (Subgroup.zpowers (SSGRoute.res k K σ)).subtype
      (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N))).V :=
    Work.SSGRoute.freeCoverSES_finite N
  haveI hfree : Module.Free ℤ (Rep.res (Subgroup.zpowers (SSGRoute.res k K σ)).subtype
      (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N))).V :=
    Work.SSGRoute.ExtChain.freeCoverSES_lattice N
  exact hbnC2_of_hasseExt1_syzygy N σ hσ hnt (fun z hz => h _ z hz) z hz

/-- **The `G`-level involution input from the general lattice Hasse principle**: composition of
`ExtChain.hbnC2_of_hasseExt1_lattice` (the lattice/syzygy seam) with
`ExtChain.extRes_zpowers_eq_zero_of_quadraticHasse` (the class-formation long exact sequence).
With this, the *only* arithmetic statement standing between the general `ℂ₂`-lattice Hasse principle
and the target is that lattice principle itself. -/
theorem extRes_zpowers_eq_zero_of_latticeHasse {k : Type} [Field k] [NumberField k] {Ω : Type}
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] {K : IntermediateField k Ω} [FiniteDimensional k K]
    [IsGalois k K] [NumberField K]
    (N : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Finite N.V]
    (σ : Ω ≃ₐ[k] Ω) (hσ : σ ^ 2 = 1) (hnt : SSGRoute.res k K σ ≠ 1)
    (h : ∀ (M : Rep.{0} SSGRoute.PTExt.Coeff ↥(Subgroup.zpowers (SSGRoute.res k K σ)))
        [Module.Finite ℤ M.V] [Module.Free ℤ M.V],
      ∀ z : CategoryTheory.Abelian.Ext.{0} M
        (Rep.res (Subgroup.zpowers (SSGRoute.res k K σ)).subtype
          (SSGRoute.PTExt.unitsK k ↥K)) 1,
      z.comp (CategoryTheory.Abelian.Ext.mk₀
          (Rep.resMap (Subgroup.zpowers (SSGRoute.res k K σ)).subtype
            (NK.HassePrinciple.ideleIncl k ↥K))) (add_zero 1) = 0 → z = 0)
    (y : CategoryTheory.Abelian.Ext.{0} N (SSGRoute.PTExt.unitsK k ↥K) 2)
    (hy : SSGRoute.PTExt.extToIdeles (k := k) y = 0) :
    SSGRoute.PTExt.extRes (Subgroup.zpowers (SSGRoute.res k K σ)).subtype y = 0 :=
  extRes_zpowers_eq_zero_of_quadraticHasse N σ hσ hnt
    (hbnC2_of_hasseExt1_lattice N σ hσ hnt h) y hy

/-- **The Γ-level involution input from the general lattice Hasse principle**: the previous lemma
composed with the involutive restriction square
`ExtChain.resH2_zpowers_e1aChainH_eq_zero_of_extRes_zpowers_eq_zero`.  This is the target's
involution half, hypothesis-free except for the lattice Hasse principle. -/
theorem himg_involution_input_two_of_latticeHasse {k : Type} [Field k] [NumberField k] {Ω : Type}
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] {K : IntermediateField k Ω} [FiniteDimensional k K]
    [IsGalois k K] [NumberField K]
    (N : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Finite N.V]
    (σ : Ω ≃ₐ[k] Ω) (hσ : σ ^ 2 = 1) (hnt : SSGRoute.res k K σ ≠ 1)
    (h : ∀ (M : Rep.{0} SSGRoute.PTExt.Coeff ↥(Subgroup.zpowers (SSGRoute.res k K σ)))
        [Module.Finite ℤ M.V] [Module.Free ℤ M.V],
      ∀ z : CategoryTheory.Abelian.Ext.{0} M
        (Rep.res (Subgroup.zpowers (SSGRoute.res k K σ)).subtype
          (SSGRoute.PTExt.unitsK k ↥K)) 1,
      z.comp (CategoryTheory.Abelian.Ext.mk₀
          (Rep.resMap (Subgroup.zpowers (SSGRoute.res k K σ)).subtype
            (NK.HassePrinciple.ideleIncl k ↥K))) (add_zero 1) = 0 → z = 0)
    (y : CategoryTheory.Abelian.Ext.{0} N (SSGRoute.PTExt.unitsK k ↥K) 2)
    (hy : SSGRoute.PTExt.extToIdeles (k := k) y = 0) :
    Work.SSGRoute.PT.resH2 (Subgroup.zpowers σ)
      (Work.SSGRoute.PT.e1aChainH (k := k) (Ω := Ω) (K := K) N y) = 0 :=
  resH2_zpowers_e1aChainH_eq_zero_of_extRes_zpowers_eq_zero (k := k) (Ω := Ω) (K := K)
    (N := N) σ hσ hnt y
    (extRes_zpowers_eq_zero_of_latticeHasse N σ hσ hnt h y hy)

/-- **The `p ≠ 2` case of the involution input — a `Subsingleton` argument.**

For `p ≠ 2` the coefficient `homCoind k Ω K (e1aN0 …)` is a module on which `|⟨σ⟩|` acts invertibly
(`|⟨σ⟩| ∣ 2` and `2` is a unit of `ZMod p`; the bijectivity is transported from `E` along the
canonical coefficient identification `e1aCoeffNat`), so the trace/idempotent argument of
`Work.GroupCohomology.Z2_le_B2_of_card_smul_bijective` (packaged as
`ExtChain.subsingleton_H2_abs_of_fintype_card_smul_bijective`) makes `H²(⟨σ⟩, homCoind …)` a
subsingleton.  Hence the restricted chain class vanishes *for every* `y`, and the involution input
is vacuous in odd characteristic — the whole content of `himg_involution_input` is `p = 2`.

(This is the extraction of the `hbij`/`hsub` block inside the proof of
`ExtChain.himgExtDeltaInput_inf_odd`; it is delegated as
`ExtChain.subsingleton_H2_zpowers_homCoind_odd`.) -/
theorem himg_involution_input_odd (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (k Ω : Type) [Field k]
    [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [NumberField K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    [hNfin : Finite (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E).V]
    (σ : Ω ≃ₐ[k] Ω) (hσ : σ ^ 2 = 1) (hnt : SSGRoute.res k K σ ≠ 1)
    (y : CategoryTheory.Abelian.Ext.{0} (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E)
      (SSGRoute.PTExt.unitsK k K) 2)
    (hy : SSGRoute.PTExt.extToIdeles (k := k) y = 0) :
    Work.SSGRoute.PT.resH2 (Subgroup.zpowers σ)
      (Work.SSGRoute.PT.e1aChainH (k := k) (Ω := Ω) (K := K)
        (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E) y) = 0 := by
  haveI : Subsingleton (Work.AbsoluteKummer.H2 ↥(Subgroup.zpowers σ)
      (Work.SSGRoute.homCoind k Ω K (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E))) :=
    Work.SSGRoute.ExtChain.subsingleton_H2_zpowers_homCoind_odd p hp k Ω K ζ hζ hζK T hT E σ hσ
  exact Subsingleton.elim _ _

/-- **The `p = 2` case of the involution input — the prime-2 correction, now proved from the
`ℂ₂`-lattice Hasse principle.**

This was the crux of the lane (§9.1/§9.2 of `NOTE_himgIdelesInput_inf_reduction.md`,
`NOTE_himgIdelesInput_inf_quadraticHasse_route.md`).  It is discharged here by the chain built in
this file:

1. `ExtChain.himg_involution_input_two_of_latticeHasse` — the Γ-level involution input follows from
   the **general quadratic (`ℂ₂`) Hasse principle with `ℤ`-lattice coefficients**
   (`ExtChain.hasseExt1_C2_lattice_general`, proved) plus the involutive restriction square
   (`ExtChain.resH2_zpowers_e1aChainH_eq_zero_of_extRes_zpowers_eq_zero`, proved);
2. whose interior is the syzygy wiring `ExtChain.hbnC2_of_hasseExt1_lattice`
   (via `ExtChain.hbnC2_of_hasseExt1_syzygy`, the canonical presentation `0 → N₁ → F → N` restricted
   to `H = ⟨σ̄⟩`, with the coefficient-naturality `ExtChain.e1aShiftEquiv_natural_coeff`) followed by
   the class-formation long exact sequence `ExtChain.extRes_zpowers_eq_zero_of_quadraticHasse`.

Note that the hypothesis `hp : p = 2` is *not* used: the reduction is uniform in `p` (the split in
`p` was only ever about which Hasse input is available; for odd `p`
`ExtChain.himg_involution_input_odd` remains a shorter proof). -/
theorem himg_involution_input_two (p : ℕ) [Fact p.Prime] (hp : p = 2) (k Ω : Type) [Field k]
    [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [NumberField K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    [hNfin : Finite (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E).V]
    (σ : Ω ≃ₐ[k] Ω) (hσ : σ ^ 2 = 1) (hnt : SSGRoute.res k K σ ≠ 1)
    (y : CategoryTheory.Abelian.Ext.{0} (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E)
      (SSGRoute.PTExt.unitsK k K) 2)
    (hy : SSGRoute.PTExt.extToIdeles (k := k) y = 0) :
    Work.SSGRoute.PT.resH2 (Subgroup.zpowers σ)
      (Work.SSGRoute.PT.e1aChainH (k := k) (Ω := Ω) (K := K)
        (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E) y) = 0 :=
  himg_involution_input_two_of_latticeHasse
    (N := Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E) σ hσ hnt
    (Work.SSGRoute.ExtChain.hasseExt1_C2_lattice_general p k Ω K σ hσ hnt) y hy

/-- **The degree-two local–global input of the involution family (the missing chapter).**

With `N = e1aN0 p k Ω K T E` and `y ∈ Ext²_G(N, Kˣ)` whose idèle localisation vanishes
(`hy : extToIdeles y = 0` — i.e. `y` is locally trivial at *every* place of `K`), the canonical
chain class `e1aChainH N y ∈ H²(Γ, Hom_ℤ(N,Ωˣ))` has zero restriction to `⟨σ⟩`.

This is *not* a per-place statement (see `NOTE_himgIdelesInput_inf_reduction.md` §3: `Ext²` of a
`p`-torsion module is not `H²` of its `Hom`-module, the `Ext¹_ℤ`-piece `Kˣ/(Kˣ)^p` survives
localisation, so no single place sees it).  Its designed proof is the **dévissage in the
coefficient `E`** of `ExtChain/NOTE_himgExtDelta_session13.md` §3bis: the case `E = 𝔽_p[G]`
(free, dual to a free module, `Ext²_G` vanishes by Shapiro/Hilbert 90) is vacuous, the naturality
squares in `E` are `e1aChainC_natural`/`Sha2Map`/`extToIdeles`-naturality, and the inductive step is
a *degree-one* local–global statement, which is on disk as
`Work.SSGRoute.hassePrinciple_h1_cocycles`. -/
theorem himg_involution_input (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [NumberField K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    [hNfin : Finite (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E).V]
    (σ : Ω ≃ₐ[k] Ω) (hσ : σ ^ 2 = 1) (hnt : SSGRoute.res k K σ ≠ 1)
    (y : CategoryTheory.Abelian.Ext.{0} (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E)
      (SSGRoute.PTExt.unitsK k K) 2)
    (hy : SSGRoute.PTExt.extToIdeles (k := k) y = 0) :
    Work.SSGRoute.PT.resH2 (Subgroup.zpowers σ)
      (Work.SSGRoute.PT.e1aChainH (k := k) (Ω := Ω) (K := K)
        (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E) y) = 0 := by
  rcases eq_or_ne p 2 with h2 | h2
  · exact himg_involution_input_two p h2 k Ω K ζ hζ hζK T hT E σ hσ hnt y hy
  · exact himg_involution_input_odd p h2 k Ω K ζ hζ hζK T hT E σ hσ hnt y hy

/-- **The involution half of the `himg` input, in hypothesis form.** -/
theorem himgIdelesInput_inf (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [NumberField K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    [hRfin : Module.Finite ℤ ↥(CategoryTheory.Limits.kernel
      (Work.SSGRoute.freeCover (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E)))]
    (z : CategoryTheory.Abelian.Ext.{0}
      (CategoryTheory.Limits.kernel
        (Work.SSGRoute.freeCover (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E)))
      (SSGRoute.PTExt.unitsK k K) 1)
    (hz : SSGRoute.PTExt.extToIdeles (k := k)
      (Work.SSGRoute.ExtChain.e1aSyzShift (k := k) (K := K)
        (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E) z) = 0)
    (σ : Ω ≃ₐ[k] Ω) (hσ : σ ^ 2 = 1) (hnt : SSGRoute.res k K σ ≠ 1) :
    Work.SSGRoute.PT.H2Fin.resH1 (Subgroup.zpowers σ)
      (Work.SSGRoute.homCoind k Ω K
        (CategoryTheory.Limits.kernel
          (Work.SSGRoute.freeCover (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E))))
      (Work.SSGRoute.ExtChain.e1cMap
        (CategoryTheory.Limits.kernel
          (Work.SSGRoute.freeCover (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E))) z) = 0 := by
  haveI := hRfin
  haveI hTfin : Finite T := Work.SSGRoute.ExtChain.e1aFiniteT p k Ω K ζ T hT
  haveI hNfin : Finite (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E).V :=
    Work.SSGRoute.PT.finite_dualMod_tensor p E T
  refine resH1_zpowers_e1cMap_eq_zero_of_resH2_e1aChainH_eq_zero
    (k := k) (Ω := Ω) (K := K)
    (N := Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E) σ hσ z ?_
  exact himg_involution_input p k Ω K ζ hζ hζK T hT E σ hσ hnt
    (Work.SSGRoute.ExtChain.e1aSyzShift (k := k) (K := K)
      (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E) z) hz

end Work.SSGRoute.ExtChain
