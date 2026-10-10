import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.PT.G1plusOwn.levelFree
import Submission.Work.SSGRoute.PT.finZH_levelChange_fix
import Submission.Work.SSGRoute.localSumDecomposition
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! Shared definitions for the value-formula node `Work.SSGRoute.PT.valueFormula_abstract`
(and for the sub-lemmas about it that are delegated in parallel). -/

namespace Work.SSGRoute.PT

open scoped TensorProduct Pointwise
open SSGRoute.PTExt CategoryTheory

set_option maxHeartbeats 8000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

/-- The coefficient module `M' = DualMod p (M ⊗[ZMod p] T)` of the value formula. -/
abbrev VFcoef (p : ℕ) (M T : Type) [AddCommGroup M] [Module (ZMod p) M] [AddCommGroup T]
    [Module (ZMod p) T] : Type := Work.SSGRoute.DualMod p (M ⊗[ZMod p] T)

section SharedCtx

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
  [NumberField K]
  (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
  (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
  (L : IntermediateField k Ω) [NumberField ↥L] [FiniteDimensional k ↥L] [IsGalois k ↥L]
  (hKL : K ≤ L) [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω]

/-- **The class at the level `L` of a level-`L` `1`-cocycle**, in the spelling
`Ext¹_{Gal(L/k)}(ℤ, res M')` of the value formula (the action of `Gal(L/k)` on `M'` being the
pull-back of the `Gal(K/k)`-action along `galRes`). -/
noncomputable def levelClassOf (ψ : (↥L ≃ₐ[k] ↥L) → VFcoef p M T)
    (hψ : ∀ g h : ↥L ≃ₐ[k] ↥L, ψ (g * h) = SSGRoute.PTExt.galRes k (↥K) (↥L) g • ψ h + ψ g) :
    SSGRoute.PTExt.extH (Rep.res (SSGRoute.PTExt.galRes k (↥K) (↥L))
      (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) (VFcoef p M T))) 1 := by
  letI hAct : DistribMulAction (↥L ≃ₐ[k] ↥L) (VFcoef p M T) :=
    DistribMulAction.compHom (VFcoef p M T) (SSGRoute.PTExt.galRes k (↥K) (↥L))
  haveI hCommZ : SMulCommClass (↥L ≃ₐ[k] ↥L) ℤ (VFcoef p M T) :=
    ⟨fun g n m =>
      map_zsmul (AddMonoidHom.mk' (fun m => g • m) (fun a b => smul_add g a b)) n m⟩
  haveI hCommC : SMulCommClass (↥L ≃ₐ[k] ↥L) SSGRoute.PTExt.Coeff (VFcoef p M T) :=
    ⟨fun g c m => smul_comm g c.down m⟩
  exact Work.SSGRoute.ExtH1.gammaHom (↥L ≃ₐ[k] ↥L) (VFcoef p M T)
    (Work.SSGRoute.augSES_shortExact (↥L ≃ₐ[k] ↥L))
    (Work.GroupCohomology.H1π (↥L ≃ₐ[k] ↥L) (VFcoef p M T)
      ⟨ψ, fun g h => hψ g h⟩)

/-- **A representative cocycle of a level-`L` class.**

Every class `h ∈ Ext¹_{Gal(L/k)}(ℤ, res M')` is the class of a `1`-cocycle `ψ` at the level `L`
(`gammaHom` is surjective and `H1π` is the quotient map), and restricting `ψ` to the level `L` of
`Ω` gives a globally defined, locally constant `1`-cocycle `b` on `Gal(Ω/k)`. -/
lemma vf_exists_rep
    (h : SSGRoute.PTExt.extH (Rep.res (SSGRoute.PTExt.galRes k (↥K) (↥L))
      (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) (VFcoef p M T))) 1) :
    ∃ (ψ : (↥L ≃ₐ[k] ↥L) → VFcoef p M T)
      (hψ : ∀ g g' : ↥L ≃ₐ[k] ↥L,
        ψ (g * g') = SSGRoute.PTExt.galRes k (↥K) (↥L) g • ψ g' + ψ g)
      (b : (Ω ≃ₐ[k] Ω) → VFcoef p M T),
      (∀ σ : Ω ≃ₐ[k] Ω, b σ = ψ (SSGRoute.res k L σ)) ∧
      h = levelClassOf (p := p) (k := k) (Ω := Ω) (K := K) (L := L) (T := T) (M := M) ψ hψ ∧
      SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b ∧
      SSGRoute.IsLocConstOn ⊤ b := by
  classical
  letI hAct : DistribMulAction (↥L ≃ₐ[k] ↥L) (VFcoef p M T) :=
    DistribMulAction.compHom (VFcoef p M T) (SSGRoute.PTExt.galRes k (↥K) (↥L))
  haveI hCommZ : SMulCommClass (↥L ≃ₐ[k] ↥L) ℤ (VFcoef p M T) :=
    ⟨fun g n m =>
      map_zsmul (AddMonoidHom.mk' (fun m => g • m) (fun a b => smul_add g a b)) n m⟩
  haveI hCommC : SMulCommClass (↥L ≃ₐ[k] ↥L) SSGRoute.PTExt.Coeff (VFcoef p M T) :=
    ⟨fun g c m => smul_comm g c.down m⟩
  obtain ⟨x, hx⟩ := Work.SSGRoute.ExtH1.gammaHom_surjective (↥L ≃ₐ[k] ↥L) (VFcoef p M T)
    (Work.SSGRoute.augSES_shortExact (↥L ≃ₐ[k] ↥L)) h
  obtain ⟨ψ₀, hψ₀⟩ : ∃ ψ : ↥(Work.GroupCohomology.Z1 (↥L ≃ₐ[k] ↥L) (VFcoef p M T)),
      Work.GroupCohomology.H1π (↥L ≃ₐ[k] ↥L) (VFcoef p M T) ψ = x :=
    QuotientAddGroup.mk'_surjective _ x
  have hclass : h = levelClassOf (p := p) (k := k) (Ω := Ω) (K := K) (L := L) (T := T)
      (M := M) ψ₀.1 (fun g h => ψ₀.2 g h) := by
    rw [← hx, ← hψ₀]
    exact congrArg (fun z : ↥(Work.GroupCohomology.Z1 (↥L ≃ₐ[k] ↥L) (VFcoef p M T)) =>
      Work.SSGRoute.ExtH1.gammaHom (↥L ≃ₐ[k] ↥L) (VFcoef p M T)
        (Work.SSGRoute.augSES_shortExact (↥L ≃ₐ[k] ↥L))
        (Work.GroupCohomology.H1π (↥L ≃ₐ[k] ↥L) (VFcoef p M T) z)) (Subtype.ext rfl)
  have hresK : ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.res k K σ
      = SSGRoute.PTExt.galRes k (↥K) (↥L) (SSGRoute.res k L σ) := by
    intro σ
    exact (SSGRoute.PTExt.galRes_trans (k := k) (K := ↥K) (L := ↥L) (L' := Ω) σ).symm
  have hcoc : SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤
      (fun σ : Ω ≃ₐ[k] Ω => ψ₀.1 (SSGRoute.res k L σ)) := by
    intro σ _ τ _
    show ψ₀.1 (SSGRoute.res k L (σ * τ)) = ψ₀.1 (SSGRoute.res k L σ)
      + SSGRoute.res k K σ • ψ₀.1 (SSGRoute.res k L τ)
    rw [map_mul, hresK σ, ψ₀.2]
    have hsm : (SSGRoute.res k L) σ • ψ₀.1 ((SSGRoute.res k L) τ)
        = SSGRoute.PTExt.galRes k (↥K) (↥L) ((SSGRoute.res k L) σ)
            • ψ₀.1 ((SSGRoute.res k L) τ) := rfl
    rw [hsm, add_comm]
  have hloc : SSGRoute.IsLocConstOn ⊤
      (fun σ : Ω ≃ₐ[k] Ω => ψ₀.1 (SSGRoute.res k L σ)) := by
    refine ⟨(SSGRoute.res k L).ker, ?_, ?_⟩
    · rw [show SSGRoute.res k L = AlgEquiv.restrictNormalHom ↥L from rfl,
        IntermediateField.restrictNormalHom_ker]
      exact IntermediateField.fixingSubgroup_isOpen L
    · intro g _ u hu _
      show ψ₀.1 (SSGRoute.res k L (g * u)) = ψ₀.1 (SSGRoute.res k L g)
      rw [map_mul, MonoidHom.mem_ker.mp hu, mul_one]
  exact ⟨ψ₀.1, fun g h => ψ₀.2 g h, fun σ => ψ₀.1 (SSGRoute.res k L σ),
    fun σ => rfl, hclass, hcoc, hloc⟩

/-- The place glue `finZF` is the restriction map on decomposition groups of the places
`finQW L A` and `finQ K A`. -/
theorem vf_finZF_eq (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) :
    Work.SSGRoute.PT.finZF hKL A hA
      = SSGRoute.decompKRestrict k (↥K) (↥L)
          (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA))
          (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW L A hA))
          (NK.GlobalCFT.Place.liesOver_ofFinite
            (asIdeal_liesOver_of_valuation_lt_one K L A (Work.SSGRoute.PT.finQ K A hA)
              (fun x => Work.SSGRoute.PT.finQ_spec K A hA x)
              (Work.SSGRoute.PT.finQW L A hA)
              (fun y => Work.SSGRoute.PT.finQW_spec L A hA y))) := by
  apply MonoidHom.ext
  intro σ
  apply Subtype.ext
  rw [Work.SSGRoute.PT.finZF_spec hKL A hA σ, SSGRoute.decompKRestrict_coe]

end SharedCtx

end Work.SSGRoute.PT
