import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.PT.vfShared

namespace Work.SSGRoute.PT

set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-- **Additivity of the level class in the representing cocycle.**  `levelClassOf` (`PT/vfShared`)
is the class in `Ext¹_{Gal(L/k)}(ℤ, res M')` of a level-`L` `1`-cocycle `ψ`; it is additive in `ψ`.
Proof: `levelClassOf ψ hψ = gammaHom (H1π ⟨ψ, hψ⟩)`, both `H1π` and `gammaHom` being `AddMonoidHom`s,
and `⟨ψ + ψ', _⟩ = ⟨ψ, _⟩ + ⟨ψ', _⟩` by `Subtype.ext rfl` (subtype addition is pointwise). -/
theorem levelClassOf_add (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [NumberField K]
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (L : IntermediateField k Ω) [NumberField ↥L] [FiniteDimensional k ↥L] [IsGalois k ↥L]
    (hKL : K ≤ L) [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω]
    (ψ ψ' : (↥L ≃ₐ[k] ↥L) → Work.SSGRoute.PT.VFcoef p M T)
    (hψ : ∀ g h : ↥L ≃ₐ[k] ↥L, ψ (g * h) = SSGRoute.PTExt.galRes k (↥K) (↥L) g • ψ h + ψ g)
    (hψ' : ∀ g h : ↥L ≃ₐ[k] ↥L, ψ' (g * h) = SSGRoute.PTExt.galRes k (↥K) (↥L) g • ψ' h + ψ' g)
    (hψadd : ∀ g h : ↥L ≃ₐ[k] ↥L,
      (ψ + ψ') (g * h) = SSGRoute.PTExt.galRes k (↥K) (↥L) g • (ψ + ψ') h + (ψ + ψ') g) :
    Work.SSGRoute.PT.levelClassOf p k Ω K T M L (ψ + ψ') hψadd
      = Work.SSGRoute.PT.levelClassOf p k Ω K T M L ψ hψ
        + Work.SSGRoute.PT.levelClassOf p k Ω K T M L ψ' hψ' := by
  letI hAct : DistribMulAction (↥L ≃ₐ[k] ↥L) (VFcoef p M T) :=
    DistribMulAction.compHom (VFcoef p M T) (SSGRoute.PTExt.galRes k (↥K) (↥L))
  haveI hCommZ : SMulCommClass (↥L ≃ₐ[k] ↥L) ℤ (VFcoef p M T) :=
    ⟨fun g n m =>
      map_zsmul (AddMonoidHom.mk' (fun m => g • m) (fun a b => smul_add g a b)) n m⟩
  haveI hCommC : SMulCommClass (↥L ≃ₐ[k] ↥L) SSGRoute.PTExt.Coeff (VFcoef p M T) :=
    ⟨fun g c m => smul_comm g c.down m⟩
  rw [show levelClassOf p k Ω K T M L (ψ + ψ') hψadd
      = Work.SSGRoute.ExtH1.gammaZ1 (↥L ≃ₐ[k] ↥L) (VFcoef p M T)
          (Work.SSGRoute.augSES_shortExact (↥L ≃ₐ[k] ↥L)) ⟨ψ + ψ', hψadd⟩ from
    Work.SSGRoute.ExtH1.gammaHom_H1π (↥L ≃ₐ[k] ↥L) (VFcoef p M T)
      (Work.SSGRoute.augSES_shortExact (↥L ≃ₐ[k] ↥L)) ⟨ψ + ψ', hψadd⟩,
    show levelClassOf p k Ω K T M L ψ hψ
      = Work.SSGRoute.ExtH1.gammaZ1 (↥L ≃ₐ[k] ↥L) (VFcoef p M T)
          (Work.SSGRoute.augSES_shortExact (↥L ≃ₐ[k] ↥L)) ⟨ψ, hψ⟩ from
    Work.SSGRoute.ExtH1.gammaHom_H1π (↥L ≃ₐ[k] ↥L) (VFcoef p M T)
      (Work.SSGRoute.augSES_shortExact (↥L ≃ₐ[k] ↥L)) ⟨ψ, hψ⟩,
    show levelClassOf p k Ω K T M L ψ' hψ'
      = Work.SSGRoute.ExtH1.gammaZ1 (↥L ≃ₐ[k] ↥L) (VFcoef p M T)
          (Work.SSGRoute.augSES_shortExact (↥L ≃ₐ[k] ↥L)) ⟨ψ', hψ'⟩ from
    Work.SSGRoute.ExtH1.gammaHom_H1π (↥L ≃ₐ[k] ↥L) (VFcoef p M T)
      (Work.SSGRoute.augSES_shortExact (↥L ≃ₐ[k] ↥L)) ⟨ψ', hψ'⟩,
    show (⟨ψ + ψ', hψadd⟩ : ↥(Work.GroupCohomology.Z1 (↥L ≃ₐ[k] ↥L) (VFcoef p M T)))
      = (⟨ψ, hψ⟩ : ↥(Work.GroupCohomology.Z1 (↥L ≃ₐ[k] ↥L) (VFcoef p M T)))
        + ⟨ψ', hψ'⟩ from Subtype.ext rfl,
    map_add]
  rfl

end Work.SSGRoute.PT
