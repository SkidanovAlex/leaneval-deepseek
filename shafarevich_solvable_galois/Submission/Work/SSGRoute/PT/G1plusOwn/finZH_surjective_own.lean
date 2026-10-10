import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.PT.G1plusOwn.levelFree
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PT.G1plusOwn

open scoped TensorProduct Pointwise
open SSGRoute.PTExt CategoryTheory

set_option maxHeartbeats 8000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

/-- The class of any `finZH` is realised by a locally constant cocycle on `decomp k A` (an own,
performance-fixed copy of `finZH_surjective`). -/
theorem finZH_surjective_own
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
    (hKL : K ≤ L)
    [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω]
    (h : SSGRoute.PTExt.extH (Rep.res (Work.SSGRoute.PT.finZF hKL A hA)
        (Rep.res (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA))).subtype
          (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) (Work.SSGRoute.DualMod p (M ⊗[ZMod p] T))))) 1) :
    ∃ (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (M ⊗[ZMod p] T))
      (b₀ : (↥L ≃ₐ[k] ↥L) → Work.SSGRoute.DualMod p (M ⊗[ZMod p] T)),
      SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b ∧
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b ∧
      (∀ σ ∈ SSGRoute.decomp k A, b σ = b₀ (AlgEquiv.restrictNormalHom L σ)) ∧
      (∀ (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b)
        (hb₀ : ∀ σ ∈ SSGRoute.decomp k A, b σ = b₀ (AlgEquiv.restrictNormalHom L σ)),
        Work.SSGRoute.PT.finZH p K T M L hKL A hA b hb b₀ hb₀ = h) := by
  classical
  -- ## The level data attached to `A`, `K`, `L`.
  let q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K) :=
    Work.SSGRoute.PT.finQ K A hA
  let w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L) :=
    Work.SSGRoute.PT.finQW L A hA
  let Dw : Subgroup (↥L ≃ₐ[k] ↥L) := decompK (k := k) (NK.GlobalCFT.Place.ofFinite w)
  let X := Work.SSGRoute.DualMod p (M ⊗[ZMod p] T)
  let φ₀ : Dw →* (↥K ≃ₐ[k] ↥K) := (decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype.comp
    (Work.SSGRoute.PT.finZF hKL A hA)
  -- ## The `D_w`-module structure on `X` used by `finLevelClass`.
  haveI hCommZ : SMulCommClass (↥K ≃ₐ[k] ↥K) ℤ X :=
    ⟨fun g n m => map_zsmul (AddMonoidHom.mk' (fun m => g • m) (fun a b => smul_add g a b)) n m⟩
  haveI hCommC : SMulCommClass (↥K ≃ₐ[k] ↥K) Coeff X :=
    ⟨fun g c m => smul_comm g c.down m⟩
  letI hAct : DistribMulAction Dw X := DistribMulAction.compHom X φ₀
  haveI hCommZp : SMulCommClass Dw (ZMod p) X := ⟨fun g c m => smul_comm (φ₀ g) c m⟩
  haveI hCommCp : SMulCommClass Dw Coeff X := ⟨fun g c m => smul_comm (φ₀ g) c m⟩
  -- ## A cocycle representing `h` at the level of `D_w`.
  -- `h` lives at the `Rep.res`-spelling of the target `Rep`, which is definitionally the
  -- `modRep D_w X` spelling used by `phiMap`.
  let hh : SSGRoute.PTExt.extH (SSGRoute.PTExt.modRep Dw X) 1 := h
  obtain ⟨f₀, hf₀⟩ :=
    (Work.SSGRoute.ExtH1.phiMap_surjective Dw X (Work.SSGRoute.augSES_shortExact Dw)) hh
  let c : Dw → X := Work.SSGRoute.ExtH1.derivCochain Dw f₀
  have hc : Work.SSGRoute.ExtH1.IsCrossedHom Dw c :=
    Work.SSGRoute.ExtH1.derivCochain_isCrossedHom Dw f₀
  have hcoc : Work.SSGRoute.ExtH1.cocycleHom Dw c hc = f₀ :=
    Work.SSGRoute.ExtH1.cocycleHom_derivCochain Dw f₀
  -- ## The witnesses.
  let b₀ : (↥L ≃ₐ[k] ↥L) → X := fun τ => if hτ : τ ∈ Dw then c ⟨τ, hτ⟩ else 0
  have hb₀coe : ∀ g : Dw, b₀ (g : ↥L ≃ₐ[k] ↥L) = c g := by
    intro g; simp only [b₀]; rw [dif_pos g.2]
  let b : (Ω ≃ₐ[k] Ω) → X := fun σ => b₀ (AlgEquiv.restrictNormalHom L σ)
  -- ## `b` is a cocycle on `decomp k A`.
  have hb₀_app : ∀ (τ : ↥L ≃ₐ[k] ↥L) (hτ : τ ∈ Dw), b₀ τ = c ⟨τ, hτ⟩ :=
    fun τ hτ => hb₀coe ⟨τ, hτ⟩
  have hcocyc : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b := by
    intro σ hσ τ hτ
    have hσw : AlgEquiv.restrictNormalHom L σ ∈ Dw := by
      rw [show Dw = decompK (k := k) (NK.GlobalCFT.Place.ofFinite w) from rfl,
        ← Work.SSGRoute.PT.finQW_glue L A hA]
      exact Subgroup.mem_map.mpr ⟨σ, hσ, rfl⟩
    have hτw : AlgEquiv.restrictNormalHom L τ ∈ Dw := by
      rw [show Dw = decompK (k := k) (NK.GlobalCFT.Place.ofFinite w) from rfl,
        ← Work.SSGRoute.PT.finQW_glue L A hA]
      exact Subgroup.mem_map.mpr ⟨τ, hτ, rfl⟩
    have hact : (φ₀ ⟨AlgEquiv.restrictNormalHom L σ, hσw⟩ : ↥K ≃ₐ[k] ↥K)
        = SSGRoute.res k K σ := by
      show ((Work.SSGRoute.PT.finZF hKL A hA ⟨AlgEquiv.restrictNormalHom L σ, hσw⟩ :
        ↥(decompK (k := k) (NK.GlobalCFT.Place.ofFinite q))) : ↥K ≃ₐ[k] ↥K) = SSGRoute.res k K σ
      rw [Work.SSGRoute.PT.finZF_spec hKL A hA]
      exact SSGRoute.PTExt.galRes_trans σ
    have h1 : b (σ * τ) = b₀ (AlgEquiv.restrictNormalHom L (σ * τ)) := rfl
    have h2 : b₀ (AlgEquiv.restrictNormalHom L (σ * τ))
        = b₀ (AlgEquiv.restrictNormalHom L σ * AlgEquiv.restrictNormalHom L τ) := by
      rw [map_mul]
    have h3 : b₀ (AlgEquiv.restrictNormalHom L σ * AlgEquiv.restrictNormalHom L τ)
        = c (⟨AlgEquiv.restrictNormalHom L σ, hσw⟩ * ⟨AlgEquiv.restrictNormalHom L τ, hτw⟩) :=
      hb₀_app _ _
    have h4 : c (⟨AlgEquiv.restrictNormalHom L σ, hσw⟩ * ⟨AlgEquiv.restrictNormalHom L τ, hτw⟩)
        = c ⟨AlgEquiv.restrictNormalHom L σ, hσw⟩
          + (φ₀ ⟨AlgEquiv.restrictNormalHom L σ, hσw⟩)
            • c ⟨AlgEquiv.restrictNormalHom L τ, hτw⟩ := hc _ _
    have h5 : c ⟨AlgEquiv.restrictNormalHom L σ, hσw⟩
          + (φ₀ ⟨AlgEquiv.restrictNormalHom L σ, hσw⟩)
            • c ⟨AlgEquiv.restrictNormalHom L τ, hτw⟩
        = b₀ (AlgEquiv.restrictNormalHom L σ)
          + (SSGRoute.res k K σ) • b₀ (AlgEquiv.restrictNormalHom L τ) := by
      rw [hb₀_app _ hσw, hb₀_app _ hτw, hact]
    exact h1.trans (h2.trans (h3.trans (h4.trans (h5.trans rfl))))
  -- ## `b` is locally constant (it factors through the finite quotient `Gal(L/k)`).
  have hloc : SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b := by
    refine ⟨(AlgEquiv.restrictNormalHom L).ker, ?_, ?_⟩
    · have hker : (AlgEquiv.restrictNormalHom L).ker = L.fixingSubgroup :=
        IntermediateField.restrictNormalHom_ker L
      rw [hker]
      exact IntermediateField.fixingSubgroup_isOpen L
    · intro g _ u hu _
      show b₀ (AlgEquiv.restrictNormalHom L (g * u)) = b₀ (AlgEquiv.restrictNormalHom L g)
      rw [map_mul, MonoidHom.mem_ker.mp hu, mul_one]
  -- ## `b` factors through `b₀ ∘ res_L`.
  have hfac : ∀ σ ∈ SSGRoute.decomp k A, b σ = b₀ (AlgEquiv.restrictNormalHom L σ) :=
    fun _ _ => rfl
  -- ## The value of `finZH` does not depend on the proofs, and is the class of `b₀`.
  have hfun : (fun σ : Dw => b₀ (σ : ↥L ≃ₐ[k] ↥L)) = c := funext (fun σ => hb₀coe σ)
  have hcrossed_b : Work.GroupCohomology.IsCrossedHom Dw X
      (fun σ : Dw => b₀ (σ : ↥L ≃ₐ[k] ↥L)) := by
    intro g h'
    show b₀ ↑(g * h') = g • b₀ ↑h' + b₀ ↑g
    rw [hb₀coe (g * h'), hb₀coe h', hb₀coe g]
    exact (hc g h').trans (add_comm _ _)
  let ψ : ↥(Work.GroupCohomology.Z1 Dw X) :=
    ⟨fun σ => b₀ (σ : ↥L ≃ₐ[k] ↥L), hcrossed_b⟩
  have hpsi : ψ = ⟨c, (Work.SSGRoute.ExtH1.crossedHom_iff Dw X c).mpr hc⟩ := Subtype.ext hfun
  have hmain : (Work.SSGRoute.ExtH1.gammaHom Dw X (Work.SSGRoute.augSES_shortExact Dw)
      (Work.GroupCohomology.H1π Dw X ψ) : SSGRoute.PTExt.extH (SSGRoute.PTExt.modRep Dw X) 1)
      = hh := by
    rw [Work.SSGRoute.ExtH1.gammaHom_H1π, hpsi, Work.SSGRoute.ExtH1.gammaZ1_apply,
        Work.SSGRoute.ExtH1.cocycleHom_proof_irrel Dw X c _ hc, hcoc]
    exact hf₀
  have hkey : ∀ (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b)
      (hb₀ : ∀ σ ∈ SSGRoute.decomp k A, b σ = b₀ (AlgEquiv.restrictNormalHom L σ)),
      Work.SSGRoute.PT.finZH p K T M L hKL A hA b hb b₀ hb₀ = h := by
    intro hb hb₀
    show (Work.SSGRoute.PT.finZH p K T M L hKL A hA b hb b₀ hb₀ :
      SSGRoute.PTExt.extH (SSGRoute.PTExt.modRep Dw X) 1) = hh
    simp only [Work.SSGRoute.PT.finZH, Work.SSGRoute.PT.finLevelClass]
    refine Eq.trans ?_ hmain
    refine congrArg (fun z : ↥(Work.GroupCohomology.Z1 Dw X) =>
      Work.SSGRoute.ExtH1.gammaHom Dw X (Work.SSGRoute.augSES_shortExact Dw)
        (Work.GroupCohomology.H1π Dw X z))
      (Subtype.ext rfl)
  exact ⟨b, b₀, hcocyc, hloc, hfac, hkey⟩

end Work.SSGRoute.PT.G1plusOwn
