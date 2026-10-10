import Mathlib.FieldTheory.KrullTopology
import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.FieldTheory.Galois.GaloisClosure
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Submission.Work.SSGRoute.HSRow.Coords
import Submission.Work.SSGRoute.HSTwoRow.finrank_H1loc_decomp
import Submission.Work.SSGRoute.Nakayama.kummerH2
import Submission.Work.SSGRoute.evCupFun_isCocycle2On
import Submission.Work.SSGRoute.sha2_hasse.locUnits_mkClass_apply
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open SSGRoute
open scoped TensorProduct

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000

namespace Work.SSGRoute.HRec

noncomputable section

open Work.SSGRoute.PTembedding.MupCard

def muKToL {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] (p : ℕ)
    (K L : IntermediateField k Ω) (hKL : K ≤ L) :
    MuAdd p K →+ Additive (↥L)ˣ :=
  ((Units.map (IntermediateField.inclusion hKL).toMonoidHom).comp
    (rootsOfUnity p K).subtype).toAdditive

@[simp] lemma muKToL_val {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] (p : ℕ)
    (K L : IntermediateField k Ω) (hKL : K ≤ L) (x : MuAdd p K) :
    ((Additive.toMul (muKToL p K L hKL x) : (↥L)ˣ) : ↥L)
      = IntermediateField.inclusion hKL
          ((((Additive.toMul x : rootsOfUnity p K)) : (↥K)ˣ) : ↥K) := rfl

lemma val_smul_units {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    (L : IntermediateField k Ω) [Normal k L] (σ : Ω ≃ₐ[k] Ω) (u : (↥L)ˣ) :
    (((SSGRoute.res k L) σ • u : (↥L)ˣ) : ↥L) = (SSGRoute.res k L) σ (u : ↥L) := by
  rw [AlgEquiv.smul_units_def, Units.coe_map]; rfl

lemma inclusion_restrictNormal' {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    (K L : IntermediateField k Ω) (hKL : K ≤ L) [Normal k K] [Normal k L]
    (σ : Ω ≃ₐ[k] Ω) (v : ↥K) :
    IntermediateField.inclusion hKL ((SSGRoute.res k K) σ v) =
      (SSGRoute.res k L) σ (IntermediateField.inclusion hKL v) := by
  apply Subtype.ext
  have hL : (↑((SSGRoute.res k L) σ (IntermediateField.inclusion hKL v)) : Ω)
      = σ (↑(IntermediateField.inclusion hKL v) : Ω) :=
    AlgEquiv.restrictNormalHom_apply (F := k) (K₁ := Ω) L σ (IntermediateField.inclusion hKL v)
  rw [hL]
  rw [show (↑(IntermediateField.inclusion hKL v) : Ω) = (↑v : Ω) from rfl]
  have h1 : (↑(IntermediateField.inclusion hKL ((SSGRoute.res k K) σ v)) : Ω)
      = (↑((SSGRoute.res k K) σ v) : Ω) := rfl
  rw [h1, AlgEquiv.restrictNormalHom_apply (F := k) (K₁ := Ω) K σ v]

lemma muKToL_equivariant {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] (p : ℕ)
    (K L : IntermediateField k Ω) (hKL : K ≤ L) [Normal k K] [Normal k L]
    (σ : Ω ≃ₐ[k] Ω) (x : MuAdd p K) :
    muKToL p K L hKL ((SSGRoute.res k K) σ • x) =
      (SSGRoute.res k L) σ • muKToL p K L hKL x := by
  apply Additive.toMul.injective
  apply Units.ext
  rw [muKToL_val]
  rw [show Additive.toMul ((SSGRoute.res k L) σ • muKToL p K L hKL x)
      = (SSGRoute.res k L) σ • Additive.toMul (muKToL p K L hKL x) from rfl]
  rw [val_smul_units, muKToL_val]
  rw [show (((Additive.toMul ((SSGRoute.res k K) σ • x) : rootsOfUnity p K)) : (↥K)ˣ)
      = Work.SSGRoute.PT.algEquivUnitsMapOfField k ↥K (SSGRoute.res k K σ)
          (((Additive.toMul x : rootsOfUnity p K)) : (↥K)ˣ) from by
        rw [show (Additive.toMul ((SSGRoute.res k K) σ • x) : rootsOfUnity p K)
            = Work.SSGRoute.PTembedding.MupKummer.muMapOfField k ↥K p (SSGRoute.res k K σ)
                (Additive.toMul x) from rfl,
          Work.SSGRoute.PTembedding.MupKummer.muMapOfField_coe]]
  rw [Work.SSGRoute.PT.algEquivUnitsMapOfField_coe]
  exact inclusion_restrictNormal' K L hKL σ ((((Additive.toMul x : rootsOfUnity p K)) : (↥K)ˣ) : ↥K)

noncomputable def cupKummerBetaData (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T]
    [DistribMulAction (K ≃ₐ[k] K) T] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (hp : p = 2)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (a : (Ω ≃ₐ[k] Ω) → M)
    (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
    (ha1 : SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ a) (ha2 : SSGRoute.IsLocConstOn ⊤ a)
    (hb1 : SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b) (hb2 : SSGRoute.IsLocConstOn ⊤ b)
    (L : FiniteGaloisIntermediateField k Ω) (hKL : K ≤ (L : IntermediateField k Ω))
    (aL : (↥(L : IntermediateField k Ω) ≃ₐ[k] ↥(L : IntermediateField k Ω)) → M)
    (bL : (↥(L : IntermediateField k Ω) ≃ₐ[k] ↥(L : IntermediateField k Ω)) →
      Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
    (haeq : ∀ g : Ω ≃ₐ[k] Ω, aL (SSGRoute.res k (L : IntermediateField k Ω) g) = a g)
    (hbeq : ∀ g : Ω ≃ₐ[k] Ω, bL (SSGRoute.res k (L : IntermediateField k Ω) g) = b g) : {β : groupCohomology (NK.HassePrinciple.unitsRep k ↥(L : IntermediateField k Ω)) 2 // (2 : ℕ) • β = 0} := by

  classical
  let θ : Work.SSGRoute.DualMod p T ≃ₗ[ZMod p] MuAdd p K :=
    Work.SSGRoute.PTembedding.MupCard.dualModEquivMu hT hζ hζK
  have hsurj : Function.Surjective (SSGRoute.res k (L : IntermediateField k Ω)) :=
    AlgEquiv.restrictNormalHom_surjective (F := k) (E := Ω)
      (K₁ := (L : IntermediateField k Ω))
  let sec : (↥(L : IntermediateField k Ω) ≃ₐ[k] ↥(L : IntermediateField k Ω)) → (Ω ≃ₐ[k] Ω) :=
    fun γ => Classical.choose (hsurj γ)
  have hsec : ∀ γ, SSGRoute.res k (L : IntermediateField k Ω) (sec γ) = γ :=
    fun γ => Classical.choose_spec (hsurj γ)
  let Z : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p T :=
    Work.SSGRoute.E7Fin.evCupFun p k Ω K T M a b
  have hfac : ∀ (g g' h h' : Ω ≃ₐ[k] Ω),
      SSGRoute.res k (L : IntermediateField k Ω) g = SSGRoute.res k (L : IntermediateField k Ω) g' →
      SSGRoute.res k (L : IntermediateField k Ω) h = SSGRoute.res k (L : IntermediateField k Ω) h' →
      Z g' h' = Z g h := by
    intro g g' h h' hg hh
    have e1 : a g' = a g := by rw [← haeq g', ← haeq g, hg]
    have e2 : b h' = b h := by rw [← hbeq h', ← hbeq h, hh]
    have hu : g⁻¹ * g' ∈ (L : IntermediateField k Ω).fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      have h2 : SSGRoute.res k (L : IntermediateField k Ω) (g⁻¹ * g') = 1 := by
        rw [map_mul, map_inv, hg, inv_mul_cancel]
      have h3 := congrArg (fun (γ : ↥(L : IntermediateField k Ω) ≃ₐ[k] ↥(L : IntermediateField k Ω)) =>
        (γ ⟨x, hx⟩ : Ω)) h2
      simp only [AlgEquiv.one_apply, OneMemClass.coe_one] at h3
      rw [AlgEquiv.restrictNormalHom_apply (F := k) (K₁ := Ω) (L : IntermediateField k Ω)
        (g⁻¹ * g') ⟨x, hx⟩] at h3
      exact h3
    have huK : g⁻¹ * g' ∈ K.fixingSubgroup :=
      IntermediateField.fixingSubgroup_antitone hKL hu
    have hker : SSGRoute.res k K (g⁻¹ * g') = 1 := by
      apply AlgEquiv.ext
      intro y
      have hy : (g⁻¹ * g') (y : Ω) = (y : Ω) :=
        (IntermediateField.mem_fixingSubgroup_iff (K : IntermediateField k Ω)
          (g⁻¹ * g')).mp huK y y.2
      rw [AlgEquiv.one_apply]
      apply Subtype.ext
      rw [AlgEquiv.restrictNormalHom_apply (F := k) (K₁ := Ω) (K : IntermediateField k Ω)
        (g⁻¹ * g') y]
      exact hy
    have e3 : SSGRoute.res k K g' = SSGRoute.res k K g := by
      have h2 : SSGRoute.res k K (g * (g⁻¹ * g')) = SSGRoute.res k K g := by
        rw [map_mul, hker, mul_one]
      rwa [mul_inv_cancel_left] at h2
    simp only [Z, Work.SSGRoute.E7Fin.evCupFun, e1, e2, e3]
  let ZL : (↥(L : IntermediateField k Ω) ≃ₐ[k] ↥(L : IntermediateField k Ω)) →
          (↥(L : IntermediateField k Ω) ≃ₐ[k] ↥(L : IntermediateField k Ω)) → MuAdd p K :=
    fun γ δ => θ (Z (sec γ) (sec δ))
  let c : (↥(L : IntermediateField k Ω) ≃ₐ[k] ↥(L : IntermediateField k Ω)) →
          (↥(L : IntermediateField k Ω) ≃ₐ[k] ↥(L : IntermediateField k Ω)) →
          Additive (↥(L : IntermediateField k Ω))ˣ :=
    fun γ δ => muKToL p K (L : IntermediateField k Ω) hKL (ZL γ δ)
  let cF : (↥(L : IntermediateField k Ω) ≃ₐ[k] ↥(L : IntermediateField k Ω)) ×
      (↥(L : IntermediateField k Ω) ≃ₐ[k] ↥(L : IntermediateField k Ω)) →
      (NK.HassePrinciple.unitsRep k ↥(L : IntermediateField k Ω)).V :=
    fun pq => c pq.1 pq.2
  have hZL : ∀ (γ δ ε : ↥(L : IntermediateField k Ω) ≃ₐ[k] ↥(L : IntermediateField k Ω)),
      (SSGRoute.res k K) (sec γ) • ZL δ ε - ZL (γ * δ) ε + ZL γ (δ * ε) - ZL γ δ = 0 := by
    intro γ δ ε
    have hZ := Work.SSGRoute.evCupFun_isCocycle2On p k Ω K T M (⊤ : Subgroup (Ω ≃ₐ[k] Ω))
      a b ha1 hb1 (sec γ) trivial (sec δ) trivial (sec ε) trivial
    have h := congrArg (fun v => θ v) hZ
    simp only [map_sub, map_add, map_zero] at h
    rw [Work.SSGRoute.PTembedding.MupCard.dualModEquivMu_smul hT hζ hζK
      (SSGRoute.res k K (sec γ)) (Z (sec δ) (sec ε))] at h
    have h1 : θ (Z (sec γ * sec δ) (sec ε)) = ZL (γ * δ) ε := by
      have e : Z (sec γ * sec δ) (sec ε) = Z (sec (γ * δ)) (sec ε) :=
        (hfac (sec γ * sec δ) (sec (γ * δ)) (sec ε) (sec ε)
          (by simp only [map_mul, hsec]) rfl).symm
      rw [e]
    rw [h1] at h
    have h2 : θ (Z (sec γ) (sec δ * sec ε)) = ZL γ (δ * ε) := by
      have e : Z (sec γ) (sec δ * sec ε) = Z (sec γ) (sec (δ * ε)) :=
        (hfac (sec γ) (sec γ) (sec δ * sec ε) (sec (δ * ε)) rfl
          (by simp only [map_mul, hsec])).symm
      rw [e]
    rw [h2] at h
    exact h
  have hc : cF ∈ groupCohomology.cocycles₂
        (NK.HassePrinciple.unitsRep k ↥(L : IntermediateField k Ω)) := by
    rw [Work.SSGRoute.sha2_hasse.mem_cocycles₂_iff
      (A := NK.HassePrinciple.unitsRep k ↥(L : IntermediateField k Ω))]
    intro γ δ ε
    have h := hZL γ δ ε
    have hkey := congrArg (fun v => muKToL p K (L : IntermediateField k Ω) hKL v) h
    simp only [map_sub, map_add, map_zero] at hkey
    rw [muKToL_equivariant p K (L : IntermediateField k Ω) hKL (sec γ) (ZL δ ε)] at hkey
    rw [hsec γ] at hkey
    exact hkey
  have hcc : cF + cF = 0 := by
    funext pq
    obtain ⟨γ, δ⟩ := pq
    have hx : ZL γ δ + ZL γ δ = 0 := by
      rw [← two_nsmul, ← hp]
      exact Work.SSGRoute.PTembedding.MupCard.nsmulMuAdd_eq_zero K (ZL γ δ)
    show c γ δ + c γ δ = 0
    simp only [c]
    rw [← map_add, hx, map_zero]
  let β := Work.SSGRoute.sha2_hasse.mkClass
    (NK.HassePrinciple.unitsRep k ↥(L : IntermediateField k Ω)) cF hc
  have hβ2 : (2 : ℕ) • β = 0 := by
    show (2 : ℕ) • Work.SSGRoute.sha2_hasse.mkClass
      (NK.HassePrinciple.unitsRep k ↥(L : IntermediateField k Ω)) cF hc = 0
    rw [show Work.SSGRoute.sha2_hasse.mkClass (NK.HassePrinciple.unitsRep k ↥(L : IntermediateField k Ω)) cF hc = (CategoryTheory.ConcreteCategory.hom (groupCohomology.H2π (NK.HassePrinciple.unitsRep k ↥(L : IntermediateField k Ω)))) (⟨cF, hc⟩ : ↥(groupCohomology.cocycles₂ (NK.HassePrinciple.unitsRep k ↥(L : IntermediateField k Ω)))) from rfl]
    have h2 : (2 : ℕ) •
        (⟨cF, hc⟩ :
          ↥(groupCohomology.cocycles₂ (NK.HassePrinciple.unitsRep k ↥(L : IntermediateField k Ω)))) = 0 := by
      apply Subtype.ext
      show (2 : ℕ) • cF = 0
      rw [two_nsmul]
      exact hcc
    rw [← map_nsmul, h2, map_zero]

  exact ⟨β, hβ2⟩

noncomputable def cupKummerBeta (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T]
    [DistribMulAction (K ≃ₐ[k] K) T] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (hp : p = 2)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (a : (Ω ≃ₐ[k] Ω) → M)
    (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
    (ha1 : SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ a) (ha2 : SSGRoute.IsLocConstOn ⊤ a)
    (hb1 : SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b) (hb2 : SSGRoute.IsLocConstOn ⊤ b)
    (L : FiniteGaloisIntermediateField k Ω) (hKL : K ≤ (L : IntermediateField k Ω))
    (aL : (↥(L : IntermediateField k Ω) ≃ₐ[k] ↥(L : IntermediateField k Ω)) → M)
    (bL : (↥(L : IntermediateField k Ω) ≃ₐ[k] ↥(L : IntermediateField k Ω)) →
      Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
    (haeq : ∀ g : Ω ≃ₐ[k] Ω, aL (SSGRoute.res k (L : IntermediateField k Ω) g) = a g)
    (hbeq : ∀ g : Ω ≃ₐ[k] Ω, bL (SSGRoute.res k (L : IntermediateField k Ω) g) = b g) :
    groupCohomology (NK.HassePrinciple.unitsRep k ↥(L : IntermediateField k Ω)) 2 :=
  (cupKummerBetaData p k Ω K ζ hζ hζK T hT hp M a b ha1 ha2 hb1 hb2 L hKL aL bL haeq hbeq).1

theorem cupKummerBeta_nsmul (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T]
    [DistribMulAction (K ≃ₐ[k] K) T] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (hp : p = 2)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (a : (Ω ≃ₐ[k] Ω) → M)
    (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
    (ha1 : SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ a) (ha2 : SSGRoute.IsLocConstOn ⊤ a)
    (hb1 : SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b) (hb2 : SSGRoute.IsLocConstOn ⊤ b)
    (L : FiniteGaloisIntermediateField k Ω) (hKL : K ≤ (L : IntermediateField k Ω))
    (aL : (↥(L : IntermediateField k Ω) ≃ₐ[k] ↥(L : IntermediateField k Ω)) → M)
    (bL : (↥(L : IntermediateField k Ω) ≃ₐ[k] ↥(L : IntermediateField k Ω)) →
      Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
    (haeq : ∀ g : Ω ≃ₐ[k] Ω, aL (SSGRoute.res k (L : IntermediateField k Ω) g) = a g)
    (hbeq : ∀ g : Ω ≃ₐ[k] Ω, bL (SSGRoute.res k (L : IntermediateField k Ω) g) = b g) :
    (2 : ℕ) • cupKummerBeta p k Ω K ζ hζ hζK T hT hp M a b ha1 ha2 hb1 hb2 L hKL aL bL haeq hbeq = 0 :=
  (cupKummerBetaData p k Ω K ζ hζ hζK T hT hp M a b ha1 ha2 hb1 hb2 L hKL aL bL haeq hbeq).2

/-- **The localisation of an explicitly given class at a general level `L`**: for a place `w` of a
finite Galois number field `L/k`, the localisation of the class of the explicit `2`-cocycle `c` is
the class of the pushed-forward cocycle `(γ,δ) ↦ (unitsToLocalUnits k L w) (c (γ, δ))` on the
decomposition group of `w`. -/
theorem locUnits_mkClass_apply_general {k : Type} [Field k] [NumberField k]
    (L : Type) [Field L] [NumberField L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (w : NK.GlobalCFT.Place L)
    (c : (L ≃ₐ[k] L) × (L ≃ₐ[k] L) → Additive Lˣ)
    (hc : c ∈ groupCohomology.cocycles₂ (NK.HassePrinciple.unitsRep k L)) :
    (NK.HassePrinciple.locUnits k L w).hom
        (Work.SSGRoute.sha2_hasse.mkClass (NK.HassePrinciple.unitsRep k L) c hc)
      = groupCohomology.H2π (NK.HassePrinciple.localUnitsRep k L w)
          (groupCohomology.mapCocycles₂ (MulAction.stabilizer (L ≃ₐ[k] L) w).subtype
            (NK.HassePrinciple.unitsToLocalUnits k L w) ⟨c, hc⟩) := by
  have hloc : NK.HassePrinciple.locUnits k L w
      = groupCohomology.map (MulAction.stabilizer (L ≃ₐ[k] L) w).subtype
          (NK.HassePrinciple.unitsToLocalUnits k L w) 2 := by
    rw [NK.HassePrinciple.locUnits, groupCohomology.resNatTrans_app]
    exact NK.NUV2.LC.RouteB.map_id_comp_apply (MulAction.stabilizer (L ≃ₐ[k] L) w).subtype
      (NK.HassePrinciple.unitsToLocalUnits k L w) 2
  rw [hloc]
  rw [show Work.SSGRoute.sha2_hasse.mkClass (NK.HassePrinciple.unitsRep k L) c hc
      = (CategoryTheory.ConcreteCategory.hom (groupCohomology.H2π (NK.HassePrinciple.unitsRep k L)))
          (⟨c, hc⟩ : ↥(groupCohomology.cocycles₂ (NK.HassePrinciple.unitsRep k L))) from rfl]
  conv_rhs => rw [← ModuleCat.comp_apply
    (groupCohomology.mapCocycles₂ (MulAction.stabilizer (L ≃ₐ[k] L) w).subtype
      (NK.HassePrinciple.unitsToLocalUnits k L w))
    (groupCohomology.H2π (NK.HassePrinciple.localUnitsRep k L w)) ⟨c, hc⟩]
  rw [← groupCohomology.H2π_comp_map (MulAction.stabilizer (L ≃ₐ[k] L) w).subtype
      (NK.HassePrinciple.unitsToLocalUnits k L w)]
  rw [ModuleCat.comp_apply]


/-- **`locUnits_w` of the constructed class, unrolled**: it vanishes exactly when the
pushed-forward cocycle `(γ,δ) ↦ (unitsToLocalUnits k L w) (c (γ, δ))` on the decomposition group of
`w` is a coboundary with values in the local units `L_wˣ`. -/
theorem locUnits_mkClass_eq_zero_iff {k : Type} [Field k] [NumberField k]
    (L : Type) [Field L] [NumberField L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (w : NK.GlobalCFT.Place L)
    (c : (L ≃ₐ[k] L) × (L ≃ₐ[k] L) → Additive Lˣ)
    (hc : c ∈ groupCohomology.cocycles₂ (NK.HassePrinciple.unitsRep k L)) :
    (NK.HassePrinciple.locUnits k L w).hom
        (Work.SSGRoute.sha2_hasse.mkClass (NK.HassePrinciple.unitsRep k L) c hc) = 0 ↔
      ∃ f : ↥(MulAction.stabilizer (L ≃ₐ[k] L) w) → ↥(NK.HassePrinciple.localUnitsRep k L w),
        ∀ γ δ, (NK.HassePrinciple.localUnitsRep k L w).ρ γ (f δ) - f (γ * δ) + f γ
          = (NK.HassePrinciple.unitsToLocalUnits k L w).hom (c (γ, δ)) := by
  rw [locUnits_mkClass_apply_general L w c hc]
  rw [groupCohomology.H2π_eq_zero_iff, groupCohomology.coboundaries₂, LinearMap.mem_range]
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨f, fun γ δ => ?_⟩
    have h1 := congrFun hf (γ, δ)
    rw [groupCohomology.d₁₂_hom_apply] at h1
    rw [show (⇑(groupCohomology.mapCocycles₂ (MulAction.stabilizer (L ≃ₐ[k] L) w).subtype
            (NK.HassePrinciple.unitsToLocalUnits k L w) ⟨c, hc⟩)) (γ, δ)
        = (NK.HassePrinciple.unitsToLocalUnits k L w).hom (c (γ, δ)) from by
          rw [groupCohomology.coe_mapCocycles₂, Work.SSGRoute.sha2_hasse.cochainsMap₂_apply]
          rfl] at h1
    exact h1
  · rintro ⟨f, hf⟩
    refine ⟨f, ?_⟩
    funext p
    obtain ⟨γ, δ⟩ := p
    simp only [groupCohomology.d₁₂_hom_apply]
    rw [show (⇑(groupCohomology.mapCocycles₂ (MulAction.stabilizer (L ≃ₐ[k] L) w).subtype
            (NK.HassePrinciple.unitsToLocalUnits k L w) ⟨c, hc⟩)) (γ, δ)
        = (NK.HassePrinciple.unitsToLocalUnits k L w).hom (c (γ, δ)) from by
          rw [groupCohomology.coe_mapCocycles₂, Work.SSGRoute.sha2_hasse.cochainsMap₂_apply]
          rfl]
    exact hf γ δ


end

end Work.SSGRoute.HRec
