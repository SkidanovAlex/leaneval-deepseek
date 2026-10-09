import Mathlib
import Submission.Work.SSGRoute.HRec.cupKummer_helpers
import Submission.Work.SSGRoute.HRec.locUnits_mkClass_eq_zero_of_inflCoboundary
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
## Assembly data for `cupKummer_matchK_forward`

The class `cupKummerBeta` is (by definition, `cupKummerBetaData`) the class of the descended cup
cocycle `cF` on `Gal(L/k)`.  This file extracts that cocycle explicitly (`cupCF`) together with the
two facts needed to apply the general local-vanishing lemma
`Work.SSGRoute.HRec.locUnits_mkClass_eq_zero_of_inflCoboundary`.

* `cupKummerBeta_eq_mkClass_cupCF` : `cupKummerBeta` is the class of `cupCF`;
* `cupCF_coboundary` : if the Ω-world cup cochain is a locally constant `2`-coboundary on
  `decomp k A`, then the inflation of `cupCF` is the coboundary of the pushed-forward witness.
-/

namespace Work.SSGRoute.HRec

open SSGRoute
open scoped TensorProduct

set_option linter.unusedSectionVars false
set_option linter.ambiguousOpen false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

/-- A chosen set-theoretic section of `Gal(Ω/k) →* Gal(L/k)`. -/
noncomputable def cupSec (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (L : FiniteGaloisIntermediateField k Ω) :
    (↥(L : IntermediateField k Ω) ≃ₐ[k] ↥(L : IntermediateField k Ω)) → (Ω ≃ₐ[k] Ω) :=
  fun γ => Classical.choose (AlgEquiv.restrictNormalHom_surjective (F := k) (E := Ω)
    (K₁ := (L : IntermediateField k Ω)) γ)

theorem cupSec_res (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (L : FiniteGaloisIntermediateField k Ω)
    (γ : ↥(L : IntermediateField k Ω) ≃ₐ[k] ↥(L : IntermediateField k Ω)) :
    SSGRoute.res k (L : IntermediateField k Ω) (cupSec k Ω L γ) = γ :=
  Classical.choose_spec (AlgEquiv.restrictNormalHom_surjective (F := k) (E := Ω)
    (K₁ := (L : IntermediateField k Ω)) γ)

/-- **The cup cochain depends only on the restrictions to `Gal(L/k)`.** -/
theorem cupZ_fac (p : ℕ) (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (T : Type) [AddCommGroup T] [Module (ZMod p) T]
    [DistribMulAction (K ≃ₐ[k] K) T] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (a : (Ω ≃ₐ[k] Ω) → M)
    (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
    (L : FiniteGaloisIntermediateField k Ω) (hKL : K ≤ (L : IntermediateField k Ω))
    (aL : (↥(L : IntermediateField k Ω) ≃ₐ[k] ↥(L : IntermediateField k Ω)) → M)
    (bL : (↥(L : IntermediateField k Ω) ≃ₐ[k] ↥(L : IntermediateField k Ω)) →
      Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
    (haeq : ∀ g : Ω ≃ₐ[k] Ω, aL (SSGRoute.res k (L : IntermediateField k Ω) g) = a g)
    (hbeq : ∀ g : Ω ≃ₐ[k] Ω, bL (SSGRoute.res k (L : IntermediateField k Ω) g) = b g)
    (g g' h h' : Ω ≃ₐ[k] Ω)
    (hg : SSGRoute.res k (L : IntermediateField k Ω) g = SSGRoute.res k (L : IntermediateField k Ω) g')
    (hh : SSGRoute.res k (L : IntermediateField k Ω) h = SSGRoute.res k (L : IntermediateField k Ω) h') :
    Work.SSGRoute.E7Fin.evCupFun p k Ω K T M a b g' h' =
      Work.SSGRoute.E7Fin.evCupFun p k Ω K T M a b g h := by
  let Z : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p T :=
    Work.SSGRoute.E7Fin.evCupFun p k Ω K T M a b
  change Z g' h' = Z g h
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

/-- **The descended cup cocycle on `Gal(L/k)`** attached to the Ω-world cup cochain. -/
noncomputable def cupCF (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T]
    [DistribMulAction (K ≃ₐ[k] K) T] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (a : (Ω ≃ₐ[k] Ω) → M)
    (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
    (L : FiniteGaloisIntermediateField k Ω) (hKL : K ≤ (L : IntermediateField k Ω)) :
    (↥(L : IntermediateField k Ω) ≃ₐ[k] ↥(L : IntermediateField k Ω)) ×
      (↥(L : IntermediateField k Ω) ≃ₐ[k] ↥(L : IntermediateField k Ω)) →
      (NK.HassePrinciple.unitsRep k ↥(L : IntermediateField k Ω)).V :=
  fun pq => muKToL p K (L : IntermediateField k Ω) hKL
    ((Work.SSGRoute.PTembedding.MupCard.dualModEquivMu hT hζ hζK)
      (Work.SSGRoute.E7Fin.evCupFun p k Ω K T M a b
        (cupSec k Ω L pq.1) (cupSec k Ω L pq.2)))

/-- The value of `cupCF` at the restrictions of `g`, `h`. -/
theorem cupCF_res (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T]
    [DistribMulAction (K ≃ₐ[k] K) T] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (a : (Ω ≃ₐ[k] Ω) → M)
    (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
    (L : FiniteGaloisIntermediateField k Ω) (hKL : K ≤ (L : IntermediateField k Ω))
    (aL : (↥(L : IntermediateField k Ω) ≃ₐ[k] ↥(L : IntermediateField k Ω)) → M)
    (bL : (↥(L : IntermediateField k Ω) ≃ₐ[k] ↥(L : IntermediateField k Ω)) →
      Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
    (haeq : ∀ g : Ω ≃ₐ[k] Ω, aL (SSGRoute.res k (L : IntermediateField k Ω) g) = a g)
    (hbeq : ∀ g : Ω ≃ₐ[k] Ω, bL (SSGRoute.res k (L : IntermediateField k Ω) g) = b g)
    (g h : Ω ≃ₐ[k] Ω) :
    cupCF p k Ω K ζ hζ hζK T hT M a b L hKL
        (SSGRoute.res k (L : IntermediateField k Ω) g,
          SSGRoute.res k (L : IntermediateField k Ω) h)
      = muKToL p K (L : IntermediateField k Ω) hKL
          ((Work.SSGRoute.PTembedding.MupCard.dualModEquivMu hT hζ hζK)
            (Work.SSGRoute.E7Fin.evCupFun p k Ω K T M a b g h)) := by
  simp only [cupCF]
  rw [cupZ_fac p k Ω K T M a b L hKL aL bL haeq hbeq
    g (cupSec k Ω L (SSGRoute.res k (L : IntermediateField k Ω) g))
    h (cupSec k Ω L (SSGRoute.res k (L : IntermediateField k Ω) h))
    (cupSec_res k Ω L (SSGRoute.res k (L : IntermediateField k Ω) g)).symm
    (cupSec_res k Ω L (SSGRoute.res k (L : IntermediateField k Ω) h)).symm]

/-- **`cupCF` is a `2`-cocycle.** -/
theorem cupCF_mem (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T]
    [DistribMulAction (K ≃ₐ[k] K) T] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (a : (Ω ≃ₐ[k] Ω) → M)
    (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
    (L : FiniteGaloisIntermediateField k Ω) (hKL : K ≤ (L : IntermediateField k Ω))
    (aL : (↥(L : IntermediateField k Ω) ≃ₐ[k] ↥(L : IntermediateField k Ω)) → M)
    (bL : (↥(L : IntermediateField k Ω) ≃ₐ[k] ↥(L : IntermediateField k Ω)) →
      Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
    (haeq : ∀ g : Ω ≃ₐ[k] Ω, aL (SSGRoute.res k (L : IntermediateField k Ω) g) = a g)
    (hbeq : ∀ g : Ω ≃ₐ[k] Ω, bL (SSGRoute.res k (L : IntermediateField k Ω) g) = b g)
    (ha1 : SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ a)
    (hb1 : SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b) :
    cupCF p k Ω K ζ hζ hζK T hT M a b L hKL ∈
      groupCohomology.cocycles₂
        (NK.HassePrinciple.unitsRep k ↥(L : IntermediateField k Ω)) := by
  let θ : Work.SSGRoute.DualMod p T ≃ₗ[ZMod p]
      Work.SSGRoute.PTembedding.MupCard.MuAdd p K :=
    Work.SSGRoute.PTembedding.MupCard.dualModEquivMu hT hζ hζK
  let Z : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p T :=
    Work.SSGRoute.E7Fin.evCupFun p k Ω K T M a b
  have hsec : ∀ γ, SSGRoute.res k (L : IntermediateField k Ω) (cupSec k Ω L γ) = γ :=
    fun γ => cupSec_res k Ω L γ
  let ZL : (↥(L : IntermediateField k Ω) ≃ₐ[k] ↥(L : IntermediateField k Ω)) →
      (↥(L : IntermediateField k Ω) ≃ₐ[k] ↥(L : IntermediateField k Ω)) →
      Work.SSGRoute.PTembedding.MupCard.MuAdd p K :=
    fun γ δ => θ (Z (cupSec k Ω L γ) (cupSec k Ω L δ))
  have hZL : ∀ (γ δ ε : ↥(L : IntermediateField k Ω) ≃ₐ[k] ↥(L : IntermediateField k Ω)),
      (SSGRoute.res k K) (cupSec k Ω L γ) • ZL δ ε - ZL (γ * δ) ε + ZL γ (δ * ε) - ZL γ δ = 0 := by
    intro γ δ ε
    have hZ := Work.SSGRoute.evCupFun_isCocycle2On p k Ω K T M (⊤ : Subgroup (Ω ≃ₐ[k] Ω))
      a b ha1 hb1 (cupSec k Ω L γ) trivial (cupSec k Ω L δ) trivial (cupSec k Ω L ε) trivial
    have h := congrArg (fun v => θ v) hZ
    simp only [map_sub, map_add, map_zero] at h
    rw [Work.SSGRoute.PTembedding.MupCard.dualModEquivMu_smul hT hζ hζK
      (SSGRoute.res k K (cupSec k Ω L γ)) (Z (cupSec k Ω L δ) (cupSec k Ω L ε))] at h
    have h1 : θ (Z (cupSec k Ω L γ * cupSec k Ω L δ) (cupSec k Ω L ε)) = ZL (γ * δ) ε := by
      have e : Z (cupSec k Ω L γ * cupSec k Ω L δ) (cupSec k Ω L ε)
          = Z (cupSec k Ω L (γ * δ)) (cupSec k Ω L ε) :=
        (cupZ_fac p k Ω K T M a b L hKL aL bL haeq hbeq
          (cupSec k Ω L γ * cupSec k Ω L δ) (cupSec k Ω L (γ * δ))
          (cupSec k Ω L ε) (cupSec k Ω L ε)
          (by simp only [map_mul, hsec]) rfl).symm
      rw [e]
    rw [h1] at h
    have h2 : θ (Z (cupSec k Ω L γ) (cupSec k Ω L δ * cupSec k Ω L ε)) = ZL γ (δ * ε) := by
      have e : Z (cupSec k Ω L γ) (cupSec k Ω L δ * cupSec k Ω L ε)
          = Z (cupSec k Ω L γ) (cupSec k Ω L (δ * ε)) :=
        (cupZ_fac p k Ω K T M a b L hKL aL bL haeq hbeq
          (cupSec k Ω L γ) (cupSec k Ω L γ)
          (cupSec k Ω L δ * cupSec k Ω L ε) (cupSec k Ω L (δ * ε)) rfl
          (by simp only [map_mul, hsec])).symm
      rw [e]
    rw [h2] at h
    exact h
  rw [Work.SSGRoute.sha2_hasse.mem_cocycles₂_iff
    (A := NK.HassePrinciple.unitsRep k ↥(L : IntermediateField k Ω))]
  intro γ δ ε
  have h := hZL γ δ ε
  have hkey := congrArg (fun v => muKToL p K (L : IntermediateField k Ω) hKL v) h
  simp only [map_sub, map_add, map_zero] at hkey
  rw [muKToL_equivariant p K (L : IntermediateField k Ω) hKL (cupSec k Ω L γ) (ZL δ ε)] at hkey
  rw [hsec γ] at hkey
  exact hkey

/-- **`cupKummerBeta` is the class of the descended cup cocycle `cupCF`.** -/
theorem cupKummerBeta_eq_mkClass_cupCF (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
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
    cupKummerBeta p k Ω K ζ hζ hζK T hT hp M a b ha1 ha2 hb1 hb2 L hKL aL bL haeq hbeq
      = Work.SSGRoute.sha2_hasse.mkClass
          (NK.HassePrinciple.unitsRep k ↥(L : IntermediateField k Ω))
          (cupCF p k Ω K ζ hζ hζK T hT M a b L hKL)
          (cupCF_mem p k Ω K ζ hζ hζK T hT M a b L hKL aL bL haeq hbeq ha1 hb1) := by
  unfold Work.SSGRoute.HRec.cupKummerBeta Work.SSGRoute.HRec.cupKummerBetaData
  rfl

/-- **The coboundary witness for the descended cup cocycle.**  If the Ω-world cup cochain is a
locally constant `2`-coboundary on `decomp k A`, then the same holds for `cupCF`, with the witness
obtained by pushing the Ω-world witness along `μ_p ⊆ Lˣ`. -/
theorem cupCF_coboundary (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T]
    [DistribMulAction (K ≃ₐ[k] K) T] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (a : (Ω ≃ₐ[k] Ω) → M)
    (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
    (L : FiniteGaloisIntermediateField k Ω) (hKL : K ≤ (L : IntermediateField k Ω))
    (aL : (↥(L : IntermediateField k Ω) ≃ₐ[k] ↥(L : IntermediateField k Ω)) → M)
    (bL : (↥(L : IntermediateField k Ω) ≃ₐ[k] ↥(L : IntermediateField k Ω)) →
      Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
    (haeq : ∀ g : Ω ≃ₐ[k] Ω, aL (SSGRoute.res k (L : IntermediateField k Ω) g) = a g)
    (hbeq : ∀ g : Ω ≃ₐ[k] Ω, bL (SSGRoute.res k (L : IntermediateField k Ω) g) = b g)
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (h : Work.SSGRoute.E7Fin.evCupFun p k Ω K T M a b ∈
      Work.SSGRoute.coboundaries2 p k Ω K (Work.SSGRoute.DualMod p T) (SSGRoute.decomp k A)) :
    ∃ b' : (Ω ≃ₐ[k] Ω) → Additive (↥(L : IntermediateField k Ω))ˣ,
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b' ∧
      ∀ g ∈ SSGRoute.decomp k A, ∀ h' ∈ SSGRoute.decomp k A,
        cupCF p k Ω K ζ hζ hζK T hT M a b L hKL
            (SSGRoute.res k (L : IntermediateField k Ω) g,
              SSGRoute.res k (L : IntermediateField k Ω) h')
          = (SSGRoute.res k (L : IntermediateField k Ω) g) • b' h' - b' (g * h') + b' g := by
  obtain ⟨bA, hbAlc, hbAcob⟩ := h
  refine ⟨fun g => muKToL p K (L : IntermediateField k Ω) hKL
      ((Work.SSGRoute.PTembedding.MupCard.dualModEquivMu hT hζ hζK) (bA g)), ?_, ?_⟩
  · obtain ⟨U, hUo, hUc⟩ := hbAlc
    exact ⟨U, hUo, fun g hg u hu huH => by
      show muKToL p K (L : IntermediateField k Ω) hKL
          ((Work.SSGRoute.PTembedding.MupCard.dualModEquivMu hT hζ hζK) (bA (g * u)))
        = muKToL p K (L : IntermediateField k Ω) hKL
          ((Work.SSGRoute.PTembedding.MupCard.dualModEquivMu hT hζ hζK) (bA g))
      rw [hUc g hg u hu huH]⟩
  · intro g hg h' hh'
    rw [cupCF_res p k Ω K ζ hζ hζK T hT M a b L hKL aL bL haeq hbeq g h']
    dsimp only
    rw [show (SSGRoute.res k (L : IntermediateField k Ω) g) •
          (muKToL p K (L : IntermediateField k Ω) hKL
            ((Work.SSGRoute.PTembedding.MupCard.dualModEquivMu hT hζ hζK) (bA h')))
        = muKToL p K (L : IntermediateField k Ω) hKL
            ((Work.SSGRoute.PTembedding.MupCard.dualModEquivMu hT hζ hζK)
              ((SSGRoute.res k K) g • bA h')) from by
      rw [Work.SSGRoute.PTembedding.MupCard.dualModEquivMu_smul hT hζ hζK
        (SSGRoute.res k K g) (bA h')]
      exact (muKToL_equivariant p K (L : IntermediateField k Ω) hKL g
        ((Work.SSGRoute.PTembedding.MupCard.dualModEquivMu hT hζ hζK) (bA h'))).symm]
    rw [hbAcob g hg h' hh']
    simp only [map_add, map_sub]
    try abel

end

theorem cupKummer_matchK_forward (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
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
    (hbeq : ∀ g : Ω ≃ₐ[k] Ω, bL (SSGRoute.res k (L : IntermediateField k Ω) g) = b g)
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (h : Work.SSGRoute.E7Fin.evCupFun p k Ω K T M a b ∈
      Work.SSGRoute.coboundaries2 p k Ω K (Work.SSGRoute.DualMod p T) (SSGRoute.decomp k A)) :
    ∀ w : NK.GlobalCFT.Place ↥(L : IntermediateField k Ω),
      NK.GlobalCFT.Place.LiesOver w
        (NK.GlobalCFT.Place.ofFinite (Submission.NeukirchUchida.primeOf A hA)) →
      (NK.HassePrinciple.locUnits k ↥(L : IntermediateField k Ω) w).hom
        (Work.SSGRoute.HRec.cupKummerBeta p k Ω K ζ hζ hζK T hT hp M a b ha1 ha2 hb1 hb2
          L hKL aL bL haeq hbeq) = 0 := by
  intro w hw
  rw [cupKummerBeta_eq_mkClass_cupCF p k Ω K ζ hζ hζK T hT hp M a b ha1 ha2 hb1 hb2
    L hKL aL bL haeq hbeq]
  obtain ⟨b', hb', hcob'⟩ := cupCF_coboundary p k Ω K ζ hζ hζK T hT M a b L hKL aL bL haeq
    hbeq A hA h
  exact Work.SSGRoute.HRec.locUnits_mkClass_eq_zero_of_inflCoboundary k Ω L
    (cupCF p k Ω K ζ hζ hζK T hT M a b L hKL)
    (cupCF_mem p k Ω K ζ hζ hζK T hT M a b L hKL aL bL haeq hbeq ha1 hb1)
    A hA b' hb' hcob' w hw

end Work.SSGRoute.HRec
