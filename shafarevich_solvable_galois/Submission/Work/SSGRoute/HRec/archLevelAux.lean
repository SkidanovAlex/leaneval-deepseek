import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
import Submission.Work.SSGRoute.HRec.archUnitsDefs
import Submission.Work.SSGRoute.HRec.cupKummer_helpers
import Submission.Work.SSGRoute.HRec.exists_conjInv_kummerChar_eq_zero_iff
import Submission.Work.SSGRoute.HSTwoRow.procyclic_hypotheses
import Submission.Work.SSGRoute.PT.isCoboundary2On_of_proCyclic_growth
import Submission.Work.SSGRoute.PTCore.h2loc_mup_finrank
import Submission.Work.SSGRoute.ZDataTwo.ArchDictionary
import Submission.Work.SSGRoute.inertiaStructureOfFinPlace_zhat
import Submission.Work.SSGRoute.sha2_hasse.locUnits_levelClass_eq_zero_infinitePlace
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Auxiliary lemmas for the archimedean matching `cupKummer_archMatchK`

This file collects the archimedean dictionary steps that the assembly of
`Work.SSGRoute.HRec.cupKummer_archMatchK` needs, stated in terms of the level cup cocycle of
`cupKummer_matchK_forward`:

* `muKToL_injective`, `muKToL_eq_zero_or_negUnit` — the Kummer coefficient map `μ₂(K) → Lˣ` is
  an injection with values in `{0, -1}`;
* `realPlaceOfInvolution_isReal` — the real place attached to a non-trivial involution;
* `archInvolutionEmbedding` — a lift `Ψ : Ω →+* ℂ` of that real place which intertwines `c` with
  complex conjugation;
* `archStabGen_conjRes` — at every infinite place of a finite Galois level above that real place,
  a conjugate of the restriction of `c` acts by complex conjugation.
-/

open SSGRoute
open scoped TensorProduct

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000

namespace Work.SSGRoute.HRec

noncomputable section

/-! ## The Kummer coefficient map `μ₂(K) → Lˣ` -/

theorem muKToL_injective {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] (p : ℕ)
    (K L : IntermediateField k Ω) (hKL : K ≤ L) :
    Function.Injective (muKToL p K L hKL) := by
  have hcomp : Function.Injective
      (((Units.map (IntermediateField.inclusion hKL).toMonoidHom)).comp
        (rootsOfUnity p K).subtype) :=
    (Units.map_injective (IntermediateField.inclusion_injective hKL)).comp
      Subtype.coe_injective
  intro x y h
  have h' : ((Units.map (IntermediateField.inclusion hKL).toMonoidHom)).comp
      (rootsOfUnity p K).subtype (Additive.toMul x)
      = ((Units.map (IntermediateField.inclusion hKL).toMonoidHom)).comp
        (rootsOfUnity p K).subtype (Additive.toMul y) := h
  exact Additive.toMul.injective (hcomp h')

theorem muKToL_eq_zero_or_negUnit {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    (p : ℕ) (hp : p = 2) (K L : IntermediateField k Ω) (hKL : K ≤ L) [CharZero ↥L]
    (x : Work.SSGRoute.PTembedding.MupCard.MuAdd p K) :
    muKToL p K L hKL x = 0 ∨
      muKToL p K L hKL x = Additive.ofMul (Work.SSGRoute.HRec.negUnit ↥L) := by
  subst hp
  set u : (↥K)ˣ := (((Additive.toMul x : rootsOfUnity 2 K)) : (↥K)ˣ) with hu
  have hu2 : u ^ 2 = 1 := (Additive.toMul x : rootsOfUnity 2 K).2
  have huK : ((u : ↥K)) ^ 2 = 1 := by
    have h := congrArg (fun z : (↥K)ˣ => (z : ↥K)) hu2
    simpa using h
  have hfac : (((u : ↥K)) - 1) * (((u : ↥K)) + 1) = 0 := by
    calc (((u : ↥K)) - 1) * (((u : ↥K)) + 1) = ((u : ↥K)) ^ 2 - 1 := by ring
      _ = 0 := by rw [huK]; ring
  rcases mul_eq_zero.mp hfac with h | h
  · have hu1 : (((Additive.toMul x : rootsOfUnity 2 K)) : (↥K)ˣ) = 1 := by
      rw [← hu]; exact Units.ext (by simpa using sub_eq_zero.mp h)
    have hx0 : x = 0 := by
      have h0 : Additive.toMul (0 : Work.SSGRoute.PTembedding.MupCard.MuAdd 2 K) = 1 := rfl
      refine Additive.toMul.injective ?_
      rw [h0]
      exact Subtype.ext hu1
    left
    rw [hx0, map_zero]
  · have hum1 : (((Additive.toMul x : rootsOfUnity 2 K)) : (↥K)ˣ) = -1 := by
      rw [← hu]; exact Units.ext (by simpa using add_eq_zero_iff_eq_neg.mp h)
    right
    have hval : muKToL 2 K L hKL x = Additive.ofMul
        (Units.map (IntermediateField.inclusion hKL).toMonoidHom
          (((Additive.toMul x : rootsOfUnity 2 K)) : (↥K)ˣ)) := rfl
    have hunit : Units.map (IntermediateField.inclusion hKL).toMonoidHom (-1 : (↥K)ˣ)
        = Work.SSGRoute.HRec.negUnit ↥L := by
      apply Units.ext
      rw [Units.coe_map, Work.SSGRoute.HRec.negUnit_val]
      show IntermediateField.inclusion hKL ((-1 : (↥K)ˣ) : ↥K) = -1
      simp
    rw [hval, hum1, hunit]

/-! ## The real place of a non-trivial involution -/

private lemma toRingEquiv_mul_self {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    {c : Ω ≃ₐ[k] Ω} (hc : c ^ 2 = 1) : c.toRingEquiv * c.toRingEquiv = 1 := by
  rw [show c.toRingEquiv = (c : Ω ≃+* Ω) from rfl]
  have h2 : (c * c : Ω ≃ₐ[k] Ω) = 1 := by rw [← pow_two, hc]
  exact_mod_cast congrArg (fun e : Ω ≃ₐ[k] Ω => (e : Ω ≃+* Ω)) h2

private lemma toRingEquiv_ne_one {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    {c : Ω ≃ₐ[k] Ω} (hc1 : c ≠ 1) : c.toRingEquiv ≠ 1 := by
  intro h
  apply hc1
  ext x
  have := congrArg (fun e : Ω ≃+* Ω => e x) h
  simpa [show c.toRingEquiv = (c : Ω ≃+* Ω) from rfl] using this

theorem realPlaceOfInvolution_isReal {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (ζ : k) (hζ : IsPrimitiveRoot ζ 2)
    (c : Ω ≃ₐ[k] Ω) (hc : c ^ 2 = 1) (hc1 : c ≠ 1) :
    ∃ w : NumberField.InfinitePlace k, w.IsReal ∧
      ∀ a : kˣ, Work.SSGRoute.kummerChar (K := k) (Ω := Ω) ζ hζ a c = 0 ↔
        ¬ Work.SSGRoute.ZDataTwo.IsNegAt w a := by
  haveI : CharZero Ω :=
    charZero_of_injective_algebraMap (FaithfulSMul.algebraMap_injective k Ω)
  obtain ⟨w, hw⟩ := Work.SSGRoute.ZDataTwo.exists_realPlace_of_involution (Ω := Ω)
    ζ hζ c hc hc1
  have hzero : ∀ a : kˣ, Work.SSGRoute.kummerChar (K := k) (Ω := Ω) ζ hζ a c = 0 ↔
      ¬ Work.SSGRoute.ZDataTwo.IsNegAt w a := by
    intro a
    rw [Work.SSGRoute.ZDataTwo.zmodTwo_eq_zero_iff_ne_one]
    exact not_congr (hw a)
  have hne0 : Work.SSGRoute.kummerChar (K := k) (Ω := Ω) ζ hζ (-1 : kˣ) c ≠ 0 := by
    intro h0
    rw [Work.SSGRoute.ZDataTwo.kummerChar_eq_zero_iff_mem_normSet ζ hζ c hc (-1)] at h0
    exact Work.SSGRoute.TwoTorsion.neg_one_notMem_normSet c.toRingEquiv
      (toRingEquiv_mul_self hc) (toRingEquiv_ne_one hc1) (by simpa using h0)
  have hone : Work.SSGRoute.kummerChar (K := k) (Ω := Ω) ζ hζ (-1 : kˣ) c = 1 :=
    Work.SSGRoute.ZDataTwo.zmodTwo_eq_one_of_ne_zero' hne0
  exact ⟨w, ((hw (-1)).mp hone).isReal, hzero⟩

/-! ## The involution as complex conjugation of a lift -/

theorem archInvolutionEmbedding {k Ω : Type} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (ζ : k) (hζ : IsPrimitiveRoot ζ 2)
    (c : Ω ≃ₐ[k] Ω) (hc : c ^ 2 = 1) (hc1 : c ≠ 1)
    (w : NumberField.InfinitePlace k) (hw : w.IsReal)
    (hχ : ∀ a : kˣ, Work.SSGRoute.kummerChar (K := k) (Ω := Ω) ζ hζ a c = 0 ↔
      ¬ Work.SSGRoute.ZDataTwo.IsNegAt w a) :
    ∃ Ψ : Ω →+* ℂ, (∀ a : k, Ψ (algebraMap k Ω a) = w.embedding a) ∧
      (∀ x : Ω, Ψ (c x) = starRingEnd ℂ (Ψ x)) := by
  obtain ⟨Ψ₀, c₀, hΨ₀, hc₀2, hc₀⟩ := exists_involution_conj_comp (Ω := Ω) w hw
  have hχ₀ : ∀ a : kˣ, Work.SSGRoute.kummerChar (K := k) (Ω := Ω) ζ hζ a c₀ = 0 ↔
      ¬ Work.SSGRoute.ZDataTwo.IsNegAt w a :=
    fun a => kummerChar_eq_zero_iff_not_isNegAt ζ hζ w hw hc₀2 hΨ₀ hc₀ a
  have hnegun : Work.SSGRoute.ZDataTwo.IsNegAt w (-1 : kˣ) :=
    Work.SSGRoute.ZDataTwo.isNegAt_neg_one hw
  have hc₀1 : c₀ ≠ 1 := by
    intro h1
    have hone : Work.SSGRoute.kummerChar (K := k) (Ω := Ω) ζ hζ (-1 : kˣ) c₀ = 1 := by
      rw [Work.SSGRoute.ZDataTwo.zmodTwo_eq_one_iff_ne_zero]
      intro h0
      exact ((hχ₀ (-1)).mp h0) hnegun
    rw [h1, Work.SSGRoute.ZDataTwo.kummerChar_one ζ hζ (-1 : kˣ)] at hone
    exact zero_ne_one hone
  have hchar : ∀ a : kˣ, Work.SSGRoute.kummerChar (K := k) (Ω := Ω) ζ hζ a c = 0 ↔
      Work.SSGRoute.kummerChar (K := k) (Ω := Ω) ζ hζ a c₀ = 0 :=
    fun a => (hχ a).trans (hχ₀ a).symm
  obtain ⟨τ, hτ⟩ := Work.SSGRoute.ZDataTwo.conjugate_of_same_kummerChar ζ hζ c c₀ hc hc1
    hc₀2 hc₀1 hchar
  refine ⟨Ψ₀.comp (τ : Ω →+* Ω), ?_, ?_⟩
  · intro a
    have h1 : (τ : Ω →+* Ω) (algebraMap k Ω a) = algebraMap k Ω a := τ.commutes a
    rw [RingHom.comp_apply, h1, hΨ₀ a,
      NumberField.InfinitePlace.embedding_of_isReal_apply]
  · intro x
    have h1 : (τ : Ω →+* Ω) (c x) = c₀ ((τ : Ω →+* Ω) x) := by
      have h2 := congrArg (fun (e : Ω ≃ₐ[k] Ω) => e (τ x)) hτ
      have h3 : (τ * c * τ⁻¹ : Ω ≃ₐ[k] Ω) (τ x) = (τ : Ω →+* Ω) (c x) := by
        show (τ * c * τ⁻¹) (τ x) = (τ : Ω →+* Ω) (c x)
        rw [show τ⁻¹ = τ.symm from rfl, AlgEquiv.mul_apply, AlgEquiv.mul_apply,
          AlgEquiv.symm_apply_apply]
        rfl
      exact (h2.trans h3).symm
    change Ψ₀ ((τ : Ω →+* Ω) (c x)) = starRingEnd ℂ (Ψ₀ ((τ : Ω →+* Ω) x))
    rw [h1, hc₀]

/-! ## The conjugate of the restriction acts by complex conjugation -/

theorem archStabGen_conjRes {k Ω : Type} [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (L : IntermediateField k Ω) [FiniteDimensional k L] [IsGalois k L] [NumberField L]
    (c : Ω ≃ₐ[k] Ω)
    (v : NumberField.InfinitePlace L) (u : NumberField.InfinitePlace k)
    (hvu : v.LiesOver u) (hu : u.IsReal)
    (Ψ : Ω →+* ℂ) (hΨ : ∀ a : k, Ψ (algebraMap k Ω a) = u.embedding a)
    (hc : ∀ x : Ω, Ψ (c x) = starRingEnd ℂ (Ψ x)) :
    ∃ γ : L ≃ₐ[k] L,
      (∃ σ : L ≃ₐ[k] L, γ = σ * AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) L c * σ⁻¹) ∧
      (∀ x : L, v.embedding (γ x) = starRingEnd ℂ (v.embedding x)) := by
  set res : L ≃ₐ[k] L := AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) L c with hres
  let Λ : L →+* ℂ := Ψ.comp (algebraMap L Ω)
  -- `Λ` intertwines `res` with complex conjugation
  have hΛc : ∀ x : L, Λ (res x) = starRingEnd ℂ (Λ x) := by
    intro x
    have h1 : (↑(res x) : Ω) = c (algebraMap L Ω x) := by
      rw [hres]
      simpa using AlgEquiv.restrictNormalHom_apply (F := k) (K₁ := Ω) L c x
    show Ψ (algebraMap L Ω (↑(res x))) = starRingEnd ℂ (Ψ (algebraMap L Ω x))
    rw [show (algebraMap L Ω (↑(res x)) : Ω) = (↑(res x) : Ω) from rfl, h1, hc]
  -- `v.embedding` restricts to `u.embedding` on `k`
  have hvcomp : v.embedding.comp (algebraMap k L) = u.embedding := by
    rcases NumberField.InfinitePlace.LiesOver.embedding_comp_eq_or_conjugate_embedding_comp_eq
      v u with h | h
    · exact h
    · have hconj_u : NumberField.ComplexEmbedding.conjugate u.embedding = u.embedding := by
        rw [← NumberField.ComplexEmbedding.isReal_iff]
        exact NumberField.InfinitePlace.isReal_iff.mp hu
      have hc1 : NumberField.ComplexEmbedding.conjugate
          (v.embedding.comp (algebraMap k L)) = u.embedding := by
        rw [← h]
        exact NumberField.ComplexEmbedding.conjugate_comp v.embedding (algebraMap k L)
      have h2 := congrArg NumberField.ComplexEmbedding.conjugate hc1
      rwa [NumberField.ComplexEmbedding.involutive_conjugate _, hconj_u] at h2
  have hcomp : Λ.comp (algebraMap k L) = v.embedding.comp (algebraMap k L) := by
    rw [hvcomp]
    ext x
    show Ψ (algebraMap L Ω (algebraMap k L x)) = u.embedding x
    rw [show (algebraMap L Ω (algebraMap k L x) : Ω) = algebraMap k Ω x
      from IsScalarTower.algebraMap_apply k L Ω x, hΨ x]
  obtain ⟨σ, hσ⟩ := NumberField.ComplexEmbedding.exists_comp_symm_eq_of_comp_eq (K := L) (k := k)
    Λ v.embedding hcomp
  have hσ' : ∀ y : L, v.embedding y = Λ (σ.symm y) :=
    fun y => (RingHom.congr_fun hσ y).symm
  refine ⟨σ * res * σ⁻¹, ⟨σ, rfl⟩, ?_⟩
  intro x
  rw [hσ' ((σ * res * σ⁻¹) x), hσ' x]
  have h2 : σ.symm ((σ * res * σ⁻¹) x) = res (σ.symm x) := by
    show σ.symm (σ (res (σ⁻¹ x))) = res (σ.symm x)
    rw [AlgEquiv.symm_apply_apply]
    rfl
  rw [h2]
  exact hΛc (σ.symm x)

end

end Work.SSGRoute.HRec
