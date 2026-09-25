import Submission.NeukirchUchida.Local.PlaceFromValuation
import Submission.Commons.NumberTheory.NumberField.Valuation.centralizer_stabilizer_valuationSubring_sepClosure
import Submission.Commons.NumberTheory.NumberField.Valuation.normalizer_stabilizer_valuationSubring_sepClosure
import Submission.Commons.NumberTheory.NumberField.Valuation.exists_valuationSubring_at_prime
import Submission.Commons.NumberTheory.NumberField.exists_prime_splitsCompletely
import Submission.Commons.FieldTheory.Galois.exists_finite_galois_containing
import Submission.Commons.NumberTheory.NumberField.ncard_primesOver_eq_finrank_iff_splitCompletely
import Submission.Commons.NumberTheory.NumberField.Completion.decompositionSubgroup_eq_bot_iff_ramificationIdx_eq_one_and_inertiaDeg_eq_one
import Submission.NeukirchUchida.Local.LocalGalois

/-!
# Triviality of the centre of the absolute Galois group, reduced to rigidity of places

Reference: J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*,
2nd ed., Springer 2008, Corollary 12.1.3 and Corollary 12.1.6.

The centre of the absolute Galois group `G_F` of a number field `F` is trivial (CoNF (12.1.6)).
The book proves this from the *disjointness of decomposition groups* (CoNF (12.1.3)), and the
argument is purely formal given two arithmetic inputs:

* **Rigidity of places** (`PlaceRigidity` below): an element of `Gal(F'/F)` commuting with every
  element of the decomposition group `D_A ≤ Gal(F'/F)` of a place `A` of `F'` over a finite prime
  of `F` already lies in `D_A`.  Equivalently, the normalizer of a decomposition group is the
  decomposition group, i.e. a place of the separable closure is determined by its decomposition
  group.

* **Existence of places** (`PlaceExists` below): every finite prime of `F` has at least one
  extension to `F'`.

Given these, the proof is: let `c` commute with all of `Gal(F'/F)`.  Fix `x ∈ F'` and a finite
Galois `L ⊆ F'` containing `x`, and let `p` be a prime of `F` splitting completely in `L`
(which exists by `Commons.NumberTheory.NumberField.exists_prime_splitsCompletely`).  By rigidity
`c` lies in the decomposition group of every place `A` of `F'` above `p`; restricting to `L`,
`c|_L` lies in the decomposition group of the prime `w` of `L` cut out by `A`.  Since `p` splits
completely in `L`, that decomposition group is trivial, so `c|_L = 1`, and in particular
`c x = x`.

Thus the whole difficulty of (12.1.6) is concentrated in the two statements `PlaceRigidity` and
`PlaceExists`; neither of them involves class field theory.
-/

open scoped Pointwise NumberField

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Submission.NeukirchUchida

variable {F F' : Type*} [Field F] [NumberField F] [Field F'] [Algebra F F']

/-- **Rigidity of places of the separable closure.**

An element of `Gal(F'/F)` which commutes with every element of the decomposition group of a place
`A` of the separable closure `F'` lying over a finite prime `p` of `F` itself lies in that
decomposition group.  Here the decomposition group is described by the condition
`A.comap (τ : F' →+* F') = A`, which says that `τ` preserves the valuation subring `A`, i.e.
fixes the place.

Note that the corresponding statement for a *finite* Galois extension `F'/F` is false: if `p`
splits completely in `F'/F` then every decomposition group is trivial while its centralizer is
all of `Gal(F'/F)`.  It is essential that `F'` is a separable closure, so that decomposition
groups are the full local Galois groups. -/
def PlaceRigidity (F F' : Type*) [Field F] [NumberField F] [Field F'] [Algebra F F']
    [IsSepClosure F F'] : Prop :=
  ∀ (p : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (A : ValuationSubring F'),
    A.comap (algebraMap F F') =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime F p →
      ∀ σ : F' ≃ₐ[F] F',
        (∀ τ : F' ≃ₐ[F] F', A.comap (τ : F' →+* F') = A → σ * τ = τ * σ) →
          A.comap (σ : F' →+* F') = A

section Main

variable [IsSepClosure F F']

/-- **Triviality of the centre of the absolute Galois group**, from rigidity of places
(CoNF (12.1.6) via (12.1.3)). -/
theorem center_trivial_of_placeRigidity (hR : PlaceRigidity F F') :
    ∀ c : Gal(F'/F), (∀ g : Gal(F'/F), c * g = g * c) → c = 1 := by
  intro c hc
  ext x
  obtain ⟨L, hLfin, hLgal, hxL⟩ :=
    Commons.FieldTheory.Galois.exists_finite_galois_containing (k := F) (K := F') x
  haveI := hLfin
  haveI : Normal F ↥L := hLgal.to_normal
  obtain ⟨p, hp⟩ :=
    Commons.NumberTheory.NumberField.exists_prime_splitsCompletely (K := F) (L := ↥L)
  obtain ⟨A, hA⟩ :=
    Commons.NumberTheory.NumberField.Valuation.exists_valuationSubring_at_prime (K := F) (K' := F') p
  -- `c` commutes with the decomposition group of the place `A`, hence lies in it
  have hmem : A.comap (c : F' →+* F') = A :=
    hR p A hA c fun τ _ => hc τ
  have hstab : c ∈ MulAction.stabilizer (F' ≃ₐ[F] F') A := by
    rw [Local.mem_stabilizer_valuationSubring_iff]
    intro y
    have h := congrArg (fun (B : ValuationSubring F') => y ∈ B) hmem
    simpa [ValuationSubring.mem_comap] using h.symm
  -- the place of `L` cut out by `A`, over which `c|_L` lies in the decomposition group
  have hD : AlgEquiv.restrictNormalHom (F := F) (K₁ := F') ↥L c ∈
      Local.decompositionSubgroup (K := F) (Local.placeOf p A hA L) :=
    Local.restrictNormalHom_mem_decompositionSubgroup_of_mem_stabilizer A L (Local.placeOf p A hA L)
      (Local.comap_eq_valuationSubringAtPrime_placeOf p A hA L) c hstab
  -- that decomposition group is trivial because `p` splits completely in `L`
  have hbot : Local.decompositionSubgroup (K := F) (Local.placeOf p A hA L) = ⊥ := by
    rw [Subgroup.eq_bot_iff_card,
      Local.card_decompositionSubgroup p (Local.placeOf p A hA L)
        (Local.placeOf_liesOver p A hA L)]
    obtain ⟨h1, h2⟩ :=
      (Commons.NumberTheory.NumberField.ncard_primesOver_eq_finrank_iff_splitCompletely (K := F) (L := ↥L) p).mp hp
    simp [h1, h2]
  rw [hbot] at hD
  have hone : AlgEquiv.restrictNormalHom (F := F) (K₁ := F') ↥L c = 1 := by simpa using hD
  have hx : (AlgEquiv.restrictNormalHom (F := F) (K₁ := F') ↥L c) ⟨x, hxL⟩ = ⟨x, hxL⟩ := by
    rw [hone]; rfl
  have h3 : algebraMap ↥L F'
      ((AlgEquiv.restrictNormalHom (F := F) (K₁ := F') ↥L c) ⟨x, hxL⟩) = c x := by
    rw [Local.restrictNormalHom_apply_algebraMap L c ⟨x, hxL⟩]
    rfl
  rw [hx] at h3
  simpa using h3.symm

end Main


section Unconditional

variable [IsSepClosure F F']

/-- **Place rigidity holds** (CoNF XII (12.1.4), from the disjointness of decomposition groups
(12.1.3) and their nontriviality): the centralizer of the decomposition group of a place of the
separable closure is contained in it. -/
theorem placeRigidity : PlaceRigidity F F' :=
  fun p A hA σ hσ =>
    Commons.NumberTheory.NumberField.Valuation.centralizer_stabilizer_valuationSubring_sepClosure
      p A hA σ hσ

/-- **The centre of the absolute Galois group of a number field is trivial** (CoNF (12.1.6)). -/
theorem center_trivial_of_sepClosure (c : Gal(F'/F))
    (h : ∀ g : Gal(F'/F), c * g = g * c) : c = 1 :=
  center_trivial_of_placeRigidity placeRigidity c h

end Unconditional


/-- **Place rigidity in its strong form** (CoNF XII (12.1.3)/(12.1.4)): the normalizer of the
decomposition group of a place of the separable closure is the decomposition group itself, i.e. a
place of the separable closure is determined by its decomposition group.  This is the form needed
for the *existence* half of Neukirch–Uchida (it is the "only if" direction of Neukirch's
characterization (12.1.9) of decomposition groups among the closed subgroups of `G_F`). -/
theorem normalizer_stabilizer_valuationSubring_sepClosure_unconditional {K K' : Type*} [Field K]
    [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K']
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (A : ValuationSubring K')
    (hA : A.comap (algebraMap K K') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K p)
    (σ : K' ≃ₐ[K] K')
    (hσ : ∀ τ : K' ≃ₐ[K] K', A.comap (τ : K' →+* K') = A →
      A.comap ((σ * τ * σ⁻¹ : K' ≃ₐ[K] K') : K' →+* K') = A) :
    A.comap (σ : K' →+* K') = A :=
  Commons.NumberTheory.NumberField.Valuation.normalizer_stabilizer_valuationSubring_sepClosure
    p A hA σ hσ

end Submission.NeukirchUchida
