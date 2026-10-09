/-
Work of the Neukirch–Uchida team: the Čebotarev density theorem.
-/
import Mathlib
import Submission.NK.Chebotarev.Density
import Submission.NK.Chebotarev.IsFrobAtRestrictNormalHom
import Submission.NK.Chebotarev.Infinite
import Submission.NK.Chebotarev.FrobRestriction
import Submission.Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver
import Submission.Commons.NumberTheory.NumberField.numberField_of_intermediateField
import Submission.Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Frobenius elements of `Gal(K'/K)` with prescribed restriction to a normal subextension

Let `K` be a number field, `K'/K` a Galois extension and `L₀/K` a finite normal (hence Galois)
subextension.  Assume Čebotarev's theorem in the form `hC`: for every finite normal intermediate
field `L` and every `τ ∈ Gal(L/K)` there is a prime `p` of `K` and a prime `P` of `𝓞 L` above `p`,
unramified over `p`, at which `τ` is a Frobenius element.

Then every `τ₀ ∈ Gal(L₀/K)` is the restriction of an element `σ ∈ Gal(K'/K)` which is a Frobenius
element at a prime above one and the same prime `p` of `K` in *every* finite normal subextension:
there is `p` such that for each finite normal `L/K'`-intermediate `L` there is a prime `P` of `𝓞 L`
above `p` with `IsFrobAt P (σ|_L)`.

The proof is a compactness (finite intersection) argument.  The set of `σ ∈ Gal(K'/K)` whose
restriction to `M` is a Frobenius element at a prime above a fixed `p` for a *fixed* finite normal
`M ⊇ L₀` — and whose restriction to `L₀` is `τ₀` — is a closed subset of the compact group
`Gal(K'/K)`, and the family of these subsets indexed by `M` is directed under inclusion because
Frobenius elements restrict to Frobenius elements.  The intersection over a compositum is
contained in each member, so the family has the finite intersection property; compactness gives a
common element.
-/

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace NK.Chebotarev

open IsDedekindDomain

/-! ## Extending a Frobenius element with a prescribed restriction

The finite-intersection property is verified at a finite set of levels by first extending the data
at the compositum of the levels. -/

/-- **An element of `Gal(K'/K)` restricting to `τ₀` on `L₀` and being a Frobenius element at a
prime above `p` on `M`.**  Here `L₀ ≤ M` are finite normal intermediate fields and `τ₀` is a
Frobenius element at the prime `P₀` of `𝓞 L₀`, unramified over `p`. -/
theorem exists_sigma_restrict_eq_and_isFrobAtPrime {K K' : Type*} [Field K] [NumberField K]
    [Field K'] [Algebra K K'] [IsGalois K K']
    (L₀ M : IntermediateField K K') (h : L₀ ≤ M)
    [FiniteDimensional K L₀] [Normal K L₀] [NumberField ↥L₀]
    [FiniteDimensional K M] [Normal K M] [NumberField ↥M]
    (p : PrimeIdeal K) (P₀ : PrimeIdeal ↥L₀) (τ₀ : Gal(↥L₀/K))
    (hP₀ : P₀.asIdeal.LiesOver p.asIdeal)
    (he₀ : P₀.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1)
    (hτ₀ : IsFrobAt P₀ τ₀) :
    ∃ σ : Gal(K'/K), AlgEquiv.restrictNormalHom (F := K) (K₁ := K') L₀ σ = τ₀ ∧
      IsFrobAtPrime (K := K) (L := ↥M) p
        (AlgEquiv.restrictNormalHom (F := K) (K₁ := K') M σ) := by
  haveI : IsGalois K ↥M := Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
  haveI : IsGalois K ↥L₀ := Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
  letI : Algebra ↥L₀ ↥M := (Subsemiring.inclusion h).toAlgebra
  haveI htow₁ : IsScalarTower K ↥L₀ ↥M := IsScalarTower.of_algebraMap_eq fun x => rfl
  haveI htow₂ : IsScalarTower ↥L₀ ↥M K' := IsScalarTower.of_algebraMap_eq fun x => rfl
  -- A prime of `𝓞 M` above `P₀`.
  obtain ⟨Q, hQlies⟩ :=
    Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver (K := ↥L₀) (L := ↥M) P₀
  have hQp : Q.asIdeal.LiesOver p.asIdeal := by
    refine ⟨?_⟩
    rw [hP₀.over, hQlies.over, Ideal.under_under]
  -- A Frobenius element at `Q`, together with the identification of the prime below it with `P₀`.
  obtain ⟨ρ, hρ⟩ := exists_isFrobAt (K := K) (L := ↥M) p Q hQp
  have hQund : Q.under (NumberField.RingOfIntegers ↥L₀) = P₀ := by
    ext : 1
    exact hQlies.over.symm
  have hρL₀ : IsFrobAt P₀ (AlgEquiv.restrictNormalHom (F := K) (K₁ := ↥M) ↥L₀ ρ) := by
    rw [← hQund]
    exact isFrobAt_restrictNormalHom_le L₀ M h hρ
  have hρτ₀ : AlgEquiv.restrictNormalHom (F := K) (K₁ := ↥M) ↥L₀ ρ = τ₀ :=
    IsFrobAt.eq_of_isFrobAt hP₀ he₀ hρL₀ hτ₀
  -- Lift `ρ` to `Gal(K'/K)`.
  obtain ⟨σ, hσ⟩ :=
    AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := ↥M) (E := K') ρ
  refine ⟨σ, ?_, ⟨Q, hQp, ?_⟩⟩
  · rw [restrictNormalHom_le_comp L₀ M h σ, hσ, hρτ₀]
  · rw [hσ]
    exact hρ

/-! ## The compactness argument -/

theorem ExistsFrobeniusOfRestriction {K K' : Type*} [Field K] [NumberField K] [Field K']
    [Algebra K K'] [IsGalois K K']
    (hC : ∀ (L : IntermediateField K K') [FiniteDimensional K L] [Normal K L] [NumberField ↥L]
      (τ : Gal(↥L/K)), ∃ p : NK.Chebotarev.PrimeIdeal K, ∃ P : NK.Chebotarev.PrimeIdeal ↥L,
        P.asIdeal.LiesOver p.asIdeal ∧
        P.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1 ∧
        NK.Chebotarev.IsFrobAt P τ)
    (L₀ : IntermediateField K K') [FiniteDimensional K L₀] [Normal K L₀] [NumberField ↥L₀]
    (τ₀ : Gal(↥L₀/K)) :
    ∃ σ : Gal(K'/K), AlgEquiv.restrictNormalHom L₀ σ = τ₀ ∧ ∃ p : NK.Chebotarev.PrimeIdeal K,
      ∀ (L : IntermediateField K K') [FiniteDimensional K L] [Normal K L] [NumberField ↥L],
        ∃ P : NK.Chebotarev.PrimeIdeal ↥L, P.asIdeal.LiesOver p.asIdeal ∧
          NK.Chebotarev.IsFrobAt P (AlgEquiv.restrictNormalHom L σ) := by
  classical
  -- The Čebotarev hypothesis at `L₀` provides the prime `p` and the prime `P₀` of `𝓞 L₀`.
  obtain ⟨p, P₀, hP₀, he₀, hτ₀⟩ := hC L₀ τ₀
  -- The index set: the finite normal intermediate fields containing `L₀`.
  let ι := {M : IntermediateField K K' // L₀ ≤ M ∧ FiniteDimensional K M ∧ Normal K M ∧
    NumberField ↥M}
  -- The family of conditions: `σ` restricts to a Frobenius element at a prime above `p` on `M`,
  -- and to `τ₀` on `L₀`.
  let t : ι → Set Gal(K'/K) := fun M => by
    letI : FiniteDimensional K M.1 := M.2.2.1
    letI : Normal K M.1 := M.2.2.2.1
    letI : NumberField ↥M.1 := M.2.2.2.2
    exact {σ : Gal(K'/K) |
      IsFrobAtPrime (K := K) (L := ↥M.1) p
          (AlgEquiv.restrictNormalHom (F := K) (K₁ := K') M.1 σ) ∧
        AlgEquiv.restrictNormalHom (F := K) (K₁ := K') L₀ σ = τ₀}
  haveI hιne : Nonempty ι :=
    ⟨⟨L₀, le_rfl, inferInstance, inferInstance, inferInstance⟩⟩
  -- The family is directed: the condition at a compositum implies the conditions at the factors.
  have hdir : Directed (· ⊇ ·) t := by
    intro M₁ M₂
    haveI : FiniteDimensional K M₁.1 := M₁.2.2.1
    haveI : Normal K M₁.1 := M₁.2.2.2.1
    haveI : NumberField ↥M₁.1 := M₁.2.2.2.2
    haveI : FiniteDimensional K M₂.1 := M₂.2.2.1
    haveI : Normal K M₂.1 := M₂.2.2.2.1
    haveI : NumberField ↥M₂.1 := M₂.2.2.2.2
    haveI : FiniteDimensional K ↥(M₁.1 ⊔ M₂.1) := inferInstance
    haveI : Normal K ↥(M₁.1 ⊔ M₂.1) := inferInstance
    haveI : NumberField ↥(M₁.1 ⊔ M₂.1) :=
      Commons.NumberTheory.NumberField.numberField_of_intermediateField (K := K) (K' := K')
        (M₁.1 ⊔ M₂.1)
    refine ⟨⟨M₁.1 ⊔ M₂.1, M₁.2.1.trans le_sup_left, inferInstance, inferInstance,
      inferInstance⟩, ?_, ?_⟩
    · intro σ hσ
      exact ⟨exists_isFrobAtPrime_of_le M₁.1 (M₁.1 ⊔ M₂.1) le_sup_left hσ.1, hσ.2⟩
    · intro σ hσ
      exact ⟨exists_isFrobAtPrime_of_le M₂.1 (M₁.1 ⊔ M₂.1) le_sup_right hσ.1, hσ.2⟩
  -- Each condition is satisfied.
  have hne : ∀ M : ι, (t M).Nonempty := by
    intro M
    haveI : FiniteDimensional K M.1 := M.2.2.1
    haveI : Normal K M.1 := M.2.2.2.1
    haveI : NumberField ↥M.1 := M.2.2.2.2
    obtain ⟨σ, hσ₁, hσ₂⟩ :=
      exists_sigma_restrict_eq_and_isFrobAtPrime L₀ M.1 M.2.1 p P₀ τ₀ hP₀ he₀ hτ₀
    exact ⟨σ, hσ₂, hσ₁⟩
  -- Each condition is closed: it is the preimage of a subset of the finite group `Gal(↥M/K)`.
  have hcl : ∀ M : ι, IsClosed (t M) := by
    intro M
    haveI : FiniteDimensional K M.1 := M.2.2.1
    haveI : Normal K M.1 := M.2.2.2.1
    haveI : NumberField ↥M.1 := M.2.2.2.2
    have h₁ : IsClosed ((AlgEquiv.restrictNormalHom (F := K) (K₁ := K') M.1) ⁻¹'
        {ρ : Gal(↥M.1/K) | IsFrobAtPrime (K := K) (L := ↥M.1) p ρ}) :=
      IsClosed.preimage (InfiniteGalois.restrictNormalHom_continuous M.1) (isClosed_discrete _)
    have h₂ : IsClosed ((AlgEquiv.restrictNormalHom (F := K) (K₁ := K') L₀) ⁻¹' {τ₀}) :=
      IsClosed.preimage (InfiniteGalois.restrictNormalHom_continuous L₀) (isClosed_discrete _)
    rw [show t M = ((AlgEquiv.restrictNormalHom (F := K) (K₁ := K') M.1) ⁻¹'
          {ρ : Gal(↥M.1/K) | IsFrobAtPrime (K := K) (L := ↥M.1) p ρ}) ∩
          ((AlgEquiv.restrictNormalHom (F := K) (K₁ := K') L₀) ⁻¹' {τ₀}) from by
      ext σ
      exact Iff.rfl]
    exact h₁.inter h₂
  -- Compactness: the intersection of the family is nonempty.
  obtain ⟨σ, hσ⟩ :=
    IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed t hdir hne
      (fun M => (hcl M).isCompact) hcl
  have hL₀ : AlgEquiv.restrictNormalHom (F := K) (K₁ := K') L₀ σ = τ₀ :=
    (Set.mem_iInter.mp hσ ⟨L₀, le_rfl, inferInstance, inferInstance, inferInstance⟩).2
  refine ⟨σ, hL₀, p, ?_⟩
  intro L FinL NormL NFL
  haveI : FiniteDimensional K L := FinL
  haveI : Normal K L := NormL
  haveI : NumberField ↥L := NFL
  haveI : FiniteDimensional K ↥(L₀ ⊔ L) := inferInstance
  haveI : Normal K ↥(L₀ ⊔ L) := inferInstance
  haveI : NumberField ↥(L₀ ⊔ L) :=
    Commons.NumberTheory.NumberField.numberField_of_intermediateField (K := K) (K' := K')
      (L₀ ⊔ L)
  exact exists_isFrobAtPrime_of_le L (L₀ ⊔ L) le_sup_right
    (Set.mem_iInter.mp hσ ⟨L₀ ⊔ L, le_sup_left, inferInstance, inferInstance, inferInstance⟩).1

end NK.Chebotarev
