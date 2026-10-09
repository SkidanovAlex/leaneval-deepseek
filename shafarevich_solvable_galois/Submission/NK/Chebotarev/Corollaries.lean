/-
Work of the Neukirch–Uchida team: the Čebotarev density theorem.
-/
import Submission.NK.Chebotarev.Abelian
import Submission.NK.Chebotarev.FrobeniusGenerateTop
import Submission.NK.Chebotarev.EquivDeterminedByFrobenius
import Submission.NK.Chebotarev.Infinite
import Submission.NK.Chebotarev.AbelianChebotarevOfLFunctions
import Submission.NK.Chebotarev.HasDirichletDensityFrobClassOfCharacterData
import Submission.NK.Chebotarev.AbelianChebotarevOfArtinReciprocity
import Submission.NK.Chebotarev.DenseFrobeniusSet
import Submission.NK.Chebotarev.FrobeniusCorrespondence
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Corollaries of Čebotarev

The consequences of the density theorem that are used downstream: the Frobenius elements of a
prescribed class are infinite in number (`infinite_setOf_isFrobAtPrime_of_kroneckerWeber`), the
Frobenius elements generate the Galois group (`FrobeniusGenerateTop`), and a group isomorphism is
determined by its values on Frobenius elements (`EquivDeterminedByFrobenius`).
-/

set_option linter.unusedSectionVars false

namespace NK.Chebotarev

universe u

/-- **The set of primes with a prescribed Frobenius is infinite** (abelian extensions of `ℚ`,
conditional on Kronecker–Weber).  This is the form of Čebotarev used to produce primes with a
prescribed decomposition behaviour. -/
theorem infinite_setOf_isFrobAtPrime_of_kroneckerWeber (hKW : KroneckerWeber.{u})
    {L : Type u} [Field L] [NumberField L] [IsGalois ℚ L]
    (hcomm : ∀ a b : Gal(L/ℚ), a * b = b * a) (σ : Gal(L/ℚ)) :
    {p : PrimeIdeal ℚ | IsFrobAtPrime (K := ℚ) (L := L) p σ}.Infinite :=
  infinite_of_hasDirichletDensity_pos (abelianChebotarev_of_kroneckerWeber hKW hcomm σ)
    (by
      have h := Module.finrank_pos (R := ℚ) (M := L)
      positivity)

/-- **The set of primes with a prescribed Frobenius is infinite** for an abelian extension with
the Hecke `L`-function input. -/
theorem infinite_setOf_isFrobAtPrime_of_abelianLFunctions {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (hcomm : ∀ a b : Gal(L/K), a * b = b * a) (h : AbelianLFunctions K L) (σ : Gal(L/K)) :
    {p : PrimeIdeal K | IsFrobAtPrime (K := K) (L := L) p σ}.Infinite :=
  infinite_of_hasDirichletDensity_pos (AbelianChebotarevOfLFunctions hcomm h σ)
    (by
      haveI : Nonempty (Gal(L/K)) := ⟨1⟩
      rw [one_div]
      exact inv_pos.mpr (by exact_mod_cast Nat.card_pos))

/-- **Infinitely many primes have Frobenius in a prescribed conjugacy class** (for a finite Galois
extension, from the character-data formulation of Artin reciprocity).  This is the qualitative form
of Čebotarev used to produce primes with prescribed decomposition behaviour. -/
theorem infinite_setOf_isConj_frobAtPrime_of_characterData {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    {ι : Type*} [Fintype ι] (χ : ι → Gal(L/K) → ℂ) (i₀ : ι)
    (hχ_class : ∀ (i : ι) (g h : Gal(L/K)), χ i (h⁻¹ * g * h) = χ i g)
    (hχ_triv : ∀ g : Gal(L/K), χ i₀ g = 1)
    (horth_off : ∀ g h : Gal(L/K), ¬ IsConj g h → ∑ i, χ i g * star (χ i h) = 0)
    (hnorm : ∀ g : Gal(L/K),
      ∑ i, χ i g * star (χ i g) =
        (Nat.card (Subgroup.centralizer ({g} : Set (Gal(L/K)))) : ℂ))
    (han : ∀ i : ι, i ≠ i₀ → (fun s : ℝ =>
      ∑' p : PrimeIdeal K,
        star (χ i (frobAtPrime (K := K) (L := L) p)) *
          (((Ideal.absNorm p.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ))
      =O[nhdsWithin (1 : ℝ) (Set.Ioi 1)] (fun _ : ℝ => (1 : ℂ)))
    (g₀ : Gal(L/K)) :
    {p : PrimeIdeal K | IsConj (frobAtPrime (K := K) (L := L) p) g₀}.Infinite :=
  infinite_of_hasDirichletDensity_pos
    (HasDirichletDensityFrobClassOfCharacterData χ i₀ hχ_class hχ_triv horth_off hnorm han g₀)
    (by
      haveI : Nonempty {x : Gal(L/K) // IsConj x g₀} := ⟨g₀, IsConj.refl g₀⟩
      haveI : Nonempty (Gal(L/K)) := ⟨1⟩
      have h1 : 0 < (Nat.card {x : Gal(L/K) // IsConj x g₀} : ℝ) := by
        exact_mod_cast Nat.card_pos
      have h2 : 0 < (Nat.card (Gal(L/K)) : ℝ) := by exact_mod_cast Nat.card_pos
      positivity)

end NK.Chebotarev
