import Mathlib
import Submission.NumberField.TameTowerRoute
import Submission.NumberField.MaximalProPOutsideS
import Submission.Commons.NumberTheory.NumberField.natAbs_discr_le_pow_of_tame_different
import Submission.Commons.NumberTheory.NumberField.ramificationIdx_dvd_two_pow_of_isPGroup
import Submission.Commons.NumberTheory.NumberField.isTotallyReal_of_isUnramifiedAtInfinitePlaces

set_option linter.style.haveILetI false

/-!
# The tame tower reduction, final form: the challenge follows from ONE infinitude statement

**STATUS: sorry-free.**  ON the `Submission.lean` proof path since SESSION 279 (the on-path
proof of the benchmark statement runs through `MartinetTameWall`, which lives here).

`Submission/NumberField/TameTowerRoute.lean` reduced the benchmark statement

  `∃ C > 0, ∀ N, ∃ d ≥ N, ∃ K totally real, [K : ℚ] = d ∧ |disc K| ≤ C ^ d`

to the hypothesis that the levels of a tame pro-`2` tower over a totally real base satisfy the
tame discriminant bound.  THIS module discharges that hypothesis for every level of the
MAXIMAL pro-`2` extension of a totally real base field `F` that is

* unramified outside a fixed finite set `S` of ODD primes (so every level is ramified only at
  primes over `S`, at which the ramification is TAME: a `2`-power ramification index at an odd
  prime is coprime to it), and
* unramified at the infinite places of `F` (so every level is totally real, as `F` is).

The only remaining input is the classical GOLOD--SHAFAREVICH statement that this maximal
extension is INFINITE.  Concretely we record:

* `exists_totallyReal_discr_le_of_infinite_pro2_tame` -- the reduction from an infinite pro-`2`
  extension whose levels are totally real and `S`-supported;
* `exists_totallyReal_discr_le_of_infinite_maximal_proP` -- the same, with the level properties
  supplied for the maximal extension `K` constructed by
  `Submission.NumberField.exists_maximal_proP_field_unramifiedOutside_inf`;
* `MartinetTameWall` and `exists_totallyReal_discr_le_of_martinetTameWall` -- the single
  remaining arithmetic statement, packaged as a `Prop`, and the implication to the benchmark.
-/

open scoped NumberField
open NumberField

noncomputable section

namespace Submission.NumberField

/-- **The tame tower reduction, pro-`2` form.**  Let `F` be a totally real number field, `S` a
finite set of ODD primes, and `K/F` an INFINITE Galois extension whose finite dimensional Galois
subextensions `L` are pro-`2`, totally real, and have their relative different supported on `S`.
Then the benchmark statement holds.

The proof is the tameness computation: for a level `L`, every ramification index at a prime over
`q ∈ S` divides `[L : F]`, which is a power of `2`, hence is coprime to `q ≠ 2`; so
`natAbs_discr_le_pow_of_tame_different` applies. -/
theorem exists_totallyReal_discr_le_of_infinite_pro2_tame
    {S : Finset ℕ} (hS : ∀ q ∈ S, Nat.Prime q) (hodd : ∀ q ∈ S, q ≠ 2)
    {F : Type} [Field F] [NumberField F] [NumberField.IsTotallyReal F]
    {K : Type} [Field K] [Algebra F K] [IsGalois F K] (hinf : Infinite (K ≃ₐ[F] K))
    (hpro : ∀ (L : IntermediateField F K) [NumberField ↥L], FiniteDimensional F L →
      IsGalois F L → IsPGroup 2 (L ≃ₐ[F] L))
    (htr : ∀ (L : IntermediateField F K) [NumberField ↥L], FiniteDimensional F L →
      IsGalois F L → NumberField.IsTotallyReal ↥L)
    (hsup : ∀ (L : IntermediateField F K) [NumberField ↥L], FiniteDimensional F L →
      IsGalois F L →
      ∀ (P : Ideal (𝓞 ↥L)), P.IsPrime → P ≠ ⊥ → P ∣ differentIdeal (𝓞 F) (𝓞 ↥L) →
        ∃ q ∈ S, P.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ))) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∃ d : ℕ, N ≤ d ∧
      ∃ (K' : Type) (_ : Field K') (_ : NumberField K') (_ : NumberField.IsTotallyReal K'),
        Module.finrank ℚ K' = d ∧ |(NumberField.discr K' : ℝ)| ≤ C ^ d := by
  classical
  refine exists_totallyReal_discr_le_of_infinite_tame_pro2 hS hinf htr ?_
  intro L hnumL hfdL hgalL
  haveI : NumberField ↥L := hnumL
  haveI : FiniteDimensional F ↥L := hfdL
  haveI : IsGalois F ↥L := hgalL
  refine Commons.NumberTheory.NumberField.natAbs_discr_le_pow_of_tame_different (F := F)
    (L := ↥L) S hS (hsup L hfdL hgalL) ?_
  intro q hq P hPmax hPlies
  haveI : P.IsPrime := hPmax.isPrime
  obtain ⟨k, hk⟩ :=
    Commons.NumberTheory.NumberField.ramificationIdx_dvd_two_pow_of_isPGroup (F := F)
      (L := ↥L) (hpro L hfdL hgalL) P
  rw [hk]
  exact not_dvd_of_dvd_two_pow (hS q hq) (hodd q hq) (dvd_refl _)

/-- **The tame tower reduction from the MAXIMAL extension.**  `K` is supposed to be the maximal
pro-`2` extension of `F` unramified outside `S` and at the infinite places -- i.e. the `K`
produced by `Submission.NumberField.exists_maximal_proP_field_unramifiedOutside_inf`; its two
structural properties are taken as hypotheses (`huni`: universal property, `hsub`: the property
of its finite dimensional Galois subextensions), and the remaining input is `Infinite (K ≃ₐ[F] K)`. -/
theorem exists_totallyReal_discr_le_of_infinite_maximal_proP
    {F : Type} [Field F] [NumberField F] [NumberField.IsTotallyReal F]
    {K : Type} [Field K] [Algebra F K] [IsGalois F K]
    {S : Finset ℕ} (hS : ∀ q ∈ S, Nat.Prime q) (hodd : ∀ q ∈ S, q ≠ 2)
    (hsub : ∀ (L : IntermediateField F K) [NumberField ↥L], FiniteDimensional F L →
      IsGalois F L →
      IsPGroup 2 (L ≃ₐ[F] L) ∧
        (∀ (P : Ideal (𝓞 ↥L)), P.IsPrime → P ≠ ⊥ → P ∣ differentIdeal (𝓞 F) (𝓞 ↥L) →
          ∃ q ∈ S, P.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ))) ∧
        IsUnramifiedAtInfinitePlaces F ↥L)
    (hinf : Infinite (K ≃ₐ[F] K)) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∃ d : ℕ, N ≤ d ∧
      ∃ (K' : Type) (_ : Field K') (_ : NumberField K') (_ : NumberField.IsTotallyReal K'),
        Module.finrank ℚ K' = d ∧ |(NumberField.discr K' : ℝ)| ≤ C ^ d := by
  classical
  refine exists_totallyReal_discr_le_of_infinite_pro2_tame hS hodd hinf ?_ ?_ ?_
  · intro L hnumL hfdL hgalL
    haveI : NumberField ↥L := hnumL
    exact (hsub L hfdL hgalL).1
  · intro L hnumL hfdL hgalL
    haveI : NumberField ↥L := hnumL
    haveI : FiniteDimensional F ↥L := hfdL
    haveI : IsGalois F ↥L := hgalL
    haveI : IsUnramifiedAtInfinitePlaces F ↥L := (hsub L hfdL hgalL).2.2
    exact Commons.NumberTheory.NumberField.isTotallyReal_of_isUnramifiedAtInfinitePlaces F ↥L
  · intro L hnumL hfdL hgalL
    haveI : NumberField ↥L := hnumL
    exact (hsub L hfdL hgalL).2.1

/-- **THE WALL.**  The single remaining arithmetic statement of Martinet's theorem in the tame
tower formulation: there is a totally real base field `F`, a finite set `S` of odd primes and an
INFINITE Galois extension `K/F` all of whose finite dimensional Galois subextensions are pro-`2`,
totally real, and ramified only at the primes over `S`.

(Equivalently -- see `Submission/NumberField/MaximalProPOutsideS.lean` -- it suffices that the
maximal pro-`2` extension of a totally real `F` unramified outside `S` and at the infinite places
is infinite; the existence of the maximal extension itself is formalised there, with no class
field theory.) -/
def MartinetTameWall : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : NumberField F) (_ : NumberField.IsTotallyReal F)
    (S : Finset ℕ), (∀ q ∈ S, Nat.Prime q) ∧ (∀ q ∈ S, q ≠ 2) ∧
    ∃ (K : Type) (_ : Field K) (_ : Algebra F K) (_ : IsGalois F K),
      Infinite (K ≃ₐ[F] K) ∧
      (∀ (L : IntermediateField F K) [NumberField ↥L], FiniteDimensional F L → IsGalois F L →
        IsPGroup 2 (L ≃ₐ[F] L) ∧
          (∀ (P : Ideal (𝓞 ↥L)), P.IsPrime → P ≠ ⊥ → P ∣ differentIdeal (𝓞 F) (𝓞 ↥L) →
            ∃ q ∈ S, P.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ))) ∧
          IsUnramifiedAtInfinitePlaces F ↥L)

/-- **The benchmark statement follows from THE WALL.** -/
theorem exists_totallyReal_discr_le_of_martinetTameWall (h : MartinetTameWall) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∃ d : ℕ, N ≤ d ∧
      ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : NumberField.IsTotallyReal K),
        Module.finrank ℚ K = d ∧ |(NumberField.discr K : ℝ)| ≤ C ^ d := by
  classical
  obtain ⟨F, iF, iNF, hTR, S, hS, hodd, K, iK, iA, iG, hinf, hlev⟩ := h
  letI : Field F := iF
  letI : NumberField F := iNF
  letI : NumberField.IsTotallyReal F := hTR
  letI : Field K := iK
  letI : Algebra F K := iA
  letI : IsGalois F K := iG
  exact exists_totallyReal_discr_le_of_infinite_maximal_proP hS hodd hlev hinf

/-- **THE WALL is witnessed by any infinite maximal pro-`2` extension of a totally real base
field unramified outside `S` and at the infinite places**: the structural hypotheses are exactly
what `Submission.NumberField.exists_maximal_proP_field_unramifiedOutside_inf` produces, so the
whole challenge now rests on the single infinitude statement. -/
theorem martinetTameWall_of_infinite_maximal_proP
    {F : Type} [Field F] [NumberField F] [NumberField.IsTotallyReal F]
    {S : Finset ℕ} (hS : ∀ q ∈ S, Nat.Prime q) (hodd : ∀ q ∈ S, q ≠ 2)
    {K : Type} [Field K] [Algebra F K] [IsGalois F K]
    (hsub : ∀ (L : IntermediateField F K) [NumberField ↥L], FiniteDimensional F L →
      IsGalois F L →
      IsPGroup 2 (L ≃ₐ[F] L) ∧
        (∀ (P : Ideal (𝓞 ↥L)), P.IsPrime → P ≠ ⊥ → P ∣ differentIdeal (𝓞 F) (𝓞 ↥L) →
          ∃ q ∈ S, P.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ))) ∧
        IsUnramifiedAtInfinitePlaces F ↥L)
    (hinf : Infinite (K ≃ₐ[F] K)) : MartinetTameWall :=
  ⟨F, ‹Field F›, ‹NumberField F›, ‹NumberField.IsTotallyReal F›, S, hS, hodd,
    K, ‹Field K›, ‹Algebra F K›, ‹IsGalois F K›, hinf, hsub⟩

/-- The benchmark statement follows from the infinitude of the maximal pro-`2` extension of a
totally real base field unramified outside `S` and at the infinite places. -/
theorem exists_totallyReal_discr_le_of_infinite_maximal_proP'
    {F : Type} [Field F] [NumberField F] [NumberField.IsTotallyReal F]
    {S : Finset ℕ} (hS : ∀ q ∈ S, Nat.Prime q) (hodd : ∀ q ∈ S, q ≠ 2)
    {K : Type} [Field K] [Algebra F K] [IsGalois F K]
    (hsub : ∀ (L : IntermediateField F K) [NumberField ↥L], FiniteDimensional F L →
      IsGalois F L →
      IsPGroup 2 (L ≃ₐ[F] L) ∧
        (∀ (P : Ideal (𝓞 ↥L)), P.IsPrime → P ≠ ⊥ → P ∣ differentIdeal (𝓞 F) (𝓞 ↥L) →
          ∃ q ∈ S, P.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ))) ∧
        IsUnramifiedAtInfinitePlaces F ↥L)
    (hinf : Infinite (K ≃ₐ[F] K)) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∃ d : ℕ, N ≤ d ∧
      ∃ (K' : Type) (_ : Field K') (_ : NumberField K') (_ : NumberField.IsTotallyReal K'),
        Module.finrank ℚ K' = d ∧ |(NumberField.discr K' : ℝ)| ≤ C ^ d :=
  exists_totallyReal_discr_le_of_martinetTameWall
    (martinetTameWall_of_infinite_maximal_proP hS hodd hsub hinf)


end Submission.NumberField
