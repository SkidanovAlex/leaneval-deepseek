import Mathlib
import Submission.NK.HeckeL.Zeta
import Submission.NK.HeckeL.Nonvanishing.artinPrimeSum_isBigO
import Submission.NK.HeckeL.Series.charPrimeSum_eq_sum_add_artinPrimeSum
import Submission.NK.HeckeL.Series.exists_units_factor_ne_one
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.HeckeL.Consequences

open NumberField IsDedekindDomain
open scoped BigOperators Classical Topology
open Filter Asymptotics

/-- The **modulus part** of the character-twisted prime sum is bounded as `s → 1⁺`: it is a
finite sum of terms `χ(Frob_𝔭) · N𝔭^{-s}` whose character factor has absolute value `1` and whose
archimedean factor is at most `1` for `s ≥ 0`. -/
private lemma sum_over_finset_isBigO {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] (S : Finset (NK.HeckeL.PrimeIdeal K))
    (ψ : Gal(L/K) →* ℂˣ) :
    (fun s : ℝ => ∑ 𝔭 ∈ S, (ψ (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭) : ℂ) *
        (((Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ))
      =O[nhdsWithin (1 : ℝ) (Set.Ioi 1)] (fun _ : ℝ => (1 : ℂ)) := by
  haveI : Fintype Gal(L/K) := AlgEquiv.fintype K L
  refine Asymptotics.IsBigO.of_bound (S.card : ℝ) ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs1 : (1 : ℝ) < s := hs
  have hs0 : (0 : ℝ) ≤ s := by linarith
  calc ‖∑ 𝔭 ∈ S, (ψ (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭) : ℂ) *
        (((Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ)‖
      ≤ ∑ 𝔭 ∈ S, ‖(ψ (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭) : ℂ) *
        (((Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ _𝔭 ∈ S, (1 : ℝ) := by
        refine Finset.sum_le_sum (fun 𝔭 _h𝔭 => ?_)
        have hnorm : ‖(ψ (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭) : ℂ)‖ = 1 :=
          NK.Chebotarev.norm_monoidHom_units_apply_eq_one ψ _
        have hpos : (0 : ℝ) ≤ (Ideal.absNorm 𝔭.asIdeal : ℝ) := Nat.cast_nonneg _
        have hne : Ideal.absNorm 𝔭.asIdeal ≠ 0 := fun h =>
          HeightOneSpectrum.ne_bot 𝔭 (Ideal.absNorm_eq_zero_iff.mp h)
        have hone : (1 : ℝ) ≤ (Ideal.absNorm 𝔭.asIdeal : ℝ) := by
          exact_mod_cast Nat.one_le_iff_ne_zero.mpr hne
        have hle : ((Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)) ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos hone (by linarith)
        rw [norm_mul, hnorm, one_mul]
        rw [show ‖(((Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ)‖
            = |(Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)| from by simp]
        rw [abs_of_nonneg (Real.rpow_nonneg hpos _)]
        exact hle
    _ = (S.card : ℝ) := by simp
    _ = (S.card : ℝ) * ‖(1 : ℂ)‖ := by simp

/-- **The Hecke `L`-function input of Čebotarev in the abelian case follows from the Artin
regularity input.**

Let `L/K` be a finite Galois extension of number fields, `S` a finite set of primes of `K`
containing the ramified ones, and assume every non-trivial character `ψ : Gal(L/K) → ℂˣ` has
`L`-series regular at `s = 1`.  Then for every non-trivial character `χ : Gal(L/K) → ℂ` the
character-twisted prime sum `∑_𝔭 χ(Frob_𝔭) N𝔭^{-s}` is bounded as `s → 1⁺`.

Indeed `χ` takes values in the roots of unity, so it is the composite of a `ℂˣ`-valued character
`ψ` with the inclusion `ℂˣ ↪ ℂ`; the prime sum over the primes outside `S` is bounded by
`NK.HeckeL.Nonvanishing.artinPrimeSum_isBigO`, and the finite sum over `S` is bounded
termwise. -/
theorem abelianLFunctions {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (S : Finset (NK.HeckeL.PrimeIdeal K))
    (hcomm : ∀ a b : Gal(L/K), a * b = b * a)
    (hS : ∀ 𝔭 : NK.HeckeL.PrimeIdeal K, ¬ NK.HeckeL.IsUnramifiedIn (K := K) (L := L) 𝔭 → 𝔭 ∈ S)
    (h : ∀ ψ : Gal(L/K) →* ℂˣ, ψ ≠ 1 → NK.HeckeL.ArtinLRegularAtOne K L S ψ) :
    NK.Chebotarev.AbelianLFunctions K L := by
  intro χ hχ
  -- every character of a finite group into `ℂ` is a `ℂˣ`-valued character composed with `ℂˣ ↪ ℂ`
  obtain ⟨ψ, hψne, hψeq⟩ := NK.HeckeL.Series.exists_units_factor_ne_one hχ
  have hgal : NK.HeckeL.galoisToComplex ψ = χ := hψeq
  -- the prime sum outside `S` is bounded, and so is the finite sum over `S`
  have hout : (fun s : ℝ => NK.HeckeL.artinPrimeSum K L S ψ s)
      =O[nhdsWithin (1 : ℝ) (Set.Ioi 1)] (fun _ : ℝ => (1 : ℂ)) :=
    NK.HeckeL.Nonvanishing.artinPrimeSum_isBigO S hcomm hS h ψ hψne
  have hfin := sum_over_finset_isBigO (K := K) (L := L) S ψ
  have hsum : (fun s : ℝ => (∑ 𝔭 ∈ S, (ψ (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭) : ℂ) *
        (((Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ)) +
        NK.HeckeL.artinPrimeSum K L S ψ s)
      =O[nhdsWithin (1 : ℝ) (Set.Ioi 1)] (fun _ : ℝ => (1 : ℂ)) := hfin.add hout
  -- the full prime sum agrees with the sum of the two pieces for `s > 1`
  refine hsum.congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [← hgal]
  exact (NK.HeckeL.Series.charPrimeSum_eq_sum_add_artinPrimeSum (K := K) (L := L) S ψ hs).symm

end NK.HeckeL.Consequences
