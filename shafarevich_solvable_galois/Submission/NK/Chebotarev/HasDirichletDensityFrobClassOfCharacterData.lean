/-
Work of the Neukirch–Uchida team: the Čebotarev density theorem.
-/
import Mathlib
import Submission.NK.Chebotarev.LFunctions
import Submission.NK.Chebotarev.Density
import Submission.NK.Chebotarev.SumChiMulStarChiEq
import Submission.NK.Chebotarev.NatCardConjClassMulNatCardCentralizer
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Čebotarev density for a Frobenius conjugacy class, from character data

This file proves `NK.Chebotarev.HasDirichletDensityFrobClassOfCharacterData`: given a family
`χ i : Gal(L/K) → ℂ` of class functions which is "orthogonal" in the sense that

* `∑ i, χ i g * star (χ i h) = 0` unless `g` and `h` are conjugate, and
* `∑ i, χ i g * star (χ i g) = |C(g)|`,

one index `i₀` carrying the trivial character `χ i₀ ≡ 1`, and the analytic input that every
non-trivial character-twisted prime sum `∑_𝔭 star (χ i (Frob_𝔭)) N𝔭^{-s}` stays bounded as
`s → 1⁺`, the set of primes whose Frobenius is conjugate to a prescribed `g₀` has Dirichlet
density `|Cl(g₀)| / |G|`.

The point of the orthogonality assumptions is the group-theoretic identity

`|C(g₀)| * [g ~ g₀] = ∑ i, χ i g₀ * star (χ i g)`  (`SumChiMulStarChiEq`),

which lets the *indicator* of the conjugacy class be written as a linear combination of the
characters.  Summing the resulting identity over the finite places of `K` against the weight
`N𝔭^{-s}` and exchanging the (finite) character sum with the prime sum splits the
character-twisted prime sum into the trivial-character contribution — which is the full
prime-ideal zeta sum `ζ_K`, of size `log (1/(s-1)) + O(1)` — and a bounded remainder.  Dividing
by `|C(g₀)|` yields the density statement; the orbit–stabiliser identity
(`NatCardConjClassMulNatCardCentralizer`) converts `1/|C(g₀)|` into `|Cl(g₀)|/|G|`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace NK.Chebotarev

open Filter IsDedekindDomain Asymptotics
open scoped BigOperators Classical

/-- The character-twisted prime sum `∑_𝔭 star (ψ (Frob_𝔭)) N𝔭^{-s}`: the Euler product
expansion of the Hecke `L`-function of the (conjugate of the) character `ψ`, summed over the
finite places of `K` using the chosen Frobenius elements `NK.Chebotarev.frobAtPrime`. -/
noncomputable def charStarPrimeSum {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (ψ : Gal(L/K) → ℂ) (s : ℝ) : ℂ :=
  ∑' p : PrimeIdeal K, star (ψ (frobAtPrime (K := K) (L := L) p)) *
    (((Ideal.absNorm p.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ)

/-- **The orthogonality identity, summed over the finite places.**

For `1 < s` (so that every twisted prime sum converges absolutely), the sum over the primes of
`K` of `(∑ i, χ i g₀ * star (χ i (Frob_𝔭))) N𝔭^{-s}` equals `|C(g₀)|` times the prime-ideal
zeta sum of the set of primes whose Frobenius is conjugate to `g₀`, and also equals the
`χ`-expansion `∑ i, χ i g₀ * (∑_𝔭 star (χ i (Frob_𝔭)) N𝔭^{-s})`.

The first equality is the pointwise identity `SumChiMulStarChiEq` (the sum vanishes off the
conjugacy class of `g₀` and equals `|C(g₀)|` on it), transported from the subtype of `K`-primes
in the class to all primes; the second is `Summable.tsum_finsetSum`, exchanging the finite
character sum with the prime sum, which is legitimate because each twisted sum is dominated by
`(∑_g ‖χ i g‖) * ∑_𝔭 N𝔭^{-s}`. -/
private lemma charStarPrimeSum_identity {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    {ι : Type*} [Fintype ι] (χ : ι → Gal(L/K) → ℂ) (i₀ : ι) (g₀ : Gal(L/K))
    (hχ_class : ∀ (i : ι) (g h : Gal(L/K)), χ i (h⁻¹ * g * h) = χ i g)
    (horth_off : ∀ g h : Gal(L/K), ¬ IsConj g h → ∑ i, χ i g * star (χ i h) = 0)
    (hnorm : ∀ g : Gal(L/K),
      ∑ i, χ i g * star (χ i g) =
        (Nat.card (Subgroup.centralizer ({g} : Set (Gal(L/K)))) : ℂ))
    {s : ℝ} (hs : 1 < s) :
    (Nat.card (Subgroup.centralizer ({g₀} : Set (Gal(L/K)))) : ℂ) *
      ((NumberField.Set.primeIdealZetaSum
        {p : PrimeIdeal K | IsConj (frobAtPrime (K := K) (L := L) p) g₀} s : ℝ) : ℂ)
      = ∑ i, χ i g₀ * charStarPrimeSum (χ i) s := by
  classical
  -- summability of the twisted prime sums
  have hsum_i' : ∀ i : ι, Summable (fun p : PrimeIdeal K =>
      (χ i g₀ * star (χ i (frobAtPrime (K := K) (L := L) p))) *
        (((Ideal.absNorm p.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ)) := by
    intro i
    have hsum : Summable (fun p : PrimeIdeal K => (Ideal.absNorm p.asIdeal : ℝ) ^ (-s)) :=
      Commons.NumberTheory.NumberField.Set.summable_primeIdealZetaSum (K := K) hs
    have h2 : Summable (fun p : PrimeIdeal K =>
        star (χ i (frobAtPrime (K := K) (L := L) p)) *
        (((Ideal.absNorm p.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ)) := by
      refine Summable.of_norm_bounded (g := fun p : PrimeIdeal K =>
          (∑ g : Gal(L/K), ‖χ i g‖) * (Ideal.absNorm p.asIdeal : ℝ) ^ (-s)) ?_ ?_
      · exact hsum.mul_left _
      · intro p
        rw [norm_mul, norm_star]
        have hw : ‖((((Ideal.absNorm p.asIdeal : ℝ) ^ (-s) : ℝ)) : ℂ)‖ =
            (Ideal.absNorm p.asIdeal : ℝ) ^ (-s) := by
          rw [Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
        rw [hw]
        exact mul_le_mul_of_nonneg_right
          (Finset.single_le_sum (fun g _ => norm_nonneg _) (Finset.mem_univ _))
          (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    simpa only [mul_assoc] using h2.mul_left (χ i g₀)
  -- the pointwise identity, at every finite place
  have hpoint : ∀ p : PrimeIdeal K,
      (∑ i, χ i g₀ * star (χ i (frobAtPrime (K := K) (L := L) p))) *
          (((Ideal.absNorm p.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ)
        = (Nat.card (Subgroup.centralizer ({g₀} : Set (Gal(L/K)))) : ℂ) *
            (if IsConj (frobAtPrime (K := K) (L := L) p) g₀ then
              (((Ideal.absNorm p.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ) else 0) := by
    intro p
    by_cases hp : IsConj (frobAtPrime (K := K) (L := L) p) g₀
    · rw [if_pos hp]
      rw [show (∑ i, χ i g₀ * star (χ i (frobAtPrime (K := K) (L := L) p))) =
          (Nat.card (Subgroup.centralizer ({g₀} : Set (Gal(L/K)))) : ℂ) from
        (SumChiMulStarChiEq χ i₀ g₀ hχ_class horth_off hnorm _).mpr hp]
    · rw [if_neg hp, horth_off g₀ _ (fun h => hp (IsConj.symm h)), zero_mul, mul_zero]
  -- reindex the prime-ideal zeta sum over the conjugacy class of `g₀`
  have hF : ((NumberField.Set.primeIdealZetaSum
        {p : PrimeIdeal K | IsConj (frobAtPrime (K := K) (L := L) p) g₀} s : ℝ) : ℂ)
      = ∑' p : {p : PrimeIdeal K | IsConj (frobAtPrime (K := K) (L := L) p) g₀},
          (((Ideal.absNorm p.1.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ) := by
    rw [NumberField.Set.primeIdealZetaSum_def, Complex.ofReal_tsum]
  have hsub : (∑' p : {p : PrimeIdeal K | IsConj (frobAtPrime (K := K) (L := L) p) g₀},
        (((Ideal.absNorm p.1.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ))
      = ∑' p : PrimeIdeal K, (if IsConj (frobAtPrime (K := K) (L := L) p) g₀ then
          (((Ideal.absNorm p.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ) else 0) := by
    refine (tsum_subtype {p : PrimeIdeal K | IsConj (frobAtPrime (K := K) (L := L) p) g₀}
      (fun q : PrimeIdeal K => (((Ideal.absNorm q.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ))).trans ?_
    refine tsum_congr (fun p => ?_)
    by_cases hp : IsConj (frobAtPrime (K := K) (L := L) p) g₀
    · simp [Set.indicator_apply, hp]
    · simp [Set.indicator_apply, hp]
  rw [hF, hsub, ← tsum_mul_left]
  calc ∑' p : PrimeIdeal K, (Nat.card (Subgroup.centralizer ({g₀} : Set (Gal(L/K)))) : ℂ) *
        (if IsConj (frobAtPrime (K := K) (L := L) p) g₀ then
          (((Ideal.absNorm p.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ) else 0)
      = ∑' p : PrimeIdeal K, (∑ i, χ i g₀ * star (χ i (frobAtPrime (K := K) (L := L) p))) *
          (((Ideal.absNorm p.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ) :=
        (tsum_congr (fun p => hpoint p)).symm
    _ = ∑' p : PrimeIdeal K, ∑ i, (χ i g₀ * star (χ i (frobAtPrime (K := K) (L := L) p))) *
          (((Ideal.absNorm p.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ) :=
        tsum_congr (fun p => Finset.sum_mul _ _ _)
    _ = ∑ i, ∑' p : PrimeIdeal K, (χ i g₀ * star (χ i (frobAtPrime (K := K) (L := L) p))) *
          (((Ideal.absNorm p.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ) :=
        Summable.tsum_finsetSum (s := Finset.univ) (fun i _ => hsum_i' i)
    _ = ∑ i, χ i g₀ * charStarPrimeSum (χ i) s := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [charStarPrimeSum, ← tsum_mul_left]
        refine tsum_congr (fun p => by ring)

theorem HasDirichletDensityFrobClassOfCharacterData {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    {ι : Type*} [Fintype ι] (χ : ι → Gal(L/K) → ℂ) (i₀ : ι)
    (hχ_class : ∀ (i : ι) (g h : Gal(L/K)), χ i (h⁻¹ * g * h) = χ i g)
    (hχ_triv : ∀ g : Gal(L/K), χ i₀ g = 1)
    (horth_off : ∀ g h : Gal(L/K), ¬ IsConj g h → ∑ i, χ i g * star (χ i h) = 0)
    (hnorm : ∀ g : Gal(L/K),
      ∑ i, χ i g * star (χ i g) =
        (Nat.card (Subgroup.centralizer ({g} : Set (Gal(L/K)))) : ℂ))
    (han : ∀ i : ι, i ≠ i₀ → (fun s : ℝ =>
      ∑' p : NK.Chebotarev.PrimeIdeal K,
        star (χ i (NK.Chebotarev.frobAtPrime (K := K) (L := L) p)) *
          (((Ideal.absNorm p.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ))
      =O[nhdsWithin (1 : ℝ) (Set.Ioi 1)] (fun _ : ℝ => (1 : ℂ)))
    (g₀ : Gal(L/K)) :
    NumberField.Set.HasDirichletDensity
      {p : NK.Chebotarev.PrimeIdeal K |
        IsConj (NK.Chebotarev.frobAtPrime (K := K) (L := L) p) g₀}
      ((Nat.card {x : Gal(L/K) // IsConj x g₀} : ℝ) / (Nat.card (Gal(L/K)) : ℝ)) := by
  classical
  haveI : Finite (Gal(L/K)) := inferInstance
  -- the analytic input, in terms of `charStarPrimeSum`
  have han' : ∀ i : ι, i ≠ i₀ → (fun s : ℝ => charStarPrimeSum (χ i) s)
      =O[nhdsWithin (1 : ℝ) (Set.Ioi 1)] (fun _ : ℝ => (1 : ℂ)) := by
    intro i hi
    simpa only [charStarPrimeSum] using han i hi
  -- the orthogonality identity, summed over the finite places
  have hid : ∀ s : ℝ, 1 < s →
      (Nat.card (Subgroup.centralizer ({g₀} : Set (Gal(L/K)))) : ℂ) *
        ((NumberField.Set.primeIdealZetaSum
          {p : PrimeIdeal K | IsConj (frobAtPrime (K := K) (L := L) p) g₀} s : ℝ) : ℂ)
        = ∑ i, χ i g₀ * charStarPrimeSum (χ i) s :=
    fun s hs => charStarPrimeSum_identity χ i₀ g₀ hχ_class horth_off hnorm hs
  -- the trivial character contributes the full prime-ideal zeta sum
  have hB_i₀ : ∀ s : ℝ, charStarPrimeSum (χ i₀) s =
      ((NumberField.Set.primeIdealZetaSum (Set.univ : Set (PrimeIdeal K)) s : ℝ) : ℂ) := by
    intro s
    rw [charStarPrimeSum]
    trans ∑' p : PrimeIdeal K, (((Ideal.absNorm p.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ)
    · exact tsum_congr (fun p => by rw [hχ_triv, star_one, one_mul])
    · rw [← Complex.ofReal_tsum]
      congr 1
      rw [NumberField.Set.primeIdealZetaSum_def,
        tsum_univ (f := fun 𝔭 : PrimeIdeal K => (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s))]
  -- taking real parts: `|C(g₀)| * ζ_S = ζ_K + (bounded)`
  have hreal : ∀ s : ℝ, 1 < s →
      (Nat.card (Subgroup.centralizer ({g₀} : Set (Gal(L/K)))) : ℝ) *
        NumberField.Set.primeIdealZetaSum
          {p : PrimeIdeal K | IsConj (frobAtPrime (K := K) (L := L) p) g₀} s
      = NumberField.Set.primeIdealZetaSum (Set.univ : Set (PrimeIdeal K)) s
        + ∑ i ∈ ({i₀}ᶜ : Finset ι), (χ i g₀ * charStarPrimeSum (χ i) s).re := by
    intro s hs
    have h := congrArg Complex.re (hid s hs)
    rw [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, Complex.re_sum] at h
    rw [Fintype.sum_eq_add_sum_compl i₀
      (fun i => (χ i g₀ * charStarPrimeSum (χ i) s).re)] at h
    have h1 : (χ i₀ g₀ * charStarPrimeSum (χ i₀) s).re =
        NumberField.Set.primeIdealZetaSum (Set.univ : Set (PrimeIdeal K)) s := by
      rw [hχ_triv, one_mul, hB_i₀ s, Complex.ofReal_re]
    rw [h1] at h
    exact h
  -- the non-trivial characters contribute `O(1)`
  have hO' : (∑ i ∈ ({i₀}ᶜ : Finset ι), fun s : ℝ => (χ i g₀ * charStarPrimeSum (χ i) s).re)
      =O[nhdsWithin (1 : ℝ) (Set.Ioi 1)] (fun _ : ℝ => (1 : ℝ)) := by
    refine IsBigO.sum (fun i hi => ?_)
    have hne : i ≠ i₀ := by simpa using hi
    have h2 : (fun s : ℝ => χ i g₀ * charStarPrimeSum (χ i) s)
        =O[nhdsWithin (1 : ℝ) (Set.Ioi 1)] (fun _ : ℝ => (1 : ℂ)) :=
      (han' i hne).const_mul_left (χ i g₀)
    obtain ⟨C, hC⟩ := h2.bound
    refine IsBigO.of_bound C ?_
    filter_upwards [hC] with s hs
    simp only [norm_one, mul_one] at hs ⊢
    exact (Complex.abs_re_le_norm _).trans hs
  have hO : (fun s : ℝ => ∑ i ∈ ({i₀}ᶜ : Finset ι), (χ i g₀ * charStarPrimeSum (χ i) s).re)
      =O[nhdsWithin (1 : ℝ) (Set.Ioi 1)] (fun _ : ℝ => (1 : ℝ)) :=
    hO'.congr' (Filter.EventuallyEq.of_eq
      (funext fun s => by simp only [Finset.sum_apply])) Filter.EventuallyEq.rfl
  have hmain : (fun s : ℝ => (Nat.card (Subgroup.centralizer ({g₀} : Set (Gal(L/K)))) : ℝ) *
        NumberField.Set.primeIdealZetaSum
          {p : PrimeIdeal K | IsConj (frobAtPrime (K := K) (L := L) p) g₀} s
      - NumberField.Set.primeIdealZetaSum (Set.univ : Set (PrimeIdeal K)) s)
      =O[nhdsWithin (1 : ℝ) (Set.Ioi 1)] (fun _ : ℝ => (1 : ℝ)) := by
    refine hO.congr' ?_ Filter.EventuallyEq.rfl
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs1 : 1 < s := hs
    rw [hreal s hs1]
    ring
  -- the Dedekind zeta function contributes the logarithmic pole
  have hz := Commons.NumberTheory.NumberField.Set.isBigO_primeIdealZetaSum_sub_log K
  have hcomb : (fun s : ℝ => (Nat.card (Subgroup.centralizer ({g₀} : Set (Gal(L/K)))) : ℝ) *
        NumberField.Set.primeIdealZetaSum
          {p : PrimeIdeal K | IsConj (frobAtPrime (K := K) (L := L) p) g₀} s
      - Real.log (1 / (s - 1)))
      =O[nhdsWithin (1 : ℝ) (Set.Ioi 1)] (fun _ : ℝ => (1 : ℝ)) :=
    (hmain.add hz).congr' (Filter.EventuallyEq.of_eq (funext fun s => by ring))
      Filter.EventuallyEq.rfl
  -- divide by `|C(g₀)|`
  have hcpos : (0 : ℝ) < (Nat.card (Subgroup.centralizer ({g₀} : Set (Gal(L/K))))) := by
    haveI : Nonempty (Subgroup.centralizer ({g₀} : Set (Gal(L/K)))) := ⟨1⟩
    exact_mod_cast Nat.card_pos
  have hdiv : (fun s : ℝ => NumberField.Set.primeIdealZetaSum
        {p : PrimeIdeal K | IsConj (frobAtPrime (K := K) (L := L) p) g₀} s
      - ((Nat.card (Subgroup.centralizer ({g₀} : Set (Gal(L/K))))) : ℝ)⁻¹ *
          Real.log (1 / (s - 1)))
      =O[nhdsWithin (1 : ℝ) (Set.Ioi 1)] (fun _ : ℝ => (1 : ℝ)) := by
    have hc : ((Nat.card (Subgroup.centralizer ({g₀} : Set (Gal(L/K))))) : ℝ) ≠ 0 :=
      ne_of_gt hcpos
    refine (hcomb.const_mul_left
      (((Nat.card (Subgroup.centralizer ({g₀} : Set (Gal(L/K))))) : ℝ)⁻¹)).congr' ?_
      Filter.EventuallyEq.rfl
    filter_upwards with s
    rw [mul_sub, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  -- orbit–stabiliser: `|Cl(g₀)| / |G| = 1 / |C(g₀)|`
  have hδ : ((Nat.card {x : Gal(L/K) // IsConj x g₀} : ℝ) / (Nat.card (Gal(L/K)) : ℝ))
      = ((Nat.card (Subgroup.centralizer ({g₀} : Set (Gal(L/K))))) : ℝ)⁻¹ := by
    have hG' : (Nat.card (Gal(L/K)) : ℝ) =
        (Nat.card {x : Gal(L/K) // IsConj x g₀} : ℝ) *
          (Nat.card (Subgroup.centralizer ({g₀} : Set (Gal(L/K))))) := by
      rw [← NatCardConjClassMulNatCardCentralizer g₀]
      push_cast
      ring
    have hCl : (Nat.card {x : Gal(L/K) // IsConj x g₀} : ℝ) ≠ 0 := by
      intro h
      have hG0 : (Nat.card (Gal(L/K)) : ℝ) = 0 := by rw [hG', h, zero_mul]
      have hpos : (0 : ℝ) < (Nat.card (Gal(L/K))) := by
        haveI : Nonempty (Gal(L/K)) := ⟨1⟩
        exact_mod_cast Nat.card_pos
      linarith
    rw [hG']
    field_simp
  rw [hδ]
  exact Commons.NumberTheory.NumberField.Set.hasDirichletDensity_of_isBigO_primeIdealZetaSum_sub_log
    hdiv

end NK.Chebotarev
