import Mathlib
import Submission.Commons.NumberTheory.NumberField.Set.hasDirichletDensity_compl
import Submission.Commons.Analysis.SpecialFunctions.Log.log_eq_tsum_log_of_hasProd
import Submission.Commons.Analysis.ExpLog.log_inv_one_sub_le_two
import Submission.Commons.NumberTheory.NumberField.ideal_card_norm_le_tupleFinset
import Submission.Commons.NumberTheory.NumberField.tsum_prime_pow_card_mul_pow
import Submission.Commons.NumberTheory.NumberField.card_ideals_absNorm_mul
import Submission.Commons.NumberTheory.NumberField.natCard_quotient_eq_pow_inertiaDeg
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.NumberTheory.NumberField.DedekindZeta

open Filter IsDedekindDomain Topology Asymptotics
open scoped Real BigOperators

/-- The `n`-th coefficient of the Dirichlet series of the Dedekind zeta function, evaluated at a
real `s`: the number of integral ideals of `𝓞 K` of norm `n`, times `n^{-s}`. -/
noncomputable def zetaTerm (K : Type*) [Field K] [NumberField K] (s : ℝ) (n : ℕ) : ℝ :=
  (Nat.card {I : Ideal (NumberField.RingOfIntegers K) // Ideal.absNorm I = n} : ℝ)
    * (n:ℝ) ^ (-s)

/-- The local Euler factor `(1 - N𝔭^{-s})^{-1}` of a prime `𝔭` (or, for a non-prime, of an
arbitrary ideal). -/
noncomputable def localFactor (K : Type*) [Field K] [NumberField K] (s : ℝ)
    (P : Ideal (NumberField.RingOfIntegers K)) : ℝ :=
  (1 - (Ideal.absNorm P : ℝ) ^ (-s))⁻¹

section Aux

variable {K : Type*} [Field K] [NumberField K]

/-- The absolute norm of the principal ideal `(p)` in `ℤ` is `p`. -/
lemma absNorm_span_int (p : ℕ) :
    Ideal.absNorm (Ideal.span ({(p:ℤ)} : Set ℤ)) = p := by
  rw [Ideal.absNorm_span_singleton]
  simp

/-- The rational prime below a nonzero prime ideal of `𝓞 K`. -/
noncomputable def underlyingPrime (𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K)) : Nat.Primes :=
  ⟨Ideal.absNorm (Ideal.under ℤ 𝔭.asIdeal),
    Commons.NumberTheory.NumberField.primeIndex_underlying_prime 𝔭.asIdeal 𝔭.isPrime 𝔭.ne_bot⟩

lemma underlyingPrime_eq_iff (p : ℕ) (hp : Nat.Prime p)
    (𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    (underlyingPrime 𝔭 : ℕ) = p ↔
      𝔭.asIdeal ∈ IsDedekindDomain.primesOverFinset (Ideal.span ({(p:ℤ)} : Set ℤ))
        (NumberField.RingOfIntegers K) := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hpne : (Ideal.span ({(p : ℤ)} : Set ℤ)) ≠ ⊥ := (Ideal.span_singleton_eq_bot).not.mpr hp0
  haveI hmax : (Ideal.span ({(p : ℤ)} : Set ℤ)).IsMaximal :=
    ((Ideal.span_singleton_prime hp0).mpr (Nat.prime_iff_prime_int.mp hp)).isMaximal hpne
  rw [IsDedekindDomain.mem_primesOverFinset_iff (B := NumberField.RingOfIntegers K) hpne]
  simp only [Ideal.primesOver, Set.mem_ofPred_eq, Ideal.liesOver_iff]
  constructor
  · intro h
    refine ⟨𝔭.isPrime, ?_⟩
    rw [← h]
    exact (Ideal.liesOver_iff _ _).mp
      (Commons.NumberTheory.NumberField.primeIndex_underlying_liesOver 𝔭.asIdeal 𝔭.isPrime 𝔭.ne_bot)
  · rintro ⟨-, h⟩
    show Ideal.absNorm (Ideal.under ℤ 𝔭.asIdeal) = p
    rw [← h, absNorm_span_int]

lemma isPrime_of_mem_primesOverF {p : ℕ} (hp : Nat.Prime p)
    {P : Ideal (NumberField.RingOfIntegers K)}
    (hP : P ∈ IsDedekindDomain.primesOverFinset (Ideal.span ({(p:ℤ)} : Set ℤ))
        (NumberField.RingOfIntegers K)) : P.IsPrime := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hpne : (Ideal.span ({(p : ℤ)} : Set ℤ)) ≠ ⊥ := (Ideal.span_singleton_eq_bot).not.mpr hp0
  haveI hmax : (Ideal.span ({(p : ℤ)} : Set ℤ)).IsMaximal :=
    ((Ideal.span_singleton_prime hp0).mpr (Nat.prime_iff_prime_int.mp hp)).isMaximal hpne
  rw [IsDedekindDomain.mem_primesOverFinset_iff (B := NumberField.RingOfIntegers K) hpne,
    Ideal.primesOver, Set.mem_ofPred_eq] at hP
  exact hP.1

lemma ne_bot_of_mem_primesOverF {p : ℕ} (hp : Nat.Prime p)
    {P : Ideal (NumberField.RingOfIntegers K)}
    (hP : P ∈ IsDedekindDomain.primesOverFinset (Ideal.span ({(p:ℤ)} : Set ℤ))
        (NumberField.RingOfIntegers K)) : P ≠ ⊥ := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hpne : (Ideal.span ({(p : ℤ)} : Set ℤ)) ≠ ⊥ := (Ideal.span_singleton_eq_bot).not.mpr hp0
  haveI hmax : (Ideal.span ({(p : ℤ)} : Set ℤ)).IsMaximal :=
    ((Ideal.span_singleton_prime hp0).mpr (Nat.prime_iff_prime_int.mp hp)).isMaximal hpne
  have hlies : P.LiesOver (Ideal.span ({(p:ℤ)} : Set ℤ)) := by
    rw [IsDedekindDomain.mem_primesOverFinset_iff (B := NumberField.RingOfIntegers K) hpne,
      Ideal.primesOver, Set.mem_ofPred_eq] at hP
    exact hP.2
  intro hbot
  rw [Ideal.liesOver_iff, hbot, Ideal.under_bot] at hlies
  exact hpne hlies

/-- For a prime `P` above `p`, the absolute norm of `P` is `p` to the inertia degree. -/
lemma absNorm_eq_pow_inertiaDeg_of_mem_primesOverF {p : ℕ} (hp : Nat.Prime p)
    {P : Ideal (NumberField.RingOfIntegers K)}
    (hP : P ∈ IsDedekindDomain.primesOverFinset (Ideal.span ({(p:ℤ)} : Set ℤ))
        (NumberField.RingOfIntegers K)) :
    Ideal.absNorm P = p ^ P.inertiaDeg ℤ := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact Commons.NumberTheory.NumberField.natCard_quotient_eq_pow_inertiaDeg p P hP

/-- The primes of `𝓞 K` lying above the rational prime `p`, exhibited as the elements of the
finset `primesOverF p`. -/
noncomputable def fiberEquiv (p : Nat.Primes) :
    {𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K) // underlyingPrime 𝔭 = p} ≃
      {P : Ideal (NumberField.RingOfIntegers K) //
        P ∈ IsDedekindDomain.primesOverFinset (Ideal.span ({((p:ℕ):ℤ)} : Set ℤ))
          (NumberField.RingOfIntegers K)} where
  toFun 𝔭 := ⟨𝔭.1.asIdeal,
    (underlyingPrime_eq_iff (p:ℕ) p.2 𝔭.1).mp (congrArg Subtype.val 𝔭.2)⟩
  invFun P := ⟨⟨P.1, isPrime_of_mem_primesOverF p.2 P.2, ne_bot_of_mem_primesOverF p.2 P.2⟩,
    Subtype.ext ((underlyingPrime_eq_iff (p:ℕ) p.2 _).mpr P.2)⟩
  left_inv 𝔭 := by ext <;> rfl
  right_inv P := by ext <;> rfl

/-- A finite product over the primes above `p` can be written as an infinite product over the
corresponding nonzero prime ideals. -/
lemma prod_primesOverF_eq_prod_fiber (p : Nat.Primes)
    (g : Ideal (NumberField.RingOfIntegers K) → ℝ) :
    (∏ P ∈ IsDedekindDomain.primesOverFinset (Ideal.span ({((p:ℕ):ℤ)} : Set ℤ))
        (NumberField.RingOfIntegers K), g P)
      = ∏' 𝔭 : {𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K) //
          underlyingPrime 𝔭 = p}, g 𝔭.1.asIdeal := by
  classical
  haveI hfin : Fintype {𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K) //
      underlyingPrime 𝔭 = p} :=
    Fintype.ofEquiv _ (fiberEquiv (K := K) p).symm
  rw [tprod_fintype]
  exact (Finset.prod_finset_coe (s := IsDedekindDomain.primesOverFinset
      (Ideal.span ({((p:ℕ):ℤ)} : Set ℤ)) (NumberField.RingOfIntegers K)) g).symm.trans
    (Equiv.prod_comp (fiberEquiv (K := K) p)
      (fun P : {P : Ideal (NumberField.RingOfIntegers K) //
          P ∈ IsDedekindDomain.primesOverFinset (Ideal.span ({((p:ℕ):ℤ)} : Set ℤ))
            (NumberField.RingOfIntegers K)} => g P.1)).symm

end Aux

section Analysis

variable {K : Type*} [Field K] [NumberField K]

lemma absNorm_primeIdeal_ne_zero (𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    Ideal.absNorm 𝔭.asIdeal ≠ 0 :=
  fun h => 𝔭.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)

lemma absNorm_primeIdeal_pos (𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    0 < (Ideal.absNorm 𝔭.asIdeal : ℝ) :=
  Nat.cast_pos.mpr (Nat.pos_of_ne_zero (absNorm_primeIdeal_ne_zero 𝔭))

lemma two_le_absNorm_primeIdeal (𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    2 ≤ (Ideal.absNorm 𝔭.asIdeal : ℝ) := by
  have h1 : 1 < Ideal.absNorm 𝔭.asIdeal := by
    rw [lt_iff_le_and_ne]
    exact ⟨Nat.one_le_iff_ne_zero.mpr (absNorm_primeIdeal_ne_zero 𝔭),
      fun h => 𝔭.isPrime.ne_top (Ideal.absNorm_eq_one_iff.mp h.symm)⟩
  exact_mod_cast (by omega : 2 ≤ Ideal.absNorm 𝔭.asIdeal)

lemma rpow_neg_absNorm_primeIdeal_pos (s : ℝ)
    (𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    0 < (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) :=
  Real.rpow_pos_of_pos (absNorm_primeIdeal_pos 𝔭) _

lemma rpow_neg_absNorm_primeIdeal_lt_one {s : ℝ} (hs : 0 < s)
    (𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) < 1 :=
  (Real.rpow_lt_one_iff_of_pos (absNorm_primeIdeal_pos 𝔭)).mpr
    (Or.inl ⟨by linarith [two_le_absNorm_primeIdeal 𝔭], by linarith⟩)

/-- The partial sums of the ideal-counting function are bounded by the count of ideals of norm
at most `N`. -/
lemma partial_sum_idealCount_le (N : ℕ) :
    ∑ k ∈ Finset.Icc 1 N, Nat.card {I : Ideal (NumberField.RingOfIntegers K) // Ideal.absNorm I = k}
      ≤ Nat.card {I : Ideal (NumberField.RingOfIntegers K) // Ideal.absNorm I ≤ N} := by
  classical
  have hfin : ∀ k : {k : ℕ // k ∈ Finset.Icc 1 N},
      Finite {I : Ideal (NumberField.RingOfIntegers K) // Ideal.absNorm I = k.1} := fun k =>
    (Ideal.finite_setOfPred_absNorm_eq k.1).to_subtype
  haveI := hfin
  haveI : Finite {I : Ideal (NumberField.RingOfIntegers K) // Ideal.absNorm I ≤ N} :=
    (Ideal.finite_setOfPred_absNorm_le N).to_subtype
  have heq : Nat.card (Sigma (fun k : {k : ℕ // k ∈ Finset.Icc 1 N} =>
        {I : Ideal (NumberField.RingOfIntegers K) // Ideal.absNorm I = k.1}))
      = ∑ k ∈ Finset.Icc 1 N, Nat.card {I : Ideal (NumberField.RingOfIntegers K) // Ideal.absNorm I = k} := by
    rw [Nat.card_sigma]
    exact Finset.sum_coe_sort (Finset.Icc 1 N) (fun k => Nat.card
      {I : Ideal (NumberField.RingOfIntegers K) // Ideal.absNorm I = k})
  rw [← heq]
  refine Nat.card_le_card_of_injective (fun x : Sigma (fun k : {k : ℕ // k ∈ Finset.Icc 1 N} =>
        {I : Ideal (NumberField.RingOfIntegers K) // Ideal.absNorm I = k.1}) =>
      (⟨x.2.1, by rw [x.2.2]; exact (Finset.mem_Icc.mp x.1.2).2⟩ :
        {I : Ideal (NumberField.RingOfIntegers K) // Ideal.absNorm I ≤ N})) ?_
  intro a b h
  simp only [Subtype.mk.injEq] at h
  have hk : (a.1 : ℕ) = b.1 := by rw [← a.2.2, ← b.2.2, h]
  exact Sigma.ext (Subtype.ext hk) ((Subtype.heq_iff_coe_eq (fun x => by rw [hk])).mpr h)

/-- The ideal-counting partial sums are `O(N)`. -/
lemma logEuler_idealCount_bigO :
    (fun N : ℕ => ∑ k ∈ Finset.Icc 1 N,
        (Nat.card {I : Ideal (NumberField.RingOfIntegers K) // Ideal.absNorm I = k} : ℝ))
      =O[atTop] (fun N : ℕ => (N : ℝ) ^ (1 : ℝ)) := by
  obtain ⟨C, hC⟩ := (Commons.NumberTheory.NumberField.Set.absNorm_card_le_bigO K).bound
  refine IsBigO.of_bound C ?_
  filter_upwards [hC] with N hN
  rw [Real.norm_of_nonneg (Finset.sum_nonneg fun k _ => Nat.cast_nonneg _)]
  have hle : (∑ k ∈ Finset.Icc 1 N,
      (Nat.card {I : Ideal (NumberField.RingOfIntegers K) // Ideal.absNorm I = k} : ℝ))
      ≤ (Nat.card {I : Ideal (NumberField.RingOfIntegers K) // Ideal.absNorm I ≤ N} : ℝ) := by
    exact_mod_cast partial_sum_idealCount_le (K := K) N
  calc (∑ k ∈ Finset.Icc 1 N,
        (Nat.card {I : Ideal (NumberField.RingOfIntegers K) // Ideal.absNorm I = k} : ℝ))
      ≤ (Nat.card {I : Ideal (NumberField.RingOfIntegers K) // Ideal.absNorm I ≤ N} : ℝ) := hle
    _ ≤ C * (N:ℝ) := by
        simpa only [Real.norm_of_nonneg (Nat.cast_nonneg (Nat.card {I : Ideal (NumberField.RingOfIntegers K) // Ideal.absNorm I ≤ N})), Real.norm_of_nonneg (Nat.cast_nonneg N)] using hN
    _ = C * ‖(N:ℝ)^(1:ℝ)‖ := by rw [Real.rpow_one, Real.norm_of_nonneg (Nat.cast_nonneg N)]

/-- The Dirichlet series of the ideal-counting function converges for `s > 1`. -/
lemma summable_zetaTerm {s : ℝ} (hs : 1 < s) : Summable (zetaTerm K s) :=
  Commons.NumberTheory.NumberField.Set.summable_mul_rpow_neg_of_sum_Icc_bigO
    (fun n => Nat.cast_nonneg _) (logEuler_idealCount_bigO (K := K)) (by norm_num) hs

/-- The `L`-series of the ideal-counting function converges for `s > 1`. -/
lemma logEuler_LSeriesSummable_idealCount {s : ℝ} (hs : 1 < s) :
    LSeriesSummable (fun n : ℕ =>
      (Nat.card {I : Ideal (NumberField.RingOfIntegers K) // Ideal.absNorm I = n} : ℂ)) (s:ℂ) := by
  have := LSeriesSummable_of_sum_norm_bigO_and_nonneg
    (f := fun n : ℕ => (Nat.card {I : Ideal (NumberField.RingOfIntegers K) // Ideal.absNorm I = n} : ℝ))
    (logEuler_idealCount_bigO (K := K)) (fun n => Nat.cast_nonneg _) (by norm_num) (s := (s:ℂ))
    (by simpa using hs)
  simpa using this

/-- The real part of the Dedekind zeta function at a real `s > 1` is the real Dirichlet series
of the ideal-counting function. -/
lemma logEuler_dedekindZeta_re_eq_tsum {s : ℝ} (hs : 1 < s) :
    (NumberField.dedekindZeta K (s:ℂ)).re = ∑' n : ℕ, zetaTerm K s n := by
  have hsumm := logEuler_LSeriesSummable_idealCount (K := K) hs
  have hterm : ∀ n : ℕ,
      LSeries.term (fun n : ℕ =>
        (Nat.card {I : Ideal (NumberField.RingOfIntegers K) // Ideal.absNorm I = n} : ℂ)) (s:ℂ) n
      = (((Nat.card {I : Ideal (NumberField.RingOfIntegers K) // Ideal.absNorm I = n} : ℝ)
          * (n:ℝ)^(-s) : ℝ) : ℂ) := by
    intro n
    rw [LSeries.term]
    split_ifs with hn
    · subst hn
      simp [Real.zero_rpow (by linarith : (-s) ≠ 0)]
    · have hc : ((n:ℂ)) ^ (s:ℂ) = (((n:ℝ)^s : ℝ) : ℂ) := by
        rw [show (n:ℂ) = (((n:ℝ) : ℝ) : ℂ) by simp]
        exact (Complex.ofReal_cpow (Nat.cast_nonneg n) s).symm
      rw [hc, ← Complex.ofReal_natCast, ← Complex.ofReal_div, Real.rpow_neg (Nat.cast_nonneg n),
        div_eq_mul_inv]
  have hcongr : (fun n : ℕ => LSeries.term (fun n : ℕ =>
        (Nat.card {I : Ideal (NumberField.RingOfIntegers K) // Ideal.absNorm I = n} : ℂ)) (s:ℂ) n)
      = fun n : ℕ => (((Nat.card {I : Ideal (NumberField.RingOfIntegers K) // Ideal.absNorm I = n} : ℝ)
          * (n:ℝ)^(-s) : ℝ) : ℂ) := funext hterm
  change (LSeries (fun n : ℕ =>
    (Nat.card {I : Ideal (NumberField.RingOfIntegers K) // Ideal.absNorm I = n} : ℂ)) (s:ℂ)).re = _
  change (∑' n, LSeries.term (fun n : ℕ =>
    (Nat.card {I : Ideal (NumberField.RingOfIntegers K) // Ideal.absNorm I = n} : ℂ)) (s:ℂ) n).re = _
  have hsumm' : Summable (fun n : ℕ =>
      (((Nat.card {I : Ideal (NumberField.RingOfIntegers K) // Ideal.absNorm I = n} : ℝ)
          * (n:ℝ)^(-s) : ℝ) : ℂ)) := by
    rw [← hcongr]; exact hsumm
  rw [hcongr, Complex.re_tsum hsumm', tsum_congr fun n => Complex.ofReal_re _]
  exact tsum_congr fun n => rfl

/-- The series `∑_𝔭 log ((1 - N𝔭^{-s})^{-1})` over the nonzero prime ideals converges. -/
lemma summable_log_localFactor {s : ℝ} (hs : 1 < s) :
    Summable (fun 𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K) =>
      Real.log (localFactor K s 𝔭.asIdeal)) := by
  have hs0 : (0:ℝ) < s := lt_trans zero_lt_one hs
  have hbase : Summable (fun 𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K) =>
      2 * (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)) :=
    (Commons.NumberTheory.NumberField.Set.summable_primeIdealNorm K hs).mul_left 2
  have hhalf : ∀ 𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K),
      2 * (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) ≤ 1 := fun 𝔭 => by
    have hle : (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) ≤ (2:ℝ) ^ (-s) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) (two_le_absNorm_primeIdeal 𝔭) (by linarith)
    have h2lt : (2:ℝ) * 2 ^ (-s) < 1 := by
      have h : (2:ℝ) ^ (1 + (-s)) < 1 :=
        (Real.rpow_lt_one_iff_of_pos (show (0:ℝ) < 2 by norm_num)).mpr
          (Or.inl ⟨by norm_num, by linarith⟩)
      rw [Real.rpow_add (show (0:ℝ) < 2 by norm_num), Real.rpow_one] at h
      exact h
    linarith
  have hle : ∀ 𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K),
      Real.log (localFactor K s 𝔭.asIdeal) ≤ 2 * (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) := fun 𝔭 =>
    Commons.Analysis.ExpLog.log_inv_one_sub_le_two
      (le_of_lt (rpow_neg_absNorm_primeIdeal_pos s 𝔭)) (hhalf 𝔭)
  refine Summable.of_nonneg_of_le (fun 𝔭 => ?_) hle hbase
  · rw [localFactor, Real.log_inv]
    exact neg_nonneg.mpr (Real.log_nonpos (by linarith [rpow_neg_absNorm_primeIdeal_lt_one hs0 𝔭])
      (by linarith [rpow_neg_absNorm_primeIdeal_pos s 𝔭]))

/-- The logarithmic series over the nonzero prime ideals converges. -/
lemma summable_log_one_sub_primeIdeal {s : ℝ} (hs : 1 < s) :
    Summable (fun 𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K) =>
      -Real.log (1 - (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s))) := by
  have := summable_log_localFactor (K := K) hs
  refine this.congr fun 𝔭 => ?_
  rw [localFactor, Real.log_inv]

end Analysis

/-! ## The logarithmic Euler product -/

/-- **The logarithmic Euler product for the Dedekind zeta function of a number field.**

For real `s > 1`, the logarithm of the Dedekind zeta function is the sum, over the nonzero prime
ideals `𝔭` of `𝓞 K`, of `-log (1 - N𝔭^{-s})`. -/
theorem log_eulerProduct_primeIdeal (K : Type*) [Field K] [NumberField K] {s : ℝ} (hs : 1 < s) :
    ∑' 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
        -Real.log (1 - (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s))
      = Real.log ((NumberField.dedekindZeta K (s : ℂ)).re) := by
  classical
  have hspos : (0:ℝ) < s := lt_trans zero_lt_one hs
  have hmono : ∀ n : ℕ, 0 ≤ zetaTerm K s n := fun n =>
    mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hzt0 : zetaTerm K s 0 = 0 := by
    simp only [zetaTerm, Nat.cast_zero, Real.zero_rpow (by linarith : (-s) ≠ 0), mul_zero]
  have hzt1 : zetaTerm K s 1 = 1 := by
    haveI : Unique {I : Ideal (NumberField.RingOfIntegers K) // Ideal.absNorm I = 1} :=
      { default := ⟨⊤, by rw [Ideal.absNorm_top]⟩
        uniq := fun I => Subtype.ext (Ideal.absNorm_eq_one_iff.mp I.2) }
    simp only [zetaTerm, Nat.card_unique, Nat.cast_one, Real.one_rpow, mul_one]
  have hmul : ∀ {m n : ℕ}, Nat.Coprime m n →
      zetaTerm K s (m * n) = zetaTerm K s m * zetaTerm K s n := by
    intro m n hmn
    have ha := Commons.NumberTheory.NumberField.card_ideals_absNorm_mul (K := K) hmn
    simp only [zetaTerm]
    rw [ha, Nat.cast_mul, Nat.cast_mul,
      Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)]
    ring
  have hsum : Summable (zetaTerm K s) := summable_zetaTerm (K := K) hs
  have hEuler : HasProd (fun p : Nat.Primes => ∑' e : ℕ, zetaTerm K s ((p:ℕ) ^ e))
      (NumberField.dedekindZeta K (s : ℂ)).re := by
    have hE := _root_.EulerProduct.eulerProduct_hasProd (f := zetaTerm K s) hzt1
      (fun {_ _} hmn => hmul hmn) hsum.norm hzt0
    rw [← logEuler_dedekindZeta_re_eq_tsum (K := K) hs] at hE
    exact hE
  have hLpos : 0 < (NumberField.dedekindZeta K (s : ℂ)).re := by
    rw [logEuler_dedekindZeta_re_eq_tsum (K := K) hs]
    exact Summable.tsum_pos hsum (fun n => hmono n) 1 (by rw [hzt1]; norm_num)
  -- The local factors.
  have hloc : ∀ p : Nat.Primes,
      ∑' e : ℕ, zetaTerm K s ((p:ℕ) ^ e)
        = ∏ P ∈ IsDedekindDomain.primesOverFinset (Ideal.span ({((p:ℕ):ℤ)} : Set ℤ))
            (NumberField.RingOfIntegers K), localFactor K s P := by
    intro p
    haveI : Fact (Nat.Prime (p:ℕ)) := ⟨p.2⟩
    have hppos : (0:ℝ) < (p:ℕ) := by exact_mod_cast p.2.pos
    have hX0 : 0 ≤ ((p:ℕ):ℝ) ^ (-s) := Real.rpow_nonneg (le_of_lt hppos) _
    have hX1 : ((p:ℕ):ℝ) ^ (-s) < 1 :=
      (Real.rpow_lt_one_iff_of_pos hppos).mpr (Or.inl ⟨by
        have : (2:ℝ) ≤ (p:ℕ) := by exact_mod_cast p.2.two_le
        linarith, by linarith⟩)
    have hterm : ∀ e : ℕ, zetaTerm K s ((p:ℕ) ^ e)
        = (Nat.card {I : Ideal (NumberField.RingOfIntegers K) // Ideal.absNorm I = (p:ℕ) ^ e} : ℝ)
          * (((p:ℕ):ℝ) ^ (-s)) ^ e := by
      intro e
      simp only [zetaTerm]
      rw [Nat.cast_pow]
      congr 1
      rw [← Real.rpow_natCast_mul (le_of_lt hppos) e (-s),
        show ((e:ℝ) * (-s)) = (-s) * (e:ℝ) by ring,
        Real.rpow_mul_natCast (le_of_lt hppos) (-s) e]
    rw [tsum_congr hterm]
    rw [Commons.NumberTheory.NumberField.tsum_prime_pow_card_mul_pow (K := K) (p : ℕ) (X := ((p:ℕ):ℝ) ^ (-s)) hX0 hX1]
    refine Finset.prod_congr rfl fun P hP => ?_
    rw [localFactor]
    congr 1
    rw [absNorm_eq_pow_inertiaDeg_of_mem_primesOverF (K := K) p.2 hP, Nat.cast_pow]
    rw [← Real.rpow_natCast_mul (le_of_lt hppos) (P.inertiaDeg ℤ) (-s),
      show ((P.inertiaDeg ℤ : ℝ) * (-s)) = (-s) * (P.inertiaDeg ℤ : ℝ) by ring,
      Real.rpow_mul_natCast (le_of_lt hppos) (-s) (P.inertiaDeg ℤ)]
  -- The local factors indexed by nonzero prime ideals.
  have hEuler' : HasProd (fun p : Nat.Primes =>
      ∏' 𝔭 : {𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K) //
        underlyingPrime 𝔭 = p}, localFactor K s 𝔭.1.asIdeal)
      (NumberField.dedekindZeta K (s : ℂ)).re := by
    rw [← show (fun p : Nat.Primes => ∑' e : ℕ, zetaTerm K s ((p:ℕ) ^ e))
        = (fun p : Nat.Primes => ∏' 𝔭 : {𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K) //
            underlyingPrime 𝔭 = p}, localFactor K s 𝔭.1.asIdeal) from funext fun p =>
        (hloc p).trans ((prod_primesOverF_eq_prod_fiber (K := K) p (localFactor K s)).trans
          (tprod_congr fun 𝔭 => rfl))]
    exact hEuler
  have hposg : ∀ 𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K),
      0 < localFactor K s 𝔭.asIdeal := by
    intro 𝔭
    rw [localFactor]
    exact inv_pos.mpr (by linarith [rpow_neg_absNorm_primeIdeal_lt_one hspos 𝔭])
  have hlogg : ∀ 𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K),
      Real.log (localFactor K s 𝔭.asIdeal)
        = -Real.log (1 - (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)) := by
    intro 𝔭
    rw [localFactor, Real.log_inv]
  have hmult : Multipliable (fun 𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K) =>
      localFactor K s 𝔭.asIdeal) :=
    Real.multipliable_of_summable_log hposg (summable_log_localFactor (K := K) hs)
  have hmultSigma : Multipliable (fun x : Sigma (fun p : Nat.Primes =>
      {𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K) // underlyingPrime 𝔭 = p}) =>
      localFactor K s x.2.1.asIdeal) :=
    (Equiv.multipliable_iff (f := fun 𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K) =>
        localFactor K s 𝔭.asIdeal)
      (Equiv.sigmaFiberEquiv (underlyingPrime (K := K)))).mpr hmult
  have hHasProdSigma : HasProd (fun x : Sigma (fun p : Nat.Primes =>
      {𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K) // underlyingPrime 𝔭 = p}) =>
      localFactor K s x.2.1.asIdeal) (NumberField.dedekindZeta K (s : ℂ)).re :=
    HasProd.sigma_of_hasProd hEuler' (fun p => by
      haveI : Fintype {𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K) //
          underlyingPrime 𝔭 = p} :=
        Fintype.ofEquiv _ (fiberEquiv (K := K) p).symm
      rw [tprod_fintype]
      exact hasProd_fintype
        (fun 𝔭 : {𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K) //
          underlyingPrime 𝔭 = p} => localFactor K s 𝔭.1.asIdeal)) hmultSigma
  have hHasProdg : HasProd (fun 𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K) =>
      localFactor K s 𝔭.asIdeal) (NumberField.dedekindZeta K (s : ℂ)).re :=
    (Equiv.hasProd_iff (f := fun 𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K) =>
      localFactor K s 𝔭.asIdeal)
      (Equiv.sigmaFiberEquiv (underlyingPrime (K := K)))).mp hHasProdSigma
  rw [Commons.Analysis.SpecialFunctions.Log.log_eq_tsum_log_of_hasProd hHasProdg hposg hLpos]
  exact tsum_congr fun 𝔭 => (hlogg 𝔭).symm

end Commons.NumberTheory.NumberField.DedekindZeta
