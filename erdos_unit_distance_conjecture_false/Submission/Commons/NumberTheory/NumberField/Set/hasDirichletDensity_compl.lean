import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.NumberField.Ideal.Asymptotics
import Submission.Commons.NumberTheory.NumberField.Set.primeIdealZetaSum_union_of_disjoint

open Filter IsDedekindDomain Topology Set Asymptotics
open scoped Classical NNReal ENNReal

set_option linter.style.haveILetI false

/-!
# Dirichlet density of the complement of a set of prime ideals

This file proves `Commons.NumberTheory.NumberField.Set.hasDirichletDensity_compl`: if a set `S` of
nonzero prime ideals of the ring of integers of a number field has Dirichlet density `δ`, then its
complement has Dirichlet density `1 - δ`.

The whole difficulty is that the definition of `NumberField.Set.HasDirichletDensity` uses
`tsum`, which takes the junk value `0` when the underlying series is not summable.  Hence, in order
to manipulate the ratio `S.primeIdealZetaSum s / univ.primeIdealZetaSum s`, one must know that the
total sum `∑' 𝔭, (N 𝔭) ^ (-s)` is a genuine, positive real number for `s > 1`.  This is established
in `summable_primeIdealNorm` below (via `summable_mul_rpow_neg_of_sum_Icc_bigO`, an instance of the
L-series convergence criterion, applied to the prime ideals grouped by norm).
-/

namespace Commons.NumberTheory.NumberField.Set

/-- The number of integral ideals of `𝓞 K` of norm at most `N` is `O(N)`; this is the only
asymptotic input needed below. -/
theorem absNorm_card_le_bigO (K : Type*) [Field K] [NumberField K] :
    (fun N : ℕ => (Nat.card {I : Ideal (NumberField.RingOfIntegers K) // Ideal.absNorm I ≤ N} : ℝ))
      =O[atTop] (fun N : ℕ => (N : ℝ)) := by
  obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.mp (NumberField.Ideal.tendsto_norm_le_div_atTop K) 1 one_pos
  set c : ℝ := (2 ^ NumberField.InfinitePlace.nrRealPlaces K *
      (2 * Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces K *
      NumberField.Units.regulator K * (NumberField.classNumber K : ℝ) /
      ((NumberField.Units.torsionOrder K : ℝ) * Real.sqrt |(NumberField.discr K : ℝ)|)) with hc
  have hbig_real : (fun s : ℝ => (Nat.card {I : Ideal (NumberField.RingOfIntegers K) //
        (Ideal.absNorm I : ℝ) ≤ s} : ℝ)) =O[atTop] (fun s : ℝ => s) := by
    refine IsBigO.of_bound (|c| + 1) ?_
    filter_upwards [eventually_ge_atTop (max N₀ 1)] with s hs
    have hs1 : (1:ℝ) ≤ s := le_trans (le_max_right _ _) hs
    have hs0 : (0:ℝ) ≤ s := le_trans zero_le_one hs1
    have hsN : N₀ ≤ s := le_trans (le_max_left _ _) hs
    have hdist := hN₀ s hsN
    rw [Real.dist_eq] at hdist
    have hlt : (Nat.card {I : Ideal (NumberField.RingOfIntegers K) //
          (Ideal.absNorm I : ℝ) ≤ s} : ℝ) / s < |c| + 1 := by
      have := (abs_lt.mp hdist).2
      linarith [le_abs_self c]
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg hs0]
    have : (Nat.card {I : Ideal (NumberField.RingOfIntegers K) //
          (Ideal.absNorm I : ℝ) ≤ s} : ℝ) = s * ((Nat.card {I : Ideal (NumberField.RingOfIntegers K) //
          (Ideal.absNorm I : ℝ) ≤ s} : ℝ) / s) := by
      rw [mul_div_cancel₀]; exact ne_of_gt (lt_of_lt_of_le zero_lt_one hs1)
    rw [this]
    calc s * ((Nat.card {I : Ideal (NumberField.RingOfIntegers K) //
            (Ideal.absNorm I : ℝ) ≤ s} : ℝ) / s)
        ≤ s * (|c| + 1) := by gcongr
      _ = (|c| + 1) * s := by ring
  have hbig_nat : (fun N : ℕ => (Nat.card {I : Ideal (NumberField.RingOfIntegers K) //
        (Ideal.absNorm I : ℝ) ≤ (N:ℝ)} : ℝ)) =O[atTop] (fun N : ℕ => (N:ℝ)) :=
    hbig_real.comp_tendsto tendsto_natCast_atTop_atTop
  refine hbig_nat.congr_left fun N => ?_
  show ((Nat.card {I : Ideal (NumberField.RingOfIntegers K) // (Ideal.absNorm I : ℝ) ≤ (N:ℝ)} : ℝ)
      = (Nat.card {I : Ideal (NumberField.RingOfIntegers K) // Ideal.absNorm I ≤ N} : ℝ))
  rw [Nat.card_congr (Equiv.subtypeEquivRight (fun I => Nat.cast_le))]


/-- For a number field `K`, the number of nonzero prime ideals of `𝓞 K` of norm at most `N` is
bounded by the number of all integral ideals of norm at most `N`, hence is `O(N)`.  Concretely, the
partial sums of the prime-counting function `n ↦ #{𝔭 | N 𝔭 = n}` are bounded by the ideal count. -/

theorem primeIdealCount_partial_sum_le (K : Type*) [Field K] [NumberField K] (N : ℕ) :
    ∑ k ∈ Finset.Icc 1 N, Nat.card {𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) //
        Ideal.absNorm 𝔭.asIdeal = k}
      ≤ Nat.card {I : Ideal (NumberField.RingOfIntegers K) // Ideal.absNorm I ≤ N} := by
  classical
  haveI : ∀ k : {k : ℕ // k ∈ Finset.Icc 1 N},
      Finite {𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) //
        Ideal.absNorm 𝔭.asIdeal = k.1} := fun k =>
    ((Ideal.finite_setOfPred_absNorm_eq k.1).preimage
      (Set.injOn_of_injective IsDedekindDomain.HeightOneSpectrum.asIdeal_injective)).to_subtype
  haveI : Finite {I : Ideal (NumberField.RingOfIntegers K) // Ideal.absNorm I ≤ N} :=
    (Ideal.finite_setOfPred_absNorm_le N).to_subtype
  have heq : Nat.card (Sigma (fun k : {k : ℕ // k ∈ Finset.Icc 1 N} =>
        {𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) //
          Ideal.absNorm 𝔭.asIdeal = k.1}))
      = ∑ k ∈ Finset.Icc 1 N, Nat.card {𝔭 : IsDedekindDomain.HeightOneSpectrum
          (NumberField.RingOfIntegers K) // Ideal.absNorm 𝔭.asIdeal = k} := by
    rw [Nat.card_sigma]
    exact Finset.sum_coe_sort (Finset.Icc 1 N) (fun k => Nat.card
      {𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) //
        Ideal.absNorm 𝔭.asIdeal = k})
  rw [← heq]
  refine Nat.card_le_card_of_injective (fun x : Sigma (fun k : {k : ℕ // k ∈ Finset.Icc 1 N} =>
        {𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) //
          Ideal.absNorm 𝔭.asIdeal = k.1}) =>
      (⟨x.2.1.asIdeal, by rw [x.2.2]; exact (Finset.mem_Icc.mp x.1.2).2⟩ :
        {I : Ideal (NumberField.RingOfIntegers K) // Ideal.absNorm I ≤ N})) ?_
  intro a b h
  simp only [Subtype.mk.injEq] at h
  have hprime : a.2.1 = b.2.1 := IsDedekindDomain.HeightOneSpectrum.asIdeal_injective h
  have hk : (a.1 : ℕ) = b.1 := by rw [← a.2.2, ← b.2.2, hprime]
  exact Sigma.ext (Subtype.ext hk)
    ((Subtype.heq_iff_coe_eq (fun x => by rw [hk])).mpr hprime)


/-- A general convergence criterion for Dirichlet series with nonnegative coefficients and partial
sums `O(N ^ r)`.  This is a direct consequence of `LSeriesSummable_of_sum_norm_bigO_and_nonneg`. -/

theorem summable_mul_rpow_neg_of_sum_Icc_bigO {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) {r s : ℝ}
    (hO : (fun N : ℕ => ∑ k ∈ Finset.Icc 1 N, f k) =O[atTop] (fun N : ℕ => (N : ℝ) ^ r))
    (hr : 0 ≤ r) (hs : r < s) :
    Summable (fun n : ℕ => f n * (n : ℝ) ^ (-s)) := by
  have hs0 : 0 < s := lt_of_le_of_lt hr hs
  have hL : LSeriesSummable (fun n => (f n : ℂ)) (s : ℂ) :=
    LSeriesSummable_of_sum_norm_bigO_and_nonneg hO hf hr (by simpa using hs)
  have hnorm : Summable (fun n : ℕ => ‖LSeries.term (fun n => (f n : ℂ)) (s:ℂ) n‖) := hL.norm
  refine (summable_congr ?_).mpr hnorm
  intro n
  rw [LSeries.norm_term_eq]
  by_cases hn : n = 0
  · subst hn
    simp [Real.zero_rpow (neg_ne_zero.mpr hs0.ne')]
  · rw [if_neg hn]
    have hfn : ‖((f n : ℂ))‖ = f n := by rw [Complex.norm_real, Real.norm_of_nonneg (hf n)]
    rw [hfn, div_eq_mul_inv, Real.rpow_neg (Nat.cast_nonneg n), Complex.ofReal_re]


/-- **Key summability input.** For every real `s > 1`, the Dirichlet series over the nonzero prime
ideals of `𝓞 K` converges:
`∑' 𝔭, (N 𝔭) ^ (-s)` is a genuine real number.

This is proved by grouping prime ideals by their norm: writing `b n = #{𝔭 | N 𝔭 = n}`, the partial
sums of `b` are `O(N)` (a prime ideal of norm `n` is, in particular, an ideal of norm `n`), so
`∑_n b n * n ^ (-s)` converges for `s > 1` by `summable_mul_rpow_neg_of_sum_Icc_bigO`; the passage
from the sums over `ℕ` back to the sums over prime ideals is done in the `ℝ≥0∞`-valued world where
`ENNReal.tsum_fiberwise` applies without summability hypotheses. -/

theorem summable_primeIdealNorm (K : Type*) [Field K] [NumberField K] {s : ℝ} (hs : 1 < s) :
    Summable (fun 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) =>
      (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)) := by
  classical
  let g : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) → ℕ :=
    fun 𝔭 => Ideal.absNorm 𝔭.asIdeal
  haveI hfin : ∀ n : ℕ, Finite ↥(g ⁻¹' {n}) := fun n =>
    ((Ideal.finite_setOfPred_absNorm_eq n).preimage
      (Set.injOn_of_injective IsDedekindDomain.HeightOneSpectrum.asIdeal_injective)).to_subtype
  let b : ℕ → ℕ := fun n => Nat.card ↥(g ⁻¹' {n})
  have hpart : (fun N : ℕ => ∑ k ∈ Finset.Icc 1 N, (b k : ℝ)) =O[atTop] (fun N : ℕ => (N:ℝ)) := by
    obtain ⟨C, hC⟩ := (absNorm_card_le_bigO K).bound
    refine IsBigO.of_bound C ?_
    filter_upwards [hC] with N hN
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _)] at hN
    rw [Real.norm_of_nonneg (Nat.cast_nonneg N)] at hN
    rw [Real.norm_of_nonneg (Finset.sum_nonneg fun k _ => Nat.cast_nonneg _)]
    rw [Real.norm_of_nonneg (Nat.cast_nonneg N)]
    have hle : (∑ k ∈ Finset.Icc 1 N, (b k : ℝ)) ≤ (Nat.card {I : Ideal (NumberField.RingOfIntegers K) //
        Ideal.absNorm I ≤ N} : ℝ) := by
      exact_mod_cast primeIdealCount_partial_sum_le K N
    exact le_trans hle hN
  have hsumb : Summable (fun n : ℕ => (b n : ℝ) * (n:ℝ)^(-s)) :=
    summable_mul_rpow_neg_of_sum_Icc_bigO (fun n => Nat.cast_nonneg _)
      (by simpa [Real.rpow_one] using hpart) (by norm_num) hs
  have hfib : (∑' 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
        ENNReal.ofReal ((g 𝔭 : ℝ)^(-s))) = ∑' n : ℕ, ENNReal.ofReal ((b n : ℝ) * (n:ℝ)^(-s)) := by
    rw [← ENNReal.tsum_fiberwise
      (fun 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) =>
        ENNReal.ofReal ((g 𝔭 : ℝ)^(-s))) g]
    refine tsum_congr fun n => ?_
    haveI : Fintype ↥(g ⁻¹' {n}) := Fintype.ofFinite _
    rw [tsum_fintype]
    have h1 : ∑ 𝔭 : ↥(g ⁻¹' {n}), ENNReal.ofReal (((g 𝔭.1 : ℕ) : ℝ)^(-s))
        = ∑ _𝔭 : ↥(g ⁻¹' {n}), ENNReal.ofReal ((n:ℝ)^(-s)) :=
      Finset.sum_congr rfl (fun 𝔭 _ => by
        have hg : g 𝔭.1 = n := 𝔭.2
        rw [hg])
    rw [h1, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, nsmul_eq_mul]
    have h2 : Nat.card ↥(g ⁻¹' {n}) = b n := rfl
    rw [h2, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg (b n))]
  have hne : (∑' 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
        ENNReal.ofReal ((g 𝔭 : ℝ)^(-s))) ≠ ⊤ := by
    rw [hfib]
    exact hsumb.tsum_ofReal_ne_top
  have hpos : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      0 ≤ (g 𝔭 : ℝ) ^ (-s) := fun 𝔭 =>
    le_of_lt (Real.rpow_pos_of_pos (Nat.cast_pos.mpr
      (Nat.pos_of_ne_zero fun h => 𝔭.ne_bot (Ideal.absNorm_eq_zero_iff.mp h))) _)
  have key : Summable (fun 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) =>
      (Real.toNNReal ((g 𝔭 : ℝ)^(-s)) : ℝ)) := by
    refine (ENNReal.tsum_coe_ne_top_iff_summable_coe (f := fun 𝔭 :
      IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) =>
      Real.toNNReal ((g 𝔭 : ℝ)^(-s)))).mp ?_
    have h2 : (∑' 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
        ((Real.toNNReal ((g 𝔭 : ℝ)^(-s)) : ℝ≥0) : ℝ≥0∞))
        = ∑' 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
          ENNReal.ofReal ((g 𝔭 : ℝ)^(-s)) :=
      tsum_congr (fun 𝔭 => ENNReal.ofNNReal_toNNReal _)
    rw [h2]
    exact hne
  exact key.congr (fun 𝔭 => Real.coe_toNNReal _ (hpos 𝔭))


theorem hasDirichletDensity_compl {K : Type*} [Field K] [NumberField K]
    {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} {δ : ℝ}
    (hS : NumberField.Set.HasDirichletDensity S δ) :
    NumberField.Set.HasDirichletDensity Sᶜ (1 - δ) := by
  rw [NumberField.Set.HasDirichletDensity] at hS ⊢
  haveI hne0 : Nonempty (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :=
    let ⟨M, hM⟩ := Ideal.exists_maximal (NumberField.RingOfIntegers K)
    ⟨⟨M, hM.isPrime,
      Ring.ne_bot_of_isMaximal_of_not_isField hM (NumberField.RingOfIntegers.not_isField K)⟩⟩
  obtain ⟨𝔭₀⟩ := hne0
  have heq : (fun s : ℝ => NumberField.Set.primeIdealZetaSum (K := K) Sᶜ s /
      NumberField.Set.primeIdealZetaSum (K := K) univ s)
      =ᶠ[𝓝[>] 1] (fun s : ℝ => 1 - NumberField.Set.primeIdealZetaSum (K := K) S s /
      NumberField.Set.primeIdealZetaSum (K := K) univ s) := by
    filter_upwards [self_mem_nhdsWithin] with s hs1
    have hsm : Summable (fun 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) =>
        (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)) := summable_primeIdealNorm K hs1
    have hSsm : Summable (fun 𝔭 : S => (Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s)) :=
      hsm.comp_injective Subtype.val_injective
    have hCsm : Summable (fun 𝔭 : ↥(Sᶜ) => (Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s)) :=
      hsm.comp_injective Subtype.val_injective
    have hsplit := primeIdealZetaSum_union_of_disjoint (S := S) (T := Sᶜ) disjoint_compl_right s hSsm hCsm
    rw [Set.union_compl_self] at hsplit
    have hpos : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
        0 < (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) := fun 𝔭 =>
      Real.rpow_pos_of_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero fun h =>
        𝔭.ne_bot (Ideal.absNorm_eq_zero_iff.mp h))) _
    have hne : NumberField.Set.primeIdealZetaSum (K := K) S s +
        NumberField.Set.primeIdealZetaSum (K := K) Sᶜ s ≠ 0 := by
      have hpu : 0 < NumberField.Set.primeIdealZetaSum (K := K)
          (univ : Set (IsDedekindDomain.HeightOneSpectrum
          (NumberField.RingOfIntegers K))) s := by
        rw [NumberField.Set.primeIdealZetaSum_def,
          tsum_univ (f := fun 𝔭 : IsDedekindDomain.HeightOneSpectrum
            (NumberField.RingOfIntegers K) => (Ideal.absNorm 𝔭.asIdeal : ℝ)^(-s))]
        exact Summable.tsum_pos hsm (fun 𝔭 => (hpos 𝔭).le) 𝔭₀ (hpos 𝔭₀)
      rw [hsplit] at hpu
      exact ne_of_gt hpu
    rw [hsplit, ← div_self hne, ← sub_div]
    ring
  refine Tendsto.congr' heq.symm ?_
  exact tendsto_const_nhds.sub hS


end Commons.NumberTheory.NumberField.Set