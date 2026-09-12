import Mathlib
import Submission.Commons.Measure.Independence.measureReal_forall_abs_le_prod
import Submission.Commons.Probability.FinFunction.sum_pow_two_le

namespace Commons.Probability.Independence

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

/-- Elementary arithmetic estimate used for the dyadic level decomposition:
`3k + 1 ≤ 4^k` for every natural number `k`. -/
private lemma three_mul_add_one_le_four_pow (k : ℕ) : 3 * k + 1 ≤ 4 ^ k := by
  induction k with
  | zero => norm_num
  | succ n ih =>
    rw [pow_succ]
    nlinarith [Nat.one_le_pow n 4 (by norm_num)]

/-- For every positive real `ε` and every real `a` there is a dyadic level `j` with
`|a| ≤ ε * 2^j`. -/
private lemma exists_dyadic_level {ε : ℝ} (hε : 0 < ε) (a : ℝ) : ∃ j : ℕ, |a| ≤ ε * 2 ^ j := by
  obtain ⟨n, hn⟩ := exists_nat_gt (|a| / ε)
  refine ⟨n, ?_⟩
  have h2 : (n : ℝ) < 2 ^ n := by exact_mod_cast Nat.lt_two_pow_self
  have h3 : |a| / ε < (2 : ℝ) ^ n := lt_trans hn h2
  have h4 : |a| < (2 : ℝ) ^ n * ε := (div_lt_iff₀ hε).mp h3
  calc |a| ≤ (2 : ℝ) ^ n * ε := le_of_lt h4
    _ = ε * 2 ^ n := by ring

/-- **Tensorization lemma, part (1)** (Tikhomirov 2020, Lemma 2.2(1)).

Let `ξ : Fin m → Ω → ℝ` be a family of mutually independent real random variables on a
probability space `(Ω, P)` (`iIndepFun ξ P`).  Assume that for some `ε₀ > 0` and `K > 0` every
`ξ k` satisfies the small-ball estimate `P{|ξ k| ≤ s} ≤ K s` for all `s ≥ ε₀`.  Then for every
`ε` with `ε₀ ≤ ε` (the statement below only asks for the range `ε₀ ≤ ε ≤ Θ ε₀`),

`P{ ‖(ξ 1, …, ξ m)‖₂ ≤ ε √m } ≤ (Ct · K · ε)^m`

with a constant `Ct > 0` depending only on `Θ`.

The proof uses the dyadic level decomposition: on the event `∑ ξ k² ≤ ε² m` each coordinate
`ξ k` has a level `lvl k ∈ ℕ` with `|ξ k| ≤ ε · 2 ^ (lvl k)` and `∑ k, 4 ^ (lvl k) ≤ 5 m`,
whence `∑ k, lvl k ≤ 4m/3`.  Therefore the event is covered by the union of the events
`{∀ k, |ξ k| ≤ ε · 2 ^ (j k)}` over the profiles `j : Fin m → Fin (⌊4m/3⌋ + 1)` with
`∑ k, (j k : ℕ) ≤ ⌊4m/3⌋`.  Independence bounds each of these by the product of the small-ball
estimates, and the profile sum is controlled by the elementary analytic estimate
`Commons.Probability.FinFunction.sum_pow_two_le`. -/
theorem tensorization_linear {Θ : ℝ} (hΘ : 1 ≤ Θ) :
    ∃ Ct : ℝ, 0 < Ct ∧ ∀ {m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] {ξ : Fin m → Ω → ℝ} (hξ : iIndepFun ξ P)
      {K ε₀ ε : ℝ} (hK : 0 < K) (hε₀ : 0 < ε₀) (h1 : ε₀ ≤ ε) (h2 : ε ≤ Θ * ε₀)
      (hsmall : ∀ k : Fin m, ∀ s : ℝ, ε₀ ≤ s → P.real {x | |ξ k x| ≤ s} ≤ K * s),
      P.real {x | (∑ k, (ξ k x) ^ 2) ≤ ε ^ 2 * (m : ℝ)} ≤ (Ct * K * ε) ^ m := by
  refine ⟨16, by norm_num, ?_⟩
  intro m Ω _ P _ ξ hξ K ε₀ ε hK hε₀ h1 h2 hsmall
  have hε : 0 < ε := lt_of_lt_of_le hε₀ h1
  -- dyadic levels
  have hex : ∀ (i : Fin m) (x : Ω), ∃ j : ℕ, |ξ i x| ≤ ε * 2 ^ j :=
    fun i x => exists_dyadic_level hε (ξ i x)
  let lvl : Fin m → Ω → ℕ := fun i x => Nat.find (hex i x)
  have hlvl_le : ∀ (i : Fin m) (x : Ω), |ξ i x| ≤ ε * 2 ^ (lvl i x) :=
    fun i x => Nat.find_spec (hex i x)
  -- the key pointwise estimate `ε² 4^(lvl i) ≤ ε² + 4 (ξ i)²`
  have hlvl_four : ∀ (i : Fin m) (x : Ω), ε ^ 2 * 4 ^ (lvl i x) ≤ ε ^ 2 + 4 * (ξ i x) ^ 2 := by
    intro i x
    by_cases h0 : lvl i x = 0
    · rw [h0, pow_zero, mul_one]
      nlinarith [sq_nonneg (ξ i x)]
    · have hpos : 1 ≤ lvl i x := by omega
      have hlt : lvl i x - 1 < lvl i x := by omega
      have hmin := Nat.find_min (hex i x) hlt
      have hstep : ε * 2 ^ (lvl i x - 1) < |ξ i x| := not_le.mp hmin
      have hsq : (ε * 2 ^ (lvl i x - 1)) ^ 2 < (ξ i x) ^ 2 := by
        have hnn : (0 : ℝ) ≤ ε * 2 ^ (lvl i x - 1) := by positivity
        have h := pow_lt_pow_left₀ hstep hnn (by norm_num : (2 : ℕ) ≠ 0)
        simpa [sq_abs] using h
      have h2sq : ((2 : ℝ) ^ (lvl i x - 1)) ^ 2 = 4 ^ (lvl i x - 1) := by
        rw [← pow_mul, mul_comm (lvl i x - 1) 2, pow_mul, show (2 : ℝ) ^ 2 = 4 by norm_num]
      have hkey : (ε * 2 ^ (lvl i x - 1)) ^ 2 = ε ^ 2 * 4 ^ (lvl i x - 1) := by
        rw [mul_pow, h2sq]
      have hk' : (4 : ℝ) ^ (lvl i x) = 4 * 4 ^ (lvl i x - 1) := by
        conv_lhs => rw [show lvl i x = (lvl i x - 1) + 1 by omega]
        rw [pow_succ]
        ring
      calc ε ^ 2 * 4 ^ (lvl i x) = 4 * (ε * 2 ^ (lvl i x - 1)) ^ 2 := by rw [hk', hkey]; ring
        _ ≤ ε ^ 2 + 4 * (ξ i x) ^ 2 := by nlinarith [hsq, sq_nonneg ε]
  set S : Set Ω := {x | (∑ k, (ξ k x) ^ 2) ≤ ε ^ 2 * (m : ℝ)} with hS
  -- on `S`, the sum of `4^(lvl i)` is at most `5m`
  have hsum4 : ∀ x ∈ S, (∑ i, (4 : ℝ) ^ (lvl i x)) ≤ 5 * (m : ℝ) := by
    intro x hx
    have hSx : (∑ i, (ξ i x) ^ 2) ≤ ε ^ 2 * (m : ℝ) := hx
    have h1' : (∑ i, ε ^ 2 * 4 ^ (lvl i x)) ≤ ∑ i, (ε ^ 2 + 4 * (ξ i x) ^ 2) :=
      Finset.sum_le_sum (fun i _ => hlvl_four i x)
    have h1'' : ∑ i, ε ^ 2 * 4 ^ (lvl i x) = ε ^ 2 * ∑ i, (4 : ℝ) ^ (lvl i x) :=
      (Finset.mul_sum _ _ _).symm
    have h2'' : ∑ i, (ε ^ 2 + 4 * (ξ i x) ^ 2) = (m : ℝ) * ε ^ 2 + 4 * ∑ i, (ξ i x) ^ 2 := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, ← Finset.mul_sum]
    rw [h1'', h2''] at h1'
    have h3' : ε ^ 2 * (∑ i, (4 : ℝ) ^ (lvl i x)) ≤ ε ^ 2 * (5 * (m : ℝ)) := by
      nlinarith [h1', hSx, sq_nonneg ε]
    exact le_of_mul_le_mul_left h3' (by positivity)
  -- hence the levels cannot exceed `4m/3`
  set Λ : ℕ := 4 * m / 3 with hΛ
  have hsumΛ : ∀ x ∈ S, (∑ i, lvl i x) ≤ Λ := by
    intro x hx
    have h4 : (∑ i, (4 : ℕ) ^ (lvl i x)) ≤ 5 * m := by
      have := hsum4 x hx
      exact_mod_cast this
    have h3 : (∑ i, (3 * (lvl i x) + 1)) ≤ ∑ i, (4 : ℕ) ^ (lvl i x) :=
      Finset.sum_le_sum (fun i _ => three_mul_add_one_le_four_pow (lvl i x))
    have h3' : (∑ i, (3 * (lvl i x) + 1)) = 3 * (∑ i, lvl i x) + m := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp [Finset.card_univ, Fintype.card_fin]
    have : 3 * (∑ i, lvl i x) ≤ 4 * m := by omega
    rw [hΛ, Nat.le_div_iff_mul_le (by norm_num : 0 < 3)]
    omega
  -- the covering by level profiles
  set F : Finset (Fin m → Fin (Λ + 1)) :=
    (Finset.univ).filter (fun j => ∑ i, ((j i : ℕ)) ≤ Λ) with hF
  set B : (Fin m → Fin (Λ + 1)) → Set Ω :=
    fun j => {x | ∀ i, |ξ i x| ≤ ε * 2 ^ ((j i : ℕ))} with hB
  have hcover : S ⊆ ⋃ j ∈ F, B j := by
    intro x hx
    have hsum := hsumΛ x hx
    have hlt : ∀ i : Fin m, lvl i x < Λ + 1 := fun i =>
      Nat.lt_succ_of_le (le_trans (Finset.single_le_sum (s := Finset.univ)
        (f := fun i => lvl i x) (fun i _ => Nat.zero_le _) (Finset.mem_univ i)) hsum)
    refine Set.mem_iUnion.mpr ⟨fun i => ⟨lvl i x, hlt i⟩, ?_⟩
    refine Set.mem_iUnion.mpr ⟨?_, ?_⟩
    · simp only [hF, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hsum
    · rw [hB]
      intro i
      exact hlvl_le i x
  -- bounding each term of the union
  have hFsum : ∑ j ∈ F, P.real (B j) ≤ (K * ε) ^ m * (4 ^ Λ * 2 ^ m) := by
    calc ∑ j ∈ F, P.real (B j)
        ≤ ∑ j ∈ F, (K * ε) ^ m * (2 : ℝ) ^ (∑ i, ((j i : ℕ))) := by
          refine Finset.sum_le_sum fun j hj => ?_
          have hprod : ∏ i : Fin m, (K * ε * 2 ^ ((j i : ℕ))) =
              (K * ε) ^ m * (2 : ℝ) ^ (∑ i, ((j i : ℕ))) := by
            calc ∏ i : Fin m, (K * ε * 2 ^ ((j i : ℕ)))
                = ∏ i : Fin m, ((K * ε) * 2 ^ ((j i : ℕ))) :=
                  Finset.prod_congr rfl (fun i _ => by ring)
              _ = (∏ i : Fin m, (K * ε)) * ∏ i : Fin m, (2 : ℝ) ^ ((j i : ℕ)) :=
                  Finset.prod_mul_distrib
              _ = (K * ε) ^ m * (2 : ℝ) ^ (∑ i, ((j i : ℕ))) := by
                  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
                      Finset.prod_pow_eq_pow_sum]
          have hsmall' : ∀ i : Fin m, P.real {x | |ξ i x| ≤ ε * 2 ^ ((j i : ℕ))} ≤
              K * ε * 2 ^ ((j i : ℕ)) := by
            intro i
            have h2' : ε₀ ≤ ε * 2 ^ ((j i : ℕ)) :=
              le_trans h1 (le_mul_of_one_le_right hε.le (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)))
            refine (hsmall i _ h2').trans (le_of_eq ?_)
            ring
          have hb := Commons.Measure.Independence.measureReal_forall_abs_le_prod P hξ
            (η := fun i => ε * 2 ^ ((j i : ℕ)))
            (τ := fun i => K * ε * 2 ^ ((j i : ℕ)))
            (fun i => by positivity) hsmall'
          rw [hB]
          exact hb.trans (le_of_eq hprod)
        _ = (K * ε) ^ m * ∑ j ∈ F, (2 : ℝ) ^ (∑ i, ((j i : ℕ))) := by
          rw [Finset.mul_sum]
        _ ≤ (K * ε) ^ m * (4 ^ Λ * 2 ^ m) := by
          apply mul_le_mul_of_nonneg_left _
            (pow_nonneg (mul_nonneg hK.le hε.le) m)
          exact Commons.Probability.FinFunction.sum_pow_two_le
  calc P.real S
      ≤ P.real (⋃ j ∈ F, B j) := measureReal_mono hcover (by simp [measure_ne_top])
    _ ≤ ∑ j ∈ F, P.real (B j) := measureReal_biUnion_finset_le F B
    _ ≤ (K * ε) ^ m * (4 ^ Λ * 2 ^ m) := hFsum
    _ ≤ (K * ε) ^ m * 2 ^ (4 * m) := by
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg (mul_nonneg hK.le hε.le) m)
        have hΛ3 : 3 * Λ ≤ 4 * m := by
          rw [hΛ]
          exact Nat.mul_div_le (4 * m) 3
        have h2Λ : 2 * Λ + m ≤ 4 * m := by omega
        calc (4 : ℝ) ^ Λ * 2 ^ m = 2 ^ (2 * Λ) * 2 ^ m := by
              rw [show (4 : ℝ) = 2 ^ 2 by norm_num, pow_mul]
          _ = 2 ^ (2 * Λ + m) := (pow_add _ _ _).symm
          _ ≤ 2 ^ (4 * m) := pow_le_pow_right₀ (by norm_num) h2Λ
    _ = (16 * K * ε) ^ m := by
        rw [show (2 : ℝ) ^ (4 * m) = 16 ^ m by
          rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul]; norm_num]
        rw [mul_comm ((K * ε) ^ m), ← mul_pow]
        ring_nf

end Commons.Probability.Independence
