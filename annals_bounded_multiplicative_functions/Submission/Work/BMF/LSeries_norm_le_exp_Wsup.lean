import Mathlib
import Submission.Work.BMF.halasz_defs
import Submission.Work.BMF.LSeries_exp_Wsup_defs
import Submission.Work.BMF.halasz_mertens_aux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Euler product bound `‖LSeries f s‖ ≤ C · exp (Wsup f x α (T+1))`

For a multiplicative `1`-bounded `f : ℕ → ℂ`, `x ≥ 2`, `0 < α`, `exp (1/α) ≤ x` and `s : ℂ` with
`Re s = 1 + α` and `|Im s| ≤ T + 1` we have

`‖LSeries f s‖ ≤ C · exp (Wsup f x α (T+1))`

where `Wsup f x α T = sup_{|t| ≤ T} Re Σ_{p ≤ x} f p · p^{-1-α-it}` and `C` is an absolute
constant.

The proof is the standard "logarithm of the Euler product" argument: on `Re s = 1 + α > 1` the
L-series is the limit of the finite Euler products `∏_{p < N} eulerFac f p s`, the local factor
obeys `‖eulerFac f p s‖ ≤ exp (Re (f p · p^{-s}) + C p^{-2 Re s})`, the `Σ_p p^{-2 Re s}` is
`O(1)`, the primes `p > x` contribute at most `Σ_{p > x} p^{-1-α} = O(1)` (this is where
`exp (1/α) ≤ x`, i.e. `α log x ≥ 1`, is used, through Mertens' theorem), and finally the value
`t = Im s` belongs to the window defining `Wsup`.
-/

namespace Work.BMF

open Finset Real Complex
open scoped Topology BigOperators

/-! ## Elementary finset facts -/

/-- For `N ≥ ⌊x⌋₊ + 1`, the primes below `N` that are `≤ x` are exactly the primes `≤ ⌊x⌋₊`. -/
lemma primesBelow_filter_le_eq (x : ℝ) (hx0 : 0 ≤ x) {N : ℕ} (hN : ⌊x⌋₊ + 1 ≤ N) :
    N.primesBelow.filter (fun p : ℕ => (p : ℝ) ≤ x) = (⌊x⌋₊).primesLE := by
  ext p
  simp only [Nat.mem_primesBelow, Finset.mem_filter, Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨hpN, hpp⟩, hpx⟩
    exact ⟨Nat.le_floor hpx, hpp⟩
  · rintro ⟨hp, hpp⟩
    exact ⟨⟨by omega, hpp⟩, le_trans (by exact_mod_cast hp) (Nat.floor_le hx0)⟩

/-! ## `Σ_{p ∈ S} p^{-2σ} ≤ 2` for a finite set of primes -/

theorem primes_rpow_sum_le (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (σ : ℝ) (hσ : 1 ≤ σ) :
    (∑ p ∈ S, (p : ℝ) ^ (-(2 * σ))) ≤ 2 := by
  have hterm : ∀ p ∈ S, (p : ℝ) ^ (-(2 * σ)) ≤ (1 : ℝ) / (p : ℝ) ^ 2 := by
    intro p hp
    have hp1 : (1 : ℝ) ≤ (p : ℝ) := by
      have := (hS p hp).two_le
      exact_mod_cast (by omega : 1 ≤ p)
    have h1 : (p : ℝ) ^ (-(2 * σ)) ≤ (p : ℝ) ^ (-(2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
    have h2 : (p : ℝ) ^ (-(2 : ℝ)) = (1 : ℝ) / (p : ℝ) ^ 2 := by
      rw [Real.rpow_neg (by linarith : (0 : ℝ) ≤ p), Real.rpow_two, one_div]
    rw [h2] at h1
    exact h1
  have hsub : S ⊆ Finset.range (S.sup id + 1) := fun p hp =>
    Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := id) hp))
  have hlast : (∑ n ∈ Finset.range (S.sup id + 1), (1 : ℝ) / (n : ℝ) ^ 2) ≤ 2 := by
    rw [Finset.range_eq_Ico]
    rcases Nat.eq_zero_or_pos (S.sup id + 1) with h | h
    · rw [h]; norm_num
    · rw [Finset.sum_eq_sum_Ico_succ_bot h]
      have h0 : (1 : ℝ) / (((0 : ℕ)) : ℝ) ^ 2 = 0 := by norm_num
      rw [h0, zero_add, Finset.Ico_add_one_left_eq_Ioo]
      have hb := sum_Ioo_inv_sq_le (α := ℝ) 0 (S.sup id + 1)
      have hb' : (∑ i ∈ Finset.Ioo 0 (S.sup id + 1), (1 : ℝ) / (i : ℝ) ^ 2) ≤ 2 := by
        simpa [one_div, Nat.cast_zero, zero_add, div_one] using hb
      exact hb'
  calc (∑ p ∈ S, (p : ℝ) ^ (-(2 * σ)))
      ≤ ∑ p ∈ S, (1 : ℝ) / (p : ℝ) ^ 2 := Finset.sum_le_sum hterm
    _ ≤ ∑ n ∈ Finset.range (S.sup id + 1), (1 : ℝ) / (n : ℝ) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => by positivity)
    _ ≤ 2 := hlast

/-! ## The local Euler factor is `≤ exp (Re (f p · p^{-s}) + C p^{-2 Re s})` -/

theorem eulerFac_norm_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : ℕ → ℂ), f 1 = 1 → (∀ n : ℕ, ‖f n‖ ≤ 1) →
      ∀ (p : ℕ), p.Prime → ∀ s : ℂ, 1 < s.re →
        ‖eulerFac f p s‖ ≤
          Real.exp ((f p * (p : ℂ) ^ (-s)).re + C * (p : ℝ) ^ (-(2 * s.re))) := by
  refine ⟨8, by norm_num, ?_⟩
  intro f hf1 hb p hp s hs
  set q : ℂ := (p : ℂ) ^ (-s) with hq
  set w : ℂ := f p * q with hw
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hppos : (0 : ℝ) < (p : ℝ) := by linarith
  have hnormq : ‖q‖ = (p : ℝ) ^ (-s.re) := by
    rw [hq, Complex.norm_natCast_cpow_of_pos hp.pos, Complex.neg_re]
  have hqle : ‖q‖ ≤ 1 / 2 := by
    rw [hnormq]
    have h1 : (p : ℝ) ^ (-s.re) ≤ (p : ℝ) ^ (-(1 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    rw [Real.rpow_neg_one] at h1
    refine le_trans h1 ?_
    simpa [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hp2
  have hwle : ‖w‖ ≤ 1 / 2 := by
    rw [hw, norm_mul]
    calc ‖f p‖ * ‖q‖ ≤ 1 * (1 / 2) :=
          mul_le_mul (hb p) hqle (norm_nonneg _) (by norm_num)
      _ = 1 / 2 := by norm_num
  have hqlt : ‖q‖ < 1 := lt_of_le_of_lt hqle (by norm_num)
  have hwq : ‖w‖ ^ 2 ≤ ‖q‖ ^ 2 := by
    have h1 : ‖w‖ ≤ ‖q‖ := by
      rw [hw, norm_mul]
      calc ‖f p‖ * ‖q‖ ≤ 1 * ‖q‖ := mul_le_mul_of_nonneg_right (hb p) (norm_nonneg _)
        _ = ‖q‖ := one_mul _
    nlinarith [norm_nonneg w, norm_nonneg q]
  have hsumm : Summable (fun e : ℕ => f (p ^ e) * q ^ e) := by
    refine Summable.of_norm_bounded (g := fun e : ℕ => ‖q‖ ^ e)
      (summable_geometric_of_norm_lt_one (by simpa using hqlt)) (fun e => ?_)
    rw [norm_mul, norm_pow]
    exact mul_le_of_le_one_left (by positivity) (hb _)
  have hvsumm : Summable (fun e : ℕ => f (p ^ (e + 2)) * q ^ (e + 2)) :=
    (summable_nat_add_iff 2).mpr hsumm
  have hsplit : eulerFac f p s = (1 + w) + ∑' e : ℕ, f (p ^ (e + 2)) * q ^ (e + 2) := by
    have h1 : (∑' e : ℕ, f (p ^ e) * q ^ e)
        = (∑ e ∈ Finset.range 2, f (p ^ e) * q ^ e)
            + ∑' e : ℕ, f (p ^ (e + 2)) * q ^ (e + 2) :=
      (Summable.sum_add_tsum_nat_add 2 hsumm).symm
    rw [eulerFac, ← hq, h1]
    simp [Finset.sum_range_succ, hf1, hw]
  have hvle : ‖∑' e : ℕ, f (p ^ (e + 2)) * q ^ (e + 2)‖ ≤ 2 * ‖q‖ ^ 2 := by
    have hnn : Summable (fun e : ℕ => ‖f (p ^ (e + 2)) * q ^ (e + 2)‖) := hvsumm.norm
    have h1 : ‖∑' e : ℕ, f (p ^ (e + 2)) * q ^ (e + 2)‖
        ≤ ∑' e : ℕ, ‖f (p ^ (e + 2)) * q ^ (e + 2)‖ := norm_tsum_le_tsum_norm hnn
    have h2 : (∑' e : ℕ, ‖f (p ^ (e + 2)) * q ^ (e + 2)‖)
        ≤ ∑' e : ℕ, ‖q‖ ^ (e + 2) := by
      refine Summable.tsum_le_tsum (fun e => ?_) hnn ?_
      · rw [norm_mul, norm_pow]
        exact mul_le_of_le_one_left (by positivity) (hb _)
      · exact (summable_nat_add_iff 2).mpr
          (summable_geometric_of_norm_lt_one (by simpa using hqlt))
    have h3 : (∑' e : ℕ, ‖q‖ ^ (e + 2)) = ‖q‖ ^ 2 * (1 - ‖q‖)⁻¹ := by
      rw [show (fun e : ℕ => ‖q‖ ^ (e + 2)) = fun e : ℕ => ‖q‖ ^ 2 * ‖q‖ ^ e by
            funext e; rw [pow_add]; ring]
      rw [tsum_mul_left, tsum_geometric_of_norm_lt_one (by simpa using hqlt)]
    have h4 : ‖q‖ ^ 2 * (1 - ‖q‖)⁻¹ ≤ 2 * ‖q‖ ^ 2 := by
      have hpos : (0 : ℝ) < 1 - ‖q‖ := by linarith
      have hle : (1 - ‖q‖)⁻¹ ≤ 2 := by
        rw [inv_le_comm₀ hpos (by norm_num : (0 : ℝ) < 2)]
        linarith
      nlinarith [sq_nonneg ‖q‖]
    linarith
  have h1w : ‖1 + w‖ ≤ Real.exp (w.re + ‖w‖ ^ 2 / 2) := by
    have hsq : ‖1 + w‖ ^ 2 = 1 + 2 * w.re + ‖w‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.one_re,
        Complex.add_im, Complex.one_im, Complex.sq_norm, Complex.normSq_apply]
      ring
    have hwnn : -(1 / 2 : ℝ) ≤ w.re := by
      have h2 : |w.re| ≤ ‖w‖ := Complex.abs_re_le_norm w
      linarith [(abs_le.mp h2).1]
    have hnn : 0 ≤ 1 + w.re + ‖w‖ ^ 2 / 2 := by nlinarith [sq_nonneg ‖w‖]
    have hle : ‖1 + w‖ ≤ 1 + w.re + ‖w‖ ^ 2 / 2 := by
      rw [show ‖1 + w‖ = Real.sqrt (‖1 + w‖ ^ 2) from (Real.sqrt_sq (norm_nonneg _)).symm]
      calc Real.sqrt (‖1 + w‖ ^ 2) ≤ Real.sqrt ((1 + w.re + ‖w‖ ^ 2 / 2) ^ 2) := by
            refine Real.sqrt_le_sqrt ?_
            rw [hsq]
            nlinarith [sq_nonneg (w.re + ‖w‖ ^ 2 / 2)]
        _ = 1 + w.re + ‖w‖ ^ 2 / 2 := Real.sqrt_sq hnn
    have h := Real.add_one_le_exp (w.re + ‖w‖ ^ 2 / 2)
    linarith
  have hq2 : (p : ℝ) ^ (-(2 * s.re)) = ‖q‖ ^ 2 := by
    rw [hnormq, show -(2 * s.re) = -s.re + -s.re by ring, Real.rpow_add hppos]
    ring
  have hexpstep : Real.exp (w.re + ‖w‖ ^ 2 / 2) + 2 * ‖q‖ ^ 2
      ≤ Real.exp ((f p * (p : ℂ) ^ (-s)).re + 8 * (p : ℝ) ^ (-(2 * s.re))) := by
    have hexp : (1 / 2 : ℝ) ≤ Real.exp (w.re + ‖w‖ ^ 2 / 2) := by
      have h1 : -(1 / 2 : ℝ) ≤ w.re + ‖w‖ ^ 2 / 2 := by
        have h2 : -(1 / 2 : ℝ) ≤ w.re := by
          have h3 : |w.re| ≤ ‖w‖ := Complex.abs_re_le_norm w
          linarith [(abs_le.mp h3).1]
        nlinarith [sq_nonneg ‖w‖]
      calc (1 / 2 : ℝ) ≤ Real.exp (-(1 / 2)) := by
            have h3 := Real.one_sub_le_exp_neg (1 / 2)
            linarith
        _ ≤ Real.exp (w.re + ‖w‖ ^ 2 / 2) := Real.exp_le_exp.mpr h1
    have hstep : Real.exp (w.re + ‖w‖ ^ 2 / 2) + 2 * ‖q‖ ^ 2
        ≤ Real.exp (w.re + ‖w‖ ^ 2 / 2 + 4 * ‖q‖ ^ 2) := by
      have h2 : 2 * ‖q‖ ^ 2 ≤ 4 * ‖q‖ ^ 2 * Real.exp (w.re + ‖w‖ ^ 2 / 2) := by nlinarith
      have h3 : 1 + 4 * ‖q‖ ^ 2 ≤ Real.exp (4 * ‖q‖ ^ 2) := by
        have h := Real.add_one_le_exp (4 * ‖q‖ ^ 2); linarith
      calc Real.exp (w.re + ‖w‖ ^ 2 / 2) + 2 * ‖q‖ ^ 2
          ≤ Real.exp (w.re + ‖w‖ ^ 2 / 2)
              + 4 * ‖q‖ ^ 2 * Real.exp (w.re + ‖w‖ ^ 2 / 2) := by linarith
        _ = Real.exp (w.re + ‖w‖ ^ 2 / 2) * (1 + 4 * ‖q‖ ^ 2) := by ring
        _ ≤ Real.exp (w.re + ‖w‖ ^ 2 / 2) * Real.exp (4 * ‖q‖ ^ 2) :=
            mul_le_mul_of_nonneg_left h3 (Real.exp_pos _).le
        _ = Real.exp (w.re + ‖w‖ ^ 2 / 2 + 4 * ‖q‖ ^ 2) := (Real.exp_add _ _).symm
    have hfin : w.re + ‖w‖ ^ 2 / 2 + 4 * ‖q‖ ^ 2 ≤ w.re + 8 * (p : ℝ) ^ (-(2 * s.re)) := by
      rw [hq2]
      nlinarith [hwq, sq_nonneg ‖q‖]
    refine le_trans hstep (Real.exp_le_exp.mpr ?_)
    rw [hw, hq]
    exact hfin
  calc ‖eulerFac f p s‖ = ‖(1 + w) + ∑' e : ℕ, f (p ^ (e + 2)) * q ^ (e + 2)‖ := by
        rw [hsplit]
    _ ≤ ‖1 + w‖ + ‖∑' e : ℕ, f (p ^ (e + 2)) * q ^ (e + 2)‖ := norm_add_le _ _
    _ ≤ Real.exp (w.re + ‖w‖ ^ 2 / 2) + 2 * ‖q‖ ^ 2 := add_le_add h1w hvle
    _ ≤ Real.exp ((f p * (p : ℂ) ^ (-s)).re + 8 * (p : ℝ) ^ (-(2 * s.re))) := hexpstep

/-! ## The tail bound `Σ_{x < p} p^{-1-α} ≤ K` -/

theorem primeRpow_tail_le :
    ∃ K : ℝ, 0 < K ∧ ∀ (T : Finset ℕ) (α x : ℝ), (∀ p ∈ T, p.Prime) → 0 < α → 2 ≤ x →
      Real.exp (1 / α) ≤ x → (∀ p ∈ T, x < (p : ℝ)) →
        (∑ p ∈ T, (1 : ℝ) / (p : ℝ) ^ (1 + α)) ≤ K := by
  obtain ⟨K₀, hK₀pos, hK₀⟩ := halasz_mertens_aux.2.2
  refine ⟨K₀ + 2, by linarith, ?_⟩
  intro T α x hT hα hx2 hexp hxT
  have hx0 : (0 : ℝ) < x := by linarith
  have hlogx : 1 / α ≤ Real.log x := by
    have h1 := Real.log_le_log (Real.exp_pos (1 / α)) hexp
    rwa [Real.log_exp] at h1
  have hαl : 1 ≤ α * Real.log x := by
    have h1 : α * (1 / α) = 1 := by field_simp
    linarith [mul_le_mul_of_nonneg_left hlogx hα.le]
  by_cases hα1 : 1 ≤ α
  · have hterm : ∀ p ∈ T, (1 : ℝ) / (p : ℝ) ^ (1 + α) ≤ (p : ℝ) ^ (-(2 * (1 : ℝ))) := by
      intro p hp
      have hp2r : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (hT p hp).two_le
      have hppos : (0 : ℝ) < (p : ℝ) := by linarith
      rw [one_div, ← Real.rpow_neg (le_of_lt hppos)]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    have h2 := primes_rpow_sum_le T hT 1 le_rfl
    rw [mul_one] at h2
    linarith [Finset.sum_le_sum hterm]
  · push_neg at hα1
    have hsplit := Finset.sum_filter_add_sum_filter_not T (fun p : ℕ => (p : ℝ) ≤ 11)
      (fun p => (1 : ℝ) / (p : ℝ) ^ (1 + α))
    have hb1 : (∑ p ∈ T.filter (fun p : ℕ => (p : ℝ) ≤ 11), (1 : ℝ) / (p : ℝ) ^ (1 + α)) ≤ 2 := by
      have hterm : ∀ p ∈ T.filter (fun p : ℕ => (p : ℝ) ≤ 11),
          (1 : ℝ) / (p : ℝ) ^ (1 + α) ≤ (1 : ℝ) / (p : ℝ) := by
        intro p hp
        have hpT : p ∈ T := (Finset.mem_filter.mp hp).1
        have hp2r : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (hT p hpT).two_le
        have hppos : (0 : ℝ) < (p : ℝ) := by linarith
        have hp1 : (1 : ℝ) ≤ (p : ℝ) := by linarith
        have h1 : (p : ℝ) ≤ (p : ℝ) ^ (1 + α) := by
          have h2 := Real.rpow_le_rpow_of_exponent_le hp1 (by linarith : (1 : ℝ) ≤ 1 + α)
          rwa [Real.rpow_one] at h2
        exact one_div_le_one_div_of_le hppos h1
      have hsub : T.filter (fun p : ℕ => (p : ℝ) ≤ 11) ⊆ Finset.Icc 3 11 := by
        intro p hp
        obtain ⟨hpT, hp11⟩ := Finset.mem_filter.mp hp
        have hp2r : (2 : ℝ) < (p : ℝ) := lt_of_le_of_lt hx2 (hxT p hpT)
        have hp2 : 2 < p := by exact_mod_cast hp2r
        exact Finset.mem_Icc.mpr ⟨by omega, by exact_mod_cast hp11⟩
      calc (∑ p ∈ T.filter (fun p : ℕ => (p : ℝ) ≤ 11), (1 : ℝ) / (p : ℝ) ^ (1 + α))
          ≤ ∑ p ∈ T.filter (fun p : ℕ => (p : ℝ) ≤ 11), (1 : ℝ) / (p : ℝ) :=
            Finset.sum_le_sum hterm
        _ ≤ ∑ n ∈ Finset.Icc (3 : ℕ) 11, (1 : ℝ) / (n : ℝ) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => by positivity)
        _ ≤ 2 := by norm_num [Finset.sum_Icc_succ_top]
    have hb2 : (∑ p ∈ T.filter (fun p : ℕ => ¬ (p : ℝ) ≤ 11), (1 : ℝ) / (p : ℝ) ^ (1 + α))
        ≤ K₀ := by
      have hTeq : T.filter (fun p : ℕ => ¬ (p : ℝ) ≤ 11)
          = T.filter (fun p : ℕ => 11 < (p : ℝ)) := Finset.filter_congr (fun p _ => not_le)
      rw [hTeq]
      have hsub : T.filter (fun p : ℕ => 11 < (p : ℝ)) ⊆
          ((⌊((max 11 (T.sup id) : ℕ) : ℝ)⌋₊).primesLE).filter
            (fun p : ℕ => max x 11 < (p : ℝ)) := by
        intro p hp
        obtain ⟨hpT, hp11⟩ := Finset.mem_filter.mp hp
        rw [Finset.mem_filter, Nat.mem_primesLE]
        refine ⟨⟨?_, hT p hpT⟩, ?_⟩
        · rw [Nat.floor_natCast]
          exact le_trans (Finset.le_sup (f := id) hpT) (le_max_right _ _)
        · exact max_lt_iff.mpr ⟨hxT p hpT, hp11⟩
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => by positivity)) ?_
      refine hK₀ α (max x 11) ((max 11 (T.sup id) : ℕ) : ℝ) hα (le_of_lt hα1)
        (by rw [lt_max_iff]; exact Or.inr (by norm_num)) ?_ ?_
      · exact_mod_cast (le_max_left (11 : ℕ) (T.sup id))
      · have h1 : Real.log x ≤ Real.log (max x 11) := Real.log_le_log hx0 (le_max_left _ _)
        nlinarith [mul_le_mul_of_nonneg_left h1 hα.le]
    rw [← hsplit]
    linarith

/-! ## The Euler product as a limit of finite products -/

theorem eulerProduct_tendsto :
    ∀ (f : ℕ → ℂ), f 1 = 1 → (∀ m n : ℕ, m.Coprime n → f (m * n) = f m * f n) →
      (∀ n : ℕ, ‖f n‖ ≤ 1) → ∀ s : ℂ, 1 < s.re →
        Filter.Tendsto (fun N : ℕ => ∏ p ∈ N.primesBelow, eulerFac f p s)
          Filter.atTop (𝓝 (LSeries f s)) := by
  intro f hf1 hmul hb s hs
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    exact absurd hs (by norm_num)
  have hbound : ∀ n : ℕ, ‖LSeries.term f s n‖ ≤ (n : ℝ) ^ (-s.re) := by
    intro n
    rw [LSeries.norm_term_eq]
    rcases eq_or_ne n 0 with rfl | hn
    · rw [if_pos rfl]
      exact Real.rpow_nonneg (Nat.cast_nonneg (0 : ℕ)) _
    · rw [if_neg hn]
      have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
      calc ‖f n‖ / (n : ℝ) ^ s.re ≤ 1 / (n : ℝ) ^ s.re :=
            div_le_div_of_nonneg_right (hb n) (Real.rpow_nonneg hnpos.le _)
        _ = (n : ℝ) ^ (-s.re) := by rw [one_div, ← Real.rpow_neg hnpos.le]
  have hgs : Summable (fun n : ℕ => (n : ℝ) ^ (-s.re)) := by
    rw [show (fun n : ℕ => (n : ℝ) ^ (-s.re)) = fun n : ℕ => (((n : ℝ) ^ s.re))⁻¹ by
      funext n; rw [Real.rpow_neg (Nat.cast_nonneg n)]]
    exact (Real.summable_nat_rpow_inv).mpr hs
  have hsumm : Summable (fun n : ℕ => ‖LSeries.term f s n‖) :=
    (Summable.of_norm_bounded (g := fun n : ℕ => (n : ℝ) ^ (-s.re)) hgs hbound).norm
  have hg1 : LSeries.term f s 1 = 1 := by
    rw [LSeries.term_of_ne_zero (by norm_num : (1 : ℕ) ≠ 0)]
    simp [hf1]
  have hgmul : ∀ {m n : ℕ}, m.Coprime n →
      LSeries.term f s (m * n) = LSeries.term f s m * LSeries.term f s n := by
    intro m n hmn
    by_cases hm : m = 0
    · subst hm
      have hn : n = 1 := (Nat.coprime_zero_left n).mp hmn
      subst hn
      simp [LSeries.term_zero]
    by_cases hn : n = 0
    · subst hn
      have hm' : m = 1 := (Nat.coprime_zero_left m).mp hmn.symm
      subst hm'
      simp [LSeries.term_zero]
    · rw [LSeries.term_of_ne_zero (Nat.mul_ne_zero hm hn),
        LSeries.term_of_ne_zero hm, LSeries.term_of_ne_zero hn, hmul m n hmn,
        Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
      rw [div_mul_div_comm]
  have hmain := EulerProduct.eulerProduct (f := fun n : ℕ => LSeries.term f s n)
    hg1 hgmul hsumm (LSeries.term_zero f s)
  have hfac : ∀ p : ℕ, p.Prime → (∑' e : ℕ, LSeries.term f s (p ^ e)) = eulerFac f p s := by
    intro p hp
    have hfe : ∀ e : ℕ, LSeries.term f s (p ^ e) = f (p ^ e) * ((p : ℂ) ^ (-s)) ^ e := by
      intro e
      rw [LSeries.term_of_ne_zero' hs0, div_eq_mul_inv, ← cpow_neg, Nat.cast_pow,
        ← Complex.natCast_cpow_natCast_mul p e (-s), Complex.cpow_nat_mul]
    rw [tsum_congr hfe]
    rfl
  have hprod : ∀ N : ℕ, (∏ p ∈ N.primesBelow, ∑' e : ℕ, LSeries.term f s (p ^ e))
      = ∏ p ∈ N.primesBelow, eulerFac f p s := fun N =>
    Finset.prod_congr rfl (fun p hp => hfac p (Nat.mem_primesBelow.mp hp).2)
  rw [show (fun N : ℕ => ∏ p ∈ N.primesBelow, eulerFac f p s)
      = fun N : ℕ => ∏ p ∈ N.primesBelow, ∑' e : ℕ, LSeries.term f s (p ^ e) from
    (funext hprod).symm]
  exact hmain

/-! ## `Re vF f x s ≤ Wsup f x α (T+1)` -/

theorem vF_re_le_Wsup (f : ℕ → ℂ) (hb : ∀ n, ‖f n‖ ≤ 1) (x α T : ℝ) (hα : 0 ≤ α)
    (s : ℂ) (hsre : s.re = 1 + α) (hsim : |s.im| ≤ T + 1) :
    (vF f x s).re ≤ Wsup f x α (T + 1) := by
  have hbdd : BddAbove (Set.range (fun t : {t : ℝ // |t| ≤ T + 1} =>
      (vF f x ((1 + α : ℝ) + t.1 * Complex.I)).re)) := by
    refine ⟨∑ p ∈ (⌊x⌋₊).primesLE, (p : ℝ) ^ (-(1 + α)), ?_⟩
    rintro y ⟨t, rfl⟩
    change (vF f x ((1 + α : ℝ) + t.1 * Complex.I)).re
      ≤ ∑ p ∈ (⌊x⌋₊).primesLE, (p : ℝ) ^ (-(1 + α))
    have hL : (vF f x ((1 + α : ℝ) + t.1 * Complex.I)).re
        = ∑ p ∈ (⌊x⌋₊).primesLE,
            (f p * (p : ℂ) ^ (-((1 + α : ℝ) + t.1 * Complex.I))).re := by
      unfold vF
      exact map_sum Complex.reAddGroupHom _ _
    rw [hL]
    refine Finset.sum_le_sum (fun p hp => ?_)
    have hp2r : (2 : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast (Nat.prime_of_mem_primesLE hp).two_le
    have hppos : (0 : ℝ) < (p : ℝ) := by linarith
    have hnorm : ‖(p : ℂ) ^ (-((1 + α : ℝ) + t.1 * Complex.I))‖ ≤ (p : ℝ) ^ (-(1 + α)) := by
      have h2 : ‖(p : ℂ) ^ (-((1 + α : ℝ) + t.1 * Complex.I))‖
          = (p : ℝ) ^ ((-((1 + α : ℝ) + t.1 * Complex.I)).re) :=
        Complex.norm_natCast_cpow_of_pos (Nat.prime_of_mem_primesLE hp).pos _
      have h1 : (-((1 + α : ℝ) + t.1 * Complex.I)).re = -(1 + α) := by simp
      rw [h1] at h2
      exact le_of_eq h2
    calc (f p * (p : ℂ) ^ (-((1 + α : ℝ) + t.1 * Complex.I))).re
        ≤ ‖f p * (p : ℂ) ^ (-((1 + α : ℝ) + t.1 * Complex.I))‖ := Complex.re_le_norm _
      _ = ‖f p‖ * ‖(p : ℂ) ^ (-((1 + α : ℝ) + t.1 * Complex.I))‖ := norm_mul _ _
      _ ≤ 1 * (p : ℝ) ^ (-(1 + α)) :=
          mul_le_mul (hb p) hnorm (norm_nonneg _) (by norm_num)
      _ = (p : ℝ) ^ (-(1 + α)) := one_mul _
  have hs_eq : s = ((1 + α : ℝ) : ℂ) + (s.im : ℂ) * Complex.I := by
    have h := Complex.re_add_im s
    rw [hsre] at h
    exact h.symm
  rw [hs_eq]
  unfold Wsup
  exact le_ciSup hbdd ⟨s.im, hsim⟩

/-! ## The main bound -/

theorem LSeries_norm_le_exp_Wsup :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : ℕ → ℂ), f 1 = 1 →
      (∀ m n : ℕ, m.Coprime n → f (m * n) = f m * f n) → (∀ n, ‖f n‖ ≤ 1) →
      ∀ x α T : ℝ, 2 ≤ x → 0 < α → Real.exp (1 / α) ≤ x →
        ∀ {s : ℂ}, s.re = 1 + α → |s.im| ≤ T + 1 →
          ‖LSeries f s‖ ≤ C * Real.exp (Work.BMF.Wsup f x α (T + 1)) := by
  obtain ⟨C₂, hC₂pos, hC₂⟩ := eulerFac_norm_le
  obtain ⟨K, hKpos, hK⟩ := primeRpow_tail_le
  refine ⟨Real.exp (K + 4 * C₂), Real.exp_pos _, ?_⟩
  intro f hf1 hmul hb x α T hx2 hα hexp s hsre hsim
  have hs1 : 1 < s.re := by rw [hsre]; linarith
  have hx0 : (0 : ℝ) < x := by linarith
  have hKnn : 0 ≤ K := le_of_lt hKpos
  have hC₂nn : 0 ≤ C₂ := le_of_lt hC₂pos
  have key : ∀ N : ℕ, ⌊x⌋₊ + 1 ≤ N →
      ‖∏ p ∈ N.primesBelow, eulerFac f p s‖ ≤ Real.exp ((vF f x s).re + (K + 4 * C₂)) := by
    intro N hN
    have hpb : ∀ p ∈ N.primesBelow, p.Prime := fun p hp => (Nat.mem_primesBelow.mp hp).2
    have h1 : ‖∏ p ∈ N.primesBelow, eulerFac f p s‖
        ≤ ∏ p ∈ N.primesBelow, ‖eulerFac f p s‖ := Finset.norm_prod_le _ _
    have h2 : ∏ p ∈ N.primesBelow, ‖eulerFac f p s‖
        ≤ ∏ p ∈ N.primesBelow,
            Real.exp ((f p * (p : ℂ) ^ (-s)).re + C₂ * (p : ℝ) ^ (-(2 * s.re))) :=
      Finset.prod_le_prod₀ (fun p _ => norm_nonneg _)
        (fun p hp => hC₂ f hf1 hb p (hpb p hp) s hs1)
    have h3 : ∏ p ∈ N.primesBelow,
          Real.exp ((f p * (p : ℂ) ^ (-s)).re + C₂ * (p : ℝ) ^ (-(2 * s.re)))
        = Real.exp (∑ p ∈ N.primesBelow,
            ((f p * (p : ℂ) ^ (-s)).re + C₂ * (p : ℝ) ^ (-(2 * s.re)))) :=
      (Real.exp_sum _ _).symm
    have hlow : (∑ p ∈ N.primesBelow.filter (fun p : ℕ => (p : ℝ) ≤ x),
          ((f p * (p : ℂ) ^ (-s)).re + C₂ * (p : ℝ) ^ (-(2 * s.re))))
        ≤ (vF f x s).re + C₂ * 2 := by
      rw [Finset.sum_add_distrib]
      have hS : N.primesBelow.filter (fun p : ℕ => (p : ℝ) ≤ x) = (⌊x⌋₊).primesLE :=
        primesBelow_filter_le_eq x (le_of_lt hx0) hN
      have hA : (∑ p ∈ N.primesBelow.filter (fun p : ℕ => (p : ℝ) ≤ x),
            (f p * (p : ℂ) ^ (-s)).re) = (vF f x s).re := by
        rw [hS, vF]
        exact (map_sum Complex.reAddGroupHom (fun p => f p * (p : ℂ) ^ (-s)) (⌊x⌋₊).primesLE).symm
      have hB : (∑ p ∈ N.primesBelow.filter (fun p : ℕ => (p : ℝ) ≤ x),
            C₂ * (p : ℝ) ^ (-(2 * s.re))) ≤ C₂ * 2 := by
        rw [← Finset.mul_sum]
        refine mul_le_mul_of_nonneg_left ?_ hC₂nn
        rw [hS]
        exact primes_rpow_sum_le _ (fun p hp => (Nat.mem_primesLE.mp hp).2) s.re (le_of_lt hs1)
      linarith
    have hhigh : (∑ p ∈ N.primesBelow.filter (fun p : ℕ => ¬ (p : ℝ) ≤ x),
          ((f p * (p : ℂ) ^ (-s)).re + C₂ * (p : ℝ) ^ (-(2 * s.re))))
        ≤ K + C₂ * 2 := by
      rw [Finset.sum_add_distrib]
      have hA : (∑ p ∈ N.primesBelow.filter (fun p : ℕ => ¬ (p : ℝ) ≤ x),
            (f p * (p : ℂ) ^ (-s)).re) ≤ K := by
        have hTeq : N.primesBelow.filter (fun p : ℕ => ¬ (p : ℝ) ≤ x)
            = N.primesBelow.filter (fun p : ℕ => x < (p : ℝ)) :=
          Finset.filter_congr (fun p _ => not_le)
        rw [hTeq]
        have hle : ∀ p ∈ N.primesBelow.filter (fun p : ℕ => x < (p : ℝ)),
            (f p * (p : ℂ) ^ (-s)).re ≤ (1 : ℝ) / (p : ℝ) ^ (1 + α) := by
          intro p hp
          obtain ⟨hpN, _⟩ := Finset.mem_filter.mp hp
          have hpp : p.Prime := hpb p hpN
          have hp2r : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
          have hppos : (0 : ℝ) < (p : ℝ) := by linarith
          have hnorm : ‖(p : ℂ) ^ (-s)‖ ≤ (p : ℝ) ^ (-(1 + α)) := by
            rw [Complex.norm_natCast_cpow_of_pos hpp.pos, Complex.neg_re, hsre]
          calc (f p * (p : ℂ) ^ (-s)).re ≤ ‖f p * (p : ℂ) ^ (-s)‖ := Complex.re_le_norm _
            _ = ‖f p‖ * ‖(p : ℂ) ^ (-s)‖ := norm_mul _ _
            _ ≤ 1 * (p : ℝ) ^ (-(1 + α)) :=
                mul_le_mul (hb p) hnorm (norm_nonneg _) (by norm_num)
            _ = (1 : ℝ) / (p : ℝ) ^ (1 + α) := by
                rw [Real.rpow_neg hppos.le, one_div, one_mul]
        refine le_trans (Finset.sum_le_sum hle) ?_
        exact hK (N.primesBelow.filter (fun p : ℕ => x < (p : ℝ))) α x
          (fun p hp => hpb p (Finset.mem_filter.mp hp).1) hα hx2 hexp
          (fun p hp => (Finset.mem_filter.mp hp).2)
      have hB : (∑ p ∈ N.primesBelow.filter (fun p : ℕ => ¬ (p : ℝ) ≤ x),
            C₂ * (p : ℝ) ^ (-(2 * s.re))) ≤ C₂ * 2 := by
        rw [← Finset.mul_sum]
        refine mul_le_mul_of_nonneg_left ?_ hC₂nn
        exact primes_rpow_sum_le _ (fun p hp => hpb p (Finset.mem_filter.mp hp).1)
          s.re (le_of_lt hs1)
      linarith
    have hsplit := Finset.sum_filter_add_sum_filter_not (N.primesBelow) (fun p : ℕ => (p : ℝ) ≤ x)
      (fun p => ((f p * (p : ℂ) ^ (-s)).re + C₂ * (p : ℝ) ^ (-(2 * s.re))))
    have h4 : (∑ p ∈ N.primesBelow,
          ((f p * (p : ℂ) ^ (-s)).re + C₂ * (p : ℝ) ^ (-(2 * s.re))))
        ≤ (vF f x s).re + (K + 4 * C₂) := by
      rw [← hsplit]
      linarith
    calc ‖∏ p ∈ N.primesBelow, eulerFac f p s‖
        ≤ ∏ p ∈ N.primesBelow, ‖eulerFac f p s‖ := h1
      _ ≤ ∏ p ∈ N.primesBelow,
            Real.exp ((f p * (p : ℂ) ^ (-s)).re + C₂ * (p : ℝ) ^ (-(2 * s.re))) := h2
      _ = Real.exp (∑ p ∈ N.primesBelow,
            ((f p * (p : ℂ) ^ (-s)).re + C₂ * (p : ℝ) ^ (-(2 * s.re)))) := h3
      _ ≤ Real.exp ((vF f x s).re + (K + 4 * C₂)) := Real.exp_le_exp.mpr h4
  have htend := eulerProduct_tendsto f hf1 hmul hb s hs1
  have hlim : ‖LSeries f s‖ ≤ Real.exp ((vF f x s).re + (K + 4 * C₂)) :=
    le_of_tendsto (Filter.Tendsto.norm htend)
      (Filter.eventually_atTop.mpr ⟨⌊x⌋₊ + 1, fun N hN => key N hN⟩)
  calc ‖LSeries f s‖ ≤ Real.exp ((vF f x s).re + (K + 4 * C₂)) := hlim
    _ = Real.exp (K + 4 * C₂) * Real.exp ((vF f x s).re) := by
        rw [← Real.exp_add]; ring_nf
    _ ≤ Real.exp (K + 4 * C₂) * Real.exp (Wsup f x α (T + 1)) :=
        mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (vF_re_le_Wsup f hb x α T (le_of_lt hα) s hsre hsim))
          (Real.exp_pos _).le

end Work.BMF
