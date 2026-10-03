import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.chi4_sum_div_tendsto_pi_div_four
import Submission.Commons.NumberTheory.FriedlanderIwaniec.chi4_prime_recip_converges
import Submission.Commons.Analysis.DirichletSeries.abel_tendsto_tsum_mul_rpow_conditional

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped BigOperators
open Filter Finset

namespace Commons.NumberTheory.FriedlanderIwaniec

noncomputable section

/-- `χ₄` evaluated at a natural number, as a real number. -/
private def c4 (n : ℕ) : ℝ := ((ZMod.χ₄ (n : ZMod 4) : ℤ) : ℝ)

private lemma c4_int (n : ℕ) :
    c4 n = if n % 2 = 0 then 0 else if n % 4 = 1 then 1 else -1 := by
  unfold c4
  rw [ZMod.χ₄_nat_eq_if_mod_four]
  split_ifs <;> norm_num

private lemma c4_val (n : ℕ) : c4 n = 0 ∨ c4 n = 1 ∨ c4 n = -1 := by
  rw [c4_int]
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

private lemma abs_c4_le_one (n : ℕ) : |c4 n| ≤ 1 := by
  rcases c4_val n with h | h | h <;> rw [h] <;> norm_num

private lemma c4_mul (m n : ℕ) : c4 (m * n) = c4 m * c4 n := by
  unfold c4
  rw [Nat.cast_mul, map_mul]
  push_cast
  ring

private lemma c4_zero_mod_two {n : ℕ} (h : n % 2 = 0) : c4 n = 0 := by
  rw [c4_int, if_pos h]

private lemma c4_one_mod_four {n : ℕ} (h : n % 4 = 1) : c4 n = 1 := by
  rw [c4_int, if_neg (by omega), if_pos h]

private lemma c4_three_mod_four {n : ℕ} (h : n % 4 = 3) : c4 n = -1 := by
  rw [c4_int, if_neg (by omega), if_neg (by omega)]

/-- The completely multiplicative function `n ↦ χ₄(n)·n^{-σ}` as a monoid-with-zero
homomorphism `ℕ → ℝ`. -/
private def fpl (σ : ℝ) : ℕ →*₀ ℝ where
  toFun n := c4 n * (n : ℝ) ^ (-σ)
  map_zero' := by
    have h0 : c4 0 = 0 := by rw [c4_int]; norm_num
    rw [h0, zero_mul]
  map_one' := by simp [c4]
  map_mul' m n := by
    rw [c4_mul, Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)]
    ring

private lemma fpl_apply (σ : ℝ) (n : ℕ) : fpl σ n = c4 n * (n : ℝ) ^ (-σ) := rfl

private lemma norm_fpl_le (σ : ℝ) (n : ℕ) : ‖fpl σ n‖ ≤ (n : ℝ) ^ (-σ) := by
  rw [fpl_apply, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
  exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg n) _) (abs_c4_le_one n)

private lemma summable_norm_fpl {σ : ℝ} (hσ : 1 < σ) : Summable (fun n : ℕ => ‖fpl σ n‖) := by
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => norm_fpl_le σ n) ?_
  exact Real.summable_nat_rpow.mpr (by linarith : -σ < -1)

/-- The Dirichlet series of `χ₄` at real `σ`: `∑ χ₄(n)·n^{-σ}`. -/
private def Ell (σ : ℝ) : ℝ := ∑' n : ℕ, fpl σ n

/-- The `p`-th summand of the logarithm of the Euler product of `χ₄`, extended by `0` on
non-primes. -/
private def Gterm (σ : ℝ) (p : ℕ) : ℝ :=
  if p.Prime then -Real.log (1 - c4 p * (p : ℝ) ^ (-σ)) else 0

/-- `-log` of the truncated Euler product, as a series over the primes. -/
private def G (σ : ℝ) : ℝ := ∑' p : ℕ, Gterm σ p

private lemma rpow_neg_le_half {σ : ℝ} (hσ : 1 ≤ σ) {p : ℕ} (hp : 2 ≤ p) :
    (p : ℝ) ^ (-σ) ≤ 1 / 2 := by
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (by omega : 1 ≤ p)
  have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  calc (p : ℝ) ^ (-σ) ≤ (p : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
    _ = (p : ℝ)⁻¹ := by rw [Real.rpow_neg_one]
    _ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) h2
    _ = 1 / 2 := by norm_num

private lemma abs_c4_mul_rpow_le {σ : ℝ} (hσ : 1 ≤ σ) {p : ℕ} (hp : p.Prime) :
    |c4 p * (p : ℝ) ^ (-σ)| ≤ 1 / 2 := by
  rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p) _)]
  calc |c4 p| * (p : ℝ) ^ (-σ) ≤ 1 * (1 / 2) :=
        mul_le_mul (abs_c4_le_one p) (rpow_neg_le_half hσ hp.two_le) (by positivity) (by norm_num)
    _ = 1 / 2 := by norm_num

private lemma one_sub_c4_pos {σ : ℝ} (hσ : 1 ≤ σ) {p : ℕ} (hp : p.Prime) :
    0 < 1 - c4 p * (p : ℝ) ^ (-σ) := by
  have h := abs_c4_mul_rpow_le hσ hp
  rw [abs_le] at h
  linarith [h.2]

private lemma abs_log_one_sub_le {x : ℝ} (hx : |x| ≤ 1 / 2) :
    |Real.log (1 - x)| ≤ 2 * |x| := by
  obtain ⟨hxl, hxu⟩ := abs_le.mp hx
  have h1 : 0 < 1 - x := by linarith
  rcases lt_or_ge x 0 with hx0 | hx0
  · have h1ge : 1 ≤ 1 - x := by linarith
    rw [abs_of_nonneg (Real.log_nonneg h1ge), abs_of_neg hx0]
    have hlog : Real.log (1 - x) ≤ (1 - x) - 1 := Real.log_le_sub_one_of_pos h1
    linarith
  · have h1le : 1 - x ≤ 1 := by linarith
    have hlog0 : Real.log (1 - x) ≤ 0 := Real.log_nonpos (le_of_lt h1) h1le
    rw [abs_of_nonpos hlog0, abs_of_nonneg hx0, ← Real.log_inv]
    calc Real.log ((1 - x)⁻¹) ≤ (1 - x)⁻¹ - 1 := Real.log_le_sub_one_of_pos (by positivity)
      _ = x / (1 - x) := by field_simp; ring
      _ ≤ 2 * x := by
          rw [div_le_iff₀ h1]; nlinarith

private lemma abs_Gterm_le {σ : ℝ} (hσ : 1 < σ) (p : ℕ) :
    |Gterm σ p| ≤ 2 * (p : ℝ) ^ (-σ) := by
  unfold Gterm
  split_ifs with hp
  · rw [abs_neg]
    have hb := abs_log_one_sub_le (abs_c4_mul_rpow_le (le_of_lt hσ) hp)
    have h2 : (2 : ℝ) * |c4 p * (p : ℝ) ^ (-σ)| ≤ 2 * (p : ℝ) ^ (-σ) := by
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p) _)]
      exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg p) _) (abs_c4_le_one p)
    linarith
  · rw [abs_zero]; positivity

private lemma summable_Gterm {σ : ℝ} (hσ : 1 < σ) : Summable (Gterm σ) := by
  refine Summable.of_norm_bounded ?_ (fun p => abs_Gterm_le hσ p)
  exact (Real.summable_nat_rpow.mpr (by linarith : -σ < -1)).mul_left 2

private lemma primesBelow_eq (N : ℕ) : Nat.primesBelow N = (range N).filter Nat.Prime := by
  ext p; simp [Nat.mem_primesBelow, Finset.mem_filter, Finset.mem_range]

private lemma prod_eq_exp_sum (σ : ℝ) (hσ : 1 ≤ σ) (N : ℕ) :
    (∏ p ∈ Nat.primesBelow N, (1 - fpl σ p)⁻¹) = Real.exp (∑ p ∈ Nat.primesBelow N, Gterm σ p) := by
  rw [Real.exp_sum]
  refine Finset.prod_congr rfl fun p hp => ?_
  have hpp : p.Prime := (Nat.mem_primesBelow.mp hp).2
  have hpos : 0 < 1 - fpl σ p := by
    rw [fpl_apply]; exact one_sub_c4_pos hσ hpp
  simp only [Gterm, if_pos hpp]
  rw [Real.exp_neg, Real.exp_log (one_sub_c4_pos hσ hpp), fpl_apply]

private lemma tendsto_partial_Gterm {σ : ℝ} (hσ : 1 < σ) :
    Tendsto (fun N : ℕ => ∑ p ∈ Nat.primesBelow N, Gterm σ p) atTop (nhds (G σ)) := by
  have h := (summable_Gterm hσ).hasSum.tendsto_sum_nat
  refine h.congr fun N => ?_
  rw [primesBelow_eq, Finset.sum_filter]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases hp : p.Prime <;> simp [Gterm, hp]

private lemma euler_prod_log {σ : ℝ} (hσ : 1 < σ) : Ell σ = Real.exp (G σ) := by
  have hprod : Tendsto (fun N : ℕ => ∏ p ∈ Nat.primesBelow N, (1 - fpl σ p)⁻¹) atTop
      (nhds (Ell σ)) := by
    have := EulerProduct.eulerProduct_completely_multiplicative (f := fpl σ)
      (summable_norm_fpl hσ)
    simpa [Ell, fpl_apply] using this
  have hsum := tendsto_partial_Gterm hσ
  have hexp : Tendsto (fun N : ℕ => Real.exp (∑ p ∈ Nat.primesBelow N, Gterm σ p)) atTop
      (nhds (Real.exp (G σ))) := Real.continuous_exp.tendsto _ |>.comp hsum
  have heq : (fun N : ℕ => ∏ p ∈ Nat.primesBelow N, (1 - fpl σ p)⁻¹)
      = fun N : ℕ => Real.exp (∑ p ∈ Nat.primesBelow N, Gterm σ p) :=
    funext fun N => prod_eq_exp_sum σ (le_of_lt hσ) N
  rw [heq] at hprod
  exact tendsto_nhds_unique hprod hexp

private lemma G_eq_log_Ell {σ : ℝ} (hσ : 1 < σ) : G σ = Real.log (Ell σ) := by
  rw [euler_prod_log hσ, Real.log_exp]


/-! ### Decomposition of the logarithm of the Euler product -/

/-- The linear part `χ₄(p)·p^{-σ}` of `Gterm`, extended by `0` on non-primes. -/
private def Pterm (σ : ℝ) (p : ℕ) : ℝ := if p.Prime then c4 p * (p : ℝ) ^ (-σ) else 0

/-- The remainder `Gterm - Pterm`, extended by `0` on non-primes. -/
private def Bterm (σ : ℝ) (p : ℕ) : ℝ :=
  if p.Prime then -(Real.log (1 - c4 p * (p : ℝ) ^ (-σ)) + c4 p * (p : ℝ) ^ (-σ)) else 0

private lemma Gterm_eq (σ : ℝ) (p : ℕ) : Gterm σ p = Pterm σ p + Bterm σ p := by
  by_cases hp : p.Prime
  · unfold Gterm Pterm Bterm
    rw [if_pos hp, if_pos hp, if_pos hp]; ring
  · unfold Gterm Pterm Bterm
    rw [if_neg hp, if_neg hp, if_neg hp]; ring

private lemma Bterm_of_prime {p : ℕ} (hp : p.Prime) (σ : ℝ) :
    Bterm σ p = -(Real.log (1 - c4 p * (p : ℝ) ^ (-σ)) + c4 p * (p : ℝ) ^ (-σ)) := by
  unfold Bterm; rw [if_pos hp]

private lemma Pterm_one_eq (p : ℕ) :
    Pterm 1 p = (if p.Prime then c4 p / (p : ℝ) else 0) := by
  unfold Pterm
  split_ifs with hp
  · rw [Real.rpow_neg_one, div_eq_mul_inv]
  · rfl

private lemma summable_Pterm {σ : ℝ} (hσ : 1 < σ) : Summable (Pterm σ) := by
  refine Summable.of_norm_bounded (f := Pterm σ) (g := fun p : ℕ => (p : ℝ) ^ (-σ)) ?_ ?_
  · exact Real.summable_nat_rpow.mpr (by linarith : -σ < -1)
  · intro p
    unfold Pterm
    split_ifs with hp
    · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p) _)]
      exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg p) _) (abs_c4_le_one p)
    · rw [norm_zero]; exact Real.rpow_nonneg (Nat.cast_nonneg p) _

private lemma abs_log_one_sub_add_le {x : ℝ} (hx : |x| ≤ 1 / 2) :
    |Real.log (1 - x) + x| ≤ 2 * x ^ 2 := by
  have hx1 : |x| < 1 := by linarith
  have h := Real.abs_log_sub_add_sum_range_le hx1 1
  simp only [Finset.sum_range_one, Nat.cast_zero, zero_add, pow_one, div_one] at h
  have h2 : |x| ^ 2 / (1 - |x|) ≤ 2 * x ^ 2 := by
    rw [sq_abs, div_le_iff₀ (by linarith : (0 : ℝ) < 1 - |x|)]
    nlinarith [abs_le.mp hx, abs_nonneg x]
  rw [add_comm] at h
  exact le_trans h h2

private lemma sq_c4_rpow_le {σ : ℝ} (hσ : 1 ≤ σ) {p : ℕ} (hp : p.Prime) :
    (c4 p * (p : ℝ) ^ (-σ)) ^ 2 ≤ (p : ℝ) ^ (-2 : ℝ) := by
  rw [mul_pow]
  have h1 : (c4 p) ^ 2 ≤ 1 := by
    rcases c4_val p with h | h | h <;> rw [h] <;> norm_num
  have h2 : ((p : ℝ) ^ (-σ)) ^ 2 ≤ (p : ℝ) ^ (-2 : ℝ) := by
    rw [← Real.rpow_natCast ((p : ℝ) ^ (-σ)) 2, ← Real.rpow_mul (Nat.cast_nonneg p)]
    refine Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hp.one_le) ?_
    push_cast; linarith
  calc (c4 p) ^ 2 * ((p : ℝ) ^ (-σ)) ^ 2 ≤ 1 * (p : ℝ) ^ (-2 : ℝ) :=
        mul_le_mul h1 h2 (by positivity) (by norm_num)
    _ = (p : ℝ) ^ (-2 : ℝ) := by rw [one_mul]

private lemma abs_Bterm_le {σ : ℝ} (hσ : 1 ≤ σ) (p : ℕ) :
    |Bterm σ p| ≤ 2 * (p : ℝ) ^ (-2 : ℝ) := by
  by_cases hp : p.Prime
  · rw [Bterm_of_prime hp, abs_neg]
    have hb := abs_log_one_sub_add_le (abs_c4_mul_rpow_le hσ hp)
    calc |Real.log (1 - c4 p * (p : ℝ) ^ (-σ)) + c4 p * (p : ℝ) ^ (-σ)|
        ≤ 2 * (c4 p * (p : ℝ) ^ (-σ)) ^ 2 := hb
      _ ≤ 2 * (p : ℝ) ^ (-2 : ℝ) := by
          have := sq_c4_rpow_le hσ hp; linarith
  · unfold Bterm; rw [if_neg hp, abs_zero]; positivity

private lemma summable_Bterm {σ : ℝ} (hσ : 1 ≤ σ) : Summable (Bterm σ) := by
  refine Summable.of_norm_bounded (f := Bterm σ) (g := fun p : ℕ => 2 * (p : ℝ) ^ (-2 : ℝ))
    ?_ (fun p => abs_Bterm_le hσ p)
  exact (Real.summable_nat_rpow.mpr (by norm_num : (-2 : ℝ) < -1)).mul_left 2

private lemma G_eq_sum {σ : ℝ} (hσ : 1 < σ) :
    G σ = (∑' p : ℕ, Pterm σ p) + ∑' p : ℕ, Bterm σ p := by
  have h1 : Summable (Pterm σ) := summable_Pterm hσ
  have h2 : Summable (Bterm σ) := summable_Bterm (le_of_lt hσ)
  rw [← h1.tsum_add h2]
  exact tsum_congr fun p => Gterm_eq σ p

/-! ### The limit of the linear part over the primes -/

private noncomputable def chi4primeLimit : ℝ := (Classical.choose chi4_prime_recip_converges).re

private lemma chi4primeLimit_spec :
    Tendsto (fun y : ℝ => ∑ p ∈ (range (⌊y⌋₊ + 1)).filter Nat.Prime,
        ((ZMod.χ₄ ((p : ℕ) : ZMod 4) : ℤ) : ℝ) / (p : ℝ)) atTop
      (nhds chi4primeLimit) := by
  have h := Classical.choose_spec chi4_prime_recip_converges
  have hr := (Complex.continuous_re.tendsto (Classical.choose chi4_prime_recip_converges)).comp h
  refine hr.congr fun y => ?_
  have hcast : (∑ p ∈ (range (⌊y⌋₊ + 1)).filter Nat.Prime,
        ((ZMod.χ₄ ((p : ℕ) : ZMod 4) : ℤ) : ℂ) / (p : ℂ)).re
      = ∑ p ∈ (range (⌊y⌋₊ + 1)).filter Nat.Prime,
        ((ZMod.χ₄ ((p : ℕ) : ZMod 4) : ℤ) : ℝ) / (p : ℝ) := by
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← Complex.ofReal_intCast, ← Complex.ofReal_natCast, ← Complex.ofReal_div,
      Complex.ofReal_re]
  rw [Function.comp_apply]
  exact hcast

private lemma tendsto_partial_Pterm_one :
    Tendsto (fun N : ℕ => ∑ n ∈ range N, Pterm 1 n) atTop (nhds chi4primeLimit) := by
  have hnat : Tendsto (fun N : ℕ => ∑ p ∈ (range (N + 1)).filter Nat.Prime, c4 p / (p : ℝ))
      atTop (nhds chi4primeLimit) := by
    have h := chi4primeLimit_spec.comp (tendsto_natCast_atTop_atTop (R := ℝ))
    refine h.congr fun N => ?_
    simp only [Function.comp_apply, Nat.floor_natCast, c4]
  have hF : Tendsto (fun M : ℕ => ∑ p ∈ (range M).filter Nat.Prime, c4 p / (p : ℝ)) atTop
      (nhds chi4primeLimit) :=
    (Filter.tendsto_add_atTop_iff_nat (f := fun M : ℕ =>
      ∑ p ∈ (range M).filter Nat.Prime, c4 p / (p : ℝ)) 1).mp hnat
  refine hF.congr fun M => ?_
  rw [Finset.sum_filter]
  exact Finset.sum_congr rfl fun p _ => (Pterm_one_eq p).symm

/-! ### Continuity of `σ ↦ Bterm σ p` -/

private lemma continuousAt_Bterm (p : ℕ) : ContinuousAt (fun σ : ℝ => Bterm σ p) 1 := by
  by_cases hp : p.Prime
  · have hfun : (fun σ : ℝ => Bterm σ p)
        = fun σ => -Real.log (1 - c4 p * (p : ℝ) ^ (-σ)) - c4 p * (p : ℝ) ^ (-σ) := by
      funext σ; rw [Bterm_of_prime hp]; ring
    rw [hfun]
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hpow : ContinuousAt (fun σ : ℝ => (p : ℝ) ^ (-σ)) 1 :=
      ((Real.continuous_const_rpow hp0).comp continuous_neg).continuousAt
    have hlin : ContinuousAt (fun σ : ℝ => 1 - c4 p * (p : ℝ) ^ (-σ)) 1 :=
      continuousAt_const.sub (continuousAt_const.mul hpow)
    have hval : 1 - c4 p * (p : ℝ) ^ (-1 : ℝ) ≠ 0 := by
      have := one_sub_c4_pos (le_refl (1 : ℝ)) hp
      simpa using this.ne'
    exact (hlin.log hval).neg.sub (continuousAt_const.mul hpow)
  · have hfun : (fun σ : ℝ => Bterm σ p) = fun _ => 0 := by
      funext σ; unfold Bterm; rw [if_neg hp]
    rw [hfun]; exact continuousAt_const

private lemma tendsto_B_one_plus :
    Tendsto (fun σ : ℝ => ∑' p : ℕ, Bterm σ p) (nhdsWithin 1 (Set.Ioi 1))
      (nhds (∑' p : ℕ, Bterm 1 p)) := by
  refine tendsto_tsum_of_dominated_convergence (f := fun σ p => Bterm σ p)
    (g := fun p => Bterm 1 p) (bound := fun p => 2 * (p : ℝ) ^ (-2 : ℝ)) ?_ ?_ ?_
  · exact (Real.summable_nat_rpow.mpr (by norm_num : (-2 : ℝ) < -1)).mul_left 2
  · intro p
    exact (continuousAt_Bterm p).tendsto.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with σ hσ p
    exact abs_Bterm_le (le_of_lt hσ) p

/-! ### The Abel limits -/

private lemma Pterm_one_mul (σ : ℝ) (n : ℕ) :
    Pterm 1 n * (n : ℝ) ^ (-(σ - 1)) = Pterm σ n := by
  by_cases hp : n.Prime
  · rw [Pterm_one_eq, if_pos hp, Pterm, if_pos hp]
    have hn : (0 : ℝ) < n := by exact_mod_cast hp.pos
    have h1 : (n : ℝ) ^ (-1 : ℝ) * (n : ℝ) ^ (-(σ - 1)) = (n : ℝ) ^ (-σ) := by
      rw [← Real.rpow_add hn]; ring_nf
    rw [div_eq_mul_inv, ← Real.rpow_neg_one (n : ℝ), mul_assoc, h1]
  · rw [Pterm_one_eq, if_neg hp, Pterm, if_neg hp, zero_mul]

private lemma c4_div_mul_rpow (σ : ℝ) (n : ℕ) :
    c4 n / (n : ℝ) * (n : ℝ) ^ (-(σ - 1)) = c4 n * (n : ℝ) ^ (-σ) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp [c4]
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have h1 : (n : ℝ) ^ (-1 : ℝ) * (n : ℝ) ^ (-(σ - 1)) = (n : ℝ) ^ (-σ) := by
      rw [← Real.rpow_add hn0]; ring_nf
    rw [div_eq_mul_inv, ← Real.rpow_neg_one (n : ℝ), mul_assoc, h1]

private lemma tendsto_shift :
    Tendsto (fun σ : ℝ => σ - 1) (nhdsWithin 1 (Set.Ioi 1)) (nhdsWithin 0 (Set.Ioi 0)) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, ?_⟩
  · have h : Tendsto (fun σ : ℝ => σ - 1) (nhds (1 : ℝ)) (nhds (1 - 1)) :=
      tendsto_id.sub tendsto_const_nhds
    simpa using h.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with σ hσ
    simp only [Set.mem_Ioi] at hσ ⊢
    linarith

private lemma tendsto_P_one_plus :
    Tendsto (fun σ : ℝ => ∑' p : ℕ, Pterm σ p) (nhdsWithin 1 (Set.Ioi 1))
      (nhds chi4primeLimit) := by
  have ha0 : Pterm 1 0 = 0 := by rw [Pterm_one_eq]; simp
  have habel := Commons.Analysis.DirichletSeries.abel_tendsto_tsum_mul_rpow_conditional
    ha0 tendsto_partial_Pterm_one
  have hcomp := habel.comp tendsto_shift
  refine hcomp.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  simp only [Function.comp_apply]
  rw [tsum_congr (fun n => Pterm_one_mul σ n),
    tsum_eq_of_summable_unconditional (summable_Pterm hσ)]

private lemma c4_div_pos {p : ℕ} (hp : p.Prime) : 0 < 1 - c4 p / (p : ℝ) := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hle : |c4 p / (p : ℝ)| ≤ 1 / 2 := by
    rw [abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (p : ℝ))]
    calc |c4 p| / (p : ℝ) ≤ 1 / (p : ℝ) :=
          div_le_div_of_nonneg_right (abs_c4_le_one p) (by positivity)
      _ ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
  have h2 : c4 p / (p : ℝ) ≤ 1 / 2 := le_trans (le_abs_self _) hle
  linarith

private lemma Ell_tendsto_pi_div_four :
    Tendsto Ell (nhdsWithin (1 : ℝ) (Set.Ioi 1)) (nhds (Real.pi / 4)) := by
  have ha0 : (fun n : ℕ => c4 n / (n : ℝ)) 0 = 0 := by simp [c4]
  have hsum : Tendsto (fun N : ℕ => ∑ n ∈ range N, c4 n / (n : ℝ)) atTop
      (nhds (Real.pi / 4)) := by
    have h := Commons.NumberTheory.DirichletCharacter.chi4_sum_div_tendsto_pi_div_four
    simpa [c4] using h
  have habel := Commons.Analysis.DirichletSeries.abel_tendsto_tsum_mul_rpow_conditional
    ha0 hsum
  have hcomp := habel.comp tendsto_shift
  refine hcomp.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  simp only [Function.comp_apply]
  rw [tsum_congr (fun n => c4_div_mul_rpow σ n),
    tsum_eq_of_summable_unconditional (f := fun n : ℕ => c4 n * (n : ℝ) ^ (-σ))
      (Summable.of_norm (summable_norm_fpl hσ))]
  rfl

private lemma G_tendsto_log :
    Tendsto G (nhdsWithin (1 : ℝ) (Set.Ioi 1)) (nhds (Real.log (Real.pi / 4))) := by
  have hlog : Tendsto (fun σ : ℝ => Real.log (Ell σ)) (nhdsWithin (1 : ℝ) (Set.Ioi 1))
      (nhds (Real.log (Real.pi / 4))) :=
    (Real.continuousAt_log (by positivity)).tendsto.comp Ell_tendsto_pi_div_four
  refine hlog.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  exact (G_eq_log_Ell hσ).symm

private lemma G_tendsto_PB :
    Tendsto G (nhdsWithin (1 : ℝ) (Set.Ioi 1))
      (nhds (chi4primeLimit + ∑' p : ℕ, Bterm 1 p)) := by
  have hsum := tendsto_P_one_plus.add tendsto_B_one_plus
  refine hsum.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  exact (G_eq_sum hσ).symm

private lemma Pinf_add_B_eq_log :
    chi4primeLimit + (∑' p : ℕ, Bterm 1 p) = Real.log (Real.pi / 4) :=
  tendsto_nhds_unique G_tendsto_PB G_tendsto_log

private lemma tendsto_partial_Gterm_one :
    Tendsto (fun N : ℕ => ∑ n ∈ range N, Gterm 1 n) atTop (nhds (Real.log (Real.pi / 4))) := by
  have hB : Tendsto (fun N : ℕ => ∑ n ∈ range N, Bterm 1 n) atTop
      (nhds (∑' p : ℕ, Bterm 1 p)) :=
    (summable_Bterm (le_refl 1)).hasSum.tendsto_sum_nat
  have hsum := tendsto_partial_Pterm_one.add hB
  rw [Pinf_add_B_eq_log] at hsum
  refine hsum.congr fun N => ?_
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun n _ => (Gterm_eq 1 n).symm

/-- The constant `H` of Friedlander–Iwaniec (4.8). The Euler product
`∏_{p ≤ N} (1 − χ₄(p)/p)` is only conditionally convergent, so the correct
formalisation is the interval limit (over `Nat.primesBelow N`), which tends to
`4/π = L(1, χ₄)^{-1}` (Leibniz for the Dirichlet beta function). -/
theorem tendsto_prod_one_sub_chi4_div_prime :
    Filter.Tendsto (fun N : ℕ => ∏ p ∈ Nat.primesBelow N,
        (1 - ((ZMod.χ₄ ((p : ℕ) : ZMod 4) : ℤ) : ℝ) / (p : ℝ)))
      Filter.atTop (nhds (4 / Real.pi)) := by
  change Tendsto (fun N : ℕ => ∏ p ∈ Nat.primesBelow N, (1 - c4 p / (p : ℝ)))
    atTop (nhds (4 / Real.pi))
  have hprodpos : ∀ N : ℕ, 0 < ∏ p ∈ Nat.primesBelow N, (1 - c4 p / (p : ℝ)) :=
    fun N => Finset.prod_pos fun p hp => c4_div_pos (Nat.mem_primesBelow.mp hp).2
  have hlog : Tendsto
      (fun N : ℕ => Real.log (∏ p ∈ Nat.primesBelow N, (1 - c4 p / (p : ℝ))))
      atTop (nhds (-Real.log (Real.pi / 4))) := by
    have hneg : Tendsto (fun N : ℕ => -(∑ n ∈ range N, Gterm 1 n)) atTop
        (nhds (-(Real.log (Real.pi / 4)))) := tendsto_partial_Gterm_one.neg
    refine hneg.congr fun N => ?_
    rw [Real.log_prod (fun p hp => (c4_div_pos (Nat.mem_primesBelow.mp hp).2).ne')]
    have h1 : ∑ p ∈ Nat.primesBelow N, Real.log (1 - c4 p / (p : ℝ))
        = -∑ p ∈ Nat.primesBelow N, Gterm 1 p := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun p hp => ?_
      have hpp : p.Prime := (Nat.mem_primesBelow.mp hp).2
      rw [show Gterm 1 p = -Real.log (1 - c4 p * (p : ℝ) ^ (-1 : ℝ)) by
        rw [Gterm, if_pos hpp]]
      rw [Real.rpow_neg_one, ← div_eq_mul_inv]; ring
    have h2 : ∑ p ∈ Nat.primesBelow N, Gterm 1 p = ∑ n ∈ range N, Gterm 1 n := by
      rw [primesBelow_eq, Finset.sum_filter]
      exact Finset.sum_congr rfl fun p _ => by by_cases hp : p.Prime <;> simp [Gterm, hp]
    rw [h1, h2]
  have hexpval : Real.exp (-Real.log (Real.pi / 4)) = 4 / Real.pi := by
    rw [Real.exp_neg, Real.exp_log (by positivity), inv_div]
  have hfinal : Tendsto
      (fun N : ℕ => Real.exp (Real.log (∏ p ∈ Nat.primesBelow N, (1 - c4 p / (p : ℝ)))))
      atTop (nhds (4 / Real.pi)) := by
    have h := Real.continuous_exp.tendsto (-Real.log (Real.pi / 4))
    rw [hexpval] at h
    exact h.comp hlog
  refine hfinal.congr fun N => ?_
  exact Real.exp_log (hprodpos N)

end
end Commons.NumberTheory.FriedlanderIwaniec
