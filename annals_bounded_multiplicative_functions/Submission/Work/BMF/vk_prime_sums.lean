import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.mangoldt_sum_not_coprime_le
import Submission.Work.BMF.norm_cpow_neg_I_mul
import Submission.Work.BMF.log_mul_loglog_le_exp
import Submission.Work.BMF.VKdenom
import Submission.Work.BMF.liouville.zetaTwSum_sub_main_le
import Submission.Work.BMF.liouville.zetaTwPerron_rect
import Submission.Work.BMF.perron_twist_core
import Submission.Work.BMF.chiPerronTw_bound
import Submission.Work.BMF.v7chi_defs
import Submission.Work.BMF.VKPrimeSums.zeroFree_LVK
import Submission.Work.BMF.VKPrimeSums.v7_of_zeroFree
import Submission.Work.BMF.VKPrimeSums.shifted_partial_sum_bound
import Submission.Work.BMF.VKPrimeSums.zeta_norm_le_region2
import Submission.Work.BMF.VKPrimeSums.vk_L_growth
import Submission.Work.BMF.VKPrimeSums.vkExpSum_clean
import Submission.Work.BMF.zeta_partial_sum_bound
import Submission.Work.BMF.zeta_approx_functional_eq
import Submission.Work.BMF.zpt.zeta_growth_strip
import Submission.Work.BMF.zeta_VK_zeroFree_of_growth
import Submission.Work.BMF.zeta_logDeriv_bound_vk

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! Guidance from the project lead (the requester):

LEAD NOTE (re-dispatch, AMENDED statement; see DESIGN.md 'Addendum: V0 exponent'). The statement file imports only Defs, because some siblings do not build yet. For the PROOF, add these imports to your file once they build: Submission.Work.BMF.Defs,Submission.Work.BMF.zeta_prime_sum_twist,Submission.Work.BMF.chi_prime_sum_twist. The previous owner's file (old exponents) is Submission/Work/BMF/V6Prev/vk_prime_sums.prev.txt (or .kept.txt); REUSE its proved parts. Proved siblings: vk_L_lower, vk_L_upper, perron_twist_core, chiPerronTw_bound, LowWidth_zero_free. Do NOT use Ford Thm 3/4; do NOT rebuild sibling nodes (vmvt_uniform, kth_derivative_reduction_uniform, and the others are their own nodes).
LEAD NOTE: read Submission/Work/BMF/DESIGN.md 'Addendum: vk_prime_sums detail' (the lead's sub-design for N10). REUSE the previous owner's proved modules: perron_twist_core (perron_twisted_uniform, chiPerronTw_sub_sum_uniform, chiGTw_eq_LSeries, chiGTw_differentiableOn, rect_edge_decomp, chiPerronTw_rect), chiPerronTw_bound, vk_L_lower, vk_L_upper. WARNING: kth_derivative_reduction does NOT build (its import core_sum_bound has a doubled 'namespace Work.BMF'); fix that or reuse its text (VKPrev/*.prev.txt). Previous partial files: Submission/Work/BMF/VKPrev/*.prev.txt. The Commons assets are in ASSETS.md; chen's generic engine borelCaratheodory_deriv_le, jensenCarleman_main and completedL_diskZeroCount_explicit is reusable for L(s,χ). Contour choice for the final step: x' = ⌊x⌋+1/2, T = exp((log x)^{1/2}) (shifted by 2 if within 1 of |u|), σ₁ = 1 − min(c₄/(2D), c₅ q^{−1/(20A)}/2, 1/4); the rectangle is then zero-free apart from ζ's pole.

## Assembly (this file)

`vk_prime_sums` is reduced to the two sibling nodes `zeta_prime_sum_twist` (V6) and
`chi_prime_sum_twist` (V7); `vk_prime_sums_of` performs that reduction.  The work done here is

* `χ ≠ 1`: nothing to do, V7 is the statement.
* `χ = 1`: the trivial character mod `q` kills exactly the integers sharing a prime factor with
  `q`, so `Σ_{n ≤ x} Λ(n)·1(n)·n^{-iu}` differs from the untwisted sum `Σ_{n ≤ x} Λ(n) n^{-iu}`
  by at most `ω(q)·log x` (`vk_norm_principal_sub_le`, from `mangoldt_sum_not_coprime_le`);
  `ω(q) ≤ 2 log q ≤ 2A log log x` is absorbed by `x·exp(-c (log x)^{1/12})`
  (`vk_omega_mul_log_le`, from `log_mul_loglog_le_exp`).
* `x < 3` is absorbed into the constant `C` by the trivial bounds
  `‖Σ‖ ≤ ⌊x⌋₊ log ⌊x⌋₊ ≤ 3 log 3` and `‖x^{1-iu}/(1-iu)‖ ≤ x < 3`.
* `vk_zeta_pnt_of_one_tenth` / `vk_chi_pnt_of_one_tenth` weaken a `(log x)^{1/10}` error to the
  `(log x)^{1/12}` error of the statement, so the same assembly applies to the `N4chain`
  interfaces `ZetaTwistedPNT`/`ChiTwistedPNT`.
-/

namespace Work.BMF

open Finset

/-- The trivial character mod `q` evaluated at `n` is `1` exactly for the units of `ZMod q`. -/
lemma vk_one_apply_eq_ite (q : ℕ) [NeZero q] (n : ℕ) :
    (1 : DirichletCharacter ℂ q) n = if n.Coprime q then 1 else 0 := by
  by_cases h : n.Coprime q
  · rw [if_pos h]
    exact MulChar.one_apply ((ZMod.isUnit_iff_coprime n q).mpr h)
  · rw [if_neg h, MulChar.apply_eq_zero_iff, ZMod.isUnit_iff_coprime]
    exact h

/-- `ω(q) ≤ log q / log 2`. -/
lemma vk_card_primeFactors_le_log_div_log_two (q : ℕ) [NeZero q] :
    (q.primeFactors.card : ℝ) ≤ Real.log q / Real.log 2 := by
  have h1 : (2 : ℕ) ^ q.primeFactors.card ≤ q.primeFactors.prod id :=
    Finset.pow_card_le_prod q.primeFactors id 2
      (fun p hp => (Nat.mem_primeFactors.mp hp).1.two_le)
  have h2 : q.primeFactors.prod id ∣ q := Nat.prod_primeFactors_dvd q
  have h3 : (2 : ℕ) ^ q.primeFactors.card ≤ q :=
    le_trans h1 (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) h2)
  have h4 : ((2 : ℝ) ^ q.primeFactors.card : ℝ) ≤ (q : ℝ) := by exact_mod_cast h3
  have h5 : ((q.primeFactors.card : ℝ)) * Real.log 2 ≤ Real.log q := by
    have hlog := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ q.primeFactors.card) h4
    rwa [Real.log_pow] at hlog
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  rw [le_div_iff₀ hlog2]
  linarith

/-- `ω(q) ≤ 2 log q`. -/
lemma vk_card_primeFactors_le_two_log (q : ℕ) [NeZero q] :
    (q.primeFactors.card : ℝ) ≤ 2 * Real.log q := by
  have h1 : (2 : ℕ) ^ q.primeFactors.card ≤ q.primeFactors.prod id :=
    Finset.pow_card_le_prod q.primeFactors id 2
      (fun p hp => (Nat.mem_primeFactors.mp hp).1.two_le)
  have h2 : q.primeFactors.prod id ∣ q := Nat.prod_primeFactors_dvd q
  have h3 : (2 : ℕ) ^ q.primeFactors.card ≤ q :=
    le_trans h1 (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) h2)
  have h4 : ((2 : ℝ) ^ q.primeFactors.card : ℝ) ≤ (q : ℝ) := by exact_mod_cast h3
  have h5 : ((q.primeFactors.card : ℝ)) * Real.log 2 ≤ Real.log q := by
    have hlog := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ q.primeFactors.card) h4
    rwa [Real.log_pow] at hlog
  have h6 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have h7 : 0 ≤ Real.log q :=
    Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q))
  nlinarith [h5, h6, h7]

/-- `ω(q)·log x` is absorbed by `C·x·exp(-c (log x)^{1/12})`, uniformly for `q ≤ (log x)^A`. -/
lemma vk_omega_mul_log_le (A c : ℝ) (hA : 0 < A) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 3 ≤ x → ∀ q : ℕ, [NeZero q] → (q : ℝ) ≤ Real.log x ^ A →
      (q.primeFactors.card : ℝ) * Real.log x ≤
        C * x * Real.exp (-c * Real.log x ^ (1 / 12 : ℝ)) := by
  obtain ⟨C, hCpos, hC⟩ := log_mul_loglog_le_exp (2 * A) c (by positivity) hc
  refine ⟨C, hCpos, ?_⟩
  intro x hx3 q _inst hq
  have hx0 : 0 < x := by linarith
  have hlogx_ge1 : 1 ≤ Real.log x := by
    have h3 : 1 ≤ Real.log 3 :=
      (Real.le_log_iff_exp_le (by norm_num)).mpr (le_of_lt Real.exp_one_lt_three)
    have h4 : Real.log 3 ≤ Real.log x := Real.log_le_log (by norm_num) hx3
    linarith
  have hlogxpos : 0 < Real.log x := by linarith
  have hcard : (q.primeFactors.card : ℝ) ≤ 2 * Real.log q :=
    vk_card_primeFactors_le_two_log q
  have hlogq : Real.log q ≤ A * Real.log (Real.log x) := by
    have hqpos : (0 : ℝ) < (q : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
    have h1 : Real.log q ≤ Real.log ((Real.log x) ^ A) := Real.log_le_log hqpos hq
    rwa [Real.log_rpow hlogxpos] at h1
  have hloglogx_nonneg : 0 ≤ Real.log (Real.log x) := Real.log_nonneg hlogx_ge1
  have hstep : (q.primeFactors.card : ℝ) * Real.log x ≤
      (2 * A) * Real.log x * Real.log (Real.log x) := by
    have h1 : (q.primeFactors.card : ℝ) * Real.log x ≤ (2 * Real.log q) * Real.log x :=
      mul_le_mul_of_nonneg_right hcard hlogxpos.le
    have h2 : (2 * Real.log q) * Real.log x ≤ (2 * (A * Real.log (Real.log x))) * Real.log x :=
      mul_le_mul_of_nonneg_right (by linarith) hlogxpos.le
    have h3 : (2 * (A * Real.log (Real.log x))) * Real.log x =
        (2 * A) * Real.log x * Real.log (Real.log x) := by ring
    linarith
  have h4 : (2 * A) * Real.log x * Real.log (Real.log x) ≤
      C * Real.exp (Real.log x - c * Real.log x ^ (1 / 10 : ℝ)) := hC (Real.log x) hlogx_ge1
  have hexp : Real.exp (Real.log x - c * Real.log x ^ (1 / 10 : ℝ)) ≤
      x * Real.exp (-c * Real.log x ^ (1 / 12 : ℝ)) := by
    rw [Real.exp_sub, Real.exp_log hx0, div_eq_mul_inv, ← Real.exp_neg]
    apply mul_le_mul_of_nonneg_left _ hx0.le
    apply Real.exp_le_exp.mpr
    have hpow : Real.log x ^ (1 / 12 : ℝ) ≤ Real.log x ^ (1 / 10 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hlogx_ge1 (by norm_num)
    have := mul_le_mul_of_nonneg_left hpow hc.le
    linarith
  calc (q.primeFactors.card : ℝ) * Real.log x
      ≤ (2 * A) * Real.log x * Real.log (Real.log x) := hstep
    _ ≤ C * Real.exp (Real.log x - c * Real.log x ^ (1 / 10 : ℝ)) := h4
    _ ≤ C * (x * Real.exp (-c * Real.log x ^ (1 / 12 : ℝ))) :=
        mul_le_mul_of_nonneg_left hexp hCpos.le
    _ = C * x * Real.exp (-c * Real.log x ^ (1 / 12 : ℝ)) := by ring

/-- `Σ_{n ≤ N} Λ(n) ≤ N log N`. -/
lemma vk_sum_mangoldt_le (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.vonMangoldt n : ℝ) ≤ (N : ℝ) * Real.log N := by
  calc ∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.vonMangoldt n : ℝ)
      ≤ ∑ _n ∈ Finset.Icc 1 N, Real.log N := by
        apply Finset.sum_le_sum
        intro n hn
        have hnN : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hn).2
        exact le_trans ArithmeticFunction.vonMangoldt_le_log
          (Real.log_le_log (by exact_mod_cast (Finset.mem_Icc.mp hn).1) hnN)
    _ = (N : ℝ) * Real.log N := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
        simp

/-- The sum twisted by the principal character mod `q` differs from the untwisted sum by at
most `ω(q)·log N`. -/
lemma vk_norm_principal_sub_le {q : ℕ} [NeZero q] (u : ℝ) (N : ℕ) :
    ‖(∑ n ∈ Finset.Icc 1 N, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
          (1 : DirichletCharacter ℂ q) n * (n : ℂ) ^ (-(Complex.I * u))) -
        ∑ n ∈ Finset.Icc 1 N, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
          (n : ℂ) ^ (-(Complex.I * u))‖
      ≤ (q.primeFactors.card : ℝ) * Real.log N := by
  have hA : (∑ n ∈ Finset.Icc 1 N, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
        (1 : DirichletCharacter ℂ q) n * (n : ℂ) ^ (-(Complex.I * u)))
      = ∑ n ∈ (Finset.Icc 1 N).filter (fun n => n.Coprime q),
          ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * (n : ℂ) ^ (-(Complex.I * u)) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n _
    rw [vk_one_apply_eq_ite]
    by_cases h : n.Coprime q <;> simp [h]
  have hB : (∑ n ∈ Finset.Icc 1 N, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
          (n : ℂ) ^ (-(Complex.I * u)))
      = ∑ n ∈ (Finset.Icc 1 N).filter (fun n => n.Coprime q),
            ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * (n : ℂ) ^ (-(Complex.I * u))
        + ∑ n ∈ (Finset.Icc 1 N).filter (fun n => ¬ n.Coprime q),
            ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * (n : ℂ) ^ (-(Complex.I * u)) :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hdiff : (∑ n ∈ (Finset.Icc 1 N).filter (fun n => n.Coprime q),
          ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * (n : ℂ) ^ (-(Complex.I * u))) -
        (∑ n ∈ (Finset.Icc 1 N).filter (fun n => n.Coprime q),
            ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * (n : ℂ) ^ (-(Complex.I * u))
          + ∑ n ∈ (Finset.Icc 1 N).filter (fun n => ¬ n.Coprime q),
            ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * (n : ℂ) ^ (-(Complex.I * u)))
      = -(∑ n ∈ (Finset.Icc 1 N).filter (fun n => ¬ n.Coprime q),
            ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * (n : ℂ) ^ (-(Complex.I * u))) := by
    ring
  rw [hA, hB, hdiff, norm_neg]
  calc ‖∑ n ∈ (Finset.Icc 1 N).filter (fun n => ¬ n.Coprime q),
        ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * (n : ℂ) ^ (-(Complex.I * u))‖
      ≤ ∑ n ∈ (Finset.Icc 1 N).filter (fun n => ¬ n.Coprime q),
          ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * (n : ℂ) ^ (-(Complex.I * u))‖ :=
        norm_sum_le _ _
    _ = ∑ n ∈ (Finset.Icc 1 N).filter (fun n => ¬ n.Coprime q),
          (ArithmeticFunction.vonMangoldt n : ℝ) := by
        apply Finset.sum_congr rfl
        intro n hn
        have hn1 : 1 ≤ n := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1
        rw [norm_mul, norm_cpow_neg_I_mul u hn1, mul_one, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    _ ≤ (q.primeFactors.card : ℝ) * Real.log N := mangoldt_sum_not_coprime_le N

/-- The twisted sum is bounded by `N log N` (trivial bounds and `Λ ≤ log`). -/
lemma vk_norm_twisted_sum_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (u : ℝ) (N : ℕ) :
    ‖∑ n ∈ Finset.Icc 1 N, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ n *
        (n : ℂ) ^ (-(Complex.I * u))‖ ≤ (N : ℝ) * Real.log N := by
  have hχ1 : ∀ n : ℕ, ‖χ n‖ ≤ 1 := fun n => DirichletCharacter.norm_le_one χ (n : ZMod q)
  calc ‖∑ n ∈ Finset.Icc 1 N, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ n *
        (n : ℂ) ^ (-(Complex.I * u))‖
      ≤ ∑ n ∈ Finset.Icc 1 N, ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ n *
          (n : ℂ) ^ (-(Complex.I * u))‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.vonMangoldt n : ℝ) := by
        apply Finset.sum_le_sum
        intro n hn
        have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
        have hL : ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)‖ =
            (ArithmeticFunction.vonMangoldt n : ℝ) := by
          rw [Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
        calc ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ n *
              (n : ℂ) ^ (-(Complex.I * u))‖
          = ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ n‖ *
              ‖(n : ℂ) ^ (-(Complex.I * u))‖ := by rw [norm_mul]
        _ = ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ n‖ := by
              rw [norm_cpow_neg_I_mul u hn1, mul_one]
        _ = ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)‖ * ‖χ n‖ := by rw [norm_mul]
        _ ≤ (ArithmeticFunction.vonMangoldt n : ℝ) * 1 := by
              rw [hL]
              exact mul_le_mul_of_nonneg_left (hχ1 n) ArithmeticFunction.vonMangoldt_nonneg
        _ = (ArithmeticFunction.vonMangoldt n : ℝ) := mul_one _
    _ ≤ (N : ℝ) * Real.log N := vk_sum_mangoldt_le N

/-- `‖x^{1-iu}/(1-iu)‖ ≤ x` for `x ≥ 0`. -/
lemma vk_norm_main_le {x : ℝ} (hx : 0 ≤ x) (u : ℝ) :
    ‖(x : ℂ) ^ (1 - Complex.I * u) / (1 - Complex.I * u)‖ ≤ x := by
  rcases eq_or_lt_of_le hx with rfl | hxpos
  · have hne : (1 - Complex.I * (u : ℂ)) ≠ 0 := by
      intro h
      have h1 : (1 - Complex.I * (u : ℂ)).re = 0 := by rw [h]; simp
      simp [Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im] at h1
    rw [Complex.ofReal_zero, Complex.zero_cpow hne, zero_div, norm_zero]
  · rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hxpos]
    have hre : (1 - Complex.I * (u : ℂ)).re = 1 := by
      simp [Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im]
    rw [hre, Real.rpow_one]
    have hden : 1 ≤ ‖(1 : ℂ) - Complex.I * (u : ℂ)‖ := by
      have hsq : ‖(1 : ℂ) - Complex.I * (u : ℂ)‖ ^ 2 = 1 + u ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]
        simp [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
          Complex.I_im]
        ring
      nlinarith [norm_nonneg ((1 : ℂ) - Complex.I * (u : ℂ)), sq_nonneg u]
    exact div_le_self hxpos.le hden

/-- `log ⌊x⌋₊ ≤ log x` for `x ≥ 1`. -/
lemma vk_log_floor_le_log (x : ℝ) (hx : 1 ≤ x) : Real.log (⌊x⌋₊ : ℝ) ≤ Real.log x := by
  rcases eq_zero_or_pos ⌊x⌋₊ with h | h
  · rw [h, Nat.cast_zero, Real.log_zero]
    exact Real.log_nonneg hx
  · exact Real.log_le_log (by exact_mod_cast h) (Nat.floor_le (by linarith))



/-- `1 / exp z = exp (-z)`. -/
lemma vk_one_div_exp (z : ℝ) : 1 / Real.exp z = Real.exp (-z) := by
  rw [one_div, ← Real.exp_neg]

/-- Weakening the exponent `1/10` to `1/12` in the error term, at the cost of a constant. -/
lemma vk_error_weaken_const (c C : ℝ) (hc : 0 < c) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ x : ℝ, 2 ≤ x →
      C * x * Real.exp (-c * Real.log x ^ (1 / 10 : ℝ)) ≤
        C' * x * Real.exp (-c * Real.log x ^ (1 / 12 : ℝ)) := by
  have hlog3nonneg : 0 ≤ Real.log 3 := (Real.log_pos (by norm_num)).le
  refine ⟨4 * |C| * Real.exp (c * Real.log 3 ^ (1 / 12 : ℝ)) + 4, by positivity, ?_⟩
  intro x hx2
  have hxpos : 0 < x := by linarith
  have hEpos : 0 < Real.exp (c * Real.log 3 ^ (1 / 12 : ℝ)) := Real.exp_pos _
  have hE1 : 1 ≤ Real.exp (c * Real.log 3 ^ (1 / 12 : ℝ)) :=
    Real.one_le_exp_iff.mpr (mul_nonneg hc.le (Real.rpow_nonneg hlog3nonneg _))
  have hEinv : Real.exp (-c * Real.log 3 ^ (1 / 12 : ℝ)) =
      1 / Real.exp (c * Real.log 3 ^ (1 / 12 : ℝ)) := by
    rw [vk_one_div_exp]
    congr 1
    ring
  by_cases hx3 : (3 : ℝ) ≤ x
  · -- `x ≥ 3`
    have hlogx1 : 1 ≤ Real.log x := by
      have h3 : 1 ≤ Real.log 3 :=
        (Real.le_log_iff_exp_le (by norm_num)).mpr (le_of_lt Real.exp_one_lt_three)
      have h4 : Real.log 3 ≤ Real.log x := Real.log_le_log (by norm_num) hx3
      linarith
    have hε : Real.exp (-c * Real.log x ^ (1 / 10 : ℝ)) ≤
        Real.exp (-c * Real.log x ^ (1 / 12 : ℝ)) := by
      apply Real.exp_le_exp.mpr
      have hpow : Real.log x ^ (1 / 12 : ℝ) ≤ Real.log x ^ (1 / 10 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hlogx1 (by norm_num)
      have := mul_le_mul_of_nonneg_left hpow hc.le
      linarith
    have hC : C ≤ 4 * |C| * Real.exp (c * Real.log 3 ^ (1 / 12 : ℝ)) + 4 := by
      nlinarith [le_abs_self C, abs_nonneg C, hE1]
    calc C * x * Real.exp (-c * Real.log x ^ (1 / 10 : ℝ))
        = C * (x * Real.exp (-c * Real.log x ^ (1 / 10 : ℝ))) := by ring
      _ ≤ |C| * (x * Real.exp (-c * Real.log x ^ (1 / 10 : ℝ))) :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
      _ ≤ |C| * (x * Real.exp (-c * Real.log x ^ (1 / 12 : ℝ))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hε hxpos.le) (abs_nonneg C)
      _ ≤ (4 * |C| * Real.exp (c * Real.log 3 ^ (1 / 12 : ℝ)) + 4) *
            (x * Real.exp (-c * Real.log x ^ (1 / 12 : ℝ))) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          nlinarith [abs_nonneg C, hE1]
      _ = (4 * |C| * Real.exp (c * Real.log 3 ^ (1 / 12 : ℝ)) + 4) * x *
            Real.exp (-c * Real.log x ^ (1 / 12 : ℝ)) := by ring
  · -- `2 ≤ x < 3`
    have hx3' : x < 3 := lt_of_not_ge hx3
    have hε10 : Real.exp (-c * Real.log x ^ (1 / 10 : ℝ)) ≤ 1 := by
      have h1 : 0 ≤ Real.log x ^ (1 / 10 : ℝ) :=
        Real.rpow_nonneg (Real.log_nonneg (by linarith)) _
      have h2 : -c * Real.log x ^ (1 / 10 : ℝ) ≤ 0 := by nlinarith [mul_nonneg hc.le h1]
      calc Real.exp (-c * Real.log x ^ (1 / 10 : ℝ)) ≤ Real.exp 0 := Real.exp_le_exp.mpr h2
        _ = 1 := Real.exp_zero
    have hε12 : 1 / Real.exp (c * Real.log 3 ^ (1 / 12 : ℝ)) ≤
        Real.exp (-c * Real.log x ^ (1 / 12 : ℝ)) := by
      rw [vk_one_div_exp]
      apply Real.exp_le_exp.mpr
      have hpow : Real.log x ^ (1 / 12 : ℝ) ≤ Real.log 3 ^ (1 / 12 : ℝ) :=
        Real.rpow_le_rpow (Real.log_nonneg (by linarith)) (Real.log_le_log (by linarith) hx3'.le)
          (by norm_num)
      have := mul_le_mul_of_nonneg_left hpow hc.le
      linarith
    have hxle : C * x ≤ |C| * 3 := by
      calc C * x ≤ |C| * x := mul_le_mul_of_nonneg_right (le_abs_self C) hxpos.le
        _ ≤ |C| * 3 := mul_le_mul_of_nonneg_left hx3'.le (abs_nonneg C)
    have hleft : C * x * Real.exp (-c * Real.log x ^ (1 / 10 : ℝ)) ≤ |C| * 3 := by
      calc C * x * Real.exp (-c * Real.log x ^ (1 / 10 : ℝ))
          ≤ |C| * 3 * 1 := mul_le_mul hxle hε10 (by positivity) (by positivity)
        _ = |C| * 3 := by ring
    have hright : |C| * 3 ≤ (4 * |C| * Real.exp (c * Real.log 3 ^ (1 / 12 : ℝ)) + 4) * x *
          Real.exp (-c * Real.log x ^ (1 / 12 : ℝ)) := by
      have h2 : (4 * |C| * Real.exp (c * Real.log 3 ^ (1 / 12 : ℝ)) + 4) * 2 *
            (1 / Real.exp (c * Real.log 3 ^ (1 / 12 : ℝ))) ≤
          (4 * |C| * Real.exp (c * Real.log 3 ^ (1 / 12 : ℝ)) + 4) * x *
            Real.exp (-c * Real.log x ^ (1 / 12 : ℝ)) := by
        have h3 : (2 : ℝ) * (1 / Real.exp (c * Real.log 3 ^ (1 / 12 : ℝ))) ≤
            x * Real.exp (-c * Real.log x ^ (1 / 12 : ℝ)) := by
          have h4 : (2 : ℝ) ≤ x := hx2
          exact mul_le_mul h4 hε12 (by positivity) (by linarith)
        calc (4 * |C| * Real.exp (c * Real.log 3 ^ (1 / 12 : ℝ)) + 4) * 2 *
              (1 / Real.exp (c * Real.log 3 ^ (1 / 12 : ℝ)))
            = (4 * |C| * Real.exp (c * Real.log 3 ^ (1 / 12 : ℝ)) + 4) *
              (2 * (1 / Real.exp (c * Real.log 3 ^ (1 / 12 : ℝ)))) := by ring
          _ ≤ (4 * |C| * Real.exp (c * Real.log 3 ^ (1 / 12 : ℝ)) + 4) *
                (x * Real.exp (-c * Real.log x ^ (1 / 12 : ℝ))) :=
                mul_le_mul_of_nonneg_left h3 (by positivity)
          _ = (4 * |C| * Real.exp (c * Real.log 3 ^ (1 / 12 : ℝ)) + 4) * x *
                Real.exp (-c * Real.log x ^ (1 / 12 : ℝ)) := by ring
      have h5 : |C| * 3 ≤ (4 * |C| * Real.exp (c * Real.log 3 ^ (1 / 12 : ℝ)) + 4) * 2 *
            (1 / Real.exp (c * Real.log 3 ^ (1 / 12 : ℝ))) := by
        have h6 : Real.exp (c * Real.log 3 ^ (1 / 12 : ℝ)) *
            (1 / Real.exp (c * Real.log 3 ^ (1 / 12 : ℝ))) = 1 := by
          field_simp
        have h7 : 0 ≤ 1 / Real.exp (c * Real.log 3 ^ (1 / 12 : ℝ)) := by positivity
        have h8 : 0 ≤ |C| := abs_nonneg C
        nlinarith [h6, h7, h8, hE1, mul_nonneg h8 (le_trans zero_le_one hE1)]
      linarith
    linarith


/-- The ζ-statement with a `(log x)^{1/10}` error implies the `(log x)^{1/12}` form. -/
lemma vk_zeta_pnt_of_one_tenth
    (h6 : ∃ c C : ℝ, 0 < c ∧ ∀ (x : ℝ), 2 ≤ x → ∀ (u : ℝ),
      |u| ≤ Real.exp (Real.log x ^ (21 / 20 : ℝ)) →
        ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
            (n : ℂ) ^ (-(Complex.I * u)) - (x : ℂ) ^ (1 - Complex.I * u) / (1 - Complex.I * u)‖
          ≤ C * x * Real.exp (-c * Real.log x ^ (1 / 10 : ℝ))) :
    ∃ c C : ℝ, 0 < c ∧ ∀ (x : ℝ), 2 ≤ x → ∀ (u : ℝ),
      |u| ≤ Real.exp (Real.log x ^ (21 / 20 : ℝ)) →
        ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
            (n : ℂ) ^ (-(Complex.I * u)) - (x : ℂ) ^ (1 - Complex.I * u) / (1 - Complex.I * u)‖
          ≤ C * x * Real.exp (-c * Real.log x ^ (1 / 12 : ℝ)) := by
  obtain ⟨c, C, hc, H⟩ := h6
  obtain ⟨C', hC'pos, hC'⟩ := vk_error_weaken_const c C hc
  exact ⟨c, C', hc, fun x hx u hu => le_trans (H x hx u hu) (hC' x hx)⟩

/-- The χ-statement with a `(log x)^{1/10}` error implies the `(log x)^{1/12}` form. -/
lemma vk_chi_pnt_of_one_tenth (A : ℝ)
    (h7 : ∃ c C : ℝ, 0 < c ∧ ∀ (x : ℝ), 2 ≤ x → ∀ (q : ℕ) [NeZero q],
      (q : ℝ) ≤ Real.log x ^ A → ∀ (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ (u : ℝ),
        |u| ≤ Real.exp (Real.log x ^ (21 / 20 : ℝ)) →
          ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ n *
              (n : ℂ) ^ (-(Complex.I * u))‖
            ≤ C * x * Real.exp (-c * Real.log x ^ (1 / 10 : ℝ))) :
    ∃ c C : ℝ, 0 < c ∧ ∀ (x : ℝ), 2 ≤ x → ∀ (q : ℕ) [NeZero q],
      (q : ℝ) ≤ Real.log x ^ A → ∀ (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ (u : ℝ),
        |u| ≤ Real.exp (Real.log x ^ (21 / 20 : ℝ)) →
          ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ n *
              (n : ℂ) ^ (-(Complex.I * u))‖
            ≤ C * x * Real.exp (-c * Real.log x ^ (1 / 12 : ℝ)) := by
  obtain ⟨c, C, hc, H⟩ := h7
  obtain ⟨C', hC'pos, hC'⟩ := vk_error_weaken_const c C hc
  exact ⟨c, C', hc, fun x hx q _ hq χ hχ u hu => le_trans (H x hx q hq χ hχ u hu) (hC' x hx)⟩


/-! ## The `χ = 1` half: the ζ input and the wiring to the twisted Perron engine -/

/-- The `ζ`-input of `Work.BMF.liouville.zetaTwSum_sub_main_le`: the Vinogradov–Korobov
zero-free region for `ζ` at heights `|t| ≥ 3` in the `VKd` shape, together with the
logarithmic-derivative bound in it. -/
def vk_zeta_box_statement : Prop :=
    (∃ c₁ : ℝ, 0 < c₁ ∧ ∀ t σ : ℝ, 3 ≤ |t| →
      1 - c₁ / Work.BMF.VKd (|t| + 3) ≤ σ → σ ≤ 1 →
      riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0) ∧
    (∃ c₂ B : ℝ, 0 < c₂ ∧ 0 < B ∧ ∀ t σ : ℝ, 3 ≤ |t| →
      1 - c₂ / Work.BMF.VKd (|t| + 3) ≤ σ → σ ≤ 2 →
      ‖deriv riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) /
        riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ B * (Real.log (|t| + 3)) ^ 2)

/-- The untwisted von Mangoldt sum is bounded by `N log N`. -/
lemma vk_norm_zetaTwSum_le (u : ℝ) (N : ℕ) :
    ‖∑ n ∈ Finset.Icc 1 N, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
        (n : ℂ) ^ (-(Complex.I * u))‖ ≤ (N : ℝ) * Real.log N := by
  have h1 : ‖∑ n ∈ Finset.Icc 1 N, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
        (n : ℂ) ^ (-(Complex.I * u))‖
      = ‖∑ n ∈ Finset.Icc 1 N, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
        (1 : DirichletCharacter ℂ 1) n * (n : ℂ) ^ (-(Complex.I * u))‖ := by
    congr 1
    apply Finset.sum_congr rfl
    intro n _
    rw [vk_one_apply_eq_ite]
    have : n.Coprime 1 := Nat.coprime_one_right n
    rw [if_pos this, mul_one]
  rw [h1]
  exact vk_norm_twisted_sum_le 1 u N

/-- The `ζ` half of `vk_prime_sums`: from the ζ zero-free box, the twisted prime number theorem
for `χ = 1`. -/
theorem vk_zeta_pnt_of_box (hbox : vk_zeta_box_statement) :
    ∃ c C : ℝ, 0 < c ∧ ∀ (x : ℝ), 2 ≤ x → ∀ (u : ℝ),
      |u| ≤ Real.exp (Real.log x ^ (21 / 20 : ℝ)) →
        ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
            (n : ℂ) ^ (-(Complex.I * u)) -
          (x : ℂ) ^ (1 - Complex.I * u) / (1 - Complex.I * u)‖
          ≤ C * x * Real.exp (-c * Real.log x ^ (1 / 12 : ℝ)) := by
  obtain ⟨hreg, hlog⟩ := hbox
  obtain ⟨c, C, hc, _hCnn, H⟩ :=
    Work.BMF.liouville.zetaTwSum_sub_main_le hreg hlog Work.BMF.liouville.zetaTwPerron_rect
  obtain ⟨C', hC'pos, hC'⟩ := vk_error_weaken_const c C hc
  have hlog3pos : 0 < Real.log 3 := Real.log_pos (by norm_num)
  refine ⟨c, max C' ((3 * Real.log 3 + 3) * Real.exp (c * Real.log 3 ^ (1 / 12 : ℝ)) + 1),
    hc, ?_⟩
  intro x hx2 u hu
  have hCpos : 0 < max C' ((3 * Real.log 3 + 3) * Real.exp (c * Real.log 3 ^ (1 / 12 : ℝ)) + 1) :=
    lt_of_lt_of_le hC'pos (le_max_left _ _)
  have hCle : C' ≤ max C' ((3 * Real.log 3 + 3) * Real.exp (c * Real.log 3 ^ (1 / 12 : ℝ)) + 1) :=
    le_max_left _ _
  by_cases hx3 : (3 : ℝ) ≤ x
  · -- `x ≥ 3`: the engine, with the exponent weakened from `1/10` to `1/12`
    have hlogx1 : 1 ≤ Real.log x := by
      have h3 : 1 ≤ Real.log 3 :=
        (Real.le_log_iff_exp_le (by norm_num)).mpr (le_of_lt Real.exp_one_lt_three)
      have h4 : Real.log 3 ≤ Real.log x := Real.log_le_log (by norm_num) hx3
      linarith
    have hle : |u| ≤ Real.exp ((Real.log x) ^ (5 / 4 : ℝ)) := by
      apply le_trans hu
      apply Real.exp_le_exp.mpr
      exact Real.rpow_le_rpow_of_exponent_le hlogx1 (by norm_num)
    have hexpeq : Real.exp (-(c * Real.log x ^ (1 / 10 : ℝ))) =
        Real.exp (-c * Real.log x ^ (1 / 10 : ℝ)) := by
      congr 1
      ring
    have hH : ‖Work.BMF.liouville.zetaTwSum u x -
        (x : ℂ) ^ (1 - Complex.I * (u : ℂ)) / (1 - Complex.I * (u : ℂ))‖
        ≤ C * x * Real.exp (-c * Real.log x ^ (1 / 10 : ℝ)) := by
      rw [← hexpeq]
      exact H x hx3 u hle
    have hH' : ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
            (n : ℂ) ^ (-(Complex.I * u)) -
          (x : ℂ) ^ (1 - Complex.I * u) / (1 - Complex.I * u)‖
        ≤ C * x * Real.exp (-c * Real.log x ^ (1 / 10 : ℝ)) := by
      simpa only [Work.BMF.liouville.zetaTwSum] using hH
    refine le_trans hH' ?_
    calc C * x * Real.exp (-c * Real.log x ^ (1 / 10 : ℝ))
        ≤ C' * x * Real.exp (-c * Real.log x ^ (1 / 12 : ℝ)) := hC' x hx2
      _ ≤ max C' ((3 * Real.log 3 + 3) * Real.exp (c * Real.log 3 ^ (1 / 12 : ℝ)) + 1) * x *
            Real.exp (-c * Real.log x ^ (1 / 12 : ℝ)) := by
          have hxpos : 0 < x := by linarith
          have h2 : C' * (x * Real.exp (-c * Real.log x ^ (1 / 12 : ℝ))) ≤
              max C' ((3 * Real.log 3 + 3) * Real.exp (c * Real.log 3 ^ (1 / 12 : ℝ)) + 1) *
                (x * Real.exp (-c * Real.log x ^ (1 / 12 : ℝ))) :=
            mul_le_mul_of_nonneg_right hCle (by positivity)
          calc C' * x * Real.exp (-c * Real.log x ^ (1 / 12 : ℝ))
              = C' * (x * Real.exp (-c * Real.log x ^ (1 / 12 : ℝ))) := by ring
            _ ≤ _ := h2
            _ = _ := by ring
  · -- `2 ≤ x < 3`: crude bounds
    push Not at hx3
    have hxpos : 0 < x := by linarith
    have hfloor3 : ⌊x⌋₊ ≤ 3 := by
      have h1 : ((⌊x⌋₊ : ℕ) : ℝ) < 3 := lt_of_le_of_lt (Nat.floor_le hxpos.le) hx3
      have h2 : (⌊x⌋₊ : ℕ) < 3 := by exact_mod_cast h1
      omega
    have hsum : ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
        (n : ℂ) ^ (-(Complex.I * u))‖ ≤ 3 * Real.log 3 := by
      have h1 := vk_norm_zetaTwSum_le u ⌊x⌋₊
      have h2 : ((⌊x⌋₊ : ℕ) : ℝ) * Real.log (⌊x⌋₊ : ℝ) ≤ 3 * Real.log 3 := by
        have hN3 : ((⌊x⌋₊ : ℕ) : ℝ) ≤ 3 := by exact_mod_cast hfloor3
        have hN1 : (1 : ℝ) ≤ ((⌊x⌋₊ : ℕ) : ℝ) := by
          have : 1 ≤ ⌊x⌋₊ := by
            have h2 : 2 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx2)
            omega
          exact_mod_cast this
        have hlog : Real.log (⌊x⌋₊ : ℝ) ≤ Real.log 3 := Real.log_le_log (by linarith) hN3
        have hnn : 0 ≤ Real.log (⌊x⌋₊ : ℝ) := Real.log_nonneg hN1
        have hNnn : 0 ≤ ((⌊x⌋₊ : ℕ) : ℝ) := by linarith
        nlinarith
      linarith
    have hmain : ‖(x : ℂ) ^ (1 - Complex.I * u) / (1 - Complex.I * u)‖ ≤ 3 :=
      le_trans (vk_norm_main_le hxpos.le u) hx3.le
    have hbd : ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
            (n : ℂ) ^ (-(Complex.I * u)) -
          (x : ℂ) ^ (1 - Complex.I * u) / (1 - Complex.I * u)‖ ≤ 3 * Real.log 3 + 3 :=
      le_trans (norm_sub_le _ _) (add_le_add hsum hmain)
    have hexp_ge : Real.exp (-c * Real.log 3 ^ (1 / 12 : ℝ)) ≤
        Real.exp (-c * Real.log x ^ (1 / 12 : ℝ)) := by
      apply Real.exp_le_exp.mpr
      have hpow : Real.log x ^ (1 / 12 : ℝ) ≤ Real.log 3 ^ (1 / 12 : ℝ) :=
        Real.rpow_le_rpow (Real.log_nonneg (by linarith))
          (Real.log_le_log (by linarith) hx3.le) (by norm_num)
      have := mul_le_mul_of_nonneg_left hpow hc.le
      linarith
    have hEpos : 0 < Real.exp (c * Real.log 3 ^ (1 / 12 : ℝ)) := Real.exp_pos _
    have hbig : (3 * Real.log 3 + 3) ≤
        (max C' ((3 * Real.log 3 + 3) * Real.exp (c * Real.log 3 ^ (1 / 12 : ℝ)) + 1)) * 2 *
          Real.exp (-c * Real.log 3 ^ (1 / 12 : ℝ)) := by
      have hle : (3 * Real.log 3 + 3) * Real.exp (c * Real.log 3 ^ (1 / 12 : ℝ)) ≤
          max C' ((3 * Real.log 3 + 3) * Real.exp (c * Real.log 3 ^ (1 / 12 : ℝ)) + 1) :=
        le_trans (le_add_of_nonneg_right zero_le_one) (le_max_right _ _)
      have h2 : (3 * Real.log 3 + 3) * Real.exp (c * Real.log 3 ^ (1 / 12 : ℝ)) *
            (2 * Real.exp (-c * Real.log 3 ^ (1 / 12 : ℝ))) =
          (3 * Real.log 3 + 3) * (2 * (Real.exp (c * Real.log 3 ^ (1 / 12 : ℝ)) *
            Real.exp (-c * Real.log 3 ^ (1 / 12 : ℝ)))) := by ring
      have h3 : Real.exp (c * Real.log 3 ^ (1 / 12 : ℝ)) *
          Real.exp (-c * Real.log 3 ^ (1 / 12 : ℝ)) = 1 := by
        rw [← Real.exp_add]
        norm_num
      rw [show (max C' ((3 * Real.log 3 + 3) * Real.exp (c * Real.log 3 ^ (1 / 12 : ℝ)) + 1)) * 2 *
          Real.exp (-c * Real.log 3 ^ (1 / 12 : ℝ)) =
          (max C' ((3 * Real.log 3 + 3) * Real.exp (c * Real.log 3 ^ (1 / 12 : ℝ)) + 1)) *
            (2 * Real.exp (-c * Real.log 3 ^ (1 / 12 : ℝ))) by ring]
      have h4 : 0 ≤ 2 * Real.exp (-c * Real.log 3 ^ (1 / 12 : ℝ)) := by positivity
      have h5 : (3 * Real.log 3 + 3) * Real.exp (c * Real.log 3 ^ (1 / 12 : ℝ)) *
            (2 * Real.exp (-c * Real.log 3 ^ (1 / 12 : ℝ))) ≤
          max C' ((3 * Real.log 3 + 3) * Real.exp (c * Real.log 3 ^ (1 / 12 : ℝ)) + 1) *
            (2 * Real.exp (-c * Real.log 3 ^ (1 / 12 : ℝ))) :=
        mul_le_mul_of_nonneg_right hle h4
      rw [h2, h3, mul_one] at h5
      have h6 : (3 * Real.log 3 + 3) ≤ 2 * (3 * Real.log 3 + 3) := by
        have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 3)
        linarith
      linarith [h5, h6, h4]
    have hfin : 3 * Real.log 3 + 3 ≤
        max C' ((3 * Real.log 3 + 3) * Real.exp (c * Real.log 3 ^ (1 / 12 : ℝ)) + 1) * x *
          Real.exp (-c * Real.log x ^ (1 / 12 : ℝ)) := by
      have h1 : (max C' ((3 * Real.log 3 + 3) * Real.exp (c * Real.log 3 ^ (1 / 12 : ℝ)) + 1)) * 2 *
          Real.exp (-c * Real.log 3 ^ (1 / 12 : ℝ)) ≤
          max C' ((3 * Real.log 3 + 3) * Real.exp (c * Real.log 3 ^ (1 / 12 : ℝ)) + 1) * x *
            Real.exp (-c * Real.log x ^ (1 / 12 : ℝ)) := by
        have h2 : 0 ≤ max C' ((3 * Real.log 3 + 3) * Real.exp (c * Real.log 3 ^ (1 / 12 : ℝ)) + 1) :=
          le_of_lt hCpos
        calc (max C' ((3 * Real.log 3 + 3) * Real.exp (c * Real.log 3 ^ (1 / 12 : ℝ)) + 1)) * 2 *
              Real.exp (-c * Real.log 3 ^ (1 / 12 : ℝ))
            = (max C' ((3 * Real.log 3 + 3) * Real.exp (c * Real.log 3 ^ (1 / 12 : ℝ)) + 1)) *
                (2 * Real.exp (-c * Real.log 3 ^ (1 / 12 : ℝ))) := by ring
          _ ≤ (max C' ((3 * Real.log 3 + 3) * Real.exp (c * Real.log 3 ^ (1 / 12 : ℝ)) + 1)) *
                (x * Real.exp (-c * Real.log x ^ (1 / 12 : ℝ))) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul hx2 hexp_ge (Real.exp_pos _).le (by linarith)) h2
          _ = (max C' ((3 * Real.log 3 + 3) * Real.exp (c * Real.log 3 ^ (1 / 12 : ℝ)) + 1)) * x *
                Real.exp (-c * Real.log x ^ (1 / 12 : ℝ)) := by ring
      linarith [hbig, h1]
    linarith [hbd, hfin]

/-- Version of `vk_norm_principal_sub_le` taking the character as a hypothesis. -/
lemma vk_norm_principal_sub_le' {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ = 1)
    (u : ℝ) (N : ℕ) :
    ‖(∑ n ∈ Finset.Icc 1 N, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ n *
          (n : ℂ) ^ (-(Complex.I * u))) -
        ∑ n ∈ Finset.Icc 1 N, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
          (n : ℂ) ^ (-(Complex.I * u))‖
      ≤ (q.primeFactors.card : ℝ) * Real.log N := by
  subst hχ
  exact vk_norm_principal_sub_le u N

/-- The core reduction: given the two sibling nodes, `vk_prime_sums` follows. -/
theorem vk_prime_sums_of (A : ℝ) (hA : 0 < A)
    (h6 : ∃ c C : ℝ, 0 < c ∧ ∀ (x : ℝ), 2 ≤ x → ∀ (u : ℝ),
      |u| ≤ Real.exp (Real.log x ^ (21 / 20 : ℝ)) →
        ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
            (n : ℂ) ^ (-(Complex.I * u)) - (x : ℂ) ^ (1 - Complex.I * u) / (1 - Complex.I * u)‖
          ≤ C * x * Real.exp (-c * Real.log x ^ (1 / 12 : ℝ)))
    (h7 : ∃ c C : ℝ, 0 < c ∧ ∀ (x : ℝ), 2 ≤ x → ∀ (q : ℕ) [NeZero q],
      (q : ℝ) ≤ Real.log x ^ A → ∀ (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ (u : ℝ),
        |u| ≤ Real.exp (Real.log x ^ (21 / 20 : ℝ)) →
          ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ n *
              (n : ℂ) ^ (-(Complex.I * u))‖
            ≤ C * x * Real.exp (-c * Real.log x ^ (1 / 12 : ℝ))) :
    ∃ c C : ℝ, 0 < c ∧ ∀ (x : ℝ), 2 ≤ x → ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ Real.log x ^ A →
      ∀ (χ : DirichletCharacter ℂ q) (u : ℝ), |u| ≤ Real.exp (Real.log x ^ (21 / 20 : ℝ)) →
        ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ n *
            (n : ℂ) ^ (-(Complex.I * u)) -
          (if χ = 1 then (x : ℂ) ^ (1 - Complex.I * u) / (1 - Complex.I * u) else 0)‖
          ≤ C * x * Real.exp (-c * Real.log x ^ (1 / 12 : ℝ)) := by
  obtain ⟨c6, C6, hc6, H6⟩ := h6
  obtain ⟨c7, C7, hc7, H7⟩ := h7
  set c : ℝ := min c6 c7 / 2 with hcdef
  have hcpos : 0 < c := by rw [hcdef]; positivity
  have hle6 : c ≤ c6 := by rw [hcdef]; have h := min_le_left c6 c7; linarith
  have hle7 : c ≤ c7 := by rw [hcdef]; have h := min_le_right c6 c7; linarith
  have h3log : 1 ≤ Real.log 3 :=
    (Real.le_log_iff_exp_le (by norm_num)).mpr (le_of_lt Real.exp_one_lt_three)
  have hlog3pos : 0 < Real.log 3 := lt_of_lt_of_le zero_lt_one h3log
  obtain ⟨Cp, hCppos, Hp⟩ := vk_omega_mul_log_le A c hA hcpos
  set E : ℝ := Real.exp (c * Real.log 3 ^ (1 / 12 : ℝ)) with hE
  have hEpos : 0 < E := by rw [hE]; exact Real.exp_pos _
  have hEnonneg : 0 ≤ E := le_of_lt hEpos
  have hE1 : 1 ≤ E := by
    rw [hE]
    exact Real.one_le_exp_iff.mpr (mul_nonneg hcpos.le (Real.rpow_nonneg hlog3pos.le _))
  have h3log3nonneg : 0 ≤ 3 * Real.log 3 + 3 := by linarith
  have hSEnonneg : 0 ≤ (3 * Real.log 3 + 3) * E := mul_nonneg h3log3nonneg hEnonneg
  set S : ℝ := |C6| + |C7| + Cp + 1 + (3 * Real.log 3 + 3) * E + 1 with hS
  have hSpos : 0 < S := by
    rw [hS]
    have h1 := abs_nonneg C6; have h2 := abs_nonneg C7
    linarith
  have hC6S : C6 ≤ S := by
    rw [hS]; have h1 := le_abs_self C6; have h2 := abs_nonneg C7; linarith
  have hC7S : C7 ≤ S := by
    rw [hS]; have h1 := le_abs_self C7; have h2 := abs_nonneg C6; linarith
  have hCpS : Cp ≤ S := by
    rw [hS]; have h1 := abs_nonneg C6; have h2 := abs_nonneg C7; linarith
  have hSES : (3 * Real.log 3 + 3) * E ≤ S := by
    rw [hS]; have h1 := abs_nonneg C6; have h2 := abs_nonneg C7; linarith
  set C₀ : ℝ := 16 * S with hC₀def
  have hC₀pos : 0 < C₀ := by rw [hC₀def]; linarith [hSpos]
  have hSC₀ : S ≤ C₀ := by rw [hC₀def]; linarith [hSpos]
  refine ⟨c, C₀, hcpos, ?_⟩
  intro x hx2 q _inst hq χ u hu
  by_cases hx3 : (3 : ℝ) ≤ x
  · -- ## the range `x ≥ 3`
    have hxpos : 0 < x := by linarith
    have hlogxpos : 0 < Real.log x := Real.log_pos (by linarith)
    have hlogxnonneg : 0 ≤ Real.log x := hlogxpos.le
    have hlogx1 : 1 ≤ Real.log x := by
      have h4 : Real.log 3 ≤ Real.log x := Real.log_le_log (by norm_num) hx3
      linarith
    have hpow12 : 0 ≤ Real.log x ^ (1 / 12 : ℝ) := Real.rpow_nonneg hlogxnonneg _
    have hεpos : 0 < Real.exp (-c * Real.log x ^ (1 / 12 : ℝ)) := Real.exp_pos _
    -- a general bound: `C ≤ S`, `c' ≤ c` give `C x exp(-c' ...) ≤ S x exp(-c ...)`
    have hbound_generic : ∀ C c' : ℝ, C ≤ S → c ≤ c' →
        C * x * Real.exp (-c' * Real.log x ^ (1 / 12 : ℝ)) ≤
          S * x * Real.exp (-c * Real.log x ^ (1 / 12 : ℝ)) := by
      intro C c' hCS hcc'
      have hε : Real.exp (-c' * Real.log x ^ (1 / 12 : ℝ)) ≤
          Real.exp (-c * Real.log x ^ (1 / 12 : ℝ)) := by
        apply Real.exp_le_exp.mpr
        have := mul_le_mul_of_nonneg_right hcc' hpow12
        linarith
      calc C * x * Real.exp (-c' * Real.log x ^ (1 / 12 : ℝ))
          = C * (x * Real.exp (-c' * Real.log x ^ (1 / 12 : ℝ))) := by ring
        _ ≤ S * (x * Real.exp (-c' * Real.log x ^ (1 / 12 : ℝ))) :=
            mul_le_mul_of_nonneg_right hCS (by positivity)
        _ ≤ S * (x * Real.exp (-c * Real.log x ^ (1 / 12 : ℝ))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hε hxpos.le) (le_of_lt hSpos)
        _ = S * x * Real.exp (-c * Real.log x ^ (1 / 12 : ℝ)) := by ring
    have hbound6 : C6 * x * Real.exp (-c6 * Real.log x ^ (1 / 12 : ℝ)) ≤
        S * x * Real.exp (-c * Real.log x ^ (1 / 12 : ℝ)) := hbound_generic C6 c6 hC6S hle6
    have hbound7 : C7 * x * Real.exp (-c7 * Real.log x ^ (1 / 12 : ℝ)) ≤
        S * x * Real.exp (-c * Real.log x ^ (1 / 12 : ℝ)) := hbound_generic C7 c7 hC7S hle7
    have hboundp : Cp * x * Real.exp (-c * Real.log x ^ (1 / 12 : ℝ)) ≤
        S * x * Real.exp (-c * Real.log x ^ (1 / 12 : ℝ)) := hbound_generic Cp c hCpS le_rfl
    have hSxC : S * x * Real.exp (-c * Real.log x ^ (1 / 12 : ℝ)) ≤
        C₀ * x * Real.exp (-c * Real.log x ^ (1 / 12 : ℝ)) := by
      calc S * x * Real.exp (-c * Real.log x ^ (1 / 12 : ℝ))
          = S * (x * Real.exp (-c * Real.log x ^ (1 / 12 : ℝ))) := by ring
        _ ≤ C₀ * (x * Real.exp (-c * Real.log x ^ (1 / 12 : ℝ))) :=
            mul_le_mul_of_nonneg_right hSC₀ (by positivity)
        _ = C₀ * x * Real.exp (-c * Real.log x ^ (1 / 12 : ℝ)) := by ring
    by_cases hχ : χ = 1
    · -- ## principal character
      have hsub : (if χ = 1 then (x : ℂ) ^ (1 - Complex.I * u) / (1 - Complex.I * u) else 0)
          = (x : ℂ) ^ (1 - Complex.I * u) / (1 - Complex.I * u) := if_pos hχ
      rw [hsub]
      have hkey : ‖(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
              χ n * (n : ℂ) ^ (-(Complex.I * u))) -
            ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
              (n : ℂ) ^ (-(Complex.I * u))‖
          ≤ Cp * x * Real.exp (-c * Real.log x ^ (1 / 12 : ℝ)) :=
        le_trans (le_trans (vk_norm_principal_sub_le' χ hχ u ⌊x⌋₊)
          (mul_le_mul_of_nonneg_left (vk_log_floor_le_log x (by linarith)) (by positivity)))
          (Hp x hx3 q hq)
      have h6le : ‖(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
              (n : ℂ) ^ (-(Complex.I * u))) -
            (x : ℂ) ^ (1 - Complex.I * u) / (1 - Complex.I * u)‖
          ≤ C6 * x * Real.exp (-c6 * Real.log x ^ (1 / 12 : ℝ)) := H6 x hx2 u hu
      have hsplit : (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
              χ n * (n : ℂ) ^ (-(Complex.I * u))) -
            (x : ℂ) ^ (1 - Complex.I * u) / (1 - Complex.I * u)
          = ((∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
              χ n * (n : ℂ) ^ (-(Complex.I * u))) -
            ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
              (n : ℂ) ^ (-(Complex.I * u))) +
            ((∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
              (n : ℂ) ^ (-(Complex.I * u))) -
            (x : ℂ) ^ (1 - Complex.I * u) / (1 - Complex.I * u)) := by abel
      calc ‖(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
              χ n * (n : ℂ) ^ (-(Complex.I * u))) -
            (x : ℂ) ^ (1 - Complex.I * u) / (1 - Complex.I * u)‖
          = ‖((∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
              χ n * (n : ℂ) ^ (-(Complex.I * u))) -
            ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
              (n : ℂ) ^ (-(Complex.I * u))) +
            ((∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
              (n : ℂ) ^ (-(Complex.I * u))) -
            (x : ℂ) ^ (1 - Complex.I * u) / (1 - Complex.I * u))‖ := by rw [hsplit]
        _ ≤ ‖(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
              χ n * (n : ℂ) ^ (-(Complex.I * u))) -
            ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
              (n : ℂ) ^ (-(Complex.I * u))‖
          + ‖(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
              (n : ℂ) ^ (-(Complex.I * u))) -
            (x : ℂ) ^ (1 - Complex.I * u) / (1 - Complex.I * u)‖ := norm_add_le _ _
        _ ≤ Cp * x * Real.exp (-c * Real.log x ^ (1 / 12 : ℝ)) +
            C6 * x * Real.exp (-c6 * Real.log x ^ (1 / 12 : ℝ)) := add_le_add hkey h6le
        _ ≤ S * x * Real.exp (-c * Real.log x ^ (1 / 12 : ℝ)) +
            S * x * Real.exp (-c * Real.log x ^ (1 / 12 : ℝ)) := add_le_add hboundp hbound6
        _ ≤ C₀ * x * Real.exp (-c * Real.log x ^ (1 / 12 : ℝ)) := by
            have := hSxC
            linarith
    · -- ## non-principal character
      have hsub : (if χ = 1 then (x : ℂ) ^ (1 - Complex.I * u) / (1 - Complex.I * u)
          else 0) = 0 := if_neg hχ
      rw [hsub, sub_zero]
      exact le_trans (H7 x hx2 q hq χ hχ u hu) (le_trans hbound7 hSxC)
  · -- ## the range `x < 3`: crude bounds, absorbed into the constant
    push Not at hx3
    have hxpos : 0 < x := by linarith
    have hfloor1 : 1 ≤ ⌊x⌋₊ := by
      have h2 : 2 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx2)
      omega
    have hfloorlt : ⌊x⌋₊ < 3 := by
      have h1 : ((⌊x⌋₊ : ℕ) : ℝ) < 3 := lt_of_le_of_lt (Nat.floor_le hxpos.le) hx3
      exact_mod_cast h1
    have hsum : ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ n *
          (n : ℂ) ^ (-(Complex.I * u))‖ ≤ 3 * Real.log 3 := by
      have h1 := vk_norm_twisted_sum_le χ u ⌊x⌋₊
      have h2 : ((⌊x⌋₊ : ℕ) : ℝ) * Real.log (⌊x⌋₊ : ℝ) ≤ 3 * Real.log 3 := by
        have hN3 : ((⌊x⌋₊ : ℕ) : ℝ) ≤ 3 := by
          have : ⌊x⌋₊ ≤ 3 := by omega
          exact_mod_cast this
        have hN1 : (1 : ℝ) ≤ ((⌊x⌋₊ : ℕ) : ℝ) := by exact_mod_cast hfloor1
        have hlog : Real.log (⌊x⌋₊ : ℝ) ≤ Real.log 3 := Real.log_le_log (by linarith) hN3
        have hnn : 0 ≤ Real.log (⌊x⌋₊ : ℝ) := Real.log_nonneg hN1
        have hNnn : 0 ≤ ((⌊x⌋₊ : ℕ) : ℝ) := by linarith
        nlinarith
      linarith
    have hmain : ‖(if χ = 1 then (x : ℂ) ^ (1 - Complex.I * u) / (1 - Complex.I * u)
        else 0)‖ ≤ 3 := by
      by_cases hχ : χ = 1
      · rw [if_pos hχ]
        exact le_trans (vk_norm_main_le hxpos.le u) hx3.le
      · rw [if_neg hχ, norm_zero]
        positivity
    have hbd : ‖(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ n *
          (n : ℂ) ^ (-(Complex.I * u))) -
          (if χ = 1 then (x : ℂ) ^ (1 - Complex.I * u) / (1 - Complex.I * u) else 0)‖
        ≤ 3 * Real.log 3 + 3 :=
      le_trans (norm_sub_le _ _) (add_le_add hsum hmain)
    have hε : 1 / E ≤ Real.exp (-c * Real.log x ^ (1 / 12 : ℝ)) := by
      rw [hE, vk_one_div_exp]
      apply Real.exp_le_exp.mpr
      have hpow : Real.log x ^ (1 / 12 : ℝ) ≤ Real.log 3 ^ (1 / 12 : ℝ) :=
        Real.rpow_le_rpow (Real.log_nonneg (by linarith))
          (Real.log_le_log (by linarith) hx3.le) (by norm_num)
      have := mul_le_mul_of_nonneg_left hpow hcpos.le
      linarith
    have hmid : 3 * Real.log 3 + 3 ≤ 16 * ((3 * Real.log 3 + 3) * E) * (2 * (1 / E)) := by
      have hA : 16 * ((3 * Real.log 3 + 3) * E) * (2 * (1 / E)) =
          32 * (3 * Real.log 3 + 3) := by
        field_simp
        ring
      rw [hA]
      nlinarith [h3log3nonneg]
    have hstep1 : 16 * ((3 * Real.log 3 + 3) * E) * (2 * (1 / E)) ≤
        16 * S * (x * Real.exp (-c * Real.log x ^ (1 / 12 : ℝ))) := by
      have ha : 16 * ((3 * Real.log 3 + 3) * E) ≤ 16 * S := by linarith [hSES]
      have hb : 2 * (1 / E) ≤ x * Real.exp (-c * Real.log x ^ (1 / 12 : ℝ)) :=
        mul_le_mul hx2 hε (by positivity) (by linarith)
      exact mul_le_mul ha hb (by positivity) (by positivity)
    have hstep2 : 16 * S * (x * Real.exp (-c * Real.log x ^ (1 / 12 : ℝ))) =
        C₀ * x * Real.exp (-c * Real.log x ^ (1 / 12 : ℝ)) := by
      rw [hC₀def]
      ring
    linarith [hbd, hmid, hstep1, hstep2]


/-! ## The target theorem

The proof below assembles the two halves.

* `χ = 1`: the `ζ`-box (`vk_zeta_box_statement`) is built here from the Richert/VK strip growth of
  `ζ` (`Work.BMF.zpt.zeta_growth_strip`, fed by the VK exponential-sum bound of
  `Work.BMF.znl.vk_exp_sum_ford` through `Work.BMF.zeta_partial_sum_bound` and
  `Work.BMF.zeta_approx_functional_eq`), the zero-free region
  `Work.BMF.zeta_VK_zeroFree_of_growth` and the logarithmic-derivative bound
  `Work.BMF.zeta_logDeriv_bound_vk`; `vk_zeta_pnt_of_box` then gives the twisted PNT for `ζ`.
* `χ ≠ 1`: `Work.BMF.VKPrimeSums.logDeriv_LVK_of_zeroFree` turns the zero-free region of the
  `L`-functions (`Work.BMF.LFunction_zeroFree_VK_of_growth`, i.e. the node V3 with its `L`-growth
  input taken as a hypothesis) together with the low-height region `LFunction_lowHeight` into the
  `hhigh`/`hlow` inputs of `Work.BMF.VKPrimeSums.chi_pnt_of_box`.
-/

/-- **N10 (restated range `21/20`).** As before, but with `|u| ≤ exp((log x)^{21/20})` instead of
`exp((log x)^{5/4})`. The weaker range is what the explicit-constant route (V0–V7) delivers, and
every consumer (N4, N7, N9, N11, N4a) stays inside it. Proof: `χ = 1` via V6, after replacing
the principal character mod `q` by `ζ` at cost `≤ ω(q) log x`; `χ ≠ 1` via V7. -/
theorem vk_prime_sums (A : ℝ) (hA : 0 < A) :
    ∃ c C : ℝ, 0 < c ∧ ∀ (x : ℝ), 2 ≤ x → ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ Real.log x ^ A →
      ∀ (χ : DirichletCharacter ℂ q) (u : ℝ), |u| ≤ Real.exp (Real.log x ^ (21 / 20 : ℝ)) →
        ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ n *
            (n : ℂ) ^ (-(Complex.I * u)) -
          (if χ = 1 then (x : ℂ) ^ (1 - Complex.I * u) / (1 - Complex.I * u) else 0)‖
          ≤ C * x * Real.exp (-c * Real.log x ^ (1 / 12 : ℝ)) := by
  -- **(V1)** the Vinogradov–Korobov exponential-sum bound, assembled in
  -- `Work.BMF.VKPrimeSums.vkExpSum_clean` from `Work.BMF.VKExpSum.weyl_small_lambda`
  -- (`λ ≤ 13/5`) and `Work.BMF.VKF.vkf_deep` (`λ ≥ 13/5`), with the trivial regime.
  obtain ⟨CVK, DVK, hCVK, hDVK, hVK⟩ := Work.BMF.VKPrimeSums.vkExpSum_clean
  -- **(V2)** growth of `L(s,χ)` in the VK strip: the shifted partial-sum bound and the `ζ`-bound
  -- in the region (`Work.BMF.VKPrimeSums.shifted_partial_sum_bound`,
  -- `Work.BMF.VKPrimeSums.zeta_norm_le_region`) feed `Work.BMF.VKPrimeSums.vk_L_growth`.
  obtain ⟨Ash, csh, hAsh, hcsh, hsh⟩ :=
    Work.BMF.VKPrimeSums.shifted_partial_sum_bound CVK DVK hCVK hDVK hVK
  obtain ⟨Az, cz, hAz, hcz, hz⟩ :=
    Work.BMF.VKPrimeSums.zeta_norm_le_region2 CVK DVK hCVK hDVK hVK
  obtain ⟨Alg, clg, hAlg, hclg, hLgr⟩ :=
    Work.BMF.VKPrimeSums.vk_L_growth ⟨Ash, csh, hAsh, hcsh, hsh⟩ ⟨Az, cz, hAz, hcz, hz⟩
  have hV2' : VKGrowth Alg clg := ⟨hAlg, hclg, hLgr⟩
  -- **(V3)** the zero-free region of VK type for primitive characters.
  obtain ⟨cZ, hcZ, hZ⟩ := Work.BMF.LFunction_zeroFree_VK_of_growth ⟨Alg, clg, hV2'⟩
  have hzf : ∃ c : ℝ, 0 < c ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
      χ.IsPrimitive → χ ≠ 1 → ∀ σ t : ℝ, 3 ≤ |t| →
        1 - c / (Real.log (|t| + 3) ^ (6 / 7 : ℝ) *
          (Real.log ((N : ℝ) + 2) + Real.log (Real.log (|t| + 3)))) ≤ σ →
        DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 :=
    ⟨cZ, hcZ, fun N _inst χ hp _hne σ t ht hσ => hZ N χ hp σ t ht hσ⟩
  -- **(V6)** the `ζ`-box: the VK zero-free region for `ζ` and the `ζ′/ζ`-bound in it.
  have hzetaBox : vk_zeta_box_statement := by
    obtain ⟨Agr, Bgr, hAgr, hBgr, hgr⟩ :=
      Work.BMF.zpt.zeta_growth_strip ⟨CVK, DVK, hCVK, hDVK, hVK⟩
        (fun C D hC hD hV => Work.BMF.zeta_partial_sum_bound C D hC hD hV)
        Work.BMF.zeta_approx_functional_eq
    obtain ⟨c₁, hc₁, hz₁⟩ := Work.BMF.zeta_VK_zeroFree_of_growth ⟨Agr, Bgr, hAgr, hBgr, hgr⟩
    refine ⟨⟨c₁, hc₁, fun t σ ht hσ _hσ1 =>
        hz₁ σ t ht (by simpa only [Work.BMF.VKd_def] using hσ)⟩, ?_⟩
    exact Work.BMF.zeta_logDeriv_bound_vk c₁ hc₁
      (fun t σ ht hσ _hσ1 => hz₁ σ t ht (by simpa only [Work.BMF.VKd_def] using hσ))
  have h6 := vk_zeta_pnt_of_box hzetaBox
  -- **(V4)+(V5)+(V7)** the twisted PNT for `χ ≠ 1` (the V7 node, with its zero-free input).
  have h7 := Work.BMF.chi_prime_sum_twist_of_zeroFree A hA hzf
  exact vk_prime_sums_of A hA h6 h7

end Work.BMF
