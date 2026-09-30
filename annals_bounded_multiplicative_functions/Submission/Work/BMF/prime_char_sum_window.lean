import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.vk_prime_sums
import Submission.Work.BMF.Ioc_filter_prime_subset_primesIn
import Submission.Work.BMF.primesIn_sdiff_card_le_one
import Submission.Work.BMF.pcsw.abel_inv_log_identity
import Submission.Work.BMF.pcsw.intervalIntegrable_step_sum_mul
import Submission.Work.BMF.pcsw.prime_vonMangoldt_log_diff
import Submission.Work.BMF.pcsw.integral_cpow_div_log_identity
import Submission.Work.BMF.pcsw.absorb_terms

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! Guidance from the project lead (the requester):

LEAD NOTE (re-dispatch, AMENDED statement; see DESIGN.md 'Addendum: V0 exponent'). The statement
file imports only Defs, because some siblings do not build yet. For the PROOF, add these imports
to your file once they build: Submission.Work.BMF.Defs, Submission.Work.BMF.vk_prime_sums.

# N4a: the `[P,2P]` prime-character sum from the twisted PNT (N10)

## Statement

`Work.BMF.prime_char_sum_window` (verbatim as requested, unchanged): for every `A > 0` there are
`c, C, P₀` with `c > 0` such that for `P ≥ P₀`, every `q ≥ 1` with `q ≤ (log P)^A`, every
character `χ` mod `q` and every `|t| ≤ exp((log P)^{21/20})`,
`‖Σ_{p ∈ primesIn P (2P)} χ(p) p^{it} − (χ = 1 ? ∫_P^{2P} v^{it}/log v dv : 0)‖ ≤ C P e^{−c(log P)^{1/12}}`.

## Proof (complete, no unproved placeholder in this file)

N10 (`Work.BMF.vk_prime_sums`) with twist `u = −t` supplies, for every `x ≥ 2`,
`‖Λ_S(x) − M(x)‖ ≤ C₁ x e^{−c₁(log x)^{1/12}}`, where `Λ_S(x) = Σ_{n ≤ ⌊x⌋₊} Λ(n) χ(n) n^{it}` and
`M(x) = (χ = 1 ? x^{1+it}/(1+it) : 0)` (lemma `EtW_bound`). Partial summation with the weight
`1/log v` (the five `pcsw` pieces below) then gives
`Σ_{⌊P⌋₊ < k ≤ ⌊2P⌋₊} Λ(k)χ(k)k^{it}/log k = ∫_P^{2P} v^{it}/log v dv + (error terms)`
for `χ = 1`, and `= 0 + (error terms)` for `χ ≠ 1`; the left side is the prime sum plus the
proper prime powers (`prime_vonMangoldt_log_diff`). The one-prime discrepancy between
`primesIn P (2P)` and the primes of `(⌊P⌋₊, ⌊2P⌋₊]` is `< 1`
(`Ioc_filter_prime_subset_primesIn`, `primesIn_sdiff_card_le_one`), and `absorb_terms` (with
`K = 4·Cpp + 3·|C₁|`) turns the resulting sub-polynomial error into `C P e^{−(c₁/2)(log P)^{1/12}}`.

## Pieces (all proved, all axiom-clean: only `propext`, `Classical.choice`, `Quot.sound`)

* `Work.BMF.pcsw.abel_inv_log_identity` — Abel summation, weight `1/log`;
* `Work.BMF.pcsw.intervalIntegrable_step_sum_mul` — integrability of the prefix-sum integrand;
* `Work.BMF.pcsw.prime_vonMangoldt_log_diff` — `1/log`-weighted von Mangoldt sum vs prime sum,
  error `≪ √M log M`;
* `Work.BMF.pcsw.integral_cpow_div_log_identity` — integration by parts: the main term is
  `∫_P^{2P} v^{it}/log v dv`;
* `Work.BMF.pcsw.absorb_terms` — sub-polynomial absorption.

Everything else (the `‖·‖ ≤ 1` prime discrepancy, `EtW_bound`, the integrability of the main-term
integrand, the algebra of the decomposition and all the constant arithmetic) is proved in this
file.

## Verification status (2026-09-27)

`lake build Submission.Work.BMF.prime_char_sum_window` succeeds; the file contains no unproved placeholder. The only obstacle to `declare_proven()` is that `Work.BMF.vk_prime_sums` (N10) still contains one
unproved placeholder (an unproved hole), so
this theorem's axiom closure contains the placeholder axiom:

    FAIL: `Work.BMF.prime_char_sum_window` depends on forbidden axioms ['the placeholder axiom'].

The VK chain behind N10 is being proved in parallel by other nodes. As of 08:40 the state is:

* `Work.BMF.vk_prime_sums_of` (in `vk_prime_sums.lean`) is proved and axiom-clean; it turns the
  `χ = 1` and `χ ≠ 1` twisted PNT (range `21/20`, error `1/12`) into N10. The final line of
  `vk_prime_sums` still ends in an unproved placeholder.
* `zeta_prime_sum_twist` (V6) is placeholder-free but inherits the placeholder axiom through
  `logDeriv_LFunction_VK` (V4); `chi_prime_sum_twist` (V7) is still incomplete (only
  `v7chi_primitive_reduction` is proved).
* `LFunction_zeroFree_VK` (V3) has a single unproved hole near its end (line ≈ 524).
* `L_growth_VK` (V2), `vk_exp_sum` (V1) and `logDeriv_LFunction_VK` (V4) are entire theorems
  entirely unproved — V1 is the root of the chain (`vmvt_uniform` (V0) and
  `kth_derivative_reduction_uniform` (V1a) are proved).
* Clean conditional reductions exist in `Submission/Work/BMF/N4chain/`:
  `zeta_twisted_pnt_of : LogDerivLVK → ZetaTwistedPNT` and
  `logDeriv_L_VK_of : LZeroFreeVK → LGrowthVK → LogDerivLVK`.

So this node needs NO further mathematical work: re-run `declare_proven()` once
`Work.BMF.vk_prime_sums` is axiom-clean. (I checked that the deep input is genuinely needed: the
large-`t` range cannot be covered by elementary oscillation bounds, because the prefix function
`Λ_S(x) − M(x)` carries a factor `|t|` in the Abel identity; a zero-free region of some exponent
`κ < 20/21` is required, and `N4chain/zeta_twisted_pnt_of` shows Ford-quality inputs would also
do for `χ = 1`.)
-/

namespace Work.BMF

open Finset Real
open scoped BigOperators

set_option maxHeartbeats 4000000

noncomputable section


/-! ## The twisted von Mangoldt sequence and its prefix sums -/

/-- The twisted von Mangoldt summand `Λ(n) χ(n) n^{it}`. -/
private def gTw (q : ℕ) (χ : DirichletCharacter ℂ q) (t : ℝ) (n : ℕ) : ℂ :=
  ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ n * (n : ℂ) ^ (Complex.I * t)

/-- The same sequence with the `n = 0` term set to `0`, so that prefix sums starting at `0`
agree with those starting at `1`. -/
private def cTw (q : ℕ) (χ : DirichletCharacter ℂ q) (t : ℝ) : ℕ → ℂ :=
  fun n => if n = 0 then 0 else gTw q χ t n

/-- The prefix-sum step function `C(t) = Σ_{k ≤ ⌊t⌋₊} c k`. -/
private def CtW (q : ℕ) (χ : DirichletCharacter ℂ q) (t : ℝ) (v : ℝ) : ℂ :=
  ∑ k ∈ Finset.Icc 0 ⌊v⌋₊, cTw q χ t k

/-- The expected main term of the twisted von Mangoldt sum. -/
private def MtW (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ) (v : ℝ) : ℂ :=
  if χ = 1 then (v : ℂ) ^ (1 + Complex.I * t) / (1 + Complex.I * t) else 0

/-- The weight `(v (log v)^2)^{-1}` appearing in the Abel/Stieltjes formula. -/
private def Wt (v : ℝ) : ℂ := (((v * (Real.log v) ^ 2 : ℝ)) : ℂ)⁻¹

/-- The error term of the twisted von Mangoldt sum. -/
private def EtW (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ) (v : ℝ) : ℂ :=
  CtW q χ t v - MtW q χ t v

/-- Prefix sums over `Icc 0` agree with sums over `Icc 1`. -/
private lemma CtW_eq (q : ℕ) (χ : DirichletCharacter ℂ q) (t v : ℝ) :
    CtW q χ t v = ∑ n ∈ Finset.Icc 1 ⌊v⌋₊, gTw q χ t n := by
  simp only [CtW, cTw]
  rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le _), Finset.sum_cons, if_pos rfl, zero_add]
  have hIoc : Finset.Ioc 0 ⌊v⌋₊ = Finset.Icc 1 ⌊v⌋₊ := by
    simpa using (Finset.Icc_add_one_left_eq_Ioc 0 ⌊v⌋₊).symm
  rw [hIoc]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [if_neg]
  intro h
  subst h
  exact absurd (Finset.mem_Icc.mp hk).1 (by omega)

/-- `‖χ n · n^{it}‖ ≤ 1` for `n ≥ 1`. -/
private lemma norm_char_cpow_le_one (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ)
    {n : ℕ} (hn : 1 ≤ n) : ‖χ n * (n : ℂ) ^ (Complex.I * t)‖ ≤ 1 := by
  have h1 : ‖(n : ℂ) ^ (Complex.I * t)‖ = 1 := by
    rw [Complex.norm_natCast_cpow_of_pos (by omega : 0 < n)]
    have hre : (Complex.I * (t : ℂ)).re = 0 := by simp
    rw [hre, Real.rpow_zero]
  calc ‖χ n * (n : ℂ) ^ (Complex.I * t)‖ = ‖χ n‖ := by rw [norm_mul, h1, mul_one]
    _ ≤ 1 := DirichletCharacter.norm_le_one χ n

/-- The target prime sum over `primesIn P (2P)` differs from the sum over the primes of
`(⌊P⌋₊, ⌊2P⌋₊]` by at most `1` (at most one prime, namely `⌈P⌉₊`, is dropped). -/
private lemma norm_primesIn_sub_Iocfilter_le (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (t P : ℝ) :
    ‖(∑ p ∈ primesIn P (2 * P), χ p * (p : ℂ) ^ (Complex.I * t))
      - (∑ p ∈ (Finset.Ioc ⌊P⌋₊ ⌊2 * P⌋₊).filter Nat.Prime,
          χ p * (p : ℂ) ^ (Complex.I * t))‖ ≤ 1 := by
  classical
  set S : Finset ℕ := primesIn P (2 * P) with hS
  set T : Finset ℕ := (Finset.Ioc ⌊P⌋₊ ⌊2 * P⌋₊).filter Nat.Prime with hT
  have hTS : T ⊆ S := Ioc_filter_prime_subset_primesIn P
  have hcard : (S \ T).card ≤ 1 := primesIn_sdiff_card_le_one P
  have hsum : (∑ p ∈ S, χ p * (p : ℂ) ^ (Complex.I * t))
      = (∑ p ∈ S \ T, χ p * (p : ℂ) ^ (Complex.I * t))
        + (∑ p ∈ T, χ p * (p : ℂ) ^ (Complex.I * t)) := by
    have h := Finset.sum_sdiff hTS (f := fun p : ℕ => χ p * (p : ℂ) ^ (Complex.I * t))
    exact h.symm
  have hdiff : (∑ p ∈ S, χ p * (p : ℂ) ^ (Complex.I * t))
      - (∑ p ∈ T, χ p * (p : ℂ) ^ (Complex.I * t))
      = ∑ p ∈ S \ T, χ p * (p : ℂ) ^ (Complex.I * t) := by
    rw [hsum]; ring
  rw [hdiff]
  have hbound : ‖∑ p ∈ S \ T, χ p * (p : ℂ) ^ (Complex.I * t)‖ ≤ ((S \ T).card : ℝ) := by
    calc ‖∑ p ∈ S \ T, χ p * (p : ℂ) ^ (Complex.I * t)‖
        ≤ ∑ p ∈ S \ T, ‖χ p * (p : ℂ) ^ (Complex.I * t)‖ := norm_sum_le _ _
      _ ≤ ∑ _p ∈ S \ T, (1 : ℝ) := by
          refine Finset.sum_le_sum fun p hp => ?_
          refine norm_char_cpow_le_one q χ t ?_
          have hpS : p ∈ S := (Finset.mem_sdiff.mp hp).1
          exact (Finset.mem_filter.mp hpS).2.one_le
      _ = ((S \ T).card : ℝ) := by simp
  refine le_trans hbound ?_
  exact_mod_cast hcard

/-! ## The error term is bounded by N10 -/

/-- N10 (`vk_prime_sums`) applied with twist `u = -t` bounds the error term `E(x)`. -/
private lemma EtW_bound (A : ℝ) (hA : 0 < A) (c₁ C₁ : ℝ) (hc₁ : 0 < c₁)
    (hT : ∀ (x : ℝ), 2 ≤ x → ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ Real.log x ^ A →
      ∀ (χ : DirichletCharacter ℂ q) (u : ℝ), |u| ≤ Real.exp (Real.log x ^ (21 / 20 : ℝ)) →
        ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ n *
            (n : ℂ) ^ (-(Complex.I * (u : ℂ))) -
          (if χ = 1 then (x : ℂ) ^ (1 - Complex.I * (u : ℂ)) /
            (1 - Complex.I * (u : ℂ)) else 0)‖
          ≤ C₁ * x * Real.exp (-c₁ * Real.log x ^ (1 / 12 : ℝ)))
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (t x : ℝ) (hx : 2 ≤ x)
    (hq : (q : ℝ) ≤ Real.log x ^ A)
    (ht : |t| ≤ Real.exp (Real.log x ^ (21 / 20 : ℝ))) :
    ‖EtW q χ t x‖ ≤ |C₁| * x * Real.exp (-c₁ * Real.log x ^ (1 / 12 : ℝ)) := by
  have h := hT x hx q hq χ (-t) (by rwa [abs_neg])
  have hexp1 : -(Complex.I * ((-t : ℝ) : ℂ)) = Complex.I * (t : ℂ) := by push_cast; ring
  have hexp2 : (1 : ℂ) - Complex.I * ((-t : ℝ) : ℂ) = 1 + Complex.I * (t : ℂ) := by
    push_cast; ring
  rw [hexp1, hexp2] at h
  rw [EtW, CtW_eq, MtW]
  refine le_trans h ?_
  have hz : (0 : ℝ) ≤ x * Real.exp (-c₁ * Real.log x ^ (1 / 12 : ℝ)) := by positivity
  calc C₁ * x * Real.exp (-c₁ * Real.log x ^ (1 / 12 : ℝ))
      = C₁ * (x * Real.exp (-c₁ * Real.log x ^ (1 / 12 : ℝ))) := by ring
    _ ≤ |C₁| * (x * Real.exp (-c₁ * Real.log x ^ (1 / 12 : ℝ))) :=
        mul_le_mul_of_nonneg_right (le_abs_self C₁) hz
    _ = |C₁| * x * Real.exp (-c₁ * Real.log x ^ (1 / 12 : ℝ)) := by ring

/-! ## Integrability of the main-term integrand -/

/-- `v ↦ M(v) · (v (log v)^2)^{-1}` is continuous on `[P, 2P]` (for `P > 0`), hence
interval-integrable; this is what allows splitting the Abel integral into its main and error
parts. -/
private lemma intervalIntegrable_MtW_Wt (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (t P : ℝ)
    (hP : 1 < P) :
    IntervalIntegrable (fun v : ℝ => MtW q χ t v * Wt v) MeasureTheory.volume P (2 * P) := by
  by_cases hχ : χ = 1
  · have hcont : ContinuousOn (fun v : ℝ => MtW q χ t v * Wt v) (Set.Icc P (2 * P)) := by
      have hfun : (fun v : ℝ => MtW q χ t v * Wt v) = fun v : ℝ =>
          (v : ℂ) ^ (1 + Complex.I * t) / (1 + Complex.I * t) *
            (((v * (Real.log v) ^ 2 : ℝ)) : ℂ)⁻¹ := by
        funext v; simp only [MtW, Wt, hχ, if_true]
      rw [hfun]
      refine ContinuousOn.mul ?_ ?_
      · refine ContinuousOn.div ?_ continuousOn_const ?_
        · refine fun x hx =>
            (Complex.continuousAt_ofReal_cpow_const x _ (Or.inl (by simp))).continuousWithinAt
        · intro x hx hcon
          have hre := congrArg Complex.re hcon
          simp at hre
      · refine ContinuousOn.inv₀ ?_ ?_
        · refine Complex.continuous_ofReal.comp_continuousOn ?_
          refine ContinuousOn.mul continuousOn_id ?_
          refine ContinuousOn.pow ?_ 2
          refine Real.continuousOn_log.mono ?_
          intro x hx
          simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
          exact ne_of_gt (lt_of_lt_of_le (by linarith : (0:ℝ) < P) hx.1)
        · intro x hx
          refine Complex.ofReal_ne_zero.mpr ?_
          have hx1 : P ≤ x := hx.1
          have hx0 : 0 < x := by linarith
          have hlx : 0 < Real.log x := Real.log_pos (by linarith)
          exact ne_of_gt (mul_pos hx0 (pow_pos hlx 2))
    have hcont' : ContinuousOn (fun v : ℝ => MtW q χ t v * Wt v) (Set.uIcc P (2 * P)) := by
      rw [Set.uIcc_of_le (by linarith : P ≤ 2 * P)]
      exact hcont
    exact hcont'.intervalIntegrable
  · have hfun : (fun v : ℝ => MtW q χ t v * Wt v) = fun _ => (0 : ℂ) := by
      funext v; simp [MtW, hχ]
    rw [hfun]
    exact continuousOn_const.intervalIntegrable

/-! ## The main theorem -/

/-- **N4a (restated range `21/20`).** -/
theorem prime_char_sum_window (A : ℝ) (hA : 0 < A) :
    ∃ c C P₀ : ℝ, 0 < c ∧ ∀ P : ℝ, P₀ ≤ P → ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ Real.log P ^ A →
      ∀ (χ : DirichletCharacter ℂ q) (t : ℝ), |t| ≤ Real.exp (Real.log P ^ (21 / 20 : ℝ)) →
        ‖∑ p ∈ primesIn P (2 * P), χ p * (p : ℂ) ^ (Complex.I * t) -
          (if χ = 1 then ∫ v in P..(2 * P), (v : ℂ) ^ (Complex.I * t) / (Real.log v : ℂ) else 0)‖
          ≤ C * P * Real.exp (-c * Real.log P ^ (1 / 12 : ℝ)) := by
  classical
  obtain ⟨c₁, C₁, hc₁, hT⟩ := vk_prime_sums A hA
  obtain ⟨Cpp, hCpppos, hCpp⟩ := pcsw.prime_vonMangoldt_log_diff
  have hKnn : (0 : ℝ) ≤ 4 * Cpp + 3 * |C₁| := by positivity
  obtain ⟨Cab, _hCab8, hAbLE⟩ := pcsw.absorb_terms c₁ (4 * Cpp + 3 * |C₁|) hc₁ hKnn
  refine ⟨c₁ / 2, 4 * Cpp + 3 * |C₁| + 1, max Cab 8, by linarith, ?_⟩
  intro P hP q _ hq χ t ht
  have hP8 : 8 ≤ P := le_trans (le_max_right _ _) hP
  have hPCab : Cab ≤ P := le_trans (le_max_left _ _) hP
  have hP0 : 0 < P := by linarith
  have hP1 : 1 < P := by linarith
  have hP2 : 2 ≤ P := by linarith
  have hPle2 : P ≤ 2 * P := by linarith
  have hlogP : 0 < Real.log P := Real.log_pos (by linarith)
  have hlog2P : Real.log P ≤ Real.log (2 * P) := Real.log_le_log hP0 hPle2
  have hlog2Ppos : 0 < Real.log (2 * P) := lt_of_lt_of_le hlogP hlog2P
  set ee : ℝ := Real.exp (-c₁ * Real.log P ^ (1 / 12 : ℝ)) with hee
  have heepos : 0 < ee := Real.exp_pos _
  have hexp2P : Real.exp (-c₁ * Real.log (2 * P) ^ (1 / 12 : ℝ)) ≤ ee := by
    rw [hee]
    refine Real.exp_le_exp.mpr ?_
    have h : Real.log P ^ (1 / 12 : ℝ) ≤ Real.log (2 * P) ^ (1 / 12 : ℝ) :=
      Real.rpow_le_rpow hlogP.le hlog2P (by norm_num)
    nlinarith [hc₁, h]
  set K₁ : ℝ := |C₁| with hK₁
  have hK₁nn : 0 ≤ K₁ := by rw [hK₁]; exact abs_nonneg _
  have hB2 : 2 ≤ ⌊2 * P⌋₊ := Nat.le_floor (by push_cast; linarith)
  have hBle : (⌊2 * P⌋₊ : ℝ) ≤ 2 * P := Nat.floor_le (by linarith)
  have hlogBle : Real.log (⌊2 * P⌋₊ : ℝ) ≤ 2 * Real.log P := by
    have h1 : Real.log (⌊2 * P⌋₊ : ℝ) ≤ Real.log (2 * P) :=
      Real.log_le_log (by positivity) hBle
    have h2 : Real.log (2 * P) = Real.log 2 + Real.log P :=
      Real.log_mul (by norm_num) (ne_of_gt hP0)
    have h3 : Real.log 2 ≤ Real.log P := Real.log_le_log (by norm_num) (by linarith)
    linarith
  have hsqrtB : Real.sqrt (⌊2 * P⌋₊ : ℝ) ≤ 2 * Real.sqrt P := by
    have h1 : Real.sqrt (⌊2 * P⌋₊ : ℝ) ≤ Real.sqrt (2 * P) := Real.sqrt_le_sqrt hBle
    have h2 : Real.sqrt (2 * P) = Real.sqrt 2 * Real.sqrt P := Real.sqrt_mul (by norm_num) P
    have h3 : Real.sqrt 2 ≤ 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
    rw [h2] at h1
    nlinarith [Real.sqrt_nonneg P]
  -- N10 bounds the error term
  have hErr : ∀ x : ℝ, P ≤ x → ‖EtW q χ t x‖ ≤ K₁ * x * Real.exp (-c₁ * Real.log x ^ (1 / 12 : ℝ)) := by
    intro x hPx
    have hx2 : 2 ≤ x := le_trans hP2 hPx
    have hxle : Real.log P ≤ Real.log x := Real.log_le_log hP0 hPx
    have hqx : (q : ℝ) ≤ Real.log x ^ A :=
      le_trans hq (Real.rpow_le_rpow hlogP.le hxle hA.le)
    have htx : |t| ≤ Real.exp (Real.log x ^ (21 / 20 : ℝ)) :=
      le_trans ht (Real.exp_le_exp.mpr (Real.rpow_le_rpow hlogP.le hxle (by norm_num)))
    have h := EtW_bound A hA c₁ C₁ hc₁ hT q χ t x hx2 hqx htx
    rwa [hK₁]
  have hErrP : ‖EtW q χ t P‖ ≤ K₁ * P * ee := by
    have h := hErr P le_rfl
    exact h
  have hErr2P : ‖EtW q χ t (2 * P)‖ ≤ K₁ * (2 * P) * ee := by
    have h := hErr (2 * P) (by linarith)
    calc ‖EtW q χ t (2 * P)‖
        ≤ K₁ * (2 * P) * Real.exp (-c₁ * Real.log (2 * P) ^ (1 / 12 : ℝ)) := h
      _ ≤ K₁ * (2 * P) * ee := mul_le_mul_of_nonneg_left hexp2P (by positivity)
  -- integrability and the splitting of the Abel integral
  have hIntM : IntervalIntegrable (fun v : ℝ => MtW q χ t v * Wt v) MeasureTheory.volume P (2 * P) :=
    intervalIntegrable_MtW_Wt q χ t P hP1
  have hIntC : IntervalIntegrable (fun v : ℝ => CtW q χ t v * Wt v) MeasureTheory.volume P (2 * P) := by
    have h := pcsw.intervalIntegrable_step_sum_mul (cTw q χ t) P (2 * P) hP2 hPle2
    simpa only [CtW, Wt] using h
  have hIntE : IntervalIntegrable (fun v : ℝ => EtW q χ t v * Wt v) MeasureTheory.volume P (2 * P) := by
    have hfun : (fun v : ℝ => EtW q χ t v * Wt v)
        = fun v : ℝ => CtW q χ t v * Wt v - MtW q χ t v * Wt v := by
      funext v; simp only [EtW]; ring
    rw [hfun]
    exact hIntC.sub hIntM
  have hsplitE : ∫ v in P..(2 * P), CtW q χ t v * Wt v
      = (∫ v in P..(2 * P), MtW q χ t v * Wt v)
        + (∫ v in P..(2 * P), EtW q χ t v * Wt v) := by
    rw [← intervalIntegral.integral_add hIntM hIntE]
    refine intervalIntegral.integral_congr fun v _hv => ?_
    simp only [EtW]; ring
  -- Abel's summation formula
  have hAb' : (∑ k ∈ Finset.Ioc ⌊P⌋₊ ⌊2 * P⌋₊, ((Real.log k : ℝ) : ℂ)⁻¹ * cTw q χ t k)
      = ((Real.log (2 * P) : ℝ) : ℂ)⁻¹ * CtW q χ t (2 * P)
        - ((Real.log P : ℝ) : ℂ)⁻¹ * CtW q χ t P
        + ∫ v in P..(2 * P), CtW q χ t v * Wt v := by
    have h := pcsw.abel_inv_log_identity (cTw q χ t) P (2 * P) hP2 hPle2
    simpa only [CtW, Wt] using h
  -- the prime-power (von Mangoldt) comparison
  have hIocIcc : Finset.Ioc ⌊P⌋₊ ⌊2 * P⌋₊ = Finset.Icc (⌊P⌋₊ + 1) ⌊2 * P⌋₊ :=
    (Finset.Icc_add_one_left_eq_Ioc ⌊P⌋₊ ⌊2 * P⌋₊).symm
  have hfleq : ⌊P⌋₊ + 1 ≤ ⌊2 * P⌋₊ := by
    refine Nat.le_floor ?_
    have h1 : ((⌊P⌋₊ : ℕ) : ℝ) ≤ P := Nat.floor_le (by linarith)
    push_cast
    linarith
  have hcorr' : ‖(∑ k ∈ Finset.Ioc ⌊P⌋₊ ⌊2 * P⌋₊, ((Real.log k : ℝ) : ℂ)⁻¹ * cTw q χ t k)
      - (∑ p ∈ (Finset.Ioc ⌊P⌋₊ ⌊2 * P⌋₊).filter Nat.Prime, χ p * (p : ℂ) ^ (Complex.I * t))‖
      ≤ Cpp * Real.sqrt (⌊2 * P⌋₊ : ℝ) * Real.log (⌊2 * P⌋₊ : ℝ) := by
    have h2floor : 2 ≤ ⌊P⌋₊ + 1 := by
      have h8 : (8 : ℕ) ≤ ⌊P⌋₊ := Nat.le_floor (by push_cast; linarith)
      omega
    have hcorr := hCpp q χ t (⌊P⌋₊ + 1) ⌊2 * P⌋₊ h2floor hfleq
    have h1 : (∑ k ∈ Finset.Ioc ⌊P⌋₊ ⌊2 * P⌋₊, ((Real.log k : ℝ) : ℂ)⁻¹ * cTw q χ t k)
        = ∑ k ∈ Finset.Icc (⌊P⌋₊ + 1) ⌊2 * P⌋₊,
            ((Real.log k : ℝ) : ℂ)⁻¹ * gTw q χ t k := by
      rw [hIocIcc]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk0 : k ≠ 0 := by have := (Finset.mem_Icc.mp hk).1; omega
      simp only [cTw, if_neg hk0]
    have h2 : (∑ p ∈ (Finset.Ioc ⌊P⌋₊ ⌊2 * P⌋₊).filter Nat.Prime,
          χ p * (p : ℂ) ^ (Complex.I * t))
        = ∑ p ∈ (Finset.Icc (⌊P⌋₊ + 1) ⌊2 * P⌋₊).filter Nat.Prime,
            χ p * (p : ℂ) ^ (Complex.I * t) := by
      rw [hIocIcc]
    rw [h1, h2]
    simp only [gTw]
    exact hcorr
  -- the three error pieces
  have hterm1 : ‖((Real.log (2 * P) : ℝ) : ℂ)⁻¹ * EtW q χ t (2 * P)‖
      ≤ 2 * K₁ * P * ee / Real.log P := by
    have hnorm1 : ‖((Real.log (2 * P) : ℝ) : ℂ)⁻¹‖ = 1 / Real.log (2 * P) := by
      rw [norm_inv]
      simp [abs_of_pos hlog2Ppos]
    rw [norm_mul, hnorm1]
    calc (1 / Real.log (2 * P)) * ‖EtW q χ t (2 * P)‖
        ≤ (1 / Real.log (2 * P)) * (K₁ * (2 * P) * ee) :=
          mul_le_mul_of_nonneg_left hErr2P (by positivity)
      _ ≤ (1 / Real.log P) * (K₁ * (2 * P) * ee) :=
          mul_le_mul_of_nonneg_right (one_div_le_one_div_of_le hlogP hlog2P) (by positivity)
      _ = 2 * K₁ * P * ee / Real.log P := by ring
  have hterm2 : ‖((Real.log P : ℝ) : ℂ)⁻¹ * EtW q χ t P‖ ≤ K₁ * P * ee / Real.log P := by
    have hnorm1 : ‖((Real.log P : ℝ) : ℂ)⁻¹‖ = 1 / Real.log P := by
      rw [norm_inv]
      simp [abs_of_pos hlogP]
    rw [norm_mul, hnorm1]
    calc (1 / Real.log P) * ‖EtW q χ t P‖ ≤ (1 / Real.log P) * (K₁ * P * ee) :=
          mul_le_mul_of_nonneg_left hErrP (by positivity)
      _ = K₁ * P * ee / Real.log P := by ring
  have hterm3 : ‖∫ v in P..(2 * P), EtW q χ t v * Wt v‖ ≤ K₁ * P * ee / (Real.log P) ^ 2 := by
    have hb : ∀ v ∈ Set.uIoc P (2 * P),
        ‖EtW q χ t v * Wt v‖ ≤ K₁ * ee / (Real.log P) ^ 2 := by
      intro v hv
      rw [Set.uIoc_of_le hPle2] at hv
      have hvP : P ≤ v := le_of_lt hv.1
      have hvpos : 0 < v := lt_of_lt_of_le hP0 hvP
      have hEv := hErr v hvP
      have hlogv : 0 < Real.log v := Real.log_pos (by linarith)
      have hv2pos : (0 : ℝ) < v * (Real.log v) ^ 2 := mul_pos hvpos (pow_pos hlogv 2)
      have hWv : ‖Wt v‖ = 1 / (v * (Real.log v) ^ 2) := by
        rw [Wt, norm_inv]
        simp [abs_of_pos hv2pos, hvpos.le]
      rw [norm_mul, hWv]
      have hlogPv : Real.log P ≤ Real.log v := Real.log_le_log hP0 hvP
      have hexpv : Real.exp (-c₁ * Real.log v ^ (1 / 12 : ℝ)) ≤ ee := by
        rw [hee]
        refine Real.exp_le_exp.mpr ?_
        have h : Real.log P ^ (1 / 12 : ℝ) ≤ Real.log v ^ (1 / 12 : ℝ) :=
          Real.rpow_le_rpow hlogP.le hlogPv (by norm_num)
        nlinarith [hc₁, h]
      have hsq : (Real.log P) ^ 2 ≤ (Real.log v) ^ 2 := by nlinarith [hlogP, hlogPv]
      have hden : (0 : ℝ) < (Real.log P) ^ 2 := by positivity
      have hdenv : (0 : ℝ) < (Real.log v) ^ 2 := by positivity
      calc ‖EtW q χ t v‖ * (1 / (v * (Real.log v) ^ 2))
          ≤ (K₁ * v * Real.exp (-c₁ * Real.log v ^ (1 / 12 : ℝ))) * (1 / (v * (Real.log v) ^ 2)) :=
            mul_le_mul_of_nonneg_right hEv (by positivity)
        _ = K₁ * Real.exp (-c₁ * Real.log v ^ (1 / 12 : ℝ)) / (Real.log v) ^ 2 := by
            field_simp
            try ring
        _ ≤ K₁ * ee / (Real.log P) ^ 2 := by
            rw [div_le_div_iff₀ hdenv hden]
            exact mul_le_mul (mul_le_mul_of_nonneg_left hexpv hK₁nn) hsq (by positivity) (by positivity)
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := P) (b := 2 * P) (C := K₁ * ee / (Real.log P) ^ 2)
      (f := fun v : ℝ => EtW q χ t v * Wt v) hb
    have hd : |2 * P - P| = P := by rw [show 2 * P - P = P by ring, abs_of_pos hP0]
    rw [hd] at h
    have heq : (K₁ * ee / (Real.log P) ^ 2) * P = K₁ * P * ee / (Real.log P) ^ 2 := by ring
    rw [heq] at h
    exact h
  -- assembling the three error pieces
  have hbracket : ‖(∑ k ∈ Finset.Ioc ⌊P⌋₊ ⌊2 * P⌋₊, ((Real.log k : ℝ) : ℂ)⁻¹ * cTw q χ t k)
      - (((Real.log (2 * P) : ℝ) : ℂ)⁻¹ * MtW q χ t (2 * P)
        - ((Real.log P : ℝ) : ℂ)⁻¹ * MtW q χ t P
        + ∫ v in P..(2 * P), MtW q χ t v * Wt v)‖
      ≤ 2 * K₁ * P * ee / Real.log P + K₁ * P * ee / Real.log P
        + K₁ * P * ee / (Real.log P) ^ 2 := by
    have hEq : (∑ k ∈ Finset.Ioc ⌊P⌋₊ ⌊2 * P⌋₊, ((Real.log k : ℝ) : ℂ)⁻¹ * cTw q χ t k)
        - (((Real.log (2 * P) : ℝ) : ℂ)⁻¹ * MtW q χ t (2 * P)
          - ((Real.log P : ℝ) : ℂ)⁻¹ * MtW q χ t P
          + ∫ v in P..(2 * P), MtW q χ t v * Wt v)
        = ((Real.log (2 * P) : ℝ) : ℂ)⁻¹ * EtW q χ t (2 * P)
          - ((Real.log P : ℝ) : ℂ)⁻¹ * EtW q χ t P
          + ∫ v in P..(2 * P), EtW q χ t v * Wt v := by
      rw [hAb', hsplitE]
      have hA : CtW q χ t (2 * P) = MtW q χ t (2 * P) + EtW q χ t (2 * P) := by
        simp only [EtW]; ring
      have hB : CtW q χ t P = MtW q χ t P + EtW q χ t P := by
        simp only [EtW]; ring
      rw [hA, hB]
      ring
    rw [hEq]
    refine le_trans (norm_add_le _ _) ?_
    refine add_le_add ?_ hterm3
    refine le_trans (norm_sub_le _ _) ?_
    linarith [hterm1, hterm2]
  -- identification of the main term
  have hMtceq : ((Real.log (2 * P) : ℝ) : ℂ)⁻¹ * MtW q χ t (2 * P)
      - ((Real.log P : ℝ) : ℂ)⁻¹ * MtW q χ t P
      + ∫ v in P..(2 * P), MtW q χ t v * Wt v
      = (if χ = 1 then ∫ v in P..(2 * P), (v : ℂ) ^ (Complex.I * t) /
          ((Real.log v : ℝ) : ℂ) else 0) := by
    by_cases hχ : χ = 1
    · rw [if_pos hχ]
      simp only [MtW, Wt, hχ, if_true]
      rw [← pcsw.integral_cpow_div_log_identity t P (2 * P) hP1 hPle2]
    · rw [if_neg hχ]
      have hfun : (fun v : ℝ => MtW q χ t v * Wt v) = fun _ => (0 : ℂ) := by
        funext v; simp [MtW, hχ]
      simp only [MtW, hχ, if_false, zero_mul, hfun, intervalIntegral.integral_zero]
      ring
  -- the final decomposition
  have hdecomp : (∑ p ∈ primesIn P (2 * P), χ p * (p : ℂ) ^ (Complex.I * t))
      - (if χ = 1 then ∫ v in P..(2 * P), (v : ℂ) ^ (Complex.I * t) /
          ((Real.log v : ℝ) : ℂ) else 0)
      = ((∑ p ∈ primesIn P (2 * P), χ p * (p : ℂ) ^ (Complex.I * t))
          - (∑ p ∈ (Finset.Ioc ⌊P⌋₊ ⌊2 * P⌋₊).filter Nat.Prime,
              χ p * (p : ℂ) ^ (Complex.I * t)))
        - ((∑ k ∈ Finset.Ioc ⌊P⌋₊ ⌊2 * P⌋₊, ((Real.log k : ℝ) : ℂ)⁻¹ * cTw q χ t k)
          - (∑ p ∈ (Finset.Ioc ⌊P⌋₊ ⌊2 * P⌋₊).filter Nat.Prime,
              χ p * (p : ℂ) ^ (Complex.I * t)))
        + ((∑ k ∈ Finset.Ioc ⌊P⌋₊ ⌊2 * P⌋₊, ((Real.log k : ℝ) : ℂ)⁻¹ * cTw q χ t k)
          - (((Real.log (2 * P) : ℝ) : ℂ)⁻¹ * MtW q χ t (2 * P)
            - ((Real.log P : ℝ) : ℂ)⁻¹ * MtW q χ t P
            + ∫ v in P..(2 * P), MtW q χ t v * Wt v)) := by
    rw [hMtceq]
    ring
  rw [hdecomp]
  have hmain : ‖((∑ p ∈ primesIn P (2 * P), χ p * (p : ℂ) ^ (Complex.I * t))
        - (∑ p ∈ (Finset.Ioc ⌊P⌋₊ ⌊2 * P⌋₊).filter Nat.Prime,
            χ p * (p : ℂ) ^ (Complex.I * t)))
      - ((∑ k ∈ Finset.Ioc ⌊P⌋₊ ⌊2 * P⌋₊, ((Real.log k : ℝ) : ℂ)⁻¹ * cTw q χ t k)
        - (∑ p ∈ (Finset.Ioc ⌊P⌋₊ ⌊2 * P⌋₊).filter Nat.Prime,
            χ p * (p : ℂ) ^ (Complex.I * t)))
      + ((∑ k ∈ Finset.Ioc ⌊P⌋₊ ⌊2 * P⌋₊, ((Real.log k : ℝ) : ℂ)⁻¹ * cTw q χ t k)
        - (((Real.log (2 * P) : ℝ) : ℂ)⁻¹ * MtW q χ t (2 * P)
          - ((Real.log P : ℝ) : ℂ)⁻¹ * MtW q χ t P
          + ∫ v in P..(2 * P), MtW q χ t v * Wt v))‖
      ≤ 1 + Cpp * Real.sqrt (⌊2 * P⌋₊ : ℝ) * Real.log (⌊2 * P⌋₊ : ℝ)
        + (2 * K₁ * P * ee / Real.log P + K₁ * P * ee / Real.log P
          + K₁ * P * ee / (Real.log P) ^ 2) := by
    refine le_trans (norm_add_le _ _) ?_
    refine add_le_add ?_ hbracket
    refine le_trans (norm_sub_le _ _) ?_
    exact add_le_add (norm_primesIn_sub_Iocfilter_le q χ t P) hcorr'
  -- absorption
  have hAbs := hAbLE P hPCab
  rw [← hee] at hAbs
  have hSP : 0 ≤ Real.sqrt P * Real.log P := by positivity
  have hTL : 0 ≤ P * ee / Real.log P := by positivity
  have hTL2 : 0 ≤ P * ee / (Real.log P) ^ 2 := by positivity
  have hlogB2 : (1 : ℝ) ≤ (⌊2 * P⌋₊ : ℝ) := by
    have h : (2 : ℝ) ≤ (⌊2 * P⌋₊ : ℝ) := by exact_mod_cast hB2
    linarith
  have hlogBnn : 0 ≤ Real.log (⌊2 * P⌋₊ : ℝ) := Real.log_nonneg hlogB2
  have hKB : Real.sqrt (⌊2 * P⌋₊ : ℝ) * Real.log (⌊2 * P⌋₊ : ℝ)
      ≤ 4 * (Real.sqrt P * Real.log P) := by
    calc Real.sqrt (⌊2 * P⌋₊ : ℝ) * Real.log (⌊2 * P⌋₊ : ℝ)
        ≤ (2 * Real.sqrt P) * (2 * Real.log P) :=
          mul_le_mul hsqrtB hlogBle hlogBnn (by positivity)
      _ = 4 * (Real.sqrt P * Real.log P) := by ring
  have hSB : Cpp * Real.sqrt (⌊2 * P⌋₊ : ℝ) * Real.log (⌊2 * P⌋₊ : ℝ)
      ≤ 4 * Cpp * (Real.sqrt P * Real.log P) := by
    have h1 : Cpp * Real.sqrt (⌊2 * P⌋₊ : ℝ) * Real.log (⌊2 * P⌋₊ : ℝ)
        = Cpp * (Real.sqrt (⌊2 * P⌋₊ : ℝ) * Real.log (⌊2 * P⌋₊ : ℝ)) := by ring
    rw [h1]
    calc Cpp * (Real.sqrt (⌊2 * P⌋₊ : ℝ) * Real.log (⌊2 * P⌋₊ : ℝ))
        ≤ Cpp * (4 * (Real.sqrt P * Real.log P)) := mul_le_mul_of_nonneg_left hKB hCpppos.le
      _ = 4 * Cpp * (Real.sqrt P * Real.log P) := by ring
  have hstep1 : 1 + Cpp * Real.sqrt (⌊2 * P⌋₊ : ℝ) * Real.log (⌊2 * P⌋₊ : ℝ)
      + (2 * K₁ * P * ee / Real.log P + K₁ * P * ee / Real.log P
        + K₁ * P * ee / (Real.log P) ^ 2)
      ≤ (4 * Cpp + 3 * K₁ + 1) * P * Real.exp (-(c₁ / 2) * Real.log P ^ (1 / 12 : ℝ)) := by
    have hshuffle : 2 * K₁ * P * ee / Real.log P + K₁ * P * ee / Real.log P
        + K₁ * P * ee / (Real.log P) ^ 2
        = 3 * K₁ * (P * ee / Real.log P) + K₁ * (P * ee / (Real.log P) ^ 2) := by
      field_simp
      try ring
    rw [hshuffle]
    have h1 : Cpp * Real.sqrt (⌊2 * P⌋₊ : ℝ) * Real.log (⌊2 * P⌋₊ : ℝ)
        ≤ (4 * Cpp + 3 * K₁) * (Real.sqrt P * Real.log P) := by
      refine le_trans hSB ?_
      exact mul_le_mul_of_nonneg_right (by linarith) hSP
    have h2 : 3 * K₁ * (P * ee / Real.log P) ≤ (4 * Cpp + 3 * K₁) * (P * ee / Real.log P) :=
      mul_le_mul_of_nonneg_right (by linarith) hTL
    have h3 : K₁ * (P * ee / (Real.log P) ^ 2)
        ≤ (4 * Cpp + 3 * K₁) * (P * ee / (Real.log P) ^ 2) :=
      mul_le_mul_of_nonneg_right (by linarith) hTL2
    linarith [h1, h2, h3, hAbs]
  refine le_trans hmain ?_
  refine le_trans hstep1 ?_
  rw [hK₁]

end

end Work.BMF
