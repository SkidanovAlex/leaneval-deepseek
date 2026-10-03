/-
# `Submission.Work.FIChain.abs_S3minusC_le` — §8 (8.1) for the `μ(c)`-signed `S₃⁻`

This is the `λ⁻` half of the companion's §8 estimate

  `|S₃⁻(x;y,z)| ≤ J·E·log C`   (for `sz = 2^J z`)

for the **`μ(c)`-signed** splitting of `S₃` used by this chapter (`Work.FIChain.S3minusC`,
whose inner `c`-sum carries the factor `μ(c)·λ⁻(c)·a(ℓc)`), and from the contract's
`Work.FITop.RhoWindowC` — the `ρ`-window with the companion's `μ`-placement
(`Work.FITop.XrhoC` carries a *single* Möbius factor, on the product `mn`).

The proof is the exact analogue of `Submission.ASP.abs_S3minus_le` (`ASP/S8b.lean`), with

* `Xrho` replaced by `XrhoC` (`Work.FITop.XrhoC`, i.e. `ρ(n;s)·μ(ℓn)·a(ℓn)` — no `μ(n)`), and
* the extra `μ(c)` of the inner `c`-sum absorbed by the squarefree-support identity
  `μ(c)·a(ℓc) = μ(ℓ)·μ(ℓc)·a(ℓc)` (`ASP.moebius_mul_a_mul_eq`), which turns the
  `λ⁻`-weighted `c`-sum into `μ(ℓ)·XrhoC`.

Everything is proved from scratch here; no `sorry`, no `axiom`.
-/
import Mathlib
import Submission.Work.FIChain.Defs
import Submission.Work.FITop.Defs

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIChain

open Finset MeasureTheory
open Submission.ASP
open scoped Interval BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. `XrhoC` as a filtered sum, and its elementary structure -/

/-- `Work.FIPlan.gammaTrunc` and `Submission.ASP.rhoTrunc` are the same truncated Möbius sum. -/
lemma gammaTrunc_eq_rhoTrunc (s : ℝ) (n : ℕ) : Work.FIPlan.gammaTrunc s n = rhoTrunc n s := rfl

/-- `XrhoC` in "filtered" form (the range-conditions pushed into the index set). -/
lemma XrhoC_eq_sum_filter (a : ℕ → ℝ) (N m : ℕ) (s t u : ℝ) :
    Work.FITop.XrhoC a N m s t u
      = ∑ n ∈ (Finset.Icc 1 N).filter
          (fun n => t < ((n : ℕ) : ℝ) ∧ ((n : ℕ) : ℝ) ≤ u ∧ m * n ≤ N),
          Work.FIPlan.gammaTrunc s n * (ArithmeticFunction.moebius (m * n) : ℝ) * a (m * n) := by
  rw [Work.FITop.XrhoC, Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  by_cases hN : m * n ≤ N <;> by_cases h1 : t < ((n : ℕ) : ℝ) ∧ ((n : ℕ) : ℝ) ≤ u <;>
    simp [hN, h1, and_comm]

/-- `XrhoC` is additive over adjacent windows. -/
lemma XrhoC_add_adjacent (a : ℕ → ℝ) (N m : ℕ) (s : ℝ) {t v w : ℝ} (htv : t ≤ v) (hvw : v ≤ w) :
    Work.FITop.XrhoC a N m s t w
      = Work.FITop.XrhoC a N m s t v + Work.FITop.XrhoC a N m s v w := by
  rw [Work.FITop.XrhoC, Work.FITop.XrhoC, Work.FITop.XrhoC, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rcases le_or_gt (((n : ℕ) : ℝ)) t with h1 | h1
  · have h2 : ¬ (t < ((n : ℕ) : ℝ)) := not_lt.mpr h1
    have h3 : ¬ (v < ((n : ℕ) : ℝ)) := not_lt.mpr (le_trans h1 htv)
    simp [h2, h3]
  · rcases le_or_gt (((n : ℕ) : ℝ)) v with h2 | h2
    · have h3 : ¬ (v < ((n : ℕ) : ℝ)) := not_lt.mpr h2
      have h4 : ((n : ℕ) : ℝ) ≤ w := le_trans h2 hvw
      simp [h1, h2, h3, h4]
    · have h3 : ¬ (((n : ℕ) : ℝ) ≤ v) := not_le.mpr h2
      by_cases h4 : ((n : ℕ) : ℝ) ≤ w
      · simp [h1, h2, h3, h4]
      · have h5 : ¬ (((n : ℕ) : ℝ) ≤ w) := h4
        simp [h1, h2, h3, h5]

/-- The dyadic splitting of the `XrhoC` window (the intervals `(2^j u, 2^{j+1} u]`, `j < J`,
partition `(u, 2^J u]`). -/
lemma XrhoC_dyadic (a : ℕ → ℝ) (N m : ℕ) (s : ℝ) {u : ℝ} (hu : 0 < u) (J : ℕ) :
    Work.FITop.XrhoC a N m s u ((2 : ℝ) ^ J * u)
      = ∑ j ∈ Finset.range J,
          Work.FITop.XrhoC a N m s ((2 : ℝ) ^ j * u) ((2 : ℝ) ^ (j + 1) * u) := by
  induction J with
  | zero =>
      rw [Work.FITop.XrhoC, pow_zero, one_mul]
      refine Finset.sum_eq_zero (fun n _ => ?_)
      have hne : ¬ (u < ((n : ℕ) : ℝ) ∧ ((n : ℕ) : ℝ) ≤ u) :=
        fun h => absurd h.2 (not_le.mpr h.1)
      simp only [hne, if_false]
  | succ J ih =>
      have hle : u ≤ (2 : ℝ) ^ J * u := by
        have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ J := one_le_pow₀ (by norm_num)
        nlinarith
      have hle2 : (2 : ℝ) ^ J * u ≤ (2 : ℝ) ^ (J + 1) * u := by
        have h2 : (2 : ℝ) ^ J ≤ (2 : ℝ) ^ (J + 1) := by
          calc (2 : ℝ) ^ J = (2 : ℝ) ^ J * 1 := (mul_one _).symm
            _ ≤ (2 : ℝ) ^ J * 2 := by nlinarith [(show (1 : ℝ) ≤ 2 by norm_num)]
            _ = (2 : ℝ) ^ (J + 1) := by ring
        nlinarith
      rw [Finset.sum_range_succ, ← ih, XrhoC_add_adjacent (a := a) (N := N) (m := m) (s := s)
        (t := u) (v := (2 : ℝ) ^ J * u) (w := (2 : ℝ) ^ (J + 1) * u) hle hle2]

/-! ## 2. Measurability and boundedness of `XrhoC` -/

/-- Measurability of `s ↦ XrhoC a N ℓ s t u`. -/
lemma measurable_XrhoC (a : ℕ → ℝ) (N ℓ : ℕ) (t u : ℝ) :
    Measurable (fun s : ℝ => Work.FITop.XrhoC a N ℓ s t u) := by
  have h : (fun s : ℝ => Work.FITop.XrhoC a N ℓ s t u)
      = fun s => ∑ n ∈ (Finset.Icc 1 N).filter (fun n => ℓ * n ≤ N),
          (if t < ((n : ℕ) : ℝ) ∧ ((n : ℕ) : ℝ) ≤ u
            then Work.FIPlan.gammaTrunc s n
              * (ArithmeticFunction.moebius (ℓ * n) : ℝ) * a (ℓ * n) else 0) := by
    funext s; rw [Work.FITop.XrhoC]
  rw [h]
  refine Finset.measurable_sum _ (fun n _ => ?_)
  by_cases hc : t < ((n : ℕ) : ℝ) ∧ ((n : ℕ) : ℝ) ≤ u
  · simp only [if_pos hc]
    have heq : (fun s : ℝ => Work.FIPlan.gammaTrunc s n
          * (ArithmeticFunction.moebius (ℓ * n) : ℝ) * a (ℓ * n))
        = fun s : ℝ => ((ArithmeticFunction.moebius (ℓ * n) : ℝ) * a (ℓ * n))
            * Work.FIPlan.gammaTrunc s n := by
      funext s; ring
    rw [heq]
    exact measurable_const.mul (measurable_rhoTrunc n)
  · simp only [if_neg hc]; exact measurable_const

/-- `|XrhoC|` is bounded by the `τ`-weighted sum of `|a|`. -/
lemma abs_XrhoC_le (a : ℕ → ℝ) (N ℓ : ℕ) (s t u : ℝ) :
    |Work.FITop.XrhoC a N ℓ s t u|
      ≤ ∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ) * |a (ℓ * n)| := by
  rw [Work.FITop.XrhoC]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum (fun n _ => ?_)).trans
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun n _ _ => mul_nonneg (by positivity) (abs_nonneg _)))
  by_cases hc : t < ((n : ℕ) : ℝ) ∧ ((n : ℕ) : ℝ) ≤ u
  · rw [if_pos hc, abs_mul, abs_mul]
    calc |Work.FIPlan.gammaTrunc s n| * |(ArithmeticFunction.moebius (ℓ * n) : ℝ)|
          * |a (ℓ * n)|
        ≤ (n.divisors.card : ℝ) * 1 * |a (ℓ * n)| := by
          gcongr
          · exact abs_rhoTrunc_le n s
          · exact abs_moebius_cast_le_one (ℓ * n)
      _ = (n.divisors.card : ℝ) * |a (ℓ * n)| := by ring
  · rw [if_neg hc, abs_zero]; positivity

/-! ## 3. The `λ⁻`-weighted `c`-sum is an integral of `XrhoC` -/

/-- **§8**: the absolute value of the `μ(c)·λ⁻(c)`-weighted `c`-sum is bounded by the integral
of `|XrhoC|`.  (The `μ(c)` is absorbed by the squarefree-support identity
`μ(c)·a(ℓc) = μ(ℓ)·μ(ℓc)·a(ℓc)` of `ASP.S8b`.) -/
lemma abs_S3minusInnerC_le_integral (a : ℕ → ℝ) (N ℓ : ℕ) (z sz C : ℝ) (hC : 1 ≤ C)
    (ha : ∀ n, ¬ Squarefree n → a n = 0) :
    |S3minusInnerC a N ℓ z sz C|
      ≤ ∫ s in (1 : ℝ)..C, |Work.FITop.XrhoC a N ℓ s z sz| / s := by
  classical
  set Ch : Finset ℕ := (Finset.Icc 1 N).filter
    (fun c => z < ((c : ℕ) : ℝ) ∧ ((c : ℕ) : ℝ) ≤ sz ∧ ℓ * c ≤ N) with hCh
  -- the sum is `μ(ℓ)·XrhoC` at each level `s`
  have hsum_eq : ∀ s : ℝ,
      (∑ c ∈ Ch, (ArithmeticFunction.moebius c : ℝ) * a (ℓ * c) * rhoTrunc c s)
        = (ArithmeticFunction.moebius ℓ : ℝ) * Work.FITop.XrhoC a N ℓ s z sz := by
    intro s
    have hterm : ∀ c : ℕ,
        (ArithmeticFunction.moebius c : ℝ) * a (ℓ * c) * rhoTrunc c s
          = (ArithmeticFunction.moebius ℓ : ℝ)
              * (rhoTrunc c s * (ArithmeticFunction.moebius (ℓ * c) : ℝ) * a (ℓ * c)) := by
      intro c
      rw [show (ArithmeticFunction.moebius c : ℝ) * a (ℓ * c) * rhoTrunc c s
            = rhoTrunc c s * ((ArithmeticFunction.moebius c : ℝ) * a (ℓ * c)) by ring,
        moebius_mul_a_mul_eq ha ℓ c]
      ring
    have hsum : (∑ c ∈ Ch,
          rhoTrunc c s * (ArithmeticFunction.moebius (ℓ * c) : ℝ) * a (ℓ * c))
        = Work.FITop.XrhoC a N ℓ s z sz := by
      rw [XrhoC_eq_sum_filter, hCh]
      refine Finset.sum_congr rfl (fun c _ => ?_)
      rw [gammaTrunc_eq_rhoTrunc]
    rw [Finset.sum_congr rfl (fun c _ => hterm c), ← Finset.mul_sum, hsum]
  -- the `λ⁻`-weighted sum as one integral
  have hInt : S3minusInnerC a N ℓ z sz C
      = ∫ s in (1 : ℝ)..C,
          ∑ c ∈ Ch, ((ArithmeticFunction.moebius c : ℝ) * a (ℓ * c))
            * (rhoTrunc c s / s) := by
    have h1 : S3minusInnerC a N ℓ z sz C
        = ∑ c ∈ Ch, ((ArithmeticFunction.moebius c : ℝ) * a (ℓ * c))
            * (∫ s in (1 : ℝ)..C, rhoTrunc c s / s) := by
      rw [S3minusInnerC, hCh]
      refine Finset.sum_congr rfl (fun c _ => ?_)
      rw [lamMinus_eq_integral c hC]
      ring
    rw [h1]
    rw [intervalIntegral.integral_finsetSum (fun c _ =>
      (intervalIntegrable_rhoTrunc_div c hC).const_mul _)]
    simp only [intervalIntegral.integral_const_mul]
  -- pointwise comparison of the two integrands
  have hpt : ∀ s : ℝ, 1 ≤ s →
      |∑ c ∈ Ch, ((ArithmeticFunction.moebius c : ℝ) * a (ℓ * c)) * (rhoTrunc c s / s)|
        ≤ |Work.FITop.XrhoC a N ℓ s z sz| / s := by
    intro s hs1
    have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs1
    have hF : (∑ c ∈ Ch, ((ArithmeticFunction.moebius c : ℝ) * a (ℓ * c))
          * (rhoTrunc c s / s))
        = (∑ c ∈ Ch, (ArithmeticFunction.moebius c : ℝ) * a (ℓ * c) * rhoTrunc c s) / s := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl (fun c _ => by ring)
    rw [hF, hsum_eq s, abs_div, abs_of_pos hs0, abs_mul]
    calc |(ArithmeticFunction.moebius ℓ : ℝ)| * |Work.FITop.XrhoC a N ℓ s z sz| / s
        ≤ 1 * |Work.FITop.XrhoC a N ℓ s z sz| / s := by
          gcongr
          exact abs_moebius_cast_le_one ℓ
      _ = |Work.FITop.XrhoC a N ℓ s z sz| / s := by ring
  -- assemble
  rw [hInt]
  refine le_trans (intervalIntegral.abs_integral_le_integral_abs hC) ?_
  have hGm : Measurable (fun s : ℝ =>
      ∑ c ∈ Ch, (ArithmeticFunction.moebius c : ℝ) * a (ℓ * c) * rhoTrunc c s) :=
    Finset.measurable_sum _ (fun c _ => (measurable_rhoTrunc c).const_mul _)
  have hCbdd : ∀ u ∈ Set.Icc (1 : ℝ) C,
      |∑ c ∈ Ch, (ArithmeticFunction.moebius c : ℝ) * a (ℓ * c) * rhoTrunc c u|
        ≤ ∑ c ∈ Ch, (c.divisors.card : ℝ) * |a (ℓ * c)| := by
    intro u _
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun c _ => ?_))
    rw [abs_mul]
    have h1 : |(ArithmeticFunction.moebius c : ℝ) * a (ℓ * c)| ≤ |a (ℓ * c)| := by
      rw [abs_mul]
      calc |(ArithmeticFunction.moebius c : ℝ)| * |a (ℓ * c)|
          ≤ 1 * |a (ℓ * c)| :=
            mul_le_mul_of_nonneg_right (abs_moebius_cast_le_one c) (abs_nonneg _)
        _ = |a (ℓ * c)| := one_mul _
    calc |(ArithmeticFunction.moebius c : ℝ) * a (ℓ * c)| * |rhoTrunc c u|
        ≤ |a (ℓ * c)| * (c.divisors.card : ℝ) :=
          mul_le_mul h1 (abs_rhoTrunc_le c u) (abs_nonneg _) (abs_nonneg _)
      _ = (c.divisors.card : ℝ) * |a (ℓ * c)| := by ring
  have hIntL : IntervalIntegrable (fun s : ℝ =>
      ∑ c ∈ Ch, ((ArithmeticFunction.moebius c : ℝ) * a (ℓ * c)) * (rhoTrunc c s / s))
      volume (1 : ℝ) C := by
    have hFeq : (fun s : ℝ => ∑ c ∈ Ch,
          ((ArithmeticFunction.moebius c : ℝ) * a (ℓ * c)) * (rhoTrunc c s / s))
        = fun s => (∑ c ∈ Ch,
            (ArithmeticFunction.moebius c : ℝ) * a (ℓ * c) * rhoTrunc c s) / s := by
      funext s
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl (fun c _ => by ring)
    rw [hFeq]
    exact intervalIntegrable_div_Ioc hGm (by norm_num) hC _ hCbdd
  have hIntR : IntervalIntegrable (fun s : ℝ => |Work.FITop.XrhoC a N ℓ s z sz| / s)
      volume (1 : ℝ) C :=
    intervalIntegrable_div_Ioc (measurable_XrhoC a N ℓ z sz).abs (by norm_num) hC
      (∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ) * |a (ℓ * n)|)
      (fun s _ => by simpa using abs_XrhoC_le a N ℓ s z sz)
  refine intervalIntegral.integral_mono_ae_restrict hC (hIntL.abs) hIntR ?_
  change ∀ᵐ x ∂(volume.restrict (Set.Icc (1 : ℝ) C)),
    |∑ c ∈ Ch, ((ArithmeticFunction.moebius c : ℝ) * a (ℓ * c)) * (rhoTrunc c x / x)|
      ≤ |Work.FITop.XrhoC a N ℓ x z sz| / x
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
  exact Filter.Eventually.of_forall (fun s hs => hpt s hs.1)

/-! ## 4. The dyadic-window estimate -/

/-- The dyadic-window estimate for `∑_ℓ w(ℓ)|XrhoC|`, from the contract's `RhoWindowC`. -/
lemma sum_w_XrhoC_le (a : ℕ → ℝ) (N : ℕ) (z sz C : ℝ) {w : ℕ → ℝ} {E : ℝ} {J : ℕ}
    (hz : 0 < z) (hsz : sz = (2 : ℝ) ^ J * z) (hw0 : ∀ ℓ, 0 ≤ w ℓ)
    (hwin : Work.FITop.RhoWindowC a N w E C z sz) (s : ℝ) (hs1 : 1 ≤ s) (hsC : s ≤ C) :
    (∑ ℓ ∈ Finset.Icc 1 N, w ℓ * |Work.FITop.XrhoC a N ℓ s z sz|) ≤ (J : ℝ) * E := by
  have hz1 : (1 : ℝ) ≤ 2 := by norm_num
  have hdyad : ∀ ℓ : ℕ, |Work.FITop.XrhoC a N ℓ s z sz|
      ≤ ∑ j ∈ Finset.range J,
          |Work.FITop.XrhoC a N ℓ s ((2 : ℝ) ^ j * z) ((2 : ℝ) ^ (j + 1) * z)| := by
    intro ℓ
    rw [hsz, XrhoC_dyadic a N ℓ s hz J]
    exact Finset.abs_sum_le_sum_abs _ _
  calc (∑ ℓ ∈ Finset.Icc 1 N, w ℓ * |Work.FITop.XrhoC a N ℓ s z sz|)
      ≤ ∑ ℓ ∈ Finset.Icc 1 N, w ℓ * ∑ j ∈ Finset.range J,
          |Work.FITop.XrhoC a N ℓ s ((2 : ℝ) ^ j * z) ((2 : ℝ) ^ (j + 1) * z)| :=
        Finset.sum_le_sum (fun ℓ _ => mul_le_mul_of_nonneg_left (hdyad ℓ) (hw0 ℓ))
    _ = ∑ j ∈ Finset.range J, ∑ ℓ ∈ Finset.Icc 1 N, w ℓ *
          |Work.FITop.XrhoC a N ℓ s ((2 : ℝ) ^ j * z) ((2 : ℝ) ^ (j + 1) * z)| := by
        rw [Finset.sum_congr rfl (fun ℓ _ => Finset.mul_sum _ _ _), Finset.sum_comm]
    _ ≤ ∑ _j ∈ Finset.range J, E := by
        refine Finset.sum_le_sum (fun j hj => ?_)
        have hlo : z ≤ (2 : ℝ) ^ j * z := by
          have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ hz1
          nlinarith
        have hhi : (2 : ℝ) ^ j * z ≤ sz := by
          have h2 : (2 : ℝ) ^ j ≤ (2 : ℝ) ^ J :=
            pow_le_pow_right₀ hz1 (Nat.le_of_lt (Finset.mem_range.mp hj))
          rw [hsz]
          nlinarith
        simpa [show (2 : ℝ) * ((2 : ℝ) ^ j * z) = (2 : ℝ) ^ (j + 1) * z by ring]
          using hwin s ((2 : ℝ) ^ j * z) hs1 hsC hlo hhi
    _ = (J : ℝ) * E := by simp [Finset.sum_const, nsmul_eq_mul]

/-! ## 5. The estimate `|S₃⁻| ≤ J·E·log C` -/

theorem abs_S3minusC_le (a lam : ℕ → ℝ) (N : ℕ) (z sy sz C : ℝ) {w : ℕ → ℝ} {E : ℝ} {J : ℕ}
    (ha : ∀ n : ℕ, ¬ Squarefree n → a n = 0)
    (hz : 0 < z) (hC : 1 ≤ C) (hsz : sz = (2 : ℝ) ^ J * z)
    (hw0 : ∀ ℓ : ℕ, 0 ≤ w ℓ)
    (hw : ∀ ℓ : ℕ, 1 ≤ ℓ →
      |∑ b ∈ ℓ.divisors.filter (fun b => sy < ((b : ℕ) : ℝ)),
          (ArithmeticFunction.moebius b : ℝ)| * |Submission.ASP.rhoOf lam ℓ| ≤ w ℓ)
    (hwin : Work.FITop.RhoWindowC a N w E C z sz) :
    |Work.FIChain.S3minusC a lam N z sy sz C| ≤ (J : ℝ) * E * Real.log C := by
  classical
  -- Step 1: bound `(∑_{b|ℓ} μ b)·ρ_ℓ` by `w ℓ`
  have h1 : |S3minusC a lam N z sy sz C|
      ≤ ∑ ℓ ∈ Finset.Icc 1 N, w ℓ * |S3minusInnerC a N ℓ z sz C| := by
    rw [S3minusC]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun ℓ hℓ => ?_))
    rw [abs_mul, abs_mul]
    exact mul_le_mul_of_nonneg_right (hw ℓ (Finset.mem_Icc.mp hℓ).1) (abs_nonneg _)
  -- Step 2: each inner sum by its integral
  have h2 : (∑ ℓ ∈ Finset.Icc 1 N, w ℓ * |S3minusInnerC a N ℓ z sz C|)
      ≤ ∑ ℓ ∈ Finset.Icc 1 N, w ℓ *
          (∫ s in (1 : ℝ)..C, |Work.FITop.XrhoC a N ℓ s z sz| / s) := by
    refine Finset.sum_le_sum (fun ℓ _ => mul_le_mul_of_nonneg_left ?_ (hw0 ℓ))
    exact abs_S3minusInnerC_le_integral a N ℓ z sz C hC ha
  -- Step 3: swap the `ℓ`-sum and the integral
  have hInt : ∀ ℓ : ℕ, IntervalIntegrable (fun s : ℝ => |Work.FITop.XrhoC a N ℓ s z sz| / s)
      volume (1 : ℝ) C := fun ℓ =>
    intervalIntegrable_div_Ioc (measurable_XrhoC a N ℓ z sz).abs (by norm_num) hC
      (∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ) * |a (ℓ * n)|)
      (fun s _ => by simpa using abs_XrhoC_le a N ℓ s z sz)
  have h3 : (∑ ℓ ∈ Finset.Icc 1 N, w ℓ *
        (∫ s in (1 : ℝ)..C, |Work.FITop.XrhoC a N ℓ s z sz| / s))
      = ∫ s in (1 : ℝ)..C,
          ∑ ℓ ∈ Finset.Icc 1 N, w ℓ * (|Work.FITop.XrhoC a N ℓ s z sz| / s) := by
    rw [Finset.sum_congr rfl (fun ℓ _ =>
      (intervalIntegral.integral_const_mul (w ℓ)
        (fun s => |Work.FITop.XrhoC a N ℓ s z sz| / s)).symm)]
    rw [intervalIntegral.integral_finsetSum (fun ℓ _ => (hInt ℓ).const_mul (w ℓ))]
  -- Step 4: the pointwise bound (dyadic windows)
  have hpt : ∀ s : ℝ, 1 ≤ s → s ≤ C →
      (∑ ℓ ∈ Finset.Icc 1 N, w ℓ * (|Work.FITop.XrhoC a N ℓ s z sz| / s))
        ≤ ((J : ℝ) * E) / s := by
    intro s hs1 hsC
    have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs1
    calc (∑ ℓ ∈ Finset.Icc 1 N, w ℓ * (|Work.FITop.XrhoC a N ℓ s z sz| / s))
        = (∑ ℓ ∈ Finset.Icc 1 N, w ℓ * |Work.FITop.XrhoC a N ℓ s z sz|) / s := by
          rw [Finset.sum_div]
          exact Finset.sum_congr rfl (fun ℓ _ => by ring)
      _ ≤ ((J : ℝ) * E) / s :=
          div_le_div_of_nonneg_right (sum_w_XrhoC_le a N z sz C hz hsz hw0 hwin s hs1 hsC) hs0.le
  -- Step 5: integrate
  have hIntSum : IntervalIntegrable (fun s : ℝ =>
      ∑ ℓ ∈ Finset.Icc 1 N, w ℓ * (|Work.FITop.XrhoC a N ℓ s z sz| / s))
      volume (1 : ℝ) C := by
    have hfun : (∑ ℓ ∈ Finset.Icc 1 N,
          fun x : ℝ => w ℓ * (|Work.FITop.XrhoC a N ℓ x z sz| / x))
        = fun s : ℝ => ∑ ℓ ∈ Finset.Icc 1 N,
            w ℓ * (|Work.FITop.XrhoC a N ℓ s z sz| / s) := by
      funext s
      rw [Finset.sum_apply]
    rw [← hfun]
    exact IntervalIntegrable.sum (Finset.Icc 1 N) (fun ℓ _ => (hInt ℓ).const_mul (w ℓ))
  have hIntR : IntervalIntegrable (fun s : ℝ => ((J : ℝ) * E) / s) volume (1 : ℝ) C :=
    intervalIntegrable_div_Ioc measurable_const (by norm_num) hC (|(J : ℝ) * E|)
      (fun s _ => by simp)
  have h4 : (∫ s in (1 : ℝ)..C,
      ∑ ℓ ∈ Finset.Icc 1 N, w ℓ * (|Work.FITop.XrhoC a N ℓ s z sz| / s))
      ≤ (J : ℝ) * E * Real.log C := by
    have hmono : (∫ s in (1 : ℝ)..C,
        ∑ ℓ ∈ Finset.Icc 1 N, w ℓ * (|Work.FITop.XrhoC a N ℓ s z sz| / s))
        ≤ ∫ s in (1 : ℝ)..C, ((J : ℝ) * E) / s := by
      refine intervalIntegral.integral_mono_ae_restrict hC hIntSum hIntR ?_
      change ∀ᵐ x ∂(volume.restrict (Set.Icc (1 : ℝ) C)),
          (∑ ℓ ∈ Finset.Icc 1 N, w ℓ * (|Work.FITop.XrhoC a N ℓ x z sz| / x))
            ≤ ((J : ℝ) * E) / x
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
      exact Filter.Eventually.of_forall (fun s hs => hpt s hs.1 hs.2)
    have hval : (∫ s in (1 : ℝ)..C, ((J : ℝ) * E) / s) = (J : ℝ) * E * Real.log C := by
      have hfun : (fun s : ℝ => ((J : ℝ) * E) / s)
          = fun s => ((J : ℝ) * E) * (1 / s) := by funext s; ring
      rw [hfun, intervalIntegral.integral_const_mul,
        integral_one_div_of_pos zero_lt_one (by linarith), div_one]
    rw [hval] at hmono
    exact hmono
  exact le_trans h1 (le_trans h2 (le_trans (le_of_eq h3) h4))

end

end Work.FIChain
