/-
  Companion paper ("Asymptotic sieve for primes"), §7 (`S₂`): the *integrated* estimate.

  The pointwise expansion `Ksum_abs_le_merge` (S7b) leaves the divisor `ν₁` in the range of the
  inner `b`-sum.  Following the paper, the dependence on `ν₁` is removed by *averaging over*
  `y ∈ [Y, eY]` (the smoothing `∫_Y^{eY} dy/y` has total mass `1`): after the substitution
  `y = ν₁ u` the range becomes the fixed window `[Y/Δ, eY]`, the triples `(ν₁, k, ν₂)` can be
  merged along `ℓ = ν₁k` (multiplicity at most `τ(ℓ)²`), and the window can be split dyadically
  so that the bilinear hypothesis (B′) applies at each scale.

  Main statements:
  * `smAvg_Xsum_le`      — the dyadic + (B′) core;
  * `smAvg_abs_Ksum_le`  — §7 (7.1)–(7.2) in smoothed form.
-/
import Mathlib
import Submission.ASP.S7c
import Submission.Commons.Analysis.Asymptotics.integral_one_div_Ioc_exp_mul

namespace Submission.ASP

open Finset MeasureTheory
open scoped Interval

noncomputable section

/-! ### Trivial vanishing of `Xsum` -/

/-- `Xsum` vanishes when the upper end of the `b`-range is nonpositive. -/
lemma Xsum_of_nonpos (a : ℕ → ℝ) (N ℓ : ℕ) (t : ℝ) {u : ℝ} (hu : u ≤ 0) :
    Xsum a N ℓ t u = 0 := by
  rw [Xsum]
  refine Finset.sum_eq_zero (fun b hb => ?_)
  obtain ⟨hb1, -⟩ := Finset.mem_filter.mp hb
  have hbge : (1 : ℝ) ≤ (b : ℝ) := by
    have h := (Finset.mem_Icc.mp hb1).1
    exact_mod_cast h
  have hbu : ((b : ℕ) : ℝ) ≤ u := (Finset.mem_filter.mp hb).2.2.1
  linarith

/-- `Xsum` vanishes beyond the total range: if `N < ℓ` then no `b ≥ 1` satisfies `bℓ ≤ N`. -/
lemma Xsum_eq_zero_of_lt (a : ℕ → ℝ) (N : ℕ) {ℓ : ℕ} (hℓ : N < ℓ) (t u : ℝ) :
    Xsum a N ℓ t u = 0 := by
  rw [Xsum]
  refine Finset.sum_eq_zero (fun b hb => ?_)
  obtain ⟨hb1, -, -, hble⟩ := Finset.mem_filter.mp hb
  have hbge : 1 ≤ b := (Finset.mem_Icc.mp hb1).1
  have hle : ℓ ≤ N := le_trans (Nat.le_mul_of_pos_left ℓ (by omega)) hble
  omega

/-- The dyadic splitting of the `Xsum` range, with absolute values. -/
lemma Xsum_abs_dyadic_le (a : ℕ → ℝ) (N ℓ J : ℕ) (u : ℝ) :
    |Xsum a N ℓ u ((2 : ℝ) ^ J * u)|
      ≤ ∑ j ∈ Finset.range J, |Xsum a N ℓ ((2 : ℝ) ^ j * u) ((2 : ℝ) ^ (j + 1) * u)| := by
  rcases lt_or_ge u 0 with hu | hu
  · have h2u : (2 : ℝ) ^ J * u ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hu.le
    rw [Xsum_of_nonpos a N ℓ u h2u, abs_zero]
    exact Finset.sum_nonneg (fun j _ => abs_nonneg _)
  · rcases eq_or_lt_of_le hu with h0 | hpos
    · subst h0
      rw [mul_zero, Xsum_of_nonpos a N ℓ 0 le_rfl, abs_zero]
      exact Finset.sum_nonneg (fun j _ => abs_nonneg _)
    · rw [Xsum_dyadic a N ℓ hpos J]
      exact Finset.abs_sum_le_sum_abs _ _

/-! ### The merge step with the `ℓ`-range restricted to `ℓ ≤ N` -/

/-- The merge step of §7 with the range of `ℓ` restricted to `ℓ ≤ N` (terms with `ℓ > N`
vanish since `bℓ ≤ N` is unsatisfiable for `b ≥ 1`). -/
lemma sum_merge_le_Icc (a : ℕ → ℝ) (lam w : ℕ → ℝ) (N Δ : ℕ) (u : ℝ) (hΔ : 1 ≤ Δ)
    (hlam_le1 : ∀ ν, |lam ν| ≤ 1)
    (hw : ∀ ℓ, 1 ≤ ℓ → ((ℓ.divisors.card : ℝ)) ^ 2 ≤ w ℓ) :
    (∑ ν₁ ∈ Finset.Icc 1 Δ, ∑ k ∈ Finset.Icc 1 N, ∑ ν₂ ∈ k.divisors,
        |lam (ν₁ * ν₂)| * |Xsum a N (ν₁ * k) u (2 * u)|)
      ≤ ∑ ℓ ∈ Finset.Icc 1 N, w ℓ * |Xsum a N ℓ u (2 * u)| := by
  refine (sum_merge_le a lam N Δ w u hlam_le1 hw).trans (le_of_eq ?_)
  refine (Finset.sum_subset ?_ ?_).symm
  · intro ℓ hℓ
    rw [Finset.mem_Icc] at hℓ ⊢
    exact ⟨hℓ.1, le_trans hℓ.2 (Nat.le_mul_of_pos_left N (by omega))⟩
  · intro ℓ hℓ hnot
    rw [Finset.mem_Icc] at hℓ
    have hNℓ : N < ℓ := by
      by_contra hcon
      rw [not_lt] at hcon
      exact hnot (Finset.mem_Icc.mpr ⟨hℓ.1, hcon⟩)
    rw [Xsum_eq_zero_of_lt a N hNℓ u (2 * u), abs_zero, mul_zero]

/-! ### The two integrands -/

/-- The (B′)-integrand at the scale `v`: `∑_{ℓ ≤ N} w(ℓ)·|∑_{v < b ≤ 2v} μ(b)a(bℓ)|`. -/
def Bint (a : ℕ → ℝ) (N : ℕ) (w : ℕ → ℝ) (v : ℝ) : ℝ :=
  ∑ ℓ ∈ Finset.Icc 1 N, w ℓ * |Xsum a N ℓ v (2 * v)|

/-- The smoothed (B′)-sum at the dyadic level `J`: `∑_{ℓ ≤ N} w(ℓ)·|∑_{u < b ≤ 2^J u} μ(b)a(bℓ)|`. -/
def Xavg (a : ℕ → ℝ) (N : ℕ) (w : ℕ → ℝ) (J : ℕ) (u : ℝ) : ℝ :=
  ∑ ℓ ∈ Finset.Icc 1 N, w ℓ * |Xsum a N ℓ u ((2 : ℝ) ^ J * u)|

/-- `BprimeWindow` in terms of `Bint`. -/
lemma Xavg_eq_zero_of_nonpos (a : ℕ → ℝ) (N : ℕ) (w : ℕ → ℝ) (J : ℕ) {u : ℝ} (hu : u ≤ 0) :
    Xavg a N w J u = 0 := by
  simp only [Xavg]
  refine Finset.sum_eq_zero (fun ℓ _ => ?_)
  rw [Xsum_of_nonpos a N ℓ u (mul_nonpos_of_nonneg_of_nonpos (by positivity) hu), abs_zero,
    mul_zero]

lemma Bint_eq_zero_of_nonpos (a : ℕ → ℝ) (N : ℕ) (w : ℕ → ℝ) {v : ℝ} (hv : v ≤ 0) :
    Bint a N w v = 0 := by
  simp only [Bint]
  refine Finset.sum_eq_zero (fun ℓ _ => ?_)
  rw [Xsum_of_nonpos a N ℓ v (mul_nonpos_of_nonneg_of_nonpos (by norm_num) hv), abs_zero,
    mul_zero]

lemma BprimeWindow_iff (a : ℕ → ℝ) (N : ℕ) (w : ℕ → ℝ) (E lo hi : ℝ) :
    BprimeWindow a N w E lo hi ↔ ∀ t : ℝ, lo ≤ t → t ≤ hi → Bint a N w t ≤ E := Iff.rfl

lemma measurable_Bint (a : ℕ → ℝ) (N : ℕ) (w : ℕ → ℝ) : Measurable (Bint a N w) := by
  have h : Bint a N w = fun v => ∑ ℓ ∈ Finset.Icc 1 N,
      w ℓ * |Xsum a N ℓ v (2 * v)| := rfl
  rw [h]
  exact Finset.measurable_sum _ (fun ℓ _ =>
    ((measurable_Xsum a N ℓ (by norm_num : (0:ℝ) < 2)).abs).const_mul (w ℓ))

lemma measurable_Xavg (a : ℕ → ℝ) (N : ℕ) (w : ℕ → ℝ) (J : ℕ) : Measurable (Xavg a N w J) := by
  have h : Xavg a N w J = fun u => ∑ ℓ ∈ Finset.Icc 1 N,
      w ℓ * |Xsum a N ℓ u ((2 : ℝ) ^ J * u)| := rfl
  rw [h]
  exact Finset.measurable_sum _ (fun ℓ _ =>
    ((measurable_Xsum a N ℓ (pow_pos (by norm_num) J)).abs).const_mul (w ℓ))

/-- Pointwise bound of `|Xsum a N ℓ v (2v)|` by the trivial mass of the sequence. -/
lemma abs_Xsum_le (a : ℕ → ℝ) (N ℓ : ℕ) (t u : ℝ) :
    |Xsum a N ℓ t u| ≤ ∑ b ∈ Finset.Icc 1 N, |a (b * ℓ)| := by
  simp only [Xsum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum (fun b _ => ?_)).trans
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun _ _ _ => abs_nonneg _))
  rw [abs_mul]
  exact mul_le_of_le_one_left (abs_nonneg _) (abs_moebius_cast_le_one b)

lemma abs_Bint_le (a : ℕ → ℝ) (N : ℕ) (w : ℕ → ℝ) (v : ℝ) :
    |Bint a N w v| ≤ ∑ ℓ ∈ Finset.Icc 1 N, |w ℓ| * ∑ b ∈ Finset.Icc 1 N, |a (b * ℓ)| := by
  simp only [Bint]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun ℓ _ => ?_))
  rw [abs_mul, abs_abs]
  exact mul_le_mul_of_nonneg_left (abs_Xsum_le a N ℓ v (2 * v)) (abs_nonneg _)

lemma abs_Xavg_le (a : ℕ → ℝ) (N : ℕ) (w : ℕ → ℝ) (J : ℕ) (u : ℝ) :
    |Xavg a N w J u| ≤ ∑ ℓ ∈ Finset.Icc 1 N, |w ℓ| * ∑ b ∈ Finset.Icc 1 N, |a (b * ℓ)| := by
  simp only [Xavg]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun ℓ _ => ?_))
  rw [abs_mul, abs_abs]
  exact mul_le_mul_of_nonneg_left (abs_Xsum_le a N ℓ u ((2:ℝ)^J * u)) (abs_nonneg _)

/-- A function that is measurable and bounded, divided by `u`, is interval-integrable
on `[p,q]` with `0 < p ≤ q`. -/
lemma intervalIntegrable_div_of_bound {f : ℝ → ℝ} {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q)
    (hf : Measurable f) (C : ℝ) (hC : ∀ u, |f u| ≤ C) :
    IntervalIntegrable (fun u => f u / u) volume p q :=
  intervalIntegrable_div_Ioc hf hp hpq C (fun u _ => hC u)

lemma intervalIntegrable_Bint_div (a : ℕ → ℝ) (N : ℕ) (w : ℕ → ℝ) {c p q : ℝ}
    (hp : 0 < p) (hpq : p ≤ q) :
    IntervalIntegrable (fun u => Bint a N w (c * u) / u) volume p q :=
  intervalIntegrable_div_of_bound hp hpq ((measurable_Bint a N w).comp (measurable_const_mul c))
    _ (fun u => abs_Bint_le a N w (c * u))

lemma intervalIntegrable_Xavg_div (a : ℕ → ℝ) (N : ℕ) (w : ℕ → ℝ) (J : ℕ) {p q : ℝ}
    (hp : 0 < p) (hpq : p ≤ q) :
    IntervalIntegrable (fun u => Xavg a N w J u / u) volume p q :=
  intervalIntegrable_div_of_bound hp hpq (measurable_Xavg a N w J) _
    (fun u => abs_Xavg_le a N w J u)

/-! ### The two elementary changes of variables -/

/-- `∫_a^b Φ(y/c)/y dy = ∫_{a/c}^{b/c} Φ(u)/u du`. -/
lemma integral_comp_div_div_div {Φ : ℝ → ℝ} {c : ℝ} (hc : 0 < c) (a b : ℝ) :
    (∫ y in a..b, Φ (y / c) / y) = ∫ u in a / c..b / c, Φ u / u := by
  have hpt : ∀ y : ℝ, Φ (y / c) / (y / c) / c = Φ (y / c) / y := by
    intro y
    by_cases hy : y = 0
    · subst hy; simp
    · rw [div_div, div_mul_cancel₀ _ hc.ne']
  have hcongr : (∫ y in a..b, Φ (y / c) / (y / c) / c) = ∫ y in a..b, Φ (y / c) / y :=
    intervalIntegral.integral_congr (fun y _ => hpt y)
  rw [← hcongr]
  exact integral_comp_div_div (Φ := fun u => Φ u / u) hc a b

/-- `∫_a^b Φ(c·u)/u du = ∫_{ca}^{cb} Φ(v)/v dv`. -/
lemma integral_comp_mul_div {Φ : ℝ → ℝ} {c : ℝ} (hc : 0 < c) (a b : ℝ) :
    (∫ u in a..b, Φ (c * u) / u) = ∫ v in c * a..c * b, Φ v / v := by
  have h1 : (fun u : ℝ => Φ (c * u) / u)
      = fun u => c * ((fun v : ℝ => Φ v / v) (c * u)) := by
    funext u
    show Φ (c * u) / u = c * (Φ (c * u) / (c * u))
    rw [← mul_div_assoc, mul_div_mul_left _ _ hc.ne']
  rw [h1, intervalIntegral.integral_const_mul]
  have h2 : (∫ x in a..b, (fun v : ℝ => Φ v / v) (c * x))
      = c⁻¹ * ∫ x in c * a..c * b, Φ x / x := by
    simpa only [smul_eq_mul] using
      intervalIntegral.integral_comp_mul_left (fun v : ℝ => Φ v / v) hc.ne' (a := a) (b := b)
  rw [h2, ← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]

/-! ### The dyadic pieces -/

/-- The `j`-th dyadic piece: averaging `v ↦ Bint a N w (2^j v)` over `v ∈ [Y/Δ, eY]`. -/
lemma smAvg_Bint_le (a : ℕ → ℝ) (N : ℕ) (w : ℕ → ℝ) {E Y : ℝ} {J j : ℕ} {Δ : ℕ}
    (hj : j < J) (hY : 0 < Y) (hΔ : 1 ≤ Δ) (_hE : 0 ≤ E)
    (hB : BprimeWindow a N w E (Y / (Δ : ℝ)) ((2 : ℝ) ^ J * (Real.exp 1 * Y))) :
    (∫ u in Y / (Δ : ℝ)..(Real.exp 1 * Y), Bint a N w ((2 : ℝ) ^ j * u) / u)
      ≤ E * (1 + Real.log (Δ : ℝ)) := by
  have hc : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
  have hΔpos : (0 : ℝ) < (Δ : ℝ) := by exact_mod_cast (by omega : 0 < Δ)
  have hΔ1 : (1 : ℝ) ≤ (Δ : ℝ) := by exact_mod_cast hΔ
  have hYΔ : 0 < Y / (Δ : ℝ) := div_pos hY hΔpos
  have heY : 0 < Real.exp 1 * Y := mul_pos (Real.exp_pos 1) hY
  have hAB : Y / (Δ : ℝ) ≤ Real.exp 1 * Y := by
    have he1 : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp_iff.mpr (by norm_num : (0:ℝ) ≤ 1)
    have h1 : (1 : ℝ) ≤ Real.exp 1 * (Δ : ℝ) := by nlinarith [he1, hΔ1]
    calc Y / (Δ : ℝ) = Y * (Δ : ℝ)⁻¹ := rfl
      _ ≤ Y := by
          rw [mul_le_iff_le_one_right hY]
          exact inv_le_one_of_one_le₀ hΔ1
      _ ≤ Real.exp 1 * Y := by
          simpa using mul_le_mul_of_nonneg_right he1 hY.le
  rw [integral_comp_mul_div (Φ := Bint a N w) hc (Y / (Δ : ℝ)) (Real.exp 1 * Y)]
  have hcl : (2 : ℝ) ^ j * (Y / (Δ : ℝ)) ≤ (2 : ℝ) ^ j * (Real.exp 1 * Y) :=
    mul_le_mul_of_nonneg_left hAB hc.le
  have hp : 0 < (2 : ℝ) ^ j * (Y / (Δ : ℝ)) := mul_pos hc hYΔ
  have hq : 0 < (2 : ℝ) ^ j * (Real.exp 1 * Y) := mul_pos hc heY
  refine (intervalIntegral.integral_mono_ae_restrict (f := fun v => Bint a N w v / v)
    (g := fun v => E / v) hcl ?_ ?_ ?_).trans ?_
  · simpa using intervalIntegrable_Bint_div (a := a) (N := N) (w := w) (c := 1) hp hcl
  · simpa using intervalIntegrable_div_Ioc (G := fun _ : ℝ => E) measurable_const hp hcl
      (|E|) (fun u _ => le_refl _)
  · change ∀ᵐ v ∂(volume.restrict (Set.Icc ((2 : ℝ) ^ j * (Y / (Δ : ℝ)))
        ((2 : ℝ) ^ j * (Real.exp 1 * Y)))), Bint a N w v / v ≤ E / v
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    refine Filter.Eventually.of_forall (fun v hv => ?_)
    obtain ⟨hv1, hv2⟩ := Set.mem_Icc.mp hv
    have hv0 : 0 < v := lt_of_lt_of_le hp hv1
    have hle1 : Y / (Δ : ℝ) ≤ v :=
      le_trans (by
        calc Y / (Δ : ℝ) = 1 * (Y / (Δ : ℝ)) := (one_mul _).symm
          _ ≤ (2 : ℝ) ^ j * (Y / (Δ : ℝ)) :=
              mul_le_mul_of_nonneg_right (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)) hYΔ.le) hv1
    have hle2 : v ≤ (2 : ℝ) ^ J * (Real.exp 1 * Y) :=
      le_trans hv2 (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hj.le) heY.le)
    exact div_le_div_of_nonneg_right (hB v hle1 hle2) hv0.le
  · have hcongr : (∫ v in (2 : ℝ) ^ j * (Y / (Δ : ℝ))..(2 : ℝ) ^ j * (Real.exp 1 * Y), E / v)
        = ∫ v in (2 : ℝ) ^ j * (Y / (Δ : ℝ))..(2 : ℝ) ^ j * (Real.exp 1 * Y), E * (1 / v) := by
      refine intervalIntegral.integral_congr (fun v _ => ?_)
      rw [div_eq_mul_inv, one_div]
    rw [hcongr, intervalIntegral.integral_const_mul, integral_one_div_of_pos hp hq]
    rw [mul_div_mul_left _ _ hc.ne']
    have hYd : (Real.exp 1 * Y) / (Y / (Δ : ℝ)) = Real.exp 1 * (Δ : ℝ) := by
      field_simp
    rw [hYd, Real.log_mul (Real.exp_ne_zero 1) (ne_of_gt hΔpos), Real.log_exp]

/-! ### The smoothed §7 core -/

/-- **§7 core**: the smoothed, dyadically split bilinear sum is bounded by `(B′)`.

For `s = 2^J` a power of two, the average over `y ∈ [Y, eY]` with weight `dy/y` of
`∑_{ℓ ≤ N} w(ℓ)|∑_{y < b ≤ sy} μ(b)a(bℓ)|` is at most `J·E·(1 + log Δ)`, whenever the
hypothesis (B′) holds on the window `[Y/Δ, s·eY]`. -/
theorem smAvg_Xsum_le (a : ℕ → ℝ) (N : ℕ) {w : ℕ → ℝ} {s E Y : ℝ} {J : ℕ} {Δ : ℕ}
    (hs : s = (2 : ℝ) ^ J) (hY : 0 < Y) (hΔ : 1 ≤ Δ) (hw0 : ∀ ℓ, 0 ≤ w ℓ) (hE : 0 ≤ E)
    (hB : BprimeWindow a N w E (Y / (Δ : ℝ)) (s * (Real.exp 1 * Y))) :
    (∫ u in Y / (Δ : ℝ)..(Real.exp 1 * Y),
        (∑ ℓ ∈ Finset.Icc 1 N, w ℓ * |Xsum a N ℓ u (s * u)|) / u)
      ≤ (J : ℝ) * (E * (1 + Real.log (Δ : ℝ))) := by
  subst hs
  have hΔpos : (0 : ℝ) < (Δ : ℝ) := by exact_mod_cast (by omega : 0 < Δ)
  have hΔ1 : (1 : ℝ) ≤ (Δ : ℝ) := by exact_mod_cast hΔ
  have hYΔ : 0 < Y / (Δ : ℝ) := div_pos hY hΔpos
  have heY : 0 < Real.exp 1 * Y := mul_pos (Real.exp_pos 1) hY
  have hAB : Y / (Δ : ℝ) ≤ Real.exp 1 * Y := by
    have he1 : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp_iff.mpr (by norm_num : (0:ℝ) ≤ 1)
    calc Y / (Δ : ℝ) = Y * (Δ : ℝ)⁻¹ := rfl
      _ ≤ Y := by
          rw [mul_le_iff_le_one_right hY]
          exact inv_le_one_of_one_le₀ hΔ1
      _ ≤ Real.exp 1 * Y := by
          simpa using mul_le_mul_of_nonneg_right he1 hY.le
  have htw : ∀ (j : ℕ) (u : ℝ), (2 : ℝ) ^ (j + 1) * u = 2 * ((2 : ℝ) ^ j * u) := by
    intro j u; rw [pow_succ]; ring
  -- the pointwise dyadic split
  have hpointF : ∀ u : ℝ, Xavg a N w J u
      ≤ ∑ j ∈ Finset.range J, Bint a N w ((2 : ℝ) ^ j * u) := by
    intro u
    simp only [Xavg]
    calc ∑ ℓ ∈ Finset.Icc 1 N, w ℓ * |Xsum a N ℓ u ((2 : ℝ) ^ J * u)|
        ≤ ∑ ℓ ∈ Finset.Icc 1 N,
            w ℓ * ∑ j ∈ Finset.range J,
              |Xsum a N ℓ ((2 : ℝ) ^ j * u) ((2 : ℝ) ^ (j + 1) * u)| :=
          Finset.sum_le_sum (fun ℓ _ =>
            mul_le_mul_of_nonneg_left (Xsum_abs_dyadic_le a N ℓ J u) (hw0 ℓ))
      _ = ∑ j ∈ Finset.range J, ∑ ℓ ∈ Finset.Icc 1 N,
            w ℓ * |Xsum a N ℓ ((2 : ℝ) ^ j * u) ((2 : ℝ) ^ (j + 1) * u)| := by
          simp only [Finset.mul_sum]
          exact Finset.sum_comm
      _ = ∑ j ∈ Finset.range J, Bint a N w ((2 : ℝ) ^ j * u) := by
          refine Finset.sum_congr rfl (fun j _ => ?_)
          simp only [Bint]
          exact Finset.sum_congr rfl (fun ℓ _ => by rw [htw j u])
  -- the a.e. pointwise bound on `[Y/Δ, eY]` (where `u > 0`)
  have hpt : ∀ u : ℝ, Xavg a N w J u / u
      ≤ ∑ j ∈ Finset.range J, Bint a N w ((2 : ℝ) ^ j * u) / u := by
    intro u
    rcases lt_or_ge u 0 with hu | hu
    · rw [Xavg_eq_zero_of_nonpos a N w J hu.le, zero_div]
      exact Finset.sum_nonneg (fun j _ => by
        rw [Bint_eq_zero_of_nonpos a N w (mul_nonpos_of_nonneg_of_nonpos (by positivity) hu.le),
          zero_div])
    · rcases eq_or_lt_of_le hu with h0 | hpos
      · subst h0
        rw [Xavg_eq_zero_of_nonpos a N w J le_rfl, zero_div]
        exact Finset.sum_nonneg (fun j _ => by
          rw [Bint_eq_zero_of_nonpos a N w (by simp : (2 : ℝ) ^ j * 0 ≤ 0), zero_div])
      · rw [← Finset.sum_div]
        exact div_le_div_of_nonneg_right (hpointF u) hpos.le
  calc (∫ u in Y / (Δ : ℝ)..(Real.exp 1 * Y), Xavg a N w J u / u)
      ≤ ∫ u in Y / (Δ : ℝ)..(Real.exp 1 * Y),
          ∑ j ∈ Finset.range J, Bint a N w ((2 : ℝ) ^ j * u) / u :=
        intervalIntegral.integral_mono hAB
          (intervalIntegrable_Xavg_div a N w J hYΔ hAB)
          (by simpa only [Finset.sum_fn] using
            (IntervalIntegrable.sum (Finset.range J)
              (fun j _ => intervalIntegrable_Bint_div (a := a) (N := N) (w := w)
                (c := (2 : ℝ) ^ j) hYΔ hAB))) hpt
    _ = ∑ j ∈ Finset.range J,
          ∫ u in Y / (Δ : ℝ)..(Real.exp 1 * Y), Bint a N w ((2 : ℝ) ^ j * u) / u :=
        intervalIntegral.integral_finsetSum (fun j _ =>
          intervalIntegrable_Bint_div (a := a) (N := N) (w := w) (c := (2 : ℝ) ^ j) hYΔ hAB)
    _ ≤ ∑ _j ∈ Finset.range J, E * (1 + Real.log (Δ : ℝ)) :=
        Finset.sum_le_sum (fun j hj =>
          smAvg_Bint_le a N w (Finset.mem_range.mp hj) hY hΔ hE hB)
    _ = (J : ℝ) * (E * (1 + Real.log (Δ : ℝ))) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

end

end Submission.ASP
