import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedVariables false

/-!
# A uniform bound for the derivatives of a bumped monomial

Let `φ : ℝ → ℝ` be smooth and *flat outside* `[-2,2]`: all its iterated derivatives (including
the `0`-th one, i.e. `φ` itself) vanish on `{|t| ≥ 2}`.  For `ε > 0` the function

`F_ε(s) = φ (s / ε) * s ^ n / n !`

is smooth and compactly supported.  The main result of this file bounds its `a`-th Fréchet
derivative, for `a ≤ n`, by

`ε ^ (n - a) * ∑_{d ≤ a} C(a,d) Φ(a-d) · 8`,

where `Φ j` is any nonnegative bound for `‖φ^{(j)}‖`.

The proof rescales `F_ε(s) = ε ^ n · G (s / ε)` with `G u = φ u * u ^ n / n !`, so it suffices to
bound the derivatives of `G`.  The Leibniz rule for `iteratedDeriv` expands `G^{(a)}` into
binomial terms; near the support `|u| ≤ 2` the monomial factor is estimated by
`2 ^ m / m ! ≤ 8`, while outside it every term contains a vanishing derivative of `φ`.
-/

namespace Work.Diff.EXT

open Filter
open scoped Topology

/-- `2 ^ m / m ! ≤ 8` for every `m : ℕ`. -/
lemma bbl_two_pow_div_factorial_le_eight (m : ℕ) :
    (2 : ℝ) ^ m / (m.factorial : ℝ) ≤ 8 := by
  have hnat : ∀ m : ℕ, 2 ^ m ≤ 2 * m.factorial := by
    intro m
    induction m with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, Nat.factorial_succ]
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk; norm_num
      · calc 2 ^ k * 2 ≤ (2 * k.factorial) * 2 := Nat.mul_le_mul_right 2 ih
          _ = 4 * k.factorial := by ring
          _ ≤ 2 * (k + 1) * k.factorial := by
              have h : (4 : ℕ) ≤ 2 * (k + 1) := by omega
              exact Nat.mul_le_mul_right k.factorial h
          _ = 2 * ((k + 1) * k.factorial) := by ring
  have hcast : (2 : ℝ) ^ m ≤ 2 * (m.factorial : ℝ) := by exact_mod_cast hnat m
  have hpos : (0 : ℝ) < (m.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos m
  rw [div_le_iff₀ hpos]
  nlinarith

/-- Power arithmetic: `ε ^ m * (ε⁻¹) ^ b = ε ^ (m - b)` for `ε > 0` and `b ≤ m`. -/
lemma bbl_pow_mul_inv_pow (ε : ℝ) (hε : 0 < ε) {m b : ℕ} (hb : b ≤ m) :
    ε ^ m * (ε⁻¹) ^ b = ε ^ (m - b) := by
  rw [inv_pow, ← pow_sub₀ ε hε.ne' hb]

/-- The `i`-th derivative of the monomial `s ↦ s ^ n`, as an explicit product. -/
lemma bbl_norm_iteratedDeriv_pow (n i : ℕ) (t : ℝ) :
    ‖iteratedDeriv i (fun s : ℝ => s ^ n) t‖ = (n.descFactorial i : ℝ) * |t| ^ (n - i) := by
  rw [iteratedDeriv_pow, norm_mul, norm_pow, Real.norm_natCast, Real.norm_eq_abs]

/-- For `i > n` the `i`-th derivative of the monomial `s ↦ s ^ n` vanishes. -/
lemma bbl_iteratedDeriv_pow_eq_zero_of_lt {n i : ℕ} (h : n < i) (t : ℝ) :
    iteratedDeriv i (fun s : ℝ => s ^ n) t = 0 := by
  rw [iteratedDeriv_pow, Nat.descFactorial_eq_zero_iff_lt.mpr h, Nat.cast_zero, zero_mul]

/-- Monomial estimate: for `i ≤ n` and `|t| ≤ 2 ε`,
`‖(s ↦ s ^ n)^{(i)}(t)‖ / n ! ≤ 2 ^ (n - i) ε ^ (n - i) / (n - i)!`. -/
lemma bbl_norm_iteratedDeriv_pow_div_factorial_le
    (n i : ℕ) (hi : i ≤ n) (t ε : ℝ) (hε : 0 < ε) (ht : |t| ≤ 2 * ε) :
    ‖iteratedDeriv i (fun s : ℝ => s ^ n) t‖ / (n.factorial : ℝ)
      ≤ 2 ^ (n - i) * ε ^ (n - i) / ((n - i).factorial : ℝ) := by
  have hfac : (n.descFactorial i : ℝ) * ((n - i).factorial : ℝ) = (n.factorial : ℝ) := by
    rw [← Nat.cast_mul, Nat.mul_comm, Nat.factorial_mul_descFactorial hi]
  have h1 : (0 : ℝ) < (n.factorial : ℝ) := by positivity
  have h2 : (0 : ℝ) < ((n - i).factorial : ℝ) := by positivity
  have hsplit : (n.descFactorial i : ℝ) / (n.factorial : ℝ) = 1 / ((n - i).factorial : ℝ) := by
    rw [div_eq_div_iff (ne_of_gt h1) (ne_of_gt h2), one_mul]
    exact hfac
  rw [bbl_norm_iteratedDeriv_pow]
  calc (n.descFactorial i : ℝ) * |t| ^ (n - i) / (n.factorial : ℝ)
      = (1 / ((n - i).factorial : ℝ)) * |t| ^ (n - i) := by
          rw [← div_mul_eq_mul_div, hsplit]
    _ ≤ (1 / ((n - i).factorial : ℝ)) * (2 ^ (n - i) * ε ^ (n - i)) := by
          refine mul_le_mul_of_nonneg_left ?_ (le_of_lt (one_div_pos.mpr h2))
          rw [← mul_pow]
          exact pow_le_pow_left₀ (abs_nonneg t) ht (n - i)
    _ = 2 ^ (n - i) * ε ^ (n - i) / ((n - i).factorial : ℝ) := by ring

/-- Rescaling bound: `‖(φ (· / ε))^{(m)}(t)‖ ≤ (ε⁻¹) ^ m * Φ m`. -/
lemma bbl_chain_bound
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (Φ : ℕ → ℝ)
    (hΦ : ∀ j t, ‖iteratedFDeriv ℝ j φ t‖ ≤ Φ j) (ε : ℝ) (hε : 0 < ε) (m : ℕ) (t : ℝ) :
    ‖iteratedDeriv m (fun s : ℝ => φ (s / ε)) t‖ ≤ (ε⁻¹) ^ m * Φ m := by
  have hcongr : (fun s : ℝ => φ (s / ε)) = fun s : ℝ => φ (ε⁻¹ * s) := by
    funext s
    rw [div_eq_inv_mul]
  rw [hcongr, iteratedDeriv_comp_const_mul (hφ.of_le (by simp)) (ε⁻¹)]
  have hφm : ‖iteratedDeriv m φ (ε⁻¹ * t)‖ ≤ Φ m := by
    rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    exact hΦ m (ε⁻¹ * t)
  rw [norm_mul, norm_pow, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hε.le)]
  exact mul_le_mul_of_nonneg_left hφm (pow_nonneg (inv_nonneg.mpr hε.le) m)

/-- Far from the support the bumped monomial is *eventually* zero, hence all its derivatives
at `t` vanish. -/
lemma bbl_iteratedDeriv_eq_zero_of_far
    (φ : ℝ → ℝ) (hzero : ∀ j t, 2 ≤ |t| → iteratedFDeriv ℝ j φ t = 0)
    (ε : ℝ) (hε : 0 < ε) (a n : ℕ) (t : ℝ) (ht : 2 * ε < |t|) :
    iteratedDeriv a (fun s : ℝ => φ (s / ε) * s ^ n / (n.factorial : ℝ)) t = 0 := by
  have hφ0 : ∀ᶠ s in 𝓝 t, φ (s / ε) = 0 := by
    have hδ : 0 < |t| - 2 * ε := by linarith
    filter_upwards [Metric.ball_mem_nhds t hδ] with s hs
    have hst : |s - t| < |t| - 2 * ε := by
      simpa [Metric.mem_ball, Real.dist_eq] using hs
    have hsabs : 2 * ε < |s| := by
      have h1 := abs_sub_abs_le_abs_sub t s
      rw [abs_sub_comm] at hst
      linarith
    have h2 : 2 ≤ |s / ε| := by
      rw [abs_div, abs_of_pos hε, le_div_iff₀ hε]
      linarith
    have h4 : ‖iteratedFDeriv ℝ 0 φ (s / ε)‖ = 0 := by rw [hzero 0 (s / ε) h2, norm_zero]
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_zero] at h4
    exact norm_eq_zero.mp h4
  have hev : (fun s : ℝ => φ (s / ε) * s ^ n / (n.factorial : ℝ)) =ᶠ[𝓝 t] (fun _ : ℝ => 0) := by
    filter_upwards [hφ0] with s hs
    rw [hs, zero_mul, zero_div]
  rw [Filter.EventuallyEq.iteratedDeriv_eq a hev]
  simp

/-- The elementary relaxation
`(2 ^ (n-i) ε ^ (n-i) / (n-i)!) * (ε⁻¹) ^ (a-i) ≤ ε ^ (n-a) * 8` used to pass from the
Leibniz term bound to the stated constant. -/
lemma bbl_relax (ε : ℝ) (hε : 0 < ε) {n a i : ℕ} (hi : i ≤ a) (han : a ≤ n) :
    (2 ^ (n - i) * ε ^ (n - i) / ((n - i).factorial : ℝ)) * (ε⁻¹) ^ (a - i)
      ≤ ε ^ (n - a) * 8 := by
  have hb : a - i ≤ n - i := Nat.sub_le_sub_right han i
  have hmn : n - i - (a - i) = n - a := by omega
  have hpow : ε ^ (n - i) * (ε⁻¹) ^ (a - i) = ε ^ (n - a) := by
    rw [bbl_pow_mul_inv_pow ε hε hb, hmn]
  have h8 : (2 : ℝ) ^ (n - i) / ((n - i).factorial : ℝ) ≤ 8 :=
    bbl_two_pow_div_factorial_le_eight (n - i)
  have hεp : 0 ≤ ε ^ (n - a) := pow_nonneg hε.le _
  calc (2 ^ (n - i) * ε ^ (n - i) / ((n - i).factorial : ℝ)) * (ε⁻¹) ^ (a - i)
      = (2 ^ (n - i) / ((n - i).factorial : ℝ)) * (ε ^ (n - i) * (ε⁻¹) ^ (a - i)) := by ring
    _ = (2 ^ (n - i) / ((n - i).factorial : ℝ)) * ε ^ (n - a) := by rw [hpow]
    _ ≤ 8 * ε ^ (n - a) := mul_le_mul_of_nonneg_right h8 hεp
    _ = ε ^ (n - a) * 8 := by ring

/-- The `i`-th Leibniz term of the `a`-th derivative of the bumped monomial is bounded by
`ε ^ (n - a) · C(a,i) Φ(a-i) · 8`. -/
lemma bbl_term_bound
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (Φ : ℕ → ℝ)
    (hΦ : ∀ j t, ‖iteratedFDeriv ℝ j φ t‖ ≤ Φ j) (hΦnn : ∀ j, 0 ≤ Φ j)
    (ε : ℝ) (hε : 0 < ε) {a n : ℕ} (han : a ≤ n) {t : ℝ} (ht : |t| ≤ 2 * ε)
    {i : ℕ} (hi : i ∈ Finset.range (a + 1)) :
    ‖(a.choose i : ℝ) * iteratedDeriv i (fun s : ℝ => s ^ n) t
        * iteratedDeriv (a - i) (fun s : ℝ => φ (s / ε)) t‖ / (n.factorial : ℝ)
      ≤ ε ^ (n - a) * ((a.choose i : ℝ) * Φ (a - i) * 8) := by
  have hia : i ≤ a := by
    have := Finset.mem_range.mp hi
    omega
  by_cases hin : i ≤ n
  · have hC : 0 ≤ (a.choose i : ℝ) := Nat.cast_nonneg _
    have hD := bbl_norm_iteratedDeriv_pow_div_factorial_le n i hin t ε hε ht
    have hE := bbl_chain_bound φ hφ Φ hΦ ε hε (a - i) t
    have hposD : 0 ≤ 2 ^ (n - i) * ε ^ (n - i) / ((n - i).factorial : ℝ) := by positivity
    have hXY : (a.choose i : ℝ)
          * (‖iteratedDeriv i (fun s : ℝ => s ^ n) t‖ / (n.factorial : ℝ))
        ≤ (a.choose i : ℝ) * (2 ^ (n - i) * ε ^ (n - i) / ((n - i).factorial : ℝ)) :=
      mul_le_mul_of_nonneg_left hD hC
    have hYZ : 0 ≤ (a.choose i : ℝ) * (2 ^ (n - i) * ε ^ (n - i) / ((n - i).factorial : ℝ)) :=
      mul_nonneg hC hposD
    calc ‖(a.choose i : ℝ) * iteratedDeriv i (fun s : ℝ => s ^ n) t
            * iteratedDeriv (a - i) (fun s : ℝ => φ (s / ε)) t‖ / (n.factorial : ℝ)
        = (a.choose i : ℝ) * (‖iteratedDeriv i (fun s : ℝ => s ^ n) t‖ / (n.factorial : ℝ))
            * ‖iteratedDeriv (a - i) (fun s : ℝ => φ (s / ε)) t‖ := by
          simp only [norm_mul, Real.norm_natCast]
          ring
      _ ≤ (a.choose i : ℝ) * (2 ^ (n - i) * ε ^ (n - i) / ((n - i).factorial : ℝ))
            * ((ε⁻¹) ^ (a - i) * Φ (a - i)) :=
          mul_le_mul hXY hE (norm_nonneg _) hYZ
      _ = ((a.choose i : ℝ) * Φ (a - i))
            * ((2 ^ (n - i) * ε ^ (n - i) / ((n - i).factorial : ℝ)) * (ε⁻¹) ^ (a - i)) := by
          ring
      _ ≤ ((a.choose i : ℝ) * Φ (a - i)) * (ε ^ (n - a) * 8) :=
          mul_le_mul_of_nonneg_left (bbl_relax ε hε hia han) (mul_nonneg hC (hΦnn _))
      _ = ε ^ (n - a) * ((a.choose i : ℝ) * Φ (a - i) * 8) := by ring
  · have hin' : n < i := Nat.lt_of_not_le hin
    have hz : ‖(a.choose i : ℝ) * iteratedDeriv i (fun s : ℝ => s ^ n) t
        * iteratedDeriv (a - i) (fun s : ℝ => φ (s / ε)) t‖ = 0 := by
      rw [bbl_iteratedDeriv_pow_eq_zero_of_lt hin' t, mul_zero, zero_mul, norm_zero]
    rw [hz, zero_div]
    exact mul_nonneg (pow_nonneg hε.le _)
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hΦnn _)) (by norm_num))

theorem borel_bump_pow_le
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (Φ : ℕ → ℝ)
    (hΦ : ∀ j t, ‖iteratedFDeriv ℝ j φ t‖ ≤ Φ j) (hΦnn : ∀ j, 0 ≤ Φ j)
    (hzero : ∀ j t, 2 ≤ |t| → iteratedFDeriv ℝ j φ t = 0)
    (ε : ℝ) (hε : 0 < ε) {a n : ℕ} (han : a ≤ n) (t : ℝ) :
    ‖iteratedFDeriv ℝ a (fun s : ℝ => φ (s / ε) * s ^ n / (n.factorial : ℝ)) t‖ ≤
      ε ^ (n - a) * ∑ d ∈ Finset.range (a + 1), (a.choose d : ℝ) * Φ (a - d) * 8 := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  by_cases hfar : 2 * ε < |t|
  · rw [bbl_iteratedDeriv_eq_zero_of_far φ hzero ε hε a n t hfar, norm_zero]
    refine mul_nonneg (pow_nonneg hε.le _) (Finset.sum_nonneg fun d _ => ?_)
    have h1 : (0 : ℝ) ≤ (a.choose d : ℝ) := Nat.cast_nonneg _
    have h2 : 0 ≤ Φ (a - d) := hΦnn _
    nlinarith
  · have hnear : |t| ≤ 2 * ε := le_of_not_gt hfar
    have hf : ContDiffAt ℝ ((a : ℕ) : ℕ∞) (fun s : ℝ => s ^ n) t := by fun_prop
    have hg : ContDiffAt ℝ ((a : ℕ) : ℕ∞) (fun s : ℝ => φ (s / ε)) t :=
      (((hφ.of_le (by simp)).comp (contDiff_id.div_const ε)).contDiffAt)
    have hleib : iteratedDeriv a (fun s : ℝ => φ (s / ε) * s ^ n) t
        = ∑ i ∈ Finset.range (a + 1), (a.choose i : ℝ) * iteratedDeriv i (fun s : ℝ => s ^ n) t
            * iteratedDeriv (a - i) (fun s : ℝ => φ (s / ε)) t := by
      have h := iteratedDeriv_mul (𝕜 := ℝ) (n := a) (x := t)
        (f := fun s : ℝ => s ^ n) (g := fun s : ℝ => φ (s / ε)) hf hg
      have hfun : (fun s : ℝ => φ (s / ε) * s ^ n) = (fun s : ℝ => s ^ n * φ (s / ε)) := by
        funext s; ring
      rw [hfun]; exact h
    have hmain : iteratedDeriv a (fun s : ℝ => φ (s / ε) * s ^ n / (n.factorial : ℝ)) t
        = (∑ i ∈ Finset.range (a + 1), (a.choose i : ℝ) * iteratedDeriv i (fun s : ℝ => s ^ n) t
            * iteratedDeriv (a - i) (fun s : ℝ => φ (s / ε)) t) / (n.factorial : ℝ) := by
      rw [iteratedDeriv_div_const, hleib]
    rw [hmain, norm_div, Real.norm_natCast]
    calc ‖∑ i ∈ Finset.range (a + 1), (a.choose i : ℝ) * iteratedDeriv i (fun s : ℝ => s ^ n) t
              * iteratedDeriv (a - i) (fun s : ℝ => φ (s / ε)) t‖ / (n.factorial : ℝ)
        ≤ (∑ i ∈ Finset.range (a + 1), ‖(a.choose i : ℝ)
              * iteratedDeriv i (fun s : ℝ => s ^ n) t
              * iteratedDeriv (a - i) (fun s : ℝ => φ (s / ε)) t‖) / (n.factorial : ℝ) :=
          div_le_div_of_nonneg_right (norm_sum_le _ _) (by positivity)
      _ = ∑ i ∈ Finset.range (a + 1), ‖(a.choose i : ℝ)
              * iteratedDeriv i (fun s : ℝ => s ^ n) t
              * iteratedDeriv (a - i) (fun s : ℝ => φ (s / ε)) t‖ / (n.factorial : ℝ) := by
          rw [Finset.sum_div]
      _ ≤ ∑ i ∈ Finset.range (a + 1), ε ^ (n - a) * ((a.choose i : ℝ) * Φ (a - i) * 8) :=
          Finset.sum_le_sum fun i hi => bbl_term_bound φ hφ Φ hΦ hΦnn ε hε han hnear hi
      _ = ε ^ (n - a) * ∑ i ∈ Finset.range (a + 1), (a.choose i : ℝ) * Φ (a - i) * 8 := by
          rw [← Finset.mul_sum]

end Work.Diff.EXT

