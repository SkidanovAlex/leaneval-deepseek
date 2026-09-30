import Mathlib
import Submission.Work.BMF.halasz_plancherel_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory Filter
open scoped Topology

namespace Work.BMF

/-- The `n`-th summand `f n · log n · n^{-s}` of the Dirichlet series of `f`. -/
private noncomputable abbrev dterm (f : ℕ → ℂ) (s : ℂ) (n : ℕ) : ℂ :=
  (f n * (Real.log n : ℂ)) * (n : ℂ) ^ (-s)

/-- Termwise comparison for `Σ ‖log n‖ / n ^ (1+α)`: the `n`-th term is dominated by
`(2/α) n^{-(1+α/2)}`. -/
private lemma log_div_rpow_le (α : ℝ) (hα : 0 < α) (n : ℕ) :
    ‖Real.log n‖ / (n : ℝ) ^ (1 + α) ≤ (2 / α) * (n : ℝ) ^ (-(1 + α / 2)) := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h
    simp only [Nat.cast_zero, Real.log_zero, norm_zero, zero_div]
    exact mul_nonneg (by positivity) (Real.rpow_nonneg (le_refl 0) _)
  · have hn : (0 : ℝ) < (n : ℝ) := by exact_mod_cast h
    have hlog : ‖Real.log n‖ ≤ (n : ℝ) ^ (α / 2) / (α / 2) := by
      have h1 := Complex.norm_log_natCast_le_rpow_div n (show (0 : ℝ) < α / 2 by linarith)
      have h2 : ‖Real.log n‖ = ‖Complex.log (n : ℂ)‖ := by
        rw [← Complex.natCast_log, Complex.norm_real]
      rwa [h2]
    have hlog' : ‖Real.log n‖ ≤ (2 / α) * (n : ℝ) ^ (α / 2) := by
      calc ‖Real.log n‖ ≤ (n : ℝ) ^ (α / 2) / (α / 2) := hlog
        _ = (2 / α) * (n : ℝ) ^ (α / 2) := by
            rw [div_eq_mul_inv, inv_div, mul_comm]
    calc ‖Real.log n‖ / (n : ℝ) ^ (1 + α)
        ≤ ((2 / α) * (n : ℝ) ^ (α / 2)) / (n : ℝ) ^ (1 + α) :=
          div_le_div_of_nonneg_right hlog' (Real.rpow_nonneg hn.le _)
      _ = (2 / α) * ((n : ℝ) ^ (α / 2) / (n : ℝ) ^ (1 + α)) := by rw [mul_div_assoc]
      _ = (2 / α) * (n : ℝ) ^ (α / 2 - (1 + α)) := by rw [← Real.rpow_sub hn]
      _ = (2 / α) * (n : ℝ) ^ (-(1 + α / 2)) := by
          rw [show α / 2 - (1 + α) = -(1 + α / 2) by ring]

/-- For `α > 0`, `Σ_{n} ‖log n‖ / n^{1+α}` converges. -/
private lemma summable_norm_log_div_rpow (α : ℝ) (hα : 0 < α) :
    Summable (fun n : ℕ => ‖Real.log n‖ / (n : ℝ) ^ (1 + α)) := by
  refine Summable.of_nonneg_of_le
    (fun n => div_nonneg (norm_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg n) _))
    (fun n => log_div_rpow_le α hα n) ?_
  exact (Real.summable_nat_rpow.mpr (show -(1 + α / 2) < -1 by linarith)).mul_left (2 / α)

/-- Norm of the `n`-th summand of `dirSum`, compared with `‖log n‖ / n^{1+α}`. -/
private lemma norm_dterm_le (f : ℕ → ℂ) (hb : ∀ n, ‖f n‖ ≤ 1) (α τ : ℝ) {n : ℕ}
    (hn : 1 ≤ n) :
    ‖dterm f (((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I) n‖
      ≤ ‖Real.log n‖ / (n : ℝ) ^ (1 + α) := by
  have hn0 : 0 < n := hn
  have hnorm : ‖(n : ℂ) ^ (-(((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I))‖
      = ((n : ℝ) ^ (1 + α))⁻¹ := by
    rw [Complex.norm_natCast_cpow_of_pos hn0,
      show (-(((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)).re = -(1 + α) by simp,
      Real.rpow_neg (Nat.cast_nonneg n) (1 + α)]
  have h1 : ‖dterm f (((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I) n‖
      = ‖f n‖ * ‖Real.log n‖ * ((n : ℝ) ^ (1 + α))⁻¹ := by
    rw [norm_mul, norm_mul, hnorm, Complex.norm_real]
  rw [h1]
  calc ‖f n‖ * ‖Real.log n‖ * ((n : ℝ) ^ (1 + α))⁻¹
      ≤ 1 * ‖Real.log n‖ * ((n : ℝ) ^ (1 + α))⁻¹ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hb n) (norm_nonneg _))
          (inv_nonneg.mpr (Real.rpow_nonneg (Nat.cast_nonneg n) _))
    _ = ‖Real.log n‖ * ((n : ℝ) ^ (1 + α))⁻¹ := by rw [one_mul]
    _ = ‖Real.log n‖ / (n : ℝ) ^ (1 + α) := by rw [div_eq_mul_inv]

/-- Uniform bound `‖dirSum f α N τ‖ ≤ Σ_n ‖log n‖ / n^{1+α}`. -/
private lemma dirSum_norm_le (f : ℕ → ℂ) (hb : ∀ n, ‖f n‖ ≤ 1) (α : ℝ)
    (hsum : Summable (fun n : ℕ => ‖Real.log n‖ / (n : ℝ) ^ (1 + α))) (N : ℕ) (τ : ℝ) :
    ‖dirSum f α N τ‖ ≤ ∑' n : ℕ, ‖Real.log n‖ / (n : ℝ) ^ (1 + α) := by
  calc ‖dirSum f α N τ‖
      = ‖∑ n ∈ Finset.Icc 1 N, dterm f (((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I) n‖ := rfl
    _ ≤ ∑ n ∈ Finset.Icc 1 N,
          ‖dterm f (((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I) n‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Icc 1 N, ‖Real.log n‖ / (n : ℝ) ^ (1 + α) :=
        Finset.sum_le_sum (fun n hn => norm_dterm_le f hb α τ (Finset.mem_Icc.mp hn).1)
    _ ≤ ∑' n : ℕ, ‖Real.log n‖ / (n : ℝ) ^ (1 + α) :=
        Summable.sum_le_tsum (Finset.Icc 1 N)
          (fun i _ => div_nonneg (norm_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg i) _)) hsum

/-- `τ ↦ dirSum f α N τ` is continuous. -/
private lemma continuous_dirSum (f : ℕ → ℂ) (α : ℝ) (N : ℕ) :
    Continuous (fun τ : ℝ => dirSum f α N τ) := by
  change Continuous (fun τ : ℝ => ∑ n ∈ Finset.Icc 1 N,
    dterm f (((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I) n)
  refine continuous_finsetSum _ (fun n hn => ?_)
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hne : (n : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero]; omega
  have hcont : Continuous (fun τ : ℝ => -(((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)) := by
    continuity
  exact (Continuous.const_cpow hcont (Or.inl hne)).const_mul (f n * (Real.log n : ℂ))

/-- The squared modulus of the point `(1+α) + τ i` on the vertical line. -/
private lemma vline_normSq (α τ : ℝ) :
    ‖(((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2 = (1 + α) ^ 2 + τ ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_add_mul_I]

/-- The dominated-convergence majorant `C / ‖(1+α) + τ i‖²` is integrable. -/
private lemma integrable_div_normSq (α : ℝ) (hα : 0 < α) (C : ℝ) :
    Integrable (fun τ : ℝ => C / ‖(((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2)
      volume := by
  have hbase : Integrable (fun τ : ℝ => |C| * (1 + τ ^ 2)⁻¹) volume :=
    integrable_inv_one_add_sq.const_mul |C|
  refine hbase.mono' ?_ (Eventually.of_forall (fun τ => ?_))
  · refine Continuous.aestronglyMeasurable (Continuous.div continuous_const ?_ (fun τ => ?_))
    · exact ((by continuity : Continuous
        (fun τ : ℝ => (((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I))).norm).pow 2
    · have hne : (((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I) ≠ 0 := by
        intro h
        have hc := congrArg Complex.re h
        simp at hc
        linarith [hα]
      exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hne)
  · have hX : (0 : ℝ) < (1 + α) ^ 2 + τ ^ 2 := by positivity
    have hge : (1 : ℝ) + τ ^ 2 ≤ (1 + α) ^ 2 + τ ^ 2 := by
      have h1 : (1 : ℝ) ≤ (1 + α) ^ 2 := by nlinarith [hα]
      linarith
    rw [vline_normSq, Real.norm_eq_abs, abs_div, abs_of_nonneg hX.le, div_eq_mul_inv,
      ← one_div, ← one_div]
    exact mul_le_mul_of_nonneg_left
      (one_div_le_one_div_of_le (show (0 : ℝ) < 1 + τ ^ 2 by positivity) hge) (abs_nonneg C)

/-- Measurability of the truncated integrand. -/
private lemma aestronglyMeasurable_integrand (f : ℕ → ℂ) (α : ℝ) (hα : 0 < α) (N : ℕ) :
    AEStronglyMeasurable (fun τ : ℝ => ‖dirSum f α N τ‖ ^ 2 /
      ‖(((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2) volume := by
  refine Continuous.aestronglyMeasurable ?_
  have hden : Continuous (fun τ : ℝ => ‖(((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2) :=
    (by continuity : Continuous
      (fun τ : ℝ => (((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I))).norm.pow 2
  exact ((continuous_dirSum f α N).norm.pow 2).div hden (fun τ => by
    have hne : (((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I) ≠ 0 := by
      intro h
      have hc := congrArg Complex.re h
      simp at hc
      linarith [hα]
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hne))

/-- Pointwise convergence of the truncated Dirichlet series to `Kser`. -/
private lemma tendsto_dirSum (f : ℕ → ℂ) (hb : ∀ n, ‖f n‖ ≤ 1) (α : ℝ)
    (hsum : Summable (fun n : ℕ => ‖Real.log n‖ / (n : ℝ) ^ (1 + α))) (τ : ℝ) :
    Filter.Tendsto (fun N : ℕ => dirSum f α N τ) Filter.atTop
      (nhds (Kser f (((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I))) := by
  have hbnd : ∀ n, ‖dterm f (((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I) n‖
      ≤ ‖Real.log n‖ / (n : ℝ) ^ (1 + α) := by
    intro n
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      simp [dterm]
    · exact norm_dterm_le f hb α τ h
  have hsb : Summable (dterm f (((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)) :=
    Summable.of_norm (Summable.of_nonneg_of_le (fun n => norm_nonneg _) hbnd hsum)
  have hrange : Filter.Tendsto
      (fun N : ℕ => ∑ i ∈ Finset.range N,
        dterm f (((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I) i) Filter.atTop
      (nhds (∑' n, dterm f (((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I) n)) :=
    hsb.hasSum.tendsto_sum_nat
  have hshift : Filter.Tendsto
      (fun N : ℕ => ∑ i ∈ Finset.range (N + 1),
        dterm f (((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I) i) Filter.atTop
      (nhds (∑' n, dterm f (((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I) n)) :=
    hrange.comp (tendsto_add_atTop_nat 1)
  have heq : ∀ N : ℕ,
      ∑ i ∈ Finset.range (N + 1), dterm f (((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I) i
        = ∑ i ∈ Finset.Icc 1 N, dterm f (((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I) i := by
    intro N
    have hset : Finset.Icc 1 N = (Finset.range (N + 1)).erase 0 := by
      ext n
      simp only [Finset.mem_Icc, Finset.mem_erase, Finset.mem_range]
      omega
    rw [hset, Finset.sum_erase_eq_sub (Finset.mem_range.mpr (Nat.succ_pos N))]
    simp [dterm]
  have hIcc : Filter.Tendsto
      (fun N : ℕ => ∑ i ∈ Finset.Icc 1 N,
        dterm f (((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I) i) Filter.atTop
      (nhds (∑' n, dterm f (((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I) n)) :=
    hshift.congr' (Eventually.of_forall (fun N => heq N))
  change Filter.Tendsto
    (fun N : ℕ => ∑ i ∈ Finset.Icc 1 N,
      dterm f (((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I) i) Filter.atTop
    (nhds (∑' n, dterm f (((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I) n))
  exact hIcc

/-- The main convergence statement, written with `dterm`-free notation. -/
private theorem main_aux (f : ℕ → ℂ) (hb : ∀ n, ‖f n‖ ≤ 1) (α : ℝ) (hα : 0 < α) :
    Filter.Tendsto
      (fun N : ℕ => ∫ τ : ℝ, ‖dirSum f α N τ‖ ^ 2 /
        ‖(((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2)
      Filter.atTop
      (nhds (∫ τ : ℝ, ‖Kser f (((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2 /
        ‖(((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2)) := by
  have hsum := summable_norm_log_div_rpow α hα
  let A : ℝ := ∑' n : ℕ, ‖Real.log n‖ / (n : ℝ) ^ (1 + α)
  refine tendsto_integral_of_dominated_convergence
    (bound := fun τ : ℝ => A ^ 2 / ‖(((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2)
    (fun N => aestronglyMeasurable_integrand f α hα N) (integrable_div_normSq α hα (A ^ 2))
    ?_ ?_
  · intro N
    filter_upwards with τ
    have hle : ‖dirSum f α N τ‖ ≤ A := dirSum_norm_le f hb α hsum N τ
    have hsq : ‖dirSum f α N τ‖ ^ 2 ≤ A ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hle 2
    rw [Real.norm_of_nonneg (by positivity)]
    exact div_le_div_of_nonneg_right hsq (sq_nonneg _)
  · filter_upwards with τ
    have ht : Filter.Tendsto (fun N : ℕ => dirSum f α N τ) Filter.atTop
        (nhds (Kser f (((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I))) :=
      tendsto_dirSum f hb α hsum τ
    have h2 := (ht.norm.pow 2).mul_const
      ((‖(((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2)⁻¹)
    simpa only [div_eq_mul_inv] using h2

theorem tendsto_integral_dirSum (f : ℕ → ℂ) (hb : ∀ n, ‖f n‖ ≤ 1) (α : ℝ)
    (hα : 0 < α) :
    Filter.Tendsto
      (fun N : ℕ => ∫ τ : ℝ,
        ‖dirSum f α N τ‖ ^ 2 / ‖((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I‖ ^ 2)
      Filter.atTop
      (nhds (∫ τ : ℝ, ‖Kser f (((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2 /
        ‖((((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I))‖ ^ 2)) :=
  main_aux f hb α hα

end Work.BMF
