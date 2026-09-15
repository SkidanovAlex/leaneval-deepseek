import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.exists_odd_character_mod_four
import Submission.Commons.NumberTheory.LSeries.exists_bound_partial_sums_chi4_near_one_le
import Submission.Commons.NumberTheory.LSeries.LFunction_eq_tendsto_partial_sums

namespace Commons.NumberTheory.LSeries

open scoped BigOperators

noncomputable section

/-! ### Auxiliary facts about `χ₄` -/

/-- `χ₄` is not the trivial Dirichlet character modulo `4`. -/
private lemma chi4_ne_one :
    Commons.NumberTheory.DirichletCharacter.chi4 ≠ (1 : DirichletCharacter ℂ 4) := by
  intro h
  have h3 : Commons.NumberTheory.DirichletCharacter.chi4 (3 : ZMod 4) =
      (1 : DirichletCharacter ℂ 4) 3 := by rw [h]
  rw [Commons.NumberTheory.DirichletCharacter.chi4_apply,
      Commons.NumberTheory.DirichletCharacter.chi4Fun_three,
      MulChar.one_apply (isUnit_iff_exists_inv.mpr ⟨3, by decide⟩)] at h3
  norm_num at h3

/-- The value of `χ₄` at a natural number, in the explicit `n % 4` form used by the
partial-summation bounds. -/
private lemma chi4_natCast_eq (n : ℕ) :
    Commons.NumberTheory.DirichletCharacter.chi4 (n : ZMod 4) =
    (if n % 4 = 1 then (1 : ℂ) else if n % 4 = 3 then -1 else 0) := by
  rw [Commons.NumberTheory.DirichletCharacter.chi4_apply,
      Commons.NumberTheory.DirichletCharacter.chi4Fun]
  simp only [ZMod.val_natCast]
  have h4 := Nat.mod_lt n (by norm_num : 0 < 4)
  interval_cases n % 4 <;> simp

/-! ### The strip bound for `L(·, χ₄)` -/

/-- **Logarithmic bound for `L(·,χ₄)` near the line `re s = 1`**: there are `C, c > 0` with
`‖L(σ+it, χ₄)‖ ≤ C log(|t|+2)` whenever `1 ≤ |t|` and `σ ≥ 1 - c/log(|t|+2)`.

This is obtained from the partial-summation bound
`Commons.NumberTheory.LSeries.exists_bound_partial_sums_chi4_near_one_le` by passing to the
limit `N → ∞` in the Dirichlet series via
`Commons.NumberTheory.LSeries.LFunction_eq_tendsto_partial_sums`
(applicable since `re s > 0`, which follows after shrinking the constant `c`). -/
private lemma exists_bound_LFunction_chi4_near_one_aux :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ σ t : ℝ, 1 ≤ |t| →
      1 - c / Real.log (|t| + 2) ≤ σ →
      ‖DirichletCharacter.LFunction Commons.NumberTheory.DirichletCharacter.chi4
        ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C * Real.log (|t| + 2) := by
  obtain ⟨C, c, hC, hc, hbound⟩ :=
    Commons.NumberTheory.LSeries.exists_bound_partial_sums_chi4_near_one_le
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  set c' : ℝ := min c (Real.log 3 / 2) with hc'def
  have hc'pos : 0 < c' := lt_min hc (by linarith)
  have hc'le : c' ≤ c := min_le_left _ _
  have hc'le2 : c' ≤ Real.log 3 / 2 := min_le_right _ _
  refine ⟨C, c', hC, hc'pos, ?_⟩
  intro σ t ht hσ
  set L : ℝ := Real.log (|t| + 2) with hLdef
  have hLpos : 0 < L := by rw [hLdef]; exact Real.log_pos (by linarith [abs_nonneg t])
  have hL3 : Real.log 3 ≤ L := by
    rw [hLdef]; exact Real.log_le_log (by norm_num) (by linarith [abs_nonneg t, ht])
  have hσL : 1 - c' / L ≤ σ := by rw [hLdef]; exact hσ
  have hσpos : 0 < σ := by
    have h1 : c' / L ≤ 1 / 2 := by
      rw [div_le_iff₀ hLpos]
      nlinarith [hc'le2, hL3, hLpos]
    linarith
  have hσc : 1 - c / Real.log (|t| + 2) ≤ σ := by
    rw [← hLdef]
    have : c' / L ≤ c / L := div_le_div_of_nonneg_right hc'le hLpos.le
    linarith
  set s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hsdef
  have hsre : s.re = σ := by simp [hsdef]
  have htend := Commons.NumberTheory.LSeries.LFunction_eq_tendsto_partial_sums
    Commons.NumberTheory.DirichletCharacter.chi4 chi4_ne_one (s := s)
    (by rw [hsre]; exact hσpos)
  have hnorm_tend : Filter.Tendsto
      (fun M : ℕ => ‖∑ n ∈ Finset.range M,
        Commons.NumberTheory.DirichletCharacter.chi4 (n : ZMod 4) / (n : ℂ) ^ s‖)
      Filter.atTop
      (nhds ‖DirichletCharacter.LFunction Commons.NumberTheory.DirichletCharacter.chi4 s‖) :=
    htend.norm
  rw [hsdef] at hnorm_tend
  refine le_of_tendsto' hnorm_tend ?_
  intro N
  have hb := hbound σ t ht hσc N
  have hsum : (∑ n ∈ Finset.range N,
        Commons.NumberTheory.DirichletCharacter.chi4 (n : ZMod 4)
          / (n : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I))
      = ∑ n ∈ Finset.range N,
          (if n % 4 = 1 then (1 : ℂ) else if n % 4 = 3 then -1 else 0)
            / (n : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I) := by
    apply Finset.sum_congr rfl
    intro n _
    rw [chi4_natCast_eq n]
  rw [hsum]
  simpa [hLdef] using hb

/-- **Cauchy-type bound for the derivative of `L(·,χ₄)` near the line `re s = 1`.**

There are `C, d > 0` such that for all real `σ, t` with `2 ≤ |t|`,
`1 - d/log(|t|+2) ≤ σ ≤ 1 + 1/(2 log(|t|+2))`,

`‖L'(σ + it, χ₄)‖ ≤ C (log(|t|+2))²`,  where `χ₄` is
`Commons.NumberTheory.DirichletCharacter.chi4`.

PROOF.  Start from the strip bound for `χ₄` (in the commons as
`Commons.NumberTheory.LSeries.exists_bound_LFunction_chi4_near_one` if it is already there;
otherwise reprove it from the partial-sum bound
`Commons.NumberTheory.LSeries.exists_bound_partial_sums_chi4_near_one_le` together with
`Commons.NumberTheory.LSeries.LFunction_eq_tendsto_partial_sums`):
there are `C₀, c₀ > 0` with `‖L(s,χ₄)‖ ≤ C₀ log(|t|+2)` for `1 ≤ |t|` and
`re s ≥ 1 - c₀/log(|t|+2)`.  Put `L := log(|t|+2)`, `r := 1/(8L)`, `c := c₀/2`, and apply
`Complex.norm_deriv_le_of_forall_mem_sphere_norm_le` at the centre `σ + it` with radius `r`
(the function `L(·,χ₄)` is entire: `DirichletCharacter.differentiable_LFunction`, using
`chi4 ≠ 1`).  Every `z` on the circle `‖z - (σ+it)‖ = r` satisfies

* `1 - c/log(|z.im|+2) ≤ z.re`:  indeed `|z.im| ≤ |t| + r ≤ |t| + 1`, so
  `log(|z.im|+2) ≤ L`, and `z.re ≥ σ - r ≥ 1 - (c₀/2)/L - 1/(8L) ≥ 1 - c₀/L`;
  hence also `1 ≤ |z.im|` (from `2 ≤ |t|` and `r ≤ 1`);
* therefore `‖L(z,χ₄)‖ ≤ C₀ L`.

Cauchy's estimate gives `‖L'(σ+it,χ₄)‖ ≤ C₀ L / r = 800 C₀ L²`. -/
theorem exists_bound_deriv_LFunction_chi4_log_sq :
    ∃ C d : ℝ, 0 < C ∧ 0 < d ∧ ∀ σ t : ℝ, 2 ≤ |t| →
      1 - d / Real.log (|t| + 2) ≤ σ →
      σ ≤ 1 + 1 / (2 * Real.log (|t| + 2)) →
      ‖deriv (DirichletCharacter.LFunction Commons.NumberTheory.DirichletCharacter.chi4)
        ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C * (Real.log (|t| + 2)) ^ 2 := by
  obtain ⟨C₀, c₀, hC₀, hc₀, hbound⟩ := exists_bound_LFunction_chi4_near_one_aux
  set c'' : ℝ := min (c₀ / 2) (1 / 2) with hc''def
  have hc''pos : 0 < c'' := lt_min (by linarith) (by norm_num)
  have hc''le : c'' ≤ c₀ / 2 := min_le_left _ _
  have hc''le2 : c'' ≤ 1 / 2 := min_le_right _ _
  refine ⟨4 * C₀ / c'', c'' / 2, by positivity, by positivity, ?_⟩
  intro σ t ht hσ _
  set L : ℝ := Real.log (|t| + 2) with hLdef
  have hLpos : 0 < L := by rw [hLdef]; exact Real.log_pos (by linarith [abs_nonneg t])
  have hL1 : 1 ≤ L := by
    rw [hLdef]
    have h4 : (4 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t, ht]
    have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 4) h4
    have hlog4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
      ring
    have h2 : (0.69 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
    linarith [hlog, hlog4]
  have hlog2 : Real.log 2 ≤ L := by
    rw [hLdef]; exact Real.log_le_log (by norm_num) (by linarith [abs_nonneg t, ht])
  have hσL : (1 : ℝ) - (c'' / 2) / L ≤ σ := by rw [hLdef]; exact hσ
  set r : ℝ := c'' / (2 * L) with hrdef
  have hrpos : 0 < r := by rw [hrdef]; positivity
  have hrle : r ≤ 1 / 2 := by
    rw [hrdef, div_le_iff₀ (by positivity)]
    nlinarith [hc''le2, hL1]
  set s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hsdef
  have hdiff : DiffContOnCl ℂ
      (DirichletCharacter.LFunction Commons.NumberTheory.DirichletCharacter.chi4)
      (Metric.ball s r) :=
    (DirichletCharacter.differentiable_LFunction (N := 4) chi4_ne_one).diffContOnCl
  have hsphere : ∀ z ∈ Metric.sphere s r,
      ‖DirichletCharacter.LFunction Commons.NumberTheory.DirichletCharacter.chi4 z‖
        ≤ 2 * C₀ * L := by
    intro z hz
    rw [Metric.mem_sphere, dist_eq_norm] at hz
    have him : |z.im - t| ≤ r := by
      have h := Complex.abs_im_le_norm (z - s)
      have : (z - s).im = z.im - t := by simp [hsdef]
      rwa [this, hz] at h
    have hre : |z.re - σ| ≤ r := by
      have h := Complex.abs_re_le_norm (z - s)
      have : (z - s).re = z.re - σ := by simp [hsdef]
      rwa [this, hz] at h
    have hzim_le : |z.im| ≤ |t| + r := by
      calc |z.im| = |t + (z.im - t)| := by ring_nf
        _ ≤ |t| + |z.im - t| := abs_add_le t (z.im - t)
        _ ≤ |t| + r := by linarith
    have hzim_ge : 1 ≤ |z.im| := by
      have h1 : |t| ≤ |z.im| + r := by
        calc |t| = |z.im - (z.im - t)| := by ring_nf
          _ ≤ |z.im| + |z.im - t| := abs_sub z.im (z.im - t)
          _ ≤ |z.im| + r := by linarith
      linarith [h1, ht, hrle]
    have hlog_le : Real.log (|z.im| + 2) ≤ 2 * L := by
      have h1 : |z.im| + 2 ≤ 2 * (|t| + 2) := by
        nlinarith [hzim_le, abs_nonneg t, ht, hrle]
      calc Real.log (|z.im| + 2) ≤ Real.log (2 * (|t| + 2)) :=
            Real.log_le_log (by positivity) h1
        _ = Real.log 2 + L := by
            rw [Real.log_mul (by norm_num) (by linarith [abs_nonneg t]), hLdef]
        _ ≤ 2 * L := by linarith
    have hlogZpos : 0 < Real.log (|z.im| + 2) := Real.log_pos (by linarith [abs_nonneg z.im])
    have hre' : 1 - c₀ / Real.log (|z.im| + 2) ≤ z.re := by
      have h2 : (1 : ℝ) - c'' / L ≤ z.re := by
        have hσr : σ - r ≤ z.re := by linarith [(abs_le.mp hre).1]
        have hr' : r = c'' / (2 * L) := hrdef
        have hkey : (c'' / 2) / L + c'' / (2 * L) = c'' / L := by field_simp; ring
        linarith
      have hcmp : c'' / L ≤ c₀ / Real.log (|z.im| + 2) := by
        rw [div_le_div_iff₀ hLpos hlogZpos]
        have h3 : 2 * c'' ≤ c₀ := by linarith
        nlinarith [hlog_le, hLpos, h3, hc''pos]
      linarith
    have hb := hbound z.re z.im hzim_ge hre'
    rw [Complex.re_add_im] at hb
    calc ‖DirichletCharacter.LFunction Commons.NumberTheory.DirichletCharacter.chi4 z‖
        ≤ C₀ * Real.log (|z.im| + 2) := hb
      _ ≤ C₀ * (2 * L) := by
          exact mul_le_mul_of_nonneg_left hlog_le (le_of_lt hC₀)
      _ = 2 * C₀ * L := by ring
  have hcauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hrpos hdiff hsphere
  have hgoal : ‖deriv (DirichletCharacter.LFunction
      Commons.NumberTheory.DirichletCharacter.chi4) s‖ ≤ 4 * C₀ / c'' * L ^ 2 := by
    calc ‖deriv (DirichletCharacter.LFunction
            Commons.NumberTheory.DirichletCharacter.chi4) s‖
        ≤ (2 * C₀ * L) / r := hcauchy
      _ = 4 * C₀ / c'' * L ^ 2 := by
          rw [hrdef]
          field_simp
          ring
  rw [hsdef, hLdef] at hgoal
  exact hgoal

end

end Commons.NumberTheory.LSeries
