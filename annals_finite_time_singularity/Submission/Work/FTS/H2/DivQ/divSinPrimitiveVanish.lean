import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Submission.Work.FTS.H2.DivQ.vanishAux
import Submission.Work.FTS.H2.DivQ.hardyIter_tendsto_zero

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Boundary vanishing of the weighted iterated derivatives (`DivQ`)

This file proves `Work.FTS.H2.DivQ.divSinPrimitiveVanish`: if `f` is `C^∞` on `(0,x₁]` and
`∫_0^{x₁} x^{2k-γ}(f^{(k+1)})² < ∞` with `γ > -1`, then `x^j f^{(j)}(x) → 0` at `0⁺` for every
`1 ≤ j ≤ k`.

The proof is a downward induction on `j`.  The base case `j = k` is the analytic heart: writing
`F = f^{(k)}`, `G = f^{(k+1)}` and using the fundamental theorem of calculus
`F(x) = F(δ) - ∫_x^δ G` together with the weighted AM–GM pointwise inequality
`|G(s)| ≤ (x^k/2) s^{γ-2k} + (1/(2x^k)) s^{2k-γ} G(s)²` (valid for every `x > 0`), one gets

  `x^k|F(x)| ≤ x^k|F(δ)| + (x^{2k}/2)∫_x^δ s^{γ-2k} ds + (1/2)∫_x^δ s^{2k-γ}G²`,

where the middle term tends to `0` (`van_powMul_rpow_integral`) and the last one is bounded by the
(small) tail `∫_{(0,δ)} s^{2k-γ}G²` of an integrable function (`hardyIter_tendsto_zero`).
The induction step `j+1 → j` only uses the *limit* form of the hypothesis at level `j+1`.
-/

namespace Work.FTS.H2.DivQ

open MeasureTheory Filter Set
open scoped Topology

/-- **Scalar weighted integral limit.**  For `x₁ > 0`, `n ≥ 1` and `n + q + 1 > 0`, the weighted
integral `x ^ n * ∫_x^{x₁} s ^ q ds` tends to `0` as `x → 0⁺` (`s ^ q` is `Real.rpow`).

For `0 < x < x₁` the primitive gives `x^n * ∫_x^{x₁} s^q = x^n (x₁^{q+1} - x^{q+1})/(q+1)` when
`q ≠ -1`, and `x^n (log x₁ - log x)` when `q = -1`; in the first case the two terms tend to `0`
because `n > 0` and `n + q + 1 > 0`, in the second because `x^n log x → 0` at `0⁺` for `n ≥ 1`. -/
theorem van_powMul_rpow_integral (n : ℕ) (q : ℝ) (hn : 1 ≤ n)
    (hq : 0 < (n : ℝ) + q + 1) {x₁ : ℝ} (hx₁ : 0 < x₁) :
    Filter.Tendsto (fun x : ℝ => x ^ n * ∫ s in x..x₁, s ^ q)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hid : Filter.Tendsto (fun x : ℝ => x) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have hxn : Filter.Tendsto (fun x : ℝ => x ^ n) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have h := hid.pow n
    simpa [zero_pow (by omega : n ≠ 0)] using h
  have hzero : ∀ x : ℝ, x ∈ Set.Ioo (0 : ℝ) x₁ → (0 : ℝ) ∉ Set.uIcc x x₁ := by
    intro x hx
    rw [Set.uIcc_of_le hx.2.le]
    intro hmem
    exact absurd hmem.1 (not_le.mpr hx.1)
  rcases eq_or_ne q (-1) with hq1 | hq1
  · -- the logarithmic case `q = -1`
    subst hq1
    have hkey : Filter.Tendsto (fun x : ℝ => x ^ n * (Real.log x₁ - Real.log x))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have h2 : Filter.Tendsto (fun x : ℝ => Real.log x * x ^ ((n : ℝ)))
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
        tendsto_log_mul_rpow_nhdsGT_zero (by positivity : (0 : ℝ) < (n : ℝ))
      have h2' : Filter.Tendsto (fun x : ℝ => x ^ n * Real.log x)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
        refine Filter.Tendsto.congr' ?_ h2
        filter_upwards with x
        rw [Real.rpow_natCast, mul_comm]
      have h1 : Filter.Tendsto (fun x : ℝ => x ^ n * Real.log x₁)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
        simpa using hxn.mul_const (Real.log x₁)
      simpa only [mul_sub, sub_zero] using h1.sub h2'
    refine Filter.Tendsto.congr' ?_ hkey
    filter_upwards [Ioo_mem_nhdsGT hx₁] with x hx
    have h0 := hzero x hx
    have hlogeq : (∫ s in x..x₁, s ^ (-1 : ℝ)) = Real.log x₁ - Real.log x := by
      rw [show (∫ s in x..x₁, s ^ (-1 : ℝ)) = ∫ s in x..x₁, s⁻¹ by
            simp only [Real.rpow_neg_one],
          integral_inv h0, Real.log_div (ne_of_gt hx₁) (ne_of_gt hx.1)]
    rw [hlogeq]
  · -- the power case `q ≠ -1`
    have hkey : Filter.Tendsto
        (fun x : ℝ => (x₁ ^ (q + 1) * x ^ n - x ^ ((n : ℝ) + q + 1)) / (q + 1))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have h1 : Filter.Tendsto (fun x : ℝ => x₁ ^ (q + 1) * x ^ n)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
        simpa using hxn.const_mul (x₁ ^ (q + 1))
      have h2 : Filter.Tendsto (fun x : ℝ => x ^ ((n : ℝ) + q + 1))
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
        Filter.Tendsto.rpow_const_nhds_zero (f := fun x : ℝ => x) hid hq
      simpa using (h1.sub h2).div_const (q + 1)
    refine Filter.Tendsto.congr' ?_ hkey
    filter_upwards [Ioo_mem_nhdsGT hx₁] with x hx
    have h0 := hzero x hx
    have hir : (∫ s in x..x₁, s ^ q) = (x₁ ^ (q + 1) - x ^ (q + 1)) / (q + 1) :=
      integral_rpow (Or.inr ⟨hq1, h0⟩)
    have hxpow : x ^ n * x ^ (q + 1) = x ^ ((n : ℝ) + q + 1) := by
      have hcast : (x : ℝ) ^ n = x ^ ((n : ℝ)) := (Real.rpow_natCast x n).symm
      rw [hcast, ← Real.rpow_add hx.1 (n : ℝ) (q + 1),
        show (n : ℝ) + (q + 1) = (n : ℝ) + q + 1 from by ring]
    rw [hir, mul_div_assoc', mul_sub, hxpow]
    ring

/-- **Weighted AM–GM on an interval.**  For `a > 0`, `0 < x ≤ σ` and `h` continuous on `[x,σ]`,
`∫_x^σ |h| ≤ (a/2)·∫_x^σ s^e + (1/(2a))·∫_x^σ s^{-e}·h(s)²` (all powers are `Real.rpow`).

Pointwise `|h s| = s^{e/2}·(s^{-e/2}|h s|)` for `s > 0`, and the elementary AM–GM
`2uv ≤ a u² + v²/a` with `u = s^{e/2}`, `v = s^{-e/2}|h s|` gives
`|h s| ≤ (a/2) s^e + (1/(2a)) s^{-e} h(s)²`; integrate over `[x,σ]`. -/
theorem van_amgm_integral (h : ℝ → ℝ) {e a x σ : ℝ} (ha : 0 < a) (hx : 0 < x)
    (hxσ : x ≤ σ) (hcont : ContinuousOn h (Set.Icc x σ)) :
    ∫ s in x..σ, |h s| ≤ (a / 2) * (∫ s in x..σ, s ^ e)
      + (1 / (2 * a)) * (∫ s in x..σ, s ^ (-e) * (h s) ^ 2) := by
  have hs0 : ∀ s ∈ Set.Icc x σ, 0 < s := fun s hs => lt_of_lt_of_le hx hs.1
  have hpt : ∀ s ∈ Set.Icc x σ,
      |h s| ≤ (a / 2) * s ^ e + (1 / (2 * a)) * (s ^ (-e) * (h s) ^ 2) := by
    intro s hs
    have hspos := hs0 s hs
    have h1 : s ^ (e / 2) * (s ^ (-e / 2) * |h s|) = |h s| := by
      rw [← mul_assoc, ← Real.rpow_add hspos,
        show e / 2 + (-e / 2) = 0 from by ring, Real.rpow_zero, one_mul]
    have h2 : (s ^ (e / 2)) ^ 2 = s ^ e := by
      rw [pow_two, ← Real.rpow_add hspos, show e / 2 + e / 2 = e from by ring]
    have h3 : (s ^ (-e / 2) * |h s|) ^ 2 = s ^ (-e) * (h s) ^ 2 := by
      rw [mul_pow, sq_abs, pow_two (s ^ (-e / 2)), ← Real.rpow_add hspos,
        show -e / 2 + -e / 2 = -e from by ring]
    have hab := two_mul_le_mul_sq_add_div_sq (a := a) (u := s ^ (e / 2))
      (v := s ^ (-e / 2) * |h s|) ha
    rw [h1, h2, h3] at hab
    calc |h s| = (1 / 2) * (2 * |h s|) := by ring
      _ ≤ (1 / 2) * (a * s ^ e + (s ^ (-e) * (h s) ^ 2) / a) :=
          mul_le_mul_of_nonneg_left hab (by norm_num)
      _ = (a / 2) * s ^ e + (1 / (2 * a)) * (s ^ (-e) * (h s) ^ 2) := by ring
  have hcont1 : ContinuousOn (fun s : ℝ => |h s|) (Set.Icc x σ) := hcont.abs
  have hcontE : ContinuousOn (fun s : ℝ => s ^ e) (Set.Icc x σ) :=
    continuousOn_id.rpow_const fun s hs => Or.inl (ne_of_gt (hs0 s hs))
  have hcontE' : ContinuousOn (fun s : ℝ => s ^ (-e)) (Set.Icc x σ) :=
    continuousOn_id.rpow_const fun s hs => Or.inl (ne_of_gt (hs0 s hs))
  have hcont2 : ContinuousOn
      (fun s : ℝ => (a / 2) * s ^ e + (1 / (2 * a)) * (s ^ (-e) * (h s) ^ 2))
      (Set.Icc x σ) :=
    (continuousOn_const.mul hcontE).add
      (continuousOn_const.mul (hcontE'.mul (hcont.pow 2)))
  have hmono := intervalIntegral.integral_mono_on hxσ
    (hcont1.intervalIntegrable_of_Icc (μ := volume) hxσ)
    (hcont2.intervalIntegrable_of_Icc (μ := volume) hxσ) hpt
  have hi1 : IntervalIntegrable (fun s : ℝ => (a / 2) * s ^ e) volume x σ :=
    (continuousOn_const.mul hcontE).intervalIntegrable_of_Icc (μ := volume) hxσ
  have hi2 : IntervalIntegrable
      (fun s : ℝ => (1 / (2 * a)) * (s ^ (-e) * (h s) ^ 2)) volume x σ :=
    (continuousOn_const.mul (hcontE'.mul (hcont.pow 2))).intervalIntegrable_of_Icc (μ := volume) hxσ
  rw [intervalIntegral.integral_add hi1 hi2] at hmono
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hmono
  simpa using hmono

/-- Monotonicity of the set integral in the domain, for a nonnegative integrand. -/
lemma van_setIntegral_mono_Ioc {f : ℝ → ℝ} {x δ : ℝ} (hx : 0 < x)
    (hint : IntegrableOn f (Set.Ioc 0 δ)) (hnn : ∀ y ∈ Set.Ioc 0 δ, 0 ≤ f y) :
    ∫ y in Set.Ioc x δ, f y ≤ ∫ y in Set.Ioc 0 δ, f y := by
  refine integral_mono_measure (Measure.restrict_mono ?_ le_rfl) ?_ hint
  · exact Set.Ioc_subset_Ioc (le_of_lt hx) le_rfl
  · filter_upwards [ae_restrict_mem (μ := volume) (s := Set.Ioc 0 δ) measurableSet_Ioc] with y hy
    exact hnn y hy

/-- The base case `j = k` of the downward induction: from the integrability of
`x ↦ x^{2k-γ}(f^{(k+1)}x)²` on `(0,x₁]` (and `k ≥ 1`) deduce `x^k f^{(k)}(x) → 0` at `0⁺`. -/
private lemma van_baseCase (k : ℕ) (hk : 1 ≤ k) {γ x₁ : ℝ} (hx₁ : 0 < x₁) (hγ : -1 < γ)
    {f : ℝ → ℝ} (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (Set.Ioc 0 x₁))
    (hB : IntegrableOn (fun x : ℝ => x ^ (2 * (k : ℝ) - γ) * (iteratedDeriv (k + 1) f x) ^ 2)
      (Set.Ioc 0 x₁)) :
    Filter.Tendsto (fun x : ℝ => x ^ k * iteratedDeriv k f x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  -- the tail of the weighted integral is small for small `δ`
  have hΨ : Filter.Tendsto
      (fun δ : ℝ => ∫ y in Set.Ioc 0 δ, y ^ (2 * (k : ℝ) - γ) * (iteratedDeriv (k + 1) f y) ^ 2)
      (nhds 0) (nhds 0) := hardyIter_tendsto_zero hx₁ hB
  have hEv₁ : ∀ᶠ δ : ℝ in nhdsWithin 0 (Set.Ioi 0),
      (∫ y in Set.Ioc 0 δ, y ^ (2 * (k : ℝ) - γ) * (iteratedDeriv (k + 1) f y) ^ 2) < ε / 4 :=
    Filter.Tendsto.eventually_lt (hΨ.mono_left nhdsWithin_le_nhds) tendsto_const_nhds
      (by linarith)
  have hEv₂ : ∀ᶠ δ : ℝ in nhdsWithin 0 (Set.Ioi 0), 0 < δ := self_mem_nhdsWithin
  have hEv₃ : ∀ᶠ δ : ℝ in nhdsWithin 0 (Set.Ioi 0), δ < x₁ :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (Iio_mem_nhds hx₁)
  obtain ⟨δ, hδpos, hδx, hδsmall⟩ := (hEv₂.and (hEv₃.and hEv₁)).exists
  -- the two decay inputs at the level of `x`
  have hq : 0 < ((2 * k : ℕ) : ℝ) + (γ - 2 * (k : ℝ)) + 1 := by
    have hcast : ((2 * k : ℕ) : ℝ) = 2 * (k : ℝ) := by push_cast; ring
    rw [hcast]; linarith
  have hA : Filter.Tendsto
      (fun x : ℝ => (x ^ (2 * k) / 2) * (∫ s in x..δ, s ^ (γ - 2 * (k : ℝ))))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have h0 := van_powMul_rpow_integral (2 * k) (γ - 2 * (k : ℝ)) (by omega) hq hδpos
    have h := h0.const_mul (1 / 2 : ℝ)
    refine Filter.Tendsto.congr' ?_ (by simpa using h)
    filter_upwards with x
    ring
  have hA' : ∀ᶠ x : ℝ in nhdsWithin 0 (Set.Ioi 0),
      (x ^ (2 * k) / 2) * (∫ s in x..δ, s ^ (γ - 2 * (k : ℝ))) < ε / 2 :=
    Filter.Tendsto.eventually_lt hA tendsto_const_nhds (by linarith)
  have hC : Filter.Tendsto (fun x : ℝ => x ^ k * |iteratedDeriv k f δ|)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have hid : Filter.Tendsto (fun x : ℝ => x) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
    have h := (hid.pow k).mul_const |iteratedDeriv k f δ|
    simpa [zero_pow (by omega : k ≠ 0)] using h
  have hC' : ∀ᶠ x : ℝ in nhdsWithin 0 (Set.Ioi 0),
      x ^ k * |iteratedDeriv k f δ| < ε / 4 :=
    Filter.Tendsto.eventually_lt hC tendsto_const_nhds (by linarith)
  filter_upwards [Ioo_mem_nhdsGT hδpos, hA', hC'] with x hx hxA hxC
  have hxk : 0 < x ^ k := pow_pos hx.1 k
  have hxδ : x ≤ δ := hx.2.le
  -- fundamental theorem of calculus
  have hFTC : iteratedDeriv k f x
      = iteratedDeriv k f δ - ∫ s in x..δ, iteratedDeriv (k + 1) f s := by
    have h := intervalIntegral_iteratedDeriv_succ hf k hx.1 hxδ hδx
    linarith
  have hI : |∫ s in x..δ, iteratedDeriv (k + 1) f s|
      ≤ ∫ s in x..δ, |iteratedDeriv (k + 1) f s| :=
    intervalIntegral.abs_integral_le_integral_abs hxδ
  have hFx : |iteratedDeriv k f x|
      ≤ |iteratedDeriv k f δ| + ∫ s in x..δ, |iteratedDeriv (k + 1) f s| := by
    have h := abs_add_le (iteratedDeriv k f δ) (-(∫ s in x..δ, iteratedDeriv (k + 1) f s))
    rw [hFTC]
    calc |iteratedDeriv k f δ - ∫ s in x..δ, iteratedDeriv (k + 1) f s|
        ≤ |iteratedDeriv k f δ| + |∫ s in x..δ, iteratedDeriv (k + 1) f s| := by
          simpa [sub_eq_add_neg, abs_neg] using h
      _ ≤ |iteratedDeriv k f δ| + ∫ s in x..δ, |iteratedDeriv (k + 1) f s| := by linarith [hI]
  -- the weighted AM–GM bound
  have hcontG : ContinuousOn (iteratedDeriv (k + 1) f) (Set.Icc x δ) :=
    continuousOn_iteratedDeriv_Icc hf (k + 1) hx.1 hδx
  have hamgm := van_amgm_integral (iteratedDeriv (k + 1) f) (e := γ - 2 * (k : ℝ)) (a := x ^ k)
    hxk hx.1 hxδ hcontG
  simp only [show -(γ - 2 * (k : ℝ)) = 2 * (k : ℝ) - γ from by ring] at hamgm
  -- the bound on the last term of the displayed estimate
  have hTle : (1 / 2) * (∫ s in x..δ,
        s ^ (2 * (k : ℝ) - γ) * (iteratedDeriv (k + 1) f s) ^ 2)
      ≤ (1 / 2) * (∫ y in Set.Ioc 0 δ,
        y ^ (2 * (k : ℝ) - γ) * (iteratedDeriv (k + 1) f y) ^ 2) := by
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    rw [intervalIntegral.integral_of_le hxδ]
    exact van_setIntegral_mono_Ioc hx.1 (hB.mono_set (Set.Ioc_subset_Ioc le_rfl hδx.le))
      fun y hy => mul_nonneg (Real.rpow_nonneg (le_of_lt hy.1) _) (sq_nonneg _)
  -- assemble
  have hstep : x ^ k * |iteratedDeriv k f x|
      ≤ x ^ k * |iteratedDeriv k f δ|
        + (x ^ (2 * k) / 2) * (∫ s in x..δ, s ^ (γ - 2 * (k : ℝ)))
        + (1 / 2) * (∫ s in x..δ,
            s ^ (2 * (k : ℝ) - γ) * (iteratedDeriv (k + 1) f s) ^ 2) := by
    have h1 : x ^ k * |iteratedDeriv k f x|
        ≤ x ^ k * (|iteratedDeriv k f δ| + ∫ s in x..δ, |iteratedDeriv (k + 1) f s|) :=
      mul_le_mul_of_nonneg_left hFx (le_of_lt hxk)
    have h2 : x ^ k * (|iteratedDeriv k f δ| + ∫ s in x..δ, |iteratedDeriv (k + 1) f s|)
        ≤ x ^ k * (|iteratedDeriv k f δ|
          + ((x ^ k / 2) * (∫ s in x..δ, s ^ (γ - 2 * (k : ℝ)))
            + (1 / (2 * x ^ k)) * (∫ s in x..δ,
                s ^ (2 * (k : ℝ) - γ) * (iteratedDeriv (k + 1) f s) ^ 2))) := by
      refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hxk)
      linarith [hamgm]
    have h3 : x ^ k * (|iteratedDeriv k f δ|
          + ((x ^ k / 2) * (∫ s in x..δ, s ^ (γ - 2 * (k : ℝ)))
            + (1 / (2 * x ^ k)) * (∫ s in x..δ,
                s ^ (2 * (k : ℝ) - γ) * (iteratedDeriv (k + 1) f s) ^ 2)))
        = x ^ k * |iteratedDeriv k f δ|
          + (x ^ (2 * k) / 2) * (∫ s in x..δ, s ^ (γ - 2 * (k : ℝ)))
          + (1 / 2) * (∫ s in x..δ,
              s ^ (2 * (k : ℝ) - γ) * (iteratedDeriv (k + 1) f s) ^ 2) := by
      have hkk : x ^ (2 * k) = x ^ k * x ^ k := by
        rw [show 2 * k = k + k by omega, pow_add]
      rw [hkk]
      have hxne : x ^ k ≠ 0 := ne_of_gt hxk
      field_simp
      ring
    linarith [h1, h2, le_of_eq h3]
  have hTsmall : (1 / 2) * (∫ y in Set.Ioc 0 δ,
      y ^ (2 * (k : ℝ) - γ) * (iteratedDeriv (k + 1) f y) ^ 2) < ε / 8 := by
    linarith
  rw [Real.dist_eq, sub_zero, abs_mul, abs_of_nonneg (le_of_lt hxk)]
  linarith [hstep, hxA, hxC, hTle, hTsmall]

/-- The induction step `j+1 → j` of the downward induction. -/
private lemma van_step (j : ℕ) (hj : 1 ≤ j) {f : ℝ → ℝ} {x₁ : ℝ} (hx₁ : 0 < x₁)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (Set.Ioc 0 x₁))
    (h : Filter.Tendsto (fun t : ℝ => t ^ (j + 1) * iteratedDeriv (j + 1) f t)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) :
    Filter.Tendsto (fun x : ℝ => x ^ j * iteratedDeriv j f x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hjn : ((j : ℝ) ≠ 0) := by positivity
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  -- the limit hypothesis, in interval form
  have hεj : (0 : ℝ) < ε * (j : ℝ) / 2 := by positivity
  have hev := Metric.tendsto_nhds.mp h (ε * (j : ℝ) / 2) hεj
  obtain ⟨δ₀, hδ₀pos, hδ₀⟩ := (nhdsGT_basis (0 : ℝ)).eventually_iff.mp hev
  set δ : ℝ := min (δ₀ / 2) (x₁ / 2) with hδdef
  have hδpos : 0 < δ := lt_min (by linarith) (by linarith)
  have hδlt₀ : δ < δ₀ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hδx : δ < x₁ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  -- the tail bound against the model integral `∫_x^δ t^{-(j+1)}`
  have htail : ∀ x : ℝ, 0 < x → x ≤ δ →
      x ^ j * (∫ s in x..δ, |iteratedDeriv (j + 1) f s|) ≤ ε / 2 := by
    intro x hxpos hxδ
    have hxj : 0 < x ^ j := pow_pos hxpos j
    -- pointwise bound from the limit hypothesis
    have hbd : ∀ t ∈ Set.Icc x δ,
        |iteratedDeriv (j + 1) f t| ≤ (ε * (j : ℝ) / 2) * (t : ℝ) ^ (-((j : ℝ) + 1)) := by
      intro t ht
      have htpos : 0 < t := lt_of_lt_of_le hxpos ht.1
      have htδ₀ : t ∈ Set.Ioo (0 : ℝ) δ₀ := ⟨htpos, lt_of_le_of_lt ht.2 hδlt₀⟩
      have h1 := hδ₀ htδ₀
      rw [Real.dist_eq, sub_zero] at h1
      have h2 : |iteratedDeriv (j + 1) f t| * (t : ℝ) ^ (j + 1) < ε * (j : ℝ) / 2 := by
        rw [abs_mul, abs_of_nonneg (pow_nonneg (le_of_lt htpos) (j + 1)),
          mul_comm ((t : ℝ) ^ (j + 1))] at h1
        exact h1
      have h3 := mul_lt_mul_of_pos_right h2 (inv_pos.mpr (pow_pos htpos (j + 1)))
      rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt (pow_pos htpos (j + 1))), mul_one] at h3
      have hbase : (t : ℝ) ^ ((j : ℝ) + 1) = (t : ℝ) ^ (j + 1) := by
        have hcast : ((j : ℝ) + 1) = ((j + 1 : ℕ) : ℝ) := by push_cast; ring
        rw [hcast, Real.rpow_natCast]
      have hpow : (t : ℝ) ^ (-((j : ℝ) + 1)) = ((t : ℝ) ^ (j + 1))⁻¹ := by
        rw [Real.rpow_neg (le_of_lt htpos) ((j : ℝ) + 1), hbase]
      rw [hpow]
      exact h3.le
    have hint1 : IntervalIntegrable (fun s : ℝ => |iteratedDeriv (j + 1) f s|) volume x δ :=
      ((continuousOn_iteratedDeriv_Icc hf (j + 1) hxpos hδx).abs).intervalIntegrable_of_Icc
        (μ := volume) hxδ
    have hcontw : ContinuousOn (fun s : ℝ => (ε * (j : ℝ) / 2) * s ^ (-((j : ℝ) + 1)))
        (Set.Icc x δ) :=
      continuousOn_const.mul (continuousOn_id.rpow_const fun s hs =>
        Or.inl (ne_of_gt (lt_of_lt_of_le hxpos hs.1)))
    have hint2 : IntervalIntegrable (fun s : ℝ => (ε * (j : ℝ) / 2) * s ^ (-((j : ℝ) + 1)))
        volume x δ := hcontw.intervalIntegrable_of_Icc (μ := volume) hxδ
    have hmono := intervalIntegral.integral_mono_on hxδ hint1 hint2 hbd
    rw [intervalIntegral.integral_const_mul] at hmono
    -- evaluate the model integral
    have hnozero : (0 : ℝ) ∉ Set.uIcc x δ := by
      rw [Set.uIcc_of_le hxδ]
      intro hmem
      exact absurd hmem.1 (not_le.mpr hxpos)
    have hne : -((j : ℝ) + 1) ≠ -1 := by
      intro hc
      exact hjn (by linarith)
    have hval : (∫ s in x..δ, s ^ (-((j : ℝ) + 1)))
        = ((x : ℝ) ^ (-(j : ℝ)) - (δ : ℝ) ^ (-(j : ℝ))) / (j : ℝ) := by
      rw [integral_rpow (Or.inr ⟨hne, hnozero⟩)]
      have hr : (-((j : ℝ) + 1) + 1) = -(j : ℝ) := by ring
      rw [hr]
      ring
    rw [hval] at hmono
    -- multiply by `x ^ j`
    have hxd : x ^ j * ((x : ℝ) ^ (-(j : ℝ)) - (δ : ℝ) ^ (-(j : ℝ))) ≤ 1 := by
      rw [Real.rpow_neg (le_of_lt hxpos) (j : ℝ), Real.rpow_neg (le_of_lt hδpos) (j : ℝ),
        Real.rpow_natCast, Real.rpow_natCast]
      have hδj : 0 < δ ^ j := pow_pos hδpos j
      have hxinv : x ^ j * (x ^ j)⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hxj)
      have hnonneg : 0 ≤ x ^ j * (δ ^ j)⁻¹ := mul_nonneg hxj.le (inv_nonneg.mpr hδj.le)
      nlinarith [hxinv, hnonneg]
    have hstep1 : x ^ j * ((ε * (j : ℝ) / 2) * (((x : ℝ) ^ (-(j : ℝ)) - (δ : ℝ) ^ (-(j : ℝ)))
        / (j : ℝ))) ≤ ε / 2 := by
      have hrw : x ^ j * ((ε * (j : ℝ) / 2) * (((x : ℝ) ^ (-(j : ℝ)) - (δ : ℝ) ^ (-(j : ℝ)))
          / (j : ℝ))) = (ε / 2) * (x ^ j * ((x : ℝ) ^ (-(j : ℝ)) - (δ : ℝ) ^ (-(j : ℝ)))) := by
        field_simp
      rw [hrw]
      nlinarith [hxd, hε]
    exact (mul_le_mul_of_nonneg_left hmono hxj.le).trans hstep1
  -- eventually the `δ`-term is small
  have hfin : ∀ᶠ x : ℝ in nhdsWithin 0 (Set.Ioi 0),
      x ^ j * |iteratedDeriv j f δ| < ε / 2 := by
    have hid : Filter.Tendsto (fun x : ℝ => x) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
    have hh := (hid.pow j).mul_const |iteratedDeriv j f δ|
    have hh' : Filter.Tendsto (fun x : ℝ => x ^ j * |iteratedDeriv j f δ|)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      simpa [zero_pow (by omega : j ≠ 0)] using hh
    exact Filter.Tendsto.eventually_lt hh' tendsto_const_nhds (by linarith)
  filter_upwards [Ioo_mem_nhdsGT hδpos, hfin] with x hx hxfin
  have hxpos : 0 < x := hx.1
  have hxδ : x ≤ δ := hx.2.le
  have hxj : 0 < x ^ j := pow_pos hxpos j
  have hFTC : iteratedDeriv j f x
      = iteratedDeriv j f δ - ∫ s in x..δ, iteratedDeriv (j + 1) f s := by
    have hh := intervalIntegral_iteratedDeriv_succ hf j hxpos hxδ hδx
    linarith
  have hI : |∫ s in x..δ, iteratedDeriv (j + 1) f s|
      ≤ ∫ s in x..δ, |iteratedDeriv (j + 1) f s| :=
    intervalIntegral.abs_integral_le_integral_abs hxδ
  have hFx : |iteratedDeriv j f x|
      ≤ |iteratedDeriv j f δ| + ∫ s in x..δ, |iteratedDeriv (j + 1) f s| := by
    have hh := abs_add_le (iteratedDeriv j f δ) (-(∫ s in x..δ, iteratedDeriv (j + 1) f s))
    rw [hFTC]
    calc |iteratedDeriv j f δ - ∫ s in x..δ, iteratedDeriv (j + 1) f s|
        ≤ |iteratedDeriv j f δ| + |∫ s in x..δ, iteratedDeriv (j + 1) f s| := by
          simpa [sub_eq_add_neg, abs_neg] using hh
      _ ≤ |iteratedDeriv j f δ| + ∫ s in x..δ, |iteratedDeriv (j + 1) f s| := by linarith [hI]
  have htail' := htail x hxpos hxδ
  rw [Real.dist_eq, sub_zero, abs_mul, abs_of_nonneg hxj.le]
  linarith [mul_le_mul_of_nonneg_left hFx hxj.le, htail', hxfin]

/-- **Boundary vanishing of the weighted iterated derivatives.**  If `f` is `C^∞` on `(0,x₁]` and
`∫_0^{x₁} x^{2k-γ}(f^{(k+1)}(x))² dx < ∞` with `γ > -1`, then for every `1 ≤ j ≤ k`
`x^j·f^{(j)}(x) → 0` as `x → 0⁺`.

This is the analytic heart of the primitive formula for `∂_x^k(f/x)`.  Route (downward induction on `j`,
starting from `j = k`; the sharp rate is `x^{min(j,(1+γ)/2)}`):

* `f^{(k)}(x) = f^{(k)}(x₁) − ∫_x^{x₁} f^{(k+1)}` (FTC on `(0,x₁]`, and `k ≥ 1` in this case), and
  Cauchy–Schwarz with the two factors `s^{γ/2}` and `s^{k-γ/2}f^{(k+1)}(s)` over `(x,x₁)` gives
  `|∫_x^{x₁} f^{(k+1)}| ≤ B^{1/2}·(∫_x^{x₁} s^{γ-2k} ds)^{1/2}` with `B := ∫_0^{x₁} s^{2k-γ}(f^{(k+1)})²`;
  `x^{2k}∫_x^{x₁}s^{γ-2k}ds → 0` (three cases: `γ-2k ≥ -1`, `= -1` i.e. a log, or `< -1`) gives
  `x^k f^{(k)}(x) → 0`.
* Step: from `t^{j+1} f^{(j+1)}(t) → 0` (limit form, no uniform rate available) deduce `x^j f^{(j)}(x) → 0`:
  `f^{(j)}(x) = f^{(j)}(x₁) − ∫_x^{x₁} f^{(j+1)}`, split `∫_x^{x₁} = ∫_x^δ + ∫_δ^{x₁}` where δ is chosen so
  that `|f^{(j+1)}(t)| ≤ ε t^{-(j+1)}` on `(0,δ)`: then `x^j∫_x^δ t^{-(j+1)}dt ≤ ε/j` and
  `x^j∫_δ^{x₁}|f^{(j+1)}| ≤ x^j·(finite) → 0`.
  (Equivalently: carry the quantitative bound `|f^{(j)}(s)| ≤ C s^{d_j}` with `d_j = min(d_{j+1}+1, 0)`,
  which preserves `j + d_j > 0`.)

The hypothesis `f(x) → 0` at `0⁺` is *not* needed here (only `j ≥ 1` is asked about), and the case
`k = 0` makes the statement vacuous. -/
theorem divSinPrimitiveVanish (k : ℕ) (γ x₁ : ℝ) (hx₁ : 0 < x₁) (hγ : -1 < γ) :
    ∀ f : ℝ → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) f (Set.Ioc 0 x₁) →
      MeasureTheory.IntegrableOn
        (fun x : ℝ => x ^ (2 * (k : ℝ) - γ) * (iteratedDeriv (k + 1) f x) ^ 2)
        (Set.Ioc 0 x₁) →
      ∀ j : ℕ, 1 ≤ j → j ≤ k →
        Filter.Tendsto (fun x : ℝ => x ^ j * iteratedDeriv j f x)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  intro f hf hB j hj1 hjk
  have key : ∀ n : ℕ, ∀ j : ℕ, k - j ≤ n → 1 ≤ j → j ≤ k →
      Filter.Tendsto (fun x : ℝ => x ^ j * iteratedDeriv j f x)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    intro n
    induction n with
    | zero =>
      intro j hle hj1 hjk
      have hjk' : j = k := by omega
      subst j
      exact van_baseCase k hj1 hx₁ hγ hf hB
    | succ n ih =>
      intro j hle hj1 hjk
      rcases Nat.lt_or_ge (k - j) (n + 1) with hlt | hge
      · exact ih j (Nat.lt_succ_iff.mp hlt) hj1 hjk
      · exact van_step j hj1 hx₁ hf (ih (j + 1) (by omega) (by omega) (by omega))
  exact key k j (Nat.sub_le k j) hj1 hjk

end Work.FTS.H2.DivQ
