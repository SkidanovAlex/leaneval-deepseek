import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Submission.Work.FTS.H2.DivQ.two_mul_div_abs_le
import Submission.Work.FTS.H2.DivQ.powerIbp
import Submission.Work.FTS.H2.DivQ.hardy_combine

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2.DivQ

open MeasureTheory Set Filter
open scoped Topology

/-- Pointwise AM-GM with a power weight: for `x > 0` and `p ≠ -1`,
`(2/|p+1|) · x^{p+1}·|u w| ≤ (1/2)·x^p u² + (2/(p+1)²)·x^{p+2} w²`.  The two squares on the
right are the `L²` weights of the Hardy inequality, and the pointwise identity
`(x^{p+1}|uw|)² = (x^p u²)·(x^{p+2}w²)` (for `x > 0`) reduces this to `two_mul_div_abs_le`. -/
lemma rpow_two_mul_div_abs_le (p : ℝ) (hp : p ≠ -1) {x : ℝ} (hx : 0 < x) (u w : ℝ) :
    (2 / |p + 1|) * (x ^ (p + 1) * |u * w|)
      ≤ (1 / 2) * (x ^ p * u ^ 2) + (2 / (p + 1) ^ 2) * (x ^ (p + 2) * w ^ 2) := by
  have hs : p + 1 ≠ 0 := by intro h; exact hp (by linarith)
  have hsq : (x ^ (p + 1) * |u * w|) ^ 2 ≤ (x ^ p * u ^ 2) * (x ^ (p + 2) * w ^ 2) := by
    have h1 : (x ^ (p + 1)) ^ 2 = x ^ p * x ^ (p + 2) := by
      rw [pow_two, ← Real.rpow_add hx (p + 1) (p + 1), ← Real.rpow_add hx p (p + 2)]
      congr 1
      ring
    rw [mul_pow, sq_abs, h1]
    exact le_of_eq (by ring)
  have h := two_mul_div_abs_le (x ^ p * u ^ 2) (x ^ (p + 2) * w ^ 2) (x ^ (p + 1) * |u * w|)
    (p + 1) (by positivity) (by positivity) (by positivity) hsq hs
  calc (2 / |p + 1|) * (x ^ (p + 1) * |u * w|)
      = 2 * (x ^ (p + 1) * |u * w|) / |p + 1| := by ring
    _ ≤ (x ^ p * u ^ 2) / 2 + 2 * (x ^ (p + 2) * w ^ 2) / (p + 1) ^ 2 := h
    _ = (1 / 2) * (x ^ p * u ^ 2) + (2 / (p + 1) ^ 2) * (x ^ (p + 2) * w ^ 2) := by ring

/-- The weighted Hardy inequality with a power weight and an explicit boundary term, on a
half-open interval `(0, x₁]`, for every real exponent `p ≠ -1`:

  `∫_0^{x₁} x^p v² dx ≤ 4/(p+1)² ∫_0^{x₁} x^{p+2} (v')² dx + 2 x₁^{p+1}/|p+1| * (v x₁)²`,

for `v` of class `C^∞` on `(0,x₁]` (note `Set.Ioc`, so that the value `v x₁` is tied to the
behaviour on the interval and is the left limit), with `x^{p+1}v(x)² → 0` at `0⁺` and with the
right-hand integral honest.  (`x^{p+1}v(x)² → 0` is automatic when `p > -1` and `v → 0`; for
`p < -1` it is a genuine boundary condition.  The constant `4/(p+1)²` is the sharp Hardy constant;
the last term collects the boundary contribution at `x₁`, positive (harmful) exactly when `p > -1`
and helpful when `p < -1`, so the absolute value is the safe formulation.)

PROOF.  For `0 < ε < x₁` integrate by parts over `(ε,x₁)` (`x^{p+1} v²` has derivative
`(p+1)x^p v² + 2x^{p+1}vv'`):

  `A_ε = (x₁^{p+1}v(x₁)² - ε^{p+1}v(ε)²)/(p+1) - 2/(p+1) ∫_ε^{x₁} x^{p+1} v v'`

with `A_ε = ∫_ε^{x₁}x^p v²`.  Cauchy–Schwarz in the form
`∫_ε^{x₁}x^{p+1}|vv'| ≤ A_ε^{1/2} C_ε^{1/2}` with `C_ε = ∫_ε^{x₁}x^{p+2}(v')² ≤ C := ∫_0^{x₁}x^{p+2}(v')²`
gives `A_ε ≤ x₁^{p+1}v(x₁)²/|p+1| + |ε^{p+1}v(ε)²/(p+1)| + 2/|p+1| A_ε^{1/2}C^{1/2}`; the
`ε`-term tends to `0` by hypothesis, and completing the square (`A_ε - 2|p+1|^{-1}C^{1/2}A_ε^{1/2} ≤ M`,
`M := x₁^{p+1}v(x₁)²/|p+1|`) yields `A_ε^{1/2} ≤ C^{1/2}/|p+1| + (M + C/(p+1)²)^{1/2}`, hence
`A_ε ≤ 2M + 4C/(p+1)²`; monotone convergence to `A = ∫_0^{x₁}x^pv²` gives the claim. -/
theorem powerHardyBoundary (p x₁ : ℝ) (hp : p ≠ -1) (hx₁ : 0 < x₁) :
    ∀ v : ℝ → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) v (Set.Ioc 0 x₁) →
      Filter.Tendsto (fun x : ℝ => x ^ (p + 1) * (v x) ^ 2) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) →
      MeasureTheory.IntegrableOn (fun x : ℝ => x ^ (p + 2) * (deriv v x) ^ 2) (Set.Ioc 0 x₁) →
      (∫ x in (0 : ℝ)..x₁, x ^ p * (v x) ^ 2)
        ≤ 4 / (p + 1) ^ 2 * (∫ x in (0 : ℝ)..x₁, x ^ (p + 2) * (deriv v x) ^ 2)
          + 2 * (x₁ ^ (p + 1) / |p + 1|) * (v x₁) ^ 2 := by
  intro v hv hv0 hvint
  have hs0 : p + 1 ≠ 0 := by intro h; exact hp (by linarith)
  have hsabs : 0 < |p + 1| := abs_pos.mpr hs0
  set D : ℝ → ℝ := derivWithin v (Set.Ioc 0 x₁) with hDdef
  have hvcont : ContinuousOn v (Set.Ioc 0 x₁) := hv.continuousOn
  have hDcont : ContinuousOn D (Set.Ioc 0 x₁) := by
    rw [hDdef]
    exact hv.continuousOn_derivWithin (uniqueDiffOn_Ioc 0 x₁) (WithTop.coe_le_coe.mpr le_top)
  have hDeq : ∀ x ∈ Set.Ioo (0 : ℝ) x₁, D x = deriv v x := by
    intro x hx
    rw [hDdef]
    exact derivWithin_of_mem_nhds (Ioc_mem_nhds hx.1 hx.2)
  -- integrability of the `D`-version of the weight, and identification of the two integrals
  have hCint : IntegrableOn (fun x : ℝ => x ^ (p + 2) * (D x) ^ 2) (Set.Ioc 0 x₁) := by
    have h1 : IntegrableOn (fun x : ℝ => x ^ (p + 2) * (deriv v x) ^ 2) (Set.Ioo 0 x₁) :=
      hvint.mono_set Set.Ioo_subset_Ioc_self
    have h2 : IntegrableOn (fun x : ℝ => x ^ (p + 2) * (D x) ^ 2) (Set.Ioo 0 x₁) :=
      h1.congr_fun (fun x hx => by rw [hDeq x hx]) measurableSet_Ioo
    exact h2.congr_set_ae Ioo_ae_eq_Ioc.symm
  have hCeq : (∫ x in (0 : ℝ)..x₁, x ^ (p + 2) * (deriv v x) ^ 2)
      = ∫ x in (0 : ℝ)..x₁, x ^ (p + 2) * (D x) ^ 2 := by
    rw [intervalIntegral.integral_of_le hx₁.le, intervalIntegral.integral_of_le hx₁.le]
    symm
    refine setIntegral_congr_ae measurableSet_Ioc ?_
    rw [MeasureTheory.ae_iff]
    refine measure_mono_null ?_ (measure_singleton x₁)
    intro x hx
    simp only [mem_ofPred_eq, not_imp] at hx
    by_contra hxne
    have hne : x ≠ x₁ := by simpa using hxne
    exact hx.2 (by rw [hDeq x ⟨hx.1.1, lt_of_le_of_ne hx.1.2 hne⟩])
  -- continuity of the pieces on `Icc ε x₁`
  have hcontf : ∀ ε : ℝ, 0 < ε →
      ContinuousOn (fun x : ℝ => x ^ p * (v x) ^ 2) (Set.Icc ε x₁) := by
    intro ε hε
    have hsub : Set.Icc ε x₁ ⊆ Set.Ioc 0 x₁ := fun x hx => ⟨lt_of_lt_of_le hε hx.1, hx.2⟩
    exact (continuousOn_id.rpow_const (fun x hx => Or.inl (ne_of_gt (lt_of_lt_of_le hε hx.1)))).mul
      ((hvcont.mono hsub).pow 2)
  have hcontg : ∀ ε : ℝ, 0 < ε →
      ContinuousOn (fun x : ℝ => x ^ (p + 2) * (D x) ^ 2) (Set.Icc ε x₁) := by
    intro ε hε
    have hsub : Set.Icc ε x₁ ⊆ Set.Ioc 0 x₁ := fun x hx => ⟨lt_of_lt_of_le hε hx.1, hx.2⟩
    exact (continuousOn_id.rpow_const (fun x hx => Or.inl (ne_of_gt (lt_of_lt_of_le hε hx.1)))).mul
      ((hDcont.mono hsub).pow 2)
  have hcontJ : ∀ ε : ℝ, 0 < ε →
      ContinuousOn (fun x : ℝ => x ^ (p + 1) * (v x * D x)) (Set.Icc ε x₁) := by
    intro ε hε
    have hsub : Set.Icc ε x₁ ⊆ Set.Ioc 0 x₁ := fun x hx => ⟨lt_of_lt_of_le hε hx.1, hx.2⟩
    exact (continuousOn_id.rpow_const (fun x hx => Or.inl (ne_of_gt (lt_of_lt_of_le hε hx.1)))).mul
      ((hvcont.mono hsub).mul (hDcont.mono hsub))
  have hcontJa : ∀ ε : ℝ, 0 < ε →
      ContinuousOn (fun x : ℝ => x ^ (p + 1) * |v x * D x|) (Set.Icc ε x₁) := by
    intro ε hε
    have hsub : Set.Icc ε x₁ ⊆ Set.Ioc 0 x₁ := fun x hx => ⟨lt_of_lt_of_le hε hx.1, hx.2⟩
    exact (continuousOn_id.rpow_const (fun x hx => Or.inl (ne_of_gt (lt_of_lt_of_le hε hx.1)))).mul
      ((hvcont.mono hsub).mul (hDcont.mono hsub)).abs
  -- the per-`ε` bound
  have key : ∀ ε : ℝ, 0 < ε → ε < x₁ →
      (∫ x in ε..x₁, x ^ p * (v x) ^ 2)
        ≤ 4 / (p + 1) ^ 2 * (∫ x in (0 : ℝ)..x₁, x ^ (p + 2) * (D x) ^ 2)
          + 2 * (x₁ ^ (p + 1) / |p + 1|) * (v x₁) ^ 2
          + 2 * (ε ^ (p + 1) * (v ε) ^ 2) / |p + 1| := by
    intro ε hε hεx
    have hεle : ε ≤ x₁ := hεx.le
    -- (1) integration by parts
    have hIBP : (p + 1) * (∫ x in ε..x₁, x ^ p * (v x) ^ 2)
        = x₁ ^ (p + 1) * (v x₁) ^ 2 - ε ^ (p + 1) * (v ε) ^ 2
          - 2 * (∫ x in ε..x₁, x ^ (p + 1) * (v x * D x)) := by
      have h := powerIbp p x₁ ε hε hεx v hv
      rw [hDdef]
      exact h
    -- (2) `|J| ≤ Ja` and the integrated AM-GM
    have hJle : |∫ x in ε..x₁, x ^ (p + 1) * (v x * D x)|
        ≤ ∫ x in ε..x₁, x ^ (p + 1) * |v x * D x| := by
      refine (intervalIntegral.abs_integral_le_integral_abs hεle).trans ?_
      refine intervalIntegral.integral_mono_on hεle ?_ ?_ ?_
      · exact ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hεle ((hcontJ ε hε).abs)
      · exact ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hεle (hcontJa ε hε)
      · intro x hx
        rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (le_of_lt (lt_of_lt_of_le hε hx.1)) _)]
    have hamgm : 2 * (∫ x in ε..x₁, x ^ (p + 1) * |v x * D x|) / |p + 1|
        ≤ (∫ x in ε..x₁, x ^ p * (v x) ^ 2) / 2
          + 2 * (∫ x in ε..x₁, x ^ (p + 2) * (D x) ^ 2) / (p + 1) ^ 2 := by
      have hpt : ∀ x ∈ Set.Icc ε x₁, (2 / |p + 1|) * (x ^ (p + 1) * |v x * D x|)
          ≤ (1 / 2) * (x ^ p * (v x) ^ 2)
            + (2 / (p + 1) ^ 2) * (x ^ (p + 2) * (D x) ^ 2) :=
        fun x hx => rpow_two_mul_div_abs_le p hp (lt_of_lt_of_le hε hx.1) (v x) (D x)
      have h1 : IntervalIntegrable
          (fun x : ℝ => (2 / |p + 1|) * (x ^ (p + 1) * |v x * D x|)) volume ε x₁ :=
        ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hεle ((hcontJa ε hε).const_mul _)
      have h2a : IntervalIntegrable (fun x : ℝ => (1 / 2) * (x ^ p * (v x) ^ 2)) volume ε x₁ :=
        ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hεle ((hcontf ε hε).const_mul _)
      have h2b : IntervalIntegrable
          (fun x : ℝ => (2 / (p + 1) ^ 2) * (x ^ (p + 2) * (D x) ^ 2)) volume ε x₁ :=
        ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hεle ((hcontg ε hε).const_mul _)
      have h2 : IntervalIntegrable
          (fun x : ℝ => (1 / 2) * (x ^ p * (v x) ^ 2)
            + (2 / (p + 1) ^ 2) * (x ^ (p + 2) * (D x) ^ 2)) volume ε x₁ :=
        h2a.add h2b
      have hmono := intervalIntegral.integral_mono_on hεle h1 h2 hpt
      rw [intervalIntegral.integral_const_mul] at hmono
      rw [intervalIntegral.integral_add h2a h2b, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul] at hmono
      calc 2 * (∫ x in ε..x₁, x ^ (p + 1) * |v x * D x|) / |p + 1|
          = (2 / |p + 1|) * (∫ x in ε..x₁, x ^ (p + 1) * |v x * D x|) := by ring
        _ ≤ (1 / 2) * (∫ x in ε..x₁, x ^ p * (v x) ^ 2)
              + (2 / (p + 1) ^ 2) * (∫ x in ε..x₁, x ^ (p + 2) * (D x) ^ 2) := hmono
        _ = (∫ x in ε..x₁, x ^ p * (v x) ^ 2) / 2
              + 2 * (∫ x in ε..x₁, x ^ (p + 2) * (D x) ^ 2) / (p + 1) ^ 2 := by ring
    -- (3) monotonicity in `ε` of the `C`-integral
    have hcC : (∫ x in ε..x₁, x ^ (p + 2) * (D x) ^ 2)
        ≤ (∫ x in (0 : ℝ)..x₁, x ^ (p + 2) * (D x) ^ 2) := by
      rw [intervalIntegral.integral_of_le hεle, intervalIntegral.integral_of_le hx₁.le]
      refine integral_mono_measure (Measure.restrict_mono ?_ le_rfl) ?_ hCint
      · exact Ioc_subset_Ioc (le_of_lt hε) le_rfl
      · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
        exact mul_nonneg (Real.rpow_nonneg (le_of_lt hx.1) _) (sq_nonneg _)
    -- (4) nonnegativity
    have ha0 : 0 ≤ ∫ x in ε..x₁, x ^ p * (v x) ^ 2 := by
      rw [intervalIntegral.integral_of_le hεle]
      refine setIntegral_nonneg measurableSet_Ioc (fun x hx => ?_)
      exact mul_nonneg (Real.rpow_nonneg (le_of_lt (lt_trans hε hx.1)) _) (sq_nonneg _)
    have hc0 : 0 ≤ ∫ x in ε..x₁, x ^ (p + 2) * (D x) ^ 2 := by
      rw [intervalIntegral.integral_of_le hεle]
      refine setIntegral_nonneg measurableSet_Ioc (fun x hx => ?_)
      exact mul_nonneg (Real.rpow_nonneg (le_of_lt (lt_trans hε hx.1)) _) (sq_nonneg _)
    have hJa0 : 0 ≤ ∫ x in ε..x₁, x ^ (p + 1) * |v x * D x| := by
      rw [intervalIntegral.integral_of_le hεle]
      refine setIntegral_nonneg measurableSet_Ioc (fun x hx => ?_)
      exact mul_nonneg (Real.rpow_nonneg (le_of_lt (lt_trans hε hx.1)) _) (abs_nonneg _)
    -- (5) the arithmetic
    have hcomb := hardy_combine (∫ x in ε..x₁, x ^ p * (v x) ^ 2)
      (x₁ ^ (p + 1) * (v x₁) ^ 2) (ε ^ (p + 1) * (v ε) ^ 2)
      (∫ x in ε..x₁, x ^ (p + 1) * (v x * D x)) (∫ x in ε..x₁, x ^ (p + 1) * |v x * D x|)
      (∫ x in ε..x₁, x ^ (p + 2) * (D x) ^ 2)
      (∫ x in (0 : ℝ)..x₁, x ^ (p + 2) * (D x) ^ 2) (p + 1) hs0 ha0 (by positivity) (by positivity)
      hJle hJa0 hc0 hcC hIBP hamgm
    calc (∫ x in ε..x₁, x ^ p * (v x) ^ 2)
        ≤ 4 * (∫ x in (0 : ℝ)..x₁, x ^ (p + 2) * (D x) ^ 2) / (p + 1) ^ 2
            + 2 * (x₁ ^ (p + 1) * (v x₁) ^ 2 + ε ^ (p + 1) * (v ε) ^ 2) / |p + 1| := hcomb
      _ = 4 / (p + 1) ^ 2 * (∫ x in (0 : ℝ)..x₁, x ^ (p + 2) * (D x) ^ 2)
            + 2 * (x₁ ^ (p + 1) / |p + 1|) * (v x₁) ^ 2
            + 2 * (ε ^ (p + 1) * (v ε) ^ 2) / |p + 1| := by ring
  -- the `n`-indexed eventual bound
  have ha0_nhds : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Filter.Eventually.of_forall fun n => by
        show (0 : ℝ) < 1 / ((n : ℝ) + 1)
        positivity⟩
  have hltx_nhds : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), ε < x₁ :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (Iio_mem_nhds hx₁)
  have hbnd_n : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in Filter.atTop,
      (∫ x in (1 / ((n : ℝ) + 1))..x₁, x ^ p * (v x) ^ 2)
        ≤ 4 / (p + 1) ^ 2 * (∫ x in (0 : ℝ)..x₁, x ^ (p + 2) * (D x) ^ 2)
          + 2 * (x₁ ^ (p + 1) / |p + 1|) * (v x₁) ^ 2 + δ := by
    intro δ hδ
    have hpos : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < ε := self_mem_nhdsWithin
    have hltx : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), ε < x₁ := hltx_nhds
    have hkey : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < ε → ε < x₁ →
        (∫ x in ε..x₁, x ^ p * (v x) ^ 2)
          ≤ 4 / (p + 1) ^ 2 * (∫ x in (0 : ℝ)..x₁, x ^ (p + 2) * (D x) ^ 2)
            + 2 * (x₁ ^ (p + 1) / |p + 1|) * (v x₁) ^ 2
            + 2 * (ε ^ (p + 1) * (v ε) ^ 2) / |p + 1| :=
      Filter.Eventually.of_forall fun ε => key ε
    have hsmall : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        ε ^ (p + 1) * (v ε) ^ 2 ≤ δ * |p + 1| / 2 :=
      hv0.eventually (eventually_le_nhds (by positivity : (0 : ℝ) < δ * |p + 1| / 2))
    have hall : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < ε ∧ ε < x₁ ∧
        (∫ x in ε..x₁, x ^ p * (v x) ^ 2)
          ≤ 4 / (p + 1) ^ 2 * (∫ x in (0 : ℝ)..x₁, x ^ (p + 2) * (D x) ^ 2)
            + 2 * (x₁ ^ (p + 1) / |p + 1|) * (v x₁) ^ 2
            + 2 * (ε ^ (p + 1) * (v ε) ^ 2) / |p + 1|
        ∧ ε ^ (p + 1) * (v ε) ^ 2 ≤ δ * |p + 1| / 2 := by
      filter_upwards [hpos, hltx, hkey, hsmall] with ε h1 h2 h3 h4
      exact ⟨h1, h2, h3 h1 h2, h4⟩
    filter_upwards [ha0_nhds.eventually hall] with n hn
    obtain ⟨h1, h2, h3, h4⟩ := hn
    have h5 : 2 * ((1 / ((n : ℝ) + 1)) ^ (p + 1) * (v (1 / ((n : ℝ) + 1))) ^ 2) / |p + 1| ≤ δ := by
      rw [div_le_iff₀ hsabs]
      nlinarith [h4]
    linarith
  -- integrability of `x^p v²` on `(0,x₁]`
  have hfint : IntegrableOn (fun x : ℝ => x ^ p * (v x) ^ 2) (Set.Ioc 0 x₁) := by
    refine integrableOn_Ioc_of_intervalIntegral_norm_bounded_left (l := Filter.atTop)
      (a := fun n : ℕ => 1 / ((n : ℝ) + 1)) (a₀ := 0) (b := x₁)
      (I := 4 / (p + 1) ^ 2 * (∫ x in (0 : ℝ)..x₁, x ^ (p + 2) * (D x) ^ 2)
        + 2 * (x₁ ^ (p + 1) / |p + 1|) * (v x₁) ^ 2 + 1) ?_ ?_ ?_
    · intro n
      rcases le_or_gt (1 / ((n : ℝ) + 1)) x₁ with hle | hgt
      · exact (ContinuousOn.intervalIntegrable_of_Icc (μ := volume)
          (a := 1 / ((n : ℝ) + 1)) (b := x₁) hle (hcontf _ (by positivity))).1
      · have hempty : Set.Ioc (1 / ((n : ℝ) + 1)) x₁ = ∅ :=
          Set.Ioc_eq_empty (a := x₁) (b := 1 / ((n : ℝ) + 1)) (not_lt.mpr (le_of_lt hgt))
        rw [hempty]
        exact integrableOn_empty
    · exact tendsto_one_div_add_atTop_nhds_zero_nat
    · filter_upwards [hbnd_n 1 one_pos, ha0_nhds.eventually hltx_nhds] with n hn hlt
      have h1 : (∫ x in Set.Ioc (1 / ((n : ℝ) + 1)) x₁, ‖x ^ p * (v x) ^ 2‖)
          = ∫ x in Set.Ioc (1 / ((n : ℝ) + 1)) x₁, x ^ p * (v x) ^ 2 := by
        refine setIntegral_congr_fun measurableSet_Ioc (fun x hx => ?_)
        rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg (le_of_lt (lt_trans (by positivity) hx.1)) _) (sq_nonneg _))]
      rw [h1, ← intervalIntegral.integral_of_le (a := 1 / ((n : ℝ) + 1)) (b := x₁) hlt.le]
      linarith
  -- the limit
  have hAEC : AECover (volume.restrict (Set.Ioc 0 x₁)) Filter.atTop
      (fun n : ℕ => Set.Ioc (1 / ((n : ℝ) + 1)) x₁) :=
    aecover_Ioc_of_Ioc tendsto_one_div_add_atTop_nhds_zero_nat tendsto_const_nhds
  have htend := hAEC.integral_tendsto_of_countably_generated hfint
  have htend' : Filter.Tendsto (fun n : ℕ => ∫ x in (1 / ((n : ℝ) + 1))..x₁, x ^ p * (v x) ^ 2)
      Filter.atTop (𝓝 (∫ x in (0 : ℝ)..x₁, x ^ p * (v x) ^ 2)) := by
    rw [intervalIntegral.integral_of_le hx₁.le]
    refine Filter.Tendsto.congr' ?_ htend
    filter_upwards [ha0_nhds.eventually hltx_nhds] with n hn
    rw [Measure.restrict_restrict measurableSet_Ioc,
      inter_eq_left.mpr (Ioc_subset_Ioc (by positivity) le_rfl),
      intervalIntegral.integral_of_le (a := 1 / ((n : ℝ) + 1)) (b := x₁) hn.le]
  have hmain : (∫ x in (0 : ℝ)..x₁, x ^ p * (v x) ^ 2)
      ≤ 4 / (p + 1) ^ 2 * (∫ x in (0 : ℝ)..x₁, x ^ (p + 2) * (D x) ^ 2)
        + 2 * (x₁ ^ (p + 1) / |p + 1|) * (v x₁) ^ 2 := by
    refine le_of_forall_pos_le_add fun δ hδ => ?_
    exact le_of_tendsto htend' (hbnd_n δ hδ)
  rw [hCeq]
  exact hmain

end Work.FTS.H2.DivQ
