import Mathlib
import Submission.Work.C17.seventeen_defs
import Submission.Work.C17f.deriv_hasSum_powSeries
import Submission.Work.C17f.differentiableOn_of_hasSum_powSeries

/-!
# The `D_y`-iterates of a power series composed with `y = z²/(z−1)`

For a power series `f = Σ cₙ Xⁿ` over `ℚ` whose coefficients grow at most geometrically with
ratio `1/R`, the function `g(w) = Σ cₙ wⁿ` is analytic on the disc `‖w‖ < R`, and

  `D_y^k (g ∘ y)(z) = ((d/dw)^k g)(y(z))`,

where `D_y = y'(z)⁻¹ · d/dz` is the derivative with respect to `y = yC z = z²/(z−1)`.

Written coefficientwise, `(d/dw)^k g` is represented by the `k`-th formal derivative of `f`:

  `DyIter k (fun w => Σₙ cₙ · yC w ^ n) z = Σₙ (coeff n (f^{(k)})) · yC z ^ n`

for `‖yC z‖ < R` and `z ∉ {0, 1, 2}` (the points at which `y'` vanishes or `yC` is singular).
-/

namespace Work.C17I

open scoped BigOperators

noncomputable section

/-- The coefficient sequence of the formal derivative: `(derivCoeff c) n = (n+1) · c (n+1)`.
The `k`-th iterate of `derivCoeff`, applied to the coefficients of `f`, gives the coefficients
of the `k`-th formal derivative of `f` (see `coeff_iter_derivative`). -/
def derivCoeff (c : ℕ → ℂ) : ℕ → ℂ := fun n => ((n : ℂ) + 1) * c (n + 1)

/-- `d/dz (z²/(z−1)) = (z² − 2z)/(z−1)²`, i.e. `(yC)'·y' = 1` for `y' = (z²−2z)/(z−1)²`. -/
lemma hasDerivAt_yC (z : ℂ) (hz : z ≠ 1) :
    HasDerivAt Work.C17.yC ((z ^ 2 - 2 * z) / (z - 1) ^ 2) z := by
  have h := (hasDerivAt_pow 2 z).div ((hasDerivAt_id z).sub_const 1) (sub_ne_zero.mpr hz)
  refine h.congr_deriv ?_
  simp only [id_eq]
  ring

/-- `derivCoeff` iterated `k` times computes the coefficients of the `k`-th formal derivative. -/
lemma coeff_iter_derivative (f : PowerSeries ℚ) (k n : ℕ) :
    ((PowerSeries.coeff n ((PowerSeries.derivative (R := ℚ))^[k] f) : ℚ) : ℂ)
      = (derivCoeff^[k] (fun m : ℕ => ((PowerSeries.coeff m f : ℚ) : ℂ))) n := by
  induction k generalizing n with
  | zero => simp [Function.iterate_zero]
  | succ k ih =>
    have h1 : (PowerSeries.derivative (R := ℚ))^[k+1] f
        = PowerSeries.derivative (R := ℚ) ((PowerSeries.derivative (R := ℚ))^[k] f) :=
      Function.iterate_succ_apply' _ _ _
    rw [h1, PowerSeries.coeff_derivative, Function.iterate_succ_apply']
    simp only [derivCoeff]
    rw [← ih (n+1)]
    push_cast
    ring

/-- **Chain rule for `D_y`.**  If the series `Σ cₙ wⁿ` converges on the disc `‖w‖ < R`, then on
the region `‖yC z‖ < R`, `z ∉ {0, 1, 2}` the `k`-th iterate of `D_y = y'⁻¹ d/dz` applied to
`z ↦ Σ cₙ · yC z ^ n` is the same series with coefficients replaced by the `k`-fold formal
derivative sequence `derivCoeff^[k] c`.  (The summability statement carried along in the
conjunction is what makes the induction step work: it supplies the radius hypothesis for the
derived series.) -/
theorem dyIter_tsum_comp_yC (c : ℕ → ℂ) {R : ℝ}
    (hc : ∀ w : ℂ, ‖w‖ < R → Summable (fun n : ℕ => c n * w ^ n)) :
    ∀ k : ℕ,
      (∀ w : ℂ, ‖w‖ < R → Summable (fun n : ℕ => (derivCoeff^[k] c) n * w ^ n)) ∧
      (∀ z : ℂ, ‖Work.C17.yC z‖ < R → z ≠ 0 → z ≠ 1 → z ≠ 2 →
        Work.C17.DyIter k (fun w : ℂ => ∑' n : ℕ, c n * Work.C17.yC w ^ n) z
          = ∑' n : ℕ, (derivCoeff^[k] c) n * Work.C17.yC z ^ n) := by
  intro k
  induction k with
  | zero =>
    refine ⟨fun w hw => ?_, fun z hzR h0 h1 h2 => ?_⟩
    · simpa [Function.iterate_zero] using hc w hw
    · simp [Work.C17.DyIter, Function.iterate_zero]
  | succ k ih =>
    obtain ⟨ihsum, ihid⟩ := ih
    have hHS : ∀ u : ℂ, ‖u‖ < R →
        HasSum (fun n : ℕ => (derivCoeff^[k] c) n * u ^ n)
          (∑' n : ℕ, (derivCoeff^[k] c) n * u ^ n) :=
      fun u hu => (ihsum u hu).hasSum
    refine ⟨fun w hw => ?_, fun z hzR h0 h1 h2 => ?_⟩
    · -- summability of the derived series at every point of the disc
      have hd := Work.C17f.deriv_hasSum_powSeries (derivCoeff^[k] c) R
          (fun u : ℂ => ∑' n : ℕ, (derivCoeff^[k] c) n * u ^ n) hHS w hw
      rw [Function.iterate_succ_apply']
      exact hd.summable
    · -- the induction step: `D_y (D_y^k (g∘y)) = (d/dw)^{k+1} g ∘ y`
      have hGkdiff : DifferentiableAt ℂ
          (fun u : ℂ => ∑' n : ℕ, (derivCoeff^[k] c) n * u ^ n) (Work.C17.yC z) :=
        (Work.C17f.differentiableOn_of_hasSum_powSeries hHS).differentiableAt
          (Metric.isOpen_ball.mem_nhds (by rw [Metric.mem_ball, dist_zero_right]; exact hzR))
      have hyCdiff : DifferentiableAt ℂ Work.C17.yC z := (hasDerivAt_yC z h1).differentiableAt
      have hcomp : ((fun u : ℂ => ∑' n : ℕ, (derivCoeff^[k] c) n * u ^ n) ∘ Work.C17.yC)
          = (fun u : ℂ => ∑' n : ℕ, (derivCoeff^[k] c) n * Work.C17.yC u ^ n) := rfl
      have hchain : deriv (fun u : ℂ => ∑' n : ℕ, (derivCoeff^[k] c) n * Work.C17.yC u ^ n) z
          = deriv (fun u : ℂ => ∑' n : ℕ, (derivCoeff^[k] c) n * u ^ n) (Work.C17.yC z)
              * deriv Work.C17.yC z := by
        rw [← hcomp]
        exact deriv_comp (x := z) hGkdiff hyCdiff
      have hdyC : deriv Work.C17.yC z = (z ^ 2 - 2 * z) / (z - 1) ^ 2 :=
        (hasDerivAt_yC z h1).deriv
      have hd := Work.C17f.deriv_hasSum_powSeries (derivCoeff^[k] c) R
          (fun u : ℂ => ∑' n : ℕ, (derivCoeff^[k] c) n * u ^ n) hHS (Work.C17.yC z) hzR
      have hderiv_val : deriv (fun u : ℂ => ∑' n : ℕ, (derivCoeff^[k] c) n * u ^ n)
            (Work.C17.yC z)
          = ∑' n : ℕ, (derivCoeff^[k+1] c) n * Work.C17.yC z ^ n := by
        have hfun : (fun n : ℕ => (↑n + 1) * (derivCoeff^[k] c) (n + 1) * Work.C17.yC z ^ n)
            = (fun n : ℕ => (derivCoeff^[k+1] c) n * Work.C17.yC z ^ n) := by
          funext n
          rw [Function.iterate_succ_apply']
          rfl
        rw [hfun] at hd
        exact hd.tsum_eq.symm
      -- the three excluded points and the disc condition hold on a neighbourhood of `z`
      have hU : ∀ᶠ u in nhds z, ‖Work.C17.yC u‖ < R ∧ u ≠ 0 ∧ u ≠ 1 ∧ u ≠ 2 := by
        have hyCcont : ContinuousAt Work.C17.yC z := by
          show ContinuousAt (fun u : ℂ => u ^ 2 / (u - 1)) z
          exact (continuousAt_id.pow 2).div (continuousAt_id.sub continuousAt_const)
            (sub_ne_zero.mpr h1)
        exact (hyCcont.norm.tendsto.eventually (isOpen_Iio.mem_nhds hzR)).and
          ((eventually_ne_nhds h0).and ((eventually_ne_nhds h1).and (eventually_ne_nhds h2)))
      have hev : Work.C17.DyIter k (fun u : ℂ => ∑' n : ℕ, c n * Work.C17.yC u ^ n)
          =ᶠ[nhds z] (fun u : ℂ => ∑' n : ℕ, (derivCoeff^[k] c) n * Work.C17.yC u ^ n) := by
        filter_upwards [hU] with u hu
        exact ihid u hu.1 hu.2.1 hu.2.2.1 hu.2.2.2
      rw [show Work.C17.DyIter (k+1) (fun u : ℂ => ∑' n : ℕ, c n * Work.C17.yC u ^ n)
            = Work.C17.Dy (Work.C17.DyIter k
              (fun u : ℂ => ∑' n : ℕ, c n * Work.C17.yC u ^ n)) from by
          funext u
          simp only [Work.C17.DyIter, Function.iterate_succ_apply']]
      change deriv (Work.C17.DyIter k (fun u : ℂ => ∑' n : ℕ, c n * Work.C17.yC u ^ n)) z
          * (z - 1) ^ 2 / (z ^ 2 - 2 * z)
        = ∑' n : ℕ, (derivCoeff^[k+1] c) n * Work.C17.yC z ^ n
      rw [hev.deriv_eq, hchain, hdyC, hderiv_val]
      have hd0 : z ^ 2 - 2 * z ≠ 0 := by
        have h : z * (z - 2) ≠ 0 := mul_ne_zero h0 (sub_ne_zero.mpr h2)
        rw [show z ^ 2 - 2 * z = z * (z - 2) from by ring]
        exact h
      have hd1 : (z - 1) ^ 2 ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr h1)
      field_simp

theorem DyIter_comp_yC (f : PowerSeries ℚ) {C R : ℝ} (hC : 0 < C) (hR : 0 < R)
    (hf : ∀ n : ℕ, ‖((PowerSeries.coeff n f : ℚ) : ℂ)‖ * R ^ n ≤ C) :
    ∀ z : ℂ, ‖Work.C17.yC z‖ < R → z ≠ 0 → z ≠ 1 → z ≠ 2 → ∀ k : ℕ,
      Work.C17.DyIter k (fun w : ℂ => ∑' n : ℕ, ((PowerSeries.coeff n f : ℚ) : ℂ) * Work.C17.yC w ^ n) z
        = ∑' n : ℕ, ((PowerSeries.coeff n ((PowerSeries.derivative (R := ℚ))^[k] f) : ℚ) : ℂ)
            * Work.C17.yC z ^ n := by
  intro z hzR h0 h1 h2 k
  -- the coefficient bound gives convergence on the disc `‖w‖ < R` by comparison with a geometric
  -- series
  have hc : ∀ w : ℂ, ‖w‖ < R →
      Summable (fun n : ℕ => ((PowerSeries.coeff n f : ℚ) : ℂ) * w ^ n) := by
    intro w hw
    have hwR : ‖w‖ / R < 1 := by rw [div_lt_one hR]; exact hw
    have hgeo : Summable (fun n : ℕ => (‖w‖ / R) ^ n) := by
      refine summable_geometric_of_norm_lt_one (x := ‖w‖ / R) ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (norm_nonneg w) hR.le)]
      exact hwR
    refine Summable.of_norm_bounded (hgeo.mul_left C) fun n => ?_
    have hRpos : 0 < R ^ n := pow_pos hR n
    have hcn : ‖((PowerSeries.coeff n f : ℚ) : ℂ)‖ ≤ C / R ^ n := by
      rw [le_div_iff₀ hRpos]; exact hf n
    calc ‖((PowerSeries.coeff n f : ℚ) : ℂ) * w ^ n‖
        = ‖((PowerSeries.coeff n f : ℚ) : ℂ)‖ * ‖w‖ ^ n := by rw [norm_mul, norm_pow]
      _ ≤ (C / R ^ n) * ‖w‖ ^ n := by gcongr
      _ = C * (‖w‖ / R) ^ n := by rw [div_pow]; field_simp
  have hmain :=
    (dyIter_tsum_comp_yC (fun n : ℕ => ((PowerSeries.coeff n f : ℚ) : ℂ)) hc k).2
  rw [hmain z hzR h0 h1 h2]
  refine tsum_congr fun n => ?_
  rw [coeff_iter_derivative]

end

end Work.C17I
