import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.ArcDefs
import Submission.Work.BourgainPlan.IonescuWainger.tendsto_fourier_diffQuot
import Submission.Work.BourgainPlan.IonescuWainger.norm_fourier_diffQuot_sub_le

open Complex Real

namespace Work.BourgainPlan.IonescuWainger

/-- The `ℓ²`-valued difference quotients of the exponential sequence converge to its derivative
at `0`: for `t → 0` (with `t ≠ 0`),
`n ↦ ((e^{2πi n t} - 1)/t) * g n → n ↦ 2πi n * g n` in `ℓ²(ℤ, ℂ)`.

Hints for the proof: `fourier_coe_apply` turns `fourier n (t : Circle)` into
`exp (2π i n t)`, and `hasDerivAt_fourier (T := 1) n 0` together with the slope form of
`HasDerivAt` (`HasDerivAt.tendsto_slope`) gives the pointwise limit
`t⁻¹ (fourier n t - 1) → 2π i n`.  Let `d t n := t⁻¹ (fourier n t - 1) g n - 2π i n g n`.  Since
`‖exp z - 1‖ ≤ 2 ‖z‖` for all `z : ℂ` (Mathlib's `Complex.norm_exp_sub_one_le` for `‖z‖ ≤ 1`,
extended to all `z` by `‖exp z - 1‖ ≤ exp ‖z‖ - 1 ≤ 2‖z‖` for `‖z‖ ≥ 1`), one has
`‖d t n‖ ≤ 6 π ‖n g n‖` for all `t` (no restriction), and `(n ↦ π ‖n g n‖) ∈ ℓ²` follows from
`htgt`.  Given `ε > 0`, choose `N` with `∑_{|n| > N} ‖d t n‖² ≤ ε²` (using `Summable` of the
domination) and then `δ > 0` with `∑_{n ∈ s, |n| ≤ N} ‖d t n‖² ≤ ε²` for `|t| < δ` (finitely many
terms, each tending to `0`); conclude `‖d t‖ ≤ 2ε` with `lp.norm_le_of_forall_sum_le`
(`lp.norm_rpow_eq_tsum`) applied to the element `⟨d t, ·⟩` of `ℓ²(ℤ,ℂ)`. -/
theorem tendsto_lp_diffQuot {g : ℤ → ℂ}
    (hdq : ∀ t : ℝ, Memℓp (fun n : ℤ => ((t : ℂ)⁻¹ * (fourier n (t : Circle) - 1)) * g n) 2)
    (htgt : Memℓp (fun n : ℤ => (2 * π * I) * ((n : ℂ) * g n)) 2) :
    Filter.Tendsto (fun t : ℝ => (⟨fun n : ℤ => ((t : ℂ)⁻¹ * (fourier n (t : Circle) - 1)) * g n,
        hdq t⟩ : lp (fun _ : ℤ => ℂ) 2))
      (nhdsWithin (0 : ℝ) ({0}ᶜ))
      (nhds (⟨fun n : ℤ => (2 * π * I) * ((n : ℂ) * g n), htgt⟩ : lp (fun _ : ℤ => ℂ) 2)) := by
  let Et : ℝ → lp (fun _ : ℤ => ℂ) 2 :=
    fun t => ⟨fun n : ℤ => ((t : ℂ)⁻¹ * (fourier n (t : Circle) - 1)) * g n, hdq t⟩
  let y : lp (fun _ : ℤ => ℂ) 2 := ⟨fun n : ℤ => (2 * π * I) * ((n : ℂ) * g n), htgt⟩
  change Filter.Tendsto Et (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds y)
  let d : ℝ → ℤ → ℂ := fun t n =>
    (((t : ℂ)⁻¹ * (fourier n (t : Circle) - 1)) - (2 : ℂ) * Real.pi * Complex.I * (n : ℂ)) * g n
  -- the difference `Et t - y` is the `ℓ²`-element with coordinates `d t n`
  have hcoe : ∀ t n, ((Et t - y) n : ℂ) = d t n := by
    intro t n
    simp only [lp.coeFn_sub, Pi.sub_apply, Et, y, d]
    ring_nf
  have h2pi : ‖(2 : ℂ) * Real.pi * Complex.I‖ = 2 * Real.pi := by
    rw [norm_mul, norm_mul, Complex.norm_I, mul_one]
    simp [Real.pi_pos.le]
  -- uniform-in-`t` domination of the difference quotient
  have hbound : ∀ t n, ‖d t n‖ ≤ 2 * ‖(2 * π * I) * ((n : ℂ) * g n)‖ := by
    intro t n
    have hb1 : ‖d t n‖ = ‖((t : ℂ)⁻¹ * (fourier n (t : Circle) - 1)) - (2 : ℂ) * Real.pi * Complex.I * (n : ℂ)‖ * ‖g n‖ := by
      simp only [d, norm_mul]
    have hb2 : ‖(2 * π * I) * ((n : ℂ) * g n)‖ = (2 * Real.pi) * (‖(n : ℂ)‖ * ‖g n‖) := by
      calc ‖(2 * π * I) * ((n : ℂ) * g n)‖
          = ‖(2 : ℂ) * Real.pi * Complex.I‖ * ‖(n : ℂ) * g n‖ := by rw [norm_mul]
        _ = (2 * Real.pi) * (‖(n : ℂ)‖ * ‖g n‖) := by rw [h2pi, norm_mul]
    rw [hb1, hb2]
    calc ‖((t : ℂ)⁻¹ * (fourier n (t : Circle) - 1)) - (2 : ℂ) * Real.pi * Complex.I * (n : ℂ)‖ * ‖g n‖
        ≤ ((4 : ℝ) * Real.pi * ‖(n : ℂ)‖) * ‖g n‖ :=
          mul_le_mul_of_nonneg_right (norm_fourier_diffQuot_sub_le t n) (norm_nonneg _)
      _ = 2 * ((2 * Real.pi) * (‖(n : ℂ)‖ * ‖g n‖)) := by ring
  have hsum : Summable (fun n : ℤ => (4 : ℝ) * ‖(2 * π * I) * ((n : ℂ) * g n)‖ ^ 2) := by
    have h1 : Summable (fun n : ℤ => ‖(2 * π * I) * ((n : ℂ) * g n)‖ ^ 2) := by
      have h := Memℓp.summable (p := (2 : ENNReal)) (by norm_num) htgt
      simpa using h
    exact h1.mul_left 4
  -- pointwise convergence of the coordinates
  have hpt : ∀ n : ℤ, Filter.Tendsto (fun t : ℝ => d t n) (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds 0) := by
    intro n
    have h1 : Filter.Tendsto (fun t : ℝ => ((t : ℂ)⁻¹ * (fourier n (t : Circle) - 1)) - (2 : ℂ) * Real.pi * Complex.I * (n : ℂ))
        (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds 0) := by
      have h := (tendsto_fourier_diffQuot n).sub (tendsto_const_nhds (x := (2 : ℂ) * Real.pi * Complex.I * (n : ℂ)))
      simpa using h
    have h2 := h1.mul_const (g n)
    simpa only [d, zero_mul] using h2
  -- dominated convergence for the `ℓ²`-norms
  have hconv : Filter.Tendsto (fun t : ℝ => ∑' n : ℤ, ‖d t n‖ ^ 2) (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds 0) := by
    have hmain := tendsto_tsum_of_dominated_convergence (𝓕 := nhdsWithin (0 : ℝ) ({0}ᶜ))
      (f := fun t (n : ℤ) => ‖d t n‖ ^ 2) (g := fun _ : ℤ => (0 : ℝ))
      (bound := fun n : ℤ => (4 : ℝ) * ‖(2 * π * I) * ((n : ℂ) * g n)‖ ^ 2) hsum
      (fun n => by
        have h := (hpt n).norm.pow 2
        simpa using h)
      (Filter.Eventually.of_forall (fun t n => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        calc ‖d t n‖ ^ 2 ≤ (2 * ‖(2 * π * I) * ((n : ℂ) * g n)‖) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) (hbound t n) 2
          _ = 4 * ‖(2 * π * I) * ((n : ℂ) * g n)‖ ^ 2 := by ring))
    simpa using hmain
  have hnormsq : ∀ t : ℝ, ‖Et t - y‖ ^ 2 = ∑' n : ℤ, ‖d t n‖ ^ 2 := by
    intro t
    have h := lp.norm_rpow_eq_tsum (p := (2 : ENNReal)) (by norm_num) (Et t - y)
    have h' : ‖Et t - y‖ ^ 2 = ∑' n : ℤ, ‖(Et t - y) n‖ ^ 2 := by simpa using h
    rw [h']
    exact tsum_congr (fun n => by rw [hcoe t n])
  have hnorm : ∀ t : ℝ, ‖Et t - y‖ = Real.sqrt (∑' n : ℤ, ‖d t n‖ ^ 2) := by
    intro t
    rw [← hnormsq t, Real.sqrt_sq (norm_nonneg _)]
  have hsqrt : Filter.Tendsto (fun t : ℝ => Real.sqrt (∑' n : ℤ, ‖d t n‖ ^ 2))
      (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds 0) := by
    have h := (Real.continuous_sqrt.continuousAt (x := 0)).tendsto.comp hconv
    simpa only [Function.comp_def, Real.sqrt_zero] using h
  have hdist : Filter.Tendsto (fun t : ℝ => dist (Et t) y) (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds 0) := by
    rw [show (fun t : ℝ => dist (Et t) y) = fun t => Real.sqrt (∑' n : ℤ, ‖d t n‖ ^ 2) from
      funext fun t => by rw [dist_eq_norm, hnorm t]]
    exact hsqrt
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨δ, hδ0, hδ⟩ := (Metric.tendsto_nhdsWithin_nhds.mp hdist) (ε / 2) (by linarith)
  refine ⟨δ, hδ0, fun x hx hxd => ?_⟩
  have h1 := hδ hx hxd
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (dist_nonneg : (0 : ℝ) ≤ dist (Et x) y)] at h1
  linarith

end Work.BourgainPlan.IonescuWainger
