import Mathlib
import Submission.Work.Mostow.surjDefs

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory Metric

/-- Pointwise bound for the Poisson density.  For `θ ∈ Sph n` (so `θ` is a boundary point) with
`ε ≤ ‖θ - ξ‖` and `‖kappa u - ξ‖ ≤ ε / 2`, the density of `visual n u` with respect to `sigma n`
at `θ` is at most `((1 - ‖kappa u‖²)/(ε/2)²)^(n-1)`.

This is the chart identity `tpart u - ⟪u,θ⟫ = ‖kappa u - θ‖²/(1 - ‖kappa u‖²)` of
`Submission.Work.Mostow.surjDefs` (`busemann_kappaInv`, `kappaInv_kappa`) together with the triangle
inequality `ε/2 ≤ ‖kappa u - θ‖`. -/
theorem visual_density_le (n : ℕ) (hn : 1 ≤ n) (u θ ξ : E n) (hθ : θ ∈ Sph n)
    {ε : ℝ} (hε : 0 < ε) (hκ : ‖kappa u - ξ‖ ≤ ε / 2) (hfar : ε ≤ ‖θ - ξ‖) :
    Real.exp (-((n : ℝ) - 1) * busemann θ u) ≤
      ((1 - ‖kappa u‖ ^ 2) / (ε / 2) ^ 2) ^ (n - 1) := by
  have hb : ‖kappa u‖ < 1 := norm_kappa_lt_one u
  have hbpos : (0 : ℝ) < 1 - ‖kappa u‖ ^ 2 := by nlinarith [norm_nonneg (kappa u)]
  have hθnorm : ‖θ‖ = 1 := by
    rw [Sph, Metric.mem_sphere, dist_eq_norm, sub_zero] at hθ
    simpa using hθ
  have hbθ : (0 : ℝ) < ‖kappa u - θ‖ := by
    refine norm_pos_iff.mpr (sub_ne_zero.mpr ?_)
    intro h
    rw [h, hθnorm] at hb
    exact lt_irrefl _ hb
  have hbus : busemann θ u = 2 * Real.log ‖kappa u - θ‖ - Real.log (1 - ‖kappa u‖ ^ 2) := by
    simpa [kappaInv_kappa u] using busemann_kappaInv (kappa u) θ hb hθ
  set X : ℝ := (1 - ‖kappa u‖ ^ 2) / ‖kappa u - θ‖ ^ 2 with hXdef
  have hXpos : (0 : ℝ) < X := by rw [hXdef]; positivity
  have hlogX : -busemann θ u = Real.log X := by
    rw [hbus, hXdef, Real.log_div (ne_of_gt hbpos) (pow_ne_zero 2 (ne_of_gt hbθ)), Real.log_pow]
    ring
  have hlogX' : busemann θ u = -Real.log X := by rw [← hlogX]; ring
  have hkey : Real.exp (-((n : ℝ) - 1) * busemann θ u) = X ^ (n - 1) := by
    calc Real.exp (-((n : ℝ) - 1) * busemann θ u)
        = Real.exp (-((n : ℝ) - 1) * (-Real.log X)) := by rw [hlogX']
      _ = Real.exp (((n - 1 : ℕ) : ℝ) * Real.log X) := by
            rw [Nat.cast_sub hn]; congr 1; ring
      _ = (Real.exp (Real.log X)) ^ (n - 1) := Real.exp_nat_mul (Real.log X) (n - 1)
      _ = X ^ (n - 1) := by rw [Real.exp_log hXpos]
  rw [hkey]
  have hε2 : (0 : ℝ) < (ε / 2) ^ 2 := by positivity
  have hfar2 : (ε / 2) ≤ ‖kappa u - θ‖ := by
    have h1 : ‖θ - ξ‖ - ‖kappa u - ξ‖ ≤ ‖kappa u - θ‖ := by
      have h := norm_sub_norm_le (θ - ξ) (kappa u - ξ)
      rwa [show (θ - ξ) - (kappa u - ξ) = -(kappa u - θ) by abel, norm_neg] at h
    linarith
  have hXle : X ≤ (1 - ‖kappa u‖ ^ 2) / (ε / 2) ^ 2 := by
    rw [hXdef]
    exact div_le_div_of_nonneg_left (le_of_lt hbpos) hε2 (pow_le_pow_left₀ (by positivity) hfar2 2)
  exact pow_le_pow_left₀ (le_of_lt hXpos) hXle (n - 1)

/-- The visual measure seen from the base point `0` is `sigma n`
(the Poisson density is identically `1` there, since `busemann ξ 0 = 0`). -/
theorem visual_zero (n : ℕ) : visual n (0 : E n) = sigma n := by
  simp [visual, busemann, tpart]

/-- Concentration of the visual (Poisson) measure: if `κ u` is within `ε/2` of a boundary point
`ξ ∈ Sph n` then the visual measure seen from `u` gives mass at most
`((1 - ‖κ u‖²)/(ε/2)²)^(n-1)` to the complement of the `ε`-ball around `ξ`.

Here `kappa u = u/(1 + tpart u)` is the Poincaré-ball chart (`Submission.Work.Mostow.surjDefs`),
`visual n u = (sigma n).withDensity (ξ ↦ ofReal (exp (-((n:ℝ)-1) * busemann ξ u)))` and
`VisualProp n` is the area hypothesis from `Submission.Mostow.Interfaces`, which in particular makes
`sigma n = visual n 0` a probability measure.

Why it is true: for `θ ∈ Sph n`, `tpart u - ⟪u,θ⟫ = ‖κ u - θ‖²/(1 - ‖κ u‖²)` (the chart identity,
provable from `busemann_kappaInv`/`kappa_kappaInv` in `surjDefs`), and the density of `visual n u`
with respect to `sigma n` at `θ` is `(tpart u - ⟪u,θ⟫)^{-(n-1)}`. On the complement of the
`ε`-ball around `ξ` one has `‖κ u - θ‖ ≥ ε/2`, so the density is everywhere bounded by
`((1 - ‖κ u‖²)/(ε/2)²)^(n-1)`, and the measure of that complement is at most `1`. -/
theorem visualConcentration (n : ℕ) (hV : VisualProp n) (u : E n) (ξ : E n) (hξ : ξ ∈ Sph n)
    {ε : ℝ} (hε : 0 < ε) (hκ : ‖kappa u - ξ‖ ≤ ε / 2) :
    visual n u ((Metric.ball ξ ε)ᶜ) ≤
      ENNReal.ofReal (((1 - ‖kappa u‖ ^ 2) / (ε / 2) ^ 2) ^ (n - 1)) := by
  by_cases hn : n ≤ 1
  · -- `n ≤ 1`: the exponent `n - 1` is `0`, so the bound is the trivial `≤ 1`
    have hprob : IsProbabilityMeasure (visual n u) := (hV u).1
    have hle : visual n u (Metric.ball ξ ε)ᶜ ≤ 1 := by
      rw [← measure_univ (μ := visual n u)]
      exact measure_mono (Set.subset_univ _)
    have h1 : (n - 1 : ℕ) = 0 := by omega
    rw [h1, pow_zero, ENNReal.ofReal_one]
    exact hle
  · have hn1 : 1 ≤ n := by omega
    -- `sigma n = visual n 0` is a probability measure, carried by the sphere
    have hvis0 : visual n (0 : E n) = sigma n := visual_zero n
    have hσprob : IsProbabilityMeasure (sigma n) := by rw [← hvis0]; exact (hV 0).1
    have hσsupp : sigma n (Sph n)ᶜ = 0 := by rw [← hvis0]; exact (hV 0).2.1
    set s := (Metric.ball ξ ε)ᶜ with hsdef
    have hmeas : MeasurableSet s := Metric.isOpen_ball.measurableSet.compl
    -- `sigma n` is carried by the sphere
    have hsp : ∀ᵐ θ ∂(sigma n), θ ∈ Sph n := by
      rw [MeasureTheory.ae_iff]
      exact hσsupp
    -- the pointwise bound for the Poisson density on `s`
    have hpoint : ∀ θ, θ ∈ Sph n → ε ≤ ‖θ - ξ‖ →
        ENNReal.ofReal (Real.exp (-((n : ℝ) - 1) * busemann θ u)) ≤
          ENNReal.ofReal (((1 - ‖kappa u‖ ^ 2) / (ε / 2) ^ 2) ^ (n - 1)) := by
      intro θ hθ hfar
      exact ENNReal.ofReal_le_ofReal (visual_density_le n hn1 u θ ξ hθ hε hκ hfar)
    -- ... hence `sigma n`-a.e. on `s`
    have hbound : ∀ᵐ θ ∂(sigma n).restrict s,
        ENNReal.ofReal (Real.exp (-((n : ℝ) - 1) * busemann θ u)) ≤
          ENNReal.ofReal (((1 - ‖kappa u‖ ^ 2) / (ε / 2) ^ 2) ^ (n - 1)) := by
      have h1 : ∀ᵐ θ ∂(sigma n), θ ∈ s →
          ENNReal.ofReal (Real.exp (-((n : ℝ) - 1) * busemann θ u)) ≤
            ENNReal.ofReal (((1 - ‖kappa u‖ ^ 2) / (ε / 2) ^ 2) ^ (n - 1)) := by
        filter_upwards [hsp] with θ hθ
        intro hmem
        have hdist : ε ≤ ‖θ - ξ‖ := by
          have hlt : ¬ dist θ ξ < ε := by
            simpa [s, Metric.mem_ball] using hmem
          have := not_lt.mp hlt
          simpa [dist_eq_norm] using this
        exact hpoint θ hθ hdist
      have h2 : ∀ᵐ θ ∂(sigma n).restrict s, θ ∈ s →
          ENNReal.ofReal (Real.exp (-((n : ℝ) - 1) * busemann θ u)) ≤
            ENNReal.ofReal (((1 - ‖kappa u‖ ^ 2) / (ε / 2) ^ 2) ^ (n - 1)) :=
        ae_mono (Measure.restrict_le_self (s := s)) h1
      exact (ae_restrict_mem hmeas).mp h2
    rw [visual, MeasureTheory.withDensity_apply _ hmeas]
    calc ∫⁻ θ in s, ENNReal.ofReal (Real.exp (-((n : ℝ) - 1) * busemann θ u)) ∂(sigma n)
        = ∫⁻ θ, ENNReal.ofReal (Real.exp (-((n : ℝ) - 1) * busemann θ u)) ∂(sigma n).restrict s :=
          rfl
      _ ≤ ∫⁻ θ, ENNReal.ofReal (((1 - ‖kappa u‖ ^ 2) / (ε / 2) ^ 2) ^ (n - 1))
            ∂(sigma n).restrict s :=
          lintegral_mono_ae hbound
      _ = ENNReal.ofReal (((1 - ‖kappa u‖ ^ 2) / (ε / 2) ^ 2) ^ (n - 1)) * (sigma n) s :=
          setLIntegral_const _ _
      _ ≤ ENNReal.ofReal (((1 - ‖kappa u‖ ^ 2) / (ε / 2) ^ 2) ^ (n - 1)) * 1 := by
          gcongr
          calc (sigma n) s ≤ (sigma n) Set.univ := measure_mono (Set.subset_univ _)
            _ = 1 := measure_univ
      _ = ENNReal.ofReal (((1 - ‖kappa u‖ ^ 2) / (ε / 2) ^ 2) ^ (n - 1)) := mul_one _

end Work.Mostow
