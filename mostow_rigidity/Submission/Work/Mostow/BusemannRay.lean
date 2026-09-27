import Mathlib
import Submission.Work.Mostow.BaryBase

/-!
# The Busemann function as the limit along a geodesic ray

For `ξ ∈ Sph n` (the boundary sphere of `ℍⁿ` in the chart `E n`) the geodesic ray issued from
the base point `0` towards `ξ` is `t ↦ sinh t • ξ`.  The Busemann function of `ξ` is the
normalised limit of the distance to that ray:

`hdist u (sinh t • ξ) - t → busemann ξ u` as `t → ∞`.

The proof is the explicit computation.  With `p = tpart u`, `a = ⟪u, ξ⟫` one has
`cosh (hdist u (sinh t • ξ)) = p cosh t - a sinh t =: X t`, hence
`exp (hdist u (sinh t • ξ) - t) = e^{-t} (X t + √(X t² - 1))`, and since
`e^{-t} X t → (p - a)/2` while `e^{-t} √(X t² - 1) = √((e^{-t} X t)² - e^{-2t}) → (p - a)/2`,
the exponential tends to `p - a = exp (busemann ξ u) > 0`.  Taking logarithms gives the claim.
-/

namespace Work.Mostow

open Submission.Mostow

variable {n : ℕ}

/-- The `t`-coordinate of the point `sinh t • ξ` of the ray towards a unit vector `ξ`. -/
theorem tpart_sinh_smul (ξ : E n) (t : ℝ) (hξ : ‖ξ‖ = 1) :
    tpart (Real.sinh t • ξ) = Real.cosh t := by
  rw [tpart, norm_smul, Real.norm_eq_abs, hξ, mul_one, sq_abs, ← Real.cosh_sq']
  exact Real.sqrt_sq (le_of_lt (Real.cosh_pos t))

/-- `e^{-t} cosh t = (1 + e^{-2t})/2`. -/
theorem exp_neg_mul_cosh (t : ℝ) :
    Real.exp (-t) * Real.cosh t = (1 + Real.exp (-(2 * t))) / 2 := by
  have h1 : Real.exp (-t) * Real.exp t = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have h2 : Real.exp (-t) * Real.exp (-t) = Real.exp (-(2 * t)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [Real.cosh_eq,
    show Real.exp (-t) * ((Real.exp t + Real.exp (-t)) / 2) =
      (Real.exp (-t) * Real.exp t + Real.exp (-t) * Real.exp (-t)) / 2 by ring,
    h1, h2]

/-- `e^{-t} sinh t = (1 - e^{-2t})/2`. -/
theorem exp_neg_mul_sinh (t : ℝ) :
    Real.exp (-t) * Real.sinh t = (1 - Real.exp (-(2 * t))) / 2 := by
  have h1 : Real.exp (-t) * Real.exp t = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have h2 : Real.exp (-t) * Real.exp (-t) = Real.exp (-(2 * t)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [Real.sinh_eq,
    show Real.exp (-t) * ((Real.exp t - Real.exp (-t)) / 2) =
      (Real.exp (-t) * Real.exp t - Real.exp (-t) * Real.exp (-t)) / 2 by ring,
    h1, h2]

/-- `e^{-2t} → 0` at `+∞`. -/
theorem tendsto_exp_neg_two_mul :
    Filter.Tendsto (fun t : ℝ => Real.exp (-(2 * t))) Filter.atTop (nhds 0) :=
  Real.tendsto_exp_neg_atTop_nhds_zero.comp
    (Filter.tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))

/-- The exponential of the Busemann function is the limit of `exp (hdist u (sinh t • ξ) - t)`. -/
theorem tendsto_exp_hdist_ray (ξ : E n) (hξ : ξ ∈ Sph n) (u : E n) :
    Filter.Tendsto (fun t : ℝ => Real.exp (hdist u (Real.sinh t • ξ) - t)) Filter.atTop
      (nhds (tpart u - inner ℝ u ξ)) := by
  have hξn : ‖ξ‖ = 1 := (mem_Sph_iff ξ).mp hξ
  set p : ℝ := tpart u with hp
  set a : ℝ := inner ℝ u ξ with ha
  have hL : 0 < p - a := by
    rw [hp, ha]; exact busemann_arg_pos ξ hξ u
  have hX1 : ∀ t : ℝ, 1 ≤ p * Real.cosh t - a * Real.sinh t := by
    intro t
    have h := one_le_cosh_hdist u (Real.sinh t • ξ)
    rw [tpart_sinh_smul ξ t hξn, real_inner_smul_right] at h
    rw [hp, ha]
    rw [mul_comm (inner ℝ u ξ) (Real.sinh t)]
    exact h
  have hX : ∀ t : ℝ,
      hdist u (Real.sinh t • ξ) = Real.arcosh (p * Real.cosh t - a * Real.sinh t) := by
    intro t
    rw [hdist, hp, ha, tpart_sinh_smul ξ t hξn, real_inner_smul_right]
    congr 1
    ring
  have hexp : ∀ t : ℝ, Real.exp (hdist u (Real.sinh t • ξ) - t)
      = Real.exp (-t) * ((p * Real.cosh t - a * Real.sinh t)
          + Real.sqrt ((p * Real.cosh t - a * Real.sinh t) ^ 2 - 1)) := by
    intro t
    rw [hX t, Real.exp_sub, Real.exp_arcosh (hX1 t), Real.exp_neg]
    ring
  have hc : Filter.Tendsto (fun t : ℝ => Real.exp (-t) * Real.cosh t) Filter.atTop
      (nhds (1 / 2)) := by
    have hbase : Filter.Tendsto (fun t : ℝ => (1 + Real.exp (-(2 * t))) / 2) Filter.atTop
        (nhds ((1 + 0) / 2)) :=
      (tendsto_const_nhds.add tendsto_exp_neg_two_mul).div_const 2
    have hbase' : Filter.Tendsto (fun t : ℝ => (1 + Real.exp (-(2 * t))) / 2) Filter.atTop
        (nhds (1 / 2)) := by simpa using hbase
    exact Filter.Tendsto.congr (fun t => (exp_neg_mul_cosh t).symm) hbase'
  have hs : Filter.Tendsto (fun t : ℝ => Real.exp (-t) * Real.sinh t) Filter.atTop
      (nhds (1 / 2)) := by
    have hbase : Filter.Tendsto (fun t : ℝ => (1 - Real.exp (-(2 * t))) / 2) Filter.atTop
        (nhds ((1 - 0) / 2)) :=
      (tendsto_const_nhds.sub tendsto_exp_neg_two_mul).div_const 2
    have hbase' : Filter.Tendsto (fun t : ℝ => (1 - Real.exp (-(2 * t))) / 2) Filter.atTop
        (nhds (1 / 2)) := by simpa using hbase
    exact Filter.Tendsto.congr (fun t => (exp_neg_mul_sinh t).symm) hbase'
  have hG : Filter.Tendsto (fun t : ℝ => Real.exp (-t) * (p * Real.cosh t - a * Real.sinh t))
      Filter.atTop (nhds ((p - a) / 2)) := by
    have hmain : Filter.Tendsto
        (fun t : ℝ => p * (Real.exp (-t) * Real.cosh t) - a * (Real.exp (-t) * Real.sinh t))
        Filter.atTop (nhds (p * (1 / 2) - a * (1 / 2))) := (hc.const_mul p).sub (hs.const_mul a)
    rw [show p * (1 / 2) - a * (1 / 2) = (p - a) / 2 by ring] at hmain
    rw [show (fun t : ℝ => p * (Real.exp (-t) * Real.cosh t) - a * (Real.exp (-t) * Real.sinh t))
        = fun t : ℝ => Real.exp (-t) * (p * Real.cosh t - a * Real.sinh t) by
      funext t; ring] at hmain
    exact hmain
  have hH : Filter.Tendsto
      (fun t : ℝ => Real.exp (-t) * Real.sqrt ((p * Real.cosh t - a * Real.sinh t) ^ 2 - 1))
      Filter.atTop (nhds ((p - a) / 2)) := by
    have heq : (fun t : ℝ =>
          Real.exp (-t) * Real.sqrt ((p * Real.cosh t - a * Real.sinh t) ^ 2 - 1))
        = fun t : ℝ => Real.sqrt ((Real.exp (-t) * (p * Real.cosh t - a * Real.sinh t)) ^ 2
            - Real.exp (-(2 * t))) := by
      funext t
      have hsq : Real.exp (-t) ^ 2 = Real.exp (-(2 * t)) := by
        rw [pow_two, ← Real.exp_add]
        congr 1
        ring
      calc Real.exp (-t) * Real.sqrt ((p * Real.cosh t - a * Real.sinh t) ^ 2 - 1)
          = Real.sqrt (Real.exp (-t) ^ 2)
              * Real.sqrt ((p * Real.cosh t - a * Real.sinh t) ^ 2 - 1) := by
            rw [Real.sqrt_sq (le_of_lt (Real.exp_pos (-t)))]
        _ = Real.sqrt (Real.exp (-t) ^ 2
              * ((p * Real.cosh t - a * Real.sinh t) ^ 2 - 1)) := by
            rw [Real.sqrt_mul (sq_nonneg (Real.exp (-t)))]
        _ = Real.sqrt ((Real.exp (-t) * (p * Real.cosh t - a * Real.sinh t)) ^ 2
              - Real.exp (-(2 * t))) := by
            congr 1
            rw [← hsq]
            ring
    have hsub : Filter.Tendsto
        (fun t : ℝ => (Real.exp (-t) * (p * Real.cosh t - a * Real.sinh t)) ^ 2
          - Real.exp (-(2 * t))) Filter.atTop (nhds (((p - a) / 2) ^ 2)) := by
      have h2 := (hG.pow 2).sub tendsto_exp_neg_two_mul
      simpa using h2
    have hsqrt := hsub.sqrt
    rw [show Real.sqrt (((p - a) / 2) ^ 2) = (p - a) / 2 by
      rw [Real.sqrt_sq_eq_abs, abs_of_pos (half_pos hL)]] at hsqrt
    rw [heq]
    exact hsqrt
  have hsum : Filter.Tendsto (fun t : ℝ => Real.exp (-t) * (p * Real.cosh t - a * Real.sinh t)
        + Real.exp (-t) * Real.sqrt ((p * Real.cosh t - a * Real.sinh t) ^ 2 - 1))
      Filter.atTop (nhds ((p - a) / 2 + (p - a) / 2)) := hG.add hH
  rw [show (p - a) / 2 + (p - a) / 2 = p - a by ring] at hsum
  rw [show (fun t : ℝ => Real.exp (hdist u (Real.sinh t • ξ) - t))
      = fun t : ℝ => Real.exp (-t) * (p * Real.cosh t - a * Real.sinh t)
          + Real.exp (-t) * Real.sqrt ((p * Real.cosh t - a * Real.sinh t) ^ 2 - 1) by
    funext t; rw [hexp t]; ring]
  exact hsum

theorem BusemannRay (n : ℕ) (ξ : Submission.Mostow.E n) (hξ : ξ ∈ Submission.Mostow.Sph n) (u : Submission.Mostow.E n) :
    Filter.Tendsto (fun t : ℝ => Submission.Mostow.hdist u (Real.sinh t • ξ) - t) Filter.atTop (nhds (Submission.Mostow.busemann ξ u)) := by
  have h := tendsto_exp_hdist_ray (n := n) ξ hξ u
  have h2 := h.log (ne_of_gt (busemann_arg_pos ξ hξ u))
  have heq : (fun t : ℝ => Real.log (Real.exp (hdist u (Real.sinh t • ξ) - t)))
      = fun t : ℝ => hdist u (Real.sinh t • ξ) - t := by
    funext t; exact Real.log_exp _
  rw [heq] at h2
  rw [busemann_eq_log]
  exact h2

end Work.Mostow
