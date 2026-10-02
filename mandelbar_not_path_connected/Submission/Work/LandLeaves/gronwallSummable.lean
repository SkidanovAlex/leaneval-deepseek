import Mathlib
import Submission.Work.LandLeaves.GronwallDefs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Summability of the Gronwall coefficient series

`Work.LandLeaves.gco U k = U^{(k)}(0)/k!` is the `k`-th Taylor coefficient of `U` at `0`
(see `GronwallDefs`).  The target

`∑_k (2k+1) ‖gco U (k+1)‖² / r^{4k+2} < ∞`  for `r > 1`

is the summability half of the area (Gronwall) theorem for the odd exterior-univalent map
`z ↦ z * U (1/z²)`:  the coefficients decay fast enough that the "area series" converges at
every level `r > 1`.

The proof is elementary once one has Cauchy's estimate for a function holomorphic on the unit
ball.  Fix `ρ` with `r⁻² < ρ < 1` and let `C` bound `‖U‖` on the circle of radius `ρ`.  Cauchy's
estimate (`Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le`) gives
`‖gco U n‖ ≤ C / ρ^n`, hence

`(2k+1) ‖gco U (k+1)‖² / r^{4k+2} ≤ C² ρ⁻² r⁻² · (2k+1) · t^k`,  `t = ρ⁻² r⁻⁴`,

and `t < 1` precisely because `ρ > r⁻²`.
-/

namespace Work.LandLeaves

/-- **Cauchy's estimate for the Taylor coefficients.**  If `U` is holomorphic on the unit ball and
`C` bounds `‖U‖` on the circle `‖z‖ = ρ` (`0 < ρ < 1`), then the `k`-th Taylor coefficient of `U`
at `0` is bounded by `C / ρ^k`. -/
lemma norm_gco_le (U : ℂ → ℂ) (hU : DifferentiableOn ℂ U (Metric.ball 0 1))
    {ρ C : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hC : ∀ z ∈ Metric.sphere (0:ℂ) ρ, ‖U z‖ ≤ C) (n : ℕ) :
    ‖gco U n‖ ≤ C / ρ ^ n := by
  have hf : DiffContOnCl ℂ U (Metric.ball (0:ℂ) ρ) := by
    refine ⟨hU.mono ?_, ?_⟩
    · intro z hz
      simp only [Metric.mem_ball, dist_zero_right] at hz ⊢
      exact lt_trans hz hρ1
    · rw [closure_ball 0 (ne_of_gt hρ0)]
      refine hU.continuousOn.mono ?_
      intro z hz
      simp only [Metric.mem_closedBall, dist_zero_right] at hz
      simp only [Metric.mem_ball, dist_zero_right]
      exact lt_of_le_of_lt hz hρ1
  have hcauchy :=
    Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (F := ℂ) n hρ0 hf hC
  rw [gco, norm_mul, norm_inv, Complex.norm_natCast]
  calc ((n.factorial : ℝ))⁻¹ * ‖iteratedDeriv n U 0‖
      ≤ ((n.factorial : ℝ))⁻¹ * ((n.factorial : ℝ) * C / ρ ^ n) :=
        mul_le_mul_of_nonneg_left hcauchy (by positivity)
    _ = C / ρ ^ n := by
        rw [mul_div_assoc, ← mul_assoc,
          inv_mul_cancel₀ (by positivity : ((n.factorial : ℝ)) ≠ 0), one_mul]

theorem gronwallSummable (U : ℂ → ℂ) (hU : DifferentiableOn ℂ U (Metric.ball 0 1))
    (r : ℝ) (hr : 1 < r) :
    Summable (fun k : ℕ => (2 * (k : ℝ) + 1) * ‖Work.LandLeaves.gco U (k + 1)‖ ^ 2 / r ^ (4 * k + 2)) := by
  have hr0 : 0 < r := lt_trans zero_lt_one hr
  have hr' : 0 ≤ r⁻¹ := inv_nonneg.mpr hr0.le
  have hrinv2 : (r^2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by nlinarith : (1:ℝ) < r^2)
  -- choose `ρ` with `r⁻² < ρ < 1`
  set ρ : ℝ := ((r^2)⁻¹ + 1)/2 with hρdef
  have hρgt : (r^2)⁻¹ < ρ := by rw [hρdef]; linarith
  have hρlt : ρ < 1 := by rw [hρdef]; linarith
  have hρ0 : 0 < ρ := lt_of_le_of_lt (inv_nonneg.mpr (sq_nonneg r)) hρgt
  have hρ' : 0 ≤ ρ⁻¹ := inv_nonneg.mpr hρ0.le
  -- a bound for `U` on the circle of radius `ρ`
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ z ∈ Metric.sphere (0:ℂ) ρ, ‖U z‖ ≤ C := by
    refine (isCompact_sphere (0:ℂ) ρ).exists_bound_of_continuousOn ?_
    refine hU.continuousOn.mono ?_
    intro z hz
    rw [Metric.mem_sphere, dist_zero_right] at hz
    rw [Metric.mem_ball, dist_zero_right, hz]
    exact hρlt
  have hgco : ∀ n, ‖gco U n‖ ≤ C * (ρ⁻¹)^n := by
    intro n
    have h := norm_gco_le U hU hρ0 hρlt hC n
    rwa [div_eq_mul_inv, ← inv_pow] at h
  -- the squared coefficient bound
  have hsq : ∀ k, ‖gco U (k+1)‖^2 ≤ C^2 * (ρ⁻¹^2)^(k+1) := by
    intro k
    have h1 := hgco (k+1)
    calc ‖gco U (k+1)‖^2 ≤ (C * ρ⁻¹^(k+1))^2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ = C^2 * (ρ⁻¹^2)^(k+1) := by rw [mul_pow, ← pow_mul, ← pow_mul]; ring_nf
  have hv : ∀ k, (r^(4*k+2))⁻¹ = ((r⁻¹)^4)^k * (r⁻¹)^2 := by
    intro k; rw [← inv_pow, pow_add, ← pow_mul]
  -- the geometric ratio `t = ρ⁻² r⁻⁴ < 1`
  have ht0 : 0 ≤ ρ⁻¹^2 * (r⁻¹)^4 := mul_nonneg (pow_nonneg hρ' 2) (pow_nonneg hr' 4)
  have hρr : 1 < ρ * r^2 := by
    have := mul_lt_mul_of_pos_right hρgt (pow_pos hr0 2)
    rwa [inv_mul_cancel₀ (ne_of_gt (pow_pos hr0 2))] at this
  have ht1 : ρ⁻¹^2 * (r⁻¹)^4 < 1 := by
    have he : ρ⁻¹^2 * (r⁻¹)^4 = ((ρ * r^2)⁻¹)^2 := by
      conv_rhs => rw [mul_inv, ← inv_pow, mul_pow, ← pow_mul]
    rw [he]
    exact pow_lt_one₀ (le_of_lt (inv_pos_of_pos (lt_trans zero_lt_one hρr)))
      (inv_lt_one_of_one_lt₀ hρr) (by norm_num)
  -- `∑ (2k+1) t^k` converges
  have hgeom : Summable (fun k : ℕ => (2*(k:ℝ)+1) * (ρ⁻¹^2 * (r⁻¹)^4)^k) := by
    have h1 : Summable (fun k : ℕ => (k:ℝ) * (ρ⁻¹^2 * (r⁻¹)^4)^k) := by
      have hbase := summable_norm_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1
        (r := ρ⁻¹^2 * (r⁻¹)^4) (by rw [Real.norm_eq_abs, abs_of_nonneg ht0]; exact ht1)
      refine hbase.congr (fun n => ?_)
      rw [pow_one, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (Nat.cast_nonneg n) (pow_nonneg ht0 n))]
    refine ((h1.mul_left 2).add (summable_geometric_of_lt_one ht0 ht1)).congr (fun k => ?_)
    ring
  -- the termwise comparison
  have hterm : ∀ k : ℕ,
      (2*(k:ℝ)+1) * ‖gco U (k+1)‖^2 / r^(4*k+2)
        ≤ C^2 * (ρ⁻¹^2) * (r⁻¹)^2 * ((2*(k:ℝ)+1) * (ρ⁻¹^2 * (r⁻¹)^4)^k) := by
    intro k
    rw [div_eq_mul_inv, hv k]
    calc (2*(k:ℝ)+1) * ‖gco U (k+1)‖^2 * (((r⁻¹)^4)^k * (r⁻¹)^2)
        ≤ (2*(k:ℝ)+1) * (C^2 * (ρ⁻¹^2)^(k+1)) * (((r⁻¹)^4)^k * (r⁻¹)^2) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hsq k) (by positivity))
            (mul_nonneg (pow_nonneg (pow_nonneg hr' 4) k) (pow_nonneg hr' 2))
      _ = C^2 * (ρ⁻¹^2) * (r⁻¹)^2 * ((2*(k:ℝ)+1) * (ρ⁻¹^2 * (r⁻¹)^4)^k) := by
          rw [pow_succ, mul_pow]; ring
  refine Summable.of_nonneg_of_le (f := fun k : ℕ =>
      C^2 * (ρ⁻¹^2) * (r⁻¹)^2 * ((2*(k:ℝ)+1) * (ρ⁻¹^2 * (r⁻¹)^4)^k)) ?_ hterm ?_
  · intro k
    exact div_nonneg (mul_nonneg (by positivity) (sq_nonneg _)) (pow_pos hr0 _).le
  · exact hgeom.mul_left (C^2 * (ρ⁻¹^2) * (r⁻¹)^2)

end Work.LandLeaves
