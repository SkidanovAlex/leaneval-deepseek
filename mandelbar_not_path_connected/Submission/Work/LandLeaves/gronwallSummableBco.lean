import Mathlib
import Submission.Work.LandLeaves.gronwallDefs
import Submission.Work.LandLeaves.gronwallSummable

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Summability of the `bco` (Laurent) coefficient series

`bco ψ n = iteratedDeriv n (Fext ψ) 0 / n!` is the `n`-th Taylor coefficient at the origin of
the function `Fext ψ`, the bounded holomorphic continuation of `ζ ↦ ψ (ζ⁻¹) - ζ⁻¹` to the unit
ball (`Work.LandLeaves.Fext_diff`).  Since `‖ψ w - w‖ ≤ C` for `1 < ‖w‖`, the function `Fext ψ`
is bounded by `C` on the unit ball (away from the origin it is exactly `ψ ζ⁻¹ - ζ⁻¹`), so
Cauchy's estimate applied on the circle of radius `ρ ∈ (r⁻¹, 1)` gives `‖bco ψ n‖ ≤ C ρ⁻ⁿ`,
whence

`n ‖bco ψ n‖² r^{-2n} ≤ C² n (ρ⁻² r⁻²)ⁿ`

and `ρ⁻² r⁻² = (ρ r)⁻² < 1` because `ρ r > 1`.  This is the summability of the area (Gronwall)
series in the `ψ`-language, and (with `Work.LandLeaves.gronwallParseval`) it identifies the
contour integral `Aint ψ r` with an absolutely convergent series.
-/

namespace Work.LandLeaves

/-- `bco ψ n` (the Laurent coefficient at infinity of `ψ`, from `gronwallDefs`) is the `n`-th
Taylor coefficient `gco (Fext ψ) n` of `Fext ψ` at the origin. -/
lemma bco_eq_gco (ψ : ℂ → ℂ) (n : ℕ) : bco ψ n = gco (Fext ψ) n := by
  rw [bco, gco, div_eq_mul_inv, mul_comm]

theorem gronwallSummableBco (ψ : ℂ → ℂ) (C : ℝ)
    (hd : DifferentiableOn ℂ ψ {w : ℂ | 1 < ‖w‖})
    (hb : ∀ w, 1 < ‖w‖ → ‖ψ w - w‖ ≤ C) (r : ℝ) (hr : 1 < r) :
    Summable (fun n : ℕ => (n:ℝ) * ‖bco ψ n‖^2 * (r^(2*n))⁻¹) := by
  have hr0 : 0 < r := lt_trans zero_lt_one hr
  have hrinv0 : 0 ≤ r⁻¹ := inv_nonneg.mpr hr0.le
  have hrinv1 : r⁻¹ < 1 := inv_lt_one_of_one_lt₀ hr
  -- choose `ρ` with `r⁻¹ < ρ < 1`
  set ρ : ℝ := (r⁻¹ + 1) / 2 with hρdef
  have hρgt : r⁻¹ < ρ := by rw [hρdef]; linarith
  have hρlt : ρ < 1 := by rw [hρdef]; linarith
  have hρ0 : 0 < ρ := lt_of_le_of_lt hrinv0 hρgt
  -- `Fext ψ` is holomorphic on the unit ball
  have hFd : DifferentiableOn ℂ (Fext ψ) (Metric.ball 0 1) := Fext_diff ψ C hd hb
  -- ... and bounded by `C` on the circle of radius `ρ`
  have hbound : ∀ z ∈ Metric.sphere (0:ℂ) ρ, ‖Fext ψ z‖ ≤ C := by
    intro z hz
    rw [Metric.mem_sphere, dist_zero_right] at hz
    have hzne : z ≠ 0 := by
      rintro rfl
      rw [norm_zero] at hz
      linarith
    rw [Fext_eq ψ hzne]
    refine hb z⁻¹ ?_
    rw [norm_inv, one_lt_inv₀ (norm_pos_iff.mpr hzne), hz]
    exact hρlt
  -- Cauchy's estimate
  have hbco : ∀ n : ℕ, ‖bco ψ n‖ ≤ C * (ρ⁻¹)^n := by
    intro n
    have h := norm_gco_le (Fext ψ) hFd hρ0 hρlt hbound n
    rw [div_eq_mul_inv, ← inv_pow] at h
    rwa [bco_eq_gco ψ n]
  have hsq : ∀ n : ℕ, ‖bco ψ n‖^2 ≤ C^2 * (ρ⁻¹^2)^n := by
    intro n
    calc ‖bco ψ n‖^2 ≤ (C * (ρ⁻¹)^n)^2 := pow_le_pow_left₀ (norm_nonneg _) (hbco n) 2
      _ = C^2 * (ρ⁻¹^2)^n := by rw [mul_pow, ← pow_mul, ← pow_mul]; ring_nf
  -- the geometric ratio `t = ρ⁻² r⁻² < 1`
  set t : ℝ := ρ⁻¹^2 * (r⁻¹)^2 with htdef
  have ht0 : 0 ≤ t := by rw [htdef]; positivity
  have hρr : 1 < ρ * r := by
    have h := mul_lt_mul_of_pos_right hρgt hr0
    rwa [inv_mul_cancel₀ (ne_of_gt hr0)] at h
  have ht1 : t < 1 := by
    have he : t = ((ρ * r)⁻¹)^2 := by rw [htdef, mul_inv, mul_pow]
    rw [he]
    exact pow_lt_one₀ (inv_nonneg.mpr (le_of_lt (lt_trans zero_lt_one hρr)))
      (inv_lt_one_of_one_lt₀ hρr) (by norm_num)
  -- summability of `n ↦ (n : ℝ) * t^n`
  have hgeo : Summable (fun n : ℕ => (n:ℝ) * t^n) := by
    have hbase := summable_norm_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 (r := t)
      (by rw [Real.norm_eq_abs, abs_of_nonneg ht0]; exact ht1)
    refine hbase.congr (fun n => ?_)
    rw [pow_one, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (Nat.cast_nonneg n) (pow_nonneg ht0 n))]
  -- the termwise comparison
  have hterm : ∀ n : ℕ,
      (n:ℝ) * ‖bco ψ n‖^2 * (r^(2*n))⁻¹ ≤ C^2 * ((n:ℝ) * t^n) := by
    intro n
    have hv : (r^(2*n))⁻¹ = ((r⁻¹)^2)^n := by rw [← inv_pow, ← pow_mul]
    have hX0 : 0 ≤ ((r⁻¹)^2)^n := pow_nonneg (pow_nonneg hrinv0 2) n
    rw [hv, htdef]
    calc (n:ℝ) * ‖bco ψ n‖^2 * ((r⁻¹)^2)^n
        ≤ (n:ℝ) * (C^2 * (ρ⁻¹^2)^n) * ((r⁻¹)^2)^n :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hsq n) (Nat.cast_nonneg n)) hX0
      _ = C^2 * ((n:ℝ) * (ρ⁻¹^2 * (r⁻¹)^2)^n) := by rw [mul_pow]; ring
  refine Summable.of_nonneg_of_le (f := fun n : ℕ => C^2 * ((n:ℝ) * t^n)) ?_ hterm ?_
  · intro n
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg n) (sq_nonneg _))
      (inv_nonneg.mpr (pow_pos hr0 _).le)
  · exact hgeo.mul_left (C^2)

end Work.LandLeaves
