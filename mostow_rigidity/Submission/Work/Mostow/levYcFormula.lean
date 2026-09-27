import Mathlib
import Submission.Work.Mostow.QIDefs
import Submission.Work.Mostow.BdExt.lawCosines

/-!
# The horospherical (level, flat-coordinate) form of the hyperbolic distance

At a boundary point `ξ ∈ Sph n` a point `u : E n` of the chart model carries two pieces of data:

* its *level* `L ξ u = tpart u - ⟪u,ξ⟫ = exp (busemann ξ u)`, and
* its *normalised flat coordinate* `yc ξ u = (L ξ u)⁻¹ • wc ξ u`, where `wc ξ u = u - ⟪u,ξ⟫ • ξ`
  is the component of `u` in `ξ^⊥`.

The main theorem of this file is the classical formula expressing the hyperbolic distance of
`u` and `v` in these horospherical coordinates at `ξ`:

`cosh (hdist u v) = cosh (log (L ξ u / L ξ v)) + (L ξ u * L ξ v / 2) * ‖yc ξ u - yc ξ v‖²`.

Its content is that the horosphere of `ξ` is flat: at a *common* level the formula reduces to
`cosh (hdist u v) = 1 + (L²/2) ‖yc ξ u - yc ξ v‖²`, the Euclidean law
`‖y_u - y_v‖² = 2 (cosh d - 1) / L²`, and the general case is that rescaled by the level ratio.

## Proof

Everything is a computation in the hyperboloid chart, built on the law of cosines
`cosh (hdist u v) = tpart u * tpart v - ⟪u,v⟫` (`Work.Mostow.BdExt.cosh_hdist`).

Write `L_u = lev ξ u`, `T_u = tpart u`, `a_u = ⟪u,ξ⟫`, `w_u = wc ξ u`.  Since `‖ξ‖ = 1`,

* `⟪w_u, w_v⟫ = ⟪u,v⟫ - a_u a_v`  (`inner_wc`), and
* `1 + ‖w_u‖² = L_u (T_u + a_u)`  (`one_add_norm_wc_sq`; equivalently `T_u² - a_u² = (T_u-a_u)(T_u+a_u)`).

Consequently, expanding `‖L_v w_u - L_u w_v‖²` and completing the square gives
`‖L_v • w_u - L_u • w_v‖² = 2 L_u L_v (T_u T_v - ⟪u,v⟫) - L_u² - L_v²`
(`norm_smul_wc_sub_sq`).  On the other hand `L_u L_v • (yc ξ u - yc ξ v) = L_v • w_u - L_u • w_v`
(`lev_smul_yc_sub`), so
`(L_u L_v)² ‖yc ξ u - yc ξ v‖² = ‖L_v • w_u - L_u • w_v‖²` (`lev_sq_norm_yc_sub`).
Finally `cosh (log (L_u / L_v)) = (L_u/L_v + L_v/L_u)/2` (`Real.cosh_log`, `lev_pos`), and
`(L_u/L_v + L_v/L_u)/2 + (L_u L_v/2) · Z/(L_uL_v)² = T_uT_v - ⟪u,v⟫` when
`Z = 2L_uL_v(T_uT_v - ⟪u,v⟫) - L_u² - L_v²`: pure clearing of denominators.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

variable {n : ℕ}

/-- The `ξ^⊥`-components inherit the scalar product, up to the product of the two levels'
`ξ`-coordinates: `⟪wc ξ u, wc ξ v⟫ = ⟪u,v⟫ - ⟪u,ξ⟫ ⟪v,ξ⟫` for `ξ` on the unit sphere. -/
lemma inner_wc {ξ : E n} (hξ : ξ ∈ Sph n) (u v : E n) :
    inner ℝ (wc ξ u) (wc ξ v) = inner ℝ u v - inner ℝ u ξ * inner ℝ v ξ := by
  have hξ1 : inner ℝ ξ ξ = 1 := by
    rw [real_inner_self_eq_norm_sq]
    have h : ‖ξ‖ = 1 := by simpa [Sph, Metric.mem_sphere, dist_eq_norm] using hξ
    rw [h]; norm_num
  have hv : inner ℝ ξ v = inner ℝ v ξ := (real_inner_comm ξ v).symm
  simp only [wc, inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
    hv, hξ1]
  ring

/-- The flat coordinate and the level determine the norm of the `ξ^⊥`-component:
`1 + ‖wc ξ u‖² = lev ξ u * (tpart u + ⟪u,ξ⟫)`, i.e. `tpart u² - ⟪u,ξ⟫² = (tpart u - ⟪u,ξ⟫)(tpart u + ⟪u,ξ⟫)`. -/
lemma one_add_norm_wc_sq {ξ : E n} (hξ : ξ ∈ Sph n) (u : E n) :
    1 + ‖wc ξ u‖ ^ 2 = lev ξ u * (tpart u + inner ℝ u ξ) := by
  have hw : ‖wc ξ u‖ ^ 2 = ‖u‖ ^ 2 - (inner ℝ u ξ) ^ 2 := by
    have h := inner_wc hξ u u
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
    rw [h]; ring
  have ht : tpart u ^ 2 = 1 + ‖u‖ ^ 2 := by rw [tpart, Real.sq_sqrt (by positivity)]
  rw [hw, lev]
  nlinarith [ht]

/-- The hyperbolic law of cosines in horospherical coordinates at `ξ`, in the norm of the
difference of the (un-normalised) `ξ^⊥`-coordinates:
`‖L_v w_u - L_u w_v‖² = 2 L_u L_v cosh (hdist u v) - L_u² - L_v²`, written with the arcosh
argument `tpart u * tpart v - ⟪u,v⟫` instead of `cosh (hdist u v)`. -/
lemma norm_smul_wc_sub_sq {ξ : E n} (hξ : ξ ∈ Sph n) (u v : E n) :
    ‖lev ξ v • wc ξ u - lev ξ u • wc ξ v‖ ^ 2 =
      2 * lev ξ u * lev ξ v * (tpart u * tpart v - inner ℝ u v)
        - (lev ξ u) ^ 2 - (lev ξ v) ^ 2 := by
  have hU := inner_wc hξ u v
  have hu := one_add_norm_wc_sq hξ u
  have hv := one_add_norm_wc_sq hξ v
  have hu' : ‖wc ξ u‖ ^ 2 = lev ξ u * (tpart u + inner ℝ u ξ) - 1 := by linarith
  have hv' : ‖wc ξ v‖ ^ 2 = lev ξ v * (tpart v + inner ℝ v ξ) - 1 := by linarith
  have h1 : ‖lev ξ v • wc ξ u‖ ^ 2 = (lev ξ v) ^ 2 * ‖wc ξ u‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have h2 : ‖lev ξ u • wc ξ v‖ ^ 2 = (lev ξ u) ^ 2 * ‖wc ξ v‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have h3 : inner ℝ (lev ξ v • wc ξ u) (lev ξ u • wc ξ v)
      = lev ξ v * lev ξ u * inner ℝ (wc ξ u) (wc ξ v) := by
    rw [real_inner_smul_left, real_inner_smul_right]; ring
  rw [norm_sub_sq_real, h1, h2, h3, hU, hu', hv', lev, lev]
  ring

/-- The normalised flat coordinate is the `ξ^⊥`-coordinate divided by the level, so multiplying
the difference of two flat coordinates by the product of the levels clears the denominators. -/
lemma lev_smul_yc_sub {ξ : E n} (hξ : ξ ∈ Sph n) (u v : E n) :
    (lev ξ u * lev ξ v) • (yc ξ u - yc ξ v) = lev ξ v • wc ξ u - lev ξ u • wc ξ v := by
  have hLu : lev ξ u ≠ 0 := ne_of_gt (lev_pos ξ hξ u)
  have hLv : lev ξ v ≠ 0 := ne_of_gt (lev_pos ξ hξ v)
  have hsc1 : lev ξ u * lev ξ v * (lev ξ u)⁻¹ = lev ξ v := by
    rw [mul_comm (lev ξ u) (lev ξ v), mul_inv_cancel_right₀ hLu]
  have hsc2 : lev ξ u * lev ξ v * (lev ξ v)⁻¹ = lev ξ u := by
    rw [mul_inv_cancel_right₀ hLv]
  rw [yc, yc, smul_sub, smul_smul, smul_smul, hsc1, hsc2]

/-- Square of the previous identity: the squared Euclidean distance of two flat coordinates is
the squared norm of the `ξ^⊥`-difference, rescaled by `(L_u L_v)²`. -/
lemma lev_sq_norm_yc_sub {ξ : E n} (hξ : ξ ∈ Sph n) (u v : E n) :
    (lev ξ u * lev ξ v) ^ 2 * ‖yc ξ u - yc ξ v‖ ^ 2 =
      ‖lev ξ v • wc ξ u - lev ξ u • wc ξ v‖ ^ 2 := by
  have h := lev_smul_yc_sub hξ u v
  have hnorm : ‖(lev ξ u * lev ξ v) • (yc ξ u - yc ξ v)‖ ^ 2
      = (lev ξ u * lev ξ v) ^ 2 * ‖yc ξ u - yc ξ v‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [← hnorm, h]

/-- **The horospherical form of the hyperbolic distance.**  For `ξ` on the boundary sphere and
any two points `u`, `v` of `ℍⁿ`,
`cosh (hdist u v) = cosh (log (lev ξ u / lev ξ v)) + (lev ξ u * lev ξ v / 2) ‖yc ξ u - yc ξ v‖²`.
At a common level `L := lev ξ u = lev ξ v` this is the flatness of the horosphere:
`cosh (hdist u v) = 1 + (L²/2) ‖yc ξ u - yc ξ v‖²`. -/
theorem levYcFormula {n : ℕ} {ξ : Submission.Mostow.E n} (hξ : ξ ∈ Submission.Mostow.Sph n)
    (u v : Submission.Mostow.E n) :
    Real.cosh (Submission.Mostow.hdist u v) =
      Real.cosh (Real.log (Work.Mostow.lev ξ u / Work.Mostow.lev ξ v)) +
      (Work.Mostow.lev ξ u * Work.Mostow.lev ξ v / 2) *
        ‖Work.Mostow.yc ξ u - Work.Mostow.yc ξ v‖ ^ 2 := by
  have hLu : lev ξ u ≠ 0 := ne_of_gt (lev_pos ξ hξ u)
  have hLv : lev ξ v ≠ 0 := ne_of_gt (lev_pos ξ hξ v)
  have hY := lev_sq_norm_yc_sub hξ u v
  have hZ := norm_smul_wc_sub_sq hξ u v
  have hsq : (lev ξ u * lev ξ v) ^ 2 ≠ 0 := pow_ne_zero 2 (mul_ne_zero hLu hLv)
  have hYdiv : ‖yc ξ u - yc ξ v‖ ^ 2 =
      ‖lev ξ v • wc ξ u - lev ξ u • wc ξ v‖ ^ 2 / (lev ξ u * lev ξ v) ^ 2 := by
    rw [eq_div_iff hsq, mul_comm, hY]
  rw [Work.Mostow.BdExt.cosh_hdist u v,
    Real.cosh_log (div_pos (lev_pos ξ hξ u) (lev_pos ξ hξ v)), hYdiv, hZ]
  field_simp
  ring

end Work.Mostow
