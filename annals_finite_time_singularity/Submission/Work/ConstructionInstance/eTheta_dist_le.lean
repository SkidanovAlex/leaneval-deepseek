import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.ConstructionInstance.AuxOmegaStar
import Submission.Work.Cyl.norm_angularVec

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false

namespace Work.ConstructionInstance

open Work.Cyl

/-! # The `√2`-Lipschitz bound for the angular frame vector `e_θ`

Off the axis `r = 0` the vector `e_θ x = (-x₁, x₀, 0)/r(x)` is a unit vector, and the geometric
input used in the construction is the *sharp* quantitative continuity estimate

  `‖e_θ x - e_θ y‖ ≤ √2 ‖x - y‖ / min (r x) (r y)`  for `r x > 0`, `r y > 0`.

The weaker bound with constant `2` (single radius `r y`) is `Work.Cyl.eTheta_sub_norm_mul_le`;
the improvement to `√2` and to the *minimum* of the two radii comes from the exact angle formula
`‖u/‖u‖ - v/‖v‖‖² = 2 - 2⟪u,v⟫/(‖u‖‖v‖)` together with the identity
`‖u - v‖² = ‖u‖² + ‖v‖² - 2⟪u,v⟫`.

The proof is organised in two steps.

* `norm_unit_sub_le` is a purely Hilbert-space statement: for nonzero `u v` in a real inner
  product space, the normalised vectors satisfy `‖u/‖u‖ - v/‖v‖‖ ≤ √2 ‖u-v‖ / min ‖u‖ ‖v‖`.
  Writing `a = ‖u‖`, `b = ‖v‖`, `c = ⟪u,v⟫` and assuming `a ≤ b` (so `min = a`), multiplying by
  `a b` (both `> 0`) turns the claim into the polynomial inequality `0 ≤ b³ + c (a - 2b)`, which
  follows from `c ≤ a b` and `a ≤ b`:
  `b³ + c(a-2b) ≥ b³ + ab(a-2b) = b(a-b)² ≥ 0`.
* `eTheta x = ‖angularVec x‖⁻¹ • angularVec x` and `‖angularVec x - angularVec y‖ ≤ ‖x - y‖`
  (the map `angularVec` is the (isometric) rotation by `90°` of the projection onto the
  `(x₀,x₁)`-plane), so the Hilbert-space statement applies with `u = angularVec x`,
  `v = angularVec y`. -/

/-- The Hilbert-space core of the estimate, in the case `‖u‖ ≤ ‖v‖`: with `a = ‖u‖`, `b = ‖v‖`
and `c = ⟪u,v⟫`, `b e_θ`-style normalisation gives `‖u/a - v/b‖ ≤ √2 ‖u-v‖ / a`.

Multiplying by `a b > 0` and squaring reduces the claim to `0 ≤ b³ + c(a-2b)`, which holds
because `c ≤ a b` (`real_inner_le_norm`) and `a ≤ b`, whence
`b³ + c(a-2b) ≥ b³ + ab(a-2b) = b (a-b)² ≥ 0`. -/
private lemma norm_unit_sub_le_aux {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u v : E) (hu : u ≠ 0) (hab : ‖u‖ ≤ ‖v‖) :
    ‖(‖u‖⁻¹ : ℝ) • u - (‖v‖⁻¹ : ℝ) • v‖ ≤ Real.sqrt 2 * ‖u - v‖ / ‖u‖ := by
  have ha : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hb : 0 < ‖v‖ := lt_of_lt_of_le ha hab
  set L := ‖(‖u‖⁻¹ : ℝ) • u - (‖v‖⁻¹ : ℝ) • v‖ with hL
  have h1 : (‖u‖ * ‖v‖) * ‖u‖⁻¹ = ‖v‖ := by
    rw [mul_assoc, mul_comm ‖v‖ ‖u‖⁻¹, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt ha), one_mul]
  have h2 : (‖u‖ * ‖v‖) * ‖v‖⁻¹ = ‖u‖ := by
    rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt hb), mul_one]
  have hvec : (‖u‖ * ‖v‖) • ((‖u‖⁻¹ : ℝ) • u - (‖v‖⁻¹ : ℝ) • v) = ‖v‖ • u - ‖u‖ • v := by
    rw [smul_sub, smul_smul, smul_smul, h1, h2]
  have hLab : L * (‖u‖ * ‖v‖) = ‖‖v‖ • u - ‖u‖ • v‖ := by
    rw [hL, mul_comm, ← norm_smul_of_nonneg (mul_nonneg ha.le hb.le), hvec]
  have hsqL : ‖‖v‖ • u - ‖u‖ • v‖ ^ 2
      = 2 * ‖u‖ ^ 2 * ‖v‖ ^ 2 - 2 * ‖u‖ * ‖v‖ * (inner ℝ u v) := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right]
    rw [real_inner_comm v u, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
    ring
  have hsqR : ‖u - v‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 - 2 * (inner ℝ u v) := by
    rw [norm_sub_sq_real]; ring
  have hkey : 0 ≤ ‖v‖ ^ 3 + (inner ℝ u v) * (‖u‖ - 2 * ‖v‖) := by
    have hprod : 0 ≤ (‖u‖ * ‖v‖ - inner ℝ u v) * (2 * ‖v‖ - ‖u‖) :=
      mul_nonneg (by linarith [real_inner_le_norm u v]) (by linarith)
    have hsq2 : 0 ≤ ‖v‖ * (‖u‖ - ‖v‖) ^ 2 := mul_nonneg hb.le (sq_nonneg _)
    nlinarith [hprod, hsq2]
  have hsq : (L * (‖u‖ * ‖v‖)) ^ 2 ≤ (Real.sqrt 2 * ‖u - v‖ * ‖v‖) ^ 2 := by
    rw [hLab, hsqL]
    rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), hsqR]
    nlinarith [hkey, hb]
  have hfin : L * (‖u‖ * ‖v‖) ≤ Real.sqrt 2 * ‖u - v‖ * ‖v‖ := by
    have h := sq_le_sq.mp hsq
    rwa [abs_of_nonneg (mul_nonneg (norm_nonneg _) (mul_nonneg ha.le hb.le)),
      abs_of_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg 2) (norm_nonneg _)) hb.le)] at h
  have hfin2 : L * ‖u‖ ≤ Real.sqrt 2 * ‖u - v‖ := by
    refine le_of_mul_le_mul_right ?_ hb
    nlinarith [hfin]
  rw [le_div_iff₀ ha]
  exact hfin2

/-- **Hilbert-space core of the `√2`-Lipschitz bound.**  For nonzero `u v` in a real inner product
space, the normalised vectors satisfy
`‖u/‖u‖ - v/‖v‖‖ ≤ √2 ‖u - v‖ / min ‖u‖ ‖v‖`.

WLOG `‖u‖ ≤ ‖v‖` (`min = ‖u‖`), which is exactly `norm_unit_sub_le_aux`; the other case is
obtained by exchanging `u` and `v`, both sides being symmetric under the swap. -/
private lemma norm_unit_sub_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u v : E) (hu : u ≠ 0) (hv : v ≠ 0) :
    ‖(‖u‖⁻¹ : ℝ) • u - (‖v‖⁻¹ : ℝ) • v‖
      ≤ Real.sqrt 2 * ‖u - v‖ / min ‖u‖ ‖v‖ := by
  rcases le_total ‖u‖ ‖v‖ with h | h
  · rw [min_eq_left h]
    exact norm_unit_sub_le_aux u v hu h
  · rw [min_eq_right h]
    have hk := norm_unit_sub_le_aux v u hv h
    calc ‖(‖u‖⁻¹ : ℝ) • u - (‖v‖⁻¹ : ℝ) • v‖
        = ‖(‖v‖⁻¹ : ℝ) • v - (‖u‖⁻¹ : ℝ) • u‖ := norm_sub_rev _ _
      _ ≤ Real.sqrt 2 * ‖v - u‖ / ‖v‖ := hk
      _ = Real.sqrt 2 * ‖u - v‖ / ‖v‖ := by rw [norm_sub_rev]

/-- `angularVec` is the rotation by `90°` of the projection of `x` onto the `(x₀,x₁)`-plane, so
it does not increase distances. -/
private lemma norm_angularVec_sub_le_dist (x y : R3) :
    ‖Work.Cyl.angularVec x - Work.Cyl.angularVec y‖ ≤ ‖x - y‖ := by
  have h : ‖Work.Cyl.angularVec x - Work.Cyl.angularVec y‖ ^ 2 ≤ ‖x - y‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, Work.Cyl.inner_eq,
      Work.Cyl.inner_eq]
    simp only [PiLp.sub_apply, Work.Cyl.angularVec_apply_zero, Work.Cyl.angularVec_apply_one,
      Work.Cyl.angularVec_apply_two]
    nlinarith [sq_nonneg (x 2 - y 2)]
  have := sq_le_sq.mp h
  rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)] at this

theorem eTheta_dist_le (x y : Work.ConstructionInstance.R3)
    (hx : 0 < Work.Cyl.radial x) (hy : 0 < Work.Cyl.radial y) :
    ‖Work.Cyl.eTheta x - Work.Cyl.eTheta y‖
      ≤ Real.sqrt 2 * ‖x - y‖
        / min (Work.Cyl.radial x) (Work.Cyl.radial y) := by
  have hx0 : Work.Cyl.angularVec x ≠ 0 := by
    rw [← norm_pos_iff, Work.Cyl.norm_angularVec]; exact hx
  have hy0 : Work.Cyl.angularVec y ≠ 0 := by
    rw [← norm_pos_iff, Work.Cyl.norm_angularVec]; exact hy
  have hkey := norm_unit_sub_le (Work.Cyl.angularVec x) (Work.Cyl.angularVec y) hx0 hy0
  have hEx : Work.Cyl.eTheta x = ‖Work.Cyl.angularVec x‖⁻¹ • Work.Cyl.angularVec x := by
    rw [Work.Cyl.eTheta, one_div, ← Work.Cyl.norm_angularVec]
  have hEy : Work.Cyl.eTheta y = ‖Work.Cyl.angularVec y‖⁻¹ • Work.Cyl.angularVec y := by
    rw [Work.Cyl.eTheta, one_div, ← Work.Cyl.norm_angularVec]
  rw [← hEx, ← hEy, Work.Cyl.norm_angularVec, Work.Cyl.norm_angularVec] at hkey
  have hm : 0 < min (Work.Cyl.radial x) (Work.Cyl.radial y) := lt_min hx hy
  have hnum : Real.sqrt 2 * ‖Work.Cyl.angularVec x - Work.Cyl.angularVec y‖
      ≤ Real.sqrt 2 * ‖x - y‖ :=
    mul_le_mul_of_nonneg_left (norm_angularVec_sub_le_dist x y) (Real.sqrt_nonneg 2)
  have h1 : ‖Work.Cyl.eTheta x - Work.Cyl.eTheta y‖
      * min (Work.Cyl.radial x) (Work.Cyl.radial y) ≤ Real.sqrt 2 * ‖x - y‖ :=
    le_trans ((le_div_iff₀ hm).mp hkey) hnum
  exact (le_div_iff₀ hm).mpr h1

end Work.ConstructionInstance
