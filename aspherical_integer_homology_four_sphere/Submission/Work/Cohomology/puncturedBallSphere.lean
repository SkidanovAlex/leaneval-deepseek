import Mathlib
import Submission.Work.Cohomology.SphDefs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The punctured open ball is homotopy equivalent to the unit sphere

For a real inner product space `E`, a centre `y : E` and a radius `r > 0`, the complement of `{y}`
in the open ball `Metric.ball y r` is homotopy equivalent to the unit sphere `Metric.sphere 0 1`.

The homotopy equivalence is realized by radial projection
`z ↦ ‖z - y‖⁻¹ • (z - y)` from the punctured ball to the sphere, with homotopy inverse
`u ↦ y + (r/2) • u`.  The composite `proj ∘ incl` is literally the identity of the sphere (every
point of the sphere has norm `1`), while `incl ∘ proj` is homotopic to the identity of the
punctured ball through the straight line homotopy

`(t, z) ↦ y + ((1 - t) * ((r/2)/‖z - y‖) + t) • (z - y)`,

whose coefficient is strictly positive; hence the image is never `y`, and its distance to `y` is
`(1 - t) * (r/2) + t * ‖z - y‖ < r` because `‖z - y‖ < r` and the coefficient of `r/2` is at most
`1`.  At `t = 0` this map is `z ↦ y + ((r/2)/‖z - y‖) • (z - y) = incl (proj z)` and at `t = 1` it
is `z ↦ y + (z - y) = z`.

The same construction also shows that the whole punctured space `{v : E // v ≠ 0}` is homotopy
equivalent to the sphere (`Submission/Work/Cohomology/punctured_homotopyEquiv_sphere.lean`).
-/

open scoped unitInterval

namespace Work.Cohomology

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ## Elementary arithmetic of the two coefficients -/

/-- A convex combination of `a` and `1` with weights `1 - t` and `t`, `t ∈ [0,1]`, stays strictly
positive when `a > 0`. -/
private lemma pos_conv (t a : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (ha : 0 < a) :
    0 < (1 - t) * a + t := by
  have h1 : 0 ≤ 1 - t := by linarith
  rcases eq_or_lt_of_le ht0 with h | h
  · rw [← h]; simpa using ha
  · have h2 : 0 ≤ (1 - t) * a := mul_nonneg h1 ha.le
    linarith

/-- The distance from `y` to `y + c • (z - y)` for `c = (1 - t) * (r/2)/‖z - y‖ + t` is
`(1 - t) * (r/2) + t * ‖z - y‖`, which is `< r` when `‖z - y‖ < r`. -/
private lemma coeff_mul_lt (t b r : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hb : b < r) (hr : 0 < r) :
    (1 - t) * (r/2) + t * b < r := by
  have h1 : 0 ≤ 1 - t := by linarith
  rcases eq_or_lt_of_le ht0 with h | h
  · rw [← h]; simp; linarith
  · have h2 : (1 - t) * (r/2) ≤ (1 - t) * r := mul_le_mul_of_nonneg_left (by linarith) h1
    have h3 : t * b < t * r := mul_lt_mul_of_pos_left hb h
    have h4 : (1 - t) * r + t * r = r := by ring
    linarith

/-! ## The two maps -/

omit [InnerProductSpace ℝ E] in
private lemma sphere_norm_eq_one (x : Metric.sphere (0 : E) 1) : ‖(x : E)‖ = 1 := by
  have h := Metric.mem_sphere.mp x.2
  rwa [dist_zero_right] at h

omit [InnerProductSpace ℝ E] in
private lemma sphere_ne_zero (x : Metric.sphere (0 : E) 1) : (x : E) ≠ 0 :=
  norm_ne_zero_iff.mp (by rw [sphere_norm_eq_one x]; norm_num)

omit [InnerProductSpace ℝ E] in
private lemma continuous_coe_ball (y : E) (r : ℝ) :
    Continuous fun z : {z : Metric.ball y r // (z : E) ≠ y} => (z : E) :=
  (continuous_subtype_val : Continuous (Subtype.val : Metric.ball y r → E)).comp
    (continuous_subtype_val :
      Continuous (Subtype.val : {z : Metric.ball y r // (z : E) ≠ y} → Metric.ball y r))

private lemma norm_inv_smul_sub_mem (y : E) (r : ℝ)
    (z : {z : Metric.ball y r // (z : E) ≠ y}) :
    ‖(z : E) - y‖⁻¹ • ((z : E) - y) ∈ Metric.sphere (0 : E) 1 := by
  rw [Metric.mem_sphere, dist_zero_right, norm_smul, norm_inv, Real.norm_of_nonneg (norm_nonneg _)]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr z.2))

private lemma continuous_norm_inv_smul_sub (y : E) (r : ℝ) :
    Continuous fun z : {z : Metric.ball y r // (z : E) ≠ y} =>
      ‖(z : E) - y‖⁻¹ • ((z : E) - y) := by
  have h : Continuous fun z : {z : Metric.ball y r // (z : E) ≠ y} => (z : E) - y :=
    (continuous_coe_ball y r).sub continuous_const
  exact (h.norm.inv₀ (fun z => norm_ne_zero_iff.mpr (sub_ne_zero.mpr z.2))).smul h

/-- Radial projection of the punctured ball onto the unit sphere. -/
private def toSphere (y : E) (r : ℝ) :
    C({z : Metric.ball y r // (z : E) ≠ y}, Metric.sphere (0 : E) 1) :=
  ⟨fun z => ⟨‖(z : E) - y‖⁻¹ • ((z : E) - y), norm_inv_smul_sub_mem y r z⟩,
   Continuous.subtype_mk (continuous_norm_inv_smul_sub y r)
     (fun z => norm_inv_smul_sub_mem y r z)⟩

private lemma mem_ball_add_smul (y : E) (r : ℝ) (hr : 0 < r) (u : Metric.sphere (0 : E) 1) :
    y + (r/2) • (u : E) ∈ Metric.ball y r := by
  rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_of_nonneg (by linarith : (0:ℝ) ≤ r/2), sphere_norm_eq_one u, mul_one]
  linarith

private lemma add_smul_ne_self (y : E) (r : ℝ) (hr : 0 < r) (u : Metric.sphere (0 : E) 1) :
    y + (r/2) • (u : E) ≠ y := by
  intro h
  have h2 : (r/2) • (u : E) = 0 := by
    have h3 := sub_eq_zero.mpr h
    rwa [add_sub_cancel_left] at h3
  exact smul_ne_zero (by linarith : (r/2 : ℝ) ≠ 0) (sphere_ne_zero u) h2

/-- The inclusion of the sphere into the punctured ball, scaling by `r/2`. -/
private def incl (y : E) (r : ℝ) (hr : 0 < r) :
    C(Metric.sphere (0 : E) 1, {z : Metric.ball y r // (z : E) ≠ y}) :=
  ⟨fun u => ⟨⟨y + (r/2) • (u : E), mem_ball_add_smul y r hr u⟩, add_smul_ne_self y r hr u⟩,
   Continuous.subtype_mk (Continuous.subtype_mk
     (continuous_const.add (continuous_const.smul continuous_subtype_val))
       (fun u => mem_ball_add_smul y r hr u))
     (fun u => add_smul_ne_self y r hr u)⟩

private lemma toSphere_incl_apply (y : E) (r : ℝ) (hr : 0 < r) (u : Metric.sphere (0 : E) 1) :
    toSphere y r (incl y r hr u) = u := by
  apply Subtype.ext
  change ‖(y + (r/2) • (u : E)) - y‖⁻¹ • ((y + (r/2) • (u : E)) - y) = (u : E)
  rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg (by linarith : (0:ℝ) ≤ r/2),
      sphere_norm_eq_one u, mul_one, smul_smul, inv_mul_cancel₀ (by linarith : (r/2 : ℝ) ≠ 0),
      one_smul]

/-- The composite `proj ∘ incl` is the identity of the sphere. -/
private lemma toSphere_comp_incl (y : E) (r : ℝ) (hr : 0 < r) :
    (toSphere y r).comp (incl y r hr) = ContinuousMap.id (Metric.sphere (0 : E) 1) := by
  apply ContinuousMap.ext
  intro u
  simpa using toSphere_incl_apply y r hr u

/-! ## The homotopy from `incl ∘ proj` to the identity -/

/-- The underlying `E`-valued formula of the straight line homotopy. -/
private def hval (y : E) (r : ℝ) (p : I × {z : Metric.ball y r // (z : E) ≠ y}) : E :=
  y + ((1 - (p.1 : ℝ)) * ((r/2) / ‖(p.2 : E) - y‖) + (p.1 : ℝ)) • ((p.2 : E) - y)

private lemma hval_eq (y : E) (r : ℝ) (t : I) (z : {z : Metric.ball y r // (z : E) ≠ y}) :
    hval y r (t, z) =
      y + ((1 - (t : ℝ)) * ((r/2) / ‖(z : E) - y‖) + (t : ℝ)) • ((z : E) - y) :=
  rfl

private lemma hval_ne (y : E) (r : ℝ) (hr : 0 < r)
    (p : I × {z : Metric.ball y r // (z : E) ≠ y}) : hval y r p ≠ y := by
  have ht0 : 0 ≤ (p.1 : ℝ) := p.1.2.1
  have ht1 : (p.1 : ℝ) ≤ 1 := p.1.2.2
  have hb : 0 < ‖(p.2 : E) - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr p.2.2)
  have ha : 0 < (r/2) / ‖(p.2 : E) - y‖ := div_pos (by linarith) hb
  have hc : 0 < (1 - (p.1 : ℝ)) * ((r/2) / ‖(p.2 : E) - y‖) + (p.1 : ℝ) :=
    pos_conv _ _ ht0 ht1 ha
  intro h
  have h2 : ((1 - (p.1:ℝ)) * ((r/2) / ‖(p.2:E) - y‖) + (p.1:ℝ)) • ((p.2:E) - y) = 0 := by
    have h3 := sub_eq_zero.mpr h
    rw [hval, add_sub_cancel_left] at h3
    exact h3
  exact smul_ne_zero (ne_of_gt hc) (sub_ne_zero.mpr p.2.2) h2

private lemma hval_mem_ball (y : E) (r : ℝ) (hr : 0 < r)
    (p : I × {z : Metric.ball y r // (z : E) ≠ y}) : hval y r p ∈ Metric.ball y r := by
  have ht0 : 0 ≤ (p.1 : ℝ) := p.1.2.1
  have ht1 : (p.1 : ℝ) ≤ 1 := p.1.2.2
  have hbpos : 0 < ‖(p.2 : E) - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr p.2.2)
  have hblt : ‖(p.2 : E) - y‖ < r := by
    have h := Metric.mem_ball.mp p.2.1.2
    rwa [dist_eq_norm] at h
  have ha : 0 < (r/2) / ‖(p.2 : E) - y‖ := div_pos (by linarith) hbpos
  have hc : 0 < (1 - (p.1:ℝ)) * ((r/2)/‖(p.2:E) - y‖) + (p.1:ℝ) := pos_conv _ _ ht0 ht1 ha
  rw [Metric.mem_ball, dist_eq_norm]
  have hsub : hval y r p - y
      = ((1 - (p.1:ℝ)) * ((r/2)/‖(p.2:E) - y‖) + (p.1:ℝ)) • ((p.2:E) - y) := by
    rw [hval, add_sub_cancel_left]
  rw [hsub, norm_smul, Real.norm_of_nonneg hc.le]
  have hmul : ((1 - (p.1:ℝ)) * ((r/2)/‖(p.2:E) - y‖) + (p.1:ℝ)) * ‖(p.2:E) - y‖
      = (1 - (p.1:ℝ)) * (r/2) + (p.1:ℝ) * ‖(p.2:E) - y‖ := by
    have hbne : ‖(p.2:E) - y‖ ≠ 0 := ne_of_gt hbpos
    field_simp
  rw [hmul]
  exact coeff_mul_lt (p.1 : ℝ) ‖(p.2:E) - y‖ r ht0 ht1 hblt hr

private lemma continuous_hval (y : E) (r : ℝ) :
    Continuous fun p : I × {z : Metric.ball y r // (z : E) ≠ y} => hval y r p := by
  have ht : Continuous fun p : I × {z : Metric.ball y r // (z:E) ≠ y} => (p.1 : ℝ) :=
    continuous_subtype_val.comp continuous_fst
  have hx : Continuous fun p : I × {z : Metric.ball y r // (z:E) ≠ y} => (p.2 : E) :=
    (continuous_subtype_val : Continuous (Subtype.val : Metric.ball y r → E)).comp
      ((continuous_subtype_val :
          Continuous (Subtype.val : {z : Metric.ball y r // (z : E) ≠ y} → Metric.ball y r)).comp
        continuous_snd)
  have hsub : Continuous fun p : I × {z : Metric.ball y r // (z:E) ≠ y} => (p.2 : E) - y :=
    hx.sub continuous_const
  have hinv : Continuous fun p : I × {z : Metric.ball y r // (z:E) ≠ y} =>
      (‖(p.2 : E) - y‖)⁻¹ :=
    hsub.norm.inv₀ (fun p => norm_ne_zero_iff.mpr (sub_ne_zero.mpr p.2.2))
  have hcoe : Continuous fun p : I × {z : Metric.ball y r // (z:E) ≠ y} =>
      (1 - (p.1 : ℝ)) * ((r/2) * (‖(p.2 : E) - y‖)⁻¹) + (p.1 : ℝ) :=
    ((continuous_const.sub ht).mul (continuous_const.mul hinv)).add ht
  have hmain : Continuous fun p : I × {z : Metric.ball y r // (z:E) ≠ y} =>
      y + ((1 - (p.1 : ℝ)) * ((r/2) * (‖(p.2 : E) - y‖)⁻¹) + (p.1 : ℝ)) • ((p.2 : E) - y) :=
    continuous_const.add (hcoe.smul hsub)
  simpa only [hval, div_eq_mul_inv] using hmain

/-- The straight line homotopy, as a map into the punctured ball. -/
private def hcm (y : E) (r : ℝ) (hr : 0 < r) :
    C(I × {z : Metric.ball y r // (z : E) ≠ y}, {z : Metric.ball y r // (z : E) ≠ y}) :=
  ⟨fun p => ⟨⟨hval y r p, hval_mem_ball y r hr p⟩, hval_ne y r hr p⟩,
   Continuous.subtype_mk
     (Continuous.subtype_mk (continuous_hval y r) (fun p => hval_mem_ball y r hr p))
     (fun p => hval_ne y r hr p)⟩

/-- The straight line homotopy from `incl ∘ proj` to the identity of the punctured ball. -/
private def homotopy (y : E) (r : ℝ) (hr : 0 < r) :
    ContinuousMap.Homotopy ((incl y r hr).comp (toSphere y r))
      (ContinuousMap.id {z : Metric.ball y r // (z : E) ≠ y}) :=
  ContinuousMap.Homotopy.mk (hcm y r hr)
    (fun z => by
      apply Subtype.ext
      apply Subtype.ext
      change hval y r (0, z) = y + (r/2) • (‖(z : E) - y‖⁻¹ • ((z : E) - y))
      rw [hval_eq y r 0 z, div_eq_mul_inv, smul_smul]
      norm_num)
    (fun z => by
      apply Subtype.ext
      apply Subtype.ext
      change hval y r (1, z) = (z : E)
      rw [hval_eq y r 1 z]
      norm_num)

/-- **The punctured open ball in a real inner product space is homotopy equivalent to the unit
sphere.** -/
theorem puncturedBallSphere_general (y : E) (r : ℝ) (hr : 0 < r) :
    Nonempty (ContinuousMap.HomotopyEquiv {z : Metric.ball y r // (z : E) ≠ y}
      (Metric.sphere (0 : E) 1)) :=
  ⟨{ toFun := toSphere y r
     invFun := incl y r hr
     left_inv := ⟨homotopy y r hr⟩
     right_inv := by
       rw [toSphere_comp_incl y r hr] }⟩

end

set_option linter.unusedVariables false

/-- **The punctured open ball is homotopy equivalent to the unit sphere.**

For `n ≥ 1`, a point `y` of `EuclideanSpace ℝ (Fin n)` and `r > 0`, the complement of `{y}` in the
open ball `Metric.ball y r` (viewed as a subspace of `EuclideanSpace ℝ (Fin n)`) is homotopy
equivalent to the unit sphere `Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1`.

Intended homotopy equivalence: `z ↦ ‖z - y‖⁻¹ • (z - y)` from the punctured ball to the sphere,
with homotopy inverse `u ↦ y + (r/2) • u` (whose value lies in `Metric.ball y r` because
`dist (y + (r/2)•u) y = r/2 < r`, and is `≠ y`); the composite on the sphere is the identity
(every point of the sphere has norm `1`), and the other composite is homotopic to the identity
through `(t, z) ↦ y + ((1 - t) + t * (r/2) / ‖z - y‖) • (z - y)`, whose coefficient is strictly
positive hence the point is again `≠ y` and is at distance `< r` from `y`.

A useful model file for the continuity/compactness bookkeeping (though there the whole space
`{v : E // v ≠ 0}` is used in place of the punctured ball) is
`Submission/Work/Cohomology/punctured_homotopyEquiv_sphere.lean`. -/
theorem puncturedBallSphere (n : ℕ) (hn : 1 ≤ n) (y : EuclideanSpace ℝ (Fin n)) (r : ℝ)
    (hr : 0 < r) :
    Nonempty (ContinuousMap.HomotopyEquiv
      {z : Metric.ball y r // (z : EuclideanSpace ℝ (Fin n)) ≠ y}
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)) :=
  puncturedBallSphere_general y r hr

end Work.Cohomology
