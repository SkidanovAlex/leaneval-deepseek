/-
Copyright: work module for the Elgindi finite-time singularity project.

# `FTS_EllLimOK.ZDecayAux` — the elementary real-variable core of the `ZDecay` estimate

The lemma `Work.FTS_EllLimOK.ZDecay_of_decay_bounds` derives the boundary decay
`Work.FTS.EllipticEst.ZDecay Ψ` from the *bounds* on the jet components
`F j i : (1+z)^{3/2} * |F j i z θ| ≤ C`.  The estimate is pointwise and elementary; this module
collects the arithmetic that it needs, so that the pieces can be stated and proved separately.

Contents:

* `rpow32_sq` — `((x : ℝ) ^ (3/2)) ^ 2 = x ^ 3` for `x ≥ 0`;
* `sq_le_div_cube_of_abs_le` — from `|a| ≤ D / x^{3/2}` and `0 ≤ D`, `0 ≤ x`, the sharp bound
  `a ^ 2 ≤ D ^ 2 / x ^ 3`;
* `sq_le_inv_of_abs_le` — its consequence `a ^ 2 ≤ D ^ 2 / x` for `x ≥ 1`;
* `zsq_mul_sq_le_inv_of_abs_le` — the *radial* version:
  `z ^ 2 * a ^ 2 ≤ D ^ 2 / (1+z)` from `|a| ≤ D / (1+z)^{3/2}`, `1 ≤ z` (the instance used for
  every one of the five slots of the `z ^ 2`-weighted jet, since `z ^ 2 ≤ (1+z) ^ 2` recovers
  the extra power `(1+z) ^ (-1)`);
* `abs_le_div_rpow32_of_mul_le` — the passage from the hypothesis shape
  `(1+z)^{3/2} * |F| ≤ C` to the quotient shape `|F| ≤ C / (1+z)^{3/2}`;
* `pz_eq_zero_of_forall`, `pzIter_two_eq_zero_of_forall` — the trivial radial derivatives vanish
  at an angle where the whole `z`-slice vanishes (the endpoint case of the decay statement).

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS_EllLimOK.DecayAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK

/-! ## The half-integer power -/

/-- `((x : ℝ) ^ (3/2)) ^ 2 = x ^ 3` for `x ≥ 0`. -/
theorem rpow32_sq {x : ℝ} (hx : 0 ≤ x) : (x ^ ((3 : ℝ) / 2)) ^ 2 = x ^ 3 := by
  rw [← Real.rpow_natCast (x ^ ((3 : ℝ) / 2)) 2, ← Real.rpow_mul hx]
  norm_num

/-! ## The pointwise bounds -/

/-- From `|a| ≤ D / x^{3/2}` (with `0 ≤ D`, `0 ≤ x`) one gets the sharp `a ^ 2 ≤ D ^ 2 / x ^ 3`. -/
theorem sq_le_div_cube_of_abs_le {a D x : ℝ} (hD : 0 ≤ D) (hx : 0 ≤ x)
    (h : |a| ≤ D / x ^ ((3 : ℝ) / 2)) : a ^ 2 ≤ D ^ 2 / x ^ 3 := by
  have hDx : 0 ≤ D / x ^ ((3 : ℝ) / 2) := by positivity
  have h1 : |a| ^ 2 ≤ (D / x ^ ((3 : ℝ) / 2)) ^ 2 := by
    rw [sq_le_sq]
    simpa only [abs_of_nonneg hDx, abs_abs] using h
  calc a ^ 2 = |a| ^ 2 := (sq_abs a).symm
    _ ≤ (D / x ^ ((3 : ℝ) / 2)) ^ 2 := h1
    _ = D ^ 2 / x ^ 3 := by rw [div_pow, rpow32_sq hx]

/-- From `|a| ≤ D / x^{3/2}` (with `0 ≤ D`, `1 ≤ x`) one gets `a ^ 2 ≤ D ^ 2 / x`. -/
theorem sq_le_inv_of_abs_le {a D x : ℝ} (hD : 0 ≤ D) (hx : 1 ≤ x)
    (h : |a| ≤ D / x ^ ((3 : ℝ) / 2)) : a ^ 2 ≤ D ^ 2 / x := by
  have hxpos : 0 < x := by linarith
  have hcore := sq_le_div_cube_of_abs_le hD (le_of_lt hxpos) h
  have hx3 : x ≤ x ^ 3 := by
    have := pow_le_pow_right₀ hx (show (1 : ℕ) ≤ 3 by norm_num)
    simpa using this
  have h3 : 1 / x ^ 3 ≤ 1 / x := one_div_le_one_div_of_le hxpos hx3
  calc a ^ 2 ≤ D ^ 2 / x ^ 3 := hcore
    _ = D ^ 2 * (1 / x ^ 3) := by ring
    _ ≤ D ^ 2 * (1 / x) := mul_le_mul_of_nonneg_left h3 (sq_nonneg D)
    _ = D ^ 2 / x := by ring

/-- **The radial shape.**  From `|a (z)| ≤ D / (1+z)^{3/2}` (with `0 ≤ D`, `1 ≤ z`) one gets
`z ^ 2 * a ^ 2 ≤ D ^ 2 / (1+z)`: the factor `z ^ 2` is absorbed by `z ^ 2 ≤ (1+z) ^ 2`. -/
theorem zsq_mul_sq_le_inv_of_abs_le {a z D : ℝ} (hD : 0 ≤ D) (hz : 1 ≤ z)
    (h : |a| ≤ D / (1 + z) ^ ((3 : ℝ) / 2)) : z ^ 2 * a ^ 2 ≤ D ^ 2 / (1 + z) := by
  have hxpos : (0 : ℝ) < 1 + z := by linarith
  have ha2 : a ^ 2 ≤ D ^ 2 / (1 + z) ^ 3 :=
    sq_le_div_cube_of_abs_le hD (le_of_lt hxpos) h
  have hzx : z / (1 + z) ≤ 1 := by
    rw [div_le_one (by linarith)]
    linarith
  have hzx0 : 0 ≤ z / (1 + z) := by positivity
  have hs : (z / (1 + z)) ^ 2 ≤ 1 := by nlinarith
  have hx3 : z ^ 2 / (1 + z) ^ 3 = (z / (1 + z)) ^ 2 * (1 / (1 + z)) := by
    field_simp
  have hxinv : 0 ≤ 1 / (1 + z) := by positivity
  have hstep : z ^ 2 / (1 + z) ^ 3 ≤ 1 / (1 + z) := by
    calc z ^ 2 / (1 + z) ^ 3 = (z / (1 + z)) ^ 2 * (1 / (1 + z)) := hx3
      _ ≤ 1 * (1 / (1 + z)) := mul_le_mul_of_nonneg_right hs hxinv
      _ = 1 / (1 + z) := one_mul _
  calc z ^ 2 * a ^ 2 ≤ z ^ 2 * (D ^ 2 / (1 + z) ^ 3) :=
        mul_le_mul_of_nonneg_left ha2 (sq_nonneg z)
    _ = D ^ 2 * (z ^ 2 / (1 + z) ^ 3) := by ring
    _ ≤ D ^ 2 * (1 / (1 + z)) := mul_le_mul_of_nonneg_left hstep (sq_nonneg D)
    _ = D ^ 2 / (1 + z) := by ring

/-- The passage from the product shape `(1+z)^{3/2} * A ≤ C` of the decay hypothesis to the
quotient shape `A ≤ C / (1+z)^{3/2}`. -/
theorem abs_le_div_rpow32_of_mul_le {A C : ℝ} {z : ℝ} (hz : 0 < z)
    (h : (1 + z) ^ ((3 : ℝ) / 2) * A ≤ C) : A ≤ C / (1 + z) ^ ((3 : ℝ) / 2) := by
  have hpos : 0 < (1 + z) ^ ((3 : ℝ) / 2) := Real.rpow_pos_of_pos (by linarith) _
  rw [le_div_iff₀ hpos]
  calc A * (1 + z) ^ ((3 : ℝ) / 2) = (1 + z) ^ ((3 : ℝ) / 2) * A := by ring
    _ ≤ C := h

/-! ## The endpoint vanishing of the radial derivatives -/

/-- If the whole `z`-slice of `Ψ` at the angle `θ` vanishes, then so does `∂_zΨ` there. -/
theorem pz_eq_zero_of_forall {Ψ : ℝ → ℝ → ℝ} {θ z : ℝ} (h : ∀ z', Ψ z' θ = 0) :
    Work.Spaces.pz Ψ z θ = 0 := by
  simp only [Work.Spaces.pz]
  rw [show (fun z' => Ψ z' θ) = fun _ => (0 : ℝ) from funext h]
  simp

/-- If the whole `z`-slice of `Ψ` at the angle `θ` vanishes, then so does `∂_z²Ψ` there. -/
theorem pzIter_two_eq_zero_of_forall {Ψ : ℝ → ℝ → ℝ} {θ z : ℝ} (h : ∀ z', Ψ z' θ = 0) :
    Work.Spaces.pzIter 2 Ψ z θ = 0 := by
  have h1 : ∀ z', Work.Spaces.pz Ψ z' θ = 0 := fun z' => pz_eq_zero_of_forall h
  have := pz_eq_zero_of_forall (Ψ := Work.Spaces.pz Ψ) (θ := θ) (z := z) h1
  simpa only [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero] using this

end Work.FTS_EllLimOK
