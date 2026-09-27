import Mathlib
import Submission.Work.Drive.SeamSweep
import Submission.Work.Drive.meet32_bordism_invariance

/-!
# The box reparametrisations of the ends-clause genericity (`NOTES_LEAD_hodd_blockT6.md` §2.2)

This module fixes the **elementary vocabulary** of the parametrised family by which the ends-clause
genericity `Work.Drive.exists_homotopy_meet3Hyp_encoded` (`Drive/encodedGeneric.lean`, §2.1) is proved:
a box self-diffeomorphism of the parameter square (the *shear*) and of the level interval (the *twist*),
both with **unbounded** parameters clamped into a ball.

Why clamped: the local parametric Sard (`Work.Drive.localSard_family_in_open`) asks for the
surjectivity of the parameter derivative **at every centre** `t₀` of the parameter space, so the
parameter directions of the reparametrisation must be non-degenerate at every parameter value.  A
shear with a raw parameter `a` is a self-map of the square only for `|a|` small, so the parameter is
post-composed with the explicit diffeomorphism `ballClamp : 𝔼ⁿ → {‖x‖ < 1/2}` — which has invertible
derivative *everywhere*, so no direction is lost.

The shape of `shear` is the cross-shear of the lead's note,
`(y₀, y₁) ↦ (y₀ + C(y₁) hb y₀, y₁ + D(y₀) hb y₁)` with `C(y₁) = a₀(1-2y₁) + a₂ hb y₁` and
`D(y₀) = a₁(1-2y₀) + a₃ hb y₀`: the coefficients `C`, `D` reverse sign under `x ↦ 1-x`
(`hb (1-x) = hb x` and `(1-2(1-x)) = -(1-2x)`), which is exactly what makes the shear **commute with
the seam involution** `seamInv2` on the boundary of the square.

Notation note: `pt2` is the parametrisation of the square used by `encodedChains`
(`meet32_bordism_invariance.lean`); `mk2` (used by `refTripleClause.lean`'s clause homotopies) is the
same function, and the two are identified by `Work.Drive.pt2_eq_mk2_local`.
-/

namespace Work.Drive

open scoped Manifold Topology

noncomputable section

/-! ## 1. The parabola bump -/

/-- The parabola bump `hb x = x (1 - x)`. -/
def hb (x : ℝ) : ℝ := x * (1 - x)

/-- `hb` is symmetric about `1/2` — the identity behind the seam-equivariance of the shears. -/
lemma hb_symm (x : ℝ) : hb (1 - x) = hb x := by
  unfold hb; ring

@[simp] lemma hb_zero : hb 0 = 0 := by unfold hb; norm_num

@[simp] lemma hb_one : hb 1 = 0 := by unfold hb; norm_num

lemma hb_pos {x : ℝ} (h0 : 0 < x) (h1 : x < 1) : 0 < hb x := by
  unfold hb; nlinarith

lemma hb_nonneg {x : ℝ} (h : x ∈ Set.Icc (0 : ℝ) 1) : 0 ≤ hb x := by
  unfold hb; nlinarith [h.1, h.2]

lemma hb_le (x : ℝ) : hb x ≤ 1 / 4 := by
  unfold hb; nlinarith [sq_nonneg (x - 1 / 2)]

/-- `hb` vanishes exactly at the two ends of the interval. -/
lemma hb_eq_zero_iff {x : ℝ} (h : x ∈ Set.Icc (0 : ℝ) 1) : hb x = 0 ↔ x = 0 ∨ x = 1 := by
  unfold hb
  constructor
  · intro hx
    rcases mul_eq_zero.mp hx with h1 | h1
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  · rintro (rfl | rfl) <;> ring

/-! ## 2. The clamped parameters -/

/-- The clamped parameter of the line: `s ↦ s / (2 √(1+s²))`.  It has invertible derivative
everywhere and takes values in `(-1/2, 1/2)`. -/
def clamp1 (s : ℝ) : ℝ := (2 * Real.sqrt (1 + s ^ 2))⁻¹ * s

/-- The clamped parameter of `𝔼ⁿ`: `q ↦ q / (2 √(1+‖q‖²))`, with values in the ball of radius `1/2`. -/
def ballClamp {n : ℕ} (q : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  (2 * Real.sqrt (1 + ‖q‖ ^ 2))⁻¹ • q

@[simp] lemma ballClamp_zero {n : ℕ} : ballClamp (0 : EuclideanSpace ℝ (Fin n)) = 0 := by
  simp [ballClamp]

lemma norm_ballClamp_lt {n : ℕ} (q : EuclideanSpace ℝ (Fin n)) : ‖ballClamp q‖ < 1 / 2 := by
  have hden : 0 < 2 * Real.sqrt (1 + ‖q‖ ^ 2) := by positivity
  have hle : ‖q‖ < Real.sqrt (1 + ‖q‖ ^ 2) := by
    rw [Real.lt_sqrt (norm_nonneg q)]
    linarith [sq_nonneg ‖q‖]
  rw [ballClamp, norm_smul, Real.norm_of_nonneg (by positivity), inv_mul_lt_iff₀ hden]
  rw [mul_comm]
  linarith

@[simp] lemma clamp1_zero : clamp1 0 = 0 := by simp [clamp1]

/-! ## 3. The cross-shear of the square -/

/-- **The first triangular factor of the cross-shear**: it moves only the first coordinate, by
`y₀ + C(y₁) hb y₀` with `C(y₁) = a₀(1-2y₁) + a₂ hb y₁`, `a = ballClamp q`. -/
def shear₁ (q : EuclideanSpace ℝ (Fin 4)) (y : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  pt2 (y 0 + (ballClamp q 0 * (1 - 2 * y 1) + ballClamp q 2 * hb (y 1)) * hb (y 0)) (y 1)

/-- **The second triangular factor of the cross-shear**: it moves only the second coordinate, by
`y₁ + D(y₀) hb y₁` with `D(y₀) = a₁(1-2y₀) + a₃ hb y₀`. -/
def shear₂ (q : EuclideanSpace ℝ (Fin 4)) (y : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  pt2 (y 0) (y 1 + (ballClamp q 1 * (1 - 2 * y 0) + ballClamp q 3 * hb (y 0)) * hb (y 1))

/-- **The cross-shear of the parameter square**, with clamped parameter `q ∈ 𝔼⁴`: the composite of
the two triangular factors.  Its two ingredients are self-maps of the square (each moves one
coordinate by a strictly monotone function of that coordinate, the other coordinate being only a
parameter), which is what makes the box bijection elementary; and the coefficients `C`, `D` reverse
sign under `x ↦ 1-x`, which is what makes the composite commute with the seam involution. -/
def shear (q : EuclideanSpace ℝ (Fin 4)) (y : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  shear₂ q (shear₁ q y)

@[simp] lemma shear₁_apply_zero (q : EuclideanSpace ℝ (Fin 4)) (y : EuclideanSpace ℝ (Fin 2)) :
    shear₁ q y 0 = y 0 + (ballClamp q 0 * (1 - 2 * y 1) + ballClamp q 2 * hb (y 1)) * hb (y 0) := by
  simp [shear₁]

@[simp] lemma shear₁_apply_one (q : EuclideanSpace ℝ (Fin 4)) (y : EuclideanSpace ℝ (Fin 2)) :
    shear₁ q y 1 = y 1 := by
  simp [shear₁]

@[simp] lemma shear₂_apply_zero (q : EuclideanSpace ℝ (Fin 4)) (y : EuclideanSpace ℝ (Fin 2)) :
    shear₂ q y 0 = y 0 := by
  simp [shear₂]

@[simp] lemma shear₂_apply_one (q : EuclideanSpace ℝ (Fin 4)) (y : EuclideanSpace ℝ (Fin 2)) :
    shear₂ q y 1 = y 1 + (ballClamp q 1 * (1 - 2 * y 0) + ballClamp q 3 * hb (y 0)) * hb (y 1) := by
  simp [shear₂]

@[simp] lemma shear_apply_zero (q : EuclideanSpace ℝ (Fin 4)) (y : EuclideanSpace ℝ (Fin 2)) :
    shear q y 0 = y 0 + (ballClamp q 0 * (1 - 2 * y 1) + ballClamp q 2 * hb (y 1)) * hb (y 0) := by
  simp [shear]

@[simp] lemma shear_apply_one (q : EuclideanSpace ℝ (Fin 4)) (y : EuclideanSpace ℝ (Fin 2)) :
    shear q y 1 = y 1 + (ballClamp q 1 * (1 - 2 * (shear₁ q y 0)) + ballClamp q 3 * hb (shear₁ q y 0))
      * hb (y 1) := by
  simp [shear, shear₂_apply_one]

@[simp] lemma shear_zero (y : EuclideanSpace ℝ (Fin 2)) : shear 0 y = y := by
  ext i
  fin_cases i <;> simp [shear, hb]

@[simp] lemma shear₁_zero (y : EuclideanSpace ℝ (Fin 2)) : shear₁ 0 y = y := by
  ext i
  fin_cases i <;> simp [shear₁, hb]

@[simp] lemma shear₂_zero (y : EuclideanSpace ℝ (Fin 2)) : shear₂ 0 y = y := by
  ext i
  fin_cases i <;> simp [shear₂, hb]

/-! ## 4. The twist of the level interval -/

/-- **The twist of the level**: `θ_r x = x + r hb x` with clamped parameter `r = clamp1 s`. -/
def thetaS (s x : ℝ) : ℝ := x + clamp1 s * hb x

@[simp] lemma thetaS_zero (x : ℝ) : thetaS 0 x = x := by simp [thetaS]

/-! ## 5. The time bump of the homotopy perturbation -/

/-- The bump in the *time* coordinate of the homotopy chain by which the homotopy `H` is perturbed:
it vanishes outside `[0,1]` (so the perturbation keeps the two ends `H (0,·)`, `H (1,·)`) and is
strictly positive inside `(0,1)` (so the perturbation direction is available at every triple point,
whose third parameter lies in `(0,1)`). -/
def betaG (s : ℝ) : ℝ := expNegInvGlue s * expNegInvGlue (1 - s)

@[simp] lemma betaG_zero : betaG 0 = 0 := by simp [betaG]

@[simp] lemma betaG_one : betaG 1 = 0 := by simp [betaG]

lemma betaG_pos {s : ℝ} (h0 : 0 < s) (h1 : s < 1) : 0 < betaG s := by
  exact mul_pos (expNegInvGlue.pos_of_pos h0) (expNegInvGlue.pos_of_pos (by linarith))

lemma betaG_nonneg_of_le {s : ℝ} (h : s ≤ 0) : betaG s = 0 := by
  simp only [betaG, expNegInvGlue]
  rw [if_pos h]
  ring

lemma betaG_nonneg_of_one_le {s : ℝ} (h : 1 ≤ s) : betaG s = 0 := by
  simp only [betaG, expNegInvGlue]
  rw [if_neg (not_le.mpr (by linarith : (0:ℝ) < s)), if_pos (by linarith : 1 - s ≤ 0)]
  ring

end

end Work.Drive
