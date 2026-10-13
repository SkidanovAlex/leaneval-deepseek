/-
# `Work.FTS.EllExist.RadGreenDefs` — the explicit building blocks of `radGreen`

The radial Green function of the mode `m` is

  `radGreen α m c z = K · (z^{-q} ∫_0^z c t^{q-1} dt + z^{p} ∫_z^∞ c t^{-p-1} dt)`

with `K = 1/(α(4m+5))`, `q = (2m+5)/α` and `p = 2m/α` (`Work.FTS.PhiStar.Radial.radGreen`, the
parenthesised/intended definition).  This module names the pieces (`rgK`, `rgQ`, `rgP`, `rgF1`,
`rgF2`, `rgA`, `rgB`, `rgG1`, `rgG2`, `rgD1`, `rgD2`) and records their elementary arithmetic,
together with the key reduction

  `z^2 · rgD2 z = rgK(q(q+1)·rgG1 z + p(p-1)·rgG2 z) - c z / α^2`   (`z > 0`),

which exhibits `z^2 ∂_z^2 radGreen` as the sum of the two indicial branches and the source term.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.PhiStar.Radial.Defs
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllExist

set_option autoImplicit false

/-- The normalising constant `1/(α(4m+5))` of `radGreen`. -/
def rgK (α : ℝ) (m : ℕ) : ℝ := 1 / (α * (4 * (m : ℝ) + 5))

/-- The positively oriented decaying indicial exponent `q = (2m+5)/α` (so `s⁻ = -q`). -/
def rgQ (α : ℝ) (m : ℕ) : ℝ := (2 * (m : ℝ) + 5) / α

/-- The growing indicial exponent `p = 2m/α`. -/
def rgP (α : ℝ) (m : ℕ) : ℝ := 2 * (m : ℝ) / α

/-- The integrand `c t · t^{q-1}` of the forward primitive. -/
def rgF1 (α : ℝ) (m : ℕ) (c : ℝ → ℝ) : ℝ → ℝ := fun t => c t * t ^ (rgQ α m - 1)

/-- The integrand `c t · t^{-p-1}` of the tail primitive. -/
def rgF2 (α : ℝ) (m : ℕ) (c : ℝ → ℝ) : ℝ → ℝ := fun t => c t * t ^ (-(rgP α m) - 1)

/-- The forward primitive `z ↦ ∫_0^z c t^{q-1} dt`. -/
def rgA (α : ℝ) (m : ℕ) (c : ℝ → ℝ) : ℝ → ℝ := fun z => ∫ t in (0 : ℝ)..z, rgF1 α m c t

/-- The tail primitive `z ↦ ∫_{Ioi z} c t^{-p-1} dt`. -/
def rgB (α : ℝ) (m : ℕ) (c : ℝ → ℝ) : ℝ → ℝ := fun z => ∫ t in Set.Ioi z, rgF2 α m c t

/-- The decaying branch `g₁ = z^{-q} rgA`. -/
def rgG1 (α : ℝ) (m : ℕ) (c : ℝ → ℝ) : ℝ → ℝ := fun z => z ^ (-(rgQ α m)) * rgA α m c z

/-- The growing branch `g₂ = z^{p} rgB`. -/
def rgG2 (α : ℝ) (m : ℕ) (c : ℝ → ℝ) : ℝ → ℝ := fun z => z ^ (rgP α m) * rgB α m c z

/-- The explicit first derivative of `radGreen α m c` on `(0,∞)`. -/
def rgD1 (α : ℝ) (m : ℕ) (c : ℝ → ℝ) : ℝ → ℝ := fun z =>
  rgK α m * (-(rgQ α m) * z ^ (-(rgQ α m) - 1) * rgA α m c z
    + rgP α m * z ^ (rgP α m - 1) * rgB α m c z)

/-- The explicit second derivative of `radGreen α m c` on `(0,∞)`. -/
def rgD2 (α : ℝ) (m : ℕ) (c : ℝ → ℝ) : ℝ → ℝ := fun z =>
  rgK α m * (rgQ α m * (rgQ α m + 1) * z ^ (-(rgQ α m) - 2) * rgA α m c z
    + rgP α m * (rgP α m - 1) * z ^ (rgP α m - 2) * rgB α m c z
    - rgQ α m * z ^ (-(rgQ α m) - 1) * rgF1 α m c z
    - rgP α m * z ^ (rgP α m - 1) * rgF2 α m c z)

/-- `radGreen` is definitionally the expression in terms of the named pieces. -/
theorem radGreen_eq (α : ℝ) (m : ℕ) (c : ℝ → ℝ) (z : ℝ) :
    Work.FTS.PhiStar.Radial.radGreen α m c z
      = rgK α m * (z ^ (-(rgQ α m)) * rgA α m c z + z ^ (rgP α m) * rgB α m c z) := by
  simp only [Work.FTS.PhiStar.Radial.radGreen, rgK, rgQ, rgP, rgA, rgB, rgF1, rgF2, neg_div]

theorem radGreen_eq_fun (α : ℝ) (m : ℕ) (c : ℝ → ℝ) :
    Work.FTS.PhiStar.Radial.radGreen α m c
      = fun z => rgK α m * (z ^ (-(rgQ α m)) * rgA α m c z
          + z ^ (rgP α m) * rgB α m c z) := by
  funext z
  rw [radGreen_eq]

theorem rgK_pos {α : ℝ} (hα : 0 < α) (m : ℕ) : 0 < rgK α m := by
  rw [rgK]
  positivity

theorem rgQ_pos {α : ℝ} (hα : 0 < α) (m : ℕ) : 0 < rgQ α m := by
  rw [rgQ]
  have h : (0 : ℝ) < 2 * (m : ℝ) + 5 := by positivity
  exact div_pos h hα

theorem rgP_nonneg {α : ℝ} (hα : 0 < α) (m : ℕ) : 0 ≤ rgP α m := by
  rw [rgP]
  positivity

theorem rgP_pos {α : ℝ} (hα : 0 < α) {m : ℕ} (hm : 1 ≤ m) : 0 < rgP α m := by
  rw [rgP]
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  positivity

/-- `q ≥ 28` for `m ≥ 1` and `α ≤ 1/4`. -/
theorem rgQ_ge {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) {m : ℕ} (hm : 1 ≤ m) :
    28 ≤ rgQ α m := by
  rw [rgQ, le_div_iff₀ hα]
  have hm' : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  nlinarith

/-- `p ≥ 8` for `m ≥ 1` and `α ≤ 1/4`. -/
theorem rgP_ge {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) {m : ℕ} (hm : 1 ≤ m) :
    8 ≤ rgP α m := by
  rw [rgP, le_div_iff₀ hα]
  have hm' : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  nlinarith

theorem rgP_add_rgQ {α : ℝ} (hα : 0 < α) (m : ℕ) :
    rgP α m + rgQ α m = (4 * (m : ℝ) + 5) / α := by
  rw [rgP, rgQ]
  field_simp
  ring

/-- `K·(p+q) = 1/α²`: the coefficient of the source term in `z²∂_z² radGreen`. -/
theorem rgK_mul_add {α : ℝ} (hα : 0 < α) (m : ℕ) :
    rgK α m * (rgP α m + rgQ α m) = 1 / α ^ 2 := by
  rw [rgK, rgP_add_rgQ hα]
  field_simp

/-- The key reduction: for `z > 0`, `z² ∂_z² radGreen` is the sum of the two indicial branches
minus the source term `c z / α²`. -/
theorem zsq_rgD2 {α : ℝ} (hα : 0 < α) (m : ℕ) (c : ℝ → ℝ) {z : ℝ} (hz : 0 < z) :
    z ^ 2 * rgD2 α m c z
      = rgK α m * (rgQ α m * (rgQ α m + 1) * rgG1 α m c z
          + rgP α m * (rgP α m - 1) * rgG2 α m c z) - c z / α ^ 2 := by
  -- convert the natural power `z ^ 2` into a real power so that `Real.rpow_add` applies
  rw [show z ^ 2 = z ^ (2 : ℝ) from (Real.rpow_natCast z 2).symm]
  have hcomb1 : z ^ (2 : ℝ) * z ^ (-(rgQ α m) - 2) = z ^ (-(rgQ α m)) := by
    rw [← Real.rpow_add hz, show (2 : ℝ) + (-(rgQ α m) - 2) = -(rgQ α m) from by ring]
  have hcomb2 : z ^ (2 : ℝ) * z ^ (rgP α m - 2) = z ^ (rgP α m) := by
    rw [← Real.rpow_add hz, show (2 : ℝ) + (rgP α m - 2) = rgP α m from by ring]
  have hcomb3 : z ^ (-(rgQ α m) - 1) * z ^ (rgQ α m - 1) = z ^ (-2 : ℝ) := by
    rw [← Real.rpow_add hz, show (-(rgQ α m) - 1) + (rgQ α m - 1) = -2 from by ring]
  have hcomb4 : z ^ (rgP α m - 1) * z ^ (-(rgP α m) - 1) = z ^ (-2 : ℝ) := by
    rw [← Real.rpow_add hz, show (rgP α m - 1) + (-(rgP α m) - 1) = -2 from by ring]
  have hcomb0 : z ^ (2 : ℝ) * z ^ (-2 : ℝ) = (1 : ℝ) := by
    rw [← Real.rpow_add hz, show (2 : ℝ) + (-2) = 0 from by ring, Real.rpow_zero]
  have hA : z ^ (2 : ℝ) * (rgQ α m * (rgQ α m + 1) * z ^ (-(rgQ α m) - 2) * rgA α m c z)
      = rgQ α m * (rgQ α m + 1) * (z ^ (-(rgQ α m)) * rgA α m c z) := by
    rw [show z ^ (2 : ℝ) * (rgQ α m * (rgQ α m + 1) * z ^ (-(rgQ α m) - 2) * rgA α m c z)
        = rgQ α m * (rgQ α m + 1) * (z ^ (2 : ℝ) * z ^ (-(rgQ α m) - 2)) * rgA α m c z
        from by ring, hcomb1]
    ring
  have hB : z ^ (2 : ℝ) * (rgP α m * (rgP α m - 1) * z ^ (rgP α m - 2) * rgB α m c z)
      = rgP α m * (rgP α m - 1) * (z ^ (rgP α m) * rgB α m c z) := by
    rw [show z ^ (2 : ℝ) * (rgP α m * (rgP α m - 1) * z ^ (rgP α m - 2) * rgB α m c z)
        = rgP α m * (rgP α m - 1) * (z ^ (2 : ℝ) * z ^ (rgP α m - 2)) * rgB α m c z
        from by ring, hcomb2]
    ring
  have hC : z ^ (2 : ℝ) * (rgQ α m * z ^ (-(rgQ α m) - 1) * (c z * z ^ (rgQ α m - 1)))
      = rgQ α m * c z := by
    rw [show z ^ (2 : ℝ) * (rgQ α m * z ^ (-(rgQ α m) - 1) * (c z * z ^ (rgQ α m - 1)))
        = rgQ α m * (z ^ (2 : ℝ) * (z ^ (-(rgQ α m) - 1) * z ^ (rgQ α m - 1))) * c z
        from by ring, hcomb3, hcomb0]
    ring
  have hD : z ^ (2 : ℝ) * (rgP α m * z ^ (rgP α m - 1) * (c z * z ^ (-(rgP α m) - 1)))
      = rgP α m * c z := by
    rw [show z ^ (2 : ℝ) * (rgP α m * z ^ (rgP α m - 1) * (c z * z ^ (-(rgP α m) - 1)))
        = rgP α m * (z ^ (2 : ℝ) * (z ^ (rgP α m - 1) * z ^ (-(rgP α m) - 1))) * c z
        from by ring, hcomb4, hcomb0]
    ring
  have hK := rgK_mul_add hα m
  simp only [rgD2, rgG1, rgG2, rgF1, rgF2]
  rw [show z ^ (2 : ℝ) * (rgK α m * (rgQ α m * (rgQ α m + 1) * z ^ (-(rgQ α m) - 2) * rgA α m c z
        + rgP α m * (rgP α m - 1) * z ^ (rgP α m - 2) * rgB α m c z
        - rgQ α m * z ^ (-(rgQ α m) - 1) * (c z * z ^ (rgQ α m - 1))
        - rgP α m * z ^ (rgP α m - 1) * (c z * z ^ (-(rgP α m) - 1))))
      = rgK α m * (z ^ (2 : ℝ) * (rgQ α m * (rgQ α m + 1) * z ^ (-(rgQ α m) - 2) * rgA α m c z)
        + z ^ (2 : ℝ) * (rgP α m * (rgP α m - 1) * z ^ (rgP α m - 2) * rgB α m c z)
        - z ^ (2 : ℝ) * (rgQ α m * z ^ (-(rgQ α m) - 1) * (c z * z ^ (rgQ α m - 1)))
        - z ^ (2 : ℝ) * (rgP α m * z ^ (rgP α m - 1) * (c z * z ^ (-(rgP α m) - 1))))
      from by ring]
  rw [hA, hB, hC, hD]
  rw [show rgK α m * (rgQ α m * (rgQ α m + 1) * (z ^ (-(rgQ α m)) * rgA α m c z)
        + rgP α m * (rgP α m - 1) * (z ^ (rgP α m) * rgB α m c z)
        - rgQ α m * c z - rgP α m * c z)
      = rgK α m * (rgQ α m * (rgQ α m + 1) * (z ^ (-(rgQ α m)) * rgA α m c z)
        + rgP α m * (rgP α m - 1) * (z ^ (rgP α m) * rgB α m c z))
        - rgK α m * (rgP α m + rgQ α m) * c z from by ring]
  rw [hK]
  ring

end Work.FTS.EllExist
