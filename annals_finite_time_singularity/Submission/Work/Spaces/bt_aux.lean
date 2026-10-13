import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HardyTheta
import Submission.Work.Spaces.HardyZ
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.HkSq_mixed_le
import Submission.Work.Spaces.mixed_comm
import Submission.Work.Spaces.pth_integral
import Submission.Work.Spaces.H_le_Wt
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.integral_sin_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Spaces

set_option autoImplicit false
set_option maxHeartbeats 8000000

/-! ## Pointwise algebra for the bad term -/

/-- `sin (2 θ) ≥ 0` for `θ ∈ Iθ`. -/
theorem bt_sin_nonneg {θ : ℝ} (hθ : θ ∈ Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- `(s ^ (-a/2)) ^ 2 = s ^ (-a)` for `s ≥ 0`, `a ≠ 0`. -/
theorem bt_rpow_sq (a s : ℝ) (hs : 0 ≤ s) (ha : a ≠ 0) :
    (s ^ (-(a / 2))) ^ 2 = s ^ (-a) := by
  have hne : -(a / 2) + -(a / 2) ≠ 0 := by
    have h : -(a / 2) + -(a / 2) = -a := by ring
    rw [h]; exact neg_ne_zero.mpr ha
  rw [pow_two, ← Real.rpow_add' hs hne]
  rw [show -(a / 2) + -(a / 2) = -a by ring]

/-- `(Wt α z θ)^2 = (w z)^2 * sin(2θ)^{-γ}`. -/
theorem bt_Wt_sq (α z θ : ℝ) (hα : 0 < α) (hθ : θ ∈ Iθ) :
    (Wt α z θ) ^ 2 = (w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α)) := by
  have hs := bt_sin_nonneg hθ
  have hgam : gam α ≠ 0 := by rw [gam]; linarith
  rw [Wt, wTheta, mul_pow, bt_rpow_sq (gam α) (Real.sin (2 * θ)) hs hgam]

/-- Factorisation of the bad term, in generic variables. -/
theorem bt_factor_gen (α z θ : ℝ) (hα : 0 < α) (hθ : θ ∈ Iθ) (A B : ℝ) :
    (A * B * Wt α z θ) ^ 2
      = (A ^ 2 * (w z) ^ 2) * (B ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α))) := by
  rw [mul_pow, mul_pow, bt_Wt_sq α z θ hα hθ]
  ring

/-- The pointwise factorisation of the bad term. -/
theorem bt_factor (α z θ : ℝ) (hα : 0 < α) (hθ : θ ∈ Iθ) (f g : ℝ → ℝ → ℝ) :
    (DzIter 3 f z θ * Dth g z θ * Wt α z θ) ^ 2
      = ((DzIter 3 f z θ) ^ 2 * (w z) ^ 2)
        * ((Dth g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α))) :=
  bt_factor_gen α z θ hα hθ (DzIter 3 f z θ) (Dth g z θ)

/-- `D_θ g = sin(2θ) ∂_θ g`. -/
theorem bt_Dth_eq (g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Dth g z θ = Real.sin (2 * θ) * pth g z θ := rfl

/-- `mixed 3 1 f = sin(2θ) ∂_θ (D_z^3 f)` on the domain. -/
theorem bt_mixed_three_one {f : ℝ → ℝ → ℝ} (hf : SmoothNbhd f) {z θ : ℝ}
    (hz : z ∈ Iz) (hθ : θ ∈ Iθ) :
    mixed 3 1 f z θ = Real.sin (2 * θ) * pth (DzIter 3 f) z θ := by
  have hy : (z, θ) ∈ nbhU := mem_nbhU hz hθ
  have hc : DthIter 1 (DzIter 3 f) z θ = DzIter 3 (DthIter 1 f) z θ := by
    have h := DthIter_DzIter_comm_eqOn hf 3 1 hy
    simpa [Function.uncurry] using h
  show DzIter 3 (DthIter 1 f) z θ = Real.sin (2 * θ) * pth (DzIter 3 f) z θ
  rw [← hc]
  rfl

/-- `mixed 1 1 g = D_z D_θ g`. -/
theorem bt_mixed_one_one (g : ℝ → ℝ → ℝ) : mixed 1 1 g = Dz (Dth g) := rfl

/-- The weight identity behind the `θ`-Hardy estimate, in generic variables. -/
theorem bt_mixed_weight_gen (α z θ : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hθ : θ ∈ Iθ)
    (A C : ℝ) (hAC : C = Real.sin (2 * θ) * A) :
    A ^ 2 * (w z) ^ 2 * (Real.sin (2 * θ)) ^ (2 - gam α) = (C * Wt α z θ) ^ 2 := by
  have hs := bt_sin_nonneg hθ
  have hne1 : (1 : ℝ) + (1 - gam α) ≠ 0 := by
    have h : (1 : ℝ) + (1 - gam α) = 2 - gam α := by ring
    rw [h, gam]; intro hh; linarith
  have hne2 : (1 : ℝ) + (-(gam α)) ≠ 0 := by
    have h : (1 : ℝ) + (-(gam α)) = 1 - gam α := by ring
    rw [h, gam]; intro hh; linarith
  have hkey : (Real.sin (2 * θ)) ^ (2 - gam α)
      = (Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α)) := by
    rw [show (2 : ℝ) - gam α = 1 + (1 - gam α) by ring]
    rw [Real.rpow_add' hs hne1]
    rw [show (1 : ℝ) - gam α = 1 + (-(gam α)) by ring]
    rw [Real.rpow_add' hs hne2]
    simp only [Real.rpow_one]
    ring
  rw [hAC, hkey, mul_pow, mul_pow, bt_Wt_sq α z θ hα hθ]
  ring

/-- The weight identity behind the `θ`-Hardy estimate. -/
theorem bt_mixed_weight_id {f : ℝ → ℝ → ℝ} (hf : SmoothNbhd f) (α z θ : ℝ) (hα : 0 < α)
    (hα1 : α ≤ 1) (hz : z ∈ Iz) (hθ : θ ∈ Iθ) :
    (pth (DzIter 3 f) z θ) ^ 2 * (w z) ^ 2 * (Real.sin (2 * θ)) ^ (2 - gam α)
      = (mixed 3 1 f z θ * Wt α z θ) ^ 2 :=
  bt_mixed_weight_gen α z θ hα hα1 hθ (pth (DzIter 3 f) z θ) (mixed 3 1 f z θ)
    (bt_mixed_three_one hf hz hθ)

/-- `VanishTheta` is preserved by `D_z`-derivatives. -/
theorem bt_DzIter_vanish {f : ℝ → ℝ → ℝ} (h : VanishTheta f) (n : ℕ) :
    (∀ z : ℝ, DzIter n f z 0 = 0) ∧ (∀ z : ℝ, DzIter n f z (π / 2) = 0) := by
  constructor
  · induction n with
    | zero => intro z; exact h.1 z
    | succ m ih =>
        intro z
        rw [DzIter_succ, Dz]
        have hfun : (fun z' => DzIter m f z' 0) = fun _ => (0 : ℝ) := funext ih
        rw [pz, hfun]
        simp
  · induction n with
    | zero => intro z; exact h.2 z
    | succ m ih =>
        intro z
        rw [DzIter_succ, Dz]
        have hfun : (fun z' => DzIter m f z' (π / 2)) = fun _ => (0 : ℝ) := funext ih
        rw [pz, hfun]
        simp

end Work.Spaces
