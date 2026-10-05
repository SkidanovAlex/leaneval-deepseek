import Mathlib
import Submission.Work.RPA3.TubularDefs
import Submission.Work.RPA3.Symp
import Submission.Work.RPA3.theta_per
import Submission.Work.RPA3.theta_std
import Submission.Work.RPA3.contDiff_thetaP

/-!
# RPA3: vocabulary and elementary algebra for `theta_injective_compact`

This file collects the definitions and the elementary `Tk`-algebra (translation of the angle `q₂`)
that the proof of `Work.RPA3.theta_injective_compact` needs, so that the individual lemmas can be
stated in a common vocabulary.

`InjUpTo L ε'` is the conclusion of `theta_injective_compact` for a fixed radius `ε'`: the tubular
map `theta` is injective on the compact strip `τ ∈ [0,1]`, `|x| ≤ X₀+1`, `t ∈ [0,2π]`,
`‖ξ‖ < ε'`, up to the periodicity of the angle.
-/

open scoped ContDiff

set_option autoImplicit false
noncomputable section

namespace Work.RPA3

/-- The "injectivity up to periodicity" property of the tubular map on the compact strip: for
`τ ∈ [0,1]`, `|x| ≤ X₀+1`, `t ∈ [0,2π]` and `‖ξ‖ < ε'`, the equation
`theta τ x t ξ = Tk k (theta τ x' t' ξ')` forces `x = x'`, `ξ = ξ'` and
`t' = t + 2πm` for some `m : ℤ`. -/
def InjUpTo (L : LagFamilyAll) (ε' : ℝ) : Prop :=
  ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ x t x' t' (ξ ξ' : ℝ × ℝ), |x| ≤ L.X0 + 1 → |x'| ≤ L.X0 + 1 →
    t ∈ Set.Icc 0 (2 * Real.pi) → t' ∈ Set.Icc 0 (2 * Real.pi) → ‖ξ‖ < ε' → ‖ξ'‖ < ε' →
    ∀ k : ℤ, theta L τ x t ξ = Tk k (theta L τ x' t' ξ') →
    (x = x' ∧ ξ = ξ' ∧ ∃ m : ℤ, t' = t + 2 * Real.pi * m)

/-! ## The angle translation `Tk` -/

@[simp] theorem Tk_zero (z : PS) : Tk 0 z = z := by
  ext <;> simp [Tk]

theorem Tk_add (k l : ℤ) (z : PS) : Tk (k + l) z = Tk k (Tk l z) := by
  ext <;> simp [Tk] <;> push_cast <;> ring

@[simp] theorem Tk_fst_fst (k : ℤ) (z : PS) : (Tk k z).1.1 = z.1.1 := rfl

@[simp] theorem Tk_fst_snd (k : ℤ) (z : PS) : (Tk k z).1.2 = z.1.2 + 2 * Real.pi * k := rfl

@[simp] theorem Tk_snd (k : ℤ) (z : PS) : (Tk k z).2 = z.2 := rfl

@[simp] theorem Tk_neg_apply (k : ℤ) (z : PS) : Tk (-k) (Tk k z) = z := by
  rw [← Tk_add, neg_add_cancel, Tk_zero]

theorem Tk_injective (k : ℤ) : Function.Injective (Tk k) := by
  intro z w h
  have h' : Tk (-k) (Tk k z) = Tk (-k) (Tk k w) := by rw [h]
  rwa [Tk_neg_apply, Tk_neg_apply] at h'

theorem continuous_Tk (k : ℤ) : Continuous (Tk k) := by
  unfold Tk
  fun_prop

/-- Equality after `Tk k` is a genuine equality of points: the angular coordinate changes by
`2πk`, so `Tk k z = z` only for `k = 0`. -/
theorem Tk_eq_self_iff (k : ℤ) (z : PS) : Tk k z = z ↔ k = 0 := by
  constructor
  · intro h
    have h2 : z.1.2 + 2 * Real.pi * k = z.1.2 := by
      simpa using congrArg (fun p : PS => p.1.2) h
    have h3 : 2 * Real.pi * (k : ℝ) = 0 := by linarith
    have hπ : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    have hk : (k : ℝ) = 0 := by
      rcases mul_eq_zero.mp h3 with h | h
      · exact absurd h hπ
      · exact h
    exact_mod_cast hk
  · intro h; subst h; simp

/-! ## Continuity of the tubular map in the point variable -/

/-- `theta`, viewed as a function of `w = (τ, (x,t,ξ))`, is continuous — indeed `C⁷`. -/
theorem continuous_thetaZ (L : LagFamilyAll) : Continuous (fun w : ℝ × PS => thetaZ L w.1 w.2) :=
  (contDiff_thetaZ L).continuous

/-- The second component of `thetaP` in the coordinates of `theta`. -/
theorem thetaP_snd_eq (L : LagFamilyAll) (w : ℝ × PS) :
    (thetaP L w).2 = thetaZ L w.1 w.2 := rfl

/-- `theta` at `ξ = 0` is the family itself, in the `0 : ℝ × ℝ` spelling. -/
theorem theta_zero_zero (L : LagFamilyAll) (τ x t : ℝ) :
    theta L τ x t (0 : ℝ × ℝ) = L.ℓ τ (x, t) := theta_zero L τ x t

end Work.RPA3
