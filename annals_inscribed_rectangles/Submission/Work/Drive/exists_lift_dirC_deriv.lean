import Mathlib
import Submission.Work.Drive.OrderBase
import Submission.Work.Drive.Interfaces

namespace Work.Drive

/-! # Guidance (parent agent `orderSplit_chains`) — exists_lift_dirC_deriv

Hopf's Umlaufsatz (the hypothesis `hU : UmlaufProp`) is the input of the whole project that says that the
tangent of a smooth embedded closed plane curve turns exactly once.  For the geometric core we need its
consequence that the *doubled* direction `dirC (γ')` winds exactly **twice** around `ℝ/ℤ`:

`Submission.Drive.UmlaufProp` supplies, for `γ` and `hγ`, functions `θ, ρ : ℝ → ℝ` and `ε ∈ {1,-1}`
with `ρ > 0`, `θ` continuous,
`deriv (fun s => γ (Circle.exp s)) t = ρ t • (Real.cos (θ t), Real.sin (θ t))` and
`θ (t + 2π) - θ t = 2 π ε`.  Take `φ := θ / π`:

* `(φ t : ℝ/ℤ) = dirC (deriv (fun s => γ (Circle.exp s)) t)`: rewrite the derivative as
  `ρ t • (cos (θ t), sin (θ t))`, use `dirC (c • p) = dirC p` for `c > 0`
  (`Submission.Configuration.dirC_smul_pos`), and then the only real content of this statement is the
  trigonometric identification `dirC (Real.cos θ, Real.sin θ) = ((θ / π : ℝ) : UnitAddCircle)`.
  Prove that identification e.g. via `Complex.arg_exp_mul_I`
  (`(Complex.exp (θ * I)).arg = Real.toIocMod Real.two_pi_pos (-π) θ`, which differs from `θ` by a
  multiple of `2π`; dividing by `π` shows the two classes agree in `ℝ/ℤ`), or via the multiplicative
  picture `AddCircle.toCircle` (where `dirC v` is the class whose image is `(v/‖v‖)²`).
* `φ (t + 2π) - φ t = (2 π ε)/π = 2 ε` for every `t`, so the global increment `k := 2 ε` works (this is
  stronger than the per-`t` disjunction and is what `hU` gives directly).

This is exactly the statement that the boundary of the configuration Möbius strip, namely
`{(γ x, dirC (γ' x), 0)}`, makes two full turns in the `ℝ/ℤ` coordinate, i.e. that it is the `(2,1)`
torus knot `T(2,1) × {0}` in the notation of the paper.  It is the input the capping construction needs;
see `Submission/Work/Drive/CHAIN_ROUTE_NOTES.md`.-/

open Manifold in
open scoped Manifold ContDiff in
/-- The doubled direction of the unit vector `(cos θ, sin θ)` is the class of `θ / π` in `ℝ/ℤ`.

This is the trigonometric content of the Umlaufsatz normal form: the direction *modulo sign* of the
unit vector at angle `θ` is the angle `2θ`, and `2θ / (2π) = θ / π` in `ℝ/ℤ`. -/
theorem dirC_cos_sin (θ : ℝ) :
    Submission.Collision.dirC (Real.cos θ, Real.sin θ) = ((θ / Real.pi : ℝ) : UnitAddCircle) := by
  unfold Submission.Collision.dirC
  -- identify `(cos θ, sin θ)` with the complex exponential `exp (θ * I)`
  have hz : (⟨Real.cos θ, Real.sin θ⟩ : ℂ) = Complex.exp ((θ : ℂ) * Complex.I) := by
    rw [Complex.exp_mul_I]
    apply Complex.ext
    · simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.cos_ofReal_re,
        Complex.sin_ofReal_im, mul_one, mul_zero, sub_zero, add_zero]
    · simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.sin_ofReal_re,
        Complex.cos_ofReal_im, mul_one, mul_zero, add_zero, zero_add]
  rw [hz, Complex.arg_exp_mul_I]
  -- `toIocMod (-π) θ` differs from `θ` by an integer multiple of `2π`, hence `toIocMod θ / π` differs
  -- from `θ / π` by an integer, i.e. the two classes in `ℝ/ℤ` agree.
  have hkey : toIocMod Real.two_pi_pos (-Real.pi) θ / Real.pi - θ / Real.pi
      = ((-(2 * toIocDiv Real.two_pi_pos (-Real.pi) θ) : ℤ) : ℝ) := by
    rw [div_sub_div_same, toIocMod_sub_self Real.two_pi_pos (-Real.pi) θ, zsmul_eq_mul]
    push_cast
    field_simp
  have h0 : (((toIocMod Real.two_pi_pos (-Real.pi) θ / Real.pi - θ / Real.pi : ℝ)) :
      UnitAddCircle) = 0 := by
    rw [hkey, AddCircle.coe_eq_zero_iff]
    exact ⟨-(2 * toIocDiv Real.two_pi_pos (-Real.pi) θ), by simp [zsmul_eq_mul]⟩
  rw [AddCircle.coe_sub] at h0
  exact sub_eq_zero.mp h0

open Manifold in
open scoped Manifold ContDiff in
/-- Hopf's Umlaufsatz, in the form needed for the geometry: the doubled tangent direction of a smooth
embedded closed plane curve has a continuous lift whose total change over a period is `±2`. -/
theorem exists_lift_dirC_deriv (hU : Submission.Drive.UmlaufProp) (γ : Circle → ℝ × ℝ)
    (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ∞ γ) :
    ∃ (φ : ℝ → ℝ) (k : ℤ), (k = 2 ∨ k = -2) ∧ Continuous φ ∧
      (∀ t, ((φ t : ℝ) : UnitAddCircle) =
        Submission.Collision.dirC (deriv (fun s => γ (Circle.exp s)) t)) ∧
      (∀ t, φ (t + 2 * Real.pi) - φ t = k) := by
  obtain ⟨θ, ρ, ε, hε, hθcont, hρpos, hderiv, hper⟩ := hU γ hγ
  refine ⟨fun t => θ t / Real.pi, 2 * ε, ?_, ?_, ?_, ?_⟩
  · rcases hε with h | h <;> rw [h] <;> norm_num
  · exact hθcont.div_const _
  · intro t
    rw [hderiv t, Submission.Configuration.dirC_smul_pos (hρpos t)]
    exact (dirC_cos_sin (θ t)).symm
  · intro t
    have h := hper t
    show θ (t + 2 * Real.pi) / Real.pi - θ t / Real.pi = ((2 * ε : ℤ) : ℝ)
    rw [div_sub_div_same, h]
    push_cast
    field_simp

end Work.Drive
