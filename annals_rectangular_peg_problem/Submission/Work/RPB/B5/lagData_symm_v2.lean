import Mathlib
import Submission.Work.RPB.B5.LagData
import Submission.Work.RPB.B5.Defs
import Submission.Work.RPB.B2.chordSurf_period_swap

/-!
# B5: the `τ_π`-symmetry of the assembled family `ℓ = lagPt W Γc Ac rho` (current interface)

This is the same statement as `Work.RPB.B5.lagData_symm` in `Submission/Work/RPB/B5/lagData_symm.lean`,
but against the **current** interface `Work.RPB.B5.LagData CI a` (the one living in
`Submission/Work/RPB/B5/LagData.lean`, without the retracted `IsLevelData` parameter).

The family is `lagPt …τ x t = if x ≤ 0 then basePt …τ x t else tau π (basePt …τ (-x) (t-π))`,
i.e. the left half `x ≤ 0` is the "base" and the right half is `τ_π` of the reflected base.
With this definition the symmetry

`lagPt …τ (-x) (t+π) = tau π (lagPt …τ x t)`

holds for **all** `x`, which is the `symm` field of `Work.RPV.LagFamily`.

The two mathematical inputs are

* `basePt_add_two_pi`: the base half is `2π`-quasiperiodic in `t`,
  `base τ x (t+2π) = Tk 1 (base τ x t)` (from `hWper`/`hrhoper` on the chord chart and
  `hΓper`/`hAper` on the collar, using `levelPt u σ (a+2π) = Tk 1 (levelPt u σ a)`);
* `basePt_zero_swap`: at the middle chord `x = 0`, where the base is the chord chart at radius
  `ρ = π²/4`, i.e. the chord `chordSurf … τ t (π/2)`, one has
  `base τ 0 (t+π) = tau π (base τ 0 t)`: this is the chord-swap identity of `B2`
  (`chordSurf_period_swap`) with `r = π/2`, since `π - π/2 = π/2`.

With these, the case analysis is immediate: for `x < 0` both sides unfold to the *same* term
(the left-hand side lands in the `x > 0` branch, whose inner argument is `-(-x) = x` and whose
inner time is `(t+π)-π = t`); for `x = 0` it is `basePt_zero_swap`; for `x > 0` the left-hand side
is `base τ (-x) (t+π)` and the right-hand side reduces to `Tk 1 (base τ (-x) (t-π))` because
`tau π ∘ tau π = Tk 1`, so that `basePt_add_two_pi` finishes.

Nothing about `LagData` is used besides the fields `W`, `Γc`, `Ac`, `rho`, `hWchord`, `hWper`,
`hΓper`, `hAper`, `hrhoper` and `hrho0`.
-/

open RectangularPegProblem
open Manifold Complex Real
open scoped ContDiff

set_option autoImplicit false

noncomputable section

namespace Work.RPB.B5

/-! ## Elementary `PS`-algebra -/

/-- Shifting the phase of `levelPt` by `2π` is `Tk 1`: the reduced coordinate `e^{-ia} u` is
unchanged because `e^{-2πi} = 1`. -/
private theorem symmV2_levelPt_add_two_pi (u : ℂ) (σ a : ℝ) :
    Work.RPV.levelPt u σ (a + 2 * Real.pi) = Work.RPV.Tk 1 (Work.RPV.levelPt u σ a) := by
  have he : Complex.exp (-(((a + 2 * Real.pi : ℝ)) : ℂ) * Complex.I)
      = Complex.exp (-((a : ℝ) : ℂ) * Complex.I) := by
    rw [show -(((a + 2 * Real.pi : ℝ)) : ℂ) * Complex.I
        = -((a : ℝ) : ℂ) * Complex.I + (-1 : ℤ) * (2 * ↑Real.pi * Complex.I) by
      push_cast; ring,
      Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  simp only [Work.RPV.levelPt, Work.RPV.Tk, he, Int.cast_one]
  norm_num

/-- `tau (2π)` is `Tk 1`: the `2π`-rotation is the identity on the `(q₁,p₁)`-plane and shifts the
angle `q₂` by `2π`. -/
private theorem symmV2_tau_two_pi (x : Work.RPV.PS) :
    Work.RPV.tau (2 * Real.pi) x = Work.RPV.Tk 1 x := by
  simp only [Work.RPV.tau, Work.RPV.Tk, Real.cos_two_pi, Real.sin_two_pi, Int.cast_one,
    mul_one, mul_zero, sub_zero, zero_add]

/-- Two consecutive half turns `tau π` are a full `2π` shift, i.e. `Tk 1`. -/
private theorem symmV2_tau_pi_tau_pi (x : Work.RPV.PS) :
    Work.RPV.tau Real.pi (Work.RPV.tau Real.pi x) = Work.RPV.Tk 1 x := by
  rw [Work.RPV.tau_add]
  rw [show Real.pi + Real.pi = 2 * Real.pi by ring]
  exact symmV2_tau_two_pi x

/-! ## Unfolding `lagPt` and `basePt` -/

/-- On `x ≤ 0` the family is its base half. -/
private theorem symmV2_lagPt_of_nonpos (W : ℝ → ℝ → ℝ → Work.RPV.PS) (Γc : ℝ → ℝ → ℝ → ℂ)
    (Ac : ℝ → ℝ → ℝ → ℝ) (rho : ℝ → ℝ → ℝ → ℝ) {τ x t : ℝ} (hx : x ≤ 0) :
    lagPt W Γc Ac rho τ x t = basePt W Γc Ac rho τ x t := by
  rw [lagPt, ite_eq_left hx]

/-- On `x > 0` the family is `τ_π` of the reflected base half. -/
private theorem symmV2_lagPt_of_pos (W : ℝ → ℝ → ℝ → Work.RPV.PS) (Γc : ℝ → ℝ → ℝ → ℂ)
    (Ac : ℝ → ℝ → ℝ → ℝ) (rho : ℝ → ℝ → ℝ → ℝ) {τ x t : ℝ} (hx : 0 < x) :
    lagPt W Γc Ac rho τ x t =
      Work.RPV.tau Real.pi (basePt W Γc Ac rho τ (-x) (t - Real.pi)) := by
  rw [lagPt, ite_eq_right (not_le.mpr hx)]

/-! ## The base half: `2π`-quasiperiodicity and the swap at `x = 0` -/

/-- The base half is `2π`-quasiperiodic in `t`, for every `x` (the two branches of `basePt` are
handled separately: the collar via `hΓper`/`hAper` and `levelPt_add_two_pi`, the chord chart via
`hrhoper`/`hWper`). -/
private theorem symmV2_basePt_add_two_pi (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (D : LagData CI a) (τ x t : ℝ) :
    basePt D.W D.Γc D.Ac D.rho τ x (t + 2 * Real.pi)
      = Work.RPV.Tk 1 (basePt D.W D.Γc D.Ac D.rho τ x t) := by
  by_cases hxs : x ≤ -Real.sqrt 2
  · rw [basePt, ite_eq_left hxs, basePt, ite_eq_left hxs, collarPt, collarPt]
    rw [D.hΓper τ (sig x) t, D.hAper τ (sig x) t]
    exact symmV2_levelPt_add_two_pi _ _ _
  · rw [basePt, ite_eq_right hxs, basePt, ite_eq_right hxs, D.hrhoper τ x t]
    exact D.hWper τ t (D.rho τ x t)

/-- At the middle chord `x = 0` the base half is the chord chart at radius `π/2` and the chord is
its own `τ_π`-image: `base τ 0 (t+π) = tau π (base τ 0 t)`.  This is `chordSurf_period_swap` at
`r = π/2`, using `ρ(0) = π²/4` (`hrho0`). -/
private theorem symmV2_basePt_zero_swap (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (ha : Work.RPB.IsChordPhase CI.c a) (D : LagData CI a)
    (τ t : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    basePt D.W D.Γc D.Ac D.rho τ 0 (t + Real.pi)
      = Work.RPV.tau Real.pi (basePt D.W D.Γc D.Ac D.rho τ 0 t) := by
  have h0 : ¬ ((0 : ℝ) ≤ -Real.sqrt 2) := by
    have := Real.sqrt_pos_of_pos (by norm_num : (0 : ℝ) < 2)
    intro h; linarith
  rw [basePt, ite_eq_right h0, basePt, ite_eq_right h0]
  rw [D.hrho0 τ hτ (t + Real.pi), D.hrho0 τ hτ t]
  have hr : (Real.pi / 2) ∈ Set.Ioc (0 : ℝ) (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], le_refl _⟩
  have hsq : (Real.pi / 2) ^ 2 = Real.pi ^ 2 / 4 := by ring
  have hW1 : D.W τ t (Real.pi ^ 2 / 4) = Work.RPB.chordSurf CI.c a τ t (Real.pi / 2) := by
    have h := D.hWchord τ hτ t (Real.pi / 2) hr
    rwa [hsq] at h
  have hW2 : D.W τ (t + Real.pi) (Real.pi ^ 2 / 4)
      = Work.RPB.chordSurf CI.c a τ (t + Real.pi) (Real.pi / 2) := by
    have h := D.hWchord τ hτ (t + Real.pi) (Real.pi / 2) hr
    rwa [hsq] at h
  have hswap := (Work.RPB.B2.chordSurf_period_swap CI a ha).2 τ hτ t (Real.pi / 2)
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  rw [show Real.pi - Real.pi / 2 = Real.pi / 2 by ring] at hswap
  rw [hW2, hW1]
  exact hswap

/-! ## The symmetry -/

theorem lagData_symm_v2 (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (ha : Work.RPB.IsChordPhase CI.c a) (D : Work.RPB.B5.LagData CI a) :
    ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ x t,
      Work.RPB.B5.lagPt D.W D.Γc D.Ac D.rho τ (-x) (t + Real.pi)
        = Work.RPV.tau Real.pi (Work.RPB.B5.lagPt D.W D.Γc D.Ac D.rho τ x t) := by
  intro τ hτ x t
  rcases lt_trichotomy x 0 with hx | hx | hx
  · -- `x < 0`: the left-hand side lands in the right-hand branch, with argument `-(-x) = x`
    -- and time `(t+π)-π = t`, so both sides are literally `tau π (base τ x t)`.
    have hxpos : 0 < -x := by linarith
    rw [symmV2_lagPt_of_pos _ _ _ _ hxpos, symmV2_lagPt_of_nonpos _ _ _ _ (le_of_lt hx),
      neg_neg, show t + Real.pi - Real.pi = t by ring]
  · -- `x = 0`: the middle-chord swap.
    rw [hx, neg_zero]
    rw [symmV2_lagPt_of_nonpos _ _ _ _ (le_refl (0 : ℝ)),
      symmV2_lagPt_of_nonpos _ _ _ _ (le_refl (0 : ℝ))]
    exact symmV2_basePt_zero_swap CI a ha D τ t hτ
  · -- `x > 0`: the left-hand side is `base τ (-x) (t+π)`, the right-hand side reduces to
    -- `Tk 1 (base τ (-x) (t-π))` via `tau π ∘ tau π = Tk 1`, and `(t-π)+2π = t+π`.
    have hxneg : -x ≤ 0 := by linarith
    rw [symmV2_lagPt_of_nonpos _ _ _ _ hxneg, symmV2_lagPt_of_pos _ _ _ _ hx]
    have hper := symmV2_basePt_add_two_pi CI a D τ (-x) (t - Real.pi)
    rw [show t - Real.pi + 2 * Real.pi = t + Real.pi by ring] at hper
    rw [symmV2_tau_pi_tau_pi]
    exact hper

end Work.RPB.B5
