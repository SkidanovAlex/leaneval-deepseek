import Mathlib
import Submission.Work.Drive.CappingDefs
import Submission.Work.Drive.CappingSpace
import Submission.Work.Drive.position_angle_lift

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff

/-- The circle-valued polar angle of `CappingDefs`, read in `ℂ`, is the exponential of `2πiψ`.  This is
the bridge between the abstract `circleOf` of the capping and the concrete `cos`/`sin` of
`polarLift`. -/
lemma circleOf_coe_eq (ψ : ℝ) :
    circleOf ((ψ : ℝ) : UnitAddCircle) =
      Complex.exp (((2 * Real.pi * ψ : ℝ) : ℂ) * Complex.I) := by
  show ((AddCircle.homeomorphCircle (T := 1) one_ne_zero) ((ψ : ℝ) : UnitAddCircle) : ℂ) = _
  rw [AddCircle.homeomorphCircle_apply, AddCircle.toCircle_apply_mk, Circle.coe_exp]
  rw [show 2 * Real.pi / (1 : ℝ) * ψ = 2 * Real.pi * ψ by ring]

/-- `polarLift` depends on the angle only through `circleOf`: equal circle-valued angles and equal
radii give equal polar lifts.  Concretely, `circleOf ↑ψ = circleOf ↑ψ'` gives
`cos (2πψ) = cos (2πψ')` and `sin (2πψ) = sin (2πψ')`, and `polarLift` is
`(r cos (2πψ), r sin (2πψ))`. -/
lemma polarLift_eq_of_circleOf_eq {r r' ψ ψ' : ℝ}
    (hr : r = r') (h : circleOf ((ψ:ℝ):UnitAddCircle) = circleOf ((ψ':ℝ):UnitAddCircle)) :
    polarLift (r, ψ) = polarLift (r', ψ') := by
  have h' : Complex.exp (((2*Real.pi*ψ : ℝ):ℂ) * Complex.I) =
            Complex.exp (((2*Real.pi*ψ' : ℝ):ℂ) * Complex.I) := by
    rw [← circleOf_coe_eq, ← circleOf_coe_eq, h]
  have hcos : Real.cos (2*Real.pi*ψ) = Real.cos (2*Real.pi*ψ') := by
    have hh := congrArg Complex.re h'
    rwa [Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_re] at hh
  have hsin : Real.sin (2*Real.pi*ψ) = Real.sin (2*Real.pi*ψ') := by
    have hh := congrArg Complex.im h'
    rwa [Complex.exp_ofReal_mul_I_im, Complex.exp_ofReal_mul_I_im] at hh
  rw [polarLift, polarLift, hr, hcos, hsin]

open Manifold in
open scoped Manifold ContDiff in
/-- The cap disks of the capping are pairwise disjoint.  For a smooth embedded curve `γ` avoiding `0`, a polar lift `(ρ, Ψ)` of the position vector and a continuous periodic lift `Θ` of the first coordinate `θ = arg²(γ') - 2 Ψ` of the band boundary, the points `((1 - s) * r₀ + s * ρ t, (Θ 0 + s * (Θ t - Θ 0) : ℝ/ℤ) + u, s * circleOf (Ψ t))` of `ℝ × ℝ/ℤ × ℂ` form, as `u ∈ ℝ/ℤ` varies, a pairwise disjoint family of cones: if the points for `(u, s, t)` and `(v, s', t')` with `s, s' ∈ [0,1]` coincide then `u = v` and `s = s'`.  This is what makes the capped planes `P_u = u·M ∪ cap_u` disjoint for `v - u ∈ Zc γ`, the hypothesis of Hugelmeyer's Theorem 2.

Proof route: the third coordinate has norm `s`, so `s = s'`, and `s = 0` gives `u = v` directly from the
second coordinate.  For `s > 0` the first coordinate gives `ρ t = ρ t'` and the third gives
`circleOf (Ψ t) = circleOf (Ψ t')`; since `polarLift (r, ψ) = (r cos 2πψ, r sin 2πψ)` descends through
`circleOf`, `hpolar` gives `γ (Circle.exp t) = γ (Circle.exp t')`, injectivity of `γ` gives
`t = t' + 2π k`, and the `2π`-periodicity `hΘper` of `Θ` gives `Θ t = Θ t'`, whence the second
coordinate gives `u = v`. -/
theorem capDisks_disjoint {γ : Circle → ℝ × ℝ}
    (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ∞ γ) (h0 : ∀ x : Circle, γ x ≠ 0)
    {ρ Ψ : ℝ → ℝ} (hρ : Continuous ρ) (hΨ : Continuous Ψ) (hρpos : ∀ t, 0 < ρ t)
    (hpolar : ∀ t, polarLift (ρ t, Ψ t) = γ (Circle.exp t))
    (hΨper : ∀ t, circleOf (Ψ (t + 2 * Real.pi)) = circleOf (Ψ t))
    {Θ : ℝ → ℝ} (hΘ : Continuous Θ) (hΘper : ∀ t, Θ (t + 2 * Real.pi) = Θ t)
    {r₀ : ℝ} (hr₀pos : 0 < r₀) (hr₀ : ∀ t, ρ t ≠ r₀) :
    ∀ (u v : UnitAddCircle) (s s' t t' : ℝ),
      s ∈ Set.Icc (0 : ℝ) 1 → s' ∈ Set.Icc (0 : ℝ) 1 →
      ((1 - s) * r₀ + s * ρ t,
        (((Θ 0 + s * (Θ t - Θ 0) : ℝ) : UnitAddCircle) + u),
        (s : ℂ) * circleOf (Ψ t))
      = ((1 - s') * r₀ + s' * ρ t',
        (((Θ 0 + s' * (Θ t' - Θ 0) : ℝ) : UnitAddCircle) + v),
        (s' : ℂ) * circleOf (Ψ t')) →
      u = v ∧ s = s' := by
  intro u v s s' t t' hs hs' heq
  have h1 : (1 - s) * r₀ + s * ρ t = (1 - s') * r₀ + s' * ρ t' := by
    simpa using congrArg Prod.fst heq
  have h2 : (((Θ 0 + s * (Θ t - Θ 0) : ℝ) : UnitAddCircle) + u) =
            (((Θ 0 + s' * (Θ t' - Θ 0) : ℝ) : UnitAddCircle) + v) := by
    simpa using congrArg (fun p : ℝ × UnitAddCircle × ℂ => p.2.1) heq
  have h3 : (s : ℂ) * circleOf (Ψ t) = (s' : ℂ) * circleOf (Ψ t') := by
    simpa using congrArg (fun p : ℝ × UnitAddCircle × ℂ => p.2.2) heq
  -- the third coordinate has norm `s`, which is the function `s ↦ s` on `[0,1]`, so `s = s'`.
  have hn : ‖(s:ℂ) * circleOf (Ψ t)‖ = ‖(s':ℂ) * circleOf (Ψ t')‖ := by rw [h3]
  simp only [norm_mul, norm_circleOf, mul_one] at hn
  simp only [Complex.norm_real, Real.norm_eq_abs] at hn
  rw [abs_of_nonneg hs.1, abs_of_nonneg hs'.1] at hn
  have hss' : s = s' := hn
  by_cases hs0 : s = 0
  · -- `s = s' = 0`: the second coordinate reads off `u = v` directly.
    have hs'0 : s' = 0 := by rw [← hss', hs0]
    have h2' : (((Θ 0 : ℝ)) : UnitAddCircle) + u = (((Θ 0 : ℝ)) : UnitAddCircle) + v := by
      rw [hs0, hs'0] at h2
      simpa using h2
    exact ⟨add_left_cancel h2', hss'⟩
  · -- `s = s' > 0`: the third coordinate gives `circleOf (Ψ t) = circleOf (Ψ t')`, the first
    -- gives `ρ t = ρ t'`, and `hpolar` plus injectivity of `γ` identifies `t` and `t'` up to `2π`.
    have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs0
    have hcirc : circleOf (Ψ t) = circleOf (Ψ t') := by
      rw [← hss'] at h3
      exact mul_left_cancel₀ hsC h3
    have hρeq : ρ t = ρ t' := by
      rw [← hss'] at h1
      exact mul_left_cancel₀ hs0 (add_left_cancel h1)
    have hpol : polarLift (ρ t, Ψ t) = polarLift (ρ t', Ψ t') :=
      polarLift_eq_of_circleOf_eq hρeq hcirc
    have hγeq : γ (Circle.exp t) = γ (Circle.exp t') := by
      rw [← hpolar t, hpol, hpolar t']
    have hexp : Circle.exp t = Circle.exp t' := hγ.isEmbedding.injective hγeq
    obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp hexp
    -- `Θ` is `2π`-periodic, so `Θ t = Θ t'`.
    have hΘeq : Θ t = Θ t' := by
      have hper : Function.Periodic Θ (2 * Real.pi) := hΘper
      have := hper.int_mul m
      rw [hm]
      exact this t'
    have h2' := h2
    rw [← hss', hΘeq] at h2'
    exact ⟨add_left_cancel h2', hss'⟩

end Work.Drive
