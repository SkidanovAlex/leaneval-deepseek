import Mathlib
import Submission.Work.Drive.CappingDefs
import Submission.Work.Drive.cappingPolar_identification

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff

/-- **The polar lift of a smooth closed plane curve avoiding the origin (the capping's second input).**

For a smooth embedding `γ : Circle → ℝ²` whose image avoids the origin, there are continuous
`ρ : ℝ → ℝ`, `Θ : ℝ → ℝ` with `ρ > 0` pointwise such that

`polarLift (ρ t, Θ t) = γ (Circle.exp t)` for all `t`,

i.e. `(ρ, Θ)` are a *global polar-coordinate lift* of the parametrised curve, and the angle coordinate
has an *integer* total change over one period: `Θ (2π) - Θ 0 ∈ ℤ` — the winding number of the curve
around the origin.  (`polarLift (r, ψ) = (r cos (2πψ), r sin (2πψ))` is the polar parametrisation of
`Submission.Work.Drive.CappingDefs`; its identification of `(0,∞) × (ℝ/ℤ)` with `ℝ² ∖ {0}` is
`cappingPolar_identification`.)

This is the *position half* of the statement that the boundary `∂M` of the configuration Möbius strip is
a `(2,1)`-curve in the boundary torus of the configuration space: the *direction half* (the doubled
tangent direction winds twice over a period) is `Work.Drive.doubledTangent_winding`.  With the gluing
identification of `Submission.Work.Drive.cappingGlue_identification` and the fact that the induced torus
map carries the `(2,1)`-family onto the meridians (`glueTorus_preimage_t21`) this is what makes `∂M` a
meridian of the cap, the input the chain-level representative of Hugelmeyer's class `ω_P` needs on the
route to `Work.Drive.chainParity`.

The *value* of the winding (that the integer is `±1` for a Jordan curve) is not asserted here: it is the
Jordan-curve input, kept separate so that this brick is exactly the covering-space statement. -/
theorem position_angle_lift (γ : Circle → ℝ × ℝ)
    (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ∞ γ) (h0 : ∀ x : Circle, γ x ≠ 0) :
    ∃ (ρ : ℝ → ℝ) (Θ : ℝ → ℝ), Continuous ρ ∧ Continuous Θ ∧ (∀ t, 0 < ρ t) ∧
      (∀ t, Work.Drive.polarLift (ρ t, Θ t) = γ (Circle.exp t)) ∧
      ∃ m : ℤ, Θ (2 * Real.pi) - Θ 0 = (m : ℝ) := by
  have hγcont : Continuous γ := hγ.isEmbedding.continuous
  set v : ℝ → ℝ × ℝ := fun t => γ (Circle.exp t) with hv
  have hvcont : Continuous v := hγcont.comp Circle.exp.continuous
  have hv_ne : ∀ t, v t ≠ 0 := by
    intro t
    rw [hv]
    exact h0 (Circle.exp t)
  have hg_cont : Continuous fun t => ((v t).1 : ℂ) + ((v t).2 : ℂ) * Complex.I := by
    have h1 : Continuous fun t => ((v t).1 : ℂ) :=
      Complex.continuous_ofReal.comp (continuous_fst.comp hvcont)
    have h2 : Continuous fun t => ((v t).2 : ℂ) :=
      Complex.continuous_ofReal.comp (continuous_snd.comp hvcont)
    exact h1.add (h2.mul continuous_const)
  have hg_ne : ∀ t, ((v t).1 : ℂ) + ((v t).2 : ℂ) * Complex.I ≠ 0 := by
    intro t h
    have h1 : (v t).1 = 0 := by
      have := congrArg Complex.re h
      simpa using this
    have h2 : (v t).2 = 0 := by
      have := congrArg Complex.im h
      simpa using this
    exact hv_ne t (by ext <;> simp [h1, h2])
  -- the curve as a continuous nowhere vanishing complex function
  let g : C(ℝ, ℂ) := ⟨fun t => ((v t).1 : ℂ) + ((v t).2 : ℂ) * Complex.I, hg_cont⟩
  have hg_apply : ∀ t, g t = ((v t).1 : ℂ) + ((v t).2 : ℂ) * Complex.I := fun t => rfl
  -- lift through the covering map `exp : ℂ → ℂ`
  obtain ⟨F, hFexp⟩ : ∃ F : C(ℝ, ℂ), ∀ t, Complex.exp (F t) = g t := by
    obtain ⟨F, -, hF⟩ :=
      (Complex.isCoveringMapOn_exp.existsUnique_continuousMap_lifts g (a₀ := 0)
        (e₀ := Complex.log (g 0))
        (by rw [hg_apply]; exact Complex.exp_log (hg_ne 0))
        (by intro a; rw [Set.mem_compl_iff]; exact hg_ne a)).exists
    exact ⟨F, fun t => congrFun hF t⟩
  have hre : ∀ t, ((g t).re) = (v t).1 := by
    intro t; rw [hg_apply t]; simp
  have him : ∀ t, ((g t).im) = (v t).2 := by
    intro t; rw [hg_apply t]; simp
  -- the parametrisation is periodic, so the two endpoint lifts differ by an element of `2πiℤ`
  have hg_eq : g (2 * Real.pi) = g 0 := by
    have hexp_eq : Circle.exp (2 * Real.pi) = Circle.exp 0 := by
      rw [Circle.exp_two_pi, Circle.exp_zero]
    have hv_eq : v (2 * Real.pi) = v 0 := by
      rw [hv]; exact congrArg γ hexp_eq
    simp only [hg_apply, hv_eq]
  have hexpF : Complex.exp (F (2 * Real.pi)) = Complex.exp (F 0) := by
    rw [hFexp (2 * Real.pi), hFexp 0, hg_eq]
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexpF
  have himn : (F (2 * Real.pi)).im = (F 0).im + (n : ℝ) * (2 * Real.pi) := by
    have h := congrArg Complex.im hn
    simpa using h
  refine ⟨fun t => Real.exp ((F t).re), fun t => (F t).im / (2 * Real.pi), ?_, ?_, ?_, ?_, ?_⟩
  · exact Real.continuous_exp.comp (Complex.continuous_re.comp F.continuous)
  · exact (Complex.continuous_im.comp F.continuous).div_const _
  · intro t; exact Real.exp_pos _
  · intro t
    have h2pi : 2 * Real.pi * ((F t).im / (2 * Real.pi)) = (F t).im := by
      field_simp
    have h1 : Real.exp ((F t).re) * Real.cos (2 * Real.pi * ((F t).im / (2 * Real.pi))) =
        (v t).1 := by
      rw [h2pi]
      rw [← Complex.exp_re, hFexp t, hre t]
    have h2 : Real.exp ((F t).re) * Real.sin (2 * Real.pi * ((F t).im / (2 * Real.pi))) =
        (v t).2 := by
      rw [h2pi]
      rw [← Complex.exp_im, hFexp t, him t]
    change Work.Drive.polarLift (Real.exp (F t).re, (F t).im / (2 * Real.pi)) = v t
    simp only [Work.Drive.polarLift]
    exact Prod.ext h1 h2
  · refine ⟨n, ?_⟩
    show (F (2 * Real.pi)).im / (2 * Real.pi) - (F 0).im / (2 * Real.pi) = (n : ℝ)
    rw [div_sub_div_same, himn, add_sub_cancel_left, mul_div_cancel_right₀ _ (by positivity)]


end Work.Drive
