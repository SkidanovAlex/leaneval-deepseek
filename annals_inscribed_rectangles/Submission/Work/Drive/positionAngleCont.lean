import Mathlib
import Submission.Work.Drive.CappingDefs
import Submission.Work.Drive.cappingPolar_identification

/-!
# The polar (position-angle) lift, under continuity only

`Work.Drive.position_angle_lift` states the existence of the global polar-coordinate lift of a smooth
closed plane curve avoiding the origin.  Its proof uses the smoothness hypothesis only to extract
continuity of the curve, so the statement is recorded here in the sharper form actually needed by the
capping: for a merely *continuous* curve `γ : Circle → ℝ × ℝ` avoiding `0` there are continuous
`ρ, Θ` with `ρ > 0`, `polarLift (ρ t, Θ t) = γ (exp t)` and `Θ (2π) - Θ 0 ∈ ℤ`.

The form used by the sign-match step of the capping is `Work.Drive.position_angle_lift_sub`: the same
statement about the translate `γ - p` of a curve avoiding the point `p`, i.e. the polar lift about an
arbitrary point of the plane rather than about the origin.  Together with
`Work.Drive.position_winding_eq_umlauf_sign` (which is already stated about a general point `p`) this
removes the need to know that a translate of a smooth embedding is again a smooth embedding
(`BRIDGE_CIRCLE_UNITADD.md`, item (B2)).
-/

namespace Work.Drive

open scoped Topology ContDiff

/-- **The polar lift of a continuous closed plane curve avoiding the origin.**  There are continuous
`ρ, Θ : ℝ → ℝ` with `ρ > 0` and `polarLift (ρ t, Θ t) = γ (exp t)`; the total change of `Θ` over one
period is an integer (the winding number of `γ` about the origin). -/
theorem position_angle_lift_continuous (γ : Circle → ℝ × ℝ) (hγcont : Continuous γ)
    (h0 : ∀ x : Circle, γ x ≠ 0) :
    ∃ (ρ : ℝ → ℝ) (Θ : ℝ → ℝ), Continuous ρ ∧ Continuous Θ ∧ (∀ t, 0 < ρ t) ∧
      (∀ t, Work.Drive.polarLift (ρ t, Θ t) = γ (Circle.exp t)) ∧
      ∃ m : ℤ, Θ (2 * Real.pi) - Θ 0 = (m : ℝ) := by

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



/-- **The polar lift about an arbitrary point.**  If a continuous curve avoids `p`, then `γ - p`
avoids the origin and `position_angle_lift_continuous` applies: this is the polar-coordinate lift of
`γ` about the point `p`, in exactly the form consumed by
`Work.Drive.position_winding_eq_umlauf_sign` (whose hypotheses `hΘlift` and `hp` are about a general
point `p`). -/
theorem position_angle_lift_sub (γ : Circle → ℝ × ℝ) (hγcont : Continuous γ) {p : ℝ × ℝ}
    (hp : ∀ x : Circle, γ x ≠ p) :
    ∃ (ρ : ℝ → ℝ) (Θ : ℝ → ℝ), Continuous ρ ∧ Continuous Θ ∧ (∀ t, 0 < ρ t) ∧
      (∀ t, Work.Drive.polarLift (ρ t, Θ t) = γ (Circle.exp t) - p) ∧
      ∃ m : ℤ, Θ (2 * Real.pi) - Θ 0 = (m : ℝ) := by
  have hcont : Continuous fun x : Circle => γ x - p := hγcont.sub continuous_const
  have h0 : ∀ x : Circle, γ x - p ≠ 0 := by
    intro x h
    exact hp x (sub_eq_zero.mp h)
  obtain ⟨ρ, Θ, hρc, hΘc, hρ, hlift, hm⟩ := position_angle_lift_continuous _ hcont h0
  exact ⟨ρ, Θ, hρc, hΘc, hρ, hlift, hm⟩

end Work.Drive
