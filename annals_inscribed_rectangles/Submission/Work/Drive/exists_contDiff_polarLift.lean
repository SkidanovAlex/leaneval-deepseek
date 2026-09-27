import Mathlib
import Submission.Work.Drive.CappingDefs
import Submission.Work.Drive.PolarTwist.exists_enclosing_point

/-!
# A `C^∞` polar lift of an arbitrary smooth nowhere-vanishing plane curve

`Work.Drive.exists_contDiff_polarLift`: for a `C^∞` curve `v : ℝ → ℂ` that never vanishes there is a
`C^∞` angle function `Θ : ℝ → ℝ` with

`polarLift (‖v t‖, Θ t) = (re (v t), im (v t))` for all `t`,

i.e. `Θ` is a global polar angle of `v` (the argument of `v`, in the normalisation of `polarLift`,
where the angle parametrises the circle by `θ ↦ (cos (2πθ), sin (2πθ))`).

Since `ℝ` is simply connected, a nowhere-vanishing smooth map into `ℂ` has a lift through the
covering map `Complex.exp : ℂ → ℂ`; the existence of the *continuous* lift is
`IsCoveringMapOn.existsUnique_continuousMap_lifts` for `Complex.isCoveringMapOn_exp`, and its
smoothness is the already-proved covering/branch-of-the-logarithm statement
`Work.Drive.PolarTwist.contDiff_polarAngle_top`.
-/

namespace Work.Drive

theorem exists_contDiff_polarLift (v : ℝ → ℂ) (hv : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) v)
    (hne : ∀ t, v t ≠ 0) :
    ∃ Θ : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θ ∧
      ∀ t, Work.Drive.polarLift ((‖v t‖ : ℝ), Θ t) = ((v t).re, (v t).im) := by
  -- `v` as a continuous map, lifted through the covering map `Complex.exp` (possible because `ℝ`
  -- is simply connected and `v` avoids `0`).
  set g : C(ℝ, ℂ) := ⟨v, hv.continuous⟩ with hg
  obtain ⟨F, hF⟩ := (Complex.isCoveringMapOn_exp.existsUnique_continuousMap_lifts g (a₀ := 0)
      (e₀ := Complex.log (g 0)) (Complex.exp_log (hne 0))
      (by intro a; rw [Set.mem_compl_iff]; exact hne a)).exists
  have hFexp : ∀ t, Complex.exp (F t) = v t := fun t => congrFun hF.2 t
  have hΘcont : Continuous fun t => (F t).im / (2 * Real.pi) :=
    (Complex.continuous_im.comp F.continuous).div_const _
  -- the two computations of the polar form of `exp (F t) = v t`
  have key : ∀ t : ℝ,
      Work.Drive.polarLift ((‖v t‖ : ℝ), (F t).im / (2 * Real.pi)) = ((v t).re, (v t).im) := by
    intro t
    have hb : 2 * Real.pi * ((F t).im / (2 * Real.pi)) = (F t).im := by field_simp
    have hn : ‖v t‖ = Real.exp ((F t).re) := by rw [← hFexp t, Complex.norm_exp]
    have h1 : (v t).re = Real.exp ((F t).re) * Real.cos ((F t).im) := by
      rw [← hFexp t, Complex.exp_re]
    have h2 : (v t).im = Real.exp ((F t).re) * Real.sin ((F t).im) := by
      rw [← hFexp t, Complex.exp_im]
    rw [Work.Drive.polarLift, hb]
    exact Prod.ext (by rw [h1, hn]) (by rw [h2, hn])
  refine ⟨fun t => (F t).im / (2 * Real.pi), ?_, key⟩
  -- smoothness of the lift: a continuous lift of the argument of a smooth curve is smooth
  refine Work.Drive.PolarTwist.contDiff_polarAngle_top (v := fun t => ((v t).re, (v t).im))
    (ρ := fun t => ‖v t‖) (Θ := fun t => (F t).im / (2 * Real.pi))
    ((Complex.reCLM.prod Complex.imCLM).contDiff.comp hv) ?_ (fun t => norm_pos_iff.mpr (hne t))
    hΘcont ?_
  · intro t h
    refine hne t (Complex.ext ?_ ?_)
    · have := congrArg Prod.fst h; simpa using this
    · have := congrArg Prod.snd h; simpa using this
  · intro t
    have hb : 2 * Real.pi * ((F t).im / (2 * Real.pi)) = (F t).im := by field_simp
    have hn : ‖v t‖ = Real.exp ((F t).re) := by rw [← hFexp t, Complex.norm_exp]
    have h1 : (v t).re = Real.exp ((F t).re) * Real.cos ((F t).im) := by
      rw [← hFexp t, Complex.exp_re]
    have h2 : (v t).im = Real.exp ((F t).re) * Real.sin ((F t).im) := by
      rw [← hFexp t, Complex.exp_im]
    rw [Work.Drive.polarLift, hb]
    exact Prod.ext (by rw [h1, hn]) (by rw [h2, hn])

end Work.Drive
