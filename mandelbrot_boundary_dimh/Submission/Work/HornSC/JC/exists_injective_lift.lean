import Mathlib
import Submission.Work.HornSC.Tools

namespace Work.HornSC.JC

open scoped Topology

/-- **The exponential lift of a null-winding curve is an injective embedding.**
If `γ : C(Circle, ℂ)` is injective, `a ∉ range γ`, and the `1`-periodic curve
`t ↦ γ (Circle.exp (2 π t)) - a` admits a continuous `1`-periodic argument function (`HasArg`), then
there is an injective continuous `Λ : C(Circle, ℂ)` with `Complex.exp (Λ z) = γ z - a` for all `z`. -/
theorem exists_injective_lift {γ : C(Circle, ℂ)} (hγ : Function.Injective γ) {a : ℂ}
    (ha : a ∉ Set.range γ)
    (h : Commons.Topology.Winding.HasArg (fun t : ℝ => γ (Circle.exp (2 * Real.pi * t)) - a) 0) :
    ∃ Λ : C(Circle, ℂ), Function.Injective Λ ∧ ∀ z : Circle, Complex.exp (Λ z) = γ z - a := by
  classical
  -- Unpack the periodic argument function.
  obtain ⟨θ, hθc, hθper, hθrep⟩ := h
  simp only [sub_zero] at hθrep
  -- The curve on `ℝ`.
  set f : ℝ → ℂ := fun t => γ (Circle.exp (2 * Real.pi * t)) - a with hfdef
  have hfc : Continuous f := by
    rw [hfdef]
    exact (γ.continuous.comp (Circle.exp.continuous.comp (by fun_prop))).sub continuous_const
  have hfnz : ∀ t, f t ≠ 0 := by
    intro t ht
    rw [hfdef] at ht
    exact ha ⟨Circle.exp (2 * Real.pi * t), sub_eq_zero.mp ht⟩
  have hfper : Function.Periodic f 1 := by
    intro t
    simp only [hfdef]
    have h1 : Circle.exp (2 * Real.pi * (t + 1)) = Circle.exp (2 * Real.pi * t) := by
      rw [show 2 * Real.pi * (t + 1) = 2 * Real.pi * t + 2 * Real.pi by ring, Circle.exp_add,
        Circle.exp_two_pi, mul_one]
    rw [h1]
  -- The lifted function `log ‖f‖ + i θ` on `ℝ`.
  set F : ℝ → ℂ := fun t => (Real.log ‖f t‖ : ℂ) + (θ t : ℂ) * Complex.I with hFdef
  have hFc : Continuous F := by
    rw [hFdef]
    exact (Complex.continuous_ofReal.comp
        (Continuous.log hfc.norm (fun t => norm_ne_zero_iff.mpr (hfnz t)))).add
      ((Complex.continuous_ofReal.comp hθc).mul continuous_const)
  have hexpF : ∀ t, Complex.exp (F t) = f t := by
    intro t
    rw [hFdef, Complex.exp_add, ← Complex.ofReal_exp,
      Real.exp_log (norm_pos_iff.mpr (hfnz t))]
    exact (hθrep t).symm
  have hFper : Function.Periodic F 1 := by
    intro t
    simp only [hFdef, hfper t, hθper t]
  -- Rescale so that the period is `2 π`, matching `Circle.exp`.
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  set Φ : ℝ → ℂ := fun u => F (u / (2 * Real.pi)) with hΦdef
  have hΦcont : Continuous Φ := hFc.comp (by fun_prop)
  have hΦper : Function.Periodic Φ (2 * Real.pi) := by
    intro u
    simp only [hΦdef]
    have hdiv : (u + 2 * Real.pi) / (2 * Real.pi) = u / (2 * Real.pi) + 1 := by
      rw [add_div, div_self hpi]
    rw [hdiv, hFper]
  -- Descend `Φ` to the circle.
  set Λ₀ : Circle → ℂ := fun z => Φ (Classical.choose (Circle.exp_surjective z)) with hΛdef
  have hΛcomp : Λ₀ ∘ Circle.exp = Φ := by
    funext u
    rw [Function.comp_apply, hΛdef]
    obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp
      (Classical.choose_spec (Circle.exp_surjective (Circle.exp u))).symm
    conv_rhs => rw [hm]
    exact (hΦper.int_mul m (Classical.choose (Circle.exp_surjective (Circle.exp u)))).symm
  have hquot : Topology.IsQuotientMap (⇑Circle.exp) :=
    IsOpenMap.isQuotientMap isLocalHomeomorph_circleExp.isOpenMap Circle.exp.continuous
      Circle.exp_surjective
  have hΛcont : Continuous Λ₀ :=
    hquot.continuous_iff.mpr (by rw [hΛcomp]; exact hΦcont)
  have hprop : ∀ z : Circle, Complex.exp (Λ₀ z) = γ z - a := by
    intro z
    have hz : Circle.exp (Classical.choose (Circle.exp_surjective z)) = z :=
      Classical.choose_spec (Circle.exp_surjective z)
    have h2 : 2 * Real.pi * (Classical.choose (Circle.exp_surjective z) / (2 * Real.pi))
        = Classical.choose (Circle.exp_surjective z) :=
      mul_div_cancel₀ (Classical.choose (Circle.exp_surjective z)) hpi
    simp only [hΛdef, hΦdef, hexpF, hfdef, h2, hz]
  have hinj : Function.Injective Λ₀ := by
    intro z w hzw
    have h1 : γ z - a = γ w - a := by rw [← hprop z, ← hprop w, hzw]
    exact hγ (sub_left_inj.mp h1)
  exact ⟨⟨Λ₀, hΛcont⟩, hinj, hprop⟩

end Work.HornSC.JC
