import Mathlib

namespace Work.KT.Dim2

/-- A continuous logarithm `F` of a map `f : S¹ → ℂˣ` exhibits `f` as null-homotopic: the
straight-line homotopy `(t, z) ↦ exp ((1 - t) * F z)` runs from `f` to the constant `1`. -/
theorem log_nullhomotopic (f : C(Metric.sphere (0 : ℂ) 1, ℂˣ))
    (h : ∃ F : C(Metric.sphere (0 : ℂ) 1, ℂ), ∀ z, Complex.exp (F z) = (f z : ℂ)) :
    ContinuousMap.Homotopic f (ContinuousMap.const _ 1) := by
  obtain ⟨F, hF⟩ := h
  -- The exponent of the straight-line homotopy, a continuous `ℂ`-valued function on `I × S¹`.
  have hθ : Continuous fun p : unitInterval × Metric.sphere (0 : ℂ) 1 =>
      (1 - (p.1 : ℝ)) * F p.2 := by fun_prop
  -- `z ↦ exp ((1 - t) * F z)` lands in the units of `ℂ`, since `exp` never vanishes.
  let G : C(unitInterval × Metric.sphere (0 : ℂ) 1, ℂˣ) :=
    { toFun := fun p => Units.mk0 (Complex.exp ((1 - (p.1 : ℝ)) * F p.2))
        (Complex.exp_ne_zero _)
      continuous_toFun := by
        refine Units.continuous_iff.mpr ⟨?_, ?_⟩
        · exact Complex.continuous_exp.comp hθ
        · simp only [Units.val_inv_eq_inv_val, Units.val_mk0, ← Complex.exp_neg]
          exact Complex.continuous_exp.comp hθ.neg }
  refine ⟨ContinuousMap.Homotopy.mk G ?_ ?_⟩
  · intro z
    apply Units.ext
    simpa [G] using hF z
  · intro z
    apply Units.ext
    simp [G]

end Work.KT.Dim2
