import Mathlib

namespace Work.OdeCont

/-- Two functions holomorphic on open sets `U` and `V` that agree on `U ∩ V` glue to a
single function differentiable on `U ∪ V`. The witness is the obvious `F z = f z` on `U`
and `F z = g z` off `U`. -/
theorem glue_two {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {U V : Set ℂ} (hU : IsOpen U) (hV : IsOpen V) (f g : ℂ → E)
    (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g V)
    (h : Set.EqOn f g (U ∩ V)) :
    ∃ F : ℂ → E, DifferentiableOn ℂ F (U ∪ V) ∧ Set.EqOn F f U ∧ Set.EqOn F g V := by
  classical
  -- The glued function: agree with `f` on `U`, otherwise use `g`.
  let F : ℂ → E := fun z => if z ∈ U then f z else g z
  have hFU : DifferentiableOn ℂ F U :=
    hf.congr (fun x hx => by simp only [F]; exact if_pos hx)
  have hFV : DifferentiableOn ℂ F V :=
    hg.congr (fun x hx => by
      by_cases hxU : x ∈ U
      · simp only [F, if_pos hxU]; exact h ⟨hxU, hx⟩
      · simp only [F, if_neg hxU])
  refine ⟨F, ?_, ?_, ?_⟩
  · -- Differentiability on `U ∪ V`, pointwise.
    intro x hx
    rcases hx with hxU | hxV
    · exact (hFU.differentiableAt (hU.mem_nhds hxU)).differentiableWithinAt
    · exact (hFV.differentiableAt (hV.mem_nhds hxV)).differentiableWithinAt
  · -- `F = f` on `U`.
    intro x hx; simp only [F]; exact if_pos hx
  · -- `F = g` on `V`.
    intro x hx
    by_cases hxU : x ∈ U
    · simp only [F, if_pos hxU]; exact h ⟨hxU, hx⟩
    · simp only [F, if_neg hxU]

end Work.OdeCont
