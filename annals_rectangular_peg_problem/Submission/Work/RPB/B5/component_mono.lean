import Mathlib

/-!
# The `0`-component of `{f' ≠ 0}`: sign of the derivative and strict monotonicity

If `f : ℝ → ℝ` is `C¹` on an open interval `(a,b) ∋ 0` and `deriv f 0 > 0`, then on the
connected component `C` of `0` in `U = {ρ ∈ (a,b) : deriv f ρ ≠ 0}` the derivative is positive
and `f` is strictly increasing.  (`C` is the maximal interval around `0` on which `f'` keeps its
sign; `Work.RPB.B5.strictMonoOn_of_deriv_pos_nhds` only gives some neighbourhood of `0`.)
-/

set_option autoImplicit false

noncomputable section

namespace Work.RPB.B5

/-- The component of `0` in `{f' ≠ 0}`: `f' > 0` there and `f` strictly increasing there. -/
theorem component_mono {f : ℝ → ℝ} {a b : ℝ}
    (ha : a < 0) (hb : 0 < b) (hf : ContDiffOn ℝ 1 f (Set.Ioo a b)) (hd : 0 < deriv f 0) :
    (∀ ρ ∈ connectedComponentIn {ρ : ℝ | ρ ∈ Set.Ioo a b ∧ deriv f ρ ≠ 0} 0,
      0 < deriv f ρ) ∧
    StrictMonoOn f (connectedComponentIn {ρ : ℝ | ρ ∈ Set.Ioo a b ∧ deriv f ρ ≠ 0} 0) := by
  set U : Set ℝ := {ρ : ℝ | ρ ∈ Set.Ioo a b ∧ deriv f ρ ≠ 0} with hU
  set C : Set ℝ := connectedComponentIn U 0 with hC
  -- `0` lies in `U`, hence in its own component, and the component sits inside `U ⊆ (a,b)`.
  have h0U : (0 : ℝ) ∈ U := ⟨⟨ha, hb⟩, hd.ne'⟩
  have h0C : (0 : ℝ) ∈ C := mem_connectedComponentIn h0U
  have hCsubU : C ⊆ U := connectedComponentIn_subset U 0
  have hCsub : C ⊆ Set.Ioo a b := fun x hx => (hCsubU hx).1
  have hCne : ∀ x ∈ C, deriv f x ≠ 0 := fun x hx => (hCsubU hx).2
  -- The component is preconnected and `deriv f` is continuous on it.
  have hCpre : IsPreconnected C := isPreconnected_connectedComponentIn
  have hdcont : ContinuousOn (deriv f) C :=
    (hf.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl).mono hCsub
  -- A preconnected set on which a continuous function is nowhere zero has constant sign;
  -- the sign is the sign at `0`, which is positive.
  have hpos : ∀ ρ ∈ C, 0 < deriv f ρ :=
    fun ρ hρ => hCpre.lt_of_ne hdcont hCne ⟨0, h0C, hd⟩ hρ
  refine ⟨fun ρ hρ => hpos ρ hρ, ?_⟩
  -- A preconnected subset of `ℝ` is convex, and `f` is continuous on it, so a positive
  -- derivative on the interior gives strict monotonicity.
  exact strictMonoOn_of_deriv_pos hCpre.convex (hf.continuousOn.mono hCsub)
    (fun x hx => hpos x (interior_subset hx))

end Work.RPB.B5
