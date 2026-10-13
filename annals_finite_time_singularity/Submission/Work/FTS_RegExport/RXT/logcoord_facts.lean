import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Construction.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXT

/-- `sin (2 * arctan t) / 2 = t / (1 + t²)`: the elementary trigonometric identity behind the
change of coordinate `θ = arctan (e^ψ)`. -/
lemma sin_two_arctan_div_two (t : ℝ) : Real.sin (2 * Real.arctan t) / 2 = t / (1 + t ^ 2) := by
  have hD : (0 : ℝ) ≤ 1 + t ^ 2 := by positivity
  have h2 : Real.sin (Real.arctan t) * Real.cos (Real.arctan t) = t / (1 + t ^ 2) := by
    rw [Real.sin_arctan, Real.cos_arctan, div_mul_div_comm, mul_one, Real.mul_self_sqrt hD]
  rw [Real.sin_two_mul]
  rw [show (2 : ℝ) * Real.sin (Real.arctan t) * Real.cos (Real.arctan t) / 2
        = Real.sin (Real.arctan t) * Real.cos (Real.arctan t) by ring]
  exact h2

/-- `|cos (2θ) - sin²θ| ≤ 2`: both summands lie in `[-1,1]`. -/
lemma abs_c2m_le_two (θ : ℝ) : |Work.Construction.c2m θ| ≤ 2 := by
  rw [Work.Construction.c2m_eq]
  calc |Real.cos (2 * θ) - Real.sin θ ^ 2|
      ≤ |Real.cos (2 * θ)| + |Real.sin θ ^ 2| := abs_sub _ _
    _ ≤ 2 := by
        have h1 := Real.abs_cos_le_one (2 * θ)
        have h2 : |Real.sin θ ^ 2| ≤ 1 := by
          rw [abs_of_nonneg (sq_nonneg (Real.sin θ))]
          exact Real.sin_sq_le_one θ
        linarith

/-- Elementary facts about the logarithmic angular coordinate `ψ ↦ θ = arctan(e^ψ)`, which maps
`ℝ` onto the open interval `(0, π/2)`:

* `0 < arctan (e^ψ) < π/2` for every `ψ`;
* `d/dψ arctan(e^ψ) = sin (2·arctan(e^ψ))/2 = e^ψ/(1+e^{2ψ})`; in particular the derivative is
  positive, so `sin (2·arctan(e^ψ)) > 0`;
* every `z > 0` is `e^s` for some `s`, and every `θ ∈ (0,π/2)` is `arctan(e^ψ)` for some `ψ`
  (namely `ψ = log (tan θ)`);
* `0 < sin (2θ)` for `0 < θ < π/2`;
* `|c2m θ| ≤ 2` where `c2m θ = cos 2θ − sin²θ` (`Work.Construction.c2m`). -/
theorem logcoord_facts :
    (∀ ψ : ℝ, 0 < Real.arctan (Real.exp ψ) ∧ Real.arctan (Real.exp ψ) < Real.pi / 2) ∧
    (∀ ψ : ℝ, 0 < Real.sin (2 * Real.arctan (Real.exp ψ))) ∧
    (∀ ψ : ℝ, HasDerivAt (fun ψ' => Real.arctan (Real.exp ψ'))
      (Real.sin (2 * Real.arctan (Real.exp ψ)) / 2) ψ) ∧
    (∀ z : ℝ, 0 < z → ∃ s : ℝ, Real.exp s = z) ∧
    (∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 → ∃ ψ : ℝ, Real.arctan (Real.exp ψ) = θ) ∧
    (∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 → 0 < Real.sin (2 * θ)) ∧
    (∀ θ : ℝ, |Work.Construction.c2m θ| ≤ 2) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ψ
    exact ⟨(Real.arctan_pos).mpr (Real.exp_pos ψ), Real.arctan_lt_pi_div_two (Real.exp ψ)⟩
  · intro ψ
    refine Real.sin_pos_of_pos_of_lt_pi ?_ ?_
    · exact mul_pos two_pos ((Real.arctan_pos).mpr (Real.exp_pos ψ))
    · nlinarith [Real.arctan_lt_pi_div_two (Real.exp ψ), Real.pi_pos]
  · intro ψ
    have h := (Real.hasDerivAt_arctan (Real.exp ψ)).comp ψ (Real.hasDerivAt_exp ψ)
    have hv : (1 / (1 + (Real.exp ψ) ^ 2)) * Real.exp ψ
        = Real.sin (2 * Real.arctan (Real.exp ψ)) / 2 := by
      rw [sin_two_arctan_div_two]
      rw [one_div, inv_mul_eq_div]
    rw [hv] at h
    exact h
  · intro z hz
    exact ⟨Real.log z, Real.exp_log hz⟩
  · intro θ h1 h2
    refine ⟨Real.log (Real.tan θ), ?_⟩
    rw [Real.exp_log (Real.tan_pos_of_pos_of_lt_pi_div_two h1 h2)]
    exact Real.arctan_tan (by linarith [Real.pi_pos]) h2
  · intro θ h1 h2
    refine Real.sin_pos_of_pos_of_lt_pi ?_ ?_
    · linarith
    · linarith [Real.pi_pos]
  · exact abs_c2m_le_two

end Work.FTS_RegExport.RXT
