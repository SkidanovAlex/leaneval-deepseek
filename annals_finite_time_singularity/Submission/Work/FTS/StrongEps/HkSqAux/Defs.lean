/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/HkSqAux/Defs.lean`

Definitions used by the `E1`-boundedness lemma `Work.FTS.StrongEps.HkSq_Jeps_le`
(`Submission/Work/FTS/StrongEps/HkSq_Jeps_le.lean`) and by the auxiliary lemmas delegated for it.

The log-coordinate mollifier `Jeps ρ ε` is, in the coordinates

  `s = log z`,   `ζ = log tan θ`,

the convolution with the rescaled kernel `Jker ρ ε`, and the shifts `zShift`, `thShift` are the
translations `s ↦ s - p₁`, `ζ ↦ ζ - p₂`.  Consequently the *weighted* `L²`-integral defining
`HkSq` is, in these coordinates, an ordinary integral over the plane, with the extra Jacobian
factor

  `dz dθ = (e^s · (arctan ∘ exp)'(ζ)) ds dζ`,

and the change of variables is the substitution `θ = arctan (e^ζ)`, `z = e^s`, whose derivatives
are the functions `kappa` and `Real.exp`.  This module only records the definitions and their
elementary positivity properties.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.Kernel
import Submission.Work.FTS.StrongEps.Weights

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.HkSqAux

set_option autoImplicit false

/-- The log-coordinate map `(s,ζ) ↦ (e^s, arctan (e^ζ))`: a bijection of `ℝ²` onto the open
quadrant `Quad = (0,∞) × (0,π/2)`. -/
def logMap (s ζ : ℝ) : ℝ × ℝ := (Real.exp s, Real.arctan (Real.exp ζ))

/-- The derivative `ζ ↦ e^ζ / (1 + e^{2ζ})` of the map `ζ ↦ arctan (e^ζ)`. -/
def kappa (ζ : ℝ) : ℝ := Real.exp ζ / (1 + Real.exp (2 * ζ))

/-- The Jacobian factor `e^s · (arctan ∘ exp)'(ζ) = e^s · kappa ζ` of the log-coordinate
substitution. -/
def logJac (s ζ : ℝ) : ℝ := Real.exp s * kappa ζ

theorem kappa_pos (ζ : ℝ) : 0 < kappa ζ := by
  rw [kappa]
  positivity

theorem kappa_nonneg (ζ : ℝ) : 0 ≤ kappa ζ := (kappa_pos ζ).le

theorem logJac_pos (s ζ : ℝ) : 0 < logJac s ζ := by
  rw [logJac]
  exact mul_pos (Real.exp_pos s) (kappa_pos ζ)

theorem logJac_nonneg (s ζ : ℝ) : 0 ≤ logJac s ζ := (logJac_pos s ζ).le

theorem logMap_mem_Quad (s ζ : ℝ) : logMap s ζ ∈ Quad := by
  refine ⟨Real.exp_pos s, ?_, ?_⟩
  · exact Real.arctan_pos.2 (Real.exp_pos ζ)
  · exact Real.arctan_lt_pi_div_two _

/-- The range of `ζ ↦ arctan (e^ζ)` is the open interval `(0, π/2)`. -/
theorem range_arctan_exp : (fun ζ : ℝ => Real.arctan (Real.exp ζ)) '' Set.univ
    = Set.Ioo 0 (π / 2) := by
  ext θ
  constructor
  · rintro ⟨ζ, -, rfl⟩
    exact ⟨Real.arctan_pos.2 (Real.exp_pos ζ), Real.arctan_lt_pi_div_two _⟩
  · intro hθ
    refine ⟨Real.log (Real.tan θ), trivial, ?_⟩
    have hpos : 0 < Real.tan θ := Real.tan_pos_of_pos_of_lt_pi_div_two hθ.1 hθ.2
    have hlt : -(π / 2) < θ := by linarith [hθ.1, Real.pi_pos]
    show Real.arctan (Real.exp (Real.log (Real.tan θ))) = θ
    rw [Real.exp_log hpos, Real.arctan_tan hlt hθ.2]

/-- The range of `Real.exp` is `(0, ∞)`. -/
theorem range_exp : Real.exp '' Set.univ = Set.Ioi (0 : ℝ) := by
  ext x
  constructor
  · rintro ⟨s, -, rfl⟩
    exact Real.exp_pos s
  · intro hx
    exact ⟨Real.log x, trivial, Real.exp_log hx⟩

theorem kappa_eq_deriv (ζ : ℝ) :
    deriv (fun ζ' : ℝ => Real.arctan (Real.exp ζ')) ζ = kappa ζ := by
  have h1 : HasDerivAt (fun ζ' : ℝ => Real.exp ζ') (Real.exp ζ) ζ := Real.hasDerivAt_exp ζ
  have h2 := (Real.hasDerivAt_arctan (Real.exp ζ)).comp ζ h1
  have h3 : deriv (fun ζ' : ℝ => Real.arctan (Real.exp ζ')) ζ
      = (1 / (1 + (Real.exp ζ) ^ 2)) * Real.exp ζ := by
    simpa only [Function.comp_def] using h2.deriv
  have h4 : 1 + (Real.exp ζ) ^ 2 = 1 + Real.exp (2 * ζ) := by
    rw [sq, ← Real.exp_add]
    ring
  rw [h3, kappa, h4]
  ring

end Work.FTS.StrongEps.HkSqAux
