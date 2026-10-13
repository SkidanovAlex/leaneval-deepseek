/-
Copyright: work module for the Elgindi finite-time singularity project.

# `FTS_EllLimOK.ProducerH.H2.boxData_of_parts` — the endpoint data from its four parts

`BoxData α Ce E a₀ b₀` bundles the four analytic inputs of the box-`C²` chapter.  This module
assembles it from the four sibling lemmas that produce the parts:

* `th2_rate`     — the uniform bound `|∂_θ²(E g)| ≤ K · Xn6 · min(θ,π/2-θ)^β`;
* `bounds_rates` — the pointwise derivative bounds on the strip and the endpoint rates;
* `eg_limits`    — the two one-sided angular limits of `∂_θ(E g)`, `∂_z∂_θ(E g)`;
* `th2_holder`   — the two-point θ-Hölder modulus of `∂_θ²(E g)`.

The assembly is purely definitional: each part *is* the corresponding field of `BoxData`.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS_EllLimOK.RulingELF
import Submission.Work.FTS_EllLimOK.ProducerH.H2.Basic
import Submission.Work.FTS_EllLimOK.ProducerH.H2.Data
import Submission.Work.FTS_EllLimOK.ProducerH.H2.th2_rate
import Submission.Work.FTS_EllLimOK.ProducerH.H2.bounds_rates
import Submission.Work.FTS_EllLimOK.ProducerH.H2.eg_limits
import Submission.Work.FTS_EllLimOK.ProducerH.H2.th2_holder

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.ProducerH.H2

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

theorem boxData_of_parts {α Ce : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    {E : Fn →ₗ[ℝ] Fn}
    (hE : Ctx α Ce E) {a₀ b₀ : ℝ} (ha₀ : 0 < a₀) (hab : a₀ ≤ b₀) :
    BoxData α Ce E a₀ b₀ := by
  obtain ⟨K, hK, β, hβ, hmod⟩ := th2_rate hα hα4 hE ha₀ hab
  obtain ⟨C₁, hC₁, hrates⟩ := bounds_rates hα hα4 hE ha₀ hab hK hβ hmod
  obtain ⟨C₂, hC₂, hlim⟩ := eg_limits hα hα4 hE ha₀ hab hK hβ hmod
  obtain ⟨K₂, hK₂, β₂, hβ₂, hhol⟩ := th2_holder hα hα4 hE ha₀ hab
  exact ⟨K, hK, β, hβ, hmod, ⟨C₁, hC₁, hrates⟩, ⟨C₂, hC₂, hlim⟩,
    ⟨K₂, hK₂, β₂, hβ₂, hhol⟩⟩

end Work.FTS_EllLimOK.ProducerH.H2
