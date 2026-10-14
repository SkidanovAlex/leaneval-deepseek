import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS_EllLimOK.ProducerH.H2.bounds_rates
import Submission.Work.FTS_EllLimOK.ProducerH.H2.eg_limits
import Submission.Work.FTS_EllLimOK.ProducerH.H2.th2_holder
import Submission.Work.FTS_EllLimOK.ProducerH.H2.th2_rate
import Submission.Work.FTS_EllLimOK.ProducerH.MixedJets.pkgCos_le4
import Submission.Work.FTS_EllLimOK.ProducerH.slotBd_phiTil
import Submission.Work.FTS_EllLimOK.RulingELF

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
