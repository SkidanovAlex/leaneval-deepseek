import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.H2.T1Q.PwBdQ
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row24

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.Open.Row24Aux

open scoped Real Topology
open MeasureTheory Set Filter

/-- For almost every angle `θ ∈ Iθ` the `z`-slice `z ↦ h z θ` satisfies the radial Hardy
inequality `(h z θ)² ≤ Qg h θ` for every `z > 0`.  This is the `L²`-domination of the value by
the `θ`-slice of the `ℋ⁴`-density that the radial-product estimate needs.

Proof: at a.e. `θ` the `z`-slice of `HkIntegrand α 4 h` is integrable (`HkSqSwapQ`), and it
dominates the slice of `psiZ h · θ` pointwise inside the open angular interval
(`psiZ_le_HkIntegrand_of_Ioo`); Hardy's inequality `HardyZQ` applied to the slice gives the
claim. -/
theorem qgSliceAe {α : ℝ} {h : ℝ → ℝ → ℝ} (hsh : Work.FTS.LocData.SmoothQuad h)
    (hhm : Work.Spaces.HkMem α 4 h)
    (hdec : ∀ θ ∈ Work.Spaces.Iθ, Filter.Tendsto (fun z => h z θ) Filter.atTop (nhds 0)) :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      ∀ z ∈ Set.Ioi (0 : ℝ), (h z θ) ^ 2 ≤ Work.FTS.Nonlinear.RadialProd.Qg h θ := by
  obtain ⟨-, -, hsliceae⟩ := Work.H2.T1Q.HkSqSwapQ α h hsh hhm
  filter_upwards [hsliceae, Work.H2.T1Q.ae_mem_Ioo_Iθ] with θ hint hθ
  intro z hz
  have hθI : θ ∈ Work.Spaces.Iθ :=
    Set.mem_Icc.mpr ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hintpsi : MeasureTheory.IntegrableOn
      (fun s => Work.FTS.Nonlinear.RadialProd.psiZ h s θ) Work.Spaces.Iz := by
    refine MeasureTheory.Integrable.mono' hint ?_ ?_
    · refine Work.H2.T1Q.aesm_Iz_of_continuousOn ?_
      exact (Work.FTS.Nonlinear.RadialProd.continuousOn_psiZ h hsh).comp
        ((continuous_id.prodMk continuous_const).continuousOn)
        (fun s hs => ⟨hs, hθ⟩)
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun s _ => ?_)
      rw [Real.norm_of_nonneg (Work.FTS.Nonlinear.RadialProd.psiZ_nonneg h s θ)]
      exact Work.FTS.Nonlinear.RadialProd.psiZ_le_HkIntegrand_of_Ioo α h hθ s
  exact Work.FTS.Nonlinear.RadialProd.g_sq_le_Qg (g := h) hsh hθ
    (hdec θ hθI) hintpsi hz

end Work.FTS.Nonlinear.Open.Row24Aux
