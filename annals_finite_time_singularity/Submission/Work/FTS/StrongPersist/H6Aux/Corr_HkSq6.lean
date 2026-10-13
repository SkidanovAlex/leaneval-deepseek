import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.CoercivityFix.Basic
import Submission.Work.FTS.StrongPersist.Defs
import Submission.Work.FTS.StrongPersist.L6Aux.L12SlotSum6
import Submission.Work.FTS.StrongPersist.L6Aux.HkIntegrandSepLeGen
import Submission.Work.FTS.StrongPersist.H6Aux.CorrAux
import Submission.Work.FTS.StrongPersist.H6Aux.RadialAsm
import Submission.Work.FTS.StrongPersist.H6Aux.Mth6_integral_bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Aux

/-- **The `ℋ⁶`-norm of the nonlocal correction `Corr α f`.**

`Corr α f = Γ(θ)·radA α f z` is a product of the angular function `Γ = Gam α` and the radial
profile `radA α f` (`CoercivityFix.Transfer.Corr_eq_radA`), so the separation bound
`L6Aux.HkIntegrandSepLeGen` at level six gives

`HkIntegrand α 6 (Corr α f) z θ ≤ c(α)²·Mth6 α θ·SlotSum (radA α f) z`  (`θ ∈ Iθ`),

and both one-dimensional factors are bounded uniformly in `α ∈ (0,1]`:

* `∫_θ Mth6 α ≤ Cang` (`H6Aux.Mth6_integral_bound`),
* `∫_z SlotSum (radA α f) ≤ Crad·HkSq α 6 f` (`H6Aux.Alt_SlotSum_radA_le'`),

whence `HkSq α 6 (Corr α f) ≤ 100·Cang·Crad·HkSq α 6 f` (`c(α) ≤ 10`, `Spaces.c_bounds`). -/
theorem Corr_HkSq6 : ∃ C α₂ : ℝ, 0 < C ∧ 0 < α₂ ∧ ∀ α ∈ Set.Ioc 0 α₂, ∀ f : ℝ → ℝ → ℝ,
    Work.FTS.StrongPersist.H6Adm α f → Work.Spaces.HkMem α 7 f →
      Work.Spaces.HkMem α 6 (Work.FTS.CoercivityFix.Corr α f) ∧
      Work.Spaces.HkSq α 6 (Work.FTS.CoercivityFix.Corr α f)
        ≤ C * Work.Spaces.HkSq α 6 f := by
  obtain ⟨Cang, hCangpos, hang⟩ := Mth6_integral_bound
  obtain ⟨Crad, _hCradpos, hrad⟩ := Alt_SlotSum_radA_le'
  refine ⟨100 * Cang * Crad, 1, by positivity, one_pos, ?_⟩
  intro α hαIoc f hf hmem7
  have hα : 0 < α := hαIoc.1
  have hα1 : α ≤ 1 := hαIoc.2
  have hsm : Work.FTS.EllipticEst.SmoothOpen f := hf.reg.1
  have hmem := HkMem_Corr_of hα hα1 hsm hmem7 hang (hrad α hαIoc f hf hmem7)
  refine ⟨hmem, ?_⟩
  exact HkSq_Corr_le_of hα hα1 hmem (le_of_lt hCangpos) (hang α hαIoc)
    (hrad α hαIoc f hf hmem7)

end Work.FTS.StrongPersist.H6Aux
