import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.N6Trans.Hon.Defs
import Submission.Work.FTS.TransportS.SlotT2.SlotIbpDefs
import Submission.Work.Spaces.integrable_prod_of_iterated
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.N6Trans.Hon

/-- The uncurried `ℋ^k`-integrand of a function which is `C^∞` on the open quadrant is
a.e. strongly measurable for the product of the two restricted Lebesgue measures: it is
continuous on the open quadrant, and that quadrant is conull inside `Iz ×ˢ Iθ`. -/
theorem aesm_HkIntegrand_prod_open {α : ℝ} {k : ℕ} {g : ℝ → ℝ → ℝ}
    (hsg : Work.FTS.EllipticEst.SmoothOpen g) :
    MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k g p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
  Work.Spaces.aesm_of_continuousOn_Qd _
    (Work.FTS.EllipticEst.SmoothOpen.continuousOn_HkIntegrand hsg α k)

theorem HkProdOpen {α : ℝ} {k : ℕ} {g : ℝ → ℝ → ℝ}
    (hsg : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α k g) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k g p.1 p.2)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
      (∫ p, Work.Spaces.HkIntegrand α k g p.1 p.2
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ))) = Work.Spaces.HkSq α k g := by
  obtain ⟨hint, hval⟩ := Work.Spaces.integrable_prod_of_iterated
    (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
    (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
    (G := fun z θ => Work.Spaces.HkIntegrand α k g z θ)
    (fun z θ => Work.Spaces.HkIntegrand_nonneg α k g z θ)
    (aesm_HkIntegrand_prod_open hsg)
    ((MeasureTheory.ae_restrict_iff' (show MeasurableSet Work.Spaces.Iz from
      measurableSet_Ici)).mpr (Filter.Eventually.of_forall fun z hz => hmem.1 z hz))
    hmem.2
  exact ⟨hint, by rw [hval]; rfl⟩

end Work.FTS.StrongPersist.N6Trans.Hon
