import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Coercivity

open MeasureTheory Set

theorem integrableOn_Ioi_of_Icc_support {g : ℝ → ℝ} {c d : ℝ} (hc : 0 < c)
    (hcont : ContinuousOn g (Set.Icc c d))
    (hzero : ∀ z ∈ Set.Ioi 0, z ∉ Set.Icc c d → g z = 0) :
    MeasureTheory.IntegrableOn g (Set.Ioi 0) := by
  -- `g` is continuous on the compact set `Icc c d`, hence integrable there.
  have h_int : IntegrableOn g (Set.Icc c d) :=
    ContinuousOn.integrableOn_compact isCompact_Icc hcont
  -- Decompose `Ioi 0` into the part inside `Icc c d` and the part outside it.
  have h1 : IntegrableOn g (Set.Ioi 0 ∩ Set.Icc c d) :=
    h_int.mono_set Set.inter_subset_right
  have h2 : IntegrableOn g (Set.Ioi 0 \ Set.Icc c d) := by
    have hst : EqOn (fun _ : ℝ => (0 : ℝ)) g (Set.Ioi 0 \ Set.Icc c d) := by
      intro x hx
      rw [mem_sdiff, mem_Ioi] at hx
      exact (hzero x hx.1 hx.2).symm
    exact integrableOn_zero.congr_fun hst (measurableSet_Ioi.diff measurableSet_Icc)
  have hunion : IntegrableOn g ((Set.Ioi 0 ∩ Set.Icc c d) ∪ (Set.Ioi 0 \ Set.Icc c d)) :=
    h1.union h2
  have hset : (Set.Ioi 0 ∩ Set.Icc c d) ∪ (Set.Ioi 0 \ Set.Icc c d) = Set.Ioi 0 := by
    ext x
    simp only [mem_union, mem_inter_iff, mem_sdiff, mem_Ioi, mem_Icc]
    tauto
  rwa [hset] at hunion

end Work.Coercivity
