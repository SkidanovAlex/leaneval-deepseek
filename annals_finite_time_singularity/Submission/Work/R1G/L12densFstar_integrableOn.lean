import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Submission.Work.R1G.Defs
import Submission.Work.Construction.L12_Fstar_eq
import Submission.Work.FM.Core

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.R1G

/-- For `α > 0`, `F_*(s)/s = 2 (1+s)^{-2}` — the elementary form of the model density. -/
private theorem Fstar_div_self_eq (s : ℝ) (hs : 0 < s) :
    Work.FM.Fstar s / s = 2 * (s + 1) ^ (-2 : ℝ) := by
  have hs1 : (0 : ℝ) < s + 1 := by linarith
  have h2 : (s + 1) ^ (-2 : ℝ) = 1 / (s + 1) ^ 2 := by
    simp only [Real.rpow_neg (le_of_lt hs1), Real.rpow_ofNat, one_div]
  rw [h2]
  unfold Work.FM.Fstar
  field_simp
  ring

theorem L12densFstar_integrableOn {α : NNReal} (P : Work.ConstructionInstance.ProfileData α)
    {z : ℝ} (hz : 0 ≤ z) :
    MeasureTheory.IntegrableOn
      (Work.Construction.L12dens (Work.Construction.Fstar (Work.ConstructionInstance.profExp α)))
      (Set.Ioi z) := by
  have hp : 0 < Work.ConstructionInstance.profExp α :=
    Work.ConstructionInstance.profExp_pos P.hα
  have hp1 : Work.ConstructionInstance.profExp α ≤ 1 := by
    rw [Work.ConstructionInstance.profExp]
    linarith [P.hα13]
  -- the density is the elementary function `profExp α * (F_*(s)/s)`
  have hden : ∀ s ∈ Set.Ioi z,
      Work.Construction.L12dens (Work.Construction.Fstar (Work.ConstructionInstance.profExp α)) s
        = Work.ConstructionInstance.profExp α * (Work.FM.Fstar s / s) :=
    fun s _ => Work.Construction.L12dens_Fstar hp hp1 s
  -- `s ↦ (1+s)^{-2}` is integrable on `(z,∞)` for `z ≥ 0`
  have hA : MeasureTheory.IntegrableOn (fun s : ℝ => (s + 1) ^ (-2 : ℝ)) (Set.Ioi z) :=
    integrableOn_add_rpow_Ioi_of_lt (by norm_num) (by linarith : -(1 : ℝ) < z)
  refine MeasureTheory.IntegrableOn.congr_fun
    (hA.const_mul (2 * Work.ConstructionInstance.profExp α)) ?_ measurableSet_Ioi
  intro s hs
  rw [hden s hs, Fstar_div_self_eq s (lt_of_le_of_lt hz hs)]
  ring

end Work.R1G
