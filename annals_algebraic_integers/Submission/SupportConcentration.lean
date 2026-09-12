import Submission.Serre
import Submission.SerreExample

/-!
# Support concentration of Serre's measure on `[a,b]`

For `0 < a ≤ b`, Serre's measures `ν` and `μ = γ·ν + (1−γ)·μ_eq` give full
mass to the interval `[a,b]` (mass 0 on its complement).  This is the
`support` input needed when applying Smith's converse theorem
(`Submission.Converse.smith_converse_interval`) to Serre's measure.
-/

noncomputable section

open MeasureTheory
open scoped Real ENNReal

namespace Submission.SupportConcentration

open Submission.Equilibrium
open Submission.Serre

/-- Inversion sends the interval `[1/b, 1/a]` into `[a,b]` for `0 < a ≤ b`. -/
lemma inv_mem_Icc {a b x : ℝ} (ha : 0 < a) (hb : 0 < b) (hx : 0 < x)
    (hx1 : b⁻¹ ≤ x) (hx2 : x ≤ a⁻¹) : x⁻¹ ∈ Set.Icc a b := by
  constructor
  · simpa [one_div, inv_inv] using (one_div_le_one_div_of_le hx hx2)
  · simpa [one_div, inv_inv] using (one_div_le_one_div_of_le (inv_pos.mpr hb) hx1)

/-- `ν` gives zero mass to the complement of `[a,b]` (for `0 < a ≤ b`). -/
lemma nu_compl_Icc {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    nu a b ((Set.Icc a b)ᶜ) = 0 := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hcd : (b : ℝ)⁻¹ ≤ a⁻¹ := by
    simpa using (one_div_le_one_div_of_le ha hab)
  -- on the interval [1/b, 1/a], inversion lands inside [a,b]
  have hsub : invMap ⁻¹' ((Set.Icc a b)ᶜ) ⊆ (Set.Icc (b⁻¹) (a⁻¹))ᶜ := by
    intro x hx
    rw [Set.mem_preimage] at hx
    intro hmem
    exact hx (inv_mem_Icc ha hb (lt_of_lt_of_le (inv_pos.mpr hb) hmem.1) hmem.1 hmem.2)
  unfold nu
  rw [Measure.map_apply invMap_measurable (MeasurableSet.compl isClosed_Icc.measurableSet)]
  refine le_antisymm ?hle ?hge
  · exact le_trans (measure_mono hsub) (le_of_eq (equilibrium_compl_Icc (b⁻¹) (a⁻¹) hcd))
  · simp

/-- Serre's measure `μ = γ·ν + (1−γ)·μ_eq` gives zero mass to the complement
of `[a,b]` (for `0 < a ≤ b`, `0 ≤ γ ≤ 1`). -/
lemma serre_compl_Icc {a b γ : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    serreMeasure γ a b ((Set.Icc a b)ᶜ) = 0 := by
  unfold serreMeasure
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
      nu_compl_Icc ha hab, equilibrium_compl_Icc a b hab]
  simp

end Submission.SupportConcentration
