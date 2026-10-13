import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS_RegExport.RXT.datum_bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `datum_jets` — the localised datum is `O(ω)` with all jets `j ≤ 8`, `i ≤ 6`

Same argument as `Work.FTS_RegExport.RXT.datum_bound` (which handles the six index pairs
`RXT.idx k`), but for the *full* index rectangle `j ≤ 8`, `i ≤ 6` needed by the strong-solution
route.  The two ingredients are

* the radial pointwise bound `|D_z^j locR| ≤ A·z²/(1+z)²` for `j ≤ 8`
  (`Work.FTS_RegExport.RXT.radial_jet_omega_local`), and
* the angular jet bound `|D_θ^i Γ| ≤ 10⁵·Γ` for `i ≤ 6`
  (`Work.FTS.LocData6.DthIter_Gam_abs_le6`),

combined through the separability identity `Work.FTS.LocDataExt.mixed_sepGam` and the
identification `Gam (pExp α) = Gamma α` of the two angular factors.
-/

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory

namespace Work.FTS_RegExport.RXT.Sys

/-- **The localised datum `locG6 (pExp α) L β` is `O(ω)` with all mixed jets `j ≤ 8`, `i ≤ 6`**,
`ω α z θ = z²·Γ(θ)/(1+z)²` being the self-similar weight.  The datum is separable,
`locG6 = locR(z)·Γ(θ)`, so the statement is the product of the radial jet bound (order ≤ 8) and
the angular jet bound (order ≤ 6). -/
theorem datum_jets {α L β : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3) (hL : 1 ≤ L) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ j i : ℕ, j ≤ 8 → i ≤ 6 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed j i (Work.FTS.LocData6.locG6 (Work.FTS.Regularity.pExp α) L β) z θ|
        ≤ K * Work.FTS.RegExportIface.ω α z θ := by
  obtain ⟨A, hA0, hA⟩ := Work.FTS_RegExport.RXT.radial_jet_omega_local hα hα13 hL
  refine ⟨100000 * A, mul_nonneg (by norm_num) hA0, fun j i hj hi z θ hz hθ0 hθ1 => ?_⟩
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ0, le_of_lt hθ1⟩
  have hrad := hA j hj z θ hz
  have hang := Work.FTS.LocData6.DthIter_Gam_abs_le6 i hi (Work.FTS.Regularity.pExp α)
    (Work.FTS.Regularity.pExp_pos hα) (Work.FTS.Regularity.pExp_le_one hα13) hθI
  have hfac : Work.FTS.LocData6.locG6 (Work.FTS.Regularity.pExp α) L β
      = fun z θ => Work.FTS.LocDataExt.locR (Work.FTS.Regularity.pExp α) L β z
          * Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ := by
    rw [Work.FTS.LocData6.locG6_eq, Work.FTS.LocDataExt.locG_eq_locR_Gam]
  rw [hfac, Work.FTS.LocDataExt.mixed_sepGam, abs_mul]
  refine (mul_le_mul hrad hang (abs_nonneg _) (mul_nonneg hA0 (by positivity))).trans ?_
  have heq : (A * (z ^ 2 / (1 + z) ^ 2))
        * (100000 * Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ)
      = (100000 * A) * Work.FTS.RegExportIface.ω α z θ := by
    rw [Work.FTS_RegExport.RXT.Gam_pExp_eq_Gamma, Work.FTS.RegExportIface.ω]
    ring
  exact le_of_eq heq

end Work.FTS_RegExport.RXT.Sys
