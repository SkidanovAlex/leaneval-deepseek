/-
# `starSlotShift` — the shifted star slots `z/(1+z)·F_*`, `z/(1+z)·D_θF_*`, `z/(1+z)·D_zF_*`

The three "star slots" of the `N`-row of the level-six nonlinear estimate
(`Work.FTS.StrongPersist.H6Rows.Npair6SupAux.FKstarSlotPiece`, `.../radialSupMul`) are the
products of `D_z^j D_θ^i F_*` (`(i,j) = (0,0), (1,0), (0,1)`) with the radial multiplier
`z ↦ z/(1+z)`.  This file proves that they are `C^∞` on the open quadrant, honest in `ℋ⁶`, and
that their `ℋ⁶`-norms are bounded by `C·α⁻¹` with `C` universal.

## Route (details in the companion modules `StarSlotPcs/`)

Write `ρ₀(z) = 2z²/(1+z)³`, so that (with `AK α = (Γ(θ)/c α)·ρ₀(z)`, `Work.Construction.AK`)

* `z/(1+z)·F_* = α·AK α` (`StarSlotPcs/AKSlot.lean`, `zShift_Fstar_eq`);
* `z/(1+z)·D_θF_* = (α qfun θ)·(α·AK α)` (`StarSlotPcs/Identities.lean` + `DthSlot.lean`),
  where `D_θF_* = α qfun θ·F_*` (`Work.Spaces.dthU_Gam`);
* `z/(1+z)·D_zF_* = ((1-z)/(1+z))·(α·AK α)` (`StarSlotPcs/Identities.lean` + `DzSlot.lean`).

* `StarSlotPcs/AKSlot.lean`: the `F_*`-slot, from the sharp pointwise bound `AK6.AK_integrand_le6`
  and `HkIntegrand_const_mul`;
* `StarSlotPcs/DthSlot.lean`: the `D_θF_*`-slot, from the angular-multiplier estimate
  `L3Rhs.ang_mul_HkSq_le`;
* `StarSlotPcs/DzSlot.lean`: the `D_zF_*`-slot, from `radialBounded6_majorant` (this directory)
  and `DzdIter_oneSubOneAdd_le_local` (`StarSlotPcs/DzdIterBound.lean`);
* `StarSlotPcs/Congr.lean`: transport of `HkIntegrand`/`HkMem`/`HkSq` from the separated shapes
  to the functions occurring in the statement, on the *closed* domain `Iz × Iθ`.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.Construction.Defs
import Submission.Work.FTS.NonlinRows.NRow10aux.hkmem_of_majorant
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.N0SlotSplitAux
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.StarSlotPcs.DzdIterBound
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.StarSlotPcs.AKSlot
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.StarSlotPcs.DthSlot
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.StarSlotPcs.DzSlot

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6SupAux

open scoped Real Topology

noncomputable section

set_option maxHeartbeats 1600000

/-- Multiplication of a `C^∞`-quadrant function by the radial factor `z/(1+z)`. -/
theorem smoothOpen_zShift {g : ℝ → ℝ → ℝ} (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => z / (1 + z) * g z θ) := by
  refine Work.FTS.StrongPersist.H6Pair6Aux.so_mul
    (Work.FTS.StrongPersist.H6Pair6Aux.so_radial (fun n => ?_)) hg
  exact contDiffOn_id.div (contDiffOn_const.add contDiffOn_id) (fun z hz => by
    have hz' := hz; simp only [Set.mem_Ioi] at hz'; positivity)

theorem starSlotShift : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    (Work.FTS.EllipticEst.SmoothOpen (fun z θ => z / (1 + z) * Work.Construction.Fstar α z θ) ∧
      Work.Spaces.HkMem α 6 (fun z θ => z / (1 + z) * Work.Construction.Fstar α z θ) ∧
      Work.Spaces.HkNorm α 6 (fun z θ => z / (1 + z) * Work.Construction.Fstar α z θ)
        ≤ C * α ^ (-(1 : ℝ))) ∧
    (Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => z / (1 + z) * Work.Spaces.Dth (Work.Construction.Fstar α) z θ) ∧
      Work.Spaces.HkMem α 6
        (fun z θ => z / (1 + z) * Work.Spaces.Dth (Work.Construction.Fstar α) z θ) ∧
      Work.Spaces.HkNorm α 6
        (fun z θ => z / (1 + z) * Work.Spaces.Dth (Work.Construction.Fstar α) z θ)
        ≤ C * α ^ (-(1 : ℝ))) ∧
    (Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => z / (1 + z) * Work.Spaces.Dz (Work.Construction.Fstar α) z θ) ∧
      Work.Spaces.HkMem α 6
        (fun z θ => z / (1 + z) * Work.Spaces.Dz (Work.Construction.Fstar α) z θ) ∧
      Work.Spaces.HkNorm α 6
        (fun z θ => z / (1 + z) * Work.Spaces.Dz (Work.Construction.Fstar α) z θ)
        ≤ C * α ^ (-(1 : ℝ))) := by
  obtain ⟨B, hB, hbnd⟩ := DzdIter_oneSubOneAdd_le_local
  obtain ⟨CA, hCA, hA⟩ := starSlotA
  obtain ⟨CB, hCB, hB'⟩ := starSlotB
  obtain ⟨CC, hCC, hC⟩ := starSlotC_aux hB hbnd
  refine ⟨max (max CA CB) CC + 1, by positivity, ?_⟩
  intro α hαIoc
  have hα : 0 < α := hαIoc.1
  have hα1 : α ≤ 1 := hαIoc.2
  obtain ⟨hAm, hAn⟩ := hA α hαIoc
  obtain ⟨hBm, hBn⟩ := hB' α hαIoc
  obtain ⟨hCm, hCn⟩ := hC α hαIoc
  have hαinv : 1 ≤ α ^ (-(1 : ℝ)) := by
    rw [show (-(1 : ℝ)) = -1 by ring, Real.rpow_neg_one]
    exact (one_le_inv₀ hα).mpr hα1
  have hkey : ∀ D : ℝ, D ≤ max (max CA CB) CC → D ≤ (max (max CA CB) CC + 1)
      * α ^ (-(1 : ℝ)) := by
    intro D hD
    have h1 : D ≤ max (max CA CB) CC + 1 := by linarith
    have h2 : max (max CA CB) CC + 1
        ≤ (max (max CA CB) CC + 1) * α ^ (-(1 : ℝ)) := by
      simpa using mul_le_mul_of_nonneg_left hαinv
        (show (0 : ℝ) ≤ max (max CA CB) CC + 1 by positivity)
    exact le_trans h1 h2
  refine ⟨⟨smoothOpen_zShift (Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_Fstar α), hAm,
      le_trans hAn (hkey CA (le_trans (le_max_left CA CB) (le_max_left _ _)))⟩,
    ⟨smoothOpen_zShift (Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_Fstar α).Dth, hBm,
      le_trans hBn (hkey CB (le_trans (le_max_right CA CB) (le_max_left _ _)))⟩,
    ⟨smoothOpen_zShift (Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_Fstar α).Dz, hCm,
      le_trans hCn (hkey CC (le_max_right _ _))⟩⟩

end

end Work.FTS.StrongPersist.H6Rows.Npair6SupAux
