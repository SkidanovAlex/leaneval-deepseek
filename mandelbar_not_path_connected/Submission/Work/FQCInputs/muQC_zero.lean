import Mathlib
import Submission.Work.FQCInputs.Defs
import Submission.Work.FQC.muQC_aux_beltrami

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FQCInputs

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)
open Work.EL (RootParabolic F K)

/-! ## The deformation coefficient at `t = 0`

At `t = 0` the MNS twist `ℓ_0` is the identity, so its dilatation vanishes identically
(`Work.MRMT.beltramiOf (Work.FQC.ell 0) = 0`); pulling back zero along a holomorphic map
(`pullHoloOn`), along the dynamics (`pullAnti`), any number of times (`pullAntiIter`), and being
`0` outside the basin, gives `muQC d fl P 0 = 0`.  Nothing here uses the flower `fl` or the
parabolic parameter `d`: `muQC` at `t = 0` forgets them. -/

/-- The complex dilatation of the untwisted cylinder map vanishes. -/
theorem beltramiOf_ell_zero : Work.MRMT.beltramiOf (Work.FQC.ell 0) = 0 := by
  rw [Work.FQC.ell_eq_id_zero]
  funext z
  exact Work.MRMT.beltramiOf_id z

/-- Pulling back the zero coefficient along a holomorphic map (guarded on a set) is zero. -/
theorem pullHoloOn_zero (φ : ℂ → ℂ) (P : Set ℂ) : Work.FQC.pullHoloOn 0 φ P = 0 := by
  funext z
  by_cases hz : z ∈ P <;> simp [Work.FQC.pullHoloOn, hz]

/-- Pulling back the zero coefficient along an antiholomorphic map is zero. -/
theorem pullAnti_zero (f : ℂ → ℂ) : Work.FQC.pullAnti 0 f = 0 := by
  funext z
  simp [Work.FQC.pullAnti]

/-- The iterated pull-back of the zero coefficient is zero. -/
theorem pullAntiIter_zero (f : ℂ → ℂ) (n : ℕ) : Work.FQC.pullAntiIter f n 0 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Work.FQC.pullAntiIter_succ, ih, pullAnti_zero]

theorem muQC_zero {c : ℂ} (d : Work.EL.RootParabolic c)
    (fl : Work.FatouCoord.ParabolicFlower (Work.EL.F c) ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) d.z₁)
    (P : Set ℂ) : Work.FQC.muQC d fl P 0 = 0 := by
  funext z
  by_cases hz : z ∈ Work.FQC.basin d P
  · rw [Work.FQC.muQC_of_mem d hz, beltramiOf_ell_zero, pullHoloOn_zero, pullAntiIter_zero]
  · exact Work.FQC.muQC_of_notMem d hz

end Work.FQCInputs
