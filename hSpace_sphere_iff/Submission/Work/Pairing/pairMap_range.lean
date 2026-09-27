import Mathlib
import Submission.Work.Cohomology.Pairing
import Submission.Work.Cohomology.exists_chain_eval_ne_zero
import Submission.Work.Cohomology.H_equiv_dual_annihilator

namespace Work.Pairing

open Submission.Cohomology

/-- The evaluation pairing on cocycles, as a map into the dual of the cycles, coincides with the
composite of the pairing into the annihilator of the boundaries with the inclusion of that
annihilator into the dual. -/
private lemma pairMapAux_eq_subtype_comp_pairingToAnn (S : SSet.{0}) (n : ℕ) :
    pairMapAux S n
      = (Submodule.subtype ((chainBoundariesInCycles S ℚ n).dualAnnihilator)).comp
          (Work.Cohomology.pairingToAnn S n) := by
  ext u z
  simp only [LinearMap.comp_apply, Submodule.subtype_apply,
    Work.Cohomology.pairingToAnn_apply_val, Work.Cohomology.pairingMap_apply, pairMapAux]
  rfl

theorem pairMap_range (S : SSet.{0}) (n : ℕ) :
    (Submission.Cohomology.pairMap S n).range
      = (Submission.Cohomology.chainBoundariesInCycles S ℚ n).dualAnnihilator := by
  have h1 : (pairMap S n).range = (pairMapAux S n).range := by
    rw [pairMap, Submodule.range_liftQ]
  rw [h1, pairMapAux_eq_subtype_comp_pairingToAnn, LinearMap.range_comp,
    LinearMap.range_eq_top.mpr (Work.Cohomology.pairingToAnn_surjective S n),
    Submodule.map_top, Submodule.range_subtype]

end Work.Pairing
