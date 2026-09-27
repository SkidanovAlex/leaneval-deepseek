import Mathlib
import Submission.Work.Mostow.geodDeps
import Submission.Work.Mostow.resStd_hom_discrete
import Submission.Work.Mostow.blk_smul_fermi

namespace Work.Mostow

open Submission.Mostow

/-- The normal part `nrmStd 1 m` is multiplicative on the setwise stabiliser of the standard
stratum.  Same argument as `rhd_resStd_mul`: every element of the stabiliser is `blk` of its
restriction and its normal part (`rhd_stab_form`), and `blk` is multiplicative and injective
(`blk_hom`). -/
theorem nrmStd_mul (m : ℕ)
    (hA1 : Submission.Mostow.POActionProp 1) (hI1 : Submission.Mostow.HypIsometryProp 1)
    (hA : Submission.Mostow.POActionProp (1 + m)) (hI : Submission.Mostow.HypIsometryProp (1 + m))
    (g h : LeanEval.Geometry.MostowRigidity.PO (1 + m) 1) (hg : g ∈ Submission.Mostow.SetStabStd 1 m)
    (hh : h ∈ Submission.Mostow.SetStabStd 1 m) :
    Submission.Mostow.nrmStd 1 m (g * h) =
      Submission.Mostow.nrmStd 1 m g * Submission.Mostow.nrmStd 1 m h := by
  have hgh : g * h ∈ Submission.Mostow.SetStabStd 1 m :=
    rhd_mul_mem_stab 1 m hA hg hh
  have e1 := rhd_stab_form 1 m hA1 hI1 hA hI hgh
  have e2 : g * h =
      Submission.Mostow.blk 1 m (Submission.Mostow.resStd 1 m g * Submission.Mostow.resStd 1 m h)
        (Submission.Mostow.nrmStd 1 m g * Submission.Mostow.nrmStd 1 m h) := by
    conv_lhs => rw [rhd_stab_form 1 m hA1 hI1 hA hI hg,
                    rhd_stab_form 1 m hA1 hI1 hA hI hh]
    rw [← (blk_hom 1 m hA1 hI1 hA hI).1]
  exact ((blk_hom 1 m hA1 hI1 hA hI).2.2 _ _ _ _ (e1.symm.trans e2)).2

end Work.Mostow
