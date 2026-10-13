/-
  annals_wilkies_conjecture, AREA E3K (`Submission.Work.WilE3K`): the `ETSliceNull` genericity
  input of `Work.WilE3K.ET_good_exists` (independent of the delegated
  `Work.WilE3K.ETSlice_bad_null`).

  `E.ETSliceNull y` says that above `y` the critical values of the Rolle determinant form a null
  set.  The complement is exactly the set of `y` whose slice of the null set
  `E.rolleMap '' {z | det (fderiv ℝ E.rolleMap z) = 0}` is *not* null: Sard's lemma in the square
  case (`Work.WilE2.sard_square`, applied to the `C²` map `E.rolleMap`, cf.
  `ETData.rcF_contDiff_rolleMap`) says that this image is null, and Fubini
  (`Work.WilE2.slice_null_ae`) says that almost every slice of a null set is null.
-/
import Mathlib
import Submission.Work.WilE3K.ET
import Submission.Work.WilE3K.Elim
import Submission.Work.WilE3K.rolleDetFun_crossField
import Submission.Work.WilE2.sard_square
import Submission.Work.WilE2.slice_null_ae

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical Topology Filter MeasureTheory
namespace Work.WilE3K
open WilkiesConjecture WilkiesDesign WilkiesDesign.E

theorem ETSliceBadNull {N rt n re : ℕ} (E : ETData N (rt + 1) n re) :
    MeasureTheory.volume {y : Fin N → ℝ | ¬ E.ETSliceNull y} = 0 := by
  have hdiff : ∀ z : Fin (N + 1) → ℝ, HasFDerivAt E.rolleMap (fderiv ℝ E.rolleMap z) z :=
    fun z => ((E.rcF_contDiff_rolleMap.contDiffAt).differentiableAt
      (by norm_num : (2 : WithTop ℕ∞) ≠ 0)).hasFDerivAt
  have hN : MeasureTheory.volume
      (E.rolleMap '' {z : Fin (N + 1) → ℝ | (fderiv ℝ E.rolleMap z).det = 0}) = 0 :=
    Work.WilE2.sard_square E.rolleMap (fderiv ℝ E.rolleMap) hdiff
  have h := Work.WilE2.slice_null_ae hN
  simpa only [ETData.ETSliceNull, ne_eq] using h

end Work.WilE3K
