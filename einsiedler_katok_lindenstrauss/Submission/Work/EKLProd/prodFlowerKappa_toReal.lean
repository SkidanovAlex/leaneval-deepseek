import Mathlib
import Submission.Work.EKLProd.ProdFlowerAssemblyDefs
import Submission.Work.EKLProd.ProdFlowerLemmas

/-!
`prodFlowerκ` is, by definition, the translate `(νT x) · hT T U (co n x)` restricted to the
`T`-ball `V hf.R ∩ T` and normalised by its total mass.  The lemma records the value of this
normalised measure on a set `A` in terms of the *unnormalised* translate.
-/

namespace Work.EKLProd

open MeasureTheory
open scoped ENNReal

theorem prodFlowerKappa_toReal {H T U : Subgroup Work.EKLContract.SL3} {μ : MeasureTheory.Measure Work.EKLContract.X3}
    (hf : Work.EKLProd.ProdFlowerFam H T U μ) (n : ℕ)
    (νT : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3) (x : Work.EKLContract.X3)
    {A : Set Work.EKLContract.SL3} (hA : MeasurableSet A) :
    (Work.EKLProd.prodFlowerκ hf n νT x A).toReal =
      (((νT x).map (fun g : Work.EKLContract.SL3 => g * Work.EKLProd.hT T U (hf.co n x)))
          (A ∩ (Work.EKLContract.V hf.R ∩ (T : Set Work.EKLContract.SL3)))).toReal
        / (((νT x).map (fun g : Work.EKLContract.SL3 => g * Work.EKLProd.hT T U (hf.co n x)))
          (Work.EKLContract.V hf.R ∩ (T : Set Work.EKLContract.SL3))).toReal := by
  unfold Work.EKLProd.prodFlowerκ
  rw [MeasureTheory.Measure.smul_apply, MeasureTheory.Measure.restrict_apply hA, smul_eq_mul,
    ENNReal.toReal_mul, ENNReal.toReal_inv, div_eq_mul_inv]
  ring

end Work.EKLProd
