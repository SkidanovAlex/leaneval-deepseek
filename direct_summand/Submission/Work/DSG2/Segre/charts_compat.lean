import Mathlib
import Submission.Work.DSG2.Segre.Basic
import Submission.Work.DSG2.Segre.projChart_relation
import Submission.Work.DSG2.Segre.chartElemAll_surjective
import Submission.Work.DSG2.Segre.Triangle
import Submission.Work.DSG4c.ChartPushout.chartToPoly_surjective

import Submission.Work.DSG2.Segre.cc_charts
import Submission.Work.DSG2.Segre.cc_final

namespace Work.DSG2.Segre

universe u

open CategoryTheory AlgebraicGeometry Limits MvPolynomial
open scoped TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

theorem charts_compat (A : Type u) [CommRing A] (a b : ℕ) (k k' : Fin (a+1) × Fin (b+1)) :
    CategoryTheory.CategoryStruct.comp
        (CategoryTheory.Limits.pullback.fst (Work.DSG2.Segre.V A a b k).ι
          (Work.DSG2.Segre.V A a b k').ι) (Work.DSG2.Segre.sigma A a b k) =
      CategoryTheory.CategoryStruct.comp
        (CategoryTheory.Limits.pullback.snd (Work.DSG2.Segre.V A a b k).ι
          (Work.DSG2.Segre.V A a b k').ι) (Work.DSG2.Segre.sigma A a b k') := by
  exact ccSigmaF_eq_ccSigmaG A a b k k'

end Work.DSG2.Segre
