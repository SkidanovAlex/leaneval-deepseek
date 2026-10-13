import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Submission.Work.CoreResiduals.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals

/-- Pointwise-in-`y` mean value bound: if the second time derivative of a spacetime field `ω`
is bounded by `C` on the interval `Icc a b` (and exists there), then the first time derivative
is `C`-Lipschitz in time on `Ioo a b`.  This is the mean value theorem on the convex set
`Icc a b`. -/
theorem norm_timeDeriv_sub_le_of_secondDeriv_bound
    {ω : EuclideanSpace ℝ (Fin 3) → ℝ → EuclideanSpace ℝ (Fin 3)} {a b C : ℝ}
    (hdiff : ∀ y : EuclideanSpace ℝ (Fin 3), ∀ z ∈ Set.Icc a b,
      HasDerivAt (fun s => FiniteTimeSingularity.timeDeriv ω y s)
        (FiniteTimeSingularity.timeDeriv (FiniteTimeSingularity.timeDeriv ω) y z) z)
    (hbd : ∀ y : EuclideanSpace ℝ (Fin 3), ∀ z ∈ Set.Icc a b,
      ‖FiniteTimeSingularity.timeDeriv (FiniteTimeSingularity.timeDeriv ω) y z‖ ≤ C) :
    ∀ t ∈ Set.Ioo a b, ∀ t' ∈ Set.Ioo a b, ∀ y : EuclideanSpace ℝ (Fin 3),
      ‖FiniteTimeSingularity.timeDeriv ω y t - FiniteTimeSingularity.timeDeriv ω y t'‖
        ≤ C * |t - t'| := by
  intro t ht t' ht' y
  have htI : t ∈ Set.Icc a b := Set.Ioo_subset_Icc_self ht
  have ht'I : t' ∈ Set.Icc a b := Set.Ioo_subset_Icc_self ht'
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun s => FiniteTimeSingularity.timeDeriv ω y s)
      (f' := fun z => FiniteTimeSingularity.timeDeriv (FiniteTimeSingularity.timeDeriv ω) y z)
      (s := Set.Icc a b) (C := C)
      (fun z hz => (hdiff y z hz).hasDerivWithinAt)
      (fun z hz => hbd y z hz)
      (convex_Icc a b) ht'I htI
  simpa [Real.norm_eq_abs] using h

end Work.CoreResiduals
