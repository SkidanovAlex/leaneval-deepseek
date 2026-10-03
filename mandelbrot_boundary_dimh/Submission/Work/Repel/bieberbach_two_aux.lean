import Mathlib
import Submission.Work.Repel.Koebe.area_theorem
import Submission.Work.Repel.Koebe.bieberbach_two_of_area

/-!
# Bieberbach's second coefficient inequality, from the area theorem

`‖f''(0)‖ ≤ 4` for a normalised univalent `f` on the unit disc, derived from Grönwall's area
theorem (`Work.Repel.Koebe.area_theorem`).  This is a stable re-derivation used by
`Work.Repel.two_point_lower_half_ball`'s dependency chain.
-/

namespace Work.Repel

theorem bieberbach_two_aux {f : ℂ → ℂ}
    (han : ∀ z ∈ Metric.ball (0 : ℂ) 1, AnalyticAt ℂ f z)
    (hinj : Set.InjOn f (Metric.ball (0 : ℂ) 1)) (h0 : f 0 = 0) (h1 : deriv f 0 = 1) :
    ‖iteratedDeriv 2 f 0‖ ≤ 4 :=
  Koebe.bieberbach_two_of_area
    (fun {g : ℂ → ℂ} {b : ℂ} hg hinj hlim => Koebe.area_theorem hg hinj hlim)
    han hinj h0 h1

end Work.Repel
