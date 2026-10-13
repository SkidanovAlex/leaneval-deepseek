import Mathlib
import Submission.Work.WilE9G.Sard.FlatDefs
import Submission.Work.WilE9G.Sard.volume_image_eq_zero_of_lt

/-!
# The low-dimensional base case of the analytic Sard theorem, on an arbitrary set

`Work.WilE9G.Sard.volume_image_eq_zero_of_lt` proves that for `d < m` the image of an **open**
set under a map analytic on it is Lebesgue-null.  Here the source set `A` is an arbitrary subset
of `ℝᵈ` and only *pointwise* analyticity on it, `∀ x ∈ A, AnalyticAt ℝ F x`, is assumed.

The set `{x | AnalyticAt ℝ F x}` of points at which a map is analytic is open
(`isOpen_analyticAt`), so `A` is contained in the open analyticity locus `U` of `F`; the image
`F '' A` is a subset of `F '' U`, which is null by the open-set case, and a subset of a null set
is null (`measure_mono_null`).
-/

namespace Work.WilE9G.Sard

theorem baseCaseLt {d m : ℕ} (hd : d < m) (hm : 0 < m) (F : (Fin d → ℝ) → (Fin m → ℝ))
    (A : Set (Fin d → ℝ)) (han : ∀ x ∈ A, AnalyticAt ℝ F x) :
    MeasureTheory.volume (F '' A) = 0 := by
  -- The analyticity locus of `F` is open.
  have hU : IsOpen {x : Fin d → ℝ | AnalyticAt ℝ F x} := isOpen_analyticAt ℝ F
  -- `F` is analytic (within its analyticity locus, hence) on it.
  have hAn : AnalyticOn ℝ F {x : Fin d → ℝ | AnalyticAt ℝ F x} :=
    fun x hx => AnalyticAt.analyticWithinAt hx
  -- The open-set case of the low-dimensional Sard theorem.
  have hnull : MeasureTheory.volume (F '' {x : Fin d → ℝ | AnalyticAt ℝ F x}) = 0 :=
    volume_image_eq_zero_of_lt hd F hU hAn
  -- `A` sits inside the analyticity locus, and a subset of a null set is null.
  exact MeasureTheory.measure_mono_null (Set.image_mono fun x hx => han x hx) hnull

end Work.WilE9G.Sard
