/-
# ZeroFreeTables — TentFmEq

The three elementary facts about the tent's Laplace transform `tentFm` of `HB88TentDefs`,
collected at the same place because every tent engine and extraction lemma needs some of them:

* `∫₀^X e^{σt}·tent X t = tentFm σ X` — `TentLaplace`;
* `σ ↦ tentFm σ X` is monotone — `TentExtract.tentFm_mono`;
* `Re ∫₀^X e^{−zt}·tent X t ≥ 0` for `Re z ≥ 0` (HB's "Condition 2" for the tent) —
  `Work.LinnikAreas.triangle_hFnn`, whose integrand is literally `tent X`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.HB88TentDefs
import Submission.Work.ZeroFreeTables.TentLaplace
import Submission.Work.ZeroFreeTables.TentExtract
import Submission.Work.LinnikAreas.triangle_hFnn

open MeasureTheory
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables

theorem TentFmEq (X : ℝ) (hX : 0 < X) :
    (∀ σ : ℝ, (∫ t in (0:ℝ)..X, Real.exp (σ * t) * Work.ZeroFreeTables.tent X t)
        = Work.ZeroFreeTables.tentFm σ X) ∧
    Monotone (fun σ : ℝ => Work.ZeroFreeTables.tentFm σ X) ∧
    (∀ z : ℂ, 0 ≤ z.re → 0 ≤ (∫ t in (0:ℝ)..X,
        Complex.exp (-(z * (t : ℂ))) * (((Work.ZeroFreeTables.tent X t : ℝ)) : ℂ)).re) :=
  ⟨fun σ => Work.ZeroFreeTables.TentLaplace X σ hX,
   Work.ZeroFreeTables.tentFm_mono X hX.le,
   fun z hz => Work.LinnikAreas.triangle_hFnn hX z hz⟩

end Work.ZeroFreeTables
