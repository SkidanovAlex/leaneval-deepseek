import Mathlib.Order.CompletePartialOrder
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.block13_fibre_L2
import Submission.Work.BoseBoxFock.blockII1_fibre_L2
import Submission.Work.BoseBoxFock.blockTwo3_fibre_L2
import Submission.Work.BoseBoxFock.pairRowS2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.pairRowS2Inst` — the box-restricted fibre `L²` bounds

The fibre `L²` bounds `block13_fibre_L2`, `blockTwo3_fibre_L2`, `blockII1_fibre_L2` are stated over
all of `ℝ³ × ℝ³`; the block-level (S2) substitutions of `pairRowS2` consume them over the box
squared.  Because each fibre function is **supported in the box squared** whenever the state `Θ`
is, the two integrals agree (`integral_integral_eq_iterated_boxL`), so the restricted form is an
immediate corollary.  This module provides those corollaries, which discharge the `hGle` hypothesis
of `block13_Ksub` / `blockTwo3_Ksub` / `blockII1_Ksub`.

The fibre-support hypothesis `hCsupp` is exactly what `pairRowS2`'s block lemmas take; it follows
from `Function.support Θ ⊆ Work.MB.boxPow n ℓ` because each of `pairG13`, `pairG23`, `pairG21` has
`Θ` evaluated at a configuration in which one of the two kernel slots is frozen to the corresponding
kernel variable (`insertCoord` / `insertCoord2` / `Function.update`), so that variable must lie in
the box.

Everything here is `sorry`-free.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The support of `‖𝓖‖²` is contained in that of `𝓖`. -/
theorem support_normSq_uncurry_le {𝓖 : E3 → E3 → ℂ} :
    Function.support (Function.uncurry (fun w y : E3 => ‖𝓖 w y‖ ^ 2))
      ⊆ Function.support (Function.uncurry 𝓖) := by
  intro z hz
  exact Function.mem_support.mpr (fun h => Function.mem_support.mp hz (by
    show ‖𝓖 z.1 z.2‖ ^ 2 = 0
    rw [show 𝓖 z.1 z.2 = 0 from h, norm_zero, zero_pow (by norm_num : (2:ℕ) ≠ 0)]))

/-- **Box-restricted form of `block13_fibre_L2`.** -/
theorem pairG13_L2 {n : ℕ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2) {ℓ : ℝ}
    {Θ : Work.BoseDict.Xn n → ℂ} {A B : E3 → ℂ}
    (hCsupp : Function.support (Function.uncurry (pairG13 p Θ A B)) ⊆
      Set.prod (Work.BoseK15.corpusBox.boxL ℓ) (Work.BoseK15.corpusBox.boxL ℓ))
    (hΘm : MeasureTheory.AEStronglyMeasurable Θ)
    (hΘL : MeasureTheory.Integrable (fun x => ‖Θ x‖ ^ 2))
    (hAm : MeasureTheory.AEStronglyMeasurable A)
    (hAL : MeasureTheory.Integrable (fun x => ‖A x‖ ^ 2))
    (hBm : MeasureTheory.AEStronglyMeasurable B)
    (hBL : MeasureTheory.Integrable (fun x => ‖B x‖ ^ 2)) :
    ∫ w in Work.BoseK15.corpusBox.boxL ℓ,
        ∫ y in Work.BoseK15.corpusBox.boxL ℓ, ‖pairG13 p Θ A B w y‖ ^ 2
      ≤ (∫ x, ‖A x‖ ^ 2) * (∫ x, ‖B x‖ ^ 2) * (∫ x, ‖Θ x‖ ^ 2) ^ 2 := by
  rw [← integral_integral_eq_iterated_boxL (f := fun w y : E3 => ‖pairG13 p Θ A B w y‖ ^ 2)
    ((support_normSq_uncurry_le (𝓖 := pairG13 p Θ A B)).trans hCsupp)]
  exact block13_fibre_L2 p hp hΘm hΘL hAm hAL hBm hBL

/-- **Box-restricted form of `blockTwo3_fibre_L2`.** -/
theorem pairG23_L2 {n : ℕ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2) {ℓ : ℝ}
    {Θ : Work.BoseDict.Xn n → ℂ} {A B : E3 → ℂ}
    (hCsupp : Function.support (Function.uncurry (pairG23 p Θ A B)) ⊆
      Set.prod (Work.BoseK15.corpusBox.boxL ℓ) (Work.BoseK15.corpusBox.boxL ℓ))
    (hΘm : MeasureTheory.AEStronglyMeasurable Θ)
    (hΘL : MeasureTheory.Integrable (fun x => ‖Θ x‖ ^ 2))
    (hAm : MeasureTheory.AEStronglyMeasurable A)
    (hAL : MeasureTheory.Integrable (fun x => ‖A x‖ ^ 2))
    (hBm : MeasureTheory.AEStronglyMeasurable B)
    (hBL : MeasureTheory.Integrable (fun x => ‖B x‖ ^ 2)) :
    ∫ w in Work.BoseK15.corpusBox.boxL ℓ,
        ∫ y in Work.BoseK15.corpusBox.boxL ℓ, ‖pairG23 p Θ A B w y‖ ^ 2
      ≤ (∫ x, ‖A x‖ ^ 2) * (∫ x, ‖B x‖ ^ 2) * (∫ x, ‖Θ x‖ ^ 2) ^ 2 := by
  rw [← integral_integral_eq_iterated_boxL (f := fun w y : E3 => ‖pairG23 p Θ A B w y‖ ^ 2)
    ((support_normSq_uncurry_le (𝓖 := pairG23 p Θ A B)).trans hCsupp)]
  exact blockTwo3_fibre_L2 p hp hΘm hΘL hAm hAL hBm hBL

/-- **Box-restricted form of `blockII1_fibre_L2`.** -/
theorem pairG21_L2 {n : ℕ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2) {ℓ : ℝ}
    {Θ : Work.BoseDict.Xn n → ℂ} {A : E3 → ℂ}
    (hCsupp : Function.support (Function.uncurry (pairG21 p Θ A)) ⊆
      Set.prod (Work.BoseK15.corpusBox.boxL ℓ) (Work.BoseK15.corpusBox.boxL ℓ))
    (hΘm : MeasureTheory.AEStronglyMeasurable Θ)
    (hΘL : MeasureTheory.Integrable (fun x => ‖Θ x‖ ^ 2))
    (hAm : MeasureTheory.AEStronglyMeasurable A)
    (hAL : MeasureTheory.Integrable (fun x => ‖A x‖ ^ 2)) :
    ∫ w in Work.BoseK15.corpusBox.boxL ℓ,
        ∫ y in Work.BoseK15.corpusBox.boxL ℓ, ‖pairG21 p Θ A w y‖ ^ 2
      ≤ (∫ x, ‖A x‖ ^ 2) ^ 2 * (∫ x, ‖Θ x‖ ^ 2) ^ 2 := by
  rw [← integral_integral_eq_iterated_boxL (f := fun w y : E3 => ‖pairG21 p Θ A w y‖ ^ 2)
    ((support_normSq_uncurry_le (𝓖 := pairG21 p Θ A)).trans hCsupp)]
  exact blockII1_fibre_L2 p hp hΘm hΘL hAm hAL

end Work.BoseBoxFock
