import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.FreqArc

/-!
# Continuity of the iterated circle convolution

The `n`-fold circle convolution `circConvFin n F` of `FreqArc.lean` is continuous as soon as all
the factors `F i` are.  The proof is the standard one: on the compact circle `𝕋 = ℝ/ℤ` a
continuous function is locally integrable and has compact support, so it is the Mathlib
`MeasureTheory.convolution` with respect to `AddCircle.haarAddCircle`, and
`HasCompactSupport.continuous_convolution_right` gives continuity; the inductive step peels off
the last factor.
-/

open MeasureTheory
open scoped Convolution

namespace Work.BourgainPlan.IonescuWainger

/-- The convolution of two continuous functions on the circle is continuous.  Since the circle is
compact, the second factor has compact support and the first is locally integrable, so this is
Mathlib's `HasCompactSupport.continuous_convolution_right`. -/
lemma continuous_circConv {F G : Circle → ℂ} (hF : Continuous F) (hG : Continuous G) :
    Continuous (circConv F G) := by
  have h : circConv F G = F ⋆[ContinuousLinearMap.mul ℂ ℂ, AddCircle.haarAddCircle] G := rfl
  rw [h]
  exact (HasCompactSupport.of_compactSpace G).continuous_convolution_right _ hF.locallyIntegrable hG

theorem continuous_circConvFin {n : ℕ} {F : Fin n → Circle → ℂ} (hF : ∀ i, Continuous (F i)) :
    Continuous (circConvFin n F) := by
  induction n with
  | zero =>
      have h : circConvFin 0 F = fun _ => (1 : ℂ) := rfl
      rw [h]; exact continuous_const
  | succ m ih =>
      match m with
      | 0 =>
          have h : circConvFin 1 F = F 0 := rfl
          rw [h]; exact hF 0
      | k + 1 =>
          have h : circConvFin (k + 1 + 1) F =
              circConv (circConvFin (k + 1) (fun i : Fin (k + 1) => F i.castSucc))
                (F (Fin.last (k+1))) := rfl
          rw [h]
          exact continuous_circConv (ih (fun i => hF i.castSucc)) (hF _)

end Work.BourgainPlan.IonescuWainger
