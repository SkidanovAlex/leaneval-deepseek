import Mathlib
import Submission.Work.FIChain.Defs
import Submission.Work.FIChain.rhoWindowC_param
import Submission.Work.FIChain.scale_factsC
import Submission.Work.FIChain.window_marginsC
import Submission.Work.FITop.RhoWindowCProp41
import Submission.Work.FIChain.BprimeWindowIntegrated
import Submission.Work.FITop4.Red5.Vocab
import Submission.Work.FIChain.RhoWin2Defs
import Submission.Work.FIChain.RhoWin2Ident
import Submission.Work.FIChain.RhoWin2Bridge
import Submission.Work.FIChain.RhoWin2Box
import Submission.Work.FIChain.RhoWin2Moment
import Submission.Work.FIChain.RhoWin2TailInlined
import Submission.Work.FIChain.RhoWin2Integrable
import Submission.Work.FIChain.RhoWin2Main
import Submission.Work.FIChain.chainWindowFacts
import Submission.Work.FIChain.zc_DpiC_range
import Submission.Work.FIChain.bprime_window_tail_le
import Submission.Work.FIChain.BpWinAux
import Submission.Work.FITop.RCPrelude

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIChain

open Finset MeasureTheory
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

def RhoWindowInt2 (a : ℕ → ℝ) (N : ℕ) (w : ℕ → ℝ) (E C lo hi : ℝ) : Prop :=
  (∫ t in lo..hi, (∫ s in (1 : ℝ)..C,
      (∑ m ∈ Finset.Icc 1 N, w m * |Work.FITop.XrhoC a N m s t (2 * t)|) / s) / t) ≤ E

/-- The pointwise step: the `ρ`-window integrand is dominated by `Wall` (the `Π`-split sum of
the identity `RhoWin2Ident`). -/
lemma XrhoC_le_Wall (x Pz : ℕ) (s t : ℝ) :
    (∑ c ∈ Finset.Icc 1 x, wc c * |Work.FITop.XrhoC atilc x c s t (2 * t)|)
      ≤ Wall x Pz s t := by
  have hμ1 : ∀ c : ℕ, |(ArithmeticFunction.moebius c : ℝ)| ≤ 1 := fun c => by
    have := ArithmeticFunction.abs_moebius_le_one (n := c); exact_mod_cast this
  have key : ∀ c ∈ Finset.Icc 1 x, wc c * |Work.FITop.XrhoC atilc x c s t (2 * t)|
      ≤ ((c.divisors.card : ℝ)) ^ 2 *
        ∑ n₁ ∈ (ProdP Pz).divisors,
          ∑ d₁ ∈ n₁.divisors, |Xpg x Pz (c * n₁) (s / d₁) (t / n₁)| := by
    intro c _
    have h1 : |Work.FITop.XrhoC atilc x c s t (2 * t)| ≤
        ∑ n₁ ∈ (ProdP Pz).divisors,
          ∑ d₁ ∈ n₁.divisors, |Xpg x Pz (c * n₁) (s / d₁) (t / n₁)| := by
      rw [RhoWin2Ident]
      calc |(ArithmeticFunction.moebius c : ℝ) * ∑ n₁ ∈ (ProdP Pz).divisors,
              (ArithmeticFunction.moebius n₁ : ℝ) *
                ∑ d₁ ∈ n₁.divisors, (ArithmeticFunction.moebius d₁ : ℝ) *
                  Xpg x Pz (c * n₁) (s / d₁) (t / n₁)|
          = |(ArithmeticFunction.moebius c : ℝ)| * |∑ n₁ ∈ (ProdP Pz).divisors,
              (ArithmeticFunction.moebius n₁ : ℝ) *
                ∑ d₁ ∈ n₁.divisors, (ArithmeticFunction.moebius d₁ : ℝ) *
                  Xpg x Pz (c * n₁) (s / d₁) (t / n₁)| := by rw [abs_mul]
        _ ≤ 1 * ∑ n₁ ∈ (ProdP Pz).divisors,
              |(ArithmeticFunction.moebius n₁ : ℝ) *
                ∑ d₁ ∈ n₁.divisors, (ArithmeticFunction.moebius d₁ : ℝ) *
                  Xpg x Pz (c * n₁) (s / d₁) (t / n₁)| :=
            mul_le_mul (hμ1 c) (Finset.abs_sum_le_sum_abs _ _) (abs_nonneg _) (by norm_num)
        _ = ∑ n₁ ∈ (ProdP Pz).divisors,
              |(ArithmeticFunction.moebius n₁ : ℝ) *
                ∑ d₁ ∈ n₁.divisors, (ArithmeticFunction.moebius d₁ : ℝ) *
                  Xpg x Pz (c * n₁) (s / d₁) (t / n₁)| := one_mul _
        _ ≤ ∑ n₁ ∈ (ProdP Pz).divisors,
              ∑ d₁ ∈ n₁.divisors, |Xpg x Pz (c * n₁) (s / d₁) (t / n₁)| := by
            refine Finset.sum_le_sum (fun n₁ _ => ?_)
            rw [abs_mul]
            refine (mul_le_mul_of_nonneg_right (hμ1 n₁) (abs_nonneg _)).trans ?_
            rw [one_mul]
            refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun d₁ _ => ?_))
            rw [abs_mul]
            exact (mul_le_mul_of_nonneg_right (hμ1 d₁) (abs_nonneg _)).trans (le_of_eq (one_mul _))
    have h2 : wc c = ((c.divisors.card : ℝ)) ^ 2 := rfl
    rw [h2]
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  rw [Wall]
  exact Finset.sum_le_sum key

end

end Work.FIChain
