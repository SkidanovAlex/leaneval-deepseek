import Mathlib
import Submission.Work.BMF.zeta_growth_defs
import Submission.Vinogradov.Decoupling
import Submission.Vinogradov.Discretisation

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Shared vocabulary for the Vinogradov--Korobov exponential sum bound (`vk_exp_sum_ford`)

This file collects the definitions and the basic inputs that the proof of
`Work.BMF.zpt.vk_exp_sum_ford` (Ford, *Vinogradov's integral and bounds for the Riemann zeta
function*, Proc. LMS 85 (2002), Theorem 2) is assembled from.

The main input recorded here is the **sharp Vinogradov mean value bound** for the complete
system, obtained from the (sorry-free) BDG/decoupling port `Submission.Vinogradov`:
for all `X ≥ 1`,
`J_{s,k}(X) ≤ C · X^{2s - k(k+1)/2 + ε}` provided `2s ≥ k(k+1)/2`.
-/

namespace Work.BMF.zpt

open Finset
open scoped BigOperators

noncomputable section

/-- The exponential sum of Ford's Theorem 2: `Σ_{N<n≤R} (n+u)^{-it}`, summed over the integers
in `(⌊N⌋, ⌊R⌋]`, with `(n+u)^{-it} = exp(-i t log(n+u))`. -/
def ESb (N R u t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊R⌋₊, (((n : ℝ) + u : ℝ) : ℂ) ^ (-(Complex.I * (t : ℂ)))

/-- `ESb` is definitionally the sum occurring in `Work.BMF.VKExpSum`. -/
lemma ESb_eq (N R u t : ℝ) :
    ESb N R u t =
      ∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊R⌋₊, ((((n : ℝ) + u : ℝ)) : ℂ) ^ (-(Complex.I * (t : ℂ))) := rfl

/-- The sharp Vinogradov mean value bound in the form used by Ford's Lemmas 6.3 and 6.5 and
Corollary 6.4: for every `s, k ≥ 1` and `ε > 0` with `2s ≥ k(k+1)/2` there is `C` with
`J_{s,k}(X) ≤ C X^{2s - k(k+1)/2 + ε}` for **all** `X ≥ 1` (the BDG port gives the bound
uniformly in `X ≥ 1`, not merely eventually). -/
theorem J_bdg_bound (s k : ℕ) (hs : 1 ≤ s) (hk : 1 ≤ k) (ε : ℝ) (hε : 0 < ε)
    (hbig : ((k : ℝ) * ((k : ℝ) + 1)) / 2 ≤ (s : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, 1 ≤ X →
      LeanEval.NumberTheory.VinogradovMeanValue.J s k X ≤
        C * (X : ℝ) ^ (2 * (s : ℝ) - ((k : ℝ) * ((k : ℝ) + 1)) / 2 + ε) := by
  obtain ⟨C, hC, h⟩ := Submission.Vinogradov.bdg_Jsep_core s k hs hk ε hε
  refine ⟨2 * C, by positivity, ?_⟩
  intro X hX
  have hX1 : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have h1 : LeanEval.NumberTheory.VinogradovMeanValue.J s k X
      ≤ (Submission.Vinogradov.Jsep s k X : ℝ) := Submission.Vinogradov.J_le_Jsep s k X
  have h2 := h X hX
  have hexp_le : (s : ℝ) + ε ≤ 2 * (s : ℝ) - ((k : ℝ) * ((k : ℝ) + 1)) / 2 + ε := by
    linarith
  have hfirst : (X : ℝ) ^ ((s : ℝ) + ε)
      ≤ (X : ℝ) ^ (2 * (s : ℝ) - ((k : ℝ) * ((k : ℝ) + 1)) / 2 + ε) :=
    Real.rpow_le_rpow_of_exponent_le hX1 hexp_le
  have hrhs : Submission.Vinogradov.rhs s k ε X
      ≤ 2 * (X : ℝ) ^ (2 * (s : ℝ) - ((k : ℝ) * ((k : ℝ) + 1)) / 2 + ε) := by
    have hdef : Submission.Vinogradov.rhs s k ε X
        = (X : ℝ) ^ ((s : ℝ) + ε)
          + (X : ℝ) ^ ((2 * (s : ℝ)) - ((k : ℝ) * ((k : ℝ) + 1)) / 2 + ε) := rfl
    rw [hdef]
    linarith
  calc LeanEval.NumberTheory.VinogradovMeanValue.J s k X
      ≤ (Submission.Vinogradov.Jsep s k X : ℝ) := h1
    _ ≤ C * Submission.Vinogradov.rhs s k ε X := h2
    _ ≤ C * (2 * (X : ℝ) ^ (2 * (s : ℝ) - ((k : ℝ) * ((k : ℝ) + 1)) / 2 + ε)) :=
          mul_le_mul_of_nonneg_left hrhs hC.le
    _ = 2 * C * (X : ℝ) ^ (2 * (s : ℝ) - ((k : ℝ) * ((k : ℝ) + 1)) / 2 + ε) := by ring

end

end Work.BMF.zpt
