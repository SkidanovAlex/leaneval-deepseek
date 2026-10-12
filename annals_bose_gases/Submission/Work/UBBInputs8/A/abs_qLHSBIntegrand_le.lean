import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.UBBInputs8.A.abs_wSmall1Pair_chiB_le
import Submission.Work.UBBInputs8.A.abs_wSmallPair_chiB_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.UBBInputs8.A

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

/-- Elementary real-algebra core: absolute-value domination of a two-term
expression by the (nonnegative) coefficient bounds. -/
private lemma key_ineq (μ S Φ2 I P Q1 Q2 : ℝ) (hμ : 0 ≤ μ) (hS : 0 ≤ S)
    (hΦ : Φ2 ≤ S) (hΦnn : 0 ≤ Φ2) (hI : |I| ≤ Q1) (hP : |P| ≤ Q2) :
    |Φ2 * (-μ * I + (1/2) * P)| ≤ S * (μ * Q1 + (1/2) * Q2) := by
  have hkey : |-μ * I + (1/2) * P| ≤ μ * Q1 + (1/2) * Q2 := by
    have h1 : |-μ * I| ≤ μ * Q1 := by
      rw [abs_mul, abs_neg, abs_of_nonneg hμ]
      exact mul_le_mul_of_nonneg_left hI hμ
    have h2 : |(1/2) * P| ≤ (1/2) * Q2 := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]
      exact mul_le_mul_of_nonneg_left hP (by norm_num)
    calc |-μ * I + (1/2) * P| ≤ |-μ * I| + |(1/2) * P| := abs_add_le _ _
      _ ≤ μ * Q1 + (1/2) * Q2 := add_le_add h1 h2
  rw [abs_mul, abs_of_nonneg hΦnn]
  exact mul_le_mul hΦ hkey (abs_nonneg _) hS

/-- **Pointwise domination of the localised potential integrand.**

`Work.SmallBoxSliding.qLHSBIntegrand h M L dd μ Φ u x`
`= Φ x ^ 2 * (- μ * (Σᵢ ∫_{acube L} wSmall1Pair h M L dd u (xᵢ) y dy) + ½ * Σ_{p ∈ pairSet N} wSmallPair M L dd u v (x_p.1) (x_p.2))`.

Given the one-body fibre bound `|∫ wSmall1Pair| ≤ KL·T·χ_{B(u)}` (with `KL,T ≥ 0`),
the two-body bound `|wSmallPair| ≤ KP·χ_{B(u)}(·)·χ_{B(u)}(·)` (with `KP ≥ 0`) and the bound
`Φ x ^ 2 ≤ S` on the analysis box (`S ≥ 0`), the integrand is dominated in absolute value by
`S·(μ·KL·T·Σᵢχ_{B(u)}(xᵢ) + ½·KP·Σ_p χ_{B(u)}(x_p1)·χ_{B(u)}(x_p2))`
(using `μ ≥ 0`).  Pure pointwise algebra: `abs_add`, `abs_mul`, `Finset.abs_sum_le_sum_abs`,
`mul_le_mul`, `Finset.mul_sum`. -/
theorem abs_qLHSBIntegrand_le {N : ℕ} {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {M : ℕ} (hM : 1 ≤ M) {L dd μ S KL KP T : ℝ} (hL : 0 < L) (hd : 0 < dd) (hμ : 0 ≤ μ)
    (u : EuclideanSpace ℝ (Fin 3)) (hS : 0 ≤ S) (hKL : 0 ≤ KL) (hKP : 0 ≤ KP) (hT : 0 ≤ T)
    {Φ : Submission.BoseGases.X N → ℝ}
    (hΦ : ∀ x ∈ Submission.BoseGases.abox N L, (Φ x) ^ 2 ≤ S)
    (hfib : ∀ z : EuclideanSpace ℝ (Fin 3),
      |∫ y in Submission.BoseGases.acube L,
        Submission.BoseGases.wSmall1Pair h M L dd u z y|
        ≤ KL * T * Submission.BoseGases.chiSmallB M L dd u z)
    (hpair : ∀ x y : EuclideanSpace ℝ (Fin 3),
      |Submission.BoseGases.wSmallPair M L dd u v x y|
        ≤ KP * Submission.BoseGases.chiSmallB M L dd u x * Submission.BoseGases.chiSmallB M L dd u y) :
    ∀ x ∈ Submission.BoseGases.abox N L,
      |Work.SmallBoxSliding.qLHSBIntegrand h M L dd μ Φ u x|
        ≤ S * (μ * (KL * T * ∑ i : Fin N, Submission.BoseGases.chiSmallB M L dd u (x i))
            + (1 / 2) * (∑ p ∈ Submission.BoseGases.pairSet N,
                KP * Submission.BoseGases.chiSmallB M L dd u (x p.1)
                  * Submission.BoseGases.chiSmallB M L dd u (x p.2))) := by
  intro x hx
  -- one-body sum bound
  have hIfib : |∑ i : Fin N, ∫ y in Submission.BoseGases.acube L,
        Submission.BoseGases.wSmall1Pair h M L dd u (x i) y|
      ≤ KL * T * ∑ i : Fin N, Submission.BoseGases.chiSmallB M L dd u (x i) := by
    refine (Finset.abs_sum_le_sum_abs _ Finset.univ).trans ?_
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => hfib (x i))
  -- two-body sum bound
  have hPpair : |∑ p ∈ Submission.BoseGases.pairSet N,
        Submission.BoseGases.wSmallPair M L dd u v (x p.1) (x p.2)|
      ≤ ∑ p ∈ Submission.BoseGases.pairSet N,
          KP * Submission.BoseGases.chiSmallB M L dd u (x p.1)
            * Submission.BoseGases.chiSmallB M L dd u (x p.2) := by
    refine (Finset.abs_sum_le_sum_abs _ (Submission.BoseGases.pairSet N)).trans ?_
    exact Finset.sum_le_sum (fun p _ => hpair (x p.1) (x p.2))
  rw [Work.SmallBoxSliding.qLHSBIntegrand]
  exact key_ineq μ S ((Φ x) ^ 2)
    (∑ i : Fin N, ∫ y in Submission.BoseGases.acube L,
      Submission.BoseGases.wSmall1Pair h M L dd u (x i) y)
    (∑ p ∈ Submission.BoseGases.pairSet N,
      Submission.BoseGases.wSmallPair M L dd u v (x p.1) (x p.2))
    (KL * T * ∑ i : Fin N, Submission.BoseGases.chiSmallB M L dd u (x i))
    (∑ p ∈ Submission.BoseGases.pairSet N,
      KP * Submission.BoseGases.chiSmallB M L dd u (x p.1)
        * Submission.BoseGases.chiSmallB M L dd u (x p.2))
    hμ hS (hΦ x hx) (sq_nonneg _) hIfib hPpair

end Work.UBBInputs8.A
