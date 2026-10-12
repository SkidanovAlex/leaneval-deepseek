import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.qSideLossB1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1S.boxQsharpSpecB1`

The sharp (`1 + c`) spectral bound for the box-`q`-words: for the box projections
`P_{B,i} = UBBInputs8.boxPInd V A i`, `Q_{B,i} = UBBInputs8.boxQInd V A i`, the completed-square
weight `Θ₊ = √(n₀+1) + √c` (`c = μ|A|` with `|A| = V`) obeys

    Σᵢ ∫_{abox N ℓ} (Θ₊ (Q_{B,i}Φ))² ≤ 2·[ Σ_{i,j} ∫ Q_{B,i}Φ·P_{B,j}Φ + (1 + c)·Σᵢ∫(Q_{B,i}Φ)² ] .

## The argument (per slot `i`, then sum)

Write `w := Q_{B,i}Φ`, `Θ₁ := √(n₀+1)` and `Θ₊ = Θ₁ + √c` pointwise (`n0FunOp_add_const`).

* **Young step.**  `(a + √c·b)² ≤ 2a² + 2c·b²` pointwise, hence on the box
  `∫(Θ₊w)² ≤ 2∫(Θ₁w)² + 2c·∫w²`.
* **`√` quadratic form** (`n0Sqrt_quadform_good`): `∫(Θ₁w)² = ∫w·(n₀w) + ∫w²`.
* **`n₀` quadratic form** (`n0Op_quadform_sum_pInd_sq`): `∫w·(n₀w) = Σⱼ∫(P_{B,j}w)²`.
* **`Q`–`P` pairing** (`boxQIndPInd_pairing_sq`): `∫(P_{B,j}w)² = ∫Q_{B,i}Φ·P_{B,j}Φ`.

So `∫(Θ₁w)² = Σⱼ∫Q_{B,i}Φ·P_{B,j}Φ + ∫w²`, and the per-slot bound
`∫(Θ₊w)² ≤ 2·(Σⱼ∫Q_{B,i}Φ·P_{B,j}Φ + (1+c)∫w²)` follows.  Summing over `i` gives the claim.

Note that the constant is sharp: the cross term is *not* discarded, so the `c`-dependent part of
the loss is exactly `2c·n₊` and the box count enters with `(1 + c)`, not `(2 + c)`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal Real

namespace Work.BoseFixB1S

open Submission.BoseGases

/-- **Per-slot sharp spectral bound.**  The Young split of the weight `√(r+1) + √c` contributes
`2∫(√(n₀+1)w)² + 2c∫w² = 2(Σⱼ∫Q_{B,i}Φ·P_{B,j}Φ + (1+c)∫w²)`. -/
theorem boxQsharpSpecB1_slot {N : ℕ} {ℓ V c : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V) (hc : 0 ≤ c)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hVeq : V = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) (i : Fin N) :
    (∫ x in Submission.BoseGases.abox N ℓ,
        (Work.BoseFixB1S.n0FunOp V A (fun r : ℝ => Real.sqrt (r + 1) + Real.sqrt c)
          (Work.UBBInputs8.boxQInd V A i Φ)) x ^ 2)
      ≤ 2 * ((∑ j : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxQInd V A i Φ x) * (Work.UBBInputs8.boxPInd V A j Φ x))
          + (1 + c) * (∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2)) := by
  have hΦG : GoodState ℓ Φ := goodState_of_continuous hℓ hΦc
  have hwi : GoodState ℓ (Work.UBBInputs8.boxQInd V A i Φ) :=
    goodState_boxQInd hℓ hV hA hVeq hAc i hΦG
  -- GoodState of the two functional-calculus states
  have hΘG : GoodState ℓ (Work.BoseFixB1S.n0FunOp V A
      (fun r : ℝ => Real.sqrt (r + 1) + Real.sqrt c) (Work.UBBInputs8.boxQInd V A i Φ)) :=
    goodState_n0FunOpQSide hℓ hV hA hVeq hAc (fun r : ℝ => Real.sqrt (r + 1) + Real.sqrt c) hwi
  have h1G : GoodState ℓ (Work.BoseFixB1S.n0FunOp V A (fun r : ℝ => Real.sqrt (r + 1))
      (Work.UBBInputs8.boxQInd V A i Φ)) :=
    goodState_n0FunOpQSide hℓ hV hA hVeq hAc (fun r : ℝ => Real.sqrt (r + 1)) hwi
  -- integrability of the three squared states
  have hIntL : IntegrableOn (fun x : Submission.BoseGases.X N =>
      (Work.BoseFixB1S.n0FunOp V A (fun r : ℝ => Real.sqrt (r + 1) + Real.sqrt c)
        (Work.UBBInputs8.boxQInd V A i Φ)) x ^ 2)
      (Submission.BoseGases.abox N ℓ) MeasureTheory.volume :=
    integrableOn_sq_of_bound hℓ hΘG.1 hΘG.2.choose_spec
  have hInt1 : IntegrableOn (fun x : Submission.BoseGases.X N =>
      (Work.BoseFixB1S.n0FunOp V A (fun r : ℝ => Real.sqrt (r + 1))
        (Work.UBBInputs8.boxQInd V A i Φ)) x ^ 2)
      (Submission.BoseGases.abox N ℓ) MeasureTheory.volume :=
    integrableOn_sq_of_bound hℓ h1G.1 h1G.2.choose_spec
  have hIntq : IntegrableOn (fun x : Submission.BoseGases.X N =>
      (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2)
      (Submission.BoseGases.abox N ℓ) MeasureTheory.volume :=
    integrableOn_sq_of_bound hℓ hwi.1 hwi.2.choose_spec
  have hIntR : IntegrableOn (fun x : Submission.BoseGases.X N =>
      2 * (Work.BoseFixB1S.n0FunOp V A (fun r : ℝ => Real.sqrt (r + 1))
          (Work.UBBInputs8.boxQInd V A i Φ)) x ^ 2
        + 2 * c * (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2)
      (Submission.BoseGases.abox N ℓ) MeasureTheory.volume :=
    (hInt1.const_mul 2).add (hIntq.const_mul (2 * c))
  -- the pointwise Young step
  have hpt : ∀ x : Submission.BoseGases.X N,
      (Work.BoseFixB1S.n0FunOp V A (fun r : ℝ => Real.sqrt (r + 1) + Real.sqrt c)
        (Work.UBBInputs8.boxQInd V A i Φ)) x ^ 2
        ≤ 2 * (Work.BoseFixB1S.n0FunOp V A (fun r : ℝ => Real.sqrt (r + 1))
            (Work.UBBInputs8.boxQInd V A i Φ)) x ^ 2
          + 2 * c * (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2 := by
    intro x
    have hsplit : (Work.BoseFixB1S.n0FunOp V A (fun r : ℝ => Real.sqrt (r + 1) + Real.sqrt c)
          (Work.UBBInputs8.boxQInd V A i Φ)) x
        = (Work.BoseFixB1S.n0FunOp V A (fun r : ℝ => Real.sqrt (r + 1))
            (Work.UBBInputs8.boxQInd V A i Φ)) x
          + Real.sqrt c * (Work.UBBInputs8.boxQInd V A i Φ x) :=
      congrFun (n0FunOp_add_const V A (fun r : ℝ => Real.sqrt (r + 1)) (Real.sqrt c)
        (Work.UBBInputs8.boxQInd V A i Φ)) x
    rw [hsplit]
    nlinarith [sq_nonneg ((Work.BoseFixB1S.n0FunOp V A (fun r : ℝ => Real.sqrt (r + 1))
          (Work.UBBInputs8.boxQInd V A i Φ)) x
        - Real.sqrt c * (Work.UBBInputs8.boxQInd V A i Φ x)),
      Real.sq_sqrt hc]
  -- the integral form of the Young step
  have hstep : (∫ x in Submission.BoseGases.abox N ℓ,
        (Work.BoseFixB1S.n0FunOp V A (fun r : ℝ => Real.sqrt (r + 1) + Real.sqrt c)
          (Work.UBBInputs8.boxQInd V A i Φ)) x ^ 2)
      ≤ ∫ x in Submission.BoseGases.abox N ℓ,
          (2 * (Work.BoseFixB1S.n0FunOp V A (fun r : ℝ => Real.sqrt (r + 1))
              (Work.UBBInputs8.boxQInd V A i Φ)) x ^ 2
            + 2 * c * (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2) :=
    MeasureTheory.integral_mono
      (μ := MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)) hIntL hIntR hpt
  have heq : (∫ x in Submission.BoseGases.abox N ℓ,
          (2 * (Work.BoseFixB1S.n0FunOp V A (fun r : ℝ => Real.sqrt (r + 1))
              (Work.UBBInputs8.boxQInd V A i Φ)) x ^ 2
            + 2 * c * (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2))
      = 2 * (∫ x in Submission.BoseGases.abox N ℓ,
            (Work.BoseFixB1S.n0FunOp V A (fun r : ℝ => Real.sqrt (r + 1))
              (Work.UBBInputs8.boxQInd V A i Φ)) x ^ 2)
        + 2 * c * (∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2) := by
    rw [MeasureTheory.integral_add (hInt1.const_mul 2) (hIntq.const_mul (2 * c)),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  -- the two quadratic-form identities and the `Q`–`P` pairing
  have hQ := n0Sqrt_quadform_good hℓ hV hA hVeq hAc hwi
  have hN := n0Op_quadform_sum_pInd_sq hℓ hV hA hVeq hAc hwi.1 hwi.2.choose_spec
  have hPair : (∑ j : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxPInd V A j (Work.UBBInputs8.boxQInd V A i Φ) x) ^ 2)
      = ∑ j : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
          (Work.UBBInputs8.boxQInd V A i Φ x) * (Work.UBBInputs8.boxPInd V A j Φ x) :=
    Finset.sum_congr rfl (fun j _ => boxQIndPInd_pairing_sq hℓ hV hA hVeq hAc hΦG i j)
  calc (∫ x in Submission.BoseGases.abox N ℓ,
        (Work.BoseFixB1S.n0FunOp V A (fun r : ℝ => Real.sqrt (r + 1) + Real.sqrt c)
          (Work.UBBInputs8.boxQInd V A i Φ)) x ^ 2)
      ≤ ∫ x in Submission.BoseGases.abox N ℓ,
          (2 * (Work.BoseFixB1S.n0FunOp V A (fun r : ℝ => Real.sqrt (r + 1))
              (Work.UBBInputs8.boxQInd V A i Φ)) x ^ 2
            + 2 * c * (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2) := hstep
    _ = 2 * (∫ x in Submission.BoseGases.abox N ℓ,
            (Work.BoseFixB1S.n0FunOp V A (fun r : ℝ => Real.sqrt (r + 1))
              (Work.UBBInputs8.boxQInd V A i Φ)) x ^ 2)
        + 2 * c * (∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2) := heq
    _ = 2 * ((∑ j : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
              (Work.UBBInputs8.boxQInd V A i Φ x) * (Work.UBBInputs8.boxPInd V A j Φ x))
            + (∫ x in Submission.BoseGases.abox N ℓ,
                (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2))
        + 2 * c * (∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2) := by
        rw [hQ, hN, hPair]
    _ = 2 * ((∑ j : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
              (Work.UBBInputs8.boxQInd V A i Φ x) * (Work.UBBInputs8.boxPInd V A j Φ x))
            + (1 + c) * (∫ x in Submission.BoseGases.abox N ℓ,
                (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2)) := by
        ring

theorem boxQsharpSpecB1 {N : ℕ} {ℓ V c : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V) (hc : 0 ≤ c)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hVeq : V = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) :
    (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
        (Work.BoseFixB1S.n0FunOp V A
          (fun r : ℝ => Real.sqrt (r + 1) + Real.sqrt c)
          (Work.UBBInputs8.boxQInd V A i Φ)) x ^ 2)
      ≤ 2 * ((∑ i : Fin N, ∑ j : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxQInd V A i Φ x) * (Work.UBBInputs8.boxPInd V A j Φ x))
          + (1 + c) * Work.BoseFixB1S.boxQCount V ℓ A Φ) := by
  have hsum : (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
        (Work.BoseFixB1S.n0FunOp V A (fun r : ℝ => Real.sqrt (r + 1) + Real.sqrt c)
          (Work.UBBInputs8.boxQInd V A i Φ)) x ^ 2)
      ≤ ∑ i : Fin N, 2 * ((∑ j : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxQInd V A i Φ x) * (Work.UBBInputs8.boxPInd V A j Φ x))
          + (1 + c) * (∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2)) :=
    Finset.sum_le_sum (fun i _ => boxQsharpSpecB1_slot hℓ hV hc hA hVeq hAc hΦc i)
  refine le_trans hsum ?_
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hbq : (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2) = Work.BoseFixB1S.boxQCount V ℓ A Φ := rfl
  rw [hbq]

end Work.BoseFixB1S
