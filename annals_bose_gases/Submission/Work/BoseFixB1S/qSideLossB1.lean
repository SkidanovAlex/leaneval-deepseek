import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.flatPiece_eigen
import Submission.Work.BoseFixB1S.boxQIndPInd_pairing_sq
import Submission.Work.BoseFixB1S.n0FunOp_add_const
import Submission.Work.BoseFixB1S.n0Op_quadform_sum_pInd_sq
import Submission.Work.BoseFixB1S.n0Sqrt_quadform_good
import Submission.Work.BoseFixB1S.weightedQfNonnegB2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1S.qSideLossB1` — the `q`-side loss bound of the FS completion of squares

For the FS box projections `P_{B,i} = UBBInputs8.boxPInd volA A i` and their mean-free complements
`Q_{B,i} = UBBInputs8.boxQInd volA A i` (`Q_{B,i} = 1_A(x_i) − P_{B,i}`), a fibre `fib` with
`0 ≤ fib ≤ Fmax`, and the `n₀`-functional calculus `n0FunOp volA A (· ↦ √(·+1) + √(μ|A|))`, the
`q`-side loss of FS's sharp completion of squares obeys

    Σᵢ ∫_{abox} (Θ₊ (fib(xᵢ)·Q_{B,i}Φ))²
      ≤ 2 Fmax² · [ Σ_{i,j} ∫ Q_{B,i}Φ · P_{B,j}Φ + (2 + μ|A|)·boxQCount ] ,

with `Θ₊ = √(n₀+1) + √(μ|A|)` the completed-square weight of `final_v2.tex` l. 3732–3743.

## The chain (all constants come out sharp, no `μ|A|`-regime split)

Write `ψᵢ := fib(xᵢ)·Q_{B,i}Φ`, `m := μ|A|`, `Θ₊ = Θ₁ + √m` with `Θ₁ = √(n₀+1)`, and
`X := Σ_{i,j} ∫ Q_{B,i}Φ·P_{B,j}Φ`, `nq := boxQCount = Σᵢ ∫ (Q_{B,i}Φ)²`.

1. **Linear split** (`n0FunOp_add_const`): `Θ₊ψᵢ = Θ₁ψᵢ + √m·ψᵢ` pointwise, so
   `(Θ₊ψᵢ)² ≤ 2(Θ₁ψᵢ)² + 2m·ψᵢ²` (the pointwise `(a+b)² ≤ 2a²+2b²`).
2. **`√` quadratic form** (`n0Sqrt_quadform_good`): `∫(Θ₁ψᵢ)² = ∫ψᵢ·(n₀ψᵢ) + ∫ψᵢ²`.
3. **`n₀` quadratic form** (`n0Op_quadform_sum_pInd_sq`): `∫ψᵢ(n₀ψᵢ) = Σ_j ∫(P_{B,j}ψᵢ)²`.
4. **Per-slot bounds.**  For `j ≠ i` the box projection `P_{B,j}` commutes with multiplication by
   the slot-`i` function `fib(xᵢ)` (`boxPInd_smulF`), so `P_{B,j}ψᵢ = fib(xᵢ)·P_{B,j}Q_{B,i}Φ` and
   `∫(P_{B,j}ψᵢ)² ≤ Fmax² ∫(P_{B,j}Q_{B,i}Φ)²`; for `j = i` the contraction
   `boxPInd_sq_le_self` gives `∫(P_{B,i}ψᵢ)² ≤ ∫ψᵢ² ≤ Fmax²∫(Q_{B,i}Φ)²`.
5. **The `Q`–`P` pairing** (`boxQIndPInd_pairing_sq`): `∫(P_{B,j}Q_{B,i}Φ)² = ∫Q_{B,i}Φ·P_{B,j}Φ`
   for all `i,j` (so the `j = i` terms vanish: `P_{B,i}Q_{B,i} = 0`).
6. **The fibre bound** (`integral_sq_mul_coord_le`): `∫(fib(xᵢ)·g)² ≤ Fmax²∫g²` whenever
   `0 ≤ fib ≤ Fmax` and `g` is measurable and bounded on the box.

Adding up:  `Σᵢ‖Θ₊ψᵢ‖² ≤ 2[Fmax²(X+nq) + Fmax²nq] + 2m·Fmax²·nq = 2Fmax²[X + (2+m)nq]`.

Note that the box-support hypothesis `hsupp` of the target statement is *not* needed: the estimate
holds for every continuous `Φ`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal Real

namespace Work.BoseFixB1S

open Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

/-! ## Own helpers -/

/-- `n0FunOp volA A g` preserves `GoodState` (it is a finite sum of scaled subset idempotents). -/
theorem goodState_n0FunOpQSide {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = (volume : Measure E3).real A)
    (hAc : A ⊆ acube ℓ) (g : ℝ → ℝ) {Ψ : X N → ℝ} (hΨ : GoodState ℓ Ψ) :
    GoodState ℓ (n0FunOp volA A g Ψ) := by
  rw [n0FunOp_eq_sum_card volA A g Ψ]
  have hS : ∀ S : Finset (Fin N), GoodState ℓ (n0ProjOp volA A S Ψ) :=
    fun S => n0ProjOp_goodStateB1 hℓ hvol hA hvolA hAc hΨ S
  constructor
  · exact Finset.measurable_sum _ (fun S _ => (hS S).1.const_mul _)
  · refine ⟨∑ S : Finset (Fin N), |g (S.card : ℝ)| * (hS S).2.choose, fun x hx => ?_⟩
    calc |∑ S : Finset (Fin N), g (S.card : ℝ) * n0ProjOp volA A S Ψ x|
        ≤ ∑ S : Finset (Fin N), |g (S.card : ℝ) * n0ProjOp volA A S Ψ x| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ S : Finset (Fin N), |g (S.card : ℝ)| * |n0ProjOp volA A S Ψ x| := by
          simp only [abs_mul]
      _ ≤ ∑ S : Finset (Fin N), |g (S.card : ℝ)| * (hS S).2.choose :=
          Finset.sum_le_sum (fun S _ =>
            mul_le_mul_of_nonneg_left ((hS S).2.choose_spec x hx) (abs_nonneg _))

/-- **Fibre-weighted square bound**: `0 ≤ fib ≤ Fmax` transfers to the box integral of squares. -/
theorem integral_sq_mul_coord_le {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {fib : E3 → ℝ} (hfibm : Measurable fib) {Fmax : ℝ}
    (hfib0 : ∀ z, 0 ≤ fib z) (hfible : ∀ z, fib z ≤ Fmax) (i : Fin N)
    {gd : X N → ℝ} (hgm : Measurable gd) {Cg : ℝ}
    (hgb : ∀ x ∈ abox N ℓ, |gd x| ≤ Cg) :
    (∫ x in abox N ℓ, (fib (x i) * gd x) ^ 2) ≤ Fmax ^ 2 * ∫ x in abox N ℓ, (gd x) ^ 2 := by
  have hF0 : 0 ≤ Fmax := le_trans (hfib0 0) (hfible 0)
  have hfm : Measurable (fun x : X N => fib (x i)) :=
    hfibm.comp (continuous_apply i).measurable
  have hint1 : IntegrableOn (fun x : X N => (fib (x i) * gd x) ^ 2) (abox N ℓ) volume :=
    integrableOn_sq_of_bound hℓ (hfm.mul hgm) (fun x hx => by
      rw [abs_mul]
      calc |fib (x i)| * |gd x| ≤ Fmax * |Cg| :=
            mul_le_mul (by rw [abs_of_nonneg (hfib0 (x i))]; exact hfible (x i))
              (le_trans (hgb x hx) (le_abs_self Cg)) (abs_nonneg _) hF0
        _ = Fmax * |Cg| := rfl)
  have hint2 : IntegrableOn (fun x : X N => Fmax ^ 2 * (gd x) ^ 2) (abox N ℓ) volume :=
    (integrableOn_sq_of_bound hℓ hgm hgb).const_mul _
  rw [← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_mono (μ := volume.restrict (abox N ℓ)) hint1 hint2 (fun x => ?_)
  have h1 : fib (x i) ^ 2 ≤ Fmax ^ 2 := by
    rw [sq_le_sq, abs_of_nonneg (hfib0 (x i)), abs_of_nonneg hF0]
    exact hfible (x i)
  calc (fib (x i) * gd x) ^ 2 = fib (x i) ^ 2 * (gd x) ^ 2 := by ring
    _ ≤ Fmax ^ 2 * (gd x) ^ 2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg _)

/-- **The box projection is an `L²` contraction** (local replacement of the delegated
`boxPInd_sq_le_self`): `Pᵢ` is self-adjoint and idempotent, so `s := ∫(PᵢΨ)² = ∫Ψ·(PᵢΨ)`, and the
pointwise `2ab ≤ a² + b²` gives `s ≤ (s + t)/2` with `t := ∫Ψ²`. -/
theorem boxPInd_sq_le_selfB1 {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = (volume : Measure E3).real A)
    (hAc : A ⊆ acube ℓ) (i : Fin N)
    {Ψ : X N → ℝ} (hΨm : Measurable Ψ) {C : ℝ}
    (hΨb : ∀ x ∈ abox N ℓ, |Ψ x| ≤ C) :
    (∫ x in abox N ℓ, (Work.UBBInputs8.boxPInd volA A i Ψ x) ^ 2)
      ≤ ∫ x in abox N ℓ, (Ψ x) ^ 2 := by
  have hPm : Measurable (Work.UBBInputs8.boxPInd volA A i Ψ) :=
    measurable_boxPInd volA A hA i hΨm
  have hPb : ∀ x ∈ abox N ℓ, |Work.UBBInputs8.boxPInd volA A i Ψ x| ≤ C :=
    abs_boxPInd_le hℓ hvol hA hvolA hAc i hΨb
  have hP2 : IntegrableOn (fun x : X N => (Work.UBBInputs8.boxPInd volA A i Ψ x) ^ 2)
      (abox N ℓ) volume := integrableOn_sq_of_bound hℓ hPm hPb
  have hΨ2 : IntegrableOn (fun x : X N => (Ψ x) ^ 2) (abox N ℓ) volume :=
    integrableOn_sq_of_bound hℓ hΨm hΨb
  have hself : (∫ x in abox N ℓ, (Work.UBBInputs8.boxPInd volA A i Ψ x) ^ 2)
      = ∫ x in abox N ℓ, Ψ x * Work.UBBInputs8.boxPInd volA A i Ψ x :=
    n0Sum_pInd_sq_selfMul hℓ hvol hA hvolA hAc i hΨm hΨb
  have hpt : ∀ x : X N, Ψ x * Work.UBBInputs8.boxPInd volA A i Ψ x
      ≤ (1 / 2) * (Ψ x) ^ 2 + (1 / 2) * (Work.UBBInputs8.boxPInd volA A i Ψ x) ^ 2 := by
    intro x
    nlinarith [sq_nonneg (Ψ x - Work.UBBInputs8.boxPInd volA A i Ψ x)]
  have hint : IntegrableOn (fun x : X N =>
      (1 / 2) * (Ψ x) ^ 2 + (1 / 2) * (Work.UBBInputs8.boxPInd volA A i Ψ x) ^ 2)
      (abox N ℓ) volume := (hΨ2.const_mul _).add (hP2.const_mul _)
  have h1 : (∫ x in abox N ℓ, Ψ x * Work.UBBInputs8.boxPInd volA A i Ψ x)
      ≤ ∫ x in abox N ℓ,
          ((1 / 2) * (Ψ x) ^ 2 + (1 / 2) * (Work.UBBInputs8.boxPInd volA A i Ψ x) ^ 2) :=
    MeasureTheory.integral_mono (μ := volume.restrict (abox N ℓ))
      (integrableOn_mul_of_bound hℓ hΨm hPm hΨb hPb) hint hpt
  have h2 : (∫ x in abox N ℓ,
        ((1 / 2) * (Ψ x) ^ 2 + (1 / 2) * (Work.UBBInputs8.boxPInd volA A i Ψ x) ^ 2))
      = (1 / 2) * (∫ x in abox N ℓ, (Ψ x) ^ 2)
        + (1 / 2) * (∫ x in abox N ℓ, (Work.UBBInputs8.boxPInd volA A i Ψ x) ^ 2) := by
    rw [MeasureTheory.integral_add (hΨ2.const_mul _) (hP2.const_mul _),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  rw [hself]
  linarith [h1, h2]

/-! ## The `q`-side loss bound -/

/-- The slot-`i` state whose `n₀`-loss the `q`-side estimate controls:
`fib(x_i) · (Q_{B,i}Φ)`. -/
def lossFib {N : ℕ} (volA : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (fib : EuclideanSpace ℝ (Fin 3) → ℝ) (Φ : Submission.BoseGases.X N → ℝ) (i : Fin N) :
    Submission.BoseGases.X N → ℝ :=
  fun y => fib (y i) * Work.UBBInputs8.boxQInd volA A i Φ y

/-- `(√(n₀+1) + √(μ|A|))` applied to the slot-`i` `q`-state. -/
def qLossOp {N : ℕ} (volA μ : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (Φ : Submission.BoseGases.X N → ℝ) (fib : EuclideanSpace ℝ (Fin 3) → ℝ) (i : Fin N) :
    Submission.BoseGases.X N → ℝ :=
  Work.BoseFixB1S.n0FunOp volA A (fun r : ℝ => Real.sqrt (r + 1) + Real.sqrt (μ * volA))
    (lossFib volA A fib Φ i)

/-- `√(n₀+1)` applied to the slot-`i` `q`-state. -/
def qLossOp1 {N : ℕ} (volA : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (Φ : Submission.BoseGases.X N → ℝ) (fib : EuclideanSpace ℝ (Fin 3) → ℝ) (i : Fin N) :
    Submission.BoseGases.X N → ℝ :=
  Work.BoseFixB1S.n0FunOp volA A (fun r : ℝ => Real.sqrt (r + 1)) (lossFib volA A fib Φ i)

theorem qSideLossB1_aux {N : ℕ} {ℓ volA μ : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA) (hμ : 0 ≤ μ)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
    {fib : EuclideanSpace ℝ (Fin 3) → ℝ} (hfibm : Measurable fib)
    (hfib0 : ∀ z, 0 ≤ fib z) {Fmax : ℝ} (hfible : ∀ z, fib z ≤ Fmax) :
    (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ, (qLossOp volA μ A Φ fib i) x ^ 2)
      ≤ 2 * Fmax ^ 2
          * ((∑ i : Fin N, ∑ j : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
                (Work.UBBInputs8.boxQInd volA A i Φ x)
                  * (Work.UBBInputs8.boxPInd volA A j Φ x))
              + (2 + μ * volA) * (Work.BoseFixB1S.boxQCount volA ℓ A Φ)) := by
  classical
  have hFmax0 : 0 ≤ Fmax := le_trans (hfib0 0) (hfible 0)
  have hμv0 : 0 ≤ μ * volA := mul_nonneg hμ hvol.le
  obtain ⟨C0, hC00, hC0b⟩ := exists_abox_bound hℓ hΦc
  have hΦG : GoodState ℓ Φ := ⟨hΦc.measurable, C0, hC0b⟩
  have hQG : ∀ i : Fin N, GoodState ℓ (Work.UBBInputs8.boxQInd volA A i Φ) :=
    fun i => goodState_boxQInd hℓ hvol hA hvolA hAc i hΦG
  have hψG : ∀ i : Fin N, GoodState ℓ (lossFib volA A fib Φ i) := by
    intro i
    refine ⟨(hfibm.comp (continuous_apply i).measurable).mul (hQG i).1,
      Fmax * |(hQG i).2.choose|, ?_⟩
    intro x hx
    rw [lossFib, abs_mul]
    exact mul_le_mul (by rw [abs_of_nonneg (hfib0 (x i))]; exact hfible (x i))
      (le_trans ((hQG i).2.choose_spec x hx) (le_abs_self _)) (abs_nonneg _) hFmax0
  have hO1G : ∀ i : Fin N, GoodState ℓ (qLossOp1 volA A Φ fib i) :=
    fun i => goodState_n0FunOpQSide hℓ hvol hA hvolA hAc (fun r : ℝ => Real.sqrt (r + 1)) (hψG i)
  have hstep1 : ∀ i : Fin N,
      qLossOp volA μ A Φ fib i
        = fun x => qLossOp1 volA A Φ fib i x
            + Real.sqrt (μ * volA) * lossFib volA A fib Φ i x :=
    fun i => n0FunOp_add_const volA A (fun r : ℝ => Real.sqrt (r + 1)) (Real.sqrt (μ * volA))
      (lossFib volA A fib Φ i)
  -- (f1) the two-square split
  have hf1 : (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ, (qLossOp volA μ A Φ fib i) x ^ 2)
      ≤ ∑ i : Fin N, (2 * (∫ x in Submission.BoseGases.abox N ℓ, (qLossOp1 volA A Φ fib i) x ^ 2)
          + 2 * (μ * volA)
            * (∫ x in Submission.BoseGases.abox N ℓ, (lossFib volA A fib Φ i x) ^ 2)) := by
    refine Finset.sum_le_sum (fun i _ => ?_)
    have hI1 : IntegrableOn (fun x : X N => (qLossOp1 volA A Φ fib i x) ^ 2)
        (Submission.BoseGases.abox N ℓ) volume :=
      integrableOn_sq_of_bound hℓ (hO1G i).1 (hO1G i).2.choose_spec
    have hI2 : IntegrableOn (fun x : X N => (lossFib volA A fib Φ i x) ^ 2)
        (Submission.BoseGases.abox N ℓ) volume :=
      integrableOn_sq_of_bound hℓ (hψG i).1 (hψG i).2.choose_spec
    have hI3 : IntegrableOn (fun x : X N => 2 * (qLossOp1 volA A Φ fib i x) ^ 2
        + (2 * (μ * volA)) * ((lossFib volA A fib Φ i x) ^ 2))
        (Submission.BoseGases.abox N ℓ) volume :=
      (hI1.const_mul 2).add (hI2.const_mul (2 * (μ * volA)))
    calc (∫ x in Submission.BoseGases.abox N ℓ, (qLossOp volA μ A Φ fib i) x ^ 2)
        ≤ ∫ x in Submission.BoseGases.abox N ℓ,
            (2 * (qLossOp1 volA A Φ fib i x) ^ 2
              + (2 * (μ * volA)) * ((lossFib volA A fib Φ i x) ^ 2)) := by
          rw [hstep1 i]
          refine MeasureTheory.integral_mono_of_nonneg
            (Filter.Eventually.of_forall (fun x => sq_nonneg _)) hI3 ?_
          filter_upwards with x
          nlinarith [sq_nonneg (qLossOp1 volA A Φ fib i x
              - Real.sqrt (μ * volA) * lossFib volA A fib Φ i x), Real.sq_sqrt hμv0]
      _ = 2 * (∫ x in Submission.BoseGases.abox N ℓ, (qLossOp1 volA A Φ fib i x) ^ 2)
            + 2 * (μ * volA)
              * (∫ x in Submission.BoseGases.abox N ℓ, (lossFib volA A fib Φ i x) ^ 2) := by
          rw [MeasureTheory.integral_add (hI1.const_mul 2) (hI2.const_mul (2 * (μ * volA))),
            MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  -- (f2) the `√`-quadratic form
  have hS1 : (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ, (qLossOp1 volA A Φ fib i) x ^ 2)
      = (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
            (lossFib volA A fib Φ i x) * (n0Op volA A (lossFib volA A fib Φ i) x))
        + (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ, (lossFib volA A fib Φ i x) ^ 2) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => n0Sqrt_quadform_good hℓ hvol hA hvolA hAc (hψG i))
  -- (f3) the per-slot bound
  have hslot : ∀ i : Fin N,
      (∑ j : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
          (Work.UBBInputs8.boxPInd volA A j (lossFib volA A fib Φ i) x) ^ 2)
        ≤ Fmax ^ 2 * ((∫ x in Submission.BoseGases.abox N ℓ,
              (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2)
            + ∑ j ∈ Finset.univ.erase i, ∫ x in Submission.BoseGases.abox N ℓ,
                (Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x) ^ 2) := by
    intro i
    have hdiag : (∫ x in Submission.BoseGases.abox N ℓ,
          (Work.UBBInputs8.boxPInd volA A i (lossFib volA A fib Φ i) x) ^ 2)
        ≤ Fmax ^ 2 * ∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2 :=
      le_trans (boxPInd_sq_le_selfB1 hℓ hvol hA hvolA hAc i (hψG i).1 (hψG i).2.choose_spec)
        (integral_sq_mul_coord_le hℓ hfibm hfib0 hfible i (hQG i).1 (hQG i).2.choose_spec)
    have hrest : (∑ j ∈ Finset.univ.erase i, ∫ x in Submission.BoseGases.abox N ℓ,
          (Work.UBBInputs8.boxPInd volA A j (lossFib volA A fib Φ i) x) ^ 2)
        ≤ Fmax ^ 2 * ∑ j ∈ Finset.univ.erase i, ∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x) ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum (fun j hj => ?_)
      have hij : i ≠ j := ((Finset.mem_erase.mp hj).1).symm
      have hcomm : ∀ x : X N,
          Work.UBBInputs8.boxPInd volA A j (lossFib volA A fib Φ i) x
            = fib (x i) * Work.UBBInputs8.boxPInd volA A j
                (Work.UBBInputs8.boxQInd volA A i Φ) x :=
        fun x => boxPInd_smulF volA A hij x
      rw [show (∫ x in Submission.BoseGases.abox N ℓ,
              (Work.UBBInputs8.boxPInd volA A j (lossFib volA A fib Φ i) x) ^ 2)
            = ∫ x in Submission.BoseGases.abox N ℓ,
                (fib (x i) * Work.UBBInputs8.boxPInd volA A j
                  (Work.UBBInputs8.boxQInd volA A i Φ) x) ^ 2 from
          MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => by
            show (Work.UBBInputs8.boxPInd volA A j (lossFib volA A fib Φ i) x) ^ 2
                = (fib (x i) * Work.UBBInputs8.boxPInd volA A j
                    (Work.UBBInputs8.boxQInd volA A i Φ) x) ^ 2
            rw [hcomm x]))]
      exact integral_sq_mul_coord_le hℓ hfibm hfib0 hfible i
        (measurable_boxPInd volA A hA j (hQG i).1)
        (fun x hx => abs_boxPInd_le hℓ hvol hA hvolA hAc j (hQG i).2.choose_spec x hx)
    rw [mul_add, ← Finset.sum_erase_add (Finset.univ : Finset (Fin N))
      (fun j => ∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxPInd volA A j (lossFib volA A fib Φ i) x) ^ 2) (Finset.mem_univ i)]
    linarith [hrest, hdiag]
  -- (f4) the `n₀` quadratic form
  have hS3 : (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
        (lossFib volA A fib Φ i x) * (n0Op volA A (lossFib volA A fib Φ i) x))
      ≤ Fmax ^ 2 * (Work.BoseFixB1S.boxQCount volA ℓ A Φ
          + ∑ i : Fin N, ∑ j ∈ Finset.univ.erase i,
              ∫ x in Submission.BoseGases.abox N ℓ,
                (Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x) ^ 2) := by
    have hbq : Work.BoseFixB1S.boxQCount volA ℓ A Φ
        = ∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2 := rfl
    have h1 : (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
          (lossFib volA A fib Φ i x) * (n0Op volA A (lossFib volA A fib Φ i) x))
        = ∑ i : Fin N, ∑ j : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxPInd volA A j (lossFib volA A fib Φ i) x) ^ 2 :=
      Finset.sum_congr rfl (fun i _ =>
        n0Op_quadform_sum_pInd_sq hℓ hvol hA hvolA hAc (hψG i).1 (hψG i).2.choose_spec)
    rw [h1]
    refine le_trans (Finset.sum_le_sum (fun i _ => hslot i)) ?_
    rw [hbq, ← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg Fmax)
    rw [Finset.sum_add_distrib]
  -- (f5) the `fib` bound
  have hS2 : (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ, (lossFib volA A fib Φ i x) ^ 2)
      ≤ Fmax ^ 2 * Work.BoseFixB1S.boxQCount volA ℓ A Φ := by
    have hbq : Work.BoseFixB1S.boxQCount volA ℓ A Φ
        = ∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2 := rfl
    rw [hbq, Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ =>
      integral_sq_mul_coord_le hℓ hfibm hfib0 hfible i (hQG i).1 (hQG i).2.choose_spec)
  -- (f6) the pairing identity
  have hY : (∑ i : Fin N, ∑ j ∈ Finset.univ.erase i,
        ∫ x in Submission.BoseGases.abox N ℓ,
          (Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x) ^ 2)
      = (∑ i : Fin N, ∑ j : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
          (Work.UBBInputs8.boxQInd volA A i Φ x) * (Work.UBBInputs8.boxPInd volA A j Φ x)) := by
    have hdiag : ∀ i : Fin N, (∫ x in Submission.BoseGases.abox N ℓ,
          (Work.UBBInputs8.boxQInd volA A i Φ x) * (Work.UBBInputs8.boxPInd volA A i Φ x)) = 0 := by
      intro i
      rw [← boxQIndPInd_pairing_sq hℓ hvol hA hvolA hAc hΦG i i]
      rw [show (∫ x in Submission.BoseGases.abox N ℓ,
              (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A i Φ) x) ^ 2)
            = ∫ x in Submission.BoseGases.abox N ℓ, (0 : ℝ) from
          MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => by
            show (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A i Φ) x) ^ 2
                = (0 : ℝ)
            rw [BoseFixB1.boxPInd_boxQInd_apply_zero hvol hA hvolA i Φ x]; ring))]
      simp
    have hY1 : (∑ i : Fin N, ∑ j ∈ Finset.univ.erase i,
          ∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x) ^ 2)
        = ∑ i : Fin N, ∑ j ∈ Finset.univ.erase i,
            ∫ x in Submission.BoseGases.abox N ℓ,
              (Work.UBBInputs8.boxQInd volA A i Φ x) * (Work.UBBInputs8.boxPInd volA A j Φ x) :=
      Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ =>
        boxQIndPInd_pairing_sq hℓ hvol hA hvolA hAc hΦG i j))
    have hX1 : (∑ i : Fin N, ∑ j : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
          (Work.UBBInputs8.boxQInd volA A i Φ x) * (Work.UBBInputs8.boxPInd volA A j Φ x))
        = ∑ i : Fin N, ((∑ j ∈ Finset.univ.erase i,
              ∫ x in Submission.BoseGases.abox N ℓ,
                (Work.UBBInputs8.boxQInd volA A i Φ x) * (Work.UBBInputs8.boxPInd volA A j Φ x))
            + ∫ x in Submission.BoseGases.abox N ℓ,
                (Work.UBBInputs8.boxQInd volA A i Φ x) * (Work.UBBInputs8.boxPInd volA A i Φ x)) :=
      Finset.sum_congr rfl (fun i _ =>
        (Finset.sum_erase_add (Finset.univ : Finset (Fin N))
          (fun j => ∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxQInd volA A i Φ x) * (Work.UBBInputs8.boxPInd volA A j Φ x))
          (Finset.mem_univ i)).symm)
    have hX2 : (∑ i : Fin N, ((∑ j ∈ Finset.univ.erase i,
            ∫ x in Submission.BoseGases.abox N ℓ,
              (Work.UBBInputs8.boxQInd volA A i Φ x) * (Work.UBBInputs8.boxPInd volA A j Φ x))
          + ∫ x in Submission.BoseGases.abox N ℓ,
              (Work.UBBInputs8.boxQInd volA A i Φ x) * (Work.UBBInputs8.boxPInd volA A i Φ x)))
        = ∑ i : Fin N, ∑ j ∈ Finset.univ.erase i,
            ∫ x in Submission.BoseGases.abox N ℓ,
              (Work.UBBInputs8.boxQInd volA A i Φ x) * (Work.UBBInputs8.boxPInd volA A j Φ x) :=
      Finset.sum_congr rfl (fun i _ => by rw [hdiag i, add_zero])
    rw [hY1, hX1, hX2]
  -- ## the final assembly
  calc (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ, (qLossOp volA μ A Φ fib i) x ^ 2)
      ≤ ∑ i : Fin N, (2 * (∫ x in Submission.BoseGases.abox N ℓ, (qLossOp1 volA A Φ fib i) x ^ 2)
          + 2 * (μ * volA)
            * (∫ x in Submission.BoseGases.abox N ℓ, (lossFib volA A fib Φ i x) ^ 2)) := hf1
    _ = 2 * (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ, (qLossOp1 volA A Φ fib i) x ^ 2)
          + 2 * (μ * volA)
            * (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
                (lossFib volA A fib Φ i x) ^ 2) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ = 2 * ((∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
              (lossFib volA A fib Φ i x) * (n0Op volA A (lossFib volA A fib Φ i) x))
            + (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
                (lossFib volA A fib Φ i x) ^ 2))
          + 2 * (μ * volA)
            * (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
                (lossFib volA A fib Φ i x) ^ 2) := by
          rw [hS1]
    _ ≤ 2 * (Fmax ^ 2 * (Work.BoseFixB1S.boxQCount volA ℓ A Φ
            + ∑ i : Fin N, ∑ j ∈ Finset.univ.erase i,
                ∫ x in Submission.BoseGases.abox N ℓ,
                  (Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x) ^ 2)
          + Fmax ^ 2 * Work.BoseFixB1S.boxQCount volA ℓ A Φ)
          + 2 * (μ * volA) * (Fmax ^ 2 * Work.BoseFixB1S.boxQCount volA ℓ A Φ) := by
          have hb1 : 2 * ((∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
                (lossFib volA A fib Φ i x) * (n0Op volA A (lossFib volA A fib Φ i) x))
              + (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
                  (lossFib volA A fib Φ i x) ^ 2))
              ≤ 2 * (Fmax ^ 2 * (Work.BoseFixB1S.boxQCount volA ℓ A Φ
                    + ∑ i : Fin N, ∑ j ∈ Finset.univ.erase i,
                        ∫ x in Submission.BoseGases.abox N ℓ,
                          (Work.UBBInputs8.boxPInd volA A j
                            (Work.UBBInputs8.boxQInd volA A i Φ) x) ^ 2)
                  + Fmax ^ 2 * Work.BoseFixB1S.boxQCount volA ℓ A Φ) := by
            linarith [hS3, hS2]
          have hb2 : 2 * (μ * volA) * (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
                (lossFib volA A fib Φ i x) ^ 2)
              ≤ 2 * (μ * volA) * (Fmax ^ 2 * Work.BoseFixB1S.boxQCount volA ℓ A Φ) :=
            mul_le_mul_of_nonneg_left hS2 (mul_nonneg (by norm_num) hμv0)
          linarith [hb1, hb2]
    _ = 2 * Fmax ^ 2
          * ((∑ i : Fin N, ∑ j : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
                (Work.UBBInputs8.boxQInd volA A i Φ x)
                  * (Work.UBBInputs8.boxPInd volA A j Φ x))
              + (2 + μ * volA) * (Work.BoseFixB1S.boxQCount volA ℓ A Φ)) := by
          rw [hY]
          ring

theorem qSideLossB1 {N : ℕ} {ℓ volA μ : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA) (hμ : 0 ≤ μ)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
    (hsupp : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)),
      Φ x ≠ 0 → ∀ i : Fin N, x i ∈ A)
    {fib : EuclideanSpace ℝ (Fin 3) → ℝ} (hfibm : Measurable fib)
    (hfib0 : ∀ z, 0 ≤ fib z) {Fmax : ℝ} (hfible : ∀ z, fib z ≤ Fmax) :
    (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
        (Work.BoseFixB1S.n0FunOp volA A (fun r : ℝ => Real.sqrt (r + 1) + Real.sqrt (μ * volA))
          (fun y : Submission.BoseGases.X N =>
            fib (y i) * Work.UBBInputs8.boxQInd volA A i Φ y)) x ^ 2)
      ≤ 2 * Fmax ^ 2
          * ((∑ i : Fin N, ∑ j : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
                (Work.UBBInputs8.boxQInd volA A i Φ x)
                  * (Work.UBBInputs8.boxPInd volA A j Φ x))
              + (2 + μ * volA) * (Work.BoseFixB1S.boxQCount volA ℓ A Φ)) :=
  qSideLossB1_aux hℓ hvol hμ hA hvolA hAc hΦc hfibm hfib0 hfible

end Work.BoseFixB1S

