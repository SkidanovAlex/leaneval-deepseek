import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.eOneZeroOffB1
import Submission.Work.BoseFixB1S.n0IterZeroPresB1
import Submission.Work.BoseFixB1S.qSideLossB1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.boxQfibPeelB1`

**Peeling a slot-fibre weight off the `n₀`-quadratic form of the mean-free box state.**

For a measurable box `A` of volume `V = |A| > 0` inside `acube ℓ`, a fibre `fib ≥ 0` with
`fib ≤ Cf` on `A`, a continuous `Φ` and an arbitrary coefficient function `g`, the slot-`i` state
`Q_{B,i}Φ` (FS's mean-free projection, which carries the box indicator `1_A`) has

    Σᵢ ∫_{abox N ℓ} fib(xᵢ)·(g(n₀)Q_{B,i}Φ)² ≤ Cf · Σᵢ ∫_{abox N ℓ} (g(n₀)Q_{B,i}Φ)² .

## Proof

Everything is pointwise plus monotonicity of the integral:

* `A ≠ ∅` (its volume is `V > 0`), hence `0 ≤ Cf` (`0 ≤ fib z ≤ Cf` for `z ∈ A`);
* `boxQInd volA A i Φ` carries the factor `1_A(xᵢ)`, and the whole `n₀`-calculus is a finite
  combination of slot iterations built from the `P_{B,j}` and their single-slot complements, so
  `cᵢ := g(n₀)Q_{B,i}Φ` vanishes at every configuration with `xᵢ ∉ A`
  (`boxQInd_zero_offB1`, `n0FunOp_zero_offB1`);
* consequently, at every `x`, either `xᵢ ∈ A` and `fib(xᵢ)·cᵢ x² ≤ Cf·cᵢ x²`
  (multiply `fib(xᵢ) ≤ Cf` by `cᵢ x² ≥ 0`), or `xᵢ ∉ A` and both sides vanish;
* `cᵢ` is a `GoodState` (`goodState_boxQInd`, `goodState_n0FunOpQSide`, i.e. measurable and
  bounded on the finite-measure box), so both integrands are integrable and
  `MeasureTheory.integral_mono` applies, together with `integral_const_mul` to pull `Cf` out of
  the slot integral and `Finset.mul_sum` to pull it out of the sum.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseFixB1S

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## The vanishing lemmas (local copies of the `UnbddB1` support lemmas) -/

/-- `P_{B,i}Φ` vanishes wherever the slot-`i` coordinate leaves `A` (it carries `1_A(xᵢ)`). -/
theorem boxPInd_zero_offB1 {N : ℕ} {volA : ℝ} {A : Set E3} (i : Fin N)
    (Φ : Submission.BoseGases.X N → ℝ) :
    ∀ x : Submission.BoseGases.X N, x i ∉ A → UBBInputs8.boxPInd volA A i Φ x = 0 := by
  intro x hx
  simp only [UBBInputs8.boxPInd]
  rw [Set.indicator_of_notMem hx, mul_zero]

/-- `Q_{B,i}Φ` vanishes wherever the slot-`i` coordinate leaves `A` (both terms carry `1_A(xᵢ)`). -/
theorem boxQInd_zero_offB1 {N : ℕ} {volA : ℝ} {A : Set E3} (i : Fin N)
    (Φ : Submission.BoseGases.X N → ℝ) :
    ∀ x : Submission.BoseGases.X N, x i ∉ A → UBBInputs8.boxQInd volA A i Φ x = 0 := by
  intro x hx
  simp only [UBBInputs8.boxQInd]
  rw [Set.indicator_of_notMem hx, zero_mul, boxPInd_zero_offB1 i Φ x hx, sub_zero]

/-- The `n₀` functional calculus preserves vanishing off the box in the slot `i`. -/
theorem n0FunOp_zero_offB1 {N : ℕ} {volA : ℝ} {A : Set E3} {i : Fin N} (g : ℝ → ℝ)
    {Ψ : Submission.BoseGases.X N → ℝ}
    (hΨ : ∀ x : Submission.BoseGases.X N, x i ∉ A → Ψ x = 0) :
    ∀ x : Submission.BoseGases.X N, x i ∉ A → n0FunOp volA A g Ψ x = 0 := by
  intro x hx
  rw [n0FunOp_eq_sum_card]
  refine Finset.sum_eq_zero fun S _ => ?_
  rw [show n0ProjOp volA A S Ψ x = 0 from
    n0IterZeroPresB1 (volA := volA) (A := A) (i := i)
      (fun j : Fin N => decide (j ∈ S)) (List.ofFn (fun j : Fin N => j)) hΨ x hx,
    mul_zero]

/-! ## The peel -/

theorem boxQfibPeelB1 {N : ℕ} {ℓ V : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hVeq : V = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {fib : EuclideanSpace ℝ (Fin 3) → ℝ} (hfm : Measurable fib) (hfib0 : ∀ z, 0 ≤ fib z)
    {Cf : ℝ} (hfible : ∀ z ∈ A, fib z ≤ Cf)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) (g : ℝ → ℝ) :
    (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
        fib (x i) * (Work.BoseFixB1S.n0FunOp V A g
          (Work.UBBInputs8.boxQInd V A i Φ)) x ^ 2)
      ≤ Cf * ∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
          (Work.BoseFixB1S.n0FunOp V A g (Work.UBBInputs8.boxQInd V A i Φ)) x ^ 2 := by
  classical
  -- ### The box `A` is nonempty, hence `0 ≤ Cf`
  have hAne : A.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro hempty
    rw [hempty] at hVeq
    simp at hVeq
    linarith
  obtain ⟨a₀, ha₀⟩ := hAne
  have hCf0 : 0 ≤ Cf := le_trans (hfib0 a₀) (hfible a₀ ha₀)
  -- ### `Φ` is measurable and bounded on the box
  obtain ⟨C, _hC0, hCb⟩ := exists_abox_bound hℓ hΦc
  have hΦg : GoodState ℓ Φ := ⟨hΦc.measurable, C, hCb⟩
  -- ### The slot-`i` estimate
  have key : ∀ i : Fin N,
      (∫ x in Submission.BoseGases.abox N ℓ,
        fib (x i) * (n0FunOp V A g (UBBInputs8.boxQInd V A i Φ)) x ^ 2)
      ≤ Cf * ∫ x in Submission.BoseGases.abox N ℓ,
        (n0FunOp V A g (UBBInputs8.boxQInd V A i Φ)) x ^ 2 := by
    intro i
    -- the slot state and its `n₀`-image are measurable and bounded on the box
    have hQg : GoodState ℓ (UBBInputs8.boxQInd V A i Φ) :=
      goodState_boxQInd hℓ hV hA hVeq hAc i hΦg
    have hCg : GoodState ℓ (n0FunOp V A g (UBBInputs8.boxQInd V A i Φ)) :=
      goodState_n0FunOpQSide hℓ hV hA hVeq hAc g hQg
    obtain ⟨hcm, Cg, hcb⟩ := hCg
    -- the `n₀`-image vanishes off the slot-`i` box
    have hzero : ∀ x : Submission.BoseGases.X N,
        x i ∉ A → (n0FunOp V A g (UBBInputs8.boxQInd V A i Φ)) x = 0 :=
      n0FunOp_zero_offB1 (volA := V) (A := A) (i := i) g (boxQInd_zero_offB1 i Φ)
    -- the pointwise estimate
    have hpt : ∀ x : Submission.BoseGases.X N,
        fib (x i) * (n0FunOp V A g (UBBInputs8.boxQInd V A i Φ)) x ^ 2
          ≤ Cf * (n0FunOp V A g (UBBInputs8.boxQInd V A i Φ)) x ^ 2 := by
      intro x
      by_cases hxi : x i ∈ A
      · exact mul_le_mul_of_nonneg_right (hfible (x i) hxi) (sq_nonneg _)
      · rw [hzero x hxi]
        simp
    -- the square of the `n₀`-image is bounded by `Cg ^ 2` on the box
    have hc2b : ∀ x ∈ Submission.BoseGases.abox N ℓ,
        ((n0FunOp V A g (UBBInputs8.boxQInd V A i Φ)) x) ^ 2 ≤ Cg ^ 2 := by
      intro x hx
      have h := hcb x hx
      rw [abs_le] at h
      exact sq_le_sq' h.1 h.2
    -- both integrands are bounded on the box, hence integrable
    have hbound1 : ∀ x ∈ Submission.BoseGases.abox N ℓ,
        |fib (x i) * (n0FunOp V A g (UBBInputs8.boxQInd V A i Φ)) x ^ 2| ≤ Cf * Cg ^ 2 := by
      intro x hx
      by_cases hxi : x i ∈ A
      · rw [abs_mul, abs_of_nonneg (hfib0 (x i)), abs_of_nonneg (sq_nonneg _)]
        calc fib (x i) * (n0FunOp V A g (UBBInputs8.boxQInd V A i Φ)) x ^ 2
            ≤ Cf * (n0FunOp V A g (UBBInputs8.boxQInd V A i Φ)) x ^ 2 :=
              mul_le_mul_of_nonneg_right (hfible (x i) hxi) (sq_nonneg _)
          _ ≤ Cf * Cg ^ 2 := mul_le_mul_of_nonneg_left (hc2b x hx) hCf0
      · have h0 : (n0FunOp V A g (UBBInputs8.boxQInd V A i Φ)) x = 0 := hzero x hxi
        rw [h0]
        have hz : fib (x i) * (0 : ℝ) ^ 2 = 0 := by ring
        rw [hz, abs_zero]
        exact mul_nonneg hCf0 (sq_nonneg Cg)
    have hbound2 : ∀ x ∈ Submission.BoseGases.abox N ℓ,
        |Cf * (n0FunOp V A g (UBBInputs8.boxQInd V A i Φ)) x ^ 2| ≤ Cf * Cg ^ 2 := by
      intro x hx
      rw [abs_mul, abs_of_nonneg hCf0, abs_of_nonneg (sq_nonneg _)]
      exact mul_le_mul_of_nonneg_left (hc2b x hx) hCf0
    have h1int : IntegrableOn
        (fun x : Submission.BoseGases.X N =>
          fib (x i) * (n0FunOp V A g (UBBInputs8.boxQInd V A i Φ)) x ^ 2)
        (Submission.BoseGases.abox N ℓ) volume :=
      integrableOn_abox_of_bound hℓ
        ((hfm.comp (continuous_apply i).measurable).mul (hcm.pow_const 2)) hbound1
    have h2int : IntegrableOn
        (fun x : Submission.BoseGases.X N =>
          Cf * (n0FunOp V A g (UBBInputs8.boxQInd V A i Φ)) x ^ 2)
        (Submission.BoseGases.abox N ℓ) volume :=
      integrableOn_abox_of_bound hℓ (hcm.pow_const 2 |>.const_mul Cf) hbound2
    -- monotonicity of the integral
    have hmain :
        (∫ x in Submission.BoseGases.abox N ℓ,
          fib (x i) * (n0FunOp V A g (UBBInputs8.boxQInd V A i Φ)) x ^ 2)
        ≤ ∫ x in Submission.BoseGases.abox N ℓ,
          Cf * (n0FunOp V A g (UBBInputs8.boxQInd V A i Φ)) x ^ 2 :=
      MeasureTheory.integral_mono h1int h2int hpt
    rwa [MeasureTheory.integral_const_mul] at hmain
  -- ### Sum the slot estimates and pull `Cf` out
  calc (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
        fib (x i) * (Work.BoseFixB1S.n0FunOp V A g
          (Work.UBBInputs8.boxQInd V A i Φ)) x ^ 2)
      ≤ ∑ i : Fin N, Cf * ∫ x in Submission.BoseGases.abox N ℓ,
          (Work.BoseFixB1S.n0FunOp V A g (Work.UBBInputs8.boxQInd V A i Φ)) x ^ 2 :=
        Finset.sum_le_sum (fun i _ => key i)
    _ = Cf * ∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
          (Work.BoseFixB1S.n0FunOp V A g (Work.UBBInputs8.boxQInd V A i Φ)) x ^ 2 := by
        rw [Finset.mul_sum]

end Work.BoseFixB1S
