import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.integrableOn_coord_fib
import Submission.Work.BoseFixB1S.slotPIndFlatMul
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S

open MeasureTheory
open scoped Real BigOperators ENNReal

set_option maxHeartbeats 1000000

/-! ## Two pointwise facts about `Pᵢ`-fixed slots

Both are consequences of the fixed-point equation `hΨfix : PᵢΨ = Ψ` and the explicit form
`boxPInd volA A i Φ x = (1/volA)·∫_{z∈A} Φ(x|i↦z) dz · 1_A(xᵢ)` of the box projection. -/

/-- **A `Pᵢ`-fixed slot carries its own box indicator.**  If `Ψ` is fixed by
`Pᵢ = boxPInd volA A i`, then `1_A(xᵢ)·Ψ x = Ψ x`: the fixed-point equation exhibits `Ψ x` as
`1_A(xᵢ)` times the slot mean, and `1_A(xᵢ)² = 1_A(xᵢ)`. in particular a `Pᵢ`-fixed slot
vanishes at every configuration whose `i`-th slot lies outside `A`. -/
theorem boxPInd_fixed_indicator_mul {N : ℕ} {volA : ℝ}
    {A : Set (EuclideanSpace ℝ (Fin 3))} (i : Fin N)
    {Ψ : Submission.BoseGases.X N → ℝ}
    (hΨfix : Work.UBBInputs8.boxPInd volA A i Ψ = Ψ) (x : Submission.BoseGases.X N) :
    A.indicator (fun _ => (1 : ℝ)) (x i) * Ψ x = Ψ x := by
  rw [← congrFun hΨfix x]
  by_cases hx : x i ∈ A <;>
    simp [Work.UBBInputs8.boxPInd, Set.indicator_of_mem, Set.indicator_of_notMem, hx]

/-- **The fibre may be replaced by its box indicator.**  For two `Pᵢ`-fixed slots `Ψ`, `Θ` the
integrand `Ψ·Θ·fib(xᵢ)` does not see the values of `fib` outside `A`:
`Ψ·Θ·fib(xᵢ) = Ψ·Θ·(1_A fib)(xᵢ)` pointwise.  (Off `A` in slot `i` both `Ψ` and `Θ` vanish by
`boxPInd_fixed_indicator_mul`, on `A` the two fibres agree.) -/
theorem flatSlotFib_indicator_eq {n : ℕ} {volA : ℝ}
    {A : Set (EuclideanSpace ℝ (Fin 3))} (i : Fin (n + 1))
    {Ψ Θ : Submission.BoseGases.X (n + 1) → ℝ}
    (hΨfix : Work.UBBInputs8.boxPInd volA A i Ψ = Ψ)
    (hΘfix : Work.UBBInputs8.boxPInd volA A i Θ = Θ)
    (fib : EuclideanSpace ℝ (Fin 3) → ℝ) (x : Submission.BoseGases.X (n + 1)) :
    Ψ x * Θ x * fib (x i) = Ψ x * Θ x * (A.indicator fib) (x i) := by
  by_cases hx : x i ∈ A
  · simp [Set.indicator_of_mem hx]
  · have hΨ0 : Ψ x = 0 := by
      have h := boxPInd_fixed_indicator_mul (volA := volA) i hΨfix x
      simpa [Set.indicator_of_notMem hx] using h.symm
    have hΘ0 : Θ x = 0 := by
      have h := boxPInd_fixed_indicator_mul (volA := volA) i hΘfix x
      simpa [Set.indicator_of_notMem hx] using h.symm
    simp [hΨ0, hΘ0, Set.indicator_of_notMem hx]

-- The flat-slot ratio with an *integrable* (not bounded) fibre: this is
-- `Work.BoseFixB1S.slotPIndFlatMul` with `hFm`/`hFb` weakened to `IntegrableOn fib A`.
-- Route: `Work.BoseFixB1S.flatSlotMul_integral` (proved, in `slotPIndFlatMul.lean`, whose only
-- integrability input is that of the product `Ψ·Θ·g(xᵢ)`; it needs no boundedness) applied twice,
-- with `g := A.indicator fib` and `g := 1`, plus `∫_A 1 = volA` from `hvolA`.  The integrability of
-- the product `Ψ·Θ·(A.indicator fib)(xᵢ)` is `integrableOn_coord_fib`-type: `Ψ·Θ` is bounded on the
-- box and `A.indicator fib` is globally integrable (`MeasureTheory.integrable_indicator_iff`); note
-- `Ψ·Θ·fib(xᵢ) = Ψ·Θ·(A.indicator fib)(xᵢ)` pointwise because `hΨfix`/`hΘfix` make both factors carry
-- `1_A(xᵢ)` (`flatSlotPInd_fixed_eq`, `boxPInd_kcInsN`).
theorem flatSlotFib_integrable {n : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).real A)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    (i : Fin (n + 1)) {Ψ Θ : Submission.BoseGases.X (n + 1) → ℝ}
    (hΨm : Measurable Ψ) (hΘm : Measurable Θ)
    (hΨfix : Work.UBBInputs8.boxPInd volA A i Ψ = Ψ)
    (hΘfix : Work.UBBInputs8.boxPInd volA A i Θ = Θ)
    {CΨ CΘ : ℝ} (hΨb : ∀ x ∈ Submission.BoseGases.abox (n + 1) ℓ, |Ψ x| ≤ CΨ)
    (hΘb : ∀ x ∈ Submission.BoseGases.abox (n + 1) ℓ, |Θ x| ≤ CΘ)
    {fib : EuclideanSpace ℝ (Fin 3) → ℝ} (hfib : MeasureTheory.IntegrableOn fib A) :
    (∫ x in Submission.BoseGases.abox (n + 1) ℓ, Ψ x * Θ x * fib (x i))
      = ((1 / volA) * ∫ z in A, fib z)
        * (∫ x in Submission.BoseGases.abox (n + 1) ℓ, Ψ x * Θ x) := by
  -- `Ψ·Θ` is a.e.-strongly-measurable and bounded on the box.
  have hSm : AEStronglyMeasurable (fun x : Submission.BoseGases.X (n + 1) => Ψ x * Θ x)
      (volume.restrict (Submission.BoseGases.abox (n + 1) ℓ)) :=
    (hΨm.mul hΘm).aestronglyMeasurable
  have hSb : ∀ x ∈ Submission.BoseGases.abox (n + 1) ℓ,
      |(fun x : Submission.BoseGases.X (n + 1) => Ψ x * Θ x) x| ≤ CΨ * CΘ := by
    intro x hx
    rw [abs_mul]
    exact mul_le_mul (hΨb x hx) (hΘb x hx) (abs_nonneg _) (le_trans (abs_nonneg _) (hΨb x hx))
  -- Integrability of the two products, and the two instances of the flat-slot identity.
  have hIntFib : IntegrableOn
      (fun x : Submission.BoseGases.X (n + 1) => Ψ x * Θ x * A.indicator fib (x i))
      (Submission.BoseGases.abox (n + 1) ℓ) volume :=
    integrableOn_coord_fib hℓ i hA hAc hSm hSb hfib
  have hIntOne : IntegrableOn
      (fun x : Submission.BoseGases.X (n + 1) =>
        Ψ x * Θ x * (fun _ : EuclideanSpace ℝ (Fin 3) => (1 : ℝ)) (x i))
      (Submission.BoseGases.abox (n + 1) ℓ) volume :=
    integrableOn_slotMul_of_bound hℓ i aestronglyMeasurable_const (fun z _ => by simp)
      (CF := 1) hSm hSb
  have hG := flatSlotMul_integral (n := n) (ℓ := ℓ) hA hAc i hΨfix hΘfix
    (A.indicator fib) hIntFib
  have hG1 := flatSlotMul_integral (n := n) (ℓ := ℓ) hA hAc i hΨfix hΘfix
    (fun _ : EuclideanSpace ℝ (Fin 3) => (1 : ℝ)) hIntOne
  -- The common remaining factor.
  set J : ℝ := ∫ r in Submission.BoseGases.abox n ℓ,
      (∫ z in A, Ψ (Submission.BoseGases.kcInsN n i (z, r)))
        * (∫ z in A, Θ (Submission.BoseGases.kcInsN n i (z, r))) with hJdef
  -- Replacing `fib` by its `A`-indicator in the integrand.
  have hswap : (∫ x in Submission.BoseGases.abox (n + 1) ℓ, Ψ x * Θ x * fib (x i))
      = ∫ x in Submission.BoseGases.abox (n + 1) ℓ, Ψ x * Θ x * (A.indicator fib) (x i) := by
    apply integral_congr_ae
    filter_upwards with x
    exact flatSlotFib_indicator_eq i hΨfix hΘfix fib x
  have hAfib : (∫ z in A, A.indicator fib z) = ∫ z in A, fib z := by
    rw [MeasureTheory.setIntegral_indicator hA]
    simp
  -- The `fib := 1` instance computes `∫ Ψ·Θ = volA·(1/volA)²·J`.
  have hden1 : (∫ x in Submission.BoseGases.abox (n + 1) ℓ,
        Ψ x * Θ x * (fun _ : EuclideanSpace ℝ (Fin 3) => (1 : ℝ)) (x i))
      = ∫ x in Submission.BoseGases.abox (n + 1) ℓ, Ψ x * Θ x := by
    apply integral_congr_ae
    filter_upwards with x
    simp
  have hAone : (∫ z in A, (fun _ : EuclideanSpace ℝ (Fin 3) => (1 : ℝ)) z) = volA := by
    rw [MeasureTheory.setIntegral_const, smul_eq_mul, mul_one]
    exact hvolA.symm
  have hden : (∫ x in Submission.BoseGases.abox (n + 1) ℓ, Ψ x * Θ x)
      = volA * (1 / volA) ^ 2 * J := by
    rw [← hden1, hG1, hAone]
  rw [hswap, hG, hAfib, hden]
  field_simp

end Work.BoseFixB1S
