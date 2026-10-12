import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.PQIdentAux
import Submission.Work.BoseFixB1S.boxPInd_pair_mixed_peel
import Submission.Work.BoseFixB1S.integrableOn_coord_fib
import Submission.Work.BoseFixB1S.slotPIndFlatMul
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory
open scoped Real BigOperators ENNReal

namespace Work.BoseFixB1S

open Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. Combinatorial helper: the `j ≠ i` iterated sum is the `pairSet` sum -/

/-- `pairSet N` (the *ordered* pairs of distinct indices) is the disjoint union over `i` of the
sets `{i} × (univ.erase i)`; hence the `j ≠ i` iterated sum is the `pairSet` sum. -/
theorem sum_erase_eq_pairSet {N : ℕ} (f : Fin N × Fin N → ℝ) :
    (∑ i : Fin N, ∑ j ∈ Finset.univ.erase i, f (i, j))
      = ∑ p ∈ Submission.BoseGases.pairSet N, f p := by
  rw [Submission.BoseGases.pairSet, Finset.sum_filter, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.filter_ne' Finset.univ i, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : i = j
  · subst h; simp
  · simp [h, Ne.symm h]

/-! ## 2. The fibre written on the box: a vanishing slot factor times an integrable fibre -/

/-- If `S·(1_A·fib)(xᵢ)` is integrable on the box and `S` vanishes wherever the `i`-th coordinate
leaves `A`, then `S·fib(xᵢ)` is integrable on the box as well (the two integrands agree pointwise
on the box). -/
theorem integrableOn_fib_of_mul_indicator {N : ℕ} {ℓ : ℝ}
    {A : Set E3} (hA : MeasurableSet A) (i : Fin N) {S : X N → ℝ}
    {fib : E3 → ℝ}
    (hS : IntegrableOn (fun x : X N => S x * A.indicator fib (x i)) (abox N ℓ) volume)
    (hzero : ∀ x ∈ abox N ℓ, x i ∉ A → S x = 0) :
    IntegrableOn (fun x : X N => S x * fib (x i)) (abox N ℓ) volume := by
  refine hS.congr ?_
  filter_upwards [self_mem_ae_restrict (abox_measurable N ℓ)] with x hx
  by_cases h : x i ∈ A
  · simp only [Set.indicator_of_mem h]
  · simp only [Set.indicator_of_notMem h, hzero x hx h, zero_mul]

/-! ## 3. The flat-slot ratio with an integrable fibre

For `Ψ, Θ` both fixed by `Pᵢ` and an arbitrary *integrable* fibre `fib`, the fibre weight collapses
to its box average: `∫ Ψ·Θ·fib(xᵢ) = (volA⁻¹∫_A fib)·∫ Ψ·Θ`.  This is
`Work.BoseFixB1S.slotPIndFlatMul` with the boundedness of `fib` replaced by `IntegrableOn fib A`:
`flatSlotMul_integral` (whose only input is the integrability of the product) is applied twice,
with `g := fib` and `g := 1`, and the two are compared using `∫_A 1 = volA`.  The integrability of
the product comes from `integrableOn_coord_fib` (bounded slot factor times the integrable fibre
`1_A·fib` pulled back along the coordinate `i`) together with `integrableOn_fib_of_mul_indicator`
(the slot factor `Ψ·Θ` carries `1_A(xᵢ)` by `Pᵢ`-fixedness, so the indicator may be dropped). -/
theorem flatSlotFib_integrable_aux {n : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume : MeasureTheory.Measure E3).real A)
    (hAc : A ⊆ acube ℓ)
    (i : Fin (n + 1)) {Ψ Θ : X (n + 1) → ℝ}
    (hΨm : Measurable Ψ) (hΘm : Measurable Θ)
    (hΨfix : Work.UBBInputs8.boxPInd volA A i Ψ = Ψ)
    (hΘfix : Work.UBBInputs8.boxPInd volA A i Θ = Θ)
    {CΨ CΘ : ℝ} (hΨb : ∀ x ∈ abox (n + 1) ℓ, |Ψ x| ≤ CΨ)
    (hΘb : ∀ x ∈ abox (n + 1) ℓ, |Θ x| ≤ CΘ)
    {fib : E3 → ℝ} (hfib : IntegrableOn fib A) :
    (∫ x in abox (n + 1) ℓ, Ψ x * Θ x * fib (x i))
      = ((1 / volA) * ∫ z in A, fib z)
        * (∫ x in abox (n + 1) ℓ, Ψ x * Θ x) := by
  have hvolA' : volA = ((MeasureTheory.volume : MeasureTheory.Measure E3) A).toReal := by
    have h := hvolA
    rw [MeasureTheory.Measure.real_def] at h
    exact h
  -- `Pᵢ`-fixedness forces the slot factor to carry the box indicator
  have hzero : ∀ x ∈ abox (n + 1) ℓ, x i ∉ A → Ψ x * Θ x = 0 := by
    intro x hx hxA
    have hP : ∀ ξ : X (n + 1) → ℝ, Work.UBBInputs8.boxPInd volA A i ξ = ξ →
        ξ x = 0 := by
      intro ξ hξ
      have h0 : Work.UBBInputs8.boxPInd volA A i ξ x = 0 := by
        simp only [Work.UBBInputs8.boxPInd, Set.indicator_of_notMem hxA, mul_zero]
      exact (congrFun hξ x).symm.trans h0
    rw [hP Ψ hΨfix, zero_mul]
  have hSmeas : Measurable (fun x : X (n + 1) => Ψ x * Θ x) := hΨm.mul hΘm
  have hSb : ∀ x ∈ abox (n + 1) ℓ, |Ψ x * Θ x| ≤ |CΨ| * |CΘ| := by
    intro x hx
    rw [abs_mul]
    exact mul_le_mul (le_trans (hΨb x hx) (le_abs_self CΨ))
      (le_trans (hΘb x hx) (le_abs_self CΘ)) (abs_nonneg _) (abs_nonneg _)
  -- integrability of the product, first with `1_A·fib` and then with `fib`
  have hBind : IntegrableOn (fun x : X (n + 1) => (Ψ x * Θ x) * A.indicator fib (x i))
      (abox (n + 1) ℓ) volume :=
    integrableOn_coord_fib (N := n + 1) (ℓ := ℓ) hℓ i hA hAc hSmeas.aestronglyMeasurable
      (C := |CΨ| * |CΘ|) hSb hfib
  have hIntFib : IntegrableOn (fun x : X (n + 1) => Ψ x * Θ x * fib (x i))
      (abox (n + 1) ℓ) volume :=
    integrableOn_fib_of_mul_indicator hA i hBind hzero
  have hIntOne : IntegrableOn
      (fun x : X (n + 1) => Ψ x * Θ x * (fun _ : E3 => (1 : ℝ)) (x i))
      (abox (n + 1) ℓ) volume :=
    integrableOn_mul_of_bound hℓ hSmeas measurable_const hSb (Cg := 1)
      (fun z _ => by simp)
  -- the two flat-slot peels
  have h1 := flatSlotMul_integral (n := n) (ℓ := ℓ) (volA := volA) (A := A)
    hA hAc i hΨfix hΘfix fib hIntFib
  have h2 := flatSlotMul_integral (n := n) (ℓ := ℓ) (volA := volA) (A := A)
    hA hAc i hΨfix hΘfix (fun _ : E3 => (1 : ℝ)) hIntOne
  set J : ℝ := ∫ r in abox n ℓ,
    (∫ z in A, Ψ (kcInsN n i (z, r))) * (∫ z in A, Θ (kcInsN n i (z, r))) with hJ
  have hA1 : (∫ z in A, (fun _ : E3 => (1 : ℝ)) z) = volA := by
    rw [MeasureTheory.setIntegral_const, smul_eq_mul, mul_one]
    exact hvolA'.symm
  have hmass : (∫ x in abox (n + 1) ℓ, Ψ x * Θ x) = volA * (1 / volA) ^ 2 * J := by
    have h2' : (∫ x in abox (n + 1) ℓ, Ψ x * Θ x * (fun _ : E3 => (1 : ℝ)) (x i))
        = volA * (1 / volA) ^ 2 * J := by
      rw [h2, hA1]
    rw [← h2']
    apply integral_congr_ae
    filter_upwards with x
    simp
  rw [h1, hmass]
  have hvolne : volA ≠ 0 := ne_of_gt hvol
  field_simp

theorem boxPInd_fib_collapse {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    (hvolA : volA = (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).real A)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
    {fib : EuclideanSpace ℝ (Fin 3) → ℝ} (hfib : MeasureTheory.IntegrableOn fib A) :
    (Finset.sum Finset.univ (fun i : Fin N =>
        ∫ x in Submission.BoseGases.abox N ℓ,
          (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2 * fib (x i))
      = ((1 / volA) * ∫ z in A, fib z) * Work.BoseFixB1S.boxFlatCount volA ℓ A Φ)
    ∧ (Finset.sum Finset.univ (fun i : Fin N =>
        ∫ x in Submission.BoseGases.abox N ℓ,
          (Work.UBBInputs8.boxPInd volA A i Φ x)
            * (Finset.sum (Finset.univ.erase i) (fun j : Fin N =>
                Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxPInd volA A i Φ) x))
            * fib (x i))
      = ((1 / volA) * ∫ z in A, fib z) * Work.BoseFixB1S.boxPairCount volA ℓ A Φ) := by
  classical
  have hvolA' : volA = ((MeasureTheory.volume : MeasureTheory.Measure E3) A).toReal := by
    have h := hvolA
    rw [MeasureTheory.Measure.real_def] at h
    exact h
  constructor
  · -- ============ conjunct 1: the flat count ============
    cases N with
    | zero => simp [Work.BoseFixB1S.boxFlatCount]
    | succ n =>
      obtain ⟨C, hC0, hΦb, hPb, hQb⟩ :=
        boxBounds (N := n + 1) (ℓ := ℓ) (volA := volA) (A := A) hℓ hvol hA hvolA' hAc hΦc
      have hkey : ∀ i : Fin (n + 1),
          (∫ x in abox (n + 1) ℓ,
              (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2 * fib (x i))
            = ((1 / volA) * ∫ z in A, fib z)
              * (∫ x in abox (n + 1) ℓ, (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2) := by
        intro i
        have hm : Measurable (Work.UBBInputs8.boxPInd volA A i Φ) :=
          measurable_boxPInd volA A hA i hΦc.measurable
        have hfix : Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A i Φ)
            = Work.UBBInputs8.boxPInd volA A i Φ :=
          funext fun x => boxPInd_idempotent hℓ hvol hA hvolA' hAc i Φ x
        have h := flatSlotFib_integrable_aux (n := n) (ℓ := ℓ) (volA := volA) (A := A)
          hℓ hvol hA hvolA hAc i (Ψ := Work.UBBInputs8.boxPInd volA A i Φ)
          (Θ := Work.UBBInputs8.boxPInd volA A i Φ) hm hm hfix hfix (hPb i) (hPb i) hfib
        have hsq : (∫ x in abox (n + 1) ℓ,
              (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2 * fib (x i))
            = ∫ x in abox (n + 1) ℓ,
                Work.UBBInputs8.boxPInd volA A i Φ x * Work.UBBInputs8.boxPInd volA A i Φ x
                  * fib (x i) := by
          apply integral_congr_ae
          filter_upwards with x
          ring
        have hsq2 : (∫ x in abox (n + 1) ℓ, (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2)
            = ∫ x in abox (n + 1) ℓ,
                Work.UBBInputs8.boxPInd volA A i Φ x
                  * Work.UBBInputs8.boxPInd volA A i Φ x := by
          apply integral_congr_ae
          filter_upwards with x
          ring
        rw [hsq, hsq2, h]
      rw [Finset.sum_congr rfl (fun i _ => hkey i)]
      simp only [Work.BoseFixB1S.boxFlatCount]
      rw [Finset.mul_sum]
  · -- ============ conjunct 2: the flat pair count ============
    cases N with
    | zero =>
      have hzero : Work.BoseFixB1S.boxPairCount volA ℓ A Φ = 0 := by
        simp [Work.BoseFixB1S.boxPairCount, Submission.BoseGases.pairSet]
      rw [hzero, mul_zero]
      simp
    | succ n =>
      obtain ⟨C, hC0, hΦb, hPb, hQb⟩ :=
        boxBounds (N := n + 1) (ℓ := ℓ) (volA := volA) (A := A) hℓ hvol hA hvolA' hAc hΦc
      -- every pair integrand is integrable on the box
      have hint : ∀ i j : Fin (n + 1),
          IntegrableOn (fun x : X (n + 1) =>
              Work.UBBInputs8.boxPInd volA A i Φ x
                * Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxPInd volA A i Φ) x
                * fib (x i)) (abox (n + 1) ℓ) volume := by
        intro i j
        have hSm : Measurable (fun x : X (n + 1) =>
            Work.UBBInputs8.boxPInd volA A i Φ x
              * Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxPInd volA A i Φ) x) :=
          (measurable_boxPInd volA A hA i hΦc.measurable).mul
            (measurable_boxPInd volA A hA j (measurable_boxPInd volA A hA i hΦc.measurable))
        have hSb : ∀ x ∈ abox (n + 1) ℓ,
            |Work.UBBInputs8.boxPInd volA A i Φ x
              * Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxPInd volA A i Φ) x| ≤ C * C := by
          intro x hx
          rw [abs_mul]
          exact mul_le_mul (hPb i x hx)
            (abs_boxPInd_le hℓ hvol hA hvolA' hAc j (hPb i) x hx) (abs_nonneg _)
            (le_trans (abs_nonneg _) (hPb i x hx))
        have hB := integrableOn_coord_fib (N := n + 1) (ℓ := ℓ) (A := A) hℓ i hA hAc
          hSm.aestronglyMeasurable hSb hfib
        refine integrableOn_fib_of_mul_indicator hA i hB (fun x hx hxA => ?_)
        have hzero : Work.UBBInputs8.boxPInd volA A i Φ x = 0 := by
          simp only [Work.UBBInputs8.boxPInd, Set.indicator_of_notMem hxA, mul_zero]
        rw [hzero, zero_mul]
      -- the per-pair value identity
      have hkey : ∀ i j : Fin (n + 1), i ≠ j →
          (∫ x in abox (n + 1) ℓ, Work.UBBInputs8.boxPInd volA A i Φ x
              * Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxPInd volA A i Φ) x
              * fib (x i))
            = ((1 / volA) * ∫ z in A, fib z)
              * (∫ x in abox (n + 1) ℓ,
                  (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x) ^ 2) := by
        intro i j hij
        have hfix_i : Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A i Φ)
            = Work.UBBInputs8.boxPInd volA A i Φ :=
          funext fun x => boxPInd_idempotent hℓ hvol hA hvolA' hAc i Φ x
        have hfix_ij : Work.UBBInputs8.boxPInd volA A i
              (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ))
            = Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) :=
          funext fun x => boxPInd_idempotent hℓ hvol hA hvolA' hAc i
            (Work.UBBInputs8.boxPInd volA A j Φ) x
        have hC := flatSlotFib_integrable_aux (n := n) (ℓ := ℓ) (volA := volA) (A := A)
          hℓ hvol hA hvolA hAc i (Ψ := Work.UBBInputs8.boxPInd volA A i Φ)
          (Θ := Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ))
          (measurable_boxPInd volA A hA i hΦc.measurable)
          (measurable_boxPInd volA A hA i (measurable_boxPInd volA A hA j hΦc.measurable))
          hfix_i hfix_ij (hPb i) (abs_boxPInd_le hℓ hvol hA hvolA' hAc i (hPb j)) hfib
        have hcomm : ∀ x : X (n + 1),
            Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxPInd volA A i Φ) x
              = Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x :=
          fun x => (boxPInd_comm hℓ hvol hA hvolA' hAc hij hΦc x).symm
        have hL : (∫ x in abox (n + 1) ℓ, Work.UBBInputs8.boxPInd volA A i Φ x
              * Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxPInd volA A i Φ) x
              * fib (x i))
            = ∫ x in abox (n + 1) ℓ, Work.UBBInputs8.boxPInd volA A i Φ x
              * Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x
              * fib (x i) := by
          apply integral_congr_ae
          filter_upwards with x
          rw [hcomm x]
        rw [hL, hC, boxPInd_pair_mixed_peel (N := n + 1) (ℓ := ℓ) (volA := volA) (A := A)
          hℓ hvol hA hvolA' hAc (i := i) (j := j) hij hΦc]
      -- split the inner sum out of the `i`-th integral
      have hsplit : ∀ i : Fin (n + 1),
          (∫ x in abox (n + 1) ℓ, Work.UBBInputs8.boxPInd volA A i Φ x
              * (∑ j ∈ Finset.univ.erase i,
                  Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxPInd volA A i Φ) x)
              * fib (x i))
            = ∑ j ∈ Finset.univ.erase i,
                ∫ x in abox (n + 1) ℓ, Work.UBBInputs8.boxPInd volA A i Φ x
                  * Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxPInd volA A i Φ) x
                  * fib (x i) := by
        intro i
        have hpt : ∀ x : X (n + 1),
            Work.UBBInputs8.boxPInd volA A i Φ x
              * (∑ j ∈ Finset.univ.erase i,
                  Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxPInd volA A i Φ) x)
              * fib (x i)
            = ∑ j ∈ Finset.univ.erase i,
                Work.UBBInputs8.boxPInd volA A i Φ x
                  * Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxPInd volA A i Φ) x
                  * fib (x i) := by
          intro x
          rw [Finset.mul_sum, Finset.sum_mul]
        rw [show (∫ x in abox (n + 1) ℓ, Work.UBBInputs8.boxPInd volA A i Φ x
              * (∑ j ∈ Finset.univ.erase i,
                  Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxPInd volA A i Φ) x)
              * fib (x i))
            = ∫ x in abox (n + 1) ℓ, ∑ j ∈ Finset.univ.erase i,
                Work.UBBInputs8.boxPInd volA A i Φ x
                  * Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxPInd volA A i Φ) x
                  * fib (x i) from
          integral_congr_ae (ae_of_all _ hpt)]
        exact MeasureTheory.integral_finsetSum (Finset.univ.erase i)
          (fun j _ => hint i j)
      rw [Finset.sum_congr rfl (fun i _ => hsplit i)]
      rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j hj =>
        hkey i j (fun h => (Finset.mem_erase.mp hj).1 h.symm)))]
      -- pull the constant out of the double sum
      rw [show (∑ i : Fin (n + 1), ∑ j ∈ Finset.univ.erase i,
              ((1 / volA) * ∫ z in A, fib z)
                * (∫ x in abox (n + 1) ℓ,
                    (Work.UBBInputs8.boxPInd volA A i
                      (Work.UBBInputs8.boxPInd volA A j Φ) x) ^ 2))
            = ((1 / volA) * ∫ z in A, fib z)
              * (∑ i : Fin (n + 1), ∑ j ∈ Finset.univ.erase i,
                  ∫ x in abox (n + 1) ℓ,
                    (Work.UBBInputs8.boxPInd volA A i
                      (Work.UBBInputs8.boxPInd volA A j Φ) x) ^ 2) from by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ =>
          (Finset.mul_sum (Finset.univ.erase i)
            (fun j : Fin (n + 1) => ∫ x in abox (n + 1) ℓ,
              (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x) ^ 2)
            ((1 / volA) * ∫ z in A, fib z)).symm)]
      -- the iterated distinct-pair sum is the `pairSet` sum
      rw [sum_erase_eq_pairSet (fun p : Fin (n + 1) × Fin (n + 1) =>
        ∫ x in abox (n + 1) ℓ,
          (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxPInd volA A p.2 Φ) x) ^ 2)]
      simp only [Work.BoseFixB1S.boxPairCount]

end Work.BoseFixB1S
