import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.HopDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1S.hopPsideSupplyB1` — the `P`-side supply of the hopping layer

The hopping term of FS's completion of squares (`lm:appinteractionestimate`) produces, per hopping
edge `p ∈ hopPairSet i` (a pair `(S,T)` of disjoint slots with `i ∈ S`), two supplies obtained by
Cauchy–Schwarz:

* the **`Q`-side** supply `∫_{abox} ψ_{c_i(p)}²·|δ(xᵢ)|` (the *child* component, an excited block),
* the **`P`-side** supply `∫_{abox} ψ_p²·|δ(xᵢ)|` (the *parent* component, a flat block),

with `δ = fib − κ`, `κ = M₁/V`.  This file proves the `P`-side bound: since `ψ_p` lies in the range
of the box projection `Pᵢ` (`i ∈ S`), it is supported on `{xᵢ ∈ A}` and is the box indicator times a
slot-`i`-independent mean, so *the fibre weight collapses to its box average*:

    ∫_{abox N ℓ} ψ_p²·|fib(xᵢ) − κ| ≤ 2κ·∫_{abox N ℓ} ψ_p²        (i ∈ p.1),

because on `{xᵢ ∈ A}` one has `|fib − κ| ≤ fib + κ` (`fib ≥ 0` on `A`, `κ ≥ 0`) and
`∫ ψ_p²·fib(xᵢ) = κ∫ψ_p²`.  Summing over the slots `i ∈ p.1` and over the pairs, with the
coefficient `|p.1| + 1 + μV`, gives the target

    2κ·(Σ_p |p.1|²∫ψ_p² + (1+μV)·Σ_p |p.1|∫ψ_p²).

Everything is expressed with the corpus's box projections/box components
(`Work.UBBInputs8.boxPInd`, `Work.BoseFixB1S.boxCompT`) and the analysis box `abox N ℓ`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseFixB1S

open Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-! ## 0. Elementary helpers -/

/-- `A` has finite volume: it sits in the cube `acube ℓ`. -/
theorem hop_volume_ne_top {ℓ : ℝ} (hℓ : 0 < ℓ) {A : Set E3} (hAc : A ⊆ acube ℓ) :
    (volume : Measure E3) A ≠ ⊤ :=
  ne_of_lt (lt_of_le_of_lt (MeasureTheory.measure_mono hAc) (acube_lt_top ℓ hℓ.le))

/-- The square of the box indicator times a constant. -/
theorem hopIndicator_sq_mul (A : Set E3) (y : E3) (c : ℝ) :
    (A.indicator (fun _ => (1 : ℝ)) y * c) ^ 2 = A.indicator (fun _ => (1 : ℝ)) y * c ^ 2 := by
  by_cases h : y ∈ A <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]

/-- The fibre mean `M₁ = ∫_A fib` is nonnegative when `fib ≥ 0` on `A`. -/
theorem hopM1_nonneg {A : Set E3} (hA : MeasurableSet A) {fib : E3 → ℝ}
    (hfibnn : ∀ z ∈ A, 0 ≤ fib z) {M1 : ℝ} (hM1 : M1 = ∫ z in A, fib z) : 0 ≤ M1 := by
  rw [hM1]
  refine MeasureTheory.integral_nonneg_of_ae ?_
  show ∀ᵐ z ∂(volume.restrict A), (0 : ℝ) ≤ fib z
  rw [MeasureTheory.ae_restrict_iff' hA]
  exact Filter.Eventually.of_forall hfibnn

/-! ## 1. The slot-`i` box mean and the slot peel -/

/-- The slot-`i` mean of `ψ` at a configuration `r` of the remaining slots:
`V⁻¹ ∫_{z ∈ A} ψ (r|ᵢ↦z)`. -/
noncomputable def hopSlotMean {n : ℕ} (V : ℝ) (A : Set E3) (i : Fin (n + 1))
    (ψ : X (n + 1) → ℝ) : X n → ℝ :=
  fun r => (1 / V) * ∫ z in A, ψ (kcInsN n i (z, r))

/-- A component that is `Pᵢ`-fixed on the box and vanishes off `{xᵢ ∈ A}` is the box indicator
times its slot-`i` mean at every configuration of the box. -/
theorem hopSlotMean_hins {n : ℕ} {ℓ V : ℝ} (hV : 0 < V) {A : Set E3}
    (hAc : A ⊆ acube ℓ) (i : Fin (n + 1)) {ψ : X (n + 1) → ℝ}
    (hpe : ∀ x ∈ abox (n + 1) ℓ, ψ x = UBBInputs8.boxPInd V A i ψ x)
    (hvanish : ∀ x : X (n + 1), x i ∉ A → ψ x = 0) :
    ∀ r ∈ abox n ℓ, ∀ y : E3,
      ψ (kcInsN n i (y, r)) = A.indicator (fun _ => (1 : ℝ)) y * hopSlotMean V A i ψ r := by
  intro r hr y
  by_cases hy : y ∈ A
  · have hmem : kcInsN n i (y, r) ∈ abox (n + 1) ℓ := kcInsN_mem_abox hAc i hy hr
    rw [hpe _ hmem, boxPInd_kcInsN, Set.indicator_of_mem hy, one_mul]
    simp [hopSlotMean]
  · have hy' : (kcInsN n i (y, r)) i ∉ A := by
      simpa [Submission.BoseGases.kc_insN_apply_same] using hy
    rw [hvanish _ hy', Set.indicator_of_notMem hy, zero_mul]

/-- **The slot peel.**  For a component `ψ` whose slot-`i` values are `1_A(y)·m(r)` on the box,
the box integral of `ψ²·G(xᵢ)` factorises into the mean square and the `A`-integral of `G`. -/
theorem hopPeel {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {A : Set E3} (hA : MeasurableSet A)
    (hAc : A ⊆ acube ℓ) (i : Fin (n + 1)) {ψ : X (n + 1) → ℝ} {m : X n → ℝ}
    (hins : ∀ r ∈ abox n ℓ, ∀ y : E3,
      ψ (kcInsN n i (y, r)) = A.indicator (fun _ => (1 : ℝ)) y * m r)
    {G : E3 → ℝ}
    (hInt : IntegrableOn (fun x : X (n + 1) => (ψ x) ^ 2 * G (x i)) (abox (n + 1) ℓ) volume) :
    (∫ x in abox (n + 1) ℓ, (ψ x) ^ 2 * G (x i))
      = (∫ r in abox n ℓ, (m r) ^ 2) * (∫ z in A, G z) := by
  rw [Submission.BoseGases.abox_integral_peel (i := i)
    (F := fun x : X (n + 1) => (ψ x) ^ 2 * G (x i)) hInt]
  simp only [Submission.BoseGases.kc_insN_apply_same]
  calc (∫ r in abox n ℓ, ∫ y in acube ℓ, (ψ (kcInsN n i (y, r))) ^ 2 * G y)
      = ∫ r in abox n ℓ, ∫ y in acube ℓ,
          A.indicator (fun _ => (1 : ℝ)) y * ((m r) ^ 2 * G y) := by
        apply setIntegral_congr_fun (abox_measurable n ℓ)
        intro r hr
        apply setIntegral_congr_fun (acube_measurable ℓ)
        intro y hy
        simp only []
        rw [hins r hr y, hopIndicator_sq_mul]
        ring
    _ = ∫ r in abox n ℓ, (m r) ^ 2 * (∫ z in A, G z) := by
        apply setIntegral_congr_fun (abox_measurable n ℓ)
        intro r hr
        simp only []
        rw [setIntegral_indicator_one_mul hA hAc (fun y => (m r) ^ 2 * G y)]
        rw [MeasureTheory.integral_const_mul]
    _ = (∫ r in abox n ℓ, (m r) ^ 2) * (∫ z in A, G z) := by
        rw [MeasureTheory.integral_mul_const]

/-! ## 2. The fibre-deviation bound `∫_A |fib − κ| ≤ 2κV` -/

/-- Since `fib ≥ 0` on `A`, one has `∫_A |fib − κ| ≤ ∫_A (fib + κ) = M₁ + κV = 2κV`
(with `κ = M₁/V`); the non-integrable cases are handled by the `undef` conventions. -/
theorem hopAbsSubMean_le {ℓ V : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V)
    {A : Set E3} (hA : MeasurableSet A) (hVeq : V = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ acube ℓ)
    {fib : E3 → ℝ} (hfibm : Measurable fib) (hfibnn : ∀ z ∈ A, 0 ≤ fib z)
    {M1 : ℝ} (hM1 : M1 = ∫ z in A, fib z) :
    (∫ z in A, |fib z - M1 / V|) ≤ 2 * (M1 / V) * V := by
  have hM1nn : 0 ≤ M1 := hopM1_nonneg hA hfibnn hM1
  have hκnn : 0 ≤ M1 / V := div_nonneg hM1nn hV.le
  have hAne : (volume : Measure E3) A ≠ ⊤ := hop_volume_ne_top hℓ hAc
  by_cases hfib : IntegrableOn fib A volume
  · have hconst : IntegrableOn (fun _ : E3 => M1 / V) A volume :=
      integrableOn_const (C := M1 / V) hAne
    have hmono : (∫ z in A, |fib z - M1 / V|) ≤ ∫ z in A, (fib z + M1 / V) := by
      refine MeasureTheory.integral_mono_ae (hfib.sub hconst).abs (hfib.add hconst) ?_
      show ∀ᵐ z ∂(volume.restrict A), |fib z - M1 / V| ≤ fib z + M1 / V
      rw [MeasureTheory.ae_restrict_iff' hA]
      exact Filter.Eventually.of_forall (fun z hz => by
        rw [abs_le]
        exact ⟨by linarith [hfibnn z hz], by linarith [hκnn]⟩)
    have hval : (∫ z in A, (fib z + M1 / V)) = M1 + (M1 / V) * V := by
      rw [MeasureTheory.integral_add hfib hconst, ← hM1]
      congr 1
      rw [MeasureTheory.setIntegral_const, MeasureTheory.Measure.real_def, ← hVeq, smul_eq_mul,
        mul_comm]
    have hcancel : (M1 / V) * V = M1 := div_mul_cancel₀ M1 (ne_of_gt hV)
    have h2 : 2 * (M1 / V) * V = M1 + M1 := by rw [mul_assoc, hcancel]; ring
    rw [hval] at hmono
    rw [hcancel, ← h2] at hmono
    exact hmono
  · have hM1zero : M1 = 0 := by
      rw [hM1]
      exact MeasureTheory.integral_undef hfib
    subst hM1zero
    simp only [zero_div, sub_zero, mul_zero, zero_mul]
    by_cases habs : IntegrableOn (fun z : E3 => |fib z|) A volume
    · exfalso
      refine hfib (habs.congr ?_)
      rw [Filter.EventuallyEq]
      show ∀ᵐ z ∂(volume.restrict A), (fun z : E3 => |fib z|) z = fib z
      rw [MeasureTheory.ae_restrict_iff' hA]
      exact Filter.Eventually.of_forall (fun z hz => abs_of_nonneg (hfibnn z hz))
    · rw [MeasureTheory.integral_undef habs]

/-! ## 3. The per-edge `P`-side bound -/

/-- **The per-edge `P`-side supply.**  For a box component `ψ = boxCompT V A S T Φ` with `i ∈ S`
(so `ψ` is a flat (`Pᵢ`) block), the `|fib(xᵢ) − M₁/V|`-weighted box mass is paid by `2κ` times the
plain box mass. -/
theorem hopPsideInner_le {N : ℕ} {ℓ V : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V)
    {A : Set E3} (hA : MeasurableSet A) (hVeq : V = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ acube ℓ) {fib : E3 → ℝ} (hfibm : Measurable fib)
    (hfibnn : ∀ z ∈ A, 0 ≤ fib z) {M1 : ℝ} (hM1 : M1 = ∫ z in A, fib z)
    {Φ : X N → ℝ} (hΦc : Continuous Φ) {S T : Finset (Fin N)} (i : Fin N) (hi : i ∈ S) :
    (∫ x in abox N ℓ, (boxCompT V A S T Φ x) ^ 2 * |fib (x i) - M1 / V|)
      ≤ 2 * (M1 / V) * (∫ x in abox N ℓ, (boxCompT V A S T Φ x) ^ 2) := by
  have hM1nn : 0 ≤ M1 := hopM1_nonneg hA hfibnn hM1
  have hκnn : 0 ≤ M1 / V := div_nonneg hM1nn hV.le
  cases N with
  | zero => exact Fin.elim0 i
  | succ n =>
    set cr : X n → ℝ := hopSlotMean V A i (boxCompT V A S T Φ) with hcrdef
    obtain ⟨hψm, Cψ, hψb⟩ :=
      goodState_boxCompT hℓ hV hA hVeq hAc S T (goodState_of_continuous hℓ hΦc)
    have hpe : ∀ x ∈ abox (n + 1) ℓ,
        boxCompT V A S T Φ x = UBBInputs8.boxPInd V A i (boxCompT V A S T Φ) x := by
      intro x hx
      rw [boxPInd_boxCompT hℓ hV hA hVeq hAc S T hΦc i x hx, if_pos hi]
    have hvanish : ∀ x : X (n + 1), x i ∉ A → boxCompT V A S T Φ x = 0 :=
      fun x hx => boxComponent_vanish_off V A (Finset.mem_union_left T hi) Φ x hx
    have hins : ∀ r ∈ abox n ℓ, ∀ y : E3,
        boxCompT V A S T Φ (kcInsN n i (y, r)) = A.indicator (fun _ => (1 : ℝ)) y * cr r := by
      intro r hr y
      rw [hopSlotMean_hins (ℓ := ℓ) hV hAc i hpe hvanish r hr y, ← hcrdef]
    by_cases hInt : IntegrableOn
        (fun x : X (n + 1) => (boxCompT V A S T Φ x) ^ 2 * |fib (x i) - M1 / V|)
        (abox (n + 1) ℓ) volume
    · have hpeel1 := hopPeel hℓ hA hAc i hins (G := fun z => |fib z - M1 / V|) hInt
      have hInt2 : IntegrableOn
          (fun x : X (n + 1) =>
            (boxCompT V A S T Φ x) ^ 2 * (fun _ : E3 => (1 : ℝ)) (x i))
          (abox (n + 1) ℓ) volume := by
        refine (integrableOn_sq_of_bound hℓ hψm hψb).congr ?_
        filter_upwards with x
        simp
      have hpeel2 := hopPeel hℓ hA hAc i hins (G := fun _ : E3 => (1 : ℝ)) hInt2
      have hsq : (∫ x in abox (n + 1) ℓ, (boxCompT V A S T Φ x) ^ 2)
          = ∫ x in abox (n + 1) ℓ,
              (boxCompT V A S T Φ x) ^ 2 * (fun _ : E3 => (1 : ℝ)) (x i) := by
        apply setIntegral_congr_fun (abox_measurable (n + 1) ℓ)
        intro x hx
        ring
      have hV1 : (∫ z in A, (fun _ : E3 => (1 : ℝ)) z) = V := by
        rw [MeasureTheory.setIntegral_const, MeasureTheory.Measure.real_def, ← hVeq, smul_eq_mul,
          mul_one]
      rw [hpeel1, hsq, hpeel2, hV1]
      have hcr2nn : 0 ≤ (∫ r in abox n ℓ, (cr r) ^ 2) :=
        setIntegral_nonneg (abox_measurable n ℓ) (fun r _ => sq_nonneg _)
      have haux : (∫ z in A, |fib z - M1 / V|) ≤ 2 * (M1 / V) * V :=
        hopAbsSubMean_le hℓ hV hA hVeq hAc hfibm hfibnn hM1
      calc (∫ r in abox n ℓ, (cr r) ^ 2) * (∫ z in A, |fib z - M1 / V|)
          ≤ (∫ r in abox n ℓ, (cr r) ^ 2) * (2 * (M1 / V) * V) :=
            mul_le_mul_of_nonneg_left haux hcr2nn
        _ = 2 * (M1 / V) * ((∫ r in abox n ℓ, (cr r) ^ 2) * V) := by ring
    · rw [MeasureTheory.integral_undef hInt]
      exact mul_nonneg (mul_nonneg (by norm_num) hκnn)
        (setIntegral_nonneg (abox_measurable (n + 1) ℓ) (fun x _ => sq_nonneg _))

/-! ## 4. The exchange of the slot sum against the pair sum -/

/-- The hopping index set `hopPairSet i = {p ∈ disjPairs N | i ∈ p.1}` gives the exchange
`Σᵢ Σ_{p ∋ i} = Σ_p Σ_{i ∈ p.1}`. -/
theorem hopSwapSum {N : ℕ} (f : Finset (Fin N) × Finset (Fin N) → Fin N → ℝ) :
    (∑ i : Fin N, ∑ p ∈ hopPairSet i, f p i)
      = ∑ p ∈ Work.BoseFixB1.disjPairs N, ∑ i ∈ p.1, f p i := by
  simp only [hopPairSet, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp

/-! ## 5. The `P`-side supply -/

theorem hopPsideSupplyB1 {N : ℕ} {ℓ V : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hVeq : V = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {fib : EuclideanSpace ℝ (Fin 3) → ℝ} (hfibm : Measurable fib)
    (hfibnn : ∀ z ∈ A, 0 ≤ fib z)
    {M1 : ℝ} (hM1 : M1 = ∫ z in A, fib z)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) {μ : ℝ} (hμV : 0 ≤ μ * V) :
    (∑ i : Fin N, ∑ p ∈ Work.BoseFixB1S.hopPairSet i,
        ((p.1.card : ℝ) + 1 + μ * V)
          * (∫ x in Submission.BoseGases.abox N ℓ,
              (Work.BoseFixB1S.boxCompT V A p.1 p.2 Φ x) ^ 2 * |fib (x i) - M1 / V|))
      ≤ 2 * (M1 / V) *
          ((∑ p ∈ Work.BoseFixB1.disjPairs N, (p.1.card : ℝ) ^ 2 *
              ∫ x in Submission.BoseGases.abox N ℓ,
                (Work.BoseFixB1S.boxCompT V A p.1 p.2 Φ x) ^ 2)
            + (1 + μ * V) * (∑ p ∈ Work.BoseFixB1.disjPairs N, (p.1.card : ℝ) *
              ∫ x in Submission.BoseGases.abox N ℓ,
                (Work.BoseFixB1S.boxCompT V A p.1 p.2 Φ x) ^ 2)) := by
  cases N with
  | zero =>
    have hL : (∑ i : Fin 0, ∑ p ∈ hopPairSet i,
        ((p.1.card : ℝ) + 1 + μ * V)
          * (∫ x in abox 0 ℓ, (boxCompT V A p.1 p.2 Φ x) ^ 2 * |fib (x i) - M1 / V|)) = 0 :=
      Finset.sum_eq_zero fun i _ => Fin.elim0 i
    have hA2 : (∑ p ∈ Work.BoseFixB1.disjPairs 0, (p.1.card : ℝ) ^ 2 *
        ∫ x in abox 0 ℓ, (boxCompT V A p.1 p.2 Φ x) ^ 2) = 0 := by
      refine Finset.sum_eq_zero fun p hp => ?_
      have hp1 : p.1 = ∅ := Finset.eq_empty_iff_forall_notMem.mpr fun a _ => Fin.elim0 a
      simp [hp1]
    have hB2 : (∑ p ∈ Work.BoseFixB1.disjPairs 0, (p.1.card : ℝ) *
        ∫ x in abox 0 ℓ, (boxCompT V A p.1 p.2 Φ x) ^ 2) = 0 := by
      refine Finset.sum_eq_zero fun p hp => ?_
      have hp1 : p.1 = ∅ := Finset.eq_empty_iff_forall_notMem.mpr fun a _ => Fin.elim0 a
      simp [hp1]
    rw [hL, hA2, hB2]
    simp
  | succ n =>
    rw [hopSwapSum]
    calc
      (∑ p ∈ Work.BoseFixB1.disjPairs (n + 1), ∑ i ∈ p.1,
          ((p.1.card : ℝ) + 1 + μ * V)
            * (∫ x in abox (n + 1) ℓ,
                (boxCompT V A p.1 p.2 Φ x) ^ 2 * |fib (x i) - M1 / V|))
        ≤ ∑ p ∈ Work.BoseFixB1.disjPairs (n + 1), ∑ i ∈ p.1,
            ((p.1.card : ℝ) + 1 + μ * V)
              * (2 * (M1 / V) *
                (∫ x in abox (n + 1) ℓ, (boxCompT V A p.1 p.2 Φ x) ^ 2)) := by
          apply Finset.sum_le_sum
          intro p hp
          apply Finset.sum_le_sum
          intro i hi
          refine mul_le_mul_of_nonneg_left ?_ ?_
          · exact hopPsideInner_le hℓ hV hA hVeq hAc hfibm hfibnn hM1 hΦc i hi
          · have h1 : (0 : ℝ) ≤ (p.1.card : ℝ) := Nat.cast_nonneg _
            linarith [h1, hμV]
      _ = ∑ p ∈ Work.BoseFixB1.disjPairs (n + 1),
            2 * (M1 / V) * (((p.1.card : ℝ) ^ 2 *
                (∫ x in abox (n + 1) ℓ, (boxCompT V A p.1 p.2 Φ x) ^ 2))
              + (1 + μ * V) * ((p.1.card : ℝ) *
                (∫ x in abox (n + 1) ℓ, (boxCompT V A p.1 p.2 Φ x) ^ 2))) := by
          apply Finset.sum_congr rfl
          intro p hp
          rw [Finset.sum_const, nsmul_eq_mul]
          ring
      _ = 2 * (M1 / V) *
            ((∑ p ∈ Work.BoseFixB1.disjPairs (n + 1), (p.1.card : ℝ) ^ 2 *
                ∫ x in abox (n + 1) ℓ, (boxCompT V A p.1 p.2 Φ x) ^ 2)
              + (1 + μ * V) * (∑ p ∈ Work.BoseFixB1.disjPairs (n + 1), (p.1.card : ℝ) *
                ∫ x in abox (n + 1) ℓ, (boxCompT V A p.1 p.2 Φ x) ^ 2)) := by
          rw [← Finset.mul_sum]
          congr 1
          rw [Finset.sum_add_distrib, ← Finset.mul_sum]

end Work.BoseFixB1S
