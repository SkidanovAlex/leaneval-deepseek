import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.BoxTauGenMeasToolbox
import Submission.Work.BoseFixB1.boxOpG_adjoint_one
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.boxOpG_adjoint_one_meas` — the `h = 1` adjoint identity at measurable weights

The sibling `Work.BoseFixB1.boxOpG_adjoint_one` proves

  `∫ Φ·(boxOpG A f 1 Ψ) = ∫ (boxOpG A 1 f Φ)·Ψ`

for **continuous** slot functions `f` and **continuous** `Ψ`.  Here the same identity is proved
for merely measurable and bounded data:

* `f` measurable, globally bounded by `Cf` (`|f z| ≤ Cf` for all `z`);
* `Φ`, `Ψ` measurable, bounded only on the box `abox (N+1) a`.

The proof keeps the two per-slot peel computations `boxOpG_one_peel_createdSlot` /
`boxOpG_one_peel_integratedSlot` of `boxOpG_adjoint_one` verbatim — they are purely measure
theoretic modulo the `IntegrableOn` hypothesis — and replaces only the two *integrability* inputs
`boxOpG_one_integrableOn_createdSlot` / `boxOpG_one_integrableOn_integratedSlot` (which used
continuity to produce bounds) by the bounded-measurable route
`Work.BoseFixB1S.integrableOn_mul_of_bound` together with the fibre-mean bounds
`Work.BoseFixB1.abs_fibreMean_mul_le` and the unit-weight version `abs_fibreMean_one_le`.

## Main results
* `Work.BoseFixB1.abs_fibreMean_one_le` — the unit-weight fibre-mean bound;
* `Work.BoseFixB1.boxOpG_adjoint_one_meas` — the theorem.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- Boundedness of the unit-weight fibre mean on the box: for `x ∈ abox N ℓ`,

  `|∫_{z∈A} Ψ(x|i↦z) dz| ≤ max CΨ 0 · |A|`.

This is `Work.BoseFixB1.abs_fibreMean_mul_le` with the weight `h ≡ 1` and `1 * ·` collapsed. -/
theorem abs_fibreMean_one_le {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {A : Set E3} (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {Ψ : Submission.BoseGases.X N → ℝ} {CΨ : ℝ}
    (hΨb : ∀ x ∈ Submission.BoseGases.abox N ℓ, |Ψ x| ≤ CΨ)
    {x : Submission.BoseGases.X N} (hx : x ∈ Submission.BoseGases.abox N ℓ) (i : Fin N) :
    |∫ z in A, Ψ (Function.update x i z)|
      ≤ max CΨ 0 * (MeasureTheory.volume A).toReal := by
  have hfin : (MeasureTheory.volume : Measure E3) A < ⊤ :=
    Work.BoseFixB1S.volume_A_lt_top hℓ hAc
  have hb : ∀ z ∈ A, ‖Ψ (Function.update x i z)‖ ≤ max CΨ 0 := by
    intro z hz
    rw [Real.norm_eq_abs]
    exact le_trans (hΨb _ (Work.BoseFixB1.update_mem_abox_toolbox hAc hx i hz))
      (le_max_left _ _)
  have h := norm_setIntegral_le_of_norm_le_const (μ := (MeasureTheory.volume : Measure E3))
    (s := A) (f := fun z : E3 => Ψ (Function.update x i z)) (C := max CΨ 0) hfin hb
  rwa [Real.norm_eq_abs, MeasureTheory.Measure.real] at h

/-- **Integrability, created slot.**  The integrand with the box indicator and `f` in the created
slot `i` and the fibre mean of `Ψ` in the annihilated slot is integrable on the box, without any
continuity assumption on `f` or `Ψ`. -/
theorem boxOpG_one_meas_integrableOn_createdSlot {n : ℕ} {a : ℝ} (ha : 0 < a)
    {A : Set E3} (hAm : MeasurableSet A)
    (hAc : A ⊆ Submission.BoseGases.acube a)
    {f : E3 → ℝ} (hfm : Measurable f) {Cf : ℝ} (hfb : ∀ z, |f z| ≤ Cf)
    {Φ : Submission.BoseGases.X (n + 1) → ℝ} (hΦm : Measurable Φ) {CΦ : ℝ}
    (hΦb : ∀ x ∈ Submission.BoseGases.abox (n + 1) a, |Φ x| ≤ CΦ)
    {Ψ : Submission.BoseGases.X (n + 1) → ℝ} (hΨm : Measurable Ψ) {CΨ : ℝ}
    (hΨb : ∀ x ∈ Submission.BoseGases.abox (n + 1) a, |Ψ x| ≤ CΨ) (i : Fin (n + 1)) :
    MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X (n + 1) =>
        A.indicator (fun _ => (1 : ℝ)) (x i) * f (x i) * Φ x
          * (∫ z in A, Ψ (Function.update x i z)))
      (Submission.BoseGases.abox (n + 1) a) MeasureTheory.volume := by
  have hfibm : Measurable (fun x : Submission.BoseGases.X (n + 1) =>
      ∫ z in A, Ψ (Function.update x i z)) := by
    have h := Work.BoseFixB1.measurable_fibreMean_mul (A := A) hAm i
      (h := fun _ => (1 : ℝ)) measurable_const (Φ := Ψ) hΨm
    convert h using 1
    funext x
    apply MeasureTheory.integral_congr_ae
    filter_upwards with z
    simp
  have hgm : Measurable (fun x : Submission.BoseGases.X (n + 1) =>
      Φ x * ∫ z in A, Ψ (Function.update x i z)) := hΦm.mul hfibm
  have hfm' : Measurable (fun x : Submission.BoseGases.X (n + 1) =>
      A.indicator (fun _ => (1 : ℝ)) (x i) * f (x i)) :=
    ((measurable_const.indicator hAm).comp (measurable_pi_apply i)).mul
      (hfm.comp (measurable_pi_apply i))
  have h := Work.BoseFixB1S.integrableOn_mul_of_bound (N := n + 1) (ℓ := a) ha
    hfm' hgm
    (Cf := max Cf 0)
    (Cg := max CΦ 0 * (max CΨ 0 * (MeasureTheory.volume A).toReal))
    (by
      intro x hx
      rw [abs_mul]
      have h1 : |A.indicator (fun _ => (1 : ℝ)) (x i)| ≤ 1 := by
        by_cases hxi : x i ∈ A <;>
          simp [Set.indicator_of_mem, Set.indicator_of_notMem, hxi]
      simpa using mul_le_mul h1 (le_trans (hfb (x i)) (le_max_left Cf 0))
        (abs_nonneg _) zero_le_one)
    (by
      intro x hx
      rw [abs_mul]
      exact mul_le_mul (le_trans (hΦb x hx) (le_max_left CΦ 0))
        (Work.BoseFixB1.abs_fibreMean_one_le ha hAc hΨb hx i) (abs_nonneg _) (by positivity))
  refine h.congr ?_
  filter_upwards with x
  ring

/-- **Integrability, integrated slot.**  The integrand with the box indicator and `Ψ` in the slot
`i` and the fibre mean `∫ f z·Φ(·|i↦z)` in the annihilated slot is integrable on the box, without
any continuity assumption on `f` or `Φ`. -/
theorem boxOpG_one_meas_integrableOn_integratedSlot {n : ℕ} {a : ℝ} (ha : 0 < a)
    {A : Set E3} (hAm : MeasurableSet A)
    (hAc : A ⊆ Submission.BoseGases.acube a)
    {f : E3 → ℝ} (hfm : Measurable f) {Cf : ℝ} (hfb : ∀ z, |f z| ≤ Cf)
    {Φ : Submission.BoseGases.X (n + 1) → ℝ} (hΦm : Measurable Φ) {CΦ : ℝ}
    (hΦb : ∀ x ∈ Submission.BoseGases.abox (n + 1) a, |Φ x| ≤ CΦ)
    {Ψ : Submission.BoseGases.X (n + 1) → ℝ} (hΨm : Measurable Ψ) {CΨ : ℝ}
    (hΨb : ∀ x ∈ Submission.BoseGases.abox (n + 1) a, |Ψ x| ≤ CΨ) (i : Fin (n + 1)) :
    MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X (n + 1) =>
        A.indicator (fun _ => (1 : ℝ)) (x i) * Ψ x
          * (∫ z in A, f z * Φ (Function.update x i z)))
      (Submission.BoseGases.abox (n + 1) a) MeasureTheory.volume := by
  have hfibm : Measurable (fun x : Submission.BoseGases.X (n + 1) =>
      ∫ z in A, f z * Φ (Function.update x i z)) :=
    Work.BoseFixB1.measurable_fibreMean_mul (A := A) hAm i hfm hΦm
  have hfm' : Measurable (fun x : Submission.BoseGases.X (n + 1) =>
      A.indicator (fun _ => (1 : ℝ)) (x i) * Ψ x) :=
    ((measurable_const.indicator hAm).comp (measurable_pi_apply i)).mul hΨm
  have h := Work.BoseFixB1S.integrableOn_mul_of_bound (N := n + 1) (ℓ := a) ha
    hfm' hfibm
    (Cf := max CΨ 0)
    (Cg := max Cf 0 * (max CΦ 0 * (MeasureTheory.volume A).toReal))
    (by
      intro x hx
      rw [abs_mul]
      have h1 : |A.indicator (fun _ => (1 : ℝ)) (x i)| ≤ 1 := by
        by_cases hxi : x i ∈ A <;>
          simp [Set.indicator_of_mem, Set.indicator_of_notMem, hxi]
      simpa using mul_le_mul h1 (le_trans (hΨb x hx) (le_max_left CΨ 0))
        (abs_nonneg _) zero_le_one)
    (by
      intro x hx
      simpa only [mul_assoc] using
        Work.BoseFixB1.abs_fibreMean_mul_le (N := n + 1) ha hAc hfb hΦb hx i)
  refine h.congr ?_
  filter_upwards with x
  ring

theorem boxOpG_adjoint_one_meas {N : ℕ} {a : ℝ} (ha : 0 < a)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hAm : MeasurableSet A)
    (hAc : A ⊆ Submission.BoseGases.acube a)
    {f : EuclideanSpace ℝ (Fin 3) → ℝ} (hfm : Measurable f) {Cf : ℝ} (hfb : ∀ z, |f z| ≤ Cf)
    {Φ Ψ : Submission.BoseGases.X (N + 1) → ℝ} (hΦm : Measurable Φ) (hΨm : Measurable Ψ)
    {CΦ CΨ : ℝ}
    (hΦb : ∀ x ∈ Submission.BoseGases.abox (N + 1) a, |Φ x| ≤ CΦ)
    (hΨb : ∀ x ∈ Submission.BoseGases.abox (N + 1) a, |Ψ x| ≤ CΨ) :
    (∫ x in Submission.BoseGases.abox (N + 1) a,
        Φ x * Work.BoseFixB1.boxOpG A f (fun _ => (1 : ℝ)) Ψ x)
      = ∫ x in Submission.BoseGases.abox (N + 1) a,
          Work.BoseFixB1.boxOpG A (fun _ => (1 : ℝ)) f Φ x * Ψ x := by
  have hLint : ∀ i : Fin (N + 1), MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X (N + 1) =>
        A.indicator (fun _ => (1 : ℝ)) (x i) * f (x i) * Φ x
          * (∫ z in A, Ψ (Function.update x i z)))
      (Submission.BoseGases.abox (N + 1) a) MeasureTheory.volume :=
    fun i => boxOpG_one_meas_integrableOn_createdSlot ha hAm hAc hfm hfb hΦm hΦb hΨm hΨb i
  have hRint : ∀ i : Fin (N + 1), MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X (N + 1) =>
        A.indicator (fun _ => (1 : ℝ)) (x i) * Ψ x
          * (∫ z in A, f z * Φ (Function.update x i z)))
      (Submission.BoseGases.abox (N + 1) a) MeasureTheory.volume :=
    fun i => boxOpG_one_meas_integrableOn_integratedSlot ha hAm hAc hfm hfb hΦm hΦb hΨm hΨb i
  have hL : (∫ x in Submission.BoseGases.abox (N + 1) a,
        Φ x * Work.BoseFixB1.boxOpG A f (fun _ => (1 : ℝ)) Ψ x)
      = ∑ i : Fin (N + 1), ∫ r in Submission.BoseGases.abox N a,
          (∫ y in A, f y * Φ (Submission.BoseGases.kcInsN N i (y, r)))
            * (∫ z in A, Ψ (Submission.BoseGases.kcInsN N i (z, r))) := by
    have hpt : (fun x : Submission.BoseGases.X (N + 1) =>
          Φ x * Work.BoseFixB1.boxOpG A f (fun _ => (1 : ℝ)) Ψ x)
        = fun x : Submission.BoseGases.X (N + 1) =>
          ∑ i : Fin (N + 1), (A.indicator (fun _ => (1 : ℝ)) (x i) * f (x i) * Φ x
            * (∫ z in A, Ψ (Function.update x i z))) := by
      funext x
      rw [Work.BoseFixB1.boxOpG]
      have hinner : ∀ i : Fin (N + 1),
          (∫ z in A, (fun _ => (1 : ℝ)) z * Ψ (Function.update x i z))
            = ∫ z in A, Ψ (Function.update x i z) := by
        intro i
        apply MeasureTheory.integral_congr_ae
        filter_upwards with z
        simp
      simp only [hinner]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      ring
    rw [hpt]
    rw [MeasureTheory.integral_finsetSum (s := Finset.univ)
      (f := fun (i : Fin (N + 1)) (x : Submission.BoseGases.X (N + 1)) =>
        A.indicator (fun _ => (1 : ℝ)) (x i) * f (x i) * Φ x
          * (∫ z in A, Ψ (Function.update x i z)))
      (fun i _ => hLint i)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    exact Work.BoseFixB1.boxOpG_one_peel_createdSlot hAm hAc i (hLint i)
  have hR : (∫ x in Submission.BoseGases.abox (N + 1) a,
        Work.BoseFixB1.boxOpG A (fun _ => (1 : ℝ)) f Φ x * Ψ x)
      = ∑ i : Fin (N + 1), ∫ r in Submission.BoseGases.abox N a,
          (∫ y in A, Ψ (Submission.BoseGases.kcInsN N i (y, r)))
            * (∫ z in A, f z * Φ (Submission.BoseGases.kcInsN N i (z, r))) := by
    have hpt : (fun x : Submission.BoseGases.X (N + 1) =>
          Work.BoseFixB1.boxOpG A (fun _ => (1 : ℝ)) f Φ x * Ψ x)
        = fun x : Submission.BoseGases.X (N + 1) =>
          ∑ i : Fin (N + 1), (A.indicator (fun _ => (1 : ℝ)) (x i) * Ψ x
            * (∫ z in A, f z * Φ (Function.update x i z))) := by
      funext x
      rw [Work.BoseFixB1.boxOpG, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      simp only [mul_one]
      ring
    rw [hpt]
    rw [MeasureTheory.integral_finsetSum (s := Finset.univ)
      (f := fun (i : Fin (N + 1)) (x : Submission.BoseGases.X (N + 1)) =>
        A.indicator (fun _ => (1 : ℝ)) (x i) * Ψ x
          * (∫ z in A, f z * Φ (Function.update x i z)))
      (fun i _ => hRint i)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    exact Work.BoseFixB1.boxOpG_one_peel_integratedSlot hAm hAc i (hRint i)
  rw [hL, hR]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  apply MeasureTheory.integral_congr_ae
  filter_upwards with r
  exact mul_comm _ _

end Work.BoseFixB1
