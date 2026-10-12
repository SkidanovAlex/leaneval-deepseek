import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixR.KinGePDiag
import Submission.Work.BoseKinLoc.Momentum.memLp_kinFT
import Submission.Work.SlotWord.measurable_boxQInd
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.tBamp_rPart_bound`

The `r`-part bound for the window-transfer decomposition of the FS-faithful `p`-diagonal kinetic
form.  For a bounded a.e.-measurable window perturbation `rr` (`|rr z| ≤ ρ`) and the FS box
projection `Q_{B,i} = boxQInd volA A i Ψ`, the `p`-space density of the `rr`-part of the slot-`i`
amplitude satisfies

  `∫_p (a³)⁻¹ ∫_{abox (N+1) a} ‖tBamp rr p (Q_{B,i}Ψ) i x‖² ≤ (2π)³ ρ² ⌠_r ⌠_z (Q_{B,i}Ψ)²`

and the left-hand integrand is integrable in `p`.

## The mathematics

The `z`-integral defining `tBamp` is a windowed Fourier transform; by Plancherel
(`Work.BoseKinLoc.Kinetic.kinFT_sq_of_memLp`) the `p`-integral of its squared modulus is `(2π)³`
times the squared `L²`-norm of the fibre `z ↦ rr z · Q_{B,i}Ψ (x_{i←z})`.  The slot-`i`
coordinate of `x` is integrated over, so the ambient box integral peels to a `∫_r` over
`abox N a` of the fibre at the inserted configuration `kcInsN N i (z, r)`; the bound `|rr| ≤ ρ`
then gives the stated `ρ²`.

## Structure

* §1 the peels of the slot-`i` coordinate (`peel_slot_abox_indep`, `tBamp_kcInsN_eq_kinFT`);
* §2 the inserted fibre `rFibre` and the pointwise bound `|Q_{B,i}Ψ| ≤ Cq·1_A`;
* §3 joint measurability of the peeled amplitude in `(p, r)`;
* §4 the `L¹`/`L²` facts of the fibre and Plancherel;
* §5 measurability/integrability of the `r`-side and the assembly.
-/

namespace Work.BoseFixB1S

open MeasureTheory Filter
open scoped Topology Real BigOperators ENNReal

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "XX" => Submission.BoseGases.X

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-! ## 1. Slot peels -/

/-- The windowed slot amplitude at an inserted configuration, as an explicit Bochner integral
over the whole space. -/
lemma tBamp_kcInsN_eq_integral {N : ℕ} (χ : E3 → ℝ) (p : E3) {Φ : XX (N + 1) → ℝ}
    (i : Fin (N + 1)) (r : XX N) :
    Work.SmallBoxTBWord.tBamp χ p Φ i (Submission.BoseGases.kcInsN N i ((0 : E3), r))
      = ∫ z : E3, (χ z : ℂ) * Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
          (Φ (Submission.BoseGases.kcInsN N i (z, r)) : ℂ) := by
  rw [Work.SmallBoxTBWord.tBamp]
  refine integral_congr_ae (Eventually.of_forall (fun z => ?_))
  show (χ z : ℂ) * Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
      (Φ (Function.update (Submission.BoseGases.kcInsN N i ((0 : E3), r)) i z) : ℂ)
    = (χ z : ℂ) * Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
      (Φ (Submission.BoseGases.kcInsN N i (z, r)) : ℂ)
  rw [Work.SmallBoxBridge.Fourier.update_kcInsN]

/-- Inserting a point of `A` into the slot `i` of a box configuration stays in the box. -/
lemma kcInsN_mem_abox {N : ℕ} {a : ℝ} {A : Set E3} (hAc : A ⊆ Submission.BoseGases.acube a)
    (i : Fin (N + 1)) {z : E3} (hz : z ∈ A) {r : XX N}
    (hr : r ∈ Submission.BoseGases.abox N a) :
    Submission.BoseGases.kcInsN N i (z, r) ∈ Submission.BoseGases.abox (N + 1) a := by
  rw [Submission.BoseGases.mem_abox_iff] at hr ⊢
  intro j
  by_cases hj : j = i
  · subst hj
    rw [Submission.BoseGases.kc_insN_apply_same]
    exact hAc hz
  · rcases Fin.exists_succAbove_eq hj with ⟨j', rfl⟩
    rw [Submission.BoseGases.kc_insN_apply_succ]
    exact hr j'

/-- **The slot peel**: because the amplitude does not depend on the slot-`i` coordinate of `x`,
the ambient box integral factorises, the peeled slot contributing the volume factor `a³`. -/
lemma slotDens_peel {N : ℕ} {a : ℝ} (ha : 0 < a) (i : Fin (N + 1)) (χ : E3 → ℝ) (p : E3)
    {Φ : XX (N + 1) → ℝ} :
    (a ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox (N + 1) a,
        ‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2
      = ∫ r in Submission.BoseGases.abox N a,
          ‖Submission.BoseGases.kinFT (fun z : E3 =>
            (χ z : ℂ) * (Φ (Submission.BoseGases.kcInsN N i (z, r)) : ℂ)) p‖ ^ 2 := by
  have hind : ∀ (r : XX N) (y y' : E3),
      (fun x : XX (N + 1) => ‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2)
          (Submission.BoseGases.kcInsN N i (y, r))
        = (fun x : XX (N + 1) => ‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2)
          (Submission.BoseGases.kcInsN N i (y', r)) := by
    intro r y y'
    show ‖Work.SmallBoxTBWord.tBamp χ p Φ i (Submission.BoseGases.kcInsN N i (y, r))‖ ^ 2
      = ‖Work.SmallBoxTBWord.tBamp χ p Φ i (Submission.BoseGases.kcInsN N i (y', r))‖ ^ 2
    rw [Work.SmallBoxTBWord.tBamp_kcInsN_indep i p r y y']
  rw [Work.BoseFixR.peel_slot_abox_indep (m := N) (ℓ := a) ha i hind]
  exact integral_congr_ae (Eventually.of_forall (fun r => by
    show ‖Work.SmallBoxTBWord.tBamp χ p Φ i
        (Submission.BoseGases.kcInsN N i ((0 : E3), r))‖ ^ 2
      = ‖Submission.BoseGases.kinFT (fun z : E3 =>
          (χ z : ℂ) * (Φ (Submission.BoseGases.kcInsN N i (z, r)) : ℂ)) p‖ ^ 2
    rw [Work.SmallBoxTBWord.tBamp_kcInsN_eq_kinFT]))

/-! ## 2. The inserted fibre and the box-projection bound -/

/-- The windowed inserted fibre: the function of the slot-`i` variable whose `p`-Fourier
transform is the slot-`i` amplitude at the configuration `kcInsN N i (·, r)`. -/
noncomputable def rFibre (χ : E3 → ℝ) (volA : ℝ) (A : Set E3) {N : ℕ}
    (Ψ : XX (N + 1) → ℝ) (i : Fin (N + 1)) (r : XX N) : E3 → ℂ :=
  fun z => (χ z : ℂ) * ((Work.UBBInputs8.boxQInd volA A i Ψ
    (Submission.BoseGases.kcInsN N i (z, r))) : ℂ)

/-- The peel in the `rFibre` notation, specialised to `Q_{B,i}Ψ`. -/
lemma slotDens_peel_boxQInd {N : ℕ} {a volA : ℝ} (ha : 0 < a) {A : Set E3}
    (i : Fin (N + 1)) (χ : E3 → ℝ) (p : E3) {Ψ : XX (N + 1) → ℝ} :
    (a ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox (N + 1) a,
        ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA A i Ψ) i x‖ ^ 2
      = ∫ r in Submission.BoseGases.abox N a,
          ‖Submission.BoseGases.kinFT (rFibre χ volA A Ψ i r) p‖ ^ 2 := by
  rw [slotDens_peel ha i χ p]
  rfl

/-- A continuous function is bounded on the (compact) box. -/
lemma exists_abs_bound_abox {N : ℕ} {a : ℝ} (ha : 0 < a) {Ψ : XX (N + 1) → ℝ}
    (hΨ : Continuous Ψ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ Submission.BoseGases.abox (N + 1) a, |Ψ x| ≤ M := by
  obtain ⟨C, hC⟩ := (Submission.BoseGases.abox_compact (N + 1) ha).exists_bound_of_continuousOn
    hΨ.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun x hx => ?_⟩
  have h := hC x hx
  rw [Real.norm_eq_abs] at h
  exact le_trans h (le_max_left _ _)

/-- **The FS box projection is bounded by a constant times the box indicator.**  Both terms of
`Q_{B,i}Ψ = 1_A(x_i)·Ψ − |A|⁻¹(∫_A Ψ(x_{i←z})dz)·1_A(x_i)` carry the indicator of `A` in the
slot `i`; on `A` the state is bounded by its sup over the box. -/
lemma boxQInd_indicator_bound {N : ℕ} {a volA : ℝ} (ha : 0 < a) (hvolpos : 0 < volA)
    {A : Set E3} (hAc : A ⊆ Submission.BoseGases.acube a)
    (hvolA : volA = (volume A).toReal)
    {Ψ : XX (N + 1) → ℝ} (hΨc : Continuous Ψ) (i : Fin (N + 1)) :
    ∃ Cq : ℝ, 0 ≤ Cq ∧ ∀ (z : E3) (r : XX N), r ∈ Submission.BoseGases.abox N a →
      |Work.UBBInputs8.boxQInd volA A i Ψ (Submission.BoseGases.kcInsN N i (z, r))|
        ≤ Cq * A.indicator (fun _ => (1 : ℝ)) z := by
  obtain ⟨M, hM0, hM⟩ := exists_abs_bound_abox (N := N) ha hΨc
  refine ⟨2 * M, by linarith, fun z r hr => ?_⟩
  have hzi : (Submission.BoseGases.kcInsN N i (z, r)) i = z :=
    Submission.BoseGases.kc_insN_apply_same N i z r
  rw [Work.UBBInputs8.boxQInd, Work.UBBInputs8.boxPInd, hzi]
  by_cases hz : z ∈ A
  · rw [Set.indicator_of_mem hz, one_mul, mul_one]
    have h1 : |Ψ (Submission.BoseGases.kcInsN N i (z, r))| ≤ M :=
      hM _ (kcInsN_mem_abox hAc i hz hr)
    have h2 : |(1 / volA) * ∫ w in A,
        Ψ (Function.update (Submission.BoseGases.kcInsN N i (z, r)) i w)| ≤ M := by
      rw [show (fun w => Ψ (Function.update (Submission.BoseGases.kcInsN N i (z, r)) i w))
            = (fun w => Ψ (Submission.BoseGases.kcInsN N i (w, r))) from by
          funext w; rw [Work.SmallBoxBridge.Fourier.update_kcInsN]]
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / volA)]
      have hbound : ∀ w ∈ A, ‖Ψ (Submission.BoseGases.kcInsN N i (w, r))‖ ≤ M := by
        intro w hw
        simpa only [Real.norm_eq_abs] using hM _ (kcInsN_mem_abox hAc i hw hr)
      have hfin : (volume : Measure E3) A < ⊤ :=
        lt_of_le_of_lt (measure_mono hAc)
          (by rw [Submission.BoseGases.acube_volume a ha.le]; exact ENNReal.ofReal_lt_top)
      have hnorm := MeasureTheory.norm_setIntegral_le_of_norm_le_const (μ := volume) (s := A)
        (f := fun w => Ψ (Submission.BoseGases.kcInsN N i (w, r))) (C := M) hfin hbound
      rw [MeasureTheory.Measure.real_def, ← hvolA, Real.norm_eq_abs] at hnorm
      calc (1 / volA) * |∫ w in A, Ψ (Submission.BoseGases.kcInsN N i (w, r))|
          ≤ (1 / volA) * (M * volA) := mul_le_mul_of_nonneg_left hnorm (by positivity)
        _ = M := by field_simp
    calc |Ψ (Submission.BoseGases.kcInsN N i (z, r)) - (1 / volA) *
          ∫ w in A, Ψ (Function.update (Submission.BoseGases.kcInsN N i (z, r)) i w)|
        ≤ |Ψ (Submission.BoseGases.kcInsN N i (z, r))| + |(1 / volA) *
          ∫ w in A, Ψ (Function.update (Submission.BoseGases.kcInsN N i (z, r)) i w)| :=
          abs_sub _ _
      _ ≤ M + M := add_le_add h1 h2
      _ = 2 * M * 1 := by ring
  · rw [Set.indicator_of_notMem hz]
    simp

/-! ## 3. Joint measurability of the peeled amplitude -/

/-- **Joint a.e.-strong measurability of the peeled amplitude.** -/
lemma aestronglyMeasurable_pair_kinFT {N : ℕ} {a volA : ℝ} {A : Set E3} (hAcm : MeasurableSet A)
    {Ψ : XX (N + 1) → ℝ} (hΨm : Measurable Ψ) (i : Fin (N + 1)) {χ : E3 → ℝ}
    (hχ : AEStronglyMeasurable χ volume) :
    AEStronglyMeasurable
      (Function.uncurry (fun (p : E3) (r : XX N) =>
        ‖Submission.BoseGases.kinFT (rFibre χ volA A Ψ i r) p‖ ^ 2))
      ((volume : Measure E3).prod
        ((volume : Measure (XX N)).restrict (Submission.BoseGases.abox N a))) := by
  have hχz : AEStronglyMeasurable (fun q : (E3 × XX N) × E3 => (χ q.2 : ℂ))
      (((volume : Measure E3).prod
        ((volume : Measure (XX N)).restrict (Submission.BoseGases.abox N a))).prod volume) :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable
      (hχ.comp_quasiMeasurePreserving MeasureTheory.Measure.quasiMeasurePreserving_snd)
  have hQm : Measurable (fun q : (E3 × XX N) × E3 =>
      Work.UBBInputs8.boxQInd volA A i Ψ (Submission.BoseGases.kcInsN N i (q.2, q.1.2))) :=
    (Work.SlotWord.measurable_boxQInd volA A hAcm i hΨm).comp
      ((Submission.BoseGases.kcInsN_cont i).measurable.comp (by fun_prop))
  have hQz : AEStronglyMeasurable (fun q : (E3 × XX N) × E3 =>
      ((Work.UBBInputs8.boxQInd volA A i Ψ
        (Submission.BoseGases.kcInsN N i (q.2, q.1.2))) : ℂ))
      (((volume : Measure E3).prod
        ((volume : Measure (XX N)).restrict (Submission.BoseGases.abox N a))).prod volume) :=
    (Complex.continuous_ofReal.measurable.comp hQm).aestronglyMeasurable
  have hexp : AEStronglyMeasurable (fun q : (E3 × XX N) × E3 =>
      Complex.exp (-(Complex.I * (inner ℝ q.1.1 q.2 : ℂ))))
      (((volume : Measure E3).prod
        ((volume : Measure (XX N)).restrict (Submission.BoseGases.abox N a))).prod volume) :=
    (by fun_prop : Continuous (fun q : (E3 × XX N) × E3 =>
      Complex.exp (-(Complex.I * (inner ℝ q.1.1 q.2 : ℂ))))).aestronglyMeasurable
  have hf : AEStronglyMeasurable (fun q : (E3 × XX N) × E3 =>
      Complex.exp (-(Complex.I * (inner ℝ q.1.1 q.2 : ℂ))) *
        ((χ q.2 : ℂ) * ((Work.UBBInputs8.boxQInd volA A i Ψ
          (Submission.BoseGases.kcInsN N i (q.2, q.1.2))) : ℂ)))
      (((volume : Measure E3).prod
        ((volume : Measure (XX N)).restrict (Submission.BoseGases.abox N a))).prod volume) :=
    hexp.mul (hχz.mul hQz)
  have h := AEStronglyMeasurable.integral_prod_right'
    (μ := (volume : Measure E3).prod
      ((volume : Measure (XX N)).restrict (Submission.BoseGases.abox N a)))
    (ν := (volume : Measure E3)) hf
  refine (h.norm.pow 2).congr ?_
  filter_upwards with q
  obtain ⟨p, r⟩ := q
  rfl

/-! ## 4. `L¹`/`L²` of the fibre and Plancherel -/

/-- A function bounded by a constant on a finite-measure set (and vanishing outside) is in
`L¹ ∩ L²`. -/
lemma memLp_of_norm_le_indicator {s : Set E3} (hs : MeasurableSet s)
    (hfin : (volume : Measure E3) s < ⊤) {f : E3 → ℂ} (hfm : AEStronglyMeasurable f volume)
    {c : ℝ} (hc : 0 ≤ c) (hb : ∀ z, ‖f z‖ ≤ c * s.indicator (fun _ => (1 : ℝ)) z) :
    MemLp f 1 volume ∧ MemLp f 2 volume := by
  have hind : Integrable (s.indicator (fun _ => (1 : ℝ))) volume := by
    rw [MeasureTheory.integrable_indicator_iff hs]
    exact MeasureTheory.integrable_const_iff.mpr
      (Or.inr (MeasureTheory.isFiniteMeasure_restrict.mpr (ne_of_lt hfin)))
  have hg1 : Integrable (fun z : E3 => c * s.indicator (fun _ => (1 : ℝ)) z) volume :=
    hind.const_mul c
  have hg2 : Integrable (fun z : E3 => c ^ 2 * s.indicator (fun _ => (1 : ℝ)) z) volume :=
    hind.const_mul (c ^ 2)
  have hi1 : Integrable f volume := Integrable.mono' hg1 hfm (Eventually.of_forall hb)
  have hsq : ∀ z, ‖f z‖ ^ 2 ≤ c ^ 2 * s.indicator (fun _ => (1 : ℝ)) z := by
    intro z
    by_cases hz : z ∈ s
    · have hb' : ‖f z‖ ≤ c := by simpa [Set.indicator_of_mem hz] using hb z
      rw [Set.indicator_of_mem hz, mul_one]
      exact pow_le_pow_left₀ (norm_nonneg _) hb' 2
    · have h' : ‖f z‖ ≤ 0 := by
        have h2 := hb z
        rw [Set.indicator_of_notMem hz, mul_zero] at h2
        exact h2
      have h0 : ‖f z‖ = 0 := le_antisymm h' (norm_nonneg _)
      rw [Set.indicator_of_notMem hz, h0]
      simp
  have hi2 : Integrable (fun z => ‖f z‖ ^ 2) volume :=
    Integrable.mono' hg2 (hfm.norm.pow 2) (Eventually.of_forall (fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hsq z))
  exact ⟨MeasureTheory.memLp_one_iff_integrable.mpr hi1,
    (MeasureTheory.memLp_two_iff_integrable_sq_norm hfm).mpr hi2⟩

/-- `MemLp` of the inserted fibre, from the pointwise indicator bound on `Q_{B,i}Ψ`. -/
lemma memLp_rFibre {N : ℕ} {a volA Cq ρ : ℝ} {A : Set E3} (hAcm : MeasurableSet A)
    (hAfin : (volume : Measure E3) A < ⊤) {Ψ : XX (N + 1) → ℝ} (hΨm : Measurable Ψ)
    (i : Fin (N + 1)) {χ : E3 → ℝ} (hχm : AEStronglyMeasurable χ volume) (hCq0 : 0 ≤ Cq)
    (hρ0 : 0 ≤ ρ) (hrb : ∀ z, |χ z| ≤ ρ)
    (hQ : ∀ (z : E3) (r : XX N), r ∈ Submission.BoseGases.abox N a →
      |Work.UBBInputs8.boxQInd volA A i Ψ (Submission.BoseGases.kcInsN N i (z, r))|
        ≤ Cq * A.indicator (fun _ => (1 : ℝ)) z)
    {r : XX N} (hr : r ∈ Submission.BoseGases.abox N a) :
    MemLp (rFibre χ volA A Ψ i r) 1 volume ∧ MemLp (rFibre χ volA A Ψ i r) 2 volume := by
  have hfm : AEStronglyMeasurable (rFibre χ volA A Ψ i r) volume := by
    have hQm : Measurable (fun z : E3 => Work.UBBInputs8.boxQInd volA A i Ψ
        (Submission.BoseGases.kcInsN N i (z, r))) :=
      (Work.SlotWord.measurable_boxQInd volA A hAcm i hΨm).comp (by fun_prop)
    exact (Complex.continuous_ofReal.comp_aestronglyMeasurable hχm).mul
      (Complex.continuous_ofReal.comp_aestronglyMeasurable hQm.aestronglyMeasurable)
  refine memLp_of_norm_le_indicator hAcm hAfin hfm (mul_nonneg hρ0 hCq0) (fun z => ?_)
  rw [rFibre, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
  calc |χ z| * |Work.UBBInputs8.boxQInd volA A i Ψ (Submission.BoseGases.kcInsN N i (z, r))|
      ≤ ρ * (Cq * A.indicator (fun _ => (1 : ℝ)) z) :=
        mul_le_mul (hrb z) (hQ z r hr) (abs_nonneg _) hρ0
    _ = (ρ * Cq) * A.indicator (fun _ => (1 : ℝ)) z := by ring

/-- **Plancherel in the `p`-convention.** -/
lemma integral_kinFT_sq_eq {F : E3 → ℂ} (h1 : MemLp F 1 volume) (h2 : MemLp F 2 volume) :
    Integrable (fun p : E3 => ‖Submission.BoseGases.kinFT F p‖ ^ 2) volume
      ∧ (∫ p : E3, ‖Submission.BoseGases.kinFT F p‖ ^ 2)
          = (2 * Real.pi) ^ 3 * ∫ z : E3, ‖F z‖ ^ 2 := by
  obtain ⟨hi, heq⟩ := Work.BoseKinLoc.Kinetic.kinFT_sq_of_memLp h1 h2
  refine ⟨hi, ?_⟩
  have hne : ((2 * Real.pi) ^ 3 : ℝ) ≠ 0 := by positivity
  calc ∫ p : E3, ‖Submission.BoseGases.kinFT F p‖ ^ 2
      = (2 * Real.pi) ^ 3 * (((2 * Real.pi) ^ 3)⁻¹ *
          ∫ p : E3, ‖Submission.BoseGases.kinFT F p‖ ^ 2) := by
        rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul]
    _ = (2 * Real.pi) ^ 3 * ∫ z : E3, ‖F z‖ ^ 2 := by rw [heq]

/-- The squared modulus of an indicator-bounded real function: integrability and the explicit
`c²·|A|` bound. -/
lemma integrable_sq_of_abs_le_indicator {A : Set E3} {volA : ℝ} (hAcm : MeasurableSet A)
    (hAfin : (volume : Measure E3) A < ⊤) (hvolA : volA = (volume A).toReal)
    {f : E3 → ℝ} (hfm : AEStronglyMeasurable f volume) {c : ℝ} (hc : 0 ≤ c)
    (hf : ∀ z, |f z| ≤ c * A.indicator (fun _ => (1 : ℝ)) z) :
    Integrable (fun z => f z ^ 2) volume ∧ ∫ z, f z ^ 2 ≤ c ^ 2 * volA := by
  have hg : Integrable (fun z : E3 => (c ^ 2) * A.indicator (fun _ => (1 : ℝ)) z) volume := by
    have h1 : Integrable (A.indicator (fun _ => (1 : ℝ))) volume := by
      rw [MeasureTheory.integrable_indicator_iff hAcm]
      exact MeasureTheory.integrable_const_iff.mpr
        (Or.inr (MeasureTheory.isFiniteMeasure_restrict.mpr (ne_of_lt hAfin)))
    exact h1.const_mul (c ^ 2)
  have hpt : ∀ z : E3, f z ^ 2 ≤ (c ^ 2) * A.indicator (fun _ => (1 : ℝ)) z := by
    intro z
    have hsq : f z ^ 2 ≤ (c * A.indicator (fun _ => (1 : ℝ)) z) ^ 2 := by
      rw [← sq_abs (f z)]
      exact pow_le_pow_left₀ (abs_nonneg _) (hf z) 2
    have hle : (c * A.indicator (fun _ => (1 : ℝ)) z) ^ 2
        ≤ (c ^ 2) * A.indicator (fun _ => (1 : ℝ)) z := by
      by_cases hz : z ∈ A
      · simp [Set.indicator_of_mem hz]
      · simp [Set.indicator_of_notMem hz]
    exact le_trans hsq hle
  have hf2 : Integrable (fun z => f z ^ 2) volume :=
    Integrable.mono' hg (hfm.pow 2) (Eventually.of_forall (fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hpt z))
  refine ⟨hf2, ?_⟩
  calc ∫ z, f z ^ 2 ≤ ∫ z, (c ^ 2) * A.indicator (fun _ => (1 : ℝ)) z :=
        integral_mono hf2 hg hpt
    _ = c ^ 2 * volA := by
        rw [MeasureTheory.integral_const_mul,
          MeasureTheory.integral_indicator_const (1 : ℝ) hAcm, smul_eq_mul, mul_one,
          MeasureTheory.Measure.real_def, ← hvolA]

/-- The `z`-bound: the squared `L²` norm of the inserted fibre is at most `ρ²` times the
unweighted inserted square integral. -/
lemma integral_normSq_rFibre_le {N : ℕ} {a volA Cq ρ : ℝ} {A : Set E3} (hAcm : MeasurableSet A)
    (hAfin : (volume : Measure E3) A < ⊤) (hvolA : volA = (volume A).toReal)
    {Ψ : XX (N + 1) → ℝ} (hΨm : Measurable Ψ) (i : Fin (N + 1)) {χ : E3 → ℝ}
    (hχm : AEStronglyMeasurable χ volume) (hCq0 : 0 ≤ Cq) (hρ0 : 0 ≤ ρ)
    (hrb : ∀ z, |χ z| ≤ ρ)
    (hQ : ∀ (z : E3) (r : XX N), r ∈ Submission.BoseGases.abox N a →
      |Work.UBBInputs8.boxQInd volA A i Ψ (Submission.BoseGases.kcInsN N i (z, r))|
        ≤ Cq * A.indicator (fun _ => (1 : ℝ)) z)
    {r : XX N} (hr : r ∈ Submission.BoseGases.abox N a) :
    (∫ z : E3, ‖rFibre χ volA A Ψ i r z‖ ^ 2)
      ≤ ρ ^ 2 * ∫ z : E3,
          (Work.UBBInputs8.boxQInd volA A i Ψ (Submission.BoseGases.kcInsN N i (z, r))) ^ 2 := by
  obtain ⟨hm1, hm2⟩ := memLp_rFibre hAcm hAfin hΨm i hχm hCq0 hρ0 hrb hQ hr
  have hfm : AEStronglyMeasurable (rFibre χ volA A Ψ i r) volume := by
    have hQm : Measurable (fun z : E3 => Work.UBBInputs8.boxQInd volA A i Ψ
        (Submission.BoseGases.kcInsN N i (z, r))) :=
      (Work.SlotWord.measurable_boxQInd volA A hAcm i hΨm).comp (by fun_prop)
    exact (Complex.continuous_ofReal.comp_aestronglyMeasurable hχm).mul
      (Complex.continuous_ofReal.comp_aestronglyMeasurable hQm.aestronglyMeasurable)
  have hint1 : Integrable (fun z => ‖rFibre χ volA A Ψ i r z‖ ^ 2) volume :=
    (MeasureTheory.memLp_two_iff_integrable_sq_norm hfm).mp hm2
  have hint2 : Integrable (fun z : E3 => ρ ^ 2 *
      (Work.UBBInputs8.boxQInd volA A i Ψ (Submission.BoseGases.kcInsN N i (z, r))) ^ 2)
      volume :=
    ((integrable_sq_of_abs_le_indicator hAcm hAfin hvolA
      ((Work.SlotWord.measurable_boxQInd volA A hAcm i hΨm).comp (by fun_prop)).aestronglyMeasurable
      hCq0 (fun z => hQ z r hr)).1).const_mul (ρ ^ 2)
  have hmono : (∫ z : E3, ‖rFibre χ volA A Ψ i r z‖ ^ 2)
      ≤ ∫ z : E3, ρ ^ 2 * (Work.UBBInputs8.boxQInd volA A i Ψ
          (Submission.BoseGases.kcInsN N i (z, r))) ^ 2 := by
    refine integral_mono hint1 hint2 (fun z => ?_)
    have hχ2 : χ z ^ 2 ≤ ρ ^ 2 := by
      rw [← sq_abs (χ z)]
      exact pow_le_pow_left₀ (abs_nonneg _) (hrb z) 2
    calc ‖rFibre χ volA A Ψ i r z‖ ^ 2
        = χ z ^ 2 * (Work.UBBInputs8.boxQInd volA A i Ψ
            (Submission.BoseGases.kcInsN N i (z, r))) ^ 2 := by
          rw [rFibre, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
            Real.norm_eq_abs, mul_pow, sq_abs, sq_abs]
      _ ≤ ρ ^ 2 * (Work.UBBInputs8.boxQInd volA A i Ψ
            (Submission.BoseGases.kcInsN N i (z, r))) ^ 2 :=
          mul_le_mul_of_nonneg_right hχ2 (sq_nonneg _)
  calc (∫ z : E3, ‖rFibre χ volA A Ψ i r z‖ ^ 2)
      ≤ ∫ z : E3, ρ ^ 2 * (Work.UBBInputs8.boxQInd volA A i Ψ
          (Submission.BoseGases.kcInsN N i (z, r))) ^ 2 := hmono
    _ = ρ ^ 2 * ∫ z : E3, (Work.UBBInputs8.boxQInd volA A i Ψ
          (Submission.BoseGases.kcInsN N i (z, r))) ^ 2 := by
        rw [MeasureTheory.integral_const_mul]

/-- The elementary lintegral bound: for a pointwise nonnegative real function, the `ofReal` of
the Bochner integral is at most the lintegral of the `ofReal`s (the junk-value convention
`∫ = 0` for a non-integrable function makes the non-integrable case trivial). -/
lemma ofReal_integral_le_lintegral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} (hf : ∀ x, 0 ≤ f x) :
    ENNReal.ofReal (∫ x, f x ∂μ) ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
  by_cases h : Integrable f μ
  · rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal h (Eventually.of_forall hf)]
  · rw [MeasureTheory.integral_undef h, ENNReal.ofReal_zero]
    exact bot_le

/-! ## 5. Measurability and integrability of the `r`-side -/

/-- The `r`-integral of the unweighted inserted square is measurable. -/
lemma measurable_integral_boxQInd_sq {N : ℕ} {volA : ℝ} {A : Set E3} (hAcm : MeasurableSet A)
    {Ψ : XX (N + 1) → ℝ} (hΨm : Measurable Ψ) (i : Fin (N + 1)) :
    Measurable (fun r : XX N => ∫ z : E3,
      (Work.UBBInputs8.boxQInd volA A i Ψ (Submission.BoseGases.kcInsN N i (z, r))) ^ 2) := by
  have huncur : StronglyMeasurable (fun q : XX N × E3 =>
      (Work.UBBInputs8.boxQInd volA A i Ψ (Submission.BoseGases.kcInsN N i (q.2, q.1))) ^ 2) :=
    (((Work.SlotWord.measurable_boxQInd volA A hAcm i hΨm).comp (by fun_prop)).pow_const 2).stronglyMeasurable
  exact (huncur.integral_prod_right' (ν := (volume : Measure E3))).measurable

/-- The `r`-integral of the unweighted inserted square is integrable over the box. -/
lemma integrable_integral_boxQInd_sq {N : ℕ} {a volA Cq : ℝ} (ha : 0 < a) {A : Set E3}
    (hAcm : MeasurableSet A) (hAfin : (volume : Measure E3) A < ⊤)
    (hvolA : volA = (volume A).toReal) {Ψ : XX (N + 1) → ℝ} (hΨm : Measurable Ψ)
    (i : Fin (N + 1)) (hCq0 : 0 ≤ Cq)
    (hQ : ∀ (z : E3) (r : XX N), r ∈ Submission.BoseGases.abox N a →
      |Work.UBBInputs8.boxQInd volA A i Ψ (Submission.BoseGases.kcInsN N i (z, r))|
        ≤ Cq * A.indicator (fun _ => (1 : ℝ)) z) :
    Integrable (fun r : XX N => ∫ z : E3,
      (Work.UBBInputs8.boxQInd volA A i Ψ (Submission.BoseGases.kcInsN N i (z, r))) ^ 2)
      (volume.restrict (Submission.BoseGases.abox N a)) := by
  refine IntegrableOn.of_bound (Submission.BoseGases.abox_lt_top N a ha.le)
    (measurable_integral_boxQInd_sq hAcm hΨm i).aestronglyMeasurable (Cq ^ 2 * volA) ?_
  filter_upwards [MeasureTheory.ae_restrict_mem (Submission.BoseGases.abox_measurable N a)]
    with r hr
  have hb := (integrable_sq_of_abs_le_indicator hAcm hAfin hvolA
    ((Work.SlotWord.measurable_boxQInd volA A hAcm i hΨm).comp (by fun_prop)).aestronglyMeasurable
    hCq0 (fun z => hQ z r hr)).2
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun z => sq_nonneg _))]
  exact hb

/-! ## 6. The assembly -/

/-- **The `r`-part bound.** -/
theorem tBamp_rPart_bound {N : ℕ} {a volA ρ : ℝ} (ha : 0 < a) (hvolpos : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hAcm : MeasurableSet A)
    (hAc : A ⊆ Submission.BoseGases.acube a)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    {rr : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hrm : MeasureTheory.AEStronglyMeasurable rr MeasureTheory.volume)
    (hrb : ∀ z, |rr z| ≤ ρ) (hρ0 : 0 ≤ ρ)
    {Ψ : Submission.BoseGases.X (N + 1) → ℝ} (hΨ : ContDiff ℝ (⊤ : ENat) Ψ) (i : Fin (N + 1)) :
    MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
        (a ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox (N + 1) a,
          ‖Work.SmallBoxTBWord.tBamp rr p (Work.UBBInputs8.boxQInd volA A i Ψ) i x‖ ^ 2)
      MeasureTheory.volume
      ∧ (∫ p : EuclideanSpace ℝ (Fin 3), (a ^ 3)⁻¹ *
            ∫ x in Submission.BoseGases.abox (N + 1) a,
              ‖Work.SmallBoxTBWord.tBamp rr p (Work.UBBInputs8.boxQInd volA A i Ψ) i x‖ ^ 2)
        ≤ (2 * Real.pi) ^ 3 * ρ ^ 2 *
            ∫ r in Submission.BoseGases.abox N a, ∫ z : EuclideanSpace ℝ (Fin 3),
              (Work.UBBInputs8.boxQInd volA A i Ψ (Submission.BoseGases.kcInsN N i (z, r))) ^ 2 := by
  classical
  have hΨm : Measurable Ψ := hΨ.continuous.measurable
  have hAfin : (volume : Measure E3) A < ⊤ :=
    lt_of_le_of_lt (measure_mono hAc)
      (by rw [Submission.BoseGases.acube_volume a ha.le]; exact ENNReal.ofReal_lt_top)
  obtain ⟨Cq, hCq0, hCq⟩ := boxQInd_indicator_bound (N := N) ha hvolpos hAc hvolA hΨ.continuous i
  -- abbreviations
  set ν : Measure (XX N) := (volume : Measure (XX N)).restrict
    (Submission.BoseGases.abox N a) with hνdef
  set P : Measure (E3 × XX N) := (volume : Measure E3).prod ν with hPdef
  set g : E3 → XX N → ℝ := fun p r =>
    ‖Submission.BoseGases.kinFT (rFibre rr volA A Ψ i r) p‖ ^ 2 with hgdef
  set X : XX N → ℝ := fun r => ∫ z : E3,
    (Work.UBBInputs8.boxQInd volA A i Ψ (Submission.BoseGases.kcInsN N i (z, r))) ^ 2 with hXdef
  set B : ℝ := ∫ r in Submission.BoseGases.abox N a, ∫ z : E3,
    (Work.UBBInputs8.boxQInd volA A i Ψ (Submission.BoseGases.kcInsN N i (z, r))) ^ 2 with hBdef
  have hB0 : 0 ≤ B := by
    rw [hBdef]
    exact integral_nonneg (fun r => integral_nonneg (fun z => sq_nonneg _))
  -- measurability helpers
  have hmeasX : Measurable (fun r : XX N => ENNReal.ofReal (X r)) := by
    rw [hXdef]
    exact ENNReal.measurable_ofReal.comp (measurable_integral_boxQInd_sq hAcm hΨm i)
  -- the pointwise peel
  have hpeel : ∀ p : E3, (a ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox (N + 1) a,
        ‖Work.SmallBoxTBWord.tBamp rr p (Work.UBBInputs8.boxQInd volA A i Ψ) i x‖ ^ 2
      = ∫ r in Submission.BoseGases.abox N a, g p r :=
    fun p => slotDens_peel_boxQInd (N := N) ha i rr p
  -- joint measurability in `(p, r)`
  have hpair : AEStronglyMeasurable (Function.uncurry g) P := by
    rw [hPdef, hgdef]
    exact aestronglyMeasurable_pair_kinFT hAcm hΨm i hrm
  -- the a.e. Plancherel statement and the `z`-bound
  have hae : ∀ᵐ r ∂ν, Integrable (fun p : E3 => g p r) volume
      ∧ (∫ p : E3, g p r = (2 * Real.pi) ^ 3 * ∫ z : E3, ‖rFibre rr volA A Ψ i r z‖ ^ 2)
      ∧ (∫ z : E3, ‖rFibre rr volA A Ψ i r z‖ ^ 2 ≤ ρ ^ 2 * X r) := by
    rw [hνdef]
    filter_upwards [MeasureTheory.ae_restrict_mem (Submission.BoseGases.abox_measurable N a)]
      with r hr
    obtain ⟨hm1, hm2⟩ := memLp_rFibre hAcm hAfin hΨm i hrm hCq0 hρ0 hrb hCq hr
    refine ⟨?_, ?_, ?_⟩
    · rw [hgdef]
      exact (integral_kinFT_sq_eq hm1 hm2).1
    · rw [hgdef]
      exact (integral_kinFT_sq_eq hm1 hm2).2
    · rw [hXdef]
      exact integral_normSq_rFibre_le hAcm hAfin hvolA hΨm i hrm hCq0 hρ0 hrb hCq hr
  -- the master lintegral chain
  have hofReal : AEMeasurable (fun q : E3 × XX N => ENNReal.ofReal (g q.1 q.2)) P :=
    ENNReal.measurable_ofReal.comp_aemeasurable hpair.aemeasurable
  have hchain : ∫⁻ q : E3 × XX N, ENNReal.ofReal (g q.1 q.2) ∂P
      ≤ ENNReal.ofReal ((2 * Real.pi) ^ 3 * ρ ^ 2 * B) := by
    -- Tonelli
    have h1 : ∫⁻ q : E3 × XX N, ENNReal.ofReal (g q.1 q.2) ∂P
        = ∫⁻ r : XX N, ∫⁻ p : E3, ENNReal.ofReal (g p r) ∂volume ∂ν :=
      MeasureTheory.lintegral_prod_symm _ hofReal
    -- `ofReal ∫ = ∫⁻ ofReal`
    have h2 : ∫⁻ r : XX N, ∫⁻ p : E3, ENNReal.ofReal (g p r) ∂volume ∂ν
        = ∫⁻ r : XX N, ENNReal.ofReal (∫ p : E3, g p r ∂volume) ∂ν := by
      refine MeasureTheory.lintegral_congr_ae ?_
      filter_upwards [hae] with r hr
      exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hr.1
        (Eventually.of_forall (fun p => sq_nonneg _))).symm
    -- the pointwise bound
    have h3 : ∫⁻ r : XX N, ENNReal.ofReal (∫ p : E3, g p r ∂volume) ∂ν
        ≤ ∫⁻ r : XX N, ENNReal.ofReal ((2 * Real.pi) ^ 3 * (ρ ^ 2 * X r)) ∂ν := by
      refine MeasureTheory.lintegral_mono_ae ?_
      filter_upwards [hae] with r hr
      refine ENNReal.ofReal_le_ofReal ?_
      rw [hr.2.1]
      exact mul_le_mul_of_nonneg_left hr.2.2 (by positivity)
    -- pull out the constant
    have h4 : ∫⁻ r : XX N, ENNReal.ofReal ((2 * Real.pi) ^ 3 * (ρ ^ 2 * X r)) ∂ν
        = ENNReal.ofReal ((2 * Real.pi) ^ 3 * ρ ^ 2) * ∫⁻ r : XX N,
            ENNReal.ofReal (X r) ∂ν := by
      have hcongr : ∫⁻ r : XX N, ENNReal.ofReal ((2 * Real.pi) ^ 3 * (ρ ^ 2 * X r)) ∂ν
          = ∫⁻ r : XX N, ENNReal.ofReal ((2 * Real.pi) ^ 3 * ρ ^ 2) *
              ENNReal.ofReal (X r) ∂ν := by
        refine MeasureTheory.lintegral_congr (fun r => ?_)
        rw [show (2 * Real.pi) ^ 3 * (ρ ^ 2 * X r)
            = ((2 * Real.pi) ^ 3 * ρ ^ 2) * X r from by ring]
        exact ENNReal.ofReal_mul (p := (2 * Real.pi) ^ 3 * ρ ^ 2) (q := X r) (by positivity)
      rw [hcongr, MeasureTheory.lintegral_const_mul _ hmeasX]
    -- `ofReal ∫ = ∫⁻ ofReal` for the `r`-integral
    have h5 : ∫⁻ r : XX N, ENNReal.ofReal (X r) ∂ν = ENNReal.ofReal B := by
      have hcongr : ∫⁻ r : XX N, ENNReal.ofReal (X r) ∂ν
          = ∫⁻ r : XX N, ENNReal.ofReal (∫ z : E3, (Work.UBBInputs8.boxQInd volA A i Ψ
              (Submission.BoseGases.kcInsN N i (z, r))) ^ 2) ∂ν := by
        rw [hXdef]
      rw [hcongr, ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
        (integrable_integral_boxQInd_sq ha hAcm hAfin hvolA hΨm i hCq0 hCq)
        (Eventually.of_forall (fun r => integral_nonneg (fun z => sq_nonneg _))), hBdef]
    calc ∫⁻ q : E3 × XX N, ENNReal.ofReal (g q.1 q.2) ∂P
        = ∫⁻ r : XX N, ENNReal.ofReal (∫ p : E3, g p r ∂volume) ∂ν := by rw [h1, h2]
      _ ≤ ∫⁻ r : XX N, ENNReal.ofReal ((2 * Real.pi) ^ 3 * (ρ ^ 2 * X r)) ∂ν := h3
      _ = ENNReal.ofReal ((2 * Real.pi) ^ 3 * ρ ^ 2) * ENNReal.ofReal B := by rw [h4, h5]
      _ = ENNReal.ofReal ((2 * Real.pi) ^ 3 * ρ ^ 2 * B) :=
          (ENNReal.ofReal_mul (p := (2 * Real.pi) ^ 3 * ρ ^ 2) (q := B)
            (mul_nonneg (by positivity) (by positivity))).symm
  -- the lintegral of the target integrand
  have hlin : ∫⁻ p : E3, ENNReal.ofReal ((a ^ 3)⁻¹ *
        ∫ x in Submission.BoseGases.abox (N + 1) a,
          ‖Work.SmallBoxTBWord.tBamp rr p (Work.UBBInputs8.boxQInd volA A i Ψ) i x‖ ^ 2)
      ∂volume ≤ ENNReal.ofReal ((2 * Real.pi) ^ 3 * ρ ^ 2 * B) := by
    have h6 : ∫⁻ p : E3, ENNReal.ofReal ((a ^ 3)⁻¹ *
          ∫ x in Submission.BoseGases.abox (N + 1) a,
            ‖Work.SmallBoxTBWord.tBamp rr p (Work.UBBInputs8.boxQInd volA A i Ψ) i x‖ ^ 2)
        ∂volume
        = ∫⁻ p : E3, ENNReal.ofReal (∫ r in Submission.BoseGases.abox N a, g p r) ∂volume := by
      refine MeasureTheory.lintegral_congr (fun p => ?_)
      rw [hpeel p]
    have h7 : ∫⁻ p : E3, ENNReal.ofReal (∫ r in Submission.BoseGases.abox N a, g p r) ∂volume
        ≤ ∫⁻ p : E3, ∫⁻ r : XX N, ENNReal.ofReal (g p r) ∂ν ∂volume :=
      MeasureTheory.lintegral_mono (fun p =>
        ofReal_integral_le_lintegral (fun r => sq_nonneg _))
    have h8 : ∫⁻ p : E3, ∫⁻ r : XX N, ENNReal.ofReal (g p r) ∂ν ∂volume
        = ∫⁻ q : E3 × XX N, ENNReal.ofReal (g q.1 q.2) ∂P :=
      MeasureTheory.lintegral_lintegral hofReal
    calc ∫⁻ p : E3, ENNReal.ofReal ((a ^ 3)⁻¹ *
          ∫ x in Submission.BoseGases.abox (N + 1) a,
            ‖Work.SmallBoxTBWord.tBamp rr p (Work.UBBInputs8.boxQInd volA A i Ψ) i x‖ ^ 2)
        ∂volume
        = ∫⁻ p : E3, ENNReal.ofReal (∫ r in Submission.BoseGases.abox N a, g p r) ∂volume := h6
      _ ≤ ∫⁻ p : E3, ∫⁻ r : XX N, ENNReal.ofReal (g p r) ∂ν ∂volume := h7
      _ = ∫⁻ q : E3 × XX N, ENNReal.ofReal (g q.1 q.2) ∂P := h8
      _ ≤ ENNReal.ofReal ((2 * Real.pi) ^ 3 * ρ ^ 2 * B) := hchain
  -- the p-marginal is a.e.-strongly measurable
  have hAesm : AEStronglyMeasurable (fun p : E3 => (a ^ 3)⁻¹ *
      ∫ x in Submission.BoseGases.abox (N + 1) a,
        ‖Work.SmallBoxTBWord.tBamp rr p (Work.UBBInputs8.boxQInd volA A i Ψ) i x‖ ^ 2) volume := by
    have h1 : AEStronglyMeasurable (fun p : E3 =>
        ∫ r in Submission.BoseGases.abox N a, g p r) volume :=
      AEStronglyMeasurable.integral_prod_right' (μ := volume) (ν := ν) hpair
    refine h1.congr (Eventually.of_forall (fun p => ?_))
    exact (hpeel p).symm
  have hAfun0 : ∀ p : E3, 0 ≤ (a ^ 3)⁻¹ *
      ∫ x in Submission.BoseGases.abox (N + 1) a,
        ‖Work.SmallBoxTBWord.tBamp rr p (Work.UBBInputs8.boxQInd volA A i Ψ) i x‖ ^ 2 :=
    fun p => mul_nonneg (inv_nonneg.mpr (by positivity)) (integral_nonneg (fun x => sq_nonneg _))
  refine ⟨⟨hAesm, ?_⟩, ?_⟩
  · -- integrability
    refine (MeasureTheory.hasFiniteIntegral_iff_ofReal
      (Eventually.of_forall hAfun0)).mpr (lt_of_le_of_lt hlin ENNReal.ofReal_lt_top)
  · -- the bound
    have hval : (∫ p : E3, (a ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox (N + 1) a,
          ‖Work.SmallBoxTBWord.tBamp rr p (Work.UBBInputs8.boxQInd volA A i Ψ) i x‖ ^ 2)
        = (∫⁻ p : E3, ENNReal.ofReal ((a ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox (N + 1) a,
          ‖Work.SmallBoxTBWord.tBamp rr p (Work.UBBInputs8.boxQInd volA A i Ψ) i x‖ ^ 2)
          ∂volume).toReal :=
      MeasureTheory.integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hAfun0) hAesm
    calc (∫ p : E3, (a ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox (N + 1) a,
          ‖Work.SmallBoxTBWord.tBamp rr p (Work.UBBInputs8.boxQInd volA A i Ψ) i x‖ ^ 2)
        = (∫⁻ p : E3, ENNReal.ofReal ((a ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox (N + 1) a,
            ‖Work.SmallBoxTBWord.tBamp rr p (Work.UBBInputs8.boxQInd volA A i Ψ) i x‖ ^ 2)
            ∂volume).toReal := hval
      _ ≤ (ENNReal.ofReal ((2 * Real.pi) ^ 3 * ρ ^ 2 *
            ∫ r in Submission.BoseGases.abox N a, ∫ z : E3,
              (Work.UBBInputs8.boxQInd volA A i Ψ
                (Submission.BoseGases.kcInsN N i (z, r))) ^ 2)).toReal := by
          refine ENNReal.toReal_mono ENNReal.ofReal_ne_top ?_
          rw [← hBdef]
          exact hlin
      _ = (2 * Real.pi) ^ 3 * ρ ^ 2 * ∫ r in Submission.BoseGases.abox N a, ∫ z : E3,
              (Work.UBBInputs8.boxQInd volA A i Ψ
                (Submission.BoseGases.kcInsN N i (z, r))) ^ 2 := by
          rw [← hBdef]
          exact ENNReal.toReal_ofReal (mul_nonneg (by positivity) hB0)

end Work.BoseFixB1S
