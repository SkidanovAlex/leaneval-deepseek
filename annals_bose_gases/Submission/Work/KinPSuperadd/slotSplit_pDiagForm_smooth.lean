import Mathlib.Tactic.Have
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.KinPSuperadd.PDiagDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `SlotSplit` for the faithful (`pDiagForm`) small-box kinetic word

This module proves the SMOOTH-hypothesis form of the chapter's
`slotSplit_pDiagForm`:

    `SlotSplit s (fun N Φ => pDiagForm s F N Φ)`

from `hint : ∀ N Ψ, ContDiff ℝ ∞ Ψ → Integrable (p ↦ F ‖p‖ * Σ_i slotTerm …)`.

CAUTION — this is NOT the same hypothesis as the one in
`Submission/Work/KinPSuperadd/slotSplit_pDiagForm.lean`, whose `hint` is stated
with `ContDiff ℝ ⊤`, i.e. `C^ω` = ANALYTIC (`contDiff_omega_iff_analyticOnNhd`),
NOT `C^∞`.  `ContDiff ℝ ⊤` and `ContDiff ℝ ∞` are inequivalent (`ContDiff.of_le
le_top` gives analytic ⟹ smooth, not the converse); the `SlotSplit` structure —
and therefore the conclusion — speaks about `ContDiff ℝ ∞` states, and every
consumer in this directory (`Engine.lean`, `rayleigh_diagSlotWord.lean`,
`Superadd.slotSplit_diagSlotWord`) states its `hint` with `ContDiff ℝ ∞`.  The
theorem below is the statement the chapter uses.

for an arbitrary weight `F ≥ 0` and box side `s`, *given* the hypothesis `hint`
that the `p`-weighted TOTAL slot content `p ↦ F ‖p‖ * Σ_i slotTerm s N Ψ i p`
is integrable for every smooth `Ψ` (which is what makes the `p`-integral of each
individual slot meaningful and lets it be moved in and out of the block sums).

`pDiagForm` is a sum of one-particle forms over the slots, so it is
block-splittable; the block decomposition is the combination of

* the pointwise slice identity `pSlotAmp_merge_castAdd` /
  `pSlotAmp_merge_natAdd` (the slot amplitude of a merged configuration is the
  slot amplitude of the corresponding slice — `PDiagDefs`), and
* Fubini on the box (`aboxFubini` / `aboxFubini_swapped`) composed with Fubini
  between the `p`-variable and the frozen block variable, the latter supplied by
  `MeasureTheory.integrable_prod_iff` for the (nonnegative) slice kernel.

For `s ≤ 0` every centred box with `N ≠ 0` is a null set and `(s³)⁻¹ = 0` at
`s = 0`, so `pDiagForm` vanishes identically and all three fields are trivial.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.KinPSuperadd

open Submission BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

/-! ## 1  Elementary properties of the slot content -/

/-- Each slot content is nonnegative. -/
lemma slotTerm_nonneg {s : ℝ} (hs : 0 < s) (N : ℕ) (Ψ : X N → ℝ) (i : Fin N) (p : ℝ³) :
    0 ≤ slotTerm s N Ψ i p := by
  rw [slotTerm]
  exact mul_nonneg (inv_nonneg.mpr (pow_nonneg (le_of_lt hs) 3))
    (integral_nonneg (fun x => sq_nonneg _))

/-- The diagonal slot content is nonnegative. -/
lemma slotDiag_nonneg {s : ℝ} (hs : 0 < s) (N : ℕ) (Ψ : X N → ℝ) (p : ℝ³) :
    0 ≤ slotDiag s N Ψ p :=
  Finset.sum_nonneg fun i _ => slotTerm_nonneg hs N Ψ i p

/-- Each slot content is bounded by the diagonal one. -/
lemma slotTerm_le_slotDiag {s : ℝ} (hs : 0 < s) (N : ℕ) (Ψ : X N → ℝ) (i : Fin N) (p : ℝ³) :
    slotTerm s N Ψ i p ≤ slotDiag s N Ψ p :=
  Finset.single_le_sum (fun k _ => slotTerm_nonneg hs N Ψ k p) (Finset.mem_univ i)

/-- Continuity in `p` of a slot content, for a continuous state. -/
lemma continuous_slotTerm {s : ℝ} (hs : 0 < s) {N : ℕ} {Ψ : X N → ℝ} (hΨ : Continuous Ψ)
    (i : Fin N) : Continuous (fun p : ℝ³ => slotTerm s N Ψ i p) := by
  rw [show (fun p : ℝ³ => slotTerm s N Ψ i p)
      = fun p : ℝ³ => (s ^ 3)⁻¹ * ∫ x in abox N s, ‖pSlotAmp s p Ψ i x‖ ^ 2 from rfl]
  exact continuous_const.mul (Work.SmallBoxBridge.Cauchy.continuous_integral_pSlotAmp_sq hs hΨ i)

/-- Continuity in `p` of the diagonal slot content, for a continuous state. -/
lemma continuous_slotDiag {s : ℝ} (hs : 0 < s) {N : ℕ} {Ψ : X N → ℝ} (hΨ : Continuous Ψ) :
    Continuous (slotDiag s N Ψ) := by
  rw [show slotDiag s N Ψ = fun p : ℝ³ => ∑ i : Fin N, slotTerm s N Ψ i p from rfl]
  exact continuous_finsetSum Finset.univ (fun i _ => continuous_slotTerm hs hΨ i)


/-- The measurable representative of an a.e.-strongly-measurable function agrees
with it a.e. on the product with any s-finite measure (after projection). -/
lemma ae_mk_comp_fst {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν] {f : α → ℝ}
    (hf : AEStronglyMeasurable f μ) :
    ∀ᵐ q ∂(μ.prod ν), hf.mk f q.1 = f q.1 := by
  rw [MeasureTheory.ae_iff]
  have hsub : {q : α × β | ¬ hf.mk f q.1 = f q.1}
      ⊆ {p : α | ¬ hf.mk f p = f p} ×ˢ (Set.univ : Set β) := by
    intro q hq
    exact ⟨hq, Set.mem_univ _⟩
  exact measure_mono_null hsub (by
    rw [Measure.prod_prod, ae_iff.mp hf.ae_eq_mk.symm, zero_mul])

/-! ## 2  Per-slot `p`-integrability from the `hint` hypothesis -/

/-- **Peeling one summand off the `hint` integrand.**  If the total slot content
`p ↦ F ‖p‖ * Σ_i slotTerm s N Ψ i p` is integrable then so is each individual
summand `p ↦ F ‖p‖ * slotTerm s N Ψ i p`.

The point is that `F` itself need not be measurable: on the (measurable) set
`{slotDiag = 0}` every slot content vanishes, and off it one recovers `F ‖p‖`
as the quotient `slotSum / slotDiag`. -/
lemma integrable_slotForm_of_hint {s : ℝ} (hs : 0 < s) {F : ℝ → ℝ} (hF : ∀ r, 0 ≤ F r)
    (hint : ∀ (N : ℕ) (Ψ : X N → ℝ), ContDiff ℝ ∞ Ψ → Integrable (slotSum s F N Ψ))
    {N : ℕ} {Ψ : X N → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (i : Fin N) :
    Integrable (fun p : ℝ³ => F ‖p‖ * slotTerm s N Ψ i p) := by
  have hφ : Integrable (slotSum s F N Ψ) := hint N Ψ hΨ
  have hpoint : (fun p : ℝ³ => F ‖p‖ * slotTerm s N Ψ i p)
      = fun p : ℝ³ => slotSum s F N Ψ p * (slotTerm s N Ψ i p * (slotDiag s N Ψ p)⁻¹) := by
    funext p
    have hle := slotTerm_le_slotDiag hs N Ψ i p
    have hnn := slotTerm_nonneg hs N Ψ i p
    rcases eq_or_ne (slotDiag s N Ψ p) 0 with h | h
    · have h0 : slotTerm s N Ψ i p = 0 := le_antisymm (by rw [h] at hle; exact hle) hnn
      simp [slotSum, h0, h]
    · show F ‖p‖ * slotTerm s N Ψ i p
          = F ‖p‖ * slotDiag s N Ψ p * (slotTerm s N Ψ i p * (slotDiag s N Ψ p)⁻¹)
      field_simp
  have hmeas : AEMeasurable (fun p : ℝ³ => slotTerm s N Ψ i p * (slotDiag s N Ψ p)⁻¹) :=
    (((continuous_slotTerm hs hΨ.continuous i).measurable).mul
      ((continuous_slotDiag hs hΨ.continuous).measurable.inv)).aemeasurable
  rw [hpoint]
  refine Integrable.mono' hφ (hφ.aemeasurable.mul hmeas).aestronglyMeasurable ?_
  filter_upwards with p
  have hback : slotSum s F N Ψ p * (slotTerm s N Ψ i p * (slotDiag s N Ψ p)⁻¹)
      = F ‖p‖ * slotTerm s N Ψ i p := (congrFun hpoint p).symm
  rw [hback, Real.norm_of_nonneg (mul_nonneg (hF _) (slotTerm_nonneg hs N Ψ i p))]
  calc F ‖p‖ * slotTerm s N Ψ i p ≤ F ‖p‖ * slotDiag s N Ψ p :=
        mul_le_mul_of_nonneg_left (slotTerm_le_slotDiag hs N Ψ i p) (hF _)
    _ = slotSum s F N Ψ p := rfl

/-! ## 3  Continuity of the slice functionals -/

/-- Joint continuity in `(p,w)` of the first-block slice functional. -/
lemma continuous_sliceFunFirst {s : ℝ} (hs : 0 < s) (N1 N2 : ℕ)
    {Φ : X (N1 + N2) → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (i : Fin N1) :
    Continuous (fun q : ℝ³ × X N2 => ∫ u in abox N1 s,
      ‖pSlotAmp s q.1 (fun u' => Φ (mergeBlock N1 N2 (u', q.2))) i u‖ ^ 2) := by
  have hB : Continuous (fun q : ℝ³ × X (N1+N2) =>
      pSlotAmp s q.1 Φ (Fin.castAdd N2 i) q.2) :=
    Work.SmallBoxBridge.Cauchy.continuous_pSlotAmp_pair (N := N1+N2) hs hΦ.continuous
      (Fin.castAdd N2 i)
  have h1 : Continuous (fun r : (ℝ³ × X N2) × X N1 => r.1.1) := continuous_fst.comp continuous_fst
  have h2 : Continuous (fun r : (ℝ³ × X N2) × X N1 => r.1.2) := continuous_snd.comp continuous_fst
  have h3 : Continuous (fun r : (ℝ³ × X N2) × X N1 => r.2) := continuous_snd
  let Fmap : (ℝ³ × X N2) × X N1 → ℝ³ × X (N1+N2) :=
    fun r => (r.1.1, mergeBlock N1 N2 (r.2, r.1.2))
  have hFmap : Continuous Fmap := h1.prodMk ((continuous_mergeBlock N1 N2).comp (h3.prodMk h2))
  have hAmp : Continuous (fun r : (ℝ³ × X N2) × X N1 =>
      pSlotAmp s r.1.1 (fun u' => Φ (mergeBlock N1 N2 (u', r.1.2))) i r.2) :=
    (hB.comp hFmap).congr (fun r => pSlotAmp_merge_castAdd s r.1.1 Φ r.2 r.1.2 i)
  have hnn : Continuous (fun r : (ℝ³ × X N2) × X N1 =>
      ‖pSlotAmp s r.1.1 (fun u' => Φ (mergeBlock N1 N2 (u', r.1.2))) i r.2‖ ^ 2) :=
    (continuous_norm.comp hAmp).pow 2
  exact continuous_parametric_integral_of_continuous
    (μ := (volume : Measure (X N1)))
    (f := fun (q : ℝ³ × X N2) (u : X N1) =>
      ‖pSlotAmp s q.1 (fun u' => Φ (mergeBlock N1 N2 (u', q.2))) i u‖ ^ 2) hnn
    (abox_compact N1 hs)

/-- Joint continuity in `(u,p)` of the second-block slice functional. -/
lemma continuous_sliceFunLast {s : ℝ} (hs : 0 < s) (N1 N2 : ℕ)
    {Φ : X (N1 + N2) → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (j : Fin N2) :
    Continuous (fun q : X N1 × ℝ³ => ∫ w in abox N2 s,
      ‖pSlotAmp s q.2 (fun w' => Φ (mergeBlock N1 N2 (q.1, w'))) j w‖ ^ 2) := by
  have hB : Continuous (fun q : ℝ³ × X (N1+N2) =>
      pSlotAmp s q.1 Φ (Fin.natAdd N1 j) q.2) :=
    Work.SmallBoxBridge.Cauchy.continuous_pSlotAmp_pair (N := N1+N2) hs hΦ.continuous
      (Fin.natAdd N1 j)
  have h1 : Continuous (fun r : (X N1 × ℝ³) × X N2 => r.1.2) := continuous_snd.comp continuous_fst
  have h2 : Continuous (fun r : (X N1 × ℝ³) × X N2 => r.1.1) := continuous_fst.comp continuous_fst
  have h3 : Continuous (fun r : (X N1 × ℝ³) × X N2 => r.2) := continuous_snd
  let Fmap : (X N1 × ℝ³) × X N2 → ℝ³ × X (N1+N2) :=
    fun r => (r.1.2, mergeBlock N1 N2 (r.1.1, r.2))
  have hFmap : Continuous Fmap := h1.prodMk ((continuous_mergeBlock N1 N2).comp (h2.prodMk h3))
  have hAmp : Continuous (fun r : (X N1 × ℝ³) × X N2 =>
      pSlotAmp s r.1.2 (fun w' => Φ (mergeBlock N1 N2 (r.1.1, w'))) j r.2) :=
    (hB.comp hFmap).congr (fun r => pSlotAmp_merge_natAdd s r.1.2 Φ r.1.1 r.2 j)
  have hnn : Continuous (fun r : (X N1 × ℝ³) × X N2 =>
      ‖pSlotAmp s r.1.2 (fun w' => Φ (mergeBlock N1 N2 (r.1.1, w'))) j r.2‖ ^ 2) :=
    (continuous_norm.comp hAmp).pow 2
  exact continuous_parametric_integral_of_continuous
    (μ := (volume : Measure (X N2)))
    (f := fun (q : X N1 × ℝ³) (w : X N2) =>
      ‖pSlotAmp s q.2 (fun w' => Φ (mergeBlock N1 N2 (q.1, w'))) j w‖ ^ 2) hnn
    (abox_compact N2 hs)

/-! ## 4  The slice integrals -/

/-- The `w`-integral of the first-block slice functional is the full box
integral of the first-block slot amplitude. -/
lemma integral_sliceFunFirst {s : ℝ} (hs : 0 < s) (N1 N2 : ℕ)
    {Φ : X (N1 + N2) → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (i : Fin N1) (p : ℝ³) :
    (∫ w, sliceFunFirst s Φ i (p, w) ∂(volume.restrict (abox N2 s)))
      = ∫ x in abox (N1 + N2) s, ‖pSlotAmp s p Φ (Fin.castAdd N2 i) x‖ ^ 2 := by
  rw [← aboxFubini_swapped (N1 := N1) (N2 := N2) s
      (fun x => ‖pSlotAmp s p Φ (Fin.castAdd N2 i) x‖ ^ 2)
      (integrableOn_pSlotAmp_sq s hs p hΦ.continuous (Fin.castAdd N2 i))]
  apply integral_congr_ae
  filter_upwards with w
  apply integral_congr_ae
  filter_upwards with u
  rw [pSlotAmp_merge_castAdd]

/-- The `u`-integral of the second-block slice functional is the full box
integral of the second-block slot amplitude. -/
lemma integral_sliceFunLast {s : ℝ} (hs : 0 < s) (N1 N2 : ℕ)
    {Φ : X (N1 + N2) → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (j : Fin N2) (p : ℝ³) :
    (∫ u, sliceFunLast s Φ j (u, p) ∂(volume.restrict (abox N1 s)))
      = ∫ x in abox (N1 + N2) s, ‖pSlotAmp s p Φ (Fin.natAdd N1 j) x‖ ^ 2 := by
  rw [← aboxFubini (N1 := N1) (N2 := N2) s
      (fun x => ‖pSlotAmp s p Φ (Fin.natAdd N1 j) x‖ ^ 2)
      (integrableOn_pSlotAmp_sq s hs p hΦ.continuous (Fin.natAdd N1 j))]
  apply integral_congr_ae
  filter_upwards with u
  apply integral_congr_ae
  filter_upwards with w
  rw [pSlotAmp_merge_natAdd]

/-- The `w`-integral of the first-block slice KERNEL is `F ‖p‖` times the
`(N1+N2)`-particle first-block slot content. -/
lemma integral_sliceKernel_eq {s : ℝ} (hs : 0 < s) (F : ℝ → ℝ) (N1 N2 : ℕ)
    {Φ : X (N1 + N2) → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (i : Fin N1) (p : ℝ³) :
    (∫ w, sliceKernel s F Φ i (p, w) ∂(volume.restrict (abox N2 s)))
      = F ‖p‖ * slotTerm s (N1 + N2) Φ (Fin.castAdd N2 i) p := by
  rw [show (fun w => sliceKernel s F Φ i (p, w))
      = fun w => F ‖p‖ * ((fun w => (s ^ 3)⁻¹ * sliceFunFirst s Φ i (p, w)) w) from rfl]
  rw [integral_const_mul, integral_const_mul, integral_sliceFunFirst hs N1 N2 hΦ i p]
  rfl

/-- The `u`-integral of the second-block slice KERNEL is `F ‖p‖` times the
`(N1+N2)`-particle second-block slot content. -/
lemma integral_sliceKernelLast_eq {s : ℝ} (hs : 0 < s) (F : ℝ → ℝ) (N1 N2 : ℕ)
    {Φ : X (N1 + N2) → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (j : Fin N2) (p : ℝ³) :
    (∫ u, sliceKernelLast s F Φ j (u, p) ∂(volume.restrict (abox N1 s)))
      = F ‖p‖ * slotTerm s (N1 + N2) Φ (Fin.natAdd N1 j) p := by
  rw [show (fun u => sliceKernelLast s F Φ j (u, p))
      = fun u => F ‖p‖ * ((fun u => (s ^ 3)⁻¹ * sliceFunLast s Φ j (u, p)) u) from rfl]
  rw [integral_const_mul, integral_const_mul, integral_sliceFunLast hs N1 N2 hΦ j p]
  rfl

/-! ## 5  Integrability of the slice kernels on the product -/

/-- A first-block slice functional which vanishes identically on a `p`-fibre
(which happens when the diagonal slot content of the full state vanishes) is
a.e. zero along that fibre. -/
lemma sliceFunFirst_ae_zero {s : ℝ} (hs : 0 < s) (N1 N2 : ℕ) {Φ : X (N1 + N2) → ℝ}
    (hΦ : ContDiff ℝ ∞ Φ) (i : Fin N1) (p : ℝ³)
    (hp : slotDiag s (N1 + N2) Φ p = 0) :
    (fun w : X N2 => sliceFunFirst s Φ i (p, w)) =ᵐ[volume.restrict (abox N2 s)] 0 := by
  have hcw : Continuous (fun w : X N2 => sliceFunFirst s Φ i (p, w)) :=
    (continuous_sliceFunFirst hs N1 N2 hΦ i).comp (continuous_const.prodMk continuous_id)
  have hInt : Integrable (fun w : X N2 => sliceFunFirst s Φ i (p, w))
      (volume.restrict (abox N2 s)) :=
    ContinuousOn.integrableOn_compact (abox_compact N2 hs) hcw.continuousOn
  have hnn : 0 ≤ fun w : X N2 => sliceFunFirst s Φ i (p, w) :=
    fun w => integral_nonneg (fun u => sq_nonneg _)
  have hzero : (∫ w, sliceFunFirst s Φ i (p, w) ∂(volume.restrict (abox N2 s))) = 0 := by
    rw [integral_sliceFunFirst hs N1 N2 hΦ i p]
    have hle := slotTerm_le_slotDiag hs (N1 + N2) Φ (Fin.castAdd N2 i) p
    rw [slotTerm, hp] at hle
    have hpos : 0 < (s ^ 3)⁻¹ := by positivity
    have hnn2 : 0 ≤ ∫ x in abox (N1 + N2) s, ‖pSlotAmp s p Φ (Fin.castAdd N2 i) x‖ ^ 2 :=
      integral_nonneg (fun x => sq_nonneg _)
    nlinarith
  exact (integral_eq_zero_iff_of_nonneg hnn hInt).mp hzero

/-- Same, for the second block. -/
lemma sliceFunLast_ae_zero {s : ℝ} (hs : 0 < s) (N1 N2 : ℕ) {Φ : X (N1 + N2) → ℝ}
    (hΦ : ContDiff ℝ ∞ Φ) (j : Fin N2) (p : ℝ³)
    (hp : slotDiag s (N1 + N2) Φ p = 0) :
    (fun u : X N1 => sliceFunLast s Φ j (u, p)) =ᵐ[volume.restrict (abox N1 s)] 0 := by
  have hcw : Continuous (fun u : X N1 => sliceFunLast s Φ j (u, p)) :=
    (continuous_sliceFunLast hs N1 N2 hΦ j).comp (continuous_id.prodMk continuous_const)
  have hInt : Integrable (fun u : X N1 => sliceFunLast s Φ j (u, p))
      (volume.restrict (abox N1 s)) :=
    ContinuousOn.integrableOn_compact (abox_compact N1 hs) hcw.continuousOn
  have hnn : 0 ≤ fun u : X N1 => sliceFunLast s Φ j (u, p) :=
    fun u => integral_nonneg (fun w => sq_nonneg _)
  have hzero : (∫ u, sliceFunLast s Φ j (u, p) ∂(volume.restrict (abox N1 s))) = 0 := by
    rw [integral_sliceFunLast hs N1 N2 hΦ j p]
    have hle := slotTerm_le_slotDiag hs (N1 + N2) Φ (Fin.natAdd N1 j) p
    rw [slotTerm, hp] at hle
    have hpos : 0 < (s ^ 3)⁻¹ := by positivity
    have hnn2 : 0 ≤ ∫ x in abox (N1 + N2) s, ‖pSlotAmp s p Φ (Fin.natAdd N1 j) x‖ ^ 2 :=
      integral_nonneg (fun x => sq_nonneg _)
    nlinarith
  exact (integral_eq_zero_iff_of_nonneg hnn hInt).mp hzero

/-- The first-block slice kernel is integrable on the product of the `p`-space
and the frozen box. -/
lemma integrable_sliceKernel {s : ℝ} (hs : 0 < s) {F : ℝ → ℝ} (hF : ∀ r, 0 ≤ F r)
    (hint : ∀ (N : ℕ) (Ψ : X N → ℝ), ContDiff ℝ ∞ Ψ → Integrable (slotSum s F N Ψ))
    (N1 N2 : ℕ) {Φ : X (N1 + N2) → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (i : Fin N1) :
    Integrable (sliceKernel s F Φ i)
      ((volume : Measure ℝ³).prod (volume.restrict (abox N2 s))) := by
  have hφ : Integrable (slotSum s F (N1+N2) Φ) := hint (N1+N2) Φ hΦ
  have hScont : Continuous (slotDiag s (N1+N2) Φ) := continuous_slotDiag hs hΦ.continuous
  have hBcont : Continuous (sliceFunFirst s Φ i) := continuous_sliceFunFirst hs N1 N2 hΦ i
  -- the null set of fibres whose frozen slice functional does not vanish
  set bad : Set (ℝ³ × X N2) :=
    {q | slotDiag s (N1+N2) Φ q.1 = 0 ∧ sliceFunFirst s Φ i q ≠ 0} with hbaddef
  have hbadm : MeasurableSet bad := by
    rw [hbaddef]
    exact ((hScont.measurable.comp continuous_fst.measurable) (measurableSet_singleton 0)).inter
      (hBcont.measurable (measurableSet_singleton (0:ℝ)).compl)
  have hbadzero : ((volume : Measure ℝ³).prod (volume.restrict (abox N2 s))) bad = 0 := by
    refine le_antisymm ?_ zero_le
    calc ((volume : Measure ℝ³).prod (volume.restrict (abox N2 s))) bad
        ≤ ∫⁻ p, (volume.restrict (abox N2 s)) (Prod.mk p ⁻¹' bad) ∂(volume : Measure ℝ³) :=
          Measure.prod_apply_le hbadm
      _ = 0 := by
        have hfun : (fun p : ℝ³ => (volume.restrict (abox N2 s)) (Prod.mk p ⁻¹' bad))
            = fun _ => (0 : ℝ≥0∞) := by
          funext p
          by_cases hp : slotDiag s (N1+N2) Φ p = 0
          · have hset : Prod.mk p ⁻¹' bad = {w : X N2 | sliceFunFirst s Φ i (p, w) ≠ 0} := by
              ext w; rw [hbaddef]; simp [hp]
            rw [hset]
            rw [show {w : X N2 | sliceFunFirst s Φ i (p, w) ≠ 0}
                = {w : X N2 | ¬ (sliceFunFirst s Φ i (p, w) = 0)} from rfl]
            exact ae_iff.mp (sliceFunFirst_ae_zero hs N1 N2 hΦ i p hp)
          · have hset : Prod.mk p ⁻¹' bad = (∅ : Set (X N2)) := by
              ext w; rw [hbaddef]; simp [hp]
            rw [hset, measure_empty]
        rw [hfun, lintegral_zero]
  have hbad_ae : ∀ᵐ q ∂((volume : Measure ℝ³).prod (volume.restrict (abox N2 s))),
      ¬ (slotDiag s (N1+N2) Φ q.1 = 0 ∧ sliceFunFirst s Φ i q ≠ 0) := by
    have : ∀ᵐ q ∂((volume : Measure ℝ³).prod (volume.restrict (abox N2 s))), q ∉ bad := by
      refine MeasureTheory.ae_iff.mpr ?_
      rwa [show {q : ℝ³ × X N2 | ¬ q ∉ bad} = bad from by ext q; simp [not_not]]
    filter_upwards [this] with q hq
    intro hcon
    exact hq hcon
  -- the measurable surrogate
  have hGm : AEMeasurable (fun q : ℝ³ × X N2 =>
      hφ.aestronglyMeasurable.mk (slotSum s F (N1+N2) Φ) q.1 *
        ((s ^ 3)⁻¹ * sliceFunFirst s Φ i q * (slotDiag s (N1+N2) Φ q.1)⁻¹))
      ((volume : Measure ℝ³).prod (volume.restrict (abox N2 s))) := by
    have h1 : AEMeasurable (fun q : ℝ³ × X N2 =>
        hφ.aestronglyMeasurable.mk (slotSum s F (N1+N2) Φ) q.1)
        ((volume : Measure ℝ³).prod (volume.restrict (abox N2 s))) :=
      hφ.aestronglyMeasurable.stronglyMeasurable_mk.aemeasurable.comp_fst
    have h2 : AEMeasurable (fun q : ℝ³ × X N2 =>
        (s ^ 3)⁻¹ * sliceFunFirst s Φ i q * (slotDiag s (N1+N2) Φ q.1)⁻¹)
        ((volume : Measure ℝ³).prod (volume.restrict (abox N2 s))) :=
      (continuous_const.mul hBcont).aemeasurable.mul
        ((hScont.measurable.comp continuous_fst.measurable).inv.aemeasurable)
    exact h1.mul h2
  have hae : sliceKernel s F Φ i
      =ᵐ[((volume : Measure ℝ³).prod (volume.restrict (abox N2 s)))]
      (fun q : ℝ³ × X N2 => hφ.aestronglyMeasurable.mk (slotSum s F (N1+N2) Φ) q.1 *
        ((s ^ 3)⁻¹ * sliceFunFirst s Φ i q * (slotDiag s (N1+N2) Φ q.1)⁻¹)) := by
    have hgood_ae : ∀ᵐ q ∂((volume : Measure ℝ³).prod (volume.restrict (abox N2 s))),
        hφ.aestronglyMeasurable.mk (slotSum s F (N1+N2) Φ) q.1
          = slotSum s F (N1+N2) Φ q.1 :=
      ae_mk_comp_fst hφ.aestronglyMeasurable
    filter_upwards [hgood_ae, hbad_ae] with q hq1 hq2
    by_cases hS : slotDiag s (N1+N2) Φ q.1 = 0
    · have hB0 : sliceFunFirst s Φ i q = 0 := by
        by_contra hBne
        exact hq2 ⟨hS, hBne⟩
      rw [sliceKernel, hB0]
      simp only [mul_zero, hS, inv_zero, mul_zero]
    · show F ‖q.1‖ * ((s ^ 3)⁻¹ * sliceFunFirst s Φ i q)
          = hφ.aestronglyMeasurable.mk (slotSum s F (N1+N2) Φ) q.1 *
              ((s ^ 3)⁻¹ * sliceFunFirst s Φ i q * (slotDiag s (N1+N2) Φ q.1)⁻¹)
      rw [hq1]
      show F ‖q.1‖ * ((s ^ 3)⁻¹ * sliceFunFirst s Φ i q)
          = F ‖q.1‖ * slotDiag s (N1+N2) Φ q.1 *
              ((s ^ 3)⁻¹ * sliceFunFirst s Φ i q * (slotDiag s (N1+N2) Φ q.1)⁻¹)
      field_simp
  have hmeas : AEStronglyMeasurable (sliceKernel s F Φ i)
      ((volume : Measure ℝ³).prod (volume.restrict (abox N2 s))) :=
    (hGm.congr hae.symm).aestronglyMeasurable
  rw [integrable_prod_iff hmeas]
  constructor
  · filter_upwards with p
    have hcw : Continuous (fun w : X N2 => sliceKernel s F Φ i (p, w)) := by
      have : (fun w : X N2 => sliceKernel s F Φ i (p, w))
          = fun w : X N2 => F ‖p‖ * ((s ^ 3)⁻¹ * sliceFunFirst s Φ i (p, w)) := rfl
      rw [this]
      exact continuous_const.mul (continuous_const.mul
        (hBcont.comp (continuous_const.prodMk continuous_id)))
    exact ContinuousOn.integrableOn_compact (abox_compact N2 hs) hcw.continuousOn
  · have hcongr : (fun p : ℝ³ => ∫ w, ‖sliceKernel s F Φ i (p, w)‖
        ∂(volume.restrict (abox N2 s)))
        = fun p : ℝ³ => F ‖p‖ * slotTerm s (N1+N2) Φ (Fin.castAdd N2 i) p := by
      funext p
      rw [show (fun w : X N2 => ‖sliceKernel s F Φ i (p, w)‖)
          = fun w : X N2 => sliceKernel s F Φ i (p, w) from by
        funext w
        exact Real.norm_of_nonneg (mul_nonneg (hF _)
          (mul_nonneg (by positivity) (integral_nonneg (fun u => sq_nonneg _))))]
      exact integral_sliceKernel_eq hs F N1 N2 hΦ i p
    rw [hcongr]
    exact integrable_slotForm_of_hint hs hF hint hΦ (Fin.castAdd N2 i)

/-- The second-block slice kernel — in its `p`-first orientation — is integrable
on the product of the `p`-space and the frozen box. -/
lemma integrable_sliceKernelLast {s : ℝ} (hs : 0 < s) {F : ℝ → ℝ} (hF : ∀ r, 0 ≤ F r)
    (hint : ∀ (N : ℕ) (Ψ : X N → ℝ), ContDiff ℝ ∞ Ψ → Integrable (slotSum s F N Ψ))
    (N1 N2 : ℕ) {Φ : X (N1 + N2) → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (j : Fin N2) :
    Integrable (fun q : ℝ³ × X N1 => sliceKernelLast s F Φ j (q.2, q.1))
      ((volume : Measure ℝ³).prod (volume.restrict (abox N1 s))) := by
  have hφ : Integrable (slotSum s F (N1+N2) Φ) := hint (N1+N2) Φ hΦ
  have hScont : Continuous (slotDiag s (N1+N2) Φ) := continuous_slotDiag hs hΦ.continuous
  have hBcont : Continuous (sliceFunLast s Φ j) := continuous_sliceFunLast hs N1 N2 hΦ j
  have hBcont' : Continuous (fun q : ℝ³ × X N1 => sliceFunLast s Φ j (q.2, q.1)) :=
    hBcont.comp continuous_swap
  set bad : Set (ℝ³ × X N1) :=
    {q | slotDiag s (N1+N2) Φ q.1 = 0 ∧ sliceFunLast s Φ j (q.2, q.1) ≠ 0} with hbaddef
  have hbadm : MeasurableSet bad := by
    rw [hbaddef]
    exact ((hScont.measurable.comp continuous_fst.measurable) (measurableSet_singleton 0)).inter
      (hBcont'.measurable (measurableSet_singleton (0:ℝ)).compl)
  have hbadzero : ((volume : Measure ℝ³).prod (volume.restrict (abox N1 s))) bad = 0 := by
    refine le_antisymm ?_ zero_le
    calc ((volume : Measure ℝ³).prod (volume.restrict (abox N1 s))) bad
        ≤ ∫⁻ p, (volume.restrict (abox N1 s)) (Prod.mk p ⁻¹' bad) ∂(volume : Measure ℝ³) :=
          Measure.prod_apply_le hbadm
      _ = 0 := by
        have hfun : (fun p : ℝ³ => (volume.restrict (abox N1 s)) (Prod.mk p ⁻¹' bad))
            = fun _ => (0 : ℝ≥0∞) := by
          funext p
          by_cases hp : slotDiag s (N1+N2) Φ p = 0
          · have hset : Prod.mk p ⁻¹' bad = {u : X N1 | sliceFunLast s Φ j (u, p) ≠ 0} := by
              ext u; rw [hbaddef]; simp [hp]
            rw [hset]
            rw [show {u : X N1 | sliceFunLast s Φ j (u, p) ≠ 0}
                = {u : X N1 | ¬ (sliceFunLast s Φ j (u, p) = 0)} from rfl]
            exact ae_iff.mp (sliceFunLast_ae_zero hs N1 N2 hΦ j p hp)
          · have hset : Prod.mk p ⁻¹' bad = (∅ : Set (X N1)) := by
              ext u; rw [hbaddef]; simp [hp]
            rw [hset, measure_empty]
        rw [hfun, lintegral_zero]
  have hbad_ae : ∀ᵐ q ∂((volume : Measure ℝ³).prod (volume.restrict (abox N1 s))),
      ¬ (slotDiag s (N1+N2) Φ q.1 = 0 ∧ sliceFunLast s Φ j (q.2, q.1) ≠ 0) := by
    have : ∀ᵐ q ∂((volume : Measure ℝ³).prod (volume.restrict (abox N1 s))), q ∉ bad := by
      refine MeasureTheory.ae_iff.mpr ?_
      rwa [show {q : ℝ³ × X N1 | ¬ q ∉ bad} = bad from by ext q; simp [not_not]]
    filter_upwards [this] with q hq
    intro hcon
    exact hq hcon
  have hGm : AEMeasurable (fun q : ℝ³ × X N1 =>
      hφ.aestronglyMeasurable.mk (slotSum s F (N1+N2) Φ) q.1 *
        ((s ^ 3)⁻¹ * sliceFunLast s Φ j (q.2, q.1) * (slotDiag s (N1+N2) Φ q.1)⁻¹))
      ((volume : Measure ℝ³).prod (volume.restrict (abox N1 s))) := by
    have h1 : AEMeasurable (fun q : ℝ³ × X N1 =>
        hφ.aestronglyMeasurable.mk (slotSum s F (N1+N2) Φ) q.1)
        ((volume : Measure ℝ³).prod (volume.restrict (abox N1 s))) :=
      hφ.aestronglyMeasurable.stronglyMeasurable_mk.aemeasurable.comp_fst
    have h2 : AEMeasurable (fun q : ℝ³ × X N1 =>
        (s ^ 3)⁻¹ * sliceFunLast s Φ j (q.2, q.1) * (slotDiag s (N1+N2) Φ q.1)⁻¹)
        ((volume : Measure ℝ³).prod (volume.restrict (abox N1 s))) :=
      (continuous_const.mul hBcont').aemeasurable.mul
        ((hScont.measurable.comp continuous_fst.measurable).inv.aemeasurable)
    exact h1.mul h2
  have hae : (fun q : ℝ³ × X N1 => sliceKernelLast s F Φ j (q.2, q.1))
      =ᵐ[((volume : Measure ℝ³).prod (volume.restrict (abox N1 s)))]
      (fun q : ℝ³ × X N1 => hφ.aestronglyMeasurable.mk (slotSum s F (N1+N2) Φ) q.1 *
        ((s ^ 3)⁻¹ * sliceFunLast s Φ j (q.2, q.1) * (slotDiag s (N1+N2) Φ q.1)⁻¹)) := by
    have hgood_ae : ∀ᵐ q ∂((volume : Measure ℝ³).prod (volume.restrict (abox N1 s))),
        hφ.aestronglyMeasurable.mk (slotSum s F (N1+N2) Φ) q.1
          = slotSum s F (N1+N2) Φ q.1 :=
      ae_mk_comp_fst hφ.aestronglyMeasurable
    filter_upwards [hgood_ae, hbad_ae] with q hq1 hq2
    by_cases hS : slotDiag s (N1+N2) Φ q.1 = 0
    · have hB0 : sliceFunLast s Φ j (q.2, q.1) = 0 := by
        by_contra hBne
        exact hq2 ⟨hS, hBne⟩
      rw [sliceKernelLast, hB0]
      simp only [mul_zero, hS, inv_zero, mul_zero]
    · show F ‖q.1‖ * ((s ^ 3)⁻¹ * sliceFunLast s Φ j (q.2, q.1))
          = hφ.aestronglyMeasurable.mk (slotSum s F (N1+N2) Φ) q.1 *
              ((s ^ 3)⁻¹ * sliceFunLast s Φ j (q.2, q.1) * (slotDiag s (N1+N2) Φ q.1)⁻¹)
      rw [hq1]
      show F ‖q.1‖ * ((s ^ 3)⁻¹ * sliceFunLast s Φ j (q.2, q.1))
          = F ‖q.1‖ * slotDiag s (N1+N2) Φ q.1 *
              ((s ^ 3)⁻¹ * sliceFunLast s Φ j (q.2, q.1) * (slotDiag s (N1+N2) Φ q.1)⁻¹)
      field_simp
  have hmeas : AEStronglyMeasurable (fun q : ℝ³ × X N1 => sliceKernelLast s F Φ j (q.2, q.1))
      ((volume : Measure ℝ³).prod (volume.restrict (abox N1 s))) :=
    (hGm.congr hae.symm).aestronglyMeasurable
  rw [integrable_prod_iff hmeas]
  constructor
  · filter_upwards with p
    have hcw : Continuous (fun u : X N1 => sliceKernelLast s F Φ j (u, p)) := by
      have : (fun u : X N1 => sliceKernelLast s F Φ j (u, p))
          = fun u : X N1 => F ‖p‖ * ((s ^ 3)⁻¹ * sliceFunLast s Φ j (u, p)) := rfl
      rw [this]
      exact continuous_const.mul (continuous_const.mul
        (hBcont.comp (continuous_id.prodMk continuous_const)))
    exact ContinuousOn.integrableOn_compact (abox_compact N1 hs) hcw.continuousOn
  · have hcongr : (fun p : ℝ³ => ∫ u, ‖sliceKernelLast s F Φ j (u, p)‖
        ∂(volume.restrict (abox N1 s)))
        = fun p : ℝ³ => F ‖p‖ * slotTerm s (N1+N2) Φ (Fin.natAdd N1 j) p := by
      funext p
      rw [show (fun u : X N1 => ‖sliceKernelLast s F Φ j (u, p)‖)
          = fun u : X N1 => sliceKernelLast s F Φ j (u, p) from by
        funext u
        exact Real.norm_of_nonneg (mul_nonneg (hF _)
          (mul_nonneg (by positivity) (integral_nonneg (fun w => sq_nonneg _))))]
      exact integral_sliceKernelLast_eq hs F N1 N2 hΦ j p
    rw [hcongr]
    exact integrable_slotForm_of_hint hs hF hint hΦ (Fin.natAdd N1 j)

/-! ## 6  The two halves of the block decomposition -/

/-- **First-block half.**  The first-block sum of slot forms of the
`(N₁+N₂)`-particle word is the `w`-integral of the `N₁`-particle word on the
`w`-slices. -/
lemma slotForm_merge_castAdd {s : ℝ} (hs : 0 < s) {F : ℝ → ℝ} (hF : ∀ r, 0 ≤ F r)
    (hint : ∀ (N : ℕ) (Ψ : X N → ℝ), ContDiff ℝ ∞ Ψ → Integrable (slotSum s F N Ψ))
    (N1 N2 : ℕ) {Φ : X (N1 + N2) → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (i : Fin N1) :
    slotForm s F (N1 + N2) Φ (Fin.castAdd N2 i)
      = ∫ w in abox N2 s, slotForm s F N1 (fun u => Φ (mergeBlock N1 N2 (u, w))) i := by
  have hInt := integrable_sliceKernel hs hF hint N1 N2 hΦ i
  calc slotForm s F (N1 + N2) Φ (Fin.castAdd N2 i)
      = ∫ p, (∫ w, sliceKernel s F Φ i (p, w) ∂(volume.restrict (abox N2 s)))
          ∂(volume : Measure ℝ³) := by
        apply integral_congr_ae
        filter_upwards with p
        exact (integral_sliceKernel_eq hs F N1 N2 hΦ i p).symm
    _ = ∫ w, (∫ p, sliceKernel s F Φ i (p, w) ∂(volume : Measure ℝ³))
          ∂(volume.restrict (abox N2 s)) := integral_integral_swap hInt
    _ = ∫ w in abox N2 s, slotForm s F N1 (fun u => Φ (mergeBlock N1 N2 (u, w))) i := by
        apply integral_congr_ae
        filter_upwards with w
        rfl

/-- **Second-block half.**  The second-block sum of slot forms of the
`(N₁+N₂)`-particle word is the `u`-integral of the `N₂`-particle word on the
`u`-slices. -/
lemma slotForm_merge_natAdd {s : ℝ} (hs : 0 < s) {F : ℝ → ℝ} (hF : ∀ r, 0 ≤ F r)
    (hint : ∀ (N : ℕ) (Ψ : X N → ℝ), ContDiff ℝ ∞ Ψ → Integrable (slotSum s F N Ψ))
    (N1 N2 : ℕ) {Φ : X (N1 + N2) → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (j : Fin N2) :
    slotForm s F (N1 + N2) Φ (Fin.natAdd N1 j)
      = ∫ u in abox N1 s, slotForm s F N2 (fun w => Φ (mergeBlock N1 N2 (u, w))) j := by
  have hInt := integrable_sliceKernelLast hs hF hint N1 N2 hΦ j
  calc slotForm s F (N1 + N2) Φ (Fin.natAdd N1 j)
      = ∫ p, (∫ u, sliceKernelLast s F Φ j (u, p) ∂(volume.restrict (abox N1 s)))
          ∂(volume : Measure ℝ³) := by
        apply integral_congr_ae
        filter_upwards with p
        exact (integral_sliceKernelLast_eq hs F N1 N2 hΦ j p).symm
    _ = ∫ u, (∫ p, sliceKernelLast s F Φ j (u, p) ∂(volume : Measure ℝ³))
          ∂(volume.restrict (abox N1 s)) := integral_integral_swap hInt
    _ = ∫ u in abox N1 s, slotForm s F N2 (fun w => Φ (mergeBlock N1 N2 (u, w))) j := by
        apply integral_congr_ae
        filter_upwards with u
        rfl

/-! ## 7  The sum/box-integral manipulations -/

/-- The first-block sum of slot forms is the `w`-integral of the `N₁`-particle
word on the slices. -/
lemma sum_slotForm_first {s : ℝ} (hs : 0 < s) {F : ℝ → ℝ} (hF : ∀ r, 0 ≤ F r)
    (hint : ∀ (N : ℕ) (Ψ : X N → ℝ), ContDiff ℝ ∞ Ψ → Integrable (slotSum s F N Ψ))
    (N1 N2 : ℕ) {Φ : X (N1 + N2) → ℝ} (hΦ : ContDiff ℝ ∞ Φ) :
    (∑ i : Fin N1, ((2 * π) ^ 3)⁻¹ * slotForm s F (N1 + N2) Φ (Fin.castAdd N2 i))
      = ∫ w in abox N2 s, @pDiagForm s F N1 (fun u => Φ (mergeBlock N1 N2 (u, w))) := by
  have hInt : ∀ i : Fin N1, IntegrableOn (fun w : X N2 =>
      slotForm s F N1 (fun u => Φ (mergeBlock N1 N2 (u, w))) i) (abox N2 s) volume :=
    fun i => (integrable_sliceKernel hs hF hint N1 N2 hΦ i).integral_prod_right
  calc (∑ i : Fin N1, ((2 * π) ^ 3)⁻¹ * slotForm s F (N1 + N2) Φ (Fin.castAdd N2 i))
      = ∑ i : Fin N1, ((2 * π) ^ 3)⁻¹ * ∫ w in abox N2 s,
          slotForm s F N1 (fun u => Φ (mergeBlock N1 N2 (u, w))) i := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [slotForm_merge_castAdd hs hF hint N1 N2 hΦ i]
    _ = ((2 * π) ^ 3)⁻¹ * ∑ i : Fin N1, ∫ w in abox N2 s,
          slotForm s F N1 (fun u => Φ (mergeBlock N1 N2 (u, w))) i :=
        (Finset.mul_sum _ _ _).symm
    _ = ((2 * π) ^ 3)⁻¹ * ∫ w in abox N2 s, ∑ i : Fin N1,
          slotForm s F N1 (fun u => Φ (mergeBlock N1 N2 (u, w))) i := by
        rw [integral_finsetSum _ (fun i _ => hInt i)]
    _ = ∫ w in abox N2 s, ((2 * π) ^ 3)⁻¹ * ∑ i : Fin N1,
          slotForm s F N1 (fun u => Φ (mergeBlock N1 N2 (u, w))) i :=
        (integral_const_mul _ _).symm
    _ = ∫ w in abox N2 s, ∑ i : Fin N1, ((2 * π) ^ 3)⁻¹ *
          slotForm s F N1 (fun u => Φ (mergeBlock N1 N2 (u, w))) i := by
        congr 1
        ext w
        rw [Finset.mul_sum]
    _ = ∫ w in abox N2 s, @pDiagForm s F N1 (fun u => Φ (mergeBlock N1 N2 (u, w))) := by
        apply integral_congr_ae
        filter_upwards with w
        exact (pDiagForm_eq_sum_slotForm s F N1 _).symm

/-- The second-block sum of slot forms is the `u`-integral of the `N₂`-particle
word on the slices. -/
lemma sum_slotForm_last {s : ℝ} (hs : 0 < s) {F : ℝ → ℝ} (hF : ∀ r, 0 ≤ F r)
    (hint : ∀ (N : ℕ) (Ψ : X N → ℝ), ContDiff ℝ ∞ Ψ → Integrable (slotSum s F N Ψ))
    (N1 N2 : ℕ) {Φ : X (N1 + N2) → ℝ} (hΦ : ContDiff ℝ ∞ Φ) :
    (∑ j : Fin N2, ((2 * π) ^ 3)⁻¹ * slotForm s F (N1 + N2) Φ (Fin.natAdd N1 j))
      = ∫ u in abox N1 s, @pDiagForm s F N2 (fun w => Φ (mergeBlock N1 N2 (u, w))) := by
  have hInt : ∀ j : Fin N2, IntegrableOn (fun u : X N1 =>
      slotForm s F N2 (fun w => Φ (mergeBlock N1 N2 (u, w))) j) (abox N1 s) volume :=
    fun j => (integrable_sliceKernelLast hs hF hint N1 N2 hΦ j).integral_prod_right
  calc (∑ j : Fin N2, ((2 * π) ^ 3)⁻¹ * slotForm s F (N1 + N2) Φ (Fin.natAdd N1 j))
      = ∑ j : Fin N2, ((2 * π) ^ 3)⁻¹ * ∫ u in abox N1 s,
          slotForm s F N2 (fun w => Φ (mergeBlock N1 N2 (u, w))) j := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [slotForm_merge_natAdd hs hF hint N1 N2 hΦ j]
    _ = ((2 * π) ^ 3)⁻¹ * ∑ j : Fin N2, ∫ u in abox N1 s,
          slotForm s F N2 (fun w => Φ (mergeBlock N1 N2 (u, w))) j :=
        (Finset.mul_sum _ _ _).symm
    _ = ((2 * π) ^ 3)⁻¹ * ∫ u in abox N1 s, ∑ j : Fin N2,
          slotForm s F N2 (fun w => Φ (mergeBlock N1 N2 (u, w))) j := by
        rw [integral_finsetSum _ (fun j _ => hInt j)]
    _ = ∫ u in abox N1 s, ((2 * π) ^ 3)⁻¹ * ∑ j : Fin N2,
          slotForm s F N2 (fun w => Φ (mergeBlock N1 N2 (u, w))) j :=
        (integral_const_mul _ _).symm
    _ = ∫ u in abox N1 s, ∑ j : Fin N2, ((2 * π) ^ 3)⁻¹ *
          slotForm s F N2 (fun w => Φ (mergeBlock N1 N2 (u, w))) j := by
        congr 1
        ext u
        rw [Finset.mul_sum]
    _ = ∫ u in abox N1 s, @pDiagForm s F N2 (fun w => Φ (mergeBlock N1 N2 (u, w))) := by
        apply integral_congr_ae
        filter_upwards with u
        exact (pDiagForm_eq_sum_slotForm s F N2 _).symm

/-! ## 8  The degenerate case `s ≤ 0` -/

/-- For a nonpositive side length the centred box `abox N s` (`N ≠ 0`) is a null
set (a point when `s = 0`, empty when `s < 0`) and `(0³)⁻¹ = 0`, so `pDiagForm`
vanishes identically. -/
lemma pDiagForm_eq_zero_of_nonpos {N : ℕ} {s : ℝ} (hs : s ≤ 0) (F : ℝ → ℝ)
    (Ψ : X N → ℝ) : @pDiagForm s F N Ψ = 0 := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    rw [pDiagForm]
    simp
  · have hvol : (volume : Measure (X N)) (abox N s) = 0 := by
      rcases lt_or_eq_of_le hs with hlt | heq
      · have hInt : Set.Icc (-s / 2) (s / 2) = (∅ : Set ℝ) :=
          Set.Icc_eq_empty (by linarith)
        have hacube : acube s = (∅ : Set ℝ³) := by
          apply Set.eq_empty_iff_forall_notMem.mpr
          intro y hy
          rw [mem_acube_iff] at hy
          have h0 := hy 0
          rw [hInt] at h0
          exact h0
        have habox : abox N s = (∅ : Set (X N)) := by
          apply Set.eq_empty_iff_forall_notMem.mpr
          intro x hx
          rw [mem_abox_iff] at hx
          have h0 := hx ⟨0, hN⟩
          rw [hacube] at h0
          exact h0
        rw [habox, measure_empty]
      · rw [heq, abox_volume N 0 le_rfl]
        have hpow : ((0 : ℝ) ^ 3) ^ N = 0 := by
          rw [zero_pow (by norm_num : (3 : ℕ) ≠ 0), zero_pow (Nat.pos_iff_ne_zero.mp hN)]
        rw [hpow, ENNReal.ofReal_zero]
    have hz : (volume : Measure (X N)).restrict (abox N s) = 0 :=
      Measure.restrict_eq_zero.mpr hvol
    rw [pDiagForm]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [hz]
    have : (fun p : ℝ³ => F ‖p‖ * ((s ^ 3)⁻¹ * ∫ x, ‖pSlotAmp s p Ψ i x‖ ^ 2
        ∂(0 : Measure (X N)))) = fun _ => (0 : ℝ) := by
      funext p
      rw [MeasureTheory.integral_zero_measure, mul_zero, mul_zero]
    rw [this]
    simp

/-! ## 9  The theorem -/

theorem slotSplit_pDiagForm_smooth (s : ℝ) (F : ℝ → ℝ) (hF : ∀ r, 0 ≤ F r)
    (hint : ∀ (N : ℕ) (Ψ : Submission.BoseGases.X N → ℝ), ContDiff ℝ ∞ Ψ →
      MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
        F ‖p‖ * ∑ i : Fin N, (s ^ 3)⁻¹ *
          ∫ x in Submission.BoseGases.abox N s,
            ‖Submission.BoseGases.pSlotAmp s p Ψ i x‖ ^ 2)) :
    @Work.KinPSuperadd.SlotSplit s
      (fun (N : ℕ) (Φ : Submission.BoseGases.X N → ℝ)
        => @Submission.BoseGases.pDiagForm s F N Φ) := by
  by_cases hs : 0 < s
  · have hint' : ∀ (N : ℕ) (Ψ : X N → ℝ), ContDiff ℝ ∞ Ψ → Integrable (slotSum s F N Ψ) :=
      fun N Ψ hΨ => hint N Ψ hΨ
    refine ⟨?_, ?_, ?_⟩
    · intro N1 N2 Φ hΦ
      rw [show @Submission.BoseGases.pDiagForm s F (N1 + N2) Φ
            = ∑ k : Fin (N1 + N2), ((2 * π) ^ 3)⁻¹ * slotForm s F (N1 + N2) Φ k
          from pDiagForm_eq_sum_slotForm s F (N1 + N2) Φ]
      rw [Fin.sum_univ_add]
      rw [sum_slotForm_first hs hF hint' N1 N2 hΦ, sum_slotForm_last hs hF hint' N1 N2 hΦ]
    · intro N1 N2 Φ hΦ
      have hsum : Integrable (fun w : X N2 => ∑ i : Fin N1, ((2 * π) ^ 3)⁻¹ *
          slotForm s F N1 (fun u => Φ (mergeBlock N1 N2 (u, w))) i)
          (volume.restrict (abox N2 s)) :=
        integrable_finsetSum Finset.univ (fun i _ =>
          (((integrable_sliceKernel hs hF hint' N1 N2 hΦ i).integral_prod_right).const_mul _))
      refine hsum.congr ?_
      filter_upwards with w
      exact (pDiagForm_eq_sum_slotForm s F N1 _).symm
    · intro N1 N2 Φ hΦ
      have hsum : Integrable (fun u : X N1 => ∑ j : Fin N2, ((2 * π) ^ 3)⁻¹ *
          slotForm s F N2 (fun w => Φ (mergeBlock N1 N2 (u, w))) j)
          (volume.restrict (abox N1 s)) :=
        integrable_finsetSum Finset.univ (fun j _ =>
          (((integrable_sliceKernelLast hs hF hint' N1 N2 hΦ j).integral_prod_right).const_mul _))
      refine hsum.congr ?_
      filter_upwards with u
      exact (pDiagForm_eq_sum_slotForm s F N2 _).symm
  · have hsle : s ≤ 0 := le_of_not_gt hs
    refine ⟨?_, ?_, ?_⟩
    · intro N1 N2 Φ hΦ
      have h1 : (∫ w in abox N2 s, @Submission.BoseGases.pDiagForm s F N1
          (fun u => Φ (mergeBlock N1 N2 (u, w)))) = 0 := by
        rw [show (fun w : X N2 => @Submission.BoseGases.pDiagForm s F N1
            (fun u => Φ (mergeBlock N1 N2 (u, w)))) = fun _ => (0 : ℝ) from by
          funext w; exact pDiagForm_eq_zero_of_nonpos hsle F _]
        simp
      have h2 : (∫ u in abox N1 s, @Submission.BoseGases.pDiagForm s F N2
          (fun w => Φ (mergeBlock N1 N2 (u, w)))) = 0 := by
        rw [show (fun u : X N1 => @Submission.BoseGases.pDiagForm s F N2
            (fun w => Φ (mergeBlock N1 N2 (u, w)))) = fun _ => (0 : ℝ) from by
          funext u; exact pDiagForm_eq_zero_of_nonpos hsle F _]
        simp
      rw [pDiagForm_eq_zero_of_nonpos hsle F Φ, h1, h2, add_zero]
    · intro N1 N2 Φ hΦ
      rw [show (fun w : X N2 => @Submission.BoseGases.pDiagForm s F N1
          (fun u => Φ (mergeBlock N1 N2 (u, w)))) = fun _ => (0 : ℝ) from by
        funext w; exact pDiagForm_eq_zero_of_nonpos hsle F _]
      exact integrableOn_zero
    · intro N1 N2 Φ hΦ
      rw [show (fun u : X N1 => @Submission.BoseGases.pDiagForm s F N2
          (fun w => Φ (mergeBlock N1 N2 (u, w)))) = fun _ => (0 : ℝ) from by
        funext u; exact pDiagForm_eq_zero_of_nonpos hsle F _]
      exact integrableOn_zero

end Work.KinPSuperadd
