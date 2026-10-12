import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.KinPSuperadd.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `SlotSplit` for `pDiagForm` — shared definitions and elementary lemmas

This module collects the definitions and the elementary (sorry-free) lemmas that
the proof of `Work.KinPSuperadd.slotSplit_pDiagForm` — and the pieces of it
delegated to colleagues — are stated in terms of:

* `slotTerm s N Ψ i p = (s³)⁻¹∫_{abox N s}‖pSlotAmp s p Ψ i x‖²` — the per-slot,
  per-`p` content, exactly the summand of `submission.BoseGases.pDiagForm`;
* `slotDiag s N Ψ p = Σ_i slotTerm …` — the sum of the slot contents at fixed `p`
  (the integrand of the hypothesis `hint` of the theorem, modulo the factor
  `F ‖p‖`);
* `slotSum s F N Ψ p = F ‖p‖ * slotDiag …` — the `hint` integrand itself;
* `slotForm s F N Ψ i = ∫_p F ‖p‖ · slotTerm …` — one summand of `pDiagForm`.

Also here: continuity of the block reassembly `mergeBlock`, the compatibility of
`Function.update` with `mergeBlock`, and the resulting **slice identities** for
the slot amplitudes (`pSlotAmp_merge_castAdd` / `pSlotAmp_merge_natAdd`), which
say that the slot amplitude of a merged configuration is the slot amplitude of
the corresponding slice — the pointwise core of the block decomposition.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.KinPSuperadd

open Submission BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1  The per-slot functionals -/

/-- The per-slot, per-`p` content `(s³)⁻¹∫_{abox N s}‖pSlotAmp s p Ψ i x‖²`: the
summand of `pDiagForm` inside its `p`-integral. -/
noncomputable def slotTerm (s : ℝ) (N : ℕ) (Ψ : X N → ℝ) (i : Fin N) (p : ℝ³) : ℝ :=
  (s ^ 3)⁻¹ * ∫ x in abox N s, ‖pSlotAmp s p Ψ i x‖ ^ 2

/-- The sum over the slots of `slotTerm` at fixed `p`: the integrand of the
hypothesis `hint`, up to the prefactor `F ‖p‖`. -/
noncomputable def slotDiag (s : ℝ) (N : ℕ) (Ψ : X N → ℝ) (p : ℝ³) : ℝ :=
  ∑ i : Fin N, slotTerm s N Ψ i p

/-- The `hint` integrand `F ‖p‖ * Σ_i slotTerm …`. -/
noncomputable def slotSum (s : ℝ) (F : ℝ → ℝ) (N : ℕ) (Ψ : X N → ℝ) (p : ℝ³) : ℝ :=
  F ‖p‖ * slotDiag s N Ψ p

/-- One summand of `pDiagForm`: `∫_p F ‖p‖ · slotTerm s N Ψ i p`. -/
noncomputable def slotForm (s : ℝ) (F : ℝ → ℝ) (N : ℕ) (Ψ : X N → ℝ) (i : Fin N) : ℝ :=
  ∫ p : ℝ³, F ‖p‖ * slotTerm s N Ψ i p

lemma slotTerm_def (s : ℝ) (N : ℕ) (Ψ : X N → ℝ) (i : Fin N) (p : ℝ³) :
    slotTerm s N Ψ i p = (s ^ 3)⁻¹ * ∫ x in abox N s, ‖pSlotAmp s p Ψ i x‖ ^ 2 := rfl

lemma slotDiag_def (s : ℝ) (N : ℕ) (Ψ : X N → ℝ) (p : ℝ³) :
    slotDiag s N Ψ p
      = ∑ i : Fin N, (s ^ 3)⁻¹ * ∫ x in abox N s, ‖pSlotAmp s p Ψ i x‖ ^ 2 := rfl

lemma slotSum_def (s : ℝ) (F : ℝ → ℝ) (N : ℕ) (Ψ : X N → ℝ) (p : ℝ³) :
    slotSum s F N Ψ p = F ‖p‖ * ∑ i : Fin N,
      (s ^ 3)⁻¹ * ∫ x in abox N s, ‖pSlotAmp s p Ψ i x‖ ^ 2 := rfl

/-- `pDiagForm` is the sum of the slot forms. -/
lemma pDiagForm_eq_sum_slotForm (s : ℝ) (F : ℝ → ℝ) (N : ℕ) (Ψ : X N → ℝ) :
    @pDiagForm s F N Ψ = ∑ i : Fin N, ((2 * π) ^ 3)⁻¹ * slotForm s F N Ψ i := rfl

/-! ## 2  Continuity of `mergeBlock` and its compatibility with updates -/

/-- `mergeBlock N1 N2 : X N1 × X N2 → X (N1+N2)` is continuous (each coordinate
is one of the two block coordinates). -/
lemma continuous_mergeBlock (N1 N2 : ℕ) : Continuous (mergeBlock N1 N2) := by
  rw [continuous_pi_iff]
  intro k
  by_cases h : (k : ℕ) < N1
  · let i : Fin N1 := ⟨k.val, h⟩
    have hk : k = Fin.castAdd N2 i := by ext; simp [i]
    rw [hk]
    have hfun : (fun p : X N1 × X N2 => mergeBlock N1 N2 p (Fin.castAdd N2 i)) =
        fun p => p.1 i := by
      funext p; simp [mergeBlock]
    rw [hfun]
    exact (continuous_apply i).comp continuous_fst
  · let j : Fin N2 := ⟨k.val - N1, by omega⟩
    have hkN : k = Fin.natAdd N1 j := by ext; simp [j]; omega
    rw [hkN]
    have hfun : (fun p : X N1 × X N2 => mergeBlock N1 N2 p (Fin.natAdd N1 j)) =
        fun p => p.2 j := by
      funext p; simp [mergeBlock]
    rw [hfun]
    exact (continuous_apply j).comp continuous_snd

/-- Updating a first-block coordinate of a merged configuration updates the
first block. -/
lemma upd_mergeBlock_first (N1 N2 : ℕ) (u : X N1) (w : X N2) (i : Fin N1) (z : ℝ³) :
    Function.update (mergeBlock N1 N2 (u, w)) (Fin.castAdd N2 i) z
      = mergeBlock N1 N2 (Function.update u i z, w) := by
  rw [← mergeBlock_eq N1 N2 (Function.update (mergeBlock N1 N2 (u, w)) (Fin.castAdd N2 i) z)]
  simp [firstBlock_update, lastBlock_update_first, mergeBlock_first, mergeBlock_last]

/-- Updating a second-block coordinate of a merged configuration updates the
second block. -/
lemma upd_mergeBlock_last (N1 N2 : ℕ) (u : X N1) (w : X N2) (j : Fin N2) (z : ℝ³) :
    Function.update (mergeBlock N1 N2 (u, w)) (Fin.natAdd N1 j) z
      = mergeBlock N1 N2 (u, Function.update w j z) := by
  rw [← mergeBlock_eq N1 N2 (Function.update (mergeBlock N1 N2 (u, w)) (Fin.natAdd N1 j) z)]
  simp [firstBlock_update_last, lastBlock_update_last, mergeBlock_first, mergeBlock_last]

/-! ## 3  The slot amplitude of a merged configuration is the slice amplitude -/

/-- The first-block slot amplitude of a merged configuration is the slot
amplitude of the `w`-slice. -/
lemma pSlotAmp_merge_castAdd (s : ℝ) (p : ℝ³) {N1 N2 : ℕ} (Φ : X (N1+N2) → ℝ)
    (u : X N1) (w : X N2) (i : Fin N1) :
    pSlotAmp s p Φ (Fin.castAdd N2 i) (mergeBlock N1 N2 (u, w))
      = pSlotAmp s p (fun u' => Φ (mergeBlock N1 N2 (u', w))) i u := by
  simp only [pSlotAmp, upd_mergeBlock_first]

/-- The second-block slot amplitude of a merged configuration is the slot
amplitude of the `u`-slice. -/
lemma pSlotAmp_merge_natAdd (s : ℝ) (p : ℝ³) {N1 N2 : ℕ} (Φ : X (N1+N2) → ℝ)
    (u : X N1) (w : X N2) (j : Fin N2) :
    pSlotAmp s p Φ (Fin.natAdd N1 j) (mergeBlock N1 N2 (u, w))
      = pSlotAmp s p (fun w' => Φ (mergeBlock N1 N2 (u, w'))) j w := by
  simp only [pSlotAmp, upd_mergeBlock_last]

/-! ## 4  Integrability of the squared slot amplitudes -/

/-- The squared slot amplitude of a continuous state is integrable over the
centred box. -/
lemma integrableOn_pSlotAmp_sq (s : ℝ) (hs : 0 < s) (p : ℝ³) {N : ℕ} {Ψ : X N → ℝ}
    (hΨ : Continuous Ψ) (k : Fin N) :
    IntegrableOn (fun x : X N => ‖pSlotAmp s p Ψ k x‖ ^ 2) (abox N s) volume := by
  have hcont : Continuous (fun x : X N => ‖pSlotAmp s p Ψ k x‖ ^ 2) :=
    (continuous_norm.comp
      ((Work.SmallBoxBridge.Cauchy.continuous_pSlotAmp_pair hs hΨ k).comp
        (continuous_const.prodMk continuous_id))).pow 2
  exact ContinuousOn.integrableOn_compact (abox_compact N hs) hcont.continuousOn

/-! ## 5  The slice functionals of the block decomposition -/

/-- The frozen-`w` slice functional of the first block:
`(p,w) ↦ ∫_{abox N₁ s}‖pSlotAmp s p (w-slice Φ) i u‖²`. -/
noncomputable def sliceFunFirst (s : ℝ) {N1 N2 : ℕ} (Φ : X (N1+N2) → ℝ) (i : Fin N1)
    (q : ℝ³ × X N2) : ℝ :=
  ∫ u in abox N1 s,
    ‖pSlotAmp s q.1 (fun u' => Φ (mergeBlock N1 N2 (u', q.2))) i u‖ ^ 2

/-- The frozen-`u` slice functional of the second block:
`(u,p) ↦ ∫_{abox N₂ s}‖pSlotAmp s p (u-slice Φ) j w‖²`. -/
noncomputable def sliceFunLast (s : ℝ) {N1 N2 : ℕ} (Φ : X (N1+N2) → ℝ) (j : Fin N2)
    (q : X N1 × ℝ³) : ℝ :=
  ∫ w in abox N2 s,
    ‖pSlotAmp s q.2 (fun w' => Φ (mergeBlock N1 N2 (q.1, w'))) j w‖ ^ 2

/-- The first-block slice kernel `F ‖p‖ * (s³)⁻¹ * (slice functional)`. -/
noncomputable def sliceKernel (s : ℝ) (F : ℝ → ℝ) {N1 N2 : ℕ} (Φ : X (N1+N2) → ℝ)
    (i : Fin N1) (q : ℝ³ × X N2) : ℝ :=
  F ‖q.1‖ * ((s ^ 3)⁻¹ * sliceFunFirst s Φ i q)

/-- The second-block slice kernel `F ‖p‖ * (s³)⁻¹ * (slice functional)`. -/
noncomputable def sliceKernelLast (s : ℝ) (F : ℝ → ℝ) {N1 N2 : ℕ} (Φ : X (N1+N2) → ℝ)
    (j : Fin N2) (q : X N1 × ℝ³) : ℝ :=
  F ‖q.2‖ * ((s ^ 3)⁻¹ * sliceFunLast s Φ j q)

end Work.KinPSuperadd
