import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.KinPSuperadd.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `SlotSplit` for the diagonal (`pModeDiagonal`) mode word

`Submission.BoseGases.pModeDiagonal s p Ψ` is the *diagonal* (one-particle-sum)
transcription of the corpus per-mode content `P_{u_p} + P_{v_p}`:

    pModeDiagonal s p Ψ = (s³)⁻¹ Σ_i ∫_{abox N s} ‖pSlotAmp s p Ψ i x‖² ,

i.e. the quadratic form of the one-body operator `Q_Bχ_B|qMode⟩⟨qMode|χ_BQ_B`
summed over the `N` slots — as opposed to `pModeContent`, whose per-slot
amplitudes are first summed and only then squared (the square of a sum, which
does *not* decouple over groups of particles).

This module proves the block-splittability (`SlotSplit s`) of that word: the
one-particle sum commutes with the block decomposition of the particle labels.

The proof has two halves.

* For `0 < s` the block split of the centred box `abox (N₁+N₂) s` is the
  product `abox N₁ s × abox N₂ s` (`Submission.BoseGases.aboxFubini` /
  `aboxFubini_swapped`), and for a slot `i` of the first block the slot
  amplitude of the `(N₁+N₂)`-particle state at a merged configuration
  `mergeBlock (u,w)` is the slot amplitude of the `w`-slice at `u`
  (`pSlotAmp_merge_castAdd`), and symmetrically for the second block
  (`pSlotAmp_merge_natAdd`).  Summing over the slots of each block
  (`Fin.sum_univ_add`) gives the two identities `pModeDiagonal_sum_first` /
  `pModeDiagonal_sum_last`, which are exactly the two summands of `SlotSplit`.
  The two slice-integrability fields follow from continuity of the slice
  amplitude in the frozen variable (`continuous_pModeDiagonal_slice1/2`), which
  is `continuous_parametric_integral_of_continuous` applied to a jointly
  continuous integrand.

* For `s ≤ 0` every centred box `abox N s` with `N ≠ 0` is a null set (a
  point when `s = 0`, empty when `s < 0`), so `pModeDiagonal` vanishes
  identically (`pModeDiagonal_eq_zero_of_nonpos`) and all three fields of
  `SlotSplit` are trivial.

In particular the verdict of `KinPSuperadd/Defs.lean` (`Obstruction.lean`) —
that the *square-of-a-sum* word `modeP`/`pModeContent` is **not**
block-splittable — is not inherited by the diagonal word: the cross-group
interference that obstructs the former is absent here.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators

namespace Work.KinPSuperadd

open Submission BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1  Elementary infrastructure: continuity of `mergeBlock`, block updates -/

/-- `mergeBlock N1 N2 : X N1 × X N2 → X (N1+N2)` is continuous (it is the
reassembly of two blocks of coordinates). -/
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
first block (`mergeBlock` of the updated blocks). -/
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

/-! ## 2  The slot amplitude of a merged configuration is the slice amplitude -/

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

/-! ## 3  Integrability and continuity of the slice amplitudes -/

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

/-- Joint continuity of the first-block slice amplitude
`(w,u) ↦ pSlotAmp s p (w-slice Φ) i u`. -/
lemma continuous_pSlotAmp_slice1 (s : ℝ) (hs : 0 < s) (p : ℝ³) {N1 N2 : ℕ} {Φ : X (N1+N2) → ℝ}
    (hΦ : Continuous Φ) (i : Fin N1) :
    Continuous (fun q : X N2 × X N1 =>
      pSlotAmp s p (fun u' => Φ (mergeBlock N1 N2 (u', q.1))) i q.2) := by
  have h1 : Continuous (fun q : X N2 × X N1 => ∫ z in acube s,
      qMode s p z * (Φ (mergeBlock N1 N2 (Function.update q.2 i z, q.1)) : ℂ)) := by
    refine continuous_parametric_integral_of_continuous
      (μ := (volume : Measure ℝ³))
      (f := fun (q : X N2 × X N1) (z : ℝ³) =>
        qMode s p z * (Φ (mergeBlock N1 N2 (Function.update q.2 i z, q.1)) : ℂ)) ?_
      (acube_compact hs)
    rw [show Function.uncurry (fun (q : X N2 × X N1) (z : ℝ³) =>
          qMode s p z * (Φ (mergeBlock N1 N2 (Function.update q.2 i z, q.1)) : ℂ))
        = fun r : (X N2 × X N1) × ℝ³ =>
            qMode s p r.2 * (Φ (mergeBlock N1 N2 (Function.update r.1.2 i r.2, r.1.1)) : ℂ)
        from rfl]
    have hA : Continuous fun r : (X N2 × X N1) × ℝ³ => qMode s p r.2 :=
      (continuous_qMode (ℓ := s) p).comp continuous_snd
    have hB : Continuous fun r : (X N2 × X N1) × ℝ³ =>
        Φ (mergeBlock N1 N2 (Function.update r.1.2 i r.2, r.1.1)) :=
      hΦ.comp ((continuous_mergeBlock N1 N2).comp
        (((continuous_update (A := fun _ : Fin N1 => ℝ³) i).comp
          ((continuous_snd.comp continuous_fst).prodMk continuous_snd)).prodMk
            (continuous_fst.comp continuous_fst)))
    exact hA.mul (Complex.continuous_ofReal.comp hB)
  simpa only [pSlotAmp] using h1

/-- Joint continuity of the second-block slice amplitude
`(u,w) ↦ pSlotAmp s p (u-slice Φ) j w`. -/
lemma continuous_pSlotAmp_slice2 (s : ℝ) (hs : 0 < s) (p : ℝ³) {N1 N2 : ℕ} {Φ : X (N1+N2) → ℝ}
    (hΦ : Continuous Φ) (j : Fin N2) :
    Continuous (fun q : X N1 × X N2 =>
      pSlotAmp s p (fun w' => Φ (mergeBlock N1 N2 (q.1, w'))) j q.2) := by
  have h1 : Continuous (fun q : X N1 × X N2 => ∫ z in acube s,
      qMode s p z * (Φ (mergeBlock N1 N2 (q.1, Function.update q.2 j z)) : ℂ)) := by
    refine continuous_parametric_integral_of_continuous
      (μ := (volume : Measure ℝ³))
      (f := fun (q : X N1 × X N2) (z : ℝ³) =>
        qMode s p z * (Φ (mergeBlock N1 N2 (q.1, Function.update q.2 j z)) : ℂ)) ?_
      (acube_compact hs)
    rw [show Function.uncurry (fun (q : X N1 × X N2) (z : ℝ³) =>
          qMode s p z * (Φ (mergeBlock N1 N2 (q.1, Function.update q.2 j z)) : ℂ))
        = fun r : (X N1 × X N2) × ℝ³ =>
            qMode s p r.2 * (Φ (mergeBlock N1 N2 (r.1.1, Function.update r.1.2 j r.2)) : ℂ)
        from rfl]
    have hA : Continuous fun r : (X N1 × X N2) × ℝ³ => qMode s p r.2 :=
      (continuous_qMode (ℓ := s) p).comp continuous_snd
    have hB : Continuous fun r : (X N1 × X N2) × ℝ³ =>
        Φ (mergeBlock N1 N2 (r.1.1, Function.update r.1.2 j r.2)) :=
      hΦ.comp ((continuous_mergeBlock N1 N2).comp
        ((continuous_fst.comp continuous_fst).prodMk
          ((continuous_update (A := fun _ : Fin N2 => ℝ³) j).comp
            ((continuous_snd.comp continuous_fst).prodMk continuous_snd))))
    exact hA.mul (Complex.continuous_ofReal.comp hB)
  simpa only [pSlotAmp] using h1

/-- Continuity in the frozen variable of the first-block slice integral. -/
lemma continuous_integral_slice1 (s : ℝ) (hs : 0 < s) (p : ℝ³) {N1 N2 : ℕ}
    {Φ : X (N1+N2) → ℝ} (hΦ : Continuous Φ) (i : Fin N1) :
    Continuous (fun w : X N2 => ∫ u in abox N1 s,
      ‖pSlotAmp s p (fun u' => Φ (mergeBlock N1 N2 (u', w))) i u‖ ^ 2) := by
  refine continuous_parametric_integral_of_continuous
    (μ := (volume : Measure (X N1)))
    (f := fun (w : X N2) (u : X N1) =>
      ‖pSlotAmp s p (fun u' => Φ (mergeBlock N1 N2 (u', w))) i u‖ ^ 2) ?_
    (abox_compact N1 hs)
  rw [show Function.uncurry (fun (w : X N2) (u : X N1) =>
        ‖pSlotAmp s p (fun u' => Φ (mergeBlock N1 N2 (u', w))) i u‖ ^ 2)
      = fun q : X N2 × X N1 =>
          ‖pSlotAmp s p (fun u' => Φ (mergeBlock N1 N2 (u', q.1))) i q.2‖ ^ 2 from rfl]
  exact (continuous_norm.comp (continuous_pSlotAmp_slice1 s hs p hΦ i)).pow 2

/-- Continuity in the frozen variable of the second-block slice integral. -/
lemma continuous_integral_slice2 (s : ℝ) (hs : 0 < s) (p : ℝ³) {N1 N2 : ℕ}
    {Φ : X (N1+N2) → ℝ} (hΦ : Continuous Φ) (j : Fin N2) :
    Continuous (fun u : X N1 => ∫ w in abox N2 s,
      ‖pSlotAmp s p (fun w' => Φ (mergeBlock N1 N2 (u, w'))) j w‖ ^ 2) := by
  refine continuous_parametric_integral_of_continuous
    (μ := (volume : Measure (X N2)))
    (f := fun (u : X N1) (w : X N2) =>
      ‖pSlotAmp s p (fun w' => Φ (mergeBlock N1 N2 (u, w'))) j w‖ ^ 2) ?_
    (abox_compact N2 hs)
  rw [show Function.uncurry (fun (u : X N1) (w : X N2) =>
        ‖pSlotAmp s p (fun w' => Φ (mergeBlock N1 N2 (u, w'))) j w‖ ^ 2)
      = fun q : X N1 × X N2 =>
          ‖pSlotAmp s p (fun w' => Φ (mergeBlock N1 N2 (q.1, w'))) j q.2‖ ^ 2 from rfl]
  exact (continuous_norm.comp (continuous_pSlotAmp_slice2 s hs p hΦ j)).pow 2

/-- Continuity of the first-block slice word `w ↦ pModeDiagonal` of the
`w`-slice (the `int₁` field of `SlotSplit`). -/
lemma continuous_pModeDiagonal_slice1 (s : ℝ) (hs : 0 < s) (p : ℝ³) {N1 N2 : ℕ}
    {Φ : X (N1+N2) → ℝ} (hΦ : Continuous Φ) :
    Continuous (fun w : X N2 => pModeDiagonal s p (fun u => Φ (mergeBlock N1 N2 (u, w)))) := by
  have h : (fun w : X N2 => pModeDiagonal s p (fun u => Φ (mergeBlock N1 N2 (u, w))))
      = fun w : X N2 => (s ^ 3)⁻¹ * ∑ i : Fin N1, ∫ u in abox N1 s,
          ‖pSlotAmp s p (fun u' => Φ (mergeBlock N1 N2 (u', w))) i u‖ ^ 2 := rfl
  rw [h]
  exact continuous_const.mul
    (continuous_finsetSum Finset.univ (fun i _ => continuous_integral_slice1 s hs p hΦ i))

/-- Continuity of the second-block slice word `u ↦ pModeDiagonal` of the
`u`-slice (the `int₂` field of `SlotSplit`). -/
lemma continuous_pModeDiagonal_slice2 (s : ℝ) (hs : 0 < s) (p : ℝ³) {N1 N2 : ℕ}
    {Φ : X (N1+N2) → ℝ} (hΦ : Continuous Φ) :
    Continuous (fun u : X N1 => pModeDiagonal s p (fun w => Φ (mergeBlock N1 N2 (u, w)))) := by
  have h : (fun u : X N1 => pModeDiagonal s p (fun w => Φ (mergeBlock N1 N2 (u, w))))
      = fun u : X N1 => (s ^ 3)⁻¹ * ∑ j : Fin N2, ∫ w in abox N2 s,
          ‖pSlotAmp s p (fun w' => Φ (mergeBlock N1 N2 (u, w'))) j w‖ ^ 2 := rfl
  rw [h]
  exact continuous_const.mul
    (continuous_finsetSum Finset.univ (fun j _ => continuous_integral_slice2 s hs p hΦ j))

/-! ## 4  The two halves of the block decomposition -/

/-- **First-block half of the block decomposition.**  The sum of the first-block
slot integrals of the `(N₁+N₂)`-particle word equals the `w`-integral of the
`N₁`-particle word on the `w`-slices. -/
lemma pModeDiagonal_sum_first (s : ℝ) (hs : 0 < s) (p : ℝ³) {N1 N2 : ℕ} {Φ : X (N1+N2) → ℝ}
    (hΦ : Continuous Φ) :
    (s ^ 3)⁻¹ * (∑ i : Fin N1, ∫ x in abox (N1+N2) s,
        ‖pSlotAmp s p Φ (Fin.castAdd N2 i) x‖ ^ 2)
      = ∫ w in abox N2 s, pModeDiagonal s p (fun u => Φ (mergeBlock N1 N2 (u, w))) := by
  have hI : ∀ i : Fin N1,
      (∫ x in abox (N1+N2) s, ‖pSlotAmp s p Φ (Fin.castAdd N2 i) x‖ ^ 2)
        = ∫ w in abox N2 s, ∫ u in abox N1 s,
            ‖pSlotAmp s p (fun u' => Φ (mergeBlock N1 N2 (u', w))) i u‖ ^ 2 := by
    intro i
    rw [← aboxFubini_swapped (N1 := N1) (N2 := N2) s
      (fun x => ‖pSlotAmp s p Φ (Fin.castAdd N2 i) x‖ ^ 2)
      (integrableOn_pSlotAmp_sq s hs p hΦ (Fin.castAdd N2 i))]
    apply integral_congr_ae
    filter_upwards with w
    apply integral_congr_ae
    filter_upwards with u
    rw [pSlotAmp_merge_castAdd]
  have hintW : ∀ i : Fin N1, IntegrableOn (fun w : X N2 => ∫ u in abox N1 s,
      ‖pSlotAmp s p (fun u' => Φ (mergeBlock N1 N2 (u', w))) i u‖ ^ 2) (abox N2 s) volume :=
    fun i => ContinuousOn.integrableOn_compact (abox_compact N2 hs)
      (continuous_integral_slice1 s hs p hΦ i).continuousOn
  calc (s ^ 3)⁻¹ * (∑ i : Fin N1, ∫ x in abox (N1+N2) s,
          ‖pSlotAmp s p Φ (Fin.castAdd N2 i) x‖ ^ 2)
      = (s ^ 3)⁻¹ * (∑ i : Fin N1, ∫ w in abox N2 s, ∫ u in abox N1 s,
          ‖pSlotAmp s p (fun u' => Φ (mergeBlock N1 N2 (u', w))) i u‖ ^ 2) := by
        congr 1
        exact Finset.sum_congr rfl (fun i _ => hI i)
    _ = (s ^ 3)⁻¹ * (∫ w in abox N2 s, ∑ i : Fin N1, ∫ u in abox N1 s,
          ‖pSlotAmp s p (fun u' => Φ (mergeBlock N1 N2 (u', w))) i u‖ ^ 2) := by
        congr 1
        exact (integral_finsetSum Finset.univ (fun i _ => hintW i)).symm
    _ = ∫ w in abox N2 s, (s ^ 3)⁻¹ * (∑ i : Fin N1, ∫ u in abox N1 s,
          ‖pSlotAmp s p (fun u' => Φ (mergeBlock N1 N2 (u', w))) i u‖ ^ 2) :=
        (integral_const_mul _ _).symm
    _ = ∫ w in abox N2 s, pModeDiagonal s p (fun u => Φ (mergeBlock N1 N2 (u, w))) := by
        apply integral_congr_ae
        filter_upwards with w
        rfl

/-- **Second-block half of the block decomposition.**  The sum of the
second-block slot integrals of the `(N₁+N₂)`-particle word equals the
`u`-integral of the `N₂`-particle word on the `u`-slices. -/
lemma pModeDiagonal_sum_last (s : ℝ) (hs : 0 < s) (p : ℝ³) {N1 N2 : ℕ} {Φ : X (N1+N2) → ℝ}
    (hΦ : Continuous Φ) :
    (s ^ 3)⁻¹ * (∑ j : Fin N2, ∫ x in abox (N1+N2) s,
        ‖pSlotAmp s p Φ (Fin.natAdd N1 j) x‖ ^ 2)
      = ∫ u in abox N1 s, pModeDiagonal s p (fun w => Φ (mergeBlock N1 N2 (u, w))) := by
  have hI : ∀ j : Fin N2,
      (∫ x in abox (N1+N2) s, ‖pSlotAmp s p Φ (Fin.natAdd N1 j) x‖ ^ 2)
        = ∫ u in abox N1 s, ∫ w in abox N2 s,
            ‖pSlotAmp s p (fun w' => Φ (mergeBlock N1 N2 (u, w'))) j w‖ ^ 2 := by
    intro j
    rw [← aboxFubini (N1 := N1) (N2 := N2) s
      (fun x => ‖pSlotAmp s p Φ (Fin.natAdd N1 j) x‖ ^ 2)
      (integrableOn_pSlotAmp_sq s hs p hΦ (Fin.natAdd N1 j))]
    apply integral_congr_ae
    filter_upwards with u
    apply integral_congr_ae
    filter_upwards with w
    rw [pSlotAmp_merge_natAdd]
  have hintU : ∀ j : Fin N2, IntegrableOn (fun u : X N1 => ∫ w in abox N2 s,
      ‖pSlotAmp s p (fun w' => Φ (mergeBlock N1 N2 (u, w'))) j w‖ ^ 2) (abox N1 s) volume :=
    fun j => ContinuousOn.integrableOn_compact (abox_compact N1 hs)
      (continuous_integral_slice2 s hs p hΦ j).continuousOn
  calc (s ^ 3)⁻¹ * (∑ j : Fin N2, ∫ x in abox (N1+N2) s,
          ‖pSlotAmp s p Φ (Fin.natAdd N1 j) x‖ ^ 2)
      = (s ^ 3)⁻¹ * (∑ j : Fin N2, ∫ u in abox N1 s, ∫ w in abox N2 s,
          ‖pSlotAmp s p (fun w' => Φ (mergeBlock N1 N2 (u, w'))) j w‖ ^ 2) := by
        congr 1
        exact Finset.sum_congr rfl (fun j _ => hI j)
    _ = (s ^ 3)⁻¹ * (∫ u in abox N1 s, ∑ j : Fin N2, ∫ w in abox N2 s,
          ‖pSlotAmp s p (fun w' => Φ (mergeBlock N1 N2 (u, w'))) j w‖ ^ 2) := by
        congr 1
        exact (integral_finsetSum Finset.univ (fun j _ => hintU j)).symm
    _ = ∫ u in abox N1 s, (s ^ 3)⁻¹ * (∑ j : Fin N2, ∫ w in abox N2 s,
          ‖pSlotAmp s p (fun w' => Φ (mergeBlock N1 N2 (u, w'))) j w‖ ^ 2) :=
        (integral_const_mul _ _).symm
    _ = ∫ u in abox N1 s, pModeDiagonal s p (fun w => Φ (mergeBlock N1 N2 (u, w))) := by
        apply integral_congr_ae
        filter_upwards with u
        rfl

/-! ## 5  The degenerate case `s ≤ 0` -/

/-- For a nonpositive side length the centred box `abox N s` (`N ≠ 0`) is a null
set, so `pModeDiagonal` vanishes identically. -/
lemma pModeDiagonal_eq_zero_of_nonpos {N : ℕ} {s : ℝ} (hs : s ≤ 0) (p : ℝ³) (Ψ : X N → ℝ) :
    pModeDiagonal s p Ψ = 0 := by
  rw [pModeDiagonal]
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
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
    have hsum : (∑ i : Fin N, ∫ x in abox N s, ‖pSlotAmp s p Ψ i x‖ ^ 2) = 0 :=
      Finset.sum_eq_zero (fun i _ => by
        rw [hz]
        exact integral_zero_measure _)
    rw [hsum, mul_zero]

/-! ## 6  The theorem -/

theorem slotSplit_pModeDiagonal (s : ℝ) (p : EuclideanSpace ℝ (Fin 3)) :
    @Work.KinPSuperadd.SlotSplit s
      (fun (N : ℕ) (Φ : Submission.BoseGases.X N → ℝ)
        => @Submission.BoseGases.pModeDiagonal s p N Φ) := by
  by_cases hs : 0 < s
  · refine ⟨?_, ?_, ?_⟩
    · intro N1 N2 Φ hΦ
      change (s ^ 3)⁻¹ * (∑ k : Fin (N1 + N2), ∫ x in abox (N1 + N2) s,
            ‖pSlotAmp s p Φ k x‖ ^ 2)
          = (∫ w in abox N2 s, pModeDiagonal s p (fun u => Φ (mergeBlock N1 N2 (u, w))))
            + (∫ u in abox N1 s, pModeDiagonal s p (fun w => Φ (mergeBlock N1 N2 (u, w))))
      rw [Fin.sum_univ_add (a := N1) (b := N2)
            (f := fun k : Fin (N1 + N2) => ∫ x in abox (N1 + N2) s,
              ‖pSlotAmp s p Φ k x‖ ^ 2),
        mul_add, pModeDiagonal_sum_first s hs p hΦ.continuous,
        pModeDiagonal_sum_last s hs p hΦ.continuous]
    · intro N1 N2 Φ hΦ
      exact ContinuousOn.integrableOn_compact (abox_compact N2 hs)
        (continuous_pModeDiagonal_slice1 s hs p hΦ.continuous).continuousOn
    · intro N1 N2 Φ hΦ
      exact ContinuousOn.integrableOn_compact (abox_compact N1 hs)
        (continuous_pModeDiagonal_slice2 s hs p hΦ.continuous).continuousOn
  · have hsle : s ≤ 0 := le_of_not_gt hs
    refine ⟨?_, ?_, ?_⟩
    · intro N1 N2 Φ hΦ
      simp only [pModeDiagonal_eq_zero_of_nonpos hsle, integral_zero, add_zero]
    · intro N1 N2 Φ hΦ
      simp only [pModeDiagonal_eq_zero_of_nonpos hsle]
      exact integrableOn_zero
    · intro N1 N2 Φ hΦ
      simp only [pModeDiagonal_eq_zero_of_nonpos hsle]
      exact integrableOn_zero

end Work.KinPSuperadd
