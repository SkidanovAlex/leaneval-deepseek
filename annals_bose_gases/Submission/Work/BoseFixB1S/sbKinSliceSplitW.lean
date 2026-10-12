import ChallengeDeps
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1.Defs
import Submission.Work.BoseFixB1S.slotSplitCnPlusBoxInd
import Submission.Work.BoseFixB1S.wSwapPBoxTBamp
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.sbKinSliceSplitW` — the kinetic half of the word-level grouping step

The sliding small-box kinetic word `Work.BoseFixB1.sbKin μ M u`
(`= Work.UBBInputs8.tBwordBInd`, FS `eq:appTB`) is a **sum of one-slot forms over the
particles**: it is `tbGapCoeff (ℓd) ε · n₊(B) + Σ_i Q_{B,i}χ_B[√−Δ−c]₊²χ_BQ_{B,i}`,
and both summands split additively over a partition of the labels.  This file proves the
resulting structural fact `Work.KinPSuperadd.SlotSplit` for it, which is the `hKin`
hypothesis of the repaired word-level grouping step
(`Work.BoseFixB1S.sbWord_slice_superadd_regime`).

The two halves are handled separately (this is what `SlotSplit.add` / `SlotSplit.const_mul`
are for):

* `slotSplit_cnPlusBoxInd` (delegated) for the excited count
  `cnPlusBoxInd ℓ B V = Σ_i ∫_{abox N ℓ}(Q_{B,i}Φ)²`;
* the `p`-diagonal spectral half `tBdiagFormInd`, reduced to the corpus's indicator-free
  `tBdiagForm` (`Work.UBBInputs9.A.tBdiagFormInd_eq_tBdiagForm`, valid because
  `tsupport (chiB ℓ d u) ⊆ dlBox ℓ d u`), and then split slot by slot.

The key structural mechanism in both cases is that the slot-`i` functional commutes with
freezing the *other* block (`boxQ_slice_fst` / `boxQ_slice_snd`, `tBamp_slice_fst` /
`tBamp_slice_snd` below): for a configuration `merge(u,w)` and a slot `i` of the first
block, the slot-`i` functional is the slot-`j` functional of the `w`-slice applied at `u`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseFixB1S

open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-! ## 1  The one-slot slice identities -/

/-- **First-block slice of `boxQ`**: the mean-free projection of the `i`-th slot of a
merged configuration is the `j`-th slot projection of the `w`-slice. -/
lemma boxQ_slice_fst {N1 N2 : ℕ} (volA : ℝ) (A : Set ℝ³)
    (Φ : X (N1 + N2) → ℝ) (j : Fin N1) (u : X N1) (w : X N2) :
    Work.SmallBoxTBWord.boxQ volA A (Fin.castAdd N2 j) Φ (mergeBlock N1 N2 (u, w))
      = Work.SmallBoxTBWord.boxQ volA A j
          (fun u' => Φ (mergeBlock N1 N2 (u', w))) u := by
  simp only [Work.SmallBoxTBWord.boxQ, Work.SmallBoxTBWord.boxP,
    Work.KinPSuperadd.upd_mergeBlock_first]

/-- **Second-block slice of `boxQ`**. -/
lemma boxQ_slice_snd {N1 N2 : ℕ} (volA : ℝ) (A : Set ℝ³)
    (Φ : X (N1 + N2) → ℝ) (j : Fin N2) (u : X N1) (w : X N2) :
    Work.SmallBoxTBWord.boxQ volA A (Fin.natAdd N1 j) Φ (mergeBlock N1 N2 (u, w))
      = Work.SmallBoxTBWord.boxQ volA A j
          (fun w' => Φ (mergeBlock N1 N2 (u, w'))) w := by
  simp only [Work.SmallBoxTBWord.boxQ, Work.SmallBoxTBWord.boxP,
    Work.KinPSuperadd.upd_mergeBlock_last]

/-- **First-block slice of `tBamp`**: the windowed amplitude of the `i`-th slot of a
merged configuration is the amplitude of the `j`-th slot of the `w`-slice. -/
lemma tBamp_slice_fst {N1 N2 : ℕ} (χ : ℝ³ → ℝ) (p : ℝ³) (volA : ℝ) (A : Set ℝ³)
    (Φ : X (N1 + N2) → ℝ) (j : Fin N1) (u : X N1) (w : X N2) :
    Work.SmallBoxTBWord.tBamp χ p (Work.SmallBoxTBWord.boxQ volA A (Fin.castAdd N2 j) Φ)
        (Fin.castAdd N2 j) (mergeBlock N1 N2 (u, w))
      = Work.SmallBoxTBWord.tBamp χ p
          (Work.SmallBoxTBWord.boxQ volA A j (fun u' => Φ (mergeBlock N1 N2 (u', w)))) j u := by
  unfold Work.SmallBoxTBWord.tBamp
  refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
  simp only [Work.KinPSuperadd.upd_mergeBlock_first, boxQ_slice_fst]

/-- **Second-block slice of `tBamp`**. -/
lemma tBamp_slice_snd {N1 N2 : ℕ} (χ : ℝ³ → ℝ) (p : ℝ³) (volA : ℝ) (A : Set ℝ³)
    (Φ : X (N1 + N2) → ℝ) (j : Fin N2) (u : X N1) (w : X N2) :
    Work.SmallBoxTBWord.tBamp χ p (Work.SmallBoxTBWord.boxQ volA A (Fin.natAdd N1 j) Φ)
        (Fin.natAdd N1 j) (mergeBlock N1 N2 (u, w))
      = Work.SmallBoxTBWord.tBamp χ p
          (Work.SmallBoxTBWord.boxQ volA A j (fun w' => Φ (mergeBlock N1 N2 (u, w')))) j w := by
  unfold Work.SmallBoxTBWord.tBamp
  refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
  simp only [Work.KinPSuperadd.upd_mergeBlock_last, boxQ_slice_snd]

/-! ## 2  The `p`-density of one slot, and the `p ↔ box` swap

`tKin F χ V A i Ψ x = (2π)⁻³ ∫_p F‖p‖‖tBamp χ p (Q_{A,i}Ψ) i x‖²` is the `x`-density whose
box integral is (up to the slot normalisation `(s³)⁻¹`) the slot-`i` summand of
`tBdiagForm s A V χ F`.  The Fubini exchange between the `p`-integral and the box integral is
isolated in `SlotSwapProp`, so that everything below is independent of the (analytic) proof of
that exchange. -/

/-- The `p`-integrated spectral density of the slot-`i` mean-free component. -/
noncomputable def tKin (F : ℝ → ℝ) (χ : ℝ³ → ℝ) (V : ℝ) (A : Set ℝ³)
    {N : ℕ} (i : Fin N) (Ψ : X N → ℝ) (x : X N) : ℝ :=
  ((2 * π) ^ 3)⁻¹ * ∫ p : ℝ³,
    F ‖p‖ * ‖Work.SmallBoxTBWord.tBamp χ p (Work.SmallBoxTBWord.boxQ V A i Ψ) i x‖ ^ 2

/-- **The `p ↔ box` swap for one slot**: joint integrability of the slot-`i` `p`-integrand on
`ℝ³ × abox N s`, plus the Fubini exchange between the `p`-integral and the box integral. -/
def SlotSwapProp (s : ℝ) (A : Set ℝ³) (V : ℝ) (χ : ℝ³ → ℝ) (F : ℝ → ℝ) : Prop :=
  ∀ {N : ℕ} (Ψ : X N → ℝ), ContDiff ℝ ∞ Ψ → ∀ i : Fin N,
    Integrable (fun q : ℝ³ × X N =>
        F ‖q.1‖ *
          ‖Work.SmallBoxTBWord.tBamp χ q.1 (Work.SmallBoxTBWord.boxQ V A i Ψ) i q.2‖ ^ 2)
      ((volume : Measure ℝ³).prod ((volume : Measure (X N)).restrict (abox N s)))
    ∧ (∫ p : ℝ³, ∫ x in abox N s,
          F ‖p‖ * ‖Work.SmallBoxTBWord.tBamp χ p (Work.SmallBoxTBWord.boxQ V A i Ψ) i x‖ ^ 2)
      = ∫ x in abox N s, ∫ p : ℝ³,
          F ‖p‖ * ‖Work.SmallBoxTBWord.tBamp χ p (Work.SmallBoxTBWord.boxQ V A i Ψ) i x‖ ^ 2

variable {F : ℝ → ℝ} {χ : ℝ³ → ℝ} {V : ℝ} {A : Set ℝ³} {s : ℝ}

/-- **The slot summand of `tBdiagForm` in `x`-outer form.**  For a smooth state and a slot `i`,
the slot-`i` summand of `tBdiagForm` is the slot-`i` box density of `tKin`, times `(s³)⁻¹`.
The only non-elementary input is the Fubini exchange `SlotSwapProp`. -/
lemma tBdiagForm_slot_eq (hsw : SlotSwapProp s A V χ F) {N : ℕ} {Ψ : X N → ℝ}
    (hΨ : ContDiff ℝ ∞ Ψ) (i : Fin N) :
    ((2 * π) ^ 3)⁻¹ * ∫ p : ℝ³, F ‖p‖ *
        ((s ^ 3)⁻¹ * ∫ x in abox N s,
          ‖Work.SmallBoxTBWord.tBamp χ p (Work.SmallBoxTBWord.boxQ V A i Ψ) i x‖ ^ 2)
      = (s ^ 3)⁻¹ * ∫ x in abox N s, tKin F χ V A i Ψ x := by
  have hswi := (hsw Ψ hΨ i).2
  have h1 : ∀ p : ℝ³, F ‖p‖ * ((s ^ 3)⁻¹ * ∫ x in abox N s,
        ‖Work.SmallBoxTBWord.tBamp χ p (Work.SmallBoxTBWord.boxQ V A i Ψ) i x‖ ^ 2)
      = (s ^ 3)⁻¹ * (F ‖p‖ * ∫ x in abox N s,
          ‖Work.SmallBoxTBWord.tBamp χ p (Work.SmallBoxTBWord.boxQ V A i Ψ) i x‖ ^ 2) :=
    fun p => by ring
  have h2 : ∀ p : ℝ³, F ‖p‖ * (∫ x in abox N s,
        ‖Work.SmallBoxTBWord.tBamp χ p (Work.SmallBoxTBWord.boxQ V A i Ψ) i x‖ ^ 2)
      = ∫ x in abox N s,
          F ‖p‖ * ‖Work.SmallBoxTBWord.tBamp χ p (Work.SmallBoxTBWord.boxQ V A i Ψ) i x‖ ^ 2 :=
    fun p => (integral_const_mul (F ‖p‖) (fun x : X N =>
      ‖Work.SmallBoxTBWord.tBamp χ p (Work.SmallBoxTBWord.boxQ V A i Ψ) i x‖ ^ 2)).symm
  calc ((2 * π) ^ 3)⁻¹ * ∫ p : ℝ³, F ‖p‖ *
        ((s ^ 3)⁻¹ * ∫ x in abox N s,
          ‖Work.SmallBoxTBWord.tBamp χ p (Work.SmallBoxTBWord.boxQ V A i Ψ) i x‖ ^ 2)
      = ((2 * π) ^ 3)⁻¹ * ∫ p : ℝ³, (s ^ 3)⁻¹ * (F ‖p‖ * ∫ x in abox N s,
          ‖Work.SmallBoxTBWord.tBamp χ p (Work.SmallBoxTBWord.boxQ V A i Ψ) i x‖ ^ 2) := by
        congr 1
        exact integral_congr_ae (Filter.Eventually.of_forall h1)
    _ = ((2 * π) ^ 3)⁻¹ * ((s ^ 3)⁻¹ * ∫ p : ℝ³,
          F ‖p‖ * ∫ x in abox N s,
            ‖Work.SmallBoxTBWord.tBamp χ p (Work.SmallBoxTBWord.boxQ V A i Ψ) i x‖ ^ 2) := by
        rw [integral_const_mul]
    _ = ((2 * π) ^ 3)⁻¹ * ((s ^ 3)⁻¹ * ∫ p : ℝ³, ∫ x in abox N s,
          F ‖p‖ * ‖Work.SmallBoxTBWord.tBamp χ p (Work.SmallBoxTBWord.boxQ V A i Ψ) i x‖ ^ 2) := by
        congr 1
        congr 1
        exact integral_congr_ae (Filter.Eventually.of_forall h2)
    _ = ((2 * π) ^ 3)⁻¹ * ((s ^ 3)⁻¹ * ∫ x in abox N s, ∫ p : ℝ³,
          F ‖p‖ * ‖Work.SmallBoxTBWord.tBamp χ p (Work.SmallBoxTBWord.boxQ V A i Ψ) i x‖ ^ 2) := by
        rw [hswi]
    _ = (s ^ 3)⁻¹ * (((2 * π) ^ 3)⁻¹ * ∫ x in abox N s, ∫ p : ℝ³,
          F ‖p‖ * ‖Work.SmallBoxTBWord.tBamp χ p (Work.SmallBoxTBWord.boxQ V A i Ψ) i x‖ ^ 2) := by
        ring
    _ = (s ^ 3)⁻¹ * ∫ x in abox N s, ((2 * π) ^ 3)⁻¹ * ∫ p : ℝ³,
          F ‖p‖ * ‖Work.SmallBoxTBWord.tBamp χ p (Work.SmallBoxTBWord.boxQ V A i Ψ) i x‖ ^ 2 := by
        congr 1
        rw [integral_const_mul]
    _ = (s ^ 3)⁻¹ * ∫ x in abox N s, tKin F χ V A i Ψ x := rfl

/-- **The `x`-outer form of the whole spectral half**: the slot sum of `tBdiagForm` is the
sum of the slot box densities of `tKin`. -/
lemma tBdiagForm_eq_sum_tKin (hsw : SlotSwapProp s A V χ F) {N : ℕ} {Ψ : X N → ℝ}
    (hΨ : ContDiff ℝ ∞ Ψ) :
    Work.SmallBoxTBWord.tBdiagForm s A V χ F Ψ
      = ∑ i : Fin N, (s ^ 3)⁻¹ * ∫ x in abox N s, tKin F χ V A i Ψ x := by
  simp only [Work.SmallBoxTBWord.tBdiagForm]
  exact Finset.sum_congr rfl (fun i _ => tBdiagForm_slot_eq hsw hΨ i)

/-- **The pointwise slice identity for `tKin`**: the slot-`i` density of a merged
configuration, `i` in the first block, is the corresponding density of the `w`-slice. -/
lemma tKin_slice_fst {N1 N2 : ℕ} (Φ : X (N1 + N2) → ℝ) (j : Fin N1) (u : X N1) (w : X N2) :
    tKin F χ V A (Fin.castAdd N2 j) Φ (mergeBlock N1 N2 (u, w))
      = tKin F χ V A j (fun u' => Φ (mergeBlock N1 N2 (u', w))) u := by
  unfold tKin
  congr 1
  exact integral_congr_ae (Filter.Eventually.of_forall (fun p => by simp only [tBamp_slice_fst]))

/-- **The pointwise slice identity for `tKin`**, second block. -/
lemma tKin_slice_snd {N1 N2 : ℕ} (Φ : X (N1 + N2) → ℝ) (j : Fin N2) (u : X N1) (w : X N2) :
    tKin F χ V A (Fin.natAdd N1 j) Φ (mergeBlock N1 N2 (u, w))
      = tKin F χ V A j (fun w' => Φ (mergeBlock N1 N2 (u, w'))) w := by
  unfold tKin
  congr 1
  exact integral_congr_ae (Filter.Eventually.of_forall (fun p => by simp only [tBamp_slice_snd]))

/-! ## 3  The box Fubini at fixed slot, and the slice integrability -/

/-- The slot-`i` density of a smooth state is integrable on the box (from the swap property). -/
lemma integrableOn_tKin (hsw : SlotSwapProp s A V χ F) {N : ℕ} {Ψ : X N → ℝ}
    (hΨ : ContDiff ℝ ∞ Ψ) (i : Fin N) :
    IntegrableOn (fun x : X N => tKin F χ V A i Ψ x) (abox N s) volume :=
  ((hsw Ψ hΨ i).1.integral_prod_right).const_mul ((2 * π) ^ 3)⁻¹

/-- **First-block slot Fubini**: the box integral of the slot-`i` density of a merged
configuration, `i` in the first block, is the iterated integral over the two blocks of the
corresponding slice density. -/
lemma integral_tKin_merge_castAdd {N1 N2 : ℕ} {Φ : X (N1 + N2) → ℝ} (hsw : SlotSwapProp s A V χ F)
    (hΦ : ContDiff ℝ ∞ Φ) (j : Fin N1) :
    ∫ x in abox (N1 + N2) s, tKin F χ V A (Fin.castAdd N2 j) Φ x
      = ∫ w in abox N2 s, ∫ u in abox N1 s,
          tKin F χ V A j (fun u' => Φ (mergeBlock N1 N2 (u', w))) u := by
  rw [← aboxFubini_swapped (N1 := N1) (N2 := N2) s
    (fun x => tKin F χ V A (Fin.castAdd N2 j) Φ x) (integrableOn_tKin hsw hΦ _)]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun w => ?_))
  refine integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
  exact tKin_slice_fst Φ j u w

/-- **Second-block slot Fubini**. -/
lemma integral_tKin_merge_natAdd {N1 N2 : ℕ} {Φ : X (N1 + N2) → ℝ} (hsw : SlotSwapProp s A V χ F)
    (hΦ : ContDiff ℝ ∞ Φ) (j : Fin N2) :
    ∫ x in abox (N1 + N2) s, tKin F χ V A (Fin.natAdd N1 j) Φ x
      = ∫ u in abox N1 s, ∫ w in abox N2 s,
          tKin F χ V A j (fun w' => Φ (mergeBlock N1 N2 (u, w'))) w := by
  rw [← aboxFubini (N1 := N1) (N2 := N2) s
    (fun x => tKin F χ V A (Fin.natAdd N1 j) Φ x) (integrableOn_tKin hsw hΦ _)]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
  refine integral_congr_ae (Filter.Eventually.of_forall (fun w => ?_))
  exact tKin_slice_snd Φ j u w

/-- **First-block slice integrability**: the `w`-integral of the first-block slice density is
integrable over the second block's box (this is `SlotSplit.int₁` for the spectral half). -/
lemma integrableOn_tKin_slice_fst {N1 N2 : ℕ} {Φ : X (N1 + N2) → ℝ}
    (hsw : SlotSwapProp s A V χ F) (hΦ : ContDiff ℝ ∞ Φ) (j : Fin N1) :
    IntegrableOn (fun w : X N2 => ∫ u in abox N1 s,
        tKin F χ V A j (fun u' => Φ (mergeBlock N1 N2 (u', w))) u) (abox N2 s) volume := by
  have hGe : Integrable (fun p : X N1 × X N2 =>
      tKin F χ V A (Fin.castAdd N2 j) Φ (mergeBlock N1 N2 p))
      ((volume.restrict (abox N1 s)).prod (volume.restrict (abox N2 s))) := by
    apply (aboxSplit_measurePreserving_restrict N1 N2 s).integrable_comp_emb
      (blockSplitEquiv N1 N2).measurableEmbedding |>.mp
    refine (integrableOn_tKin hsw hΦ (Fin.castAdd N2 j)).congr ?_
    filter_upwards with x
    simp [Function.comp_apply, blockSplitEquiv_apply, mergeBlock_eq]
  exact (hGe.integral_prod_right).congr
    (Filter.Eventually.of_forall (fun w => by
      apply integral_congr_ae
      refine Filter.Eventually.of_forall (fun u => ?_)
      exact tKin_slice_fst Φ j u w))

/-- **Second-block slice integrability** (this is `SlotSplit.int₂` for the spectral half). -/
lemma integrableOn_tKin_slice_snd {N1 N2 : ℕ} {Φ : X (N1 + N2) → ℝ}
    (hsw : SlotSwapProp s A V χ F) (hΦ : ContDiff ℝ ∞ Φ) (j : Fin N2) :
    IntegrableOn (fun u : X N1 => ∫ w in abox N2 s,
        tKin F χ V A j (fun w' => Φ (mergeBlock N1 N2 (u, w'))) w) (abox N1 s) volume := by
  have hGe : Integrable (fun p : X N1 × X N2 =>
      tKin F χ V A (Fin.natAdd N1 j) Φ (mergeBlock N1 N2 p))
      ((volume.restrict (abox N1 s)).prod (volume.restrict (abox N2 s))) := by
    apply (aboxSplit_measurePreserving_restrict N1 N2 s).integrable_comp_emb
      (blockSplitEquiv N1 N2).measurableEmbedding |>.mp
    refine (integrableOn_tKin hsw hΦ (Fin.natAdd N1 j)).congr ?_
    filter_upwards with x
    simp [Function.comp_apply, blockSplitEquiv_apply, mergeBlock_eq]
  exact (hGe.integral_prod_left).congr
    (Filter.Eventually.of_forall (fun u => by
      apply integral_congr_ae
      refine Filter.Eventually.of_forall (fun w => ?_)
      exact tKin_slice_snd Φ j u w))

/-! ## 4  `SlotSplit` for the spectral half -/

/-- **The spectral half of `sbKin` is block-splittable.** -/
theorem slotSplit_tBdiagForm (hsw : SlotSwapProp s A V χ F) :
    Work.KinPSuperadd.SlotSplit s
      (fun (N : ℕ) (Φ : X N → ℝ) => Work.SmallBoxTBWord.tBdiagForm s A V χ F Φ) := by
  refine ⟨?_, ?_, ?_⟩
  · intro N1 N2 Φ hΦ
    rw [tBdiagForm_eq_sum_tKin hsw hΦ, Fin.sum_univ_add]
    have h1 : (∑ j : Fin N1, (s ^ 3)⁻¹ *
          ∫ x in abox (N1 + N2) s, tKin F χ V A (Fin.castAdd N2 j) Φ x)
        = ∫ w in abox N2 s, ∑ j : Fin N1, (s ^ 3)⁻¹ * ∫ u in abox N1 s,
            tKin F χ V A j (fun u' => Φ (mergeBlock N1 N2 (u', w))) u := by
      rw [Finset.sum_congr rfl (fun j _ => by
        rw [integral_tKin_merge_castAdd hsw hΦ j])]
      rw [Finset.sum_congr rfl (fun j _ => (integral_const_mul ((s ^ 3)⁻¹)
        (fun w : X N2 => ∫ u in abox N1 s,
          tKin F χ V A j (fun u' => Φ (mergeBlock N1 N2 (u', w))) u)).symm)]
      exact (integral_finsetSum Finset.univ (fun j _ =>
        (integrableOn_tKin_slice_fst hsw hΦ j).const_mul ((s ^ 3)⁻¹))).symm
    have h2 : (∑ j : Fin N2, (s ^ 3)⁻¹ *
          ∫ x in abox (N1 + N2) s, tKin F χ V A (Fin.natAdd N1 j) Φ x)
        = ∫ u in abox N1 s, ∑ j : Fin N2, (s ^ 3)⁻¹ * ∫ w in abox N2 s,
            tKin F χ V A j (fun w' => Φ (mergeBlock N1 N2 (u, w'))) w := by
      rw [Finset.sum_congr rfl (fun j _ => by
        rw [integral_tKin_merge_natAdd hsw hΦ j])]
      rw [Finset.sum_congr rfl (fun j _ => (integral_const_mul ((s ^ 3)⁻¹)
        (fun u : X N1 => ∫ w in abox N2 s,
          tKin F χ V A j (fun w' => Φ (mergeBlock N1 N2 (u, w'))) w)).symm)]
      exact (integral_finsetSum Finset.univ (fun j _ =>
        (integrableOn_tKin_slice_snd hsw hΦ j).const_mul ((s ^ 3)⁻¹))).symm
    rw [h1, h2]
    congr 1
    · refine integral_congr_ae (Filter.Eventually.of_forall (fun w => ?_))
      exact (tBdiagForm_eq_sum_tKin hsw (Work.KinPSuperadd.slice_contDiff_infty_fst hΦ w)).symm
    · refine integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
      exact (tBdiagForm_eq_sum_tKin hsw (Work.KinPSuperadd.slice_contDiff_infty_snd hΦ u)).symm
  · intro N1 N2 Φ hΦ
    have hsum : IntegrableOn (fun w : X N2 => ∑ j : Fin N1, (s ^ 3)⁻¹ * ∫ u in abox N1 s,
        tKin F χ V A j (fun u' => Φ (mergeBlock N1 N2 (u', w))) u) (abox N2 s) volume :=
      integrable_finsetSum Finset.univ (fun j _ =>
        (integrableOn_tKin_slice_fst hsw hΦ j).const_mul ((s ^ 3)⁻¹))
    refine hsum.congr (Filter.Eventually.of_forall (fun w => ?_))
    exact (tBdiagForm_eq_sum_tKin hsw (Work.KinPSuperadd.slice_contDiff_infty_fst hΦ w)).symm
  · intro N1 N2 Φ hΦ
    have hsum : IntegrableOn (fun u : X N1 => ∑ j : Fin N2, (s ^ 3)⁻¹ * ∫ w in abox N2 s,
        tKin F χ V A j (fun w' => Φ (mergeBlock N1 N2 (u, w'))) w) (abox N1 s) volume :=
      integrable_finsetSum Finset.univ (fun j _ =>
        (integrableOn_tKin_slice_snd hsw hΦ j).const_mul ((s ^ 3)⁻¹))
    refine hsum.congr (Filter.Eventually.of_forall (fun u => ?_))
    exact (tBdiagForm_eq_sum_tKin hsw (Work.KinPSuperadd.slice_contDiff_infty_snd hΦ u)).symm

end Work.BoseFixB1S

namespace Work.KinPSuperadd

open Submission BoseGases

/-- **Word congruence for `SlotSplit`**: two pointwise equal words are `SlotSplit` together. -/
lemma SlotSplit.congr_word {s : ℝ} {K L : ∀ N : ℕ, (X N → ℝ) → ℝ}
    (h : SlotSplit s K) (hKL : ∀ (N : ℕ) (Φ : X N → ℝ), K N Φ = L N Φ) : SlotSplit s L := by
  refine ⟨?_, ?_, ?_⟩
  · intro N1 N2 Φ hΦ
    rw [← hKL (N1 + N2) Φ, h.split Φ hΦ]
    congr 1
    · apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun w => hKL N1 _)
    · apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun u => hKL N2 _)
  · intro N1 N2 Φ hΦ
    exact (h.int₁ Φ hΦ).congr (Filter.Eventually.of_forall (fun w => hKL N1 _))
  · intro N1 N2 Φ hΦ
    exact (h.int₂ Φ hΦ).congr (Filter.Eventually.of_forall (fun u => hKL N2 _))

end Work.KinPSuperadd

namespace Work.BoseFixB1S

open Submission.BoseGases

/-! ## 5  The assembly -/

/-- The window vanishes off its box: `z ∉ B(u) → χ_{B(u)}(z) = 0`. -/
lemma chiB_eq_zero_of_notMem_w {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (u : ℝ³) :
    ∀ z : ℝ³, z ∉ dlBox ℓ d u → chiB ℓ d u z = 0 := by
  intro z hz
  by_contra hne
  exact hz (Work.UBBInputs9.A.tsupport_chiB_subset_dlBox hℓ hd u
    (subset_tsupport _ (Function.mem_support.mpr hne)))

/-- The kinetic symbol `[r−c]₊²` is bounded by `(|c|+1)²(1+r)²` on `r ≥ 0`. -/
lemma abs_fsKinCoeff_le_w (c : ℝ) :
    ∀ r : ℝ, 0 ≤ r → |fsKinCoeff c r| ≤ (|c| + 1) ^ 2 * (1 + r) ^ 2 := by
  intro r hr
  have h1 : fsKinCoeff c r = (max (r - c) 0) ^ 2 := rfl
  have h4 : 0 ≤ max (r - c) 0 := le_max_right _ _
  have h2 : max (r - c) 0 ≤ |c| + r :=
    max_le (by have := neg_le_abs c; linarith) (by positivity)
  have h3 : |c| + r ≤ (|c| + 1) * (1 + r) := by nlinarith [abs_nonneg c, hr]
  rw [h1, abs_of_nonneg (sq_nonneg _)]
  calc (max (r - c) 0) ^ 2 ≤ ((|c| + 1) * (1 + r)) ^ 2 :=
        pow_le_pow_left₀ h4 (le_trans h2 h3) 2
    _ = (|c| + 1) ^ 2 * (1 + r) ^ 2 := by ring

/-- **The assembly**: the `SlotSplit` property of `sbKin` from the two halves — the `p ↔ box`
swap for the spectral half and the block decomposition of the excited count. -/
theorem sbKinSliceSplitW_of_swap {v : ℝ³ → ℝ} {ε₀ μ : ℝ}
    (hAdm : Work.BoseBoxFix.Adm v ε₀ μ) (u : ℝ³)
    (hsw : SlotSwapProp (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
      (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
      (Submission.BoseGases.chiB (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
      (Submission.BoseGases.fsKinCoeff (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v))))
    (hcn : Work.KinPSuperadd.SlotSplit (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (fun (N : ℕ) (Φ : Submission.BoseGases.X N → ℝ) =>
        Work.UBBInputs8.cnPlusBoxInd (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
          (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) Φ)) :
    Work.KinPSuperadd.SlotSplit (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (fun (N : ℕ) (Φ : Submission.BoseGases.X N → ℝ) =>
        Work.BoseFixB1.sbKin (v := v) μ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M u Φ) := by
  set ℓ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v) with hℓdef
  set d := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d with hddef
  set M := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M with hMdef
  have hℓ : 0 < ℓ := by rw [hℓdef]; exact Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < d := by rw [hddef]; exact Work.BoseFixB1.adm_d_pos hAdm
  have hχE : ∀ z : ℝ³, z ∉ Submission.BoseGases.dlBox ℓ d u →
      Submission.BoseGases.chiB ℓ d u z = 0 :=
    chiB_eq_zero_of_notMem_w hℓ hd u
  set A := Submission.BoseGases.dlBox ℓ d u with hAdef
  set V := Work.SmallBoxSliding.boxMass ℓ d u with hVdef
  set χ := Submission.BoseGases.chiB ℓ d u with hχdef
  set F := Submission.BoseGases.fsKinCoeff (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) with hFdef
  have hBd : Work.KinPSuperadd.SlotSplit ℓ
      (fun (N : ℕ) (Φ : Submission.BoseGases.X N → ℝ) =>
        Work.UBBInputs8.tBdiagFormInd ℓ A V χ F Φ) := by
    refine (slotSplit_tBdiagForm (s := ℓ) (A := A) (V := V) (χ := χ) (F := F) hsw).congr_word
      (fun N Φ => ?_)
    exact (Work.UBBInputs9.A.tBdiagFormInd_eq_tBdiagForm (a := ℓ) (A := A) (volA := V)
      (χ := χ) F Φ (fun z hz => hχE z hz)).symm
  have hall : Work.KinPSuperadd.SlotSplit ℓ (fun (N : ℕ) (Φ : Submission.BoseGases.X N → ℝ) =>
      Work.SmallBoxTBWord.tbGapCoeff (ℓ * d) (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
          * Work.UBBInputs8.cnPlusBoxInd ℓ A V Φ
        + Work.UBBInputs8.tBdiagFormInd ℓ A V χ F Φ) :=
    (hcn.const_mul (Work.SmallBoxTBWord.tbGapCoeff (ℓ * d)
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT)).add hBd
  refine hall.congr_word (fun N Φ => ?_)
  simp only [Work.BoseFixB1.sbKin, Work.UBBInputs8.tBwordBInd, Work.UBBInputs8.tBwordInd,
    Work.UBBInputs8.tBwordKinInd]
  rw [← hℓdef, ← hddef, ← hAdef, ← hVdef, ← hχdef, ← hFdef]

theorem sbKinSliceSplitW {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) {ε₀ μ : ℝ} (hAdm : Work.BoseBoxFix.Adm v ε₀ μ)
    (u : EuclideanSpace ℝ (Fin 3)) :
    Work.KinPSuperadd.SlotSplit (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (fun (N : ℕ) (Φ : Submission.BoseGases.X N → ℝ) =>
        Work.BoseFixB1.sbKin (v := v) μ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M u Φ) := by
  have hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d := Work.BoseFixB1.adm_d_pos hAdm
  refine sbKinSliceSplitW_of_swap (v := v) (ε₀ := ε₀) (μ := μ) hAdm u ?_ ?_
  · intro N Ψ hΨ i
    exact wSwapPBoxTBamp hℓ (Work.SmallBoxTBWord.isCompact_dlBox hℓ hd u)
      (Work.SmallBoxTBWord.contDiff_chiB hℓ hd u)
      (Work.SmallBoxTBWord.hasCompactSupport_chiB hℓ hd u)
      (Work.BoseKinLoc.Kinetic.measurable_fsKinCoeff _) (by positivity)
      (abs_fsKinCoeff_le_w _) hΨ i
  · exact slotSplitCnPlusBoxInd hℓ (Work.SmallBoxSliding.measurableSet_dlBox _ _ _)
      (fun x hx => hx.1) (Work.SmallBoxSliding.boxMass_eq_measureReal _ _ _)

end Work.BoseFixB1S
