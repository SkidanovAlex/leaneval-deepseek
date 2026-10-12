import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1B.cnPlusBoxInd_slice_split
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1B.tBamp_amplitude_box_fubini` — the block Fubini for the `tBamp` amplitude

FS's sliding-box localisation groups the `N₁+N₂` particles into two blocks.  The **kinetic**
side of the grouping (`lem:LocKinEn`, `final_v2.tex`) is expressed through the windowed
`p`-mode amplitudes `tBamp χ p (Q_{B,i}Φ) i x` of `Work.SmallBoxTBWord`, and the grouping
identity needs the *Fubini* statement: the amplitude energy of a slot of one block, integrated
over the full centred box `abox (N₁+N₂) a`, is the iterated integral of the amplitude energy of
the corresponding slot of the *slice* of `Φ` at the frozen other block.

This file proves exactly that:

* `tBamp_mergeBlock_castAdd` / `tBamp_mergeBlock_natAdd` — the amplitude of a slot of a merged
  configuration `mergeBlock N₁ N₂ (u,w)` is the amplitude of the same slot of the frozen-block
  slice (`tBamp` only sees slot `i`, and updating slot `i` of a merged configuration updates the
  corresponding block, `cns_split_update_castAdd`);
* `tBamp_boxQInd_merge_castAdd` / `tBamp_boxQInd_merge_natAdd` — the same for the FS-faithful
  box projection `boxQInd` (`Work.UBBInputs8`), using
  `cns_split_boxQInd_merge_castAdd`/`cns_split_boxQInd_merge_natAdd`;
* `tBamp_amplitude_box_fubini` — the target, obtained from the measure-preserving block split
  `aboxFubini`/`aboxFubini_swapped` (`Submission.Work.AboxBlockSplit`) together with the
  pointwise identities above.

The statement is *hypothesis-minimal*: the only input is the `IntegrableOn` hypothesis of the
`(N₁+N₂)`-particle integrand on `abox (N₁+N₂) a` — which is exactly what the two Fubini lemmas
need — and there is no hypothesis on the sign of the box side `a` (for `a ≤ 0` the box is null
and the identity is trivial, and the Fubini lemmas cover that case uniformly).
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators ENNReal

namespace Work.BoseFixB1B

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## 1. The amplitude of a merged configuration is the amplitude of a slice -/

/-- The windowed amplitude does not depend on the slot-`i` coordinate, and updating slot
`Fin.castAdd N₂ j` of a merged configuration updates the first block; hence the `(N₁+N₂)`-slot
amplitude at a merged configuration is the `N₁`-slot amplitude of the `w`-slice. -/
lemma tBamp_mergeBlock_castAdd {N1 N2 : ℕ} {χ : E3 → ℝ} {p : E3}
    (Ψ : Submission.BoseGases.X (N1 + N2) → ℝ) (j : Fin N1)
    (u : Submission.BoseGases.X N1) (w : Submission.BoseGases.X N2) :
    Work.SmallBoxTBWord.tBamp χ p Ψ (Fin.castAdd N2 j)
        (Submission.BoseGases.mergeBlock N1 N2 (u, w))
      = Work.SmallBoxTBWord.tBamp χ p
          (fun u' => Ψ (Submission.BoseGases.mergeBlock N1 N2 (u', w))) j u := by
  simp only [Work.SmallBoxTBWord.tBamp, cns_split_update_castAdd]

/-- The `Fin.natAdd`-analogue of `tBamp_mergeBlock_castAdd` for the second block. -/
lemma tBamp_mergeBlock_natAdd {N1 N2 : ℕ} {χ : E3 → ℝ} {p : E3}
    (Ψ : Submission.BoseGases.X (N1 + N2) → ℝ) (j : Fin N2)
    (u : Submission.BoseGases.X N1) (w : Submission.BoseGases.X N2) :
    Work.SmallBoxTBWord.tBamp χ p Ψ (Fin.natAdd N1 j)
        (Submission.BoseGases.mergeBlock N1 N2 (u, w))
      = Work.SmallBoxTBWord.tBamp χ p
          (fun w' => Ψ (Submission.BoseGases.mergeBlock N1 N2 (u, w'))) j w := by
  simp only [Work.SmallBoxTBWord.tBamp, cns_split_update_natAdd]

/-- FS-faithful version: the windowed amplitude of the box-projected state
`boxQInd V A (Fin.castAdd N₂ j) Φ` at a merged configuration is the corresponding amplitude of
the `w`-slice of `Φ` (through the one-slot property of `Q_{B,i}`). -/
lemma tBamp_boxQInd_merge_castAdd {N1 N2 : ℕ} {V : ℝ} {A : Set E3}
    {χ : E3 → ℝ} {p : E3} (Φ : Submission.BoseGases.X (N1 + N2) → ℝ) (j : Fin N1)
    (u : Submission.BoseGases.X N1) (w : Submission.BoseGases.X N2) :
    Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd V A (Fin.castAdd N2 j) Φ)
        (Fin.castAdd N2 j) (Submission.BoseGases.mergeBlock N1 N2 (u, w))
      = Work.SmallBoxTBWord.tBamp χ p
          (Work.UBBInputs8.boxQInd V A j
            (fun u' => Φ (Submission.BoseGases.mergeBlock N1 N2 (u', w)))) j u := by
  simp only [Work.SmallBoxTBWord.tBamp, cns_split_update_castAdd,
    cns_split_boxQInd_merge_castAdd]

/-- The `Fin.natAdd`-analogue of `tBamp_boxQInd_merge_castAdd` for the second block. -/
lemma tBamp_boxQInd_merge_natAdd {N1 N2 : ℕ} {V : ℝ} {A : Set E3}
    {χ : E3 → ℝ} {p : E3} (Φ : Submission.BoseGases.X (N1 + N2) → ℝ) (j : Fin N2)
    (u : Submission.BoseGases.X N1) (w : Submission.BoseGases.X N2) :
    Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd V A (Fin.natAdd N1 j) Φ)
        (Fin.natAdd N1 j) (Submission.BoseGases.mergeBlock N1 N2 (u, w))
      = Work.SmallBoxTBWord.tBamp χ p
          (Work.UBBInputs8.boxQInd V A j
            (fun w' => Φ (Submission.BoseGases.mergeBlock N1 N2 (u, w')))) j w := by
  simp only [Work.SmallBoxTBWord.tBamp, cns_split_update_natAdd,
    cns_split_boxQInd_merge_natAdd]

/-! ## 2. The target: the block Fubini identity -/

theorem tBamp_amplitude_box_fubini {N1 N2 : ℕ} {a V : ℝ}
    {A : Set (EuclideanSpace ℝ (Fin 3))} {χ : EuclideanSpace ℝ (Fin 3) → ℝ}
    {Φ : Submission.BoseGases.X (N1 + N2) → ℝ} (p : EuclideanSpace ℝ (Fin 3)) :
    (∀ (j : Fin N1),
        MeasureTheory.IntegrableOn
          (fun x : Submission.BoseGases.X (N1 + N2) =>
            ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd V A (Fin.castAdd N2 j) Φ)
              (Fin.castAdd N2 j) x‖ ^ 2)
          (Submission.BoseGases.abox (N1 + N2) a) MeasureTheory.volume →
        (∫ x in Submission.BoseGases.abox (N1 + N2) a,
            ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd V A (Fin.castAdd N2 j) Φ)
              (Fin.castAdd N2 j) x‖ ^ 2)
          = ∫ w in Submission.BoseGases.abox N2 a,
              ∫ u in Submission.BoseGases.abox N1 a,
                ‖Work.SmallBoxTBWord.tBamp χ p
                  (Work.UBBInputs8.boxQInd V A j
                    (fun y => Φ (Submission.BoseGases.mergeBlock N1 N2 (y, w)))) j u‖ ^ 2)
    ∧ (∀ (j : Fin N2),
        MeasureTheory.IntegrableOn
          (fun x : Submission.BoseGases.X (N1 + N2) =>
            ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd V A (Fin.natAdd N1 j) Φ)
              (Fin.natAdd N1 j) x‖ ^ 2)
          (Submission.BoseGases.abox (N1 + N2) a) MeasureTheory.volume →
        (∫ x in Submission.BoseGases.abox (N1 + N2) a,
            ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd V A (Fin.natAdd N1 j) Φ)
              (Fin.natAdd N1 j) x‖ ^ 2)
          = ∫ u in Submission.BoseGases.abox N1 a,
              ∫ w in Submission.BoseGases.abox N2 a,
                ‖Work.SmallBoxTBWord.tBamp χ p
                  (Work.UBBInputs8.boxQInd V A j
                    (fun w' => Φ (Submission.BoseGases.mergeBlock N1 N2 (u, w')))) j w‖ ^ 2) := by
  constructor
  · intro j hInt
    let G : Submission.BoseGases.X (N1 + N2) → ℝ :=
      fun x => ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd V A (Fin.castAdd N2 j) Φ)
        (Fin.castAdd N2 j) x‖ ^ 2
    have hFub := aboxFubini_slice_swapped a G hInt
    change (∫ x in Submission.BoseGases.abox (N1 + N2) a, G x) = _
    rw [← hFub]
    apply integral_congr_ae
    filter_upwards with w
    apply integral_congr_ae
    filter_upwards with u
    exact congrArg (fun (z : ℂ) => ‖z‖ ^ 2) (tBamp_boxQInd_merge_castAdd Φ j u w)
  · intro j hInt
    let G : Submission.BoseGases.X (N1 + N2) → ℝ :=
      fun x => ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd V A (Fin.natAdd N1 j) Φ)
        (Fin.natAdd N1 j) x‖ ^ 2
    have hFub := aboxFubini_slice a G hInt
    change (∫ x in Submission.BoseGases.abox (N1 + N2) a, G x) = _
    rw [← hFub]
    apply integral_congr_ae
    filter_upwards with u
    apply integral_congr_ae
    filter_upwards with w
    exact congrArg (fun (z : ℂ) => ‖z‖ ^ 2) (tBamp_boxQInd_merge_natAdd Φ j u w)

end Work.BoseFixB1B
