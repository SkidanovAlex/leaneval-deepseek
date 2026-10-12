import ChallengeDeps
import Submission.Work.BoseFixB1B.sectorCountBoxAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1B.slotKinFibre`

**The kinetic half of the per-slot assembly of FS `thm:smallbox`**: the FS-faithful kinetic word
`tBwordBInd` of a slot piece `slotPiece B S Φ` (the indicator of the slot set `slotSet B S`, `B = B(u)`
the sliding box, the particle number running over `N = n`) equals the `y`-integral, over the outside
configurations `y ∈ slotOutside ℓ B S`, of the `|S|`-particle kinetic word of the *fibre*
`pieceFibre B S e Φ y`; and that fibre integrand is Bochner integrable on the restricted outside
measure.

## The mathematics

`tBwordBInd K ℓ d ε c u Ψ` unfolds into the two halves

    𝒯_B = tbGapCoeff (ℓ·d) ε · n₊(B, Ψ) + tBdiagFormInd ℓ B |B| χ_B (fsKinCoeff c) Ψ

so it suffices to add the two already-proved fibre factorisations at the slot piece:

* the gap (excited-count) half is `Work.SlotWord.FibreGap.cnPlusBoxInd_fibre`;
* the spectral half is `Work.SlotWord.FibreSpec.tBdiagFormInd_fibre`, whose only extra hypothesis is
  the joint `(p, y)`-integrability of the fibre amplitude integrand — supplied here, with **no**
  boundedness or decay hypothesis on the state beyond smoothness, by the uniform-in-`y` `p`-decay
  `Work.SlotWord.fibreAmpDecay` through
  `Work.SlotWord.integrable_tBdiagFibreJoint_of_decay`.

The integrability conjunct of the fibre integrand is then the sum of the (constant times) gap
integrability `Work.SlotWord.integrable_fibre_cnPlusBoxInd` — which needs only an absolute bound of
the state on `abox n ℓ`, obtained from compactness — and the spectral integrability
`Work.SlotWord.integrable_fibre_tBdiagFormInd_of_decay`. -/

namespace Work.BoseFixB1B

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-- **The kinetic word of a slot piece as the outside-configuration integral of the kinetic word of
its fibre.**

For `0 < L`, `0 < d`, a state `Φ` that is smooth and absolutely bounded by `Cb` on the analysis box
`abox n L`, a slot set `S` and a transport `e : SlotIn n S ≃ Fin S.card`, the FS-faithful kinetic
word `tBwordBInd` of the slot piece `slotPiece (dlBox L d u) S Φ` at the particle number `n` equals
the integral, over the outside configurations of the sliding box, of the `|S|`-particle kinetic word
of the fibre `pieceFibre (dlBox L d u) S e Φ y`; and that fibre integrand is integrable on
`volume.restrict (slotOutside L (dlBox L d u) S)`.

Both halves of `𝒯_B` are factorised at the piece: the gap half by
`Work.SlotWord.FibreGap.cnPlusBoxInd_fibre`, the spectral half by
`Work.SlotWord.FibreSpec.tBdiagFormInd_fibre` with the joint integrability produced by
`Work.SlotWord.fibreAmpDecay` + `Work.SlotWord.integrable_tBdiagFibreJoint_of_decay`. -/
private theorem tBwordBInd_piece_fibre {n : ℕ} (L d ε c : ℝ) (hL : 0 < L) (hd : 0 < d)
    (u : EuclideanSpace ℝ (Fin 3)) {Φ : Submission.BoseGases.X n → ℝ}
    (hΦd : ContDiff ℝ (⊤ : ENat) Φ) {Cb : ℝ} (hCb0 : 0 ≤ Cb)
    (hCb : ∀ x ∈ Submission.BoseGases.abox n L, |Φ x| ≤ Cb)
    (S : Finset (Fin n)) (e : Work.PerSector.SlotIn n S ≃ Fin S.card) :
    MeasureTheory.Integrable
        (fun y : Work.PerSector.SlotOut n S → EuclideanSpace ℝ (Fin 3) =>
          Work.UBBInputs8.tBwordBInd S.card L d ε c u
            (Work.SlotWord.pieceFibre (Submission.BoseGases.dlBox L d u) S e Φ y))
        ((MeasureTheory.volume : MeasureTheory.Measure
          (Work.PerSector.SlotOut n S → EuclideanSpace ℝ (Fin 3))).restrict
          (Work.PerSector.slotOutside L (Submission.BoseGases.dlBox L d u) S))
    ∧ Work.UBBInputs8.tBwordBInd n L d ε c u
          (Work.PerSector.slotPiece (Submission.BoseGases.dlBox L d u) S Φ)
        = ∫ y in Work.PerSector.slotOutside L (Submission.BoseGases.dlBox L d u) S,
            Work.UBBInputs8.tBwordBInd S.card L d ε c u
              (Work.SlotWord.pieceFibre (Submission.BoseGases.dlBox L d u) S e Φ y) := by
  classical
  have hΦc : Continuous Φ := hΦd.continuous
  have hΦm : Measurable Φ := hΦc.measurable
  have hfsKin_meas : ∀ c : ℝ, Measurable (Submission.BoseGases.fsKinCoeff c) := by
    intro c
    unfold Submission.BoseGases.fsKinCoeff
    fun_prop
  -- the uniform-in-`y` `p`-decay of the fibre amplitude, and the joint `(p,y)`-integrability
  obtain ⟨Cd, hCd0, hdec⟩ := Work.SlotWord.fibreAmpDecay L d hL hd u S hΦd e
  have hjoint := Work.SlotWord.integrable_tBdiagFibreJoint_of_decay L d c hL hd u S hΦm e
    ⟨Cd, hCd0, hdec⟩
  -- the two fibre factorisations at the slot piece
  have hgap := Work.SlotWord.FibreGap.cnPlusBoxInd_fibre L d hL hd u S Φ hΦc e
  have hspec := Work.SlotWord.FibreSpec.tBdiagFormInd_fibre L d hL hd u S Φ hΦc e
      (Submission.BoseGases.fsKinCoeff c) (fun r => Submission.BoseGases.fsKinCoeff_nonneg c r)
      (hfsKin_meas c) hjoint
  -- the integrability of the two fibre halves
  have hgapI : MeasureTheory.Integrable
      (fun y : Work.PerSector.SlotOut n S → EuclideanSpace ℝ (Fin 3) =>
        Work.UBBInputs8.cnPlusBoxInd L (Submission.BoseGases.dlBox L d u)
          (Work.SmallBoxSliding.boxMass L d u)
          (Work.PerSector.slotFibreState S e
            (Work.PerSector.slotPiece (Submission.BoseGases.dlBox L d u) S Φ) y))
      ((MeasureTheory.volume : MeasureTheory.Measure
        (Work.PerSector.SlotOut n S → EuclideanSpace ℝ (Fin 3))).restrict
        (Work.PerSector.slotOutside L (Submission.BoseGases.dlBox L d u) S)) :=
    Work.SlotWord.integrable_fibre_cnPlusBoxInd L hL
      (Work.SmallBoxSliding.measurableSet_dlBox L d u)
      (Work.SmallBoxSliding.dlBox_subset_acube L d u)
      (Work.SmallBoxSliding.boxMass L d u) S e hΦm hCb0 hCb
  have hspecI := Work.SlotWord.integrable_fibre_tBdiagFormInd_of_decay L d c hL hd u S hΦm e
    ⟨Cd, hCd0, hdec⟩
  refine ⟨?_, ?_⟩
  · refine ((hgapI.const_mul (Work.SmallBoxTBWord.tbGapCoeff (L * d) ε)).add hspecI).congr ?_
    filter_upwards with y
    simp only [Pi.add_apply, Work.UBBInputs8.tBwordBInd, Work.UBBInputs8.tBwordInd,
      Work.UBBInputs8.tBwordKinInd, Work.SlotWord.pieceFibre]
  · calc Work.UBBInputs8.tBwordBInd n L d ε c u
          (Work.PerSector.slotPiece (Submission.BoseGases.dlBox L d u) S Φ)
        = Work.SmallBoxTBWord.tbGapCoeff (L * d) ε
            * Work.UBBInputs8.cnPlusBoxInd L (Submission.BoseGases.dlBox L d u)
                (Work.SmallBoxSliding.boxMass L d u)
                (Work.PerSector.slotPiece (Submission.BoseGases.dlBox L d u) S Φ)
          + Work.UBBInputs8.tBdiagFormInd L (Submission.BoseGases.dlBox L d u)
                (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiB L d u)
                (Submission.BoseGases.fsKinCoeff c)
                (Work.PerSector.slotPiece (Submission.BoseGases.dlBox L d u) S Φ) := by
          simp only [Work.UBBInputs8.tBwordBInd, Work.UBBInputs8.tBwordInd,
            Work.UBBInputs8.tBwordKinInd]
      _ = Work.SmallBoxTBWord.tbGapCoeff (L * d) ε
            * (∫ y in Work.PerSector.slotOutside L (Submission.BoseGases.dlBox L d u) S,
                Work.UBBInputs8.cnPlusBoxInd L (Submission.BoseGases.dlBox L d u)
                  (Work.SmallBoxSliding.boxMass L d u)
                  (Work.PerSector.slotFibreState S e
                    (Work.PerSector.slotPiece (Submission.BoseGases.dlBox L d u) S Φ) y))
          + (∫ y in Work.PerSector.slotOutside L (Submission.BoseGases.dlBox L d u) S,
                Work.UBBInputs8.tBdiagFormInd L (Submission.BoseGases.dlBox L d u)
                  (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiB L d u)
                  (Submission.BoseGases.fsKinCoeff c)
                  (Work.PerSector.slotFibreState S e
                    (Work.PerSector.slotPiece (Submission.BoseGases.dlBox L d u) S Φ) y)) := by
          rw [hgap, hspec]
      _ = ∫ y in Work.PerSector.slotOutside L (Submission.BoseGases.dlBox L d u) S,
            (Work.SmallBoxTBWord.tbGapCoeff (L * d) ε
              * Work.UBBInputs8.cnPlusBoxInd L (Submission.BoseGases.dlBox L d u)
                  (Work.SmallBoxSliding.boxMass L d u)
                  (Work.PerSector.slotFibreState S e
                    (Work.PerSector.slotPiece (Submission.BoseGases.dlBox L d u) S Φ) y)
            + Work.UBBInputs8.tBdiagFormInd L (Submission.BoseGases.dlBox L d u)
                  (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiB L d u)
                  (Submission.BoseGases.fsKinCoeff c)
                  (Work.PerSector.slotFibreState S e
                    (Work.PerSector.slotPiece (Submission.BoseGases.dlBox L d u) S Φ) y)) := by
          rw [MeasureTheory.integral_add
              (hgapI.const_mul (Work.SmallBoxTBWord.tbGapCoeff (L * d) ε)) hspecI,
            MeasureTheory.integral_const_mul]
      _ = ∫ y in Work.PerSector.slotOutside L (Submission.BoseGases.dlBox L d u) S,
            Work.UBBInputs8.tBwordBInd S.card L d ε c u
              (Work.SlotWord.pieceFibre (Submission.BoseGases.dlBox L d u) S e Φ y) := by
          refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
          simp only [Work.UBBInputs8.tBwordBInd, Work.UBBInputs8.tBwordInd,
            Work.UBBInputs8.tBwordKinInd, Work.SlotWord.pieceFibre]

theorem slotKinFibre {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v)
    {ε₀ c C : ℝ} (hε₀ : 0 < ε₀) {μ : ℝ} (hμ : Work.BoseBoxFix.Adm v ε₀ μ)
    {u : EuclideanSpace ℝ (Fin 3)}
    (hu : u ∈ Work.SmallBoxSliding.goodSet (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBd v μ) μ)
    {n : ℕ} (Φ : Work.BoseKinLoc.BoxState n (Work.BoseFixB1B.PBℓ v μ)) :
    ∀ S : Finset (Fin n), 0 < S.card → ∀ e : Work.PerSector.SlotIn n S ≃ Fin S.card,
      MeasureTheory.Integrable
          (fun y : Work.PerSector.SlotOut n S → EuclideanSpace ℝ (Fin 3) =>
            Work.UBBInputs8.tBwordBInd S.card (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBd v μ)
              (Work.BoseFixB1B.PBeT v μ) (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) u
              (Work.SlotWord.pieceFibre (Work.BoseFixB1B.PBB v μ u) S e
                (Φ : Submission.BoseGases.X n → ℝ) y))
          ((MeasureTheory.volume : MeasureTheory.Measure
            (Work.PerSector.SlotOut n S → EuclideanSpace ℝ (Fin 3))).restrict
            (Work.PerSector.slotOutside (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBB v μ u) S))
      ∧ Work.UBBInputs8.tBwordBInd n (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBd v μ)
            (Work.BoseFixB1B.PBeT v μ) (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) u
            (Work.PerSector.slotPiece (Work.BoseFixB1B.PBB v μ u) S
              (Φ : Submission.BoseGases.X n → ℝ))
        = ∫ y in Work.PerSector.slotOutside (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBB v μ u) S,
            Work.UBBInputs8.tBwordBInd S.card (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBd v μ)
              (Work.BoseFixB1B.PBeT v μ) (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) u
              (Work.SlotWord.pieceFibre (Work.BoseFixB1B.PBB v μ u) S e
                (Φ : Submission.BoseGases.X n → ℝ) y) := by
  classical
  intro S hS e
  have hL : 0 < Work.BoseFixB1B.PBℓ v μ := Work.BoseFixB1.adm_ell_pos hμ
  have hd : 0 < Work.BoseFixB1B.PBd v μ := Work.BoseFixB1.adm_d_pos hμ
  have hΦc : Continuous ((Φ : Submission.BoseGases.X n → ℝ)) := Φ.contDiff.continuous
  obtain ⟨Cb, hCb0, hCb⟩ : ∃ Cb : ℝ, 0 ≤ Cb ∧
      ∀ x ∈ Submission.BoseGases.abox n (Work.BoseFixB1B.PBℓ v μ),
        |(Φ : Submission.BoseGases.X n → ℝ) x| ≤ Cb := by
    obtain ⟨C₀, hC₀⟩ :=
      (Work.UBBInputs9.B.abox_isCompact n (Work.BoseFixB1B.PBℓ v μ)).exists_bound_of_continuousOn
        hΦc.continuousOn
    refine ⟨max C₀ 0, le_max_right _ _, fun x hx => ?_⟩
    have h1 := hC₀ x hx
    rw [Real.norm_eq_abs] at h1
    exact le_trans h1 (le_max_left _ _)
  have hmain := tBwordBInd_piece_fibre (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBd v μ)
      (Work.BoseFixB1B.PBeT v μ) (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) hL hd u
      Φ.contDiff hCb0 hCb S e
  simp only [Work.BoseFixB1B.PBB]
  exact hmain

end Work.BoseFixB1B
