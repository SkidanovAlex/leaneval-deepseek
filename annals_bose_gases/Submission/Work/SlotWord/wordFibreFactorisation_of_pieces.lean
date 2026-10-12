import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SlotWord.FibreGap.cnPlusBoxInd_fibre
import Submission.Work.SlotWord.FibreSpec.tBdiagFormInd_fibre
import Submission.Work.SlotWord.chiSmallB_support_mem_dlBox
import Submission.Work.SlotWord.qLHSword_slotFibre
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END


namespace Work.SlotWord

theorem wordFibreFactorisation_of_pieces {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    {h : Work.UBB.ScatSol v} {M : ℕ} {L d ε c μ : ℝ} {u : EuclideanSpace ℝ (Fin 3)} {N : ℕ}
    {Φ : Submission.BoseGases.X N → ℝ} (hM : 1 ≤ M) (hL : 0 < L) (hd : 0 < d)
    (hΦ : Continuous Φ)
    (hPotN : ∀ S : Finset (Fin N), 0 < S.card → ∀ e : Work.PerSector.SlotIn N S ≃ Fin S.card,
      MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
        (Work.PerSector.slotPiece (Submission.BoseGases.dlBox L d u) S Φ x) ^ 2
          * (Submission.BoseGases.qLHSden N L μ (Submission.BoseGases.wSmallPair M L d u v)
              (Submission.BoseGases.wSmall1Pair h M L d u) x)) (Submission.BoseGases.abox N L))
    (hPotI : ∀ S : Finset (Fin N), 0 < S.card → ∀ e : Work.PerSector.SlotIn N S ≃ Fin S.card,
      MeasureTheory.Integrable
        (fun y : Work.PerSector.SlotOut N S → EuclideanSpace ℝ (Fin 3) =>
          Submission.BoseGases.qLHSword (N := S.card) L μ
            (Submission.BoseGases.wSmallPair M L d u v)
            (Submission.BoseGases.wSmall1Pair h M L d u)
            (Work.PerSector.slotFibreState S e
              (Work.PerSector.slotPiece (Submission.BoseGases.dlBox L d u) S Φ) y))
        ((MeasureTheory.volume : MeasureTheory.Measure
            (Work.PerSector.SlotOut N S → EuclideanSpace ℝ (Fin 3))).restrict
          (Work.PerSector.slotOutside L (Submission.BoseGases.dlBox L d u) S)))
    (hGapI : ∀ S : Finset (Fin N), 0 < S.card → ∀ e : Work.PerSector.SlotIn N S ≃ Fin S.card,
      MeasureTheory.Integrable
        (fun y : Work.PerSector.SlotOut N S → EuclideanSpace ℝ (Fin 3) =>
          Work.UBBInputs8.cnPlusBoxInd L (Submission.BoseGases.dlBox L d u)
            (Work.SmallBoxSliding.boxMass L d u)
            (Work.PerSector.slotFibreState S e
              (Work.PerSector.slotPiece (Submission.BoseGases.dlBox L d u) S Φ) y))
        ((MeasureTheory.volume : MeasureTheory.Measure
            (Work.PerSector.SlotOut N S → EuclideanSpace ℝ (Fin 3))).restrict
          (Work.PerSector.slotOutside L (Submission.BoseGases.dlBox L d u) S)))
    (hSpecI : ∀ S : Finset (Fin N), 0 < S.card → ∀ e : Work.PerSector.SlotIn N S ≃ Fin S.card,
      MeasureTheory.Integrable
        (fun y : Work.PerSector.SlotOut N S → EuclideanSpace ℝ (Fin 3) =>
          Work.UBBInputs8.tBdiagFormInd L (Submission.BoseGases.dlBox L d u)
            (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiB L d u)
            (Submission.BoseGases.fsKinCoeff c)
            (Work.PerSector.slotFibreState S e
              (Work.PerSector.slotPiece (Submission.BoseGases.dlBox L d u) S Φ) y))
        ((MeasureTheory.volume : MeasureTheory.Measure
            (Work.PerSector.SlotOut N S → EuclideanSpace ℝ (Fin 3))).restrict
          (Work.PerSector.slotOutside L (Submission.BoseGases.dlBox L d u) S)))
    (hswap : ∀ S : Finset (Fin N), 0 < S.card → ∀ e : Work.PerSector.SlotIn N S ≃ Fin S.card,
      MeasureTheory.Integrable
        (fun q : EuclideanSpace ℝ (Fin 3) ×
            (Work.PerSector.SlotOut N S → EuclideanSpace ℝ (Fin 3)) =>
          Work.SlotWord.tBdiagFibreJoint L d u S Φ e (Submission.BoseGases.fsKinCoeff c) q.1 q.2)
        ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
          ((MeasureTheory.volume : MeasureTheory.Measure
              (Work.PerSector.SlotOut N S → EuclideanSpace ℝ (Fin 3))).restrict
            (Work.PerSector.slotOutside L (Submission.BoseGases.dlBox L d u) S)))) :
    Work.SlotWord.WordFibreFactorisation h M L d ε c μ u N Φ := by
  intro S hS e
  have hfsKin_meas : Measurable (Submission.BoseGases.fsKinCoeff c) := by
    have h : Submission.BoseGases.fsKinCoeff c = fun r : ℝ => (max (r - c) 0) ^ 2 := rfl
    rw [h]
    fun_prop
  have hgap := Work.SlotWord.FibreGap.cnPlusBoxInd_fibre (N := N) L d hL hd u S Φ hΦ e
  have hspec := Work.SlotWord.FibreSpec.tBdiagFormInd_fibre (N := N) L d hL hd u S Φ hΦ e
      (Submission.BoseGases.fsKinCoeff c) (fun r => Submission.BoseGases.fsKinCoeff_nonneg c r)
      hfsKin_meas (hswap S hS e)
  have hsupp1 : ∀ x : EuclideanSpace ℝ (Fin 3), x ∉ Submission.BoseGases.dlBox L d u →
      ∀ y : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.wSmall1Pair h M L d u x y = 0 := by
    intro x hx y
    have h0 : Submission.BoseGases.chiSmallB M L d u x = 0 := by
      by_contra hne
      exact hx (chiSmallB_support_mem_dlBox hM hL hd hne)
    rw [Submission.BoseGases.wSmall1Pair, Submission.BoseGases.wSmallPair, h0]
    ring
  have hsupp2 : ∀ x y : EuclideanSpace ℝ (Fin 3),
      (x ∉ Submission.BoseGases.dlBox L d u ∨ y ∉ Submission.BoseGases.dlBox L d u) →
      Submission.BoseGases.wSmallPair M L d u v x y = 0 := by
    intro x y hxy
    rcases hxy with hx | hy
    · have h0 : Submission.BoseGases.chiSmallB M L d u x = 0 := by
        by_contra hne
        exact hx (chiSmallB_support_mem_dlBox hM hL hd hne)
      rw [Submission.BoseGases.wSmallPair, h0]
      ring
    · have h0 : Submission.BoseGases.chiSmallB M L d u y = 0 := by
        by_contra hne
        exact hy (chiSmallB_support_mem_dlBox hM hL hd hne)
      rw [Submission.BoseGases.wSmallPair, h0]
      ring
  have hpot := qLHSword_slotFibre (N := N) L d μ u S Φ e
      (Submission.BoseGases.wSmallPair M L d u v) (Submission.BoseGases.wSmall1Pair h M L d u)
      hsupp1 hsupp2 (hPotN S hS e)
  have htB : MeasureTheory.Integrable
      (fun y : Work.PerSector.SlotOut N S → EuclideanSpace ℝ (Fin 3) =>
        Work.UBBInputs8.tBwordBInd S.card L d ε c u
          (pieceFibre (Submission.BoseGases.dlBox L d u) S e Φ y))
      ((MeasureTheory.volume : MeasureTheory.Measure
          (Work.PerSector.SlotOut N S → EuclideanSpace ℝ (Fin 3))).restrict
        (Work.PerSector.slotOutside L (Submission.BoseGases.dlBox L d u) S)) :=
    ((hGapI S hS e).const_mul (Work.SmallBoxTBWord.tbGapCoeff (L * d) ε)).add (hSpecI S hS e)
  have hpI : MeasureTheory.Integrable
      (fun y : Work.PerSector.SlotOut N S → EuclideanSpace ℝ (Fin 3) =>
        Work.SmallBoxSliding.qLHSwordB (N := S.card) h M L d μ u
          (pieceFibre (Submission.BoseGases.dlBox L d u) S e Φ y))
      ((MeasureTheory.volume : MeasureTheory.Measure
          (Work.PerSector.SlotOut N S → EuclideanSpace ℝ (Fin 3))).restrict
        (Work.PerSector.slotOutside L (Submission.BoseGases.dlBox L d u) S)) := by
    simpa only [Work.SmallBoxSliding.qLHSwordB, pieceFibre] using hPotI S hS e
  have hTbid : (∫ y in Work.PerSector.slotOutside L (Submission.BoseGases.dlBox L d u) S,
        Work.UBBInputs8.tBwordBInd S.card L d ε c u (pieceFibre (Submission.BoseGases.dlBox L d u) S e Φ y))
      = Work.UBBInputs8.tBwordBInd N L d ε c u
          (Work.PerSector.slotPiece (Submission.BoseGases.dlBox L d u) S Φ) := by
    have hInt1 : MeasureTheory.Integrable
        (fun y : Work.PerSector.SlotOut N S → EuclideanSpace ℝ (Fin 3) =>
          Work.SmallBoxTBWord.tbGapCoeff (L * d) ε *
            Work.UBBInputs8.cnPlusBoxInd L (Submission.BoseGases.dlBox L d u)
              (Work.SmallBoxSliding.boxMass L d u)
              (Work.PerSector.slotFibreState S e
                (Work.PerSector.slotPiece (Submission.BoseGases.dlBox L d u) S Φ) y))
        ((MeasureTheory.volume : MeasureTheory.Measure
            (Work.PerSector.SlotOut N S → EuclideanSpace ℝ (Fin 3))).restrict
          (Work.PerSector.slotOutside L (Submission.BoseGases.dlBox L d u) S)) :=
      (hGapI S hS e).const_mul _
    simp only [Work.UBBInputs8.tBwordBInd, Work.UBBInputs8.tBwordInd, Work.UBBInputs8.tBwordKinInd, pieceFibre]
    rw [MeasureTheory.integral_add hInt1 (hSpecI S hS e), MeasureTheory.integral_const_mul,
      ← hgap, ← hspec]
  have hPotid : (∫ y in Work.PerSector.slotOutside L (Submission.BoseGases.dlBox L d u) S,
        Work.SmallBoxSliding.qLHSwordB (N := S.card) h M L d μ u
          (pieceFibre (Submission.BoseGases.dlBox L d u) S e Φ y))
      = Work.SmallBoxSliding.qLHSwordB (N := N) h M L d μ u
          (Work.PerSector.slotPiece (Submission.BoseGases.dlBox L d u) S Φ) := by
    simp only [Work.SmallBoxSliding.qLHSwordB, pieceFibre]
    exact hpot.symm
  simp only [fibreWord]
  rw [MeasureTheory.integral_add htB hpI, hTbid, hPotid]


end Work.SlotWord
