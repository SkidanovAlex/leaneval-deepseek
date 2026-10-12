import ChallengeDeps
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1B.matchedSlidingBCube
import Submission.Work.BoseFixB1S.LowCountWindowAllJCube
import Submission.Work.BoseFixB1S.aestronglyMeasurable_cnPlusBoxInd
import Submission.Work.BoseFixB1S.aestronglyMeasurable_cubeSpectral
import Submission.Work.BoseFixB1S.cubeSpectral_uniformBound
import Submission.Work.BoseFixB1S.sbCubeAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- A function that is a.e. strongly measurable, bounded by `B` and vanishes off a measurable set
of finite measure is integrable. -/
private lemma integrable_of_support_bound {K : Set E3} {B : ℝ} {f : E3 → ℝ}
    (hK : MeasurableSet K) (hKfin : (MeasureTheory.volume : MeasureTheory.Measure E3) K ≠ ⊤)
    (hf : AEMeasurable f MeasureTheory.volume) (hB : 0 ≤ B)
    (hzero : ∀ u, u ∉ K → f u = 0) (hb : ∀ u, |f u| ≤ B) :
    MeasureTheory.Integrable f MeasureTheory.volume := by
  have hg : MeasureTheory.Integrable (K.indicator (fun _ : E3 => B)) MeasureTheory.volume := by
    rw [MeasureTheory.integrable_indicator_iff hK]
    exact MeasureTheory.integrableOn_const hKfin (by simp)
  refine MeasureTheory.Integrable.mono' hg hf.aestronglyMeasurable ?_
  filter_upwards with u
  by_cases hu : u ∈ K
  · rw [Set.indicator_of_mem hu, Real.norm_eq_abs]
    exact hb u
  · rw [Set.indicator_of_notMem hu, hzero u hu, norm_zero]

/-- **The cube-windowed spectral slot is `u`-integrable**: bounded uniformly in `u`
(`cubeSpectral_uniformBound`), a.e. strongly measurable in `u`
(`aestronglyMeasurable_cubeSpectral`) and vanishing off the fixed centre cube
(`SbCubeAux.tBwordKinInd_cube_eq_zero_of_far`). -/
private lemma integrable_cubeSpectral {ℓ d c : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) {M : ℕ}
    (hM : 4 ≤ M) {N : ℕ} {Φ : Submission.BoseGases.X N → ℝ}
    (hΦ : ContDiff ℝ (⊤ : ENat) Φ) :
    MeasureTheory.Integrable (fun u : E3 =>
      Work.UBBInputs8.tBwordKinInd ℓ (Submission.BoseGases.dlBox ℓ d u)
        (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.chiSmallB M ℓ d u) c Φ) := by
  obtain ⟨K, hK0, hKbd⟩ := cubeSpectral_uniformBound (M := M) hM hℓ hd (N := N) hΦ
  have hmeas : AEMeasurable (fun u : E3 =>
      Work.UBBInputs8.tBwordKinInd ℓ (Submission.BoseGases.dlBox ℓ d u)
        (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.chiSmallB M ℓ d u) c Φ)
      MeasureTheory.volume :=
    (aestronglyMeasurable_cubeSpectral (M := M) (by omega) hℓ hd (N := N)
      hΦ.continuous).aemeasurable
  have hKfin : (MeasureTheory.volume : MeasureTheory.Measure E3)
      (Submission.BoseGases.acube ((1 + d) / d)) ≠ ⊤ :=
    ne_of_lt (Submission.BoseGases.acube_lt_top _ (by positivity))
  refine integrable_of_support_bound (K := Submission.BoseGases.acube ((1 + d) / d))
    (B := K) (Submission.BoseGases.acube_measurable _) hKfin hmeas hK0 ?_ ?_
  · intro u hu
    exact SbCubeAux.tBwordKinInd_cube_eq_zero_of_far (M := M) (by omega) hℓ hd Φ hu
  · intro u
    rw [abs_of_nonneg (Work.BoseFixB1.tBwordKinInd_nonneg (a := ℓ)
      (A := Submission.BoseGases.dlBox ℓ d u)
      (volA := Work.SmallBoxSliding.boxMass ℓ d u)
      (χ := Submission.BoseGases.chiSmallB M ℓ d u) (c := c) Φ)]
    exact hKbd u

/-- **The gap (excited-count) half is `u`-integrable**: it is a nonnegative summand of the
`u`-marginal-integrable frozen word `tBwordBInd` (`Work.BoseFixB1.integrable_tBwordBInd`), and it
is a.e. strongly measurable in `u` (`aestronglyMeasurable_cnPlusBoxInd`). -/
private lemma integrable_gapHalf {ℓ d ε c : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hε : 0 ≤ ε)
    {N : ℕ} {Φ : Submission.BoseGases.X N → ℝ} (hΦ : ContDiff ℝ (⊤ : ENat) Φ) :
    MeasureTheory.Integrable (fun u : E3 =>
      Work.SmallBoxTBWord.tbGapCoeff (ℓ * d) ε *
        Work.UBBInputs8.cnPlusBoxInd ℓ (Submission.BoseGases.dlBox ℓ d u)
          (Work.SmallBoxSliding.boxMass ℓ d u) Φ) := by
  have hkin : MeasureTheory.Integrable
      (fun u : E3 => Work.UBBInputs8.tBwordBInd N ℓ d ε c u Φ) :=
    Work.BoseFixB1.integrable_tBwordBInd hℓ hd hΦ
  have hmeas : AEStronglyMeasurable (fun u : E3 =>
      Work.SmallBoxTBWord.tbGapCoeff (ℓ * d) ε *
        Work.UBBInputs8.cnPlusBoxInd ℓ (Submission.BoseGases.dlBox ℓ d u)
          (Work.SmallBoxSliding.boxMass ℓ d u) Φ) MeasureTheory.volume :=
    (aestronglyMeasurable_cnPlusBoxInd hℓ hd (N := N) hΦ.continuous).const_mul _
  refine MeasureTheory.Integrable.mono' hkin.norm hmeas ?_
  filter_upwards with u
  have hgap_nn : 0 ≤ Work.SmallBoxTBWord.tbGapCoeff (ℓ * d) ε *
      Work.UBBInputs8.cnPlusBoxInd ℓ (Submission.BoseGases.dlBox ℓ d u)
        (Work.SmallBoxSliding.boxMass ℓ d u) Φ :=
    mul_nonneg (Work.SmallBoxTBWord.tbGapCoeff_nonneg hε) (by
      simp only [Work.UBBInputs8.cnPlusBoxInd]
      exact Finset.sum_nonneg fun i _ => integral_nonneg fun x => sq_nonneg _)
  have hspec_nn : 0 ≤ Work.UBBInputs8.tBdiagFormInd ℓ (Submission.BoseGases.dlBox ℓ d u)
      (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.chiB ℓ d u)
      (Submission.BoseGases.fsKinCoeff c) Φ :=
    Work.BoseFixB1.tBwordKinInd_nonneg (a := ℓ) (A := Submission.BoseGases.dlBox ℓ d u)
      (volA := Work.SmallBoxSliding.boxMass ℓ d u) (χ := Submission.BoseGases.chiB ℓ d u)
      (c := c) Φ
  have hdecomp : Work.UBBInputs8.tBwordBInd N ℓ d ε c u Φ
      = Work.SmallBoxTBWord.tbGapCoeff (ℓ * d) ε *
          Work.UBBInputs8.cnPlusBoxInd ℓ (Submission.BoseGases.dlBox ℓ d u)
            (Work.SmallBoxSliding.boxMass ℓ d u) Φ
        + Work.UBBInputs8.tBdiagFormInd ℓ (Submission.BoseGases.dlBox ℓ d u)
            (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.chiB ℓ d u)
            (Submission.BoseGases.fsKinCoeff c) Φ := rfl
  rw [Real.norm_of_nonneg hgap_nn, hdecomp,
    Real.norm_of_nonneg (add_nonneg hgap_nn hspec_nn)]
  linarith

theorem sbWordCubeIntegrable {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ → ∀ {n : ℕ}
      (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))),
      MeasureTheory.Integrable (fun u : EuclideanSpace ℝ (Fin 3) =>
        Work.BoseFixB1B.sbWordCube v h μ u (Φ : Submission.BoseGases.X n → ℝ)) := by
  obtain ⟨εreg, hεreg_pos, hεreg⟩ := Work.BoseFixB1.regime_sideAt_ge (v := v) hav hR
  refine ⟨min εreg 1, lt_min hεreg_pos one_pos, fun μ hAdm n Φ => ?_⟩
  have hAdmR : Work.BoseBoxFix.Adm v εreg μ := Work.BoseFixB1.Adm.mono hAdm (min_le_left _ _)
  have hμ : 0 < μ := Work.BoseFixB1.adm_mu_pos hAdm
  have hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := Work.BoseFixB1.adm_ell_pos hAdm
  have hdd : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d := Work.BoseFixB1.adm_d_pos hAdm
  have hM1 : 1 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M := by
    rw [Work.BoseFixB1.M_eq_mValue]; norm_num [Work.BoseBox.mValue]
  have hM4 : 4 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M := by
    rw [Work.BoseFixB1.M_eq_mValue]; norm_num [Work.BoseBox.mValue]
  have heT : 0 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT :=
    (Work.BoseFixB1.adm_eT_bounds hAdm).1
  obtain ⟨hreg, hregχ⟩ := hεreg μ hμ (Work.BoseFixB1.adm_dilute hAdmR)
  -- ### the two halves of the kinetic slot, at the frozen (`bSide`/`bD`/`bM`) spelling
  have hspec : MeasureTheory.Integrable (fun u : E3 =>
      Work.UBBInputs8.tBwordKinInd (Work.BoseFixB1.bSide v μ)
        (Submission.BoseGases.dlBox (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) u)
        (Work.SmallBoxSliding.boxMass (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) u)
        (Submission.BoseGases.chiSmallB (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
          (Work.BoseFixB1.bD v μ) u)
        (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v))
        (Φ : Submission.BoseGases.X n → ℝ)) := by
    refine integrable_cubeSpectral (ℓ := Work.BoseFixB1.bSide v μ) (d := Work.BoseFixB1.bD v μ)
      (c := Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) (M := Work.BoseFixB1.bM v μ)
      (N := n) (Φ := (Φ : Submission.BoseGases.X n → ℝ)) ?_ ?_ ?_ ?_
    · show 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
      exact hℓ
    · show 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
      exact hdd
    · show 4 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
      exact hM4
    · exact Φ.contDiff
  have hgap : MeasureTheory.Integrable (fun u : E3 =>
      Work.SmallBoxTBWord.tbGapCoeff
        (Work.BoseFixB1.bSide v μ * Work.BoseFixB1.bD v μ)
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT *
        Work.UBBInputs8.cnPlusBoxInd (Work.BoseFixB1.bSide v μ)
          (Submission.BoseGases.dlBox (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) u)
          (Work.SmallBoxSliding.boxMass (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) u)
          (Φ : Submission.BoseGases.X n → ℝ)) := by
    refine integrable_gapHalf (ℓ := Work.BoseFixB1.bSide v μ) (d := Work.BoseFixB1.bD v μ)
      (ε := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT)
      (c := Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v))
      (N := n) (Φ := (Φ : Submission.BoseGases.X n → ℝ)) ?_ ?_ ?_ ?_
    · show 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
      exact hℓ
    · show 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
      exact hdd
    · exact heT
    · exact Φ.contDiff
  -- ### the kinetic word `sbKinCube`
  have hkin : MeasureTheory.Integrable (fun u : E3 =>
      Work.BoseFixB1B.sbKinCube v μ u (Φ : Submission.BoseGases.X n → ℝ)) := by
    have hsum := hgap.add hspec
    refine hsum.congr (Filter.Eventually.of_forall fun u => ?_)
    rfl
  -- ### the potential word
  have hpot : MeasureTheory.Integrable (fun u : E3 =>
      Work.BoseFixB1.sbPot h μ u (Φ : Submission.BoseGases.X n → ℝ)) :=
    (Work.BoseFixB1.sbPot_integral_le_potWordU (v := v) (h := h) hv1 hvrad hR hv_supp hav
      hℓ hdd hM1 hreg hregχ Φ).1
  -- ### the sum
  have hall := hkin.add hpot
  refine hall.congr (Filter.Eventually.of_forall fun u => ?_)
  rfl

end Work.BoseFixB1S
