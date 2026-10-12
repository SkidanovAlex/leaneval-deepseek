import ChallengeDeps
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1B.kineticHalfAssembly
import Submission.Work.BoseFixB1B.matchedSlidingBCube
import Submission.Work.BoseFixB1S.aestronglyMeasurable_cnPlusBoxInd
import Submission.Work.BoseFixB1S.aestronglyMeasurable_cubeSpectral
import Submission.Work.BoseFixB1S.cubeSpectral_uniformBound
import Submission.Work.BoseFixB1S.sbCubeAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1B.oneBodyKineticHalfCube_of_mainWord`

The matched-window (single cube cutoff) `N = 1` kinetic half `OneBodyKineticHalfCube`
(`matchedSlidingBCube.lean`) from the **main word** statement `hmain`.

## What is proved

`hmain` is the spectral half of the cube-windowed kinetic inequality, stated against the *frozen*
large-box word `Work.BoseKinLoc.mainWord` and the frozen anchored gap coefficient `bValue/(2ℓ²)`:

    ∫_u cubeSpectral v μ φ u  ≤  mainWord ℓ d s εT 0 (slotFun1 φ) + (bValue/(2ℓ²))·cnPlus ℓ φ .

The target `OneBodyKineticHalfCube` asks for

    (b/(2ℓ²))·cnPlus ℓ φ + ∫_u sbKinCube v μ φ u  ≤  kinFormB 1 ℓ d s εT b φ .

Since `sbKinCube = bGapCoeff·n₊(B(u)) + cubeSpectral` **pointwise** (`rfl`), the only two inputs
besides `hmain` are

* the sliding **gap pairing** `KH.gap_pairing` (`∫_u n₊(B(u)) ≤ (1+π⁻²)·neuFrac`), multiplied by
  the nonnegative `bGapCoeff`, giving `bGapCoeff·∫_u n₊ ≤ neuWord` — the *frozen* statement, since
  `bGapCoeff v μ = tbGapCoeff (ℓd) εT` and the sliding box of `sbKinCube` is *literally* the
  frozen one `dlBox ℓ d u` (`bSide v μ = sideAt μ (a v)`, `bD v μ = (paramsAt μ (a v)).d`);
* the `u`-**marginal integrability** of the two summands, which makes `∫ (f + g) = ∫ f + ∫ g`
  available so that the spectral half `∫ cubeSpectral` can be bounded by `hmain` separately.  The
  two integrability statements are proved here by copying (with attribution) the two private
  helpers `integrable_cubeSpectral` / `integrable_gapHalf` of
  `Submission/Work/BoseFixB1S/sbWordCubeIntegrable.lean`, whose only hypotheses are `ℓ > 0`,
  `d > 0`, `M ≥ 4`, `ε ≥ 0` and `ContDiff φ` — all available from `Adm` (there is **no**
  hypothesis on `v` beyond `ScatSol`).

The bookkeeping is then the frozen one of `Work.BoseFixB1B.oneBodyKineticHalf_of_inputs`
(`kineticHalfAssembly.lean` §1): `fsT = neuWord + gapWord + momWord + mainWord` (`rfl`),
`gapWord ℓ b 0 ψ = bℓ⁻²·cnPlus`, `momWord ≥ 0`, and `b = bValue`.

## Status

Complete (no placeholder); axiom-clean:
`#print axioms Work.BoseFixB1B.oneBodyKineticHalfCube_of_mainWord`
= `[propext, Classical.choice, Quot.sound]`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseFixB1B

local notation "E3" => EuclideanSpace ℝ (Fin 3)

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding

set_option maxHeartbeats 1000000

/-! ## 1. The `u`-marginal integrability of the two summands of `sbKinCube`

The three lemmas below are verbatim copies of the *private* helpers `integrable_of_support_bound`,
`integrable_cubeSpectral` and `integrable_gapHalf` of the colleague-owned
`Submission/Work/BoseFixB1S/sbWordCubeIntegrable.lean` (private declarations cannot be imported),
made public here so that the split `∫ (bGapCoeff·n₊ + cubeSpectral) = ∫ bGapCoeff·n₊ + ∫ cubeSpectral`
is available.  Their hypotheses are the minimal ones (`0 < ℓ`, `0 < d`, `4 ≤ M`, `0 ≤ ε`,
`ContDiff φ`). -/

/-- A function that is a.e. strongly measurable, bounded by `B` and vanishes off a measurable set
of finite measure is integrable. -/
private lemma integrable_of_support_bound_obk {K : Set E3} {B : ℝ} {f : E3 → ℝ}
    (hK : MeasurableSet K) (hKfin : (MeasureTheory.volume : MeasureTheory.Measure E3) K ≠ ⊤)
    (hf : AEMeasurable f MeasureTheory.volume) (_hB : 0 ≤ B)
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
private lemma integrable_cubeSpectral_obk {ℓ d c : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) {M : ℕ}
    (hM : 4 ≤ M) {N : ℕ} {Φ : Submission.BoseGases.X N → ℝ}
    (hΦ : ContDiff ℝ (⊤ : ENat) Φ) :
    MeasureTheory.Integrable (fun u : E3 =>
      Work.UBBInputs8.tBwordKinInd ℓ (Submission.BoseGases.dlBox ℓ d u)
        (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.chiSmallB M ℓ d u) c Φ) := by
  obtain ⟨K, hK0, hKbd⟩ :=
    Work.BoseFixB1S.cubeSpectral_uniformBound (M := M) hM hℓ hd (N := N) hΦ
  have hmeas : AEMeasurable (fun u : E3 =>
      Work.UBBInputs8.tBwordKinInd ℓ (Submission.BoseGases.dlBox ℓ d u)
        (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.chiSmallB M ℓ d u) c Φ)
      MeasureTheory.volume :=
    (Work.BoseFixB1S.aestronglyMeasurable_cubeSpectral (M := M) (by omega) hℓ hd (N := N)
      hΦ.continuous).aemeasurable
  have hKfin : (MeasureTheory.volume : MeasureTheory.Measure E3)
      (Submission.BoseGases.acube ((1 + d) / d)) ≠ ⊤ :=
    ne_of_lt (Submission.BoseGases.acube_lt_top _ (by positivity))
  refine integrable_of_support_bound_obk (K := Submission.BoseGases.acube ((1 + d) / d))
    (B := K) (Submission.BoseGases.acube_measurable _) hKfin hmeas hK0 ?_ ?_
  · intro u hu
    exact Work.BoseFixB1S.SbCubeAux.tBwordKinInd_cube_eq_zero_of_far (M := M) (by omega) hℓ hd
      Φ hu
  · intro u
    rw [abs_of_nonneg (Work.BoseFixB1.tBwordKinInd_nonneg (a := ℓ)
      (A := Submission.BoseGases.dlBox ℓ d u)
      (volA := Work.SmallBoxSliding.boxMass ℓ d u)
      (χ := Submission.BoseGases.chiSmallB M ℓ d u) (c := c) Φ)]
    exact hKbd u

/-- **The gap (excited-count) half is `u`-integrable**: it is a nonnegative summand of the
`u`-marginal-integrable frozen word `tBwordBInd` (`Work.BoseFixB1.integrable_tBwordBInd`), and it
is a.e. strongly measurable in `u` (`aestronglyMeasurable_cnPlusBoxInd`). -/
private lemma integrable_gapHalf_obk {ℓ d ε c : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hε : 0 ≤ ε)
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
    (Work.BoseFixB1S.aestronglyMeasurable_cnPlusBoxInd hℓ hd (N := N) hΦ.continuous).const_mul _
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

/-! ## 2. The one-body cube kinetic half from the main-word statement -/

theorem oneBodyKineticHalfCube_of_mainWord {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hmain : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ φ : Submission.BoseGases.X 1 → ℝ, ContDiff ℝ (⊤ : ENat) φ →
        (∫ u : EuclideanSpace ℝ (Fin 3), Work.BoseFixB1B.cubeSpectral v μ φ u)
          ≤ Work.BoseKinLoc.mainWord (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT 0
                (Work.BSKinetic.slotFun1 φ)
            + (Work.BoseBox.bValue / (2 * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 2))
                * Submission.BoseGases.cnPlus (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) φ) :
    Work.BoseFixB1B.OneBodyKineticHalfCube v h := by
  obtain ⟨ε₀, hε₀, hmain'⟩ := hmain
  unfold Work.BoseFixB1B.OneBodyKineticHalfCube
  refine ⟨ε₀, hε₀, ?_⟩
  intro μ hAdm φ hφ
  -- positivity at FS's parameters
  have hℓpos : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) :=
    Work.BoseFixB1.adm_ell_pos hAdm
  have hdpos : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d :=
    Work.BoseFixB1.adm_d_pos hAdm
  have heT0' : 0 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT :=
    (Work.BoseFixB1.adm_eT_bounds hAdm).1
  have hM4 : 4 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M := by
    rw [Work.BoseFixB1.M_eq_mValue]; norm_num [Work.BoseBox.mValue]
  have hb0' : 0 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).b :=
    le_of_lt (Work.BoseFixB1.paramsAt_b_pos μ (_root_.BoseGases.a v))
  -- abbreviations
  set ℓ : ℝ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v) with hℓd
  set d : ℝ := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d with hdd
  set s : ℝ := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s with hsd
  set eT : ℝ := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT with heTd
  set b : ℝ := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).b with hbd
  set M : ℕ := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M with hMd
  set cc : ℝ := Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v) with hccd
  set ψ : E3 → ℝ := Work.BSKinetic.slotFun1 φ with hψd
  have hℓpos' : 0 < ℓ := hℓpos
  have hdpos' : 0 < d := hdpos
  have heT0 : 0 ≤ eT := heT0'
  have hb0 : 0 ≤ b := hb0'
  have hM4' : 4 ≤ M := hM4
  have hbval : b = Work.BoseBox.bValue := by
    rw [hbd]; exact Work.BoseFixB1.paramsAt_b_eq μ (_root_.BoseGases.a v)
  have hψc : ContDiff ℝ (⊤ : ENat) ψ := by
    rw [hψd]; exact hφ.comp (by fun_prop)
  have hφψ : (fun x : Submission.BoseGases.X 1 => ψ (x 0)) = φ := by
    funext x
    have hx : (fun _ : Fin 1 => x 0) = x := by funext j; fin_cases j; rfl
    rw [hψd, Work.BSKinetic.slotFun1, hx]
  -- ## the gap half: `∫_u n₊(B(u))` paired with the sliding Neumann fraction
  have hgap_raw := Work.BoseFixB1.KH.gap_pairing hℓpos' hdpos' ψ hψc
  have hgapeq : Work.SmallBoxTBWord.tbGapCoeff (ℓ * d) eT * (1 + (Real.pi ^ 2)⁻¹)
      = (1 / 2) * eT * (d * ℓ) ^ (-2 : ℤ) := by
    rw [show (d * ℓ) ^ (-2 : ℤ) = ((ℓ * d) ^ 2)⁻¹ by
      rw [show (-2 : ℤ) = -(2 : ℤ) by norm_num, zpow_neg, zpow_ofNat]
      congr 1
      ring]
    rw [Work.SmallBoxTBWord.tbGapCoeff, Work.SmallBoxTBWord.tbPiFactor]
    have hpi : (1 + (Real.pi ^ 2)⁻¹) ≠ 0 := by positivity
    field_simp
  have hgap1 : Work.SmallBoxTBWord.tbGapCoeff (ℓ * d) eT *
        (∫ u : E3, Work.UBBInputs8.cnPlusBoxInd ℓ (Submission.BoseGases.dlBox ℓ d u)
          (Work.SmallBoxSliding.boxMass ℓ d u) φ)
      ≤ Work.BoseKinLoc.neuWord ℓ d eT 0 ψ := by
    have h1 : (∫ u : E3, Work.UBBInputs8.cnPlusBoxInd ℓ (Submission.BoseGases.dlBox ℓ d u)
          (Work.SmallBoxSliding.boxMass ℓ d u) φ)
        ≤ (1 + (Real.pi ^ 2)⁻¹) *
            Work.BoseKinLoc.neuFrac ℓ ((d * ℓ) ^ (-2 : ℤ)) 0 (Work.BoseKinLoc.Qfree ℓ 0 ψ) := by
      rw [← hφψ]
      exact hgap_raw
    have h2 : Work.SmallBoxTBWord.tbGapCoeff (ℓ * d) eT *
          ((1 + (Real.pi ^ 2)⁻¹) *
            Work.BoseKinLoc.neuFrac ℓ ((d * ℓ) ^ (-2 : ℤ)) 0 (Work.BoseKinLoc.Qfree ℓ 0 ψ))
        = Work.BoseKinLoc.neuWord ℓ d eT 0 ψ := by
      rw [← mul_assoc, hgapeq, Work.BoseFixB1.neuWord_zero]
      rfl
    calc Work.SmallBoxTBWord.tbGapCoeff (ℓ * d) eT *
          (∫ u : E3, Work.UBBInputs8.cnPlusBoxInd ℓ (Submission.BoseGases.dlBox ℓ d u)
            (Work.SmallBoxSliding.boxMass ℓ d u) φ)
        ≤ Work.SmallBoxTBWord.tbGapCoeff (ℓ * d) eT *
            ((1 + (Real.pi ^ 2)⁻¹) *
              Work.BoseKinLoc.neuFrac ℓ ((d * ℓ) ^ (-2 : ℤ)) 0 (Work.BoseKinLoc.Qfree ℓ 0 ψ)) :=
            mul_le_mul_of_nonneg_left h1 (Work.SmallBoxTBWord.tbGapCoeff_nonneg heT0)
      _ = Work.BoseKinLoc.neuWord ℓ d eT 0 ψ := h2
  -- ## the pointwise split of `sbKinCube` and the `u`-marginal integrability of both halves
  have hIntF : MeasureTheory.Integrable (fun u : E3 =>
      Work.SmallBoxTBWord.tbGapCoeff (ℓ * d) eT *
        Work.UBBInputs8.cnPlusBoxInd ℓ (Submission.BoseGases.dlBox ℓ d u)
          (Work.SmallBoxSliding.boxMass ℓ d u) φ) :=
    integrable_gapHalf_obk (N := 1) (c := cc) hℓpos' hdpos' heT0 (Φ := φ) hφ
  have hIntG : MeasureTheory.Integrable (fun u : E3 =>
      Work.UBBInputs8.tBwordKinInd ℓ (Submission.BoseGases.dlBox ℓ d u)
        (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.chiSmallB M ℓ d u) cc φ) :=
    integrable_cubeSpectral_obk (N := 1) hℓpos' hdpos' hM4' (Φ := φ) hφ
  have hIntG' : MeasureTheory.Integrable (fun u : E3 => cubeSpectral v μ φ u) := by
    simpa only [cubeSpectral, Work.BoseFixB1.bSide, Work.BoseFixB1.bD, Work.BoseFixB1.bA,
      Work.BoseFixB1.bV, Work.BoseFixB1.bM, ← hℓd, ← hdd, ← hMd, ← hccd] using hIntG
  have hsplit : (∫ u : E3, Work.BoseFixB1B.sbKinCube v μ u φ)
      = Work.SmallBoxTBWord.tbGapCoeff (ℓ * d) eT *
          (∫ u : E3, Work.UBBInputs8.cnPlusBoxInd ℓ (Submission.BoseGases.dlBox ℓ d u)
            (Work.SmallBoxSliding.boxMass ℓ d u) φ)
        + (∫ u : E3, Work.BoseFixB1B.cubeSpectral v μ φ u) := by
    rw [← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_add hIntF hIntG']
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [Work.BoseFixB1B.sbKinCube, Work.BoseFixB1B.cubeSpectral, Work.BoseFixB1.bGapCoeff,
      Work.BoseFixB1.bSide, Work.BoseFixB1.bD, Work.BoseFixB1.bA, Work.BoseFixB1.bV,
      Work.BoseFixB1.bM, ← hℓd, ← hdd, ← heTd, ← hMd, ← hccd]
  have hkey : (∫ u : E3, Work.BoseFixB1B.sbKinCube v μ u φ)
      ≤ Work.BoseKinLoc.neuWord ℓ d eT 0 ψ
        + (∫ u : E3, Work.BoseFixB1B.cubeSpectral v μ φ u) := by
    rw [hsplit]
    linarith [hgap1]
  -- ## the spectral half: exactly `hmain`
  have hcubeA : (∫ u : E3, Work.BoseFixB1B.cubeSpectral v μ φ u)
      ≤ Work.BoseKinLoc.mainWord ℓ d s eT 0 ψ
        + (Work.BoseBox.bValue / (2 * ℓ ^ 2)) * Submission.BoseGases.cnPlus ℓ φ := by
    have hK := hmain' μ hAdm φ hφ
    simpa only [← hℓd, ← hdd, ← hsd, ← heTd, ← hψd] using hK
  -- ## the anchored bookkeeping
  have hfsT : Work.BoseKinLoc.kinFormB 1 ℓ d s eT b φ
      = Work.BoseKinLoc.fsT ℓ d s eT b 0 ψ := by
    rw [Work.BoseFixB1.kinHalf_kinFormBOne hℓpos' φ hφ, ← hψd]
  have hfsTdef : Work.BoseKinLoc.fsT ℓ d s eT b 0 ψ
      = Work.BoseKinLoc.neuWord ℓ d eT 0 ψ + Work.BoseKinLoc.gapWord ℓ b 0 ψ
        + Work.BoseKinLoc.momWord ℓ d eT b 0 ψ + Work.BoseKinLoc.mainWord ℓ d s eT 0 ψ := rfl
  have hcn : Submission.BoseGases.cnPlus ℓ φ
      = ∫ z in Submission.BoseGases.acube ℓ,
          (ψ z - (ℓ ^ 3)⁻¹ * ∫ z' in Submission.BoseGases.acube ℓ, ψ z') ^ 2 := by
    rw [Work.BoseFixB1.cnPlus_one_eq hℓpos' φ hφ, ← hψd]
  have hgapW : Work.BoseKinLoc.gapWord ℓ b 0 ψ
      = b * ℓ ^ (-2 : ℤ) * ∫ z in Submission.BoseGases.acube ℓ,
          (ψ z - (ℓ ^ 3)⁻¹ * ∫ z' in Submission.BoseGases.acube ℓ, ψ z') ^ 2 :=
    Work.BoseFixB1.gapWord_zero ψ
  have hmom : 0 ≤ Work.BoseKinLoc.momWord ℓ d eT b 0 ψ :=
    Work.BoseFixB1.momWord_nonneg hb0 heT0 0 ψ
  have hbsum : Work.BoseBox.bValue / (2 * ℓ ^ 2) + Work.BoseBox.bValue / (2 * ℓ ^ 2)
      = b * ℓ ^ (-2 : ℤ) := by
    rw [hbval, show (-2 : ℤ) = -(2 : ℤ) by norm_num, zpow_neg, zpow_ofNat]
    have hℓne : ℓ ≠ 0 := ne_of_gt hℓpos'
    field_simp
    ring
  have hbval2 : b / (2 * ℓ ^ 2) = Work.BoseBox.bValue / (2 * ℓ ^ 2) := by rw [hbval]
  -- ## assemble
  rw [hfsT, hfsTdef, hcn]
  rw [hcn] at hcubeA
  calc b / (2 * ℓ ^ 2) *
        (∫ z in Submission.BoseGases.acube ℓ,
          (ψ z - (ℓ ^ 3)⁻¹ * ∫ z' in Submission.BoseGases.acube ℓ, ψ z') ^ 2)
        + (∫ u : E3, Work.BoseFixB1B.sbKinCube v μ u φ)
      ≤ b / (2 * ℓ ^ 2) *
          (∫ z in Submission.BoseGases.acube ℓ,
            (ψ z - (ℓ ^ 3)⁻¹ * ∫ z' in Submission.BoseGases.acube ℓ, ψ z') ^ 2)
        + (Work.BoseKinLoc.neuWord ℓ d eT 0 ψ
            + (Work.BoseKinLoc.mainWord ℓ d s eT 0 ψ
                + Work.BoseBox.bValue / (2 * ℓ ^ 2) *
                    (∫ z in Submission.BoseGases.acube ℓ,
                      (ψ z - (ℓ ^ 3)⁻¹ * ∫ z' in Submission.BoseGases.acube ℓ,
                        ψ z') ^ 2))) := by
        linarith [hkey, hcubeA]
    _ = Work.BoseKinLoc.neuWord ℓ d eT 0 ψ
          + (b / (2 * ℓ ^ 2) + Work.BoseBox.bValue / (2 * ℓ ^ 2)) *
              (∫ z in Submission.BoseGases.acube ℓ,
                (ψ z - (ℓ ^ 3)⁻¹ * ∫ z' in Submission.BoseGases.acube ℓ, ψ z') ^ 2)
          + Work.BoseKinLoc.mainWord ℓ d s eT 0 ψ := by ring
    _ = Work.BoseKinLoc.neuWord ℓ d eT 0 ψ
          + b * ℓ ^ (-2 : ℤ) *
              (∫ z in Submission.BoseGases.acube ℓ,
                (ψ z - (ℓ ^ 3)⁻¹ * ∫ z' in Submission.BoseGases.acube ℓ, ψ z') ^ 2)
          + Work.BoseKinLoc.mainWord ℓ d s eT 0 ψ := by rw [hbval2, hbsum]
    _ ≤ Work.BoseKinLoc.neuWord ℓ d eT 0 ψ + Work.BoseKinLoc.gapWord ℓ b 0 ψ
        + Work.BoseKinLoc.momWord ℓ d eT b 0 ψ + Work.BoseKinLoc.mainWord ℓ d s eT 0 ψ := by
        rw [hgapW]
        linarith [hmom]

end Work.BoseFixB1B
