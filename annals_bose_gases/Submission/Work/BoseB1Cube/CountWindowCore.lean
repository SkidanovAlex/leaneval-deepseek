import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.AprioriCount.boxM1_eq_w1MassB
import Submission.Work.BoseB1Cube.ConeC.BoseB1Cube_sbWordCube_ge_a0Main_surplus
import Submission.Work.BoseB1Cube.bandErrSmall_holds
import Submission.Work.BoseB1Cube.countAbsorbArith
import Submission.Work.BoseB1Cube.cubeAritySharp
import Submission.Work.BoseB1Cube.cubeSmallNArb12
import Submission.Work.BoseB1Cube.densePairValue
import Submission.Work.BoseB1Cube.nCountB_slotComb_eq
import Submission.Work.BoseB1Cube.rpsi_ge_affine
import Submission.Work.BoseB1Cube.sbKinCube_slotFibre
import Submission.Work.BoseB1Cube.sbWordCube_slotAdditive
import Submission.Work.BoseB1Cube.tendsto_sbWordCube_cutProd
import Submission.Work.BoseFixB1.MDelta.massUpper
import Submission.Work.BoseFixB1B.lowProviderBand
import Submission.Work.BoseFixB1S.mfN0NQ_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseB1Cube

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB Work.BoseFixB1

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# `Submission.Work.BoseB1Cube.CountWindowCore` — the count window `(CW)`, the matched band fibre
# bound, the box-count cap and the *first half* of the assigned node, in a **low module**

These four declarations used to live in `cubeCrudeBand_holds.lean`, but they are the only things the
*nominal* route (`NominalPerBox.lean`, `countWindowOfNominal.lean`, `nomRouteCube.lean`) needs from
that file.  Since the assigned node is now routed through the nominal chain
(`PerBoxFNomSlots ⟹ CountWindow ⟹ CubeCrudeBand`, `Work.BoseB1Cube.cubeCrudeBand_of_slotMu`), the
import had to be reversed: this module carries the shared vocabulary, and
`cubeCrudeBand_holds.lean` imports *it* (instead of the other way round).

Contents (all PROVED, `#print axioms` clean):

* `Work.BoseB1Cube.sbWordCube_ge_neg_bandCount` — the sharp band fibre bound for the matched word;
* `Work.BoseB1Cube.boxCountAt_le_card_mul_normB` — `⟨count⟩ ≤ n‖Φ‖²`;
* `Work.BoseB1Cube.CountWindow` — FS `eq:apriorinn` (`n ≤ Cμℓ³` for low states), one `(ε₀, C)` for
  all thresholds `J ≤ K_B³`;
* `Work.BoseB1Cube.cubeCrudeBand_of_countWindow` — `(CW) ⟹ CubeCrudeBand v h` (`Work.BoseB1Cube.
  cubeCrudeBand_holds`'s first half).
-/

open scoped Topology Real BigOperators ENNReal
/-! ## 1. The sharp band lower bound for the matched word, in box-count form -/

/-- **The matched word on the band dominates `−μ·bandK·bandS²` times the box count.**
`sbWordCube = sbKinCube + sbPot` (`sbWordCube_eq`), the kinetic slot is nonnegative
(`sbKinCube_nonneg`), and `sbPot = pairSum − μ·fibSum` (`sbPot_split`) with `pairSum ≥ 0`
(`pairSum_nonneg`) and the sharp band fibre bound `fibSum ≤ bandK·bandS²·⟨count⟩`
(`fibSum_le_band_boxCount`). -/
theorem sbWordCube_ge_neg_bandCount {v : E3 → ℝ} {h : Work.UBB.ScatSol v} (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    {εr μ : ℝ} (hadmr : Work.BoseBoxFix.Adm v εr μ) {n : ℕ}
    (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))) {u : E3}
    (hu : u ∈ Work.SmallBoxSliding.bandSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ)
    (hRd : R ≤ sideAt μ (a v) * (paramsAt μ (a v)).d / 16)
    (hRχ : R ≤ sideAt μ (a v) * Submission.BoseGases.chiR0) :
    -(μ * (bandK v h (paramsAt μ (a v)).M *
          bandS (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d μ ^ 2))
        * Work.BoseFixB1.boxCountAt (sideAt μ (a v)) (paramsAt μ (a v)).d u
          (Φ : Submission.BoseGases.X n → ℝ)
      ≤ Work.BoseFixB1B.sbWordCube v h μ u (Φ : Submission.BoseGases.X n → ℝ) := by
  have hμ : 0 < μ := adm_mu_pos hadmr
  have hℓ : 0 < sideAt μ (a v) := adm_ell_pos hadmr
  have hd : 0 < (paramsAt μ (a v)).d := adm_d_pos hadmr
  have hM : 1 ≤ (paramsAt μ (a v)).M := by
    rw [M_eq_mValue]; norm_num [Work.BoseBox.mValue]
  have hcont : Continuous (Φ : Submission.BoseGases.X n → ℝ) := Φ.contDiff.continuous
  have hsplit := sbPot_split (v := v) (h := h) (R := R) hv_supp hR hv hvrad hv1 hadmr hcont u
    hRd hRχ
  have hpair : 0 ≤ pairSum v (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u
      (Φ : Submission.BoseGases.X n → ℝ) :=
    pairSum_nonneg (v := v) hv (M := (paramsAt μ (a v)).M) (ℓ := sideAt μ (a v))
      (d := (paramsAt μ (a v)).d) u (Φ : Submission.BoseGases.X n → ℝ)
  have hfib := fibSum_le_band_boxCount (v := v) (h := h) hv hvrad hR hv_supp hM hℓ hd hμ hRd hRχ hu
    (Φ : Submission.BoseGases.X n → ℝ) hcont
  have hkin : 0 ≤ Work.BoseFixB1B.sbKinCube v μ u (Φ : Submission.BoseGases.X n → ℝ) :=
    Work.BoseFixB1C.sbKinCube_nonneg hadmr u (Φ : Submission.BoseGases.X n → ℝ)
  rw [Work.BoseFixB1C.sbWordCube_eq_add u (Φ : Submission.BoseGases.X n → ℝ), hsplit]
  have h1 : -(μ * (bandK v h (paramsAt μ (a v)).M *
        bandS (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d μ ^ 2))
      * Work.BoseFixB1.boxCountAt (sideAt μ (a v)) (paramsAt μ (a v)).d u
        (Φ : Submission.BoseGases.X n → ℝ)
      ≤ -(μ * fibSum h (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u
          (Φ : Submission.BoseGases.X n → ℝ)) := by
    nlinarith [mul_le_mul_of_nonneg_left hfib hμ.le]
  linarith [h1, hpair, hkin]

/-- **The box count is at most `n·‖Φ‖²`** — the box indicator sees at most one particle per slot. -/
theorem boxCountAt_le_card_mul_normB {v : E3 → ℝ} {μ ε₀ : ℝ}
    (hAdm : Work.BoseBoxFix.Adm v ε₀ μ) {n : ℕ}
    (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))) (u : E3) :
    Work.BoseFixB1.boxCountAt (sideAt μ (a v)) (paramsAt μ (a v)).d u
        (Φ : Submission.BoseGases.X n → ℝ)
      ≤ (n : ℝ) * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) := by
  have hℓ : 0 < sideAt μ (a v) := Work.BoseFixB1.adm_ell_pos hAdm
  have hcont : Continuous (Φ : Submission.BoseGases.X n → ℝ) := Φ.contDiff.continuous
  have hmeasB : MeasurableSet (Submission.BoseGases.dlBox (sideAt μ (a v))
      (paramsAt μ (a v)).d u) := Work.SmallBoxSliding.measurableSet_dlBox _ _ u
  have hBac : Submission.BoseGases.dlBox (sideAt μ (a v)) (paramsAt μ (a v)).d u ⊆
      Submission.BoseGases.acube (sideAt μ (a v)) := Set.inter_subset_left
  rw [Work.BoseFixB1.boxCountAt, Work.BoseFixB1.normB_eq_integral]
  calc ∑ i : Fin n, ∫ x in Submission.BoseGases.abox n (sideAt μ (a v)),
        (Φ x) ^ 2 * (Submission.BoseGases.dlBox (sideAt μ (a v))
          (paramsAt μ (a v)).d u).indicator (fun _ => (1 : ℝ)) (x i)
      ≤ ∑ _i : Fin n, ∫ x in Submission.BoseGases.abox n (sideAt μ (a v)), (Φ x) ^ 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        refine MeasureTheory.setIntegral_mono_on ?_ ?_
          (Submission.BoseGases.abox_measurable n (sideAt μ (a v))) ?_
        · simpa only [one_mul] using Work.BoseFixB1S.integrableOn_phi_sq_indicator (c := 1)
            hℓ hmeasB hBac i hcont
        · exact ContinuousOn.integrableOn_compact (Submission.BoseGases.abox_compact n hℓ)
            ((hcont.pow 2).continuousOn)
        · intro x _
          by_cases hx : x i ∈ Submission.BoseGases.dlBox (sideAt μ (a v))
              (paramsAt μ (a v)).d u
          · rw [Set.indicator_of_mem hx, mul_one]
          · rw [Set.indicator_of_notMem hx, mul_zero]
            exact sq_nonneg _
    _ = (n : ℝ) * ∫ x in Submission.BoseGases.abox n (sideAt μ (a v)), (Φ x) ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **The low-state count window** `(CW)`, in the exact shape produced by
`Work.BoseFixB1S.countWindowUnif_of_aprioriUnif` (and `..._of_collectedUnifCube`): a single
`(ε₀, C)` serves every threshold `J ≤ K_B³`. -/
def CountWindow (v : E3 → ℝ) (h : ScatSol v) : Prop :=
  ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧
    ∀ (J : ℝ) (μ : ℝ), Work.BoseBoxFix.Adm v ε₀ μ → J ≤ (paramsAt μ (a v)).KB ^ 3 →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))),
        0 < Work.BoseBoxFix.normB v μ n (Φ : X n → ℝ) →
        Work.BoseBoxFix.IsLowB v h J μ n Φ →
        (n : ℝ) ≤ C * μ * (sideAt μ (a v)) ^ 3

/-- **The target from the count window.**  On the band the (PROVED) fibre bound gives
`sbWordCube ≥ −μ·bandK·bandS²·⟨count⟩`; `⟨count⟩ ≤ n‖Φ‖²`, `n ≤ Cμℓ³`, the band arithmetic
`ℓ³·bandK·bandS² ≤ K(a v)` and the diluteness `μ(a v)³ ≤ 1` convert that into the allowance
`C'(μ²(a v)χ_M(u) + μ(a v))‖Φ‖²` with `C' = C·K/(a v)³ + 1`. -/
theorem cubeCrudeBand_of_countWindow {v : E3 → ℝ} {h : Work.UBB.ScatSol v} (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) (hav : 0 < _root_.BoseGases.a v)
    (hwin : CountWindow v h) : CubeCrudeBand v h := by
  obtain ⟨εw, C, hεw, hC, hw⟩ := hwin
  obtain ⟨εr, hεr, hregh⟩ := Work.BoseFixB1.regime_sideAt_ge (v := v) hav hR
  obtain ⟨εa, Ka, hεa, hKa, harith⟩ :=
    Work.BoseFixB1S.BandSizeArithB1 (v := v) h hv hv1 hvrad hR hv_supp hav
  refine ⟨min (min (min εw εa) εr) 1, C * Ka / (_root_.BoseGases.a v) ^ 3 + 1,
    lt_min (lt_min (lt_min hεw hεa) hεr) one_pos, by positivity, ?_⟩
  intro J μ hAdm hJK n Φ hlow u hcube hgood
  have hμ : 0 < μ := Work.BoseFixB1.adm_mu_pos hAdm
  have ha : 0 < _root_.BoseGases.a v := Work.BoseFixB1.adm_a_pos hAdm
  have hℓ : 0 < sideAt μ (a v) := Work.BoseFixB1.adm_ell_pos hAdm
  have hAdmw : Work.BoseBoxFix.Adm v εw μ :=
    Work.BoseFixB1.Adm.mono hAdm
      (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_left _ _)))
  have hAdma : Work.BoseBoxFix.Adm v εa μ :=
    Work.BoseFixB1.Adm.mono hAdm
      (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _)))
  have hAdmr : Work.BoseBoxFix.Adm v εr μ :=
    Work.BoseFixB1.Adm.mono hAdm (le_trans (min_le_left _ _) (min_le_right _ _))
  have hdilute : μ * (_root_.BoseGases.a v) ^ 3 ≤ 1 :=
    le_trans (Work.BoseFixB1.adm_dilute hAdm) (min_le_right _ _)
  obtain ⟨hRd, hRχ⟩ := hregh μ hμ (Work.BoseFixB1.adm_dilute hAdmr)
  have huBand : u ∈ Work.SmallBoxSliding.bandSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ :=
    Work.BoseFixB1B.goodSet_compl_inter_cube_subset_bandSet (ℓ := sideAt μ (a v))
      (d := (paramsAt μ (a v)).d) (μ := μ) hμ ⟨hgood, hcube⟩
  have hband := sbWordCube_ge_neg_bandCount (v := v) (h := h) hv hv1 hvrad hR hv_supp
    (εr := εr) hAdmr Φ huBand hRd hRχ
  have hχ0 : 0 ≤ Work.SmallBoxSliding.chiMass (paramsAt μ (a v)).M (sideAt μ (a v))
      (paramsAt μ (a v)).d u := Work.SmallBoxSliding.chiMass_nonneg _ _ _ _
  have hN0 : 0 ≤ Work.BoseBoxFix.normB v μ n (Φ : X n → ℝ) := Work.BoseFixB1.normB_nonneg _
  have hBK : 0 ≤ bandK v h (paramsAt μ (a v)).M *
      bandS (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d μ ^ 2 :=
    mul_nonneg (bandK_nonneg _) (sq_nonneg _)
  have hCc : 0 ≤ C * Ka / (_root_.BoseGases.a v) ^ 3 + 1 := by positivity
  have harith' : (sideAt μ (a v)) ^ 3 * (bandK v h (paramsAt μ (a v)).M *
      bandS (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d μ ^ 2)
      ≤ Ka * (_root_.BoseGases.a v) := by
    simpa only [mul_assoc] using harith μ hAdma
  -- the key arithmetic: `C·μ²·Ka·a ≤ Cc·(μ²·a·χ + μ·a)`, from `μ·a³ ≤ 1`
  have hkey : C * μ ^ 2 * (Ka * (_root_.BoseGases.a v))
      ≤ (C * Ka / (_root_.BoseGases.a v) ^ 3 + 1)
        * (μ ^ 2 * (_root_.BoseGases.a v)
            * Work.SmallBoxSliding.chiMass (paramsAt μ (a v)).M (sideAt μ (a v))
                (paramsAt μ (a v)).d u
          + μ * (_root_.BoseGases.a v)) := by
    have h1 : C * μ ^ 2 * (Ka * (_root_.BoseGases.a v))
        = (C * Ka / (_root_.BoseGases.a v) ^ 3) * (μ * (_root_.BoseGases.a v))
            * (μ * (_root_.BoseGases.a v) ^ 3) := by
      field_simp
    have h2 : (C * Ka / (_root_.BoseGases.a v) ^ 3) * (μ * (_root_.BoseGases.a v))
          * (μ * (_root_.BoseGases.a v) ^ 3)
        ≤ (C * Ka / (_root_.BoseGases.a v) ^ 3) * (μ * (_root_.BoseGases.a v)) * 1 :=
      mul_le_mul_of_nonneg_left hdilute (by positivity)
    have h3 : (C * Ka / (_root_.BoseGases.a v) ^ 3) * (μ * (_root_.BoseGases.a v)) * 1
        ≤ (C * Ka / (_root_.BoseGases.a v) ^ 3 + 1) * (μ * (_root_.BoseGases.a v)) := by
      nlinarith [mul_nonneg hμ.le ha.le]
    have h4 : (C * Ka / (_root_.BoseGases.a v) ^ 3 + 1) * (μ * (_root_.BoseGases.a v))
        ≤ (C * Ka / (_root_.BoseGases.a v) ^ 3 + 1)
          * (μ ^ 2 * (_root_.BoseGases.a v)
              * Work.SmallBoxSliding.chiMass (paramsAt μ (a v)).M (sideAt μ (a v))
                  (paramsAt μ (a v)).d u
            + μ * (_root_.BoseGases.a v)) := by
      refine mul_le_mul_of_nonneg_left ?_ hCc
      nlinarith [mul_nonneg (mul_nonneg (sq_nonneg μ) ha.le) hχ0]
    linarith [h1.le, h1.ge, h2, h3, h4]
  rcases eq_or_ne (Work.BoseBoxFix.normB v μ n (Φ : X n → ℝ)) 0 with hNzero | hNne
  · -- vanishing norm: everything collapses
    have hb0 : Work.BoseFixB1.boxCountAt (sideAt μ (a v)) (paramsAt μ (a v)).d u
        (Φ : X n → ℝ) ≤ 0 := by
      have hbox := boxCountAt_le_card_mul_normB (v := v) hAdm Φ u
      rw [hNzero, mul_zero] at hbox
      exact hbox
    have hw0 : 0 ≤ Work.BoseFixB1B.sbWordCube v h μ u (Φ : X n → ℝ) := by
      have h2 : -(μ * (bandK v h (paramsAt μ (a v)).M *
            bandS (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d μ ^ 2))
          * Work.BoseFixB1.boxCountAt (sideAt μ (a v)) (paramsAt μ (a v)).d u
              (Φ : X n → ℝ) = 0 := by
        rw [le_antisymm hb0 (Work.BoseFixB1.boxCountAt_nonneg _), mul_zero]
      linarith [hband, h2]
    rw [hNzero, mul_zero]
    exact hw0
  · have hNpos : 0 < Work.BoseBoxFix.normB v μ n (Φ : X n → ℝ) :=
      lt_of_le_of_ne hN0 (Ne.symm hNne)
    have hn := hw J μ hAdmw hJK n Φ hNpos hlow
    have hbox := boxCountAt_le_card_mul_normB (v := v) hAdm Φ u
    have hcount : Work.BoseFixB1.boxCountAt (sideAt μ (a v)) (paramsAt μ (a v)).d u
        (Φ : X n → ℝ)
        ≤ C * μ * (sideAt μ (a v)) ^ 3 * Work.BoseBoxFix.normB v μ n (Φ : X n → ℝ) := by
      calc Work.BoseFixB1.boxCountAt (sideAt μ (a v)) (paramsAt μ (a v)).d u (Φ : X n → ℝ)
          ≤ (n : ℝ) * Work.BoseBoxFix.normB v μ n (Φ : X n → ℝ) := hbox
        _ ≤ (C * μ * (sideAt μ (a v)) ^ 3) * Work.BoseBoxFix.normB v μ n (Φ : X n → ℝ) :=
            mul_le_mul_of_nonneg_right hn hN0
        _ = C * μ * (sideAt μ (a v)) ^ 3 * Work.BoseBoxFix.normB v μ n (Φ : X n → ℝ) := by ring
    have hstep : μ * (bandK v h (paramsAt μ (a v)).M *
          bandS (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d μ ^ 2)
        * Work.BoseFixB1.boxCountAt (sideAt μ (a v)) (paramsAt μ (a v)).d u
            (Φ : X n → ℝ)
        ≤ C * μ ^ 2 * (Ka * (_root_.BoseGases.a v)) * Work.BoseBoxFix.normB v μ n (Φ : X n → ℝ) := by
      calc μ * (bandK v h (paramsAt μ (a v)).M *
            bandS (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d μ ^ 2)
          * Work.BoseFixB1.boxCountAt (sideAt μ (a v)) (paramsAt μ (a v)).d u (Φ : X n → ℝ)
          ≤ μ * (bandK v h (paramsAt μ (a v)).M *
              bandS (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d μ ^ 2)
            * (C * μ * (sideAt μ (a v)) ^ 3 * Work.BoseBoxFix.normB v μ n (Φ : X n → ℝ)) :=
            mul_le_mul_of_nonneg_left hcount (mul_nonneg hμ.le hBK)
        _ = C * μ ^ 2 * ((sideAt μ (a v)) ^ 3 * (bandK v h (paramsAt μ (a v)).M *
              bandS (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d μ ^ 2))
              * Work.BoseBoxFix.normB v μ n (Φ : X n → ℝ) := by ring
        _ ≤ C * μ ^ 2 * (Ka * (_root_.BoseGases.a v)) * Work.BoseBoxFix.normB v μ n (Φ : X n → ℝ) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left harith' (by positivity)) hN0
    have hchain : -(((C * Ka / (_root_.BoseGases.a v) ^ 3 + 1)
          * (μ ^ 2 * (_root_.BoseGases.a v)
              * Work.SmallBoxSliding.chiMass (paramsAt μ (a v)).M (sideAt μ (a v))
                  (paramsAt μ (a v)).d u
            + μ * (_root_.BoseGases.a v)))
          * Work.BoseBoxFix.normB v μ n (Φ : X n → ℝ))
        ≤ Work.BoseFixB1B.sbWordCube v h μ u (Φ : X n → ℝ) :=
      le_trans (le_trans (neg_le_neg (mul_le_mul_of_nonneg_right hkey hN0)) (neg_le_neg hstep))
        (by
          have h := hband
          rwa [neg_mul] at h)
    rw [neg_mul]
    exact hchain

end Work.BoseB1Cube
