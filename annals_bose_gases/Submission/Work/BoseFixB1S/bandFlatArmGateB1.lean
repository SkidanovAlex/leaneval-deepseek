import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1.BandSdefs
import Submission.Work.BoseFixB1.perBoxF_thick
import Submission.Work.BoseFixB1B.flatArmBandDefs
import Submission.Work.BoseFixB1S.fibSum_le_localSup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1S.bandFlatArmGateB1` — the sharp fibre payer and the kinetic gate

Node: `Work.BoseFixB1S.BandFlatArmB1` (= `Work.BoseFixB1B.FlatArmBand v h`).  This module records
two **proved** facts every route to that target must use, and one **proved reduction**.

## 1. The sharp fibre bound against the `χ`-weighted count

On the band, `fibSum ≤ bandK · bandS · occChi` (`fibSum_le_bandS_mul_occChi`) — **one** factor of
`bandS` instead of the corpus's two (`fibSum_le_band_boxCount` uses the unweighted `boxCountAt`).
It is `Work.BoseFixB1S.fibSum_le_localSup` at the constant local sup `S ≡ bandS`, which is
legitimate on the band by the PROVED `chiSmallB_le_bandS`.  This is the payer shape the
flat/condensed branch needs, because `occChi` is exactly the count that both the target's
occupancy hypothesis and the corpus ledger control.

## 2. The kinetic gate

`sbWord = sbKin + pairSum − μ·fibSum` (`sbWord_eq_kin_add_pair_sub_fib`, from the PROVED
`sbPot_split`), `sbKin ≥ 0` (PROVED `sbKin_nonneg`) and `pairSum ≥ 0` (PROVED `pairSum_nonneg`).
Hence **on the branch `μ·fibSum ≤ sbKin` the word is nonnegative**, so the target holds there with
the same `C` for free:

    `sbWord_nonneg_of_fib_le_kin`.

`flatArmBand_of_deficit` turns this into a proved reduction: `FlatArmBand` follows from its own
restriction `FlatArmBandDeficit` to the states where the *kinetic* word does **not** already cover
the chemical line.  So every unresolved state of the target carries `sbKin < μ·fibSum`, i.e.
bounded kinetic energy.

## What is *not* here

The deficit branch is not discharged.  Its content is the quantitative "kinetic cost of
pair-deadness": a state whose pair energy is far below the rigid value
`(M₂/V²)·boxPairCount` must pay in the kinetic word.  The pair half needs a two-slot estimate
(the wall of `FINDING_armCondensedFlatHalf.md` §3 / `FINDING_bandCountHoleArm_S3.md` §13: the
cross term `Σ_p∫(P_pΦ)R_pw` genuinely depends on the second slot, and the cusp family of §13
shows that an `H¹`-only bound cannot control it), and the kinetic half is FS's
`lm:appinteractionestimate`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1S

open _root_.BoseGases Submission.BoseGases Work.BoseBox Work.BoseBoxFix Work.UBB
open Work.SmallBoxSliding

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-! ## 1. `bandG = 8π·(a v)` -/

/-- `bandG v h = ∫|g₀| = 8π·(a v)` (`g₀ ≥ 0` a.e. and `∫g₀ = 8πa`). -/
theorem bandG_eq_eight_pi_a {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {R : ℝ} (hR : 0 < R)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) :
    Work.BoseFixB1.bandG v h = 8 * Real.pi * _root_.BoseGases.a v := by
  rw [Work.BoseFixB1.bandG]
  have habs : (∫ z : E3, |Submission.BoseGases.g0 v h z|)
      = ∫ z : E3, Submission.BoseGases.g0 v h z := by
    refine integral_congr_ae ?_
    filter_upwards [Submission.BoseGases.g0_nonneg_ae (v := v) (R := R) hR hv hvrad hv_supp h]
      with z hz
    exact abs_of_nonneg hz
  rw [habs, Submission.BoseGases.g0_integral hR hv_supp h]

/-- The corpus's band fibre constant is `16π·(a v)/smallConvLower M`. -/
theorem bandK_eq {v : E3 → ℝ} {h : Work.UBB.ScatSol v} (M : ℕ) {R : ℝ} (hR : 0 < R)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) :
    Work.BoseFixB1.bandK v h M
      = 16 * Real.pi * _root_.BoseGases.a v / Work.SmallBoxSliding.smallConvLower M := by
  rw [Work.BoseFixB1.bandK, bandG_eq_eight_pi_a (h := h) hR hv hvrad hv_supp]
  ring

/-! ## 2. The sharp fibre bound against `occChi` -/

/-- **The sharp band fibre bound in `occChi` form.** -/
theorem fibSum_le_bandS_mul_occChi {v : E3 → ℝ} (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) {M : ℕ} (hM : 1 ≤ M) {ℓ d μ : ℝ}
    (hℓ : 0 < ℓ) (hd : 0 < d) (hμ : 0 < μ) (hR16 : R ≤ ℓ * d / 16)
    (hRχ : R ≤ ℓ * Submission.BoseGases.chiR0) {u : E3} (hu : u ∈ bandSet ℓ d μ) {n : ℕ}
    (Φ : Submission.BoseGases.X n → ℝ) (hΦc : Continuous Φ) :
    Work.BoseFixB1.fibSum h M ℓ d u Φ
      ≤ Work.BoseFixB1.bandK v h M * Work.BoseFixB1.bandS M ℓ d μ
          * Work.BoseFixR.occChi M ℓ d u Φ := by
  have hmain := Work.BoseFixB1S.fibSum_le_localSup (v := v) h hv hvrad hR hv_supp hM hℓ hd
    hR16 hRχ u Φ hΦc
    (S := fun _ : E3 => Work.BoseFixB1.bandS M ℓ d μ) measurable_const
    (B := Work.BoseFixB1.bandS M ℓ d μ) (Work.BoseFixB1.bandS_nonneg M ℓ d μ)
    (fun x y _ => Work.BoseFixB1.chiSmallB_le_bandS hM hℓ hd hμ hu y)
    (fun _ => le_rfl)
  have hc : 16 * Real.pi * _root_.BoseGases.a v / Work.SmallBoxSliding.smallConvLower M
      = Work.BoseFixB1.bandK v h M := (bandK_eq (h := h) M hR hv hvrad hv_supp).symm
  rw [hc] at hmain
  have hrw : (∫ x in Submission.BoseGases.abox n ℓ,
      (Φ x) ^ 2 * ∑ i : Fin n,
        Submission.BoseGases.chiSmallB M ℓ d u (x i) * Work.BoseFixB1.bandS M ℓ d μ)
      = Work.BoseFixB1.bandS M ℓ d μ * Work.BoseFixR.occChi M ℓ d u Φ := by
    rw [Work.BoseFixR.occChi]
    rw [show (fun x : Submission.BoseGases.X n => (Φ x) ^ 2 * ∑ i : Fin n,
        Submission.BoseGases.chiSmallB M ℓ d u (x i) * Work.BoseFixB1.bandS M ℓ d μ)
      = fun x => Work.BoseFixB1.bandS M ℓ d μ *
          ((Φ x) ^ 2 * ∑ i : Fin n, Submission.BoseGases.chiSmallB M ℓ d u (x i)) by
        funext x
        rw [← Finset.sum_mul]
        ring]
    rw [MeasureTheory.integral_const_mul]
  rw [hrw] at hmain
  simpa only [mul_assoc] using hmain

/-! ## 2bis. The sharpest form: against the actual sup of `χ_B` -/

/-- The actual sup of the box cutoff, as a concrete term.  It is dominated by the band constant
`bandS` on the band (`chiSmallB_le_bandS`), but it can be *much* smaller (the band constant is
evaluated at the outermost point of the band, `A − |w_j| = 2μ^{-1/3}`). -/
noncomputable def chiSup (M : ℕ) (ℓ d : ℝ) (u : E3) : ℝ :=
  sSup (Set.range (Submission.BoseGases.chiSmallB M ℓ d u))

/-- `χ_B x ≤ chiSup` (the range is bounded above by the PROVED `abs_chiSmallB_le`). -/
theorem chiSmallB_le_chiSup {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ}
    (u x : E3) : Submission.BoseGases.chiSmallB M ℓ d u x ≤ chiSup M ℓ d u := by
  refine le_csSup ⟨Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M, ?_⟩
    ⟨x, rfl⟩
  rintro _ ⟨y, rfl⟩
  exact Work.BoseFixB1.chiSmallB_le_Cs (M := M) hM u y

/-- `0 ≤ chiSup`. -/
theorem chiSup_nonneg {M : ℕ} (hM : 1 ≤ M) (ℓ d : ℝ) (u : E3) : 0 ≤ chiSup M ℓ d u :=
  (Submission.BoseGases.chiSmallB_nonneg M ℓ d u u).trans (chiSmallB_le_chiSup (M := M) hM u u)

/-- **The sharpest fibre bound**: against the *actual* sup of `χ_B`,
`fibSum ≤ bandK·chiSup·occChi` — the band constant is not used, so the bound stays sharp for thin
slabs (`u` with `A − |w_j| ≪ 2μ^{-1/3}`), where `bandS` is a very poor proxy for `sup χ_B`. -/
theorem fibSum_le_chiSup_mul_occChi {v : E3 → ℝ} (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ}
    (hℓ : 0 < ℓ) (hd : 0 < d) (hR16 : R ≤ ℓ * d / 16)
    (hRχ : R ≤ ℓ * Submission.BoseGases.chiR0) (u : E3) {n : ℕ}
    (Φ : Submission.BoseGases.X n → ℝ) (hΦc : Continuous Φ) :
    Work.BoseFixB1.fibSum h M ℓ d u Φ
      ≤ Work.BoseFixB1.bandK v h M * chiSup M ℓ d u * Work.BoseFixR.occChi M ℓ d u Φ := by
  have hmain := Work.BoseFixB1S.fibSum_le_localSup (v := v) h hv hvrad hR hv_supp hM hℓ hd
    hR16 hRχ u Φ hΦc
    (S := fun _ : E3 => chiSup M ℓ d u) measurable_const
    (B := chiSup M ℓ d u) (chiSup_nonneg hM ℓ d u)
    (fun x y _ => chiSmallB_le_chiSup (M := M) hM u y)
    (fun _ => le_rfl)
  have hc : 16 * Real.pi * _root_.BoseGases.a v / Work.SmallBoxSliding.smallConvLower M
      = Work.BoseFixB1.bandK v h M := (bandK_eq (h := h) M hR hv hvrad hv_supp).symm
  rw [hc] at hmain
  have hrw : (∫ x in Submission.BoseGases.abox n ℓ,
      (Φ x) ^ 2 * ∑ i : Fin n,
        Submission.BoseGases.chiSmallB M ℓ d u (x i) * chiSup M ℓ d u)
      = chiSup M ℓ d u * Work.BoseFixR.occChi M ℓ d u Φ := by
    rw [Work.BoseFixR.occChi]
    rw [show (fun x : Submission.BoseGases.X n => (Φ x) ^ 2 * ∑ i : Fin n,
        Submission.BoseGases.chiSmallB M ℓ d u (x i) * chiSup M ℓ d u)
      = fun x => chiSup M ℓ d u *
          ((Φ x) ^ 2 * ∑ i : Fin n, Submission.BoseGases.chiSmallB M ℓ d u (x i)) by
        funext x
        rw [← Finset.sum_mul]
        ring]
    rw [MeasureTheory.integral_const_mul]
  rw [hrw] at hmain
  simpa only [mul_assoc] using hmain

/-! ## 3. The word split and the kinetic gate -/

/-- `sbKin ≥ 0` at an admissible point (inlined from the broken neighbour
`BandPerBoxCrudeB1.sbKin_nonneg`). -/
theorem sbKin_nonneg_gate {v : E3 → ℝ} {ε₀ μ : ℝ}
    (hadm : Work.BoseBoxFix.Adm v ε₀ μ) {n : ℕ} (u : E3)
    (Φ : Submission.BoseGases.X n → ℝ) :
    0 ≤ Work.BoseFixB1.sbKin (v := v) μ (paramsAt μ (_root_.BoseGases.a v)).M u Φ := by
  show 0 ≤ Work.UBBInputs8.tBwordBInd n (sideAt μ (_root_.BoseGases.a v))
      (paramsAt μ (_root_.BoseGases.a v)).d
      (paramsAt μ (_root_.BoseGases.a v)).eT
      (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) u Φ
  exact Work.UBBInputs9.A.tBwordBInd_nonneg (Work.BoseFixB1.adm_ell_pos hadm)
    (Work.BoseFixB1.adm_eT_bounds hadm).1 u Φ

/-- **The word split**: `sbWord = sbKin + pairSum − μ·fibSum` (from the PROVED `sbPot_split`). -/
theorem sbWord_eq_kin_add_pair_sub_fib {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {R : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) (hR : 0 < R) (hv : 0 ≤ v)
    (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    {ε₀ μ : ℝ} (hAdm : Work.BoseBoxFix.Adm v ε₀ μ) {n : ℕ}
    {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ) (u : E3)
    (hR16 : R ≤ sideAt μ (_root_.BoseGases.a v)
      * (paramsAt μ (_root_.BoseGases.a v)).d / 16)
    (hRχ : R ≤ sideAt μ (_root_.BoseGases.a v) * Submission.BoseGases.chiR0) :
    Work.BoseFixB1.sbWord h μ u Φ
      = Work.BoseFixB1.sbKin (v := v) μ (paramsAt μ (_root_.BoseGases.a v)).M u Φ
        + Work.BoseFixB1.pairSum v (paramsAt μ (_root_.BoseGases.a v)).M
            (sideAt μ (_root_.BoseGases.a v)) (paramsAt μ (_root_.BoseGases.a v)).d u Φ
        - μ * Work.BoseFixB1.fibSum h (paramsAt μ (_root_.BoseGases.a v)).M
            (sideAt μ (_root_.BoseGases.a v)) (paramsAt μ (_root_.BoseGases.a v)).d u Φ := by
  rw [Work.BoseFixB1.sbWord,
    Work.BoseFixB1.sbPot_split (v := v) (h := h) (R := R) hv_supp hR hv hvrad hv1 hAdm hΦc u
      hR16 hRχ]
  ring

/-- **The kinetic gate**: if the kinetic word already covers the chemical line, the word is
nonnegative. -/
theorem sbWord_nonneg_of_fib_le_kin {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {R : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) (hR : 0 < R) (hv : 0 ≤ v)
    (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    {ε₀ μ : ℝ} (hAdm : Work.BoseBoxFix.Adm v ε₀ μ) {n : ℕ}
    {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ) (u : E3)
    (hR16 : R ≤ sideAt μ (_root_.BoseGases.a v)
      * (paramsAt μ (_root_.BoseGases.a v)).d / 16)
    (hRχ : R ≤ sideAt μ (_root_.BoseGases.a v) * Submission.BoseGases.chiR0)
    (hgate : μ * Work.BoseFixB1.fibSum h (paramsAt μ (_root_.BoseGases.a v)).M
        (sideAt μ (_root_.BoseGases.a v)) (paramsAt μ (_root_.BoseGases.a v)).d u Φ
      ≤ Work.BoseFixB1.sbKin (v := v) μ (paramsAt μ (_root_.BoseGases.a v)).M u Φ) :
    0 ≤ Work.BoseFixB1.sbWord h μ u Φ := by
  have hsplit := sbWord_eq_kin_add_pair_sub_fib (h := h) hv_supp hR hv hvrad hv1 hAdm hΦc u
    hR16 hRχ
  have hps : 0 ≤ Work.BoseFixB1.pairSum v (paramsAt μ (_root_.BoseGases.a v)).M
      (sideAt μ (_root_.BoseGases.a v)) (paramsAt μ (_root_.BoseGases.a v)).d u Φ :=
    Work.BoseFixB1.pairSum_nonneg hv u Φ
  linarith [hsplit, hps, hgate]

/-! ## 4. The reduction of the target to its deficit branch -/

/-- **The deficit branch of the flat band arm**: the target's own statement restricted to the
states where the kinetic word does not already cover the chemical line. -/
def FlatArmBandDeficit (v : E3 → ℝ) (h : Work.UBB.ScatSol v) : Prop :=
  ∃ ε₀ K C : ℝ, 0 < ε₀ ∧ 0 < K ∧ 0 ≤ C ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (_root_.BoseGases.a v)))
        (u : E3),
        u ∈ bandSet (sideAt μ (_root_.BoseGases.a v)) (paramsAt μ (_root_.BoseGases.a v)).d
              (4 * μ) →
        Work.BoseFixR.crudeThreshold v K μ (paramsAt μ (_root_.BoseGases.a v)).M
            (sideAt μ (_root_.BoseGases.a v)) (paramsAt μ (_root_.BoseGases.a v)).d u
            (Φ : Submission.BoseGases.X n → ℝ)
          ≤ Work.BoseFixR.occChi (paramsAt μ (_root_.BoseGases.a v)).M
              (sideAt μ (_root_.BoseGases.a v)) (paramsAt μ (_root_.BoseGases.a v)).d u
              (Φ : Submission.BoseGases.X n → ℝ) →
        2 * Work.BoseFixB1S.boxQCount
              (boxMass (sideAt μ (_root_.BoseGases.a v)) (paramsAt μ (_root_.BoseGases.a v)).d u)
              (sideAt μ (_root_.BoseGases.a v))
              (Submission.BoseGases.dlBox (sideAt μ (_root_.BoseGases.a v))
                (paramsAt μ (_root_.BoseGases.a v)).d u)
              (Φ : Submission.BoseGases.X n → ℝ)
          ≤ Work.BoseFixB1S.boxFlatCount
              (boxMass (sideAt μ (_root_.BoseGases.a v)) (paramsAt μ (_root_.BoseGases.a v)).d u)
              (sideAt μ (_root_.BoseGases.a v))
              (Submission.BoseGases.dlBox (sideAt μ (_root_.BoseGases.a v))
                (paramsAt μ (_root_.BoseGases.a v)).d u)
              (Φ : Submission.BoseGases.X n → ℝ) →
        ¬ (μ * Work.BoseFixB1.fibSum h (paramsAt μ (_root_.BoseGases.a v)).M
              (sideAt μ (_root_.BoseGases.a v)) (paramsAt μ (_root_.BoseGases.a v)).d u
              (Φ : Submission.BoseGases.X n → ℝ)
            ≤ Work.BoseFixB1.sbKin (v := v) μ (paramsAt μ (_root_.BoseGases.a v)).M u
              (Φ : Submission.BoseGases.X n → ℝ)) →
        -(C * (μ ^ 2 * _root_.BoseGases.a v
              * Work.SmallBoxSliding.chiMass (paramsAt μ (_root_.BoseGases.a v)).M
                  (sideAt μ (_root_.BoseGases.a v)) (paramsAt μ (_root_.BoseGases.a v)).d u
            + μ * _root_.BoseGases.a v))
          * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
        ≤ Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ)

/-- **The reduction**: `FlatArmBand` follows from its restriction to the deficit branch.  On the
complementary branch the gate gives `sbWord ≥ 0`, and the target's right-hand side is `≤ 0`
because `0 ≤ C`, `0 ≤ μ`, `0 ≤ (a v)`, `0 ≤ chiMass`, `0 ≤ normB`.

The regime hypotheses `R ≤ ℓd/16`, `R ≤ ℓ·chiR0` are extracted from `Adm` by the PROVED
`Work.BoseFixB1.regime_sideAt_ge` (they are needed only on the gated branch). -/
theorem flatArmBand_of_deficit {v : E3 → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hav : 0 < _root_.BoseGases.a v) (hdef : FlatArmBandDeficit v h) :
    Work.BoseFixB1B.FlatArmBand v h := by
  classical
  obtain ⟨εd, K, C, hεd, hK, hC, harm⟩ := hdef
  obtain ⟨εg, hεg, hreg⟩ := Work.BoseFixB1.regime_sideAt_ge (v := v) hav hR
  refine ⟨min εd εg, K, C, lt_min hεd hεg, hK, hC, ?_⟩
  intro μ hAdm n Φ u huBand hocc hflat
  have hAdmd : Work.BoseBoxFix.Adm v εd μ := Work.BoseFixB1.Adm.mono hAdm (min_le_left _ _)
  have hAdmg : Work.BoseBoxFix.Adm v εg μ := Work.BoseFixB1.Adm.mono hAdm (min_le_right _ _)
  obtain ⟨hR16, hRχ⟩ := hreg μ hAdmg.1 (le_trans hAdm.2.1 (min_le_right _ _))
  have hΦc : Continuous (Φ : Submission.BoseGases.X n → ℝ) := Φ.contDiff.continuous
  by_cases hcrit : μ * Work.BoseFixB1.fibSum h (paramsAt μ (_root_.BoseGases.a v)).M
      (sideAt μ (_root_.BoseGases.a v)) (paramsAt μ (_root_.BoseGases.a v)).d u
      (Φ : Submission.BoseGases.X n → ℝ)
      ≤ Work.BoseFixB1.sbKin (v := v) μ (paramsAt μ (_root_.BoseGases.a v)).M u
        (Φ : Submission.BoseGases.X n → ℝ)
  · -- the gate: the word is nonnegative, and the target's right-hand side is nonpositive
    have hnn := sbWord_nonneg_of_fib_le_kin (h := h) hv_supp hR hv hvrad hv1 hAdmd hΦc u hR16
      hRχ hcrit
    have hI0 : 0 ≤ Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) :=
      Work.BoseFixB1.normB_nonneg _
    have hpre : 0 ≤ C * (μ ^ 2 * _root_.BoseGases.a v
        * Work.SmallBoxSliding.chiMass (paramsAt μ (_root_.BoseGases.a v)).M
            (sideAt μ (_root_.BoseGases.a v)) (paramsAt μ (_root_.BoseGases.a v)).d u
      + μ * _root_.BoseGases.a v) := by
      refine mul_nonneg hC (add_nonneg (mul_nonneg (mul_nonneg (sq_nonneg μ) hav.le) ?_) ?_)
      · rw [Work.SmallBoxSliding.chiMass_def]
        exact integral_nonneg fun x => sq_nonneg _
      · exact mul_nonneg hAdmd.1.le hav.le
    have hneg : -(C * (μ ^ 2 * _root_.BoseGases.a v
          * Work.SmallBoxSliding.chiMass (paramsAt μ (_root_.BoseGases.a v)).M
              (sideAt μ (_root_.BoseGases.a v)) (paramsAt μ (_root_.BoseGases.a v)).d u
        + μ * _root_.BoseGases.a v))
        * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) ≤ 0 := by
      have hh : -(C * (μ ^ 2 * _root_.BoseGases.a v
            * Work.SmallBoxSliding.chiMass (paramsAt μ (_root_.BoseGases.a v)).M
                (sideAt μ (_root_.BoseGases.a v)) (paramsAt μ (_root_.BoseGases.a v)).d u
          + μ * _root_.BoseGases.a v))
          * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
          = -(C * (μ ^ 2 * _root_.BoseGases.a v
            * Work.SmallBoxSliding.chiMass (paramsAt μ (_root_.BoseGases.a v)).M
                (sideAt μ (_root_.BoseGases.a v)) (paramsAt μ (_root_.BoseGases.a v)).d u
          + μ * _root_.BoseGases.a v)
            * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)) := by ring
      rw [hh]
      exact neg_nonpos.mpr (mul_nonneg hpre hI0)
    linarith [hnn, hneg]
  · exact harm μ hAdmd n Φ u huBand hocc hflat hcrit

end Work.BoseFixB1S
