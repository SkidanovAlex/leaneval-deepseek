import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB1Cube.particleWindowMu
import Submission.Work.BoseSWE.countWindowOfPerBoxFNomSlotsE
import Submission.Work.BoseSWE.ledgerNomE
import Submission.Work.BoseSWE.perBoxFNomSlotsE_of_perBoxFNomMuE
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseSWE.F4d_Node` — the **endgame of the `E`-route**: `NodeB1B` from
# `PerBoxFNomMuE`

This module is the area owner's composition (BRIEF interface summary).  From the one-slot nominal
row with the vanishing slack,

    `PerBoxFNomMuE v h R`  =  FS `thm:smallbox` at the sliding box with `Dem ↦ Dem − CE·aμn·d^80`,

it produces the frozen §5 node `Work.BoseBoxFix.NodeB1B v h J`, reusing every PROVED consumer of
the nominal chain:

* `Work.BoseSWE.ledgerNomE` (the a-priori ledger with the slack) and
  `Work.BoseSWE.countWindowOfPerBoxFNomSlotsE` (the count window with the slack) give the **clean**
  rows `Work.BoseB1Cube.NomAprioriUnif` — the ledger's error slot (now `E'` instead of the
  prescribed `E = 1`) is absorbed by the count window exactly as in the twin `nomCleanRowsMu`;
* `Work.BoseB1Cube.nomWindowBridgeMu` (PROVED) turns the clean rows into the sharp particle window
  `ParticleWindowMu`;
* the excited window `NPlusWindowMu` is the twin of `nPlusWindowMu_of_perBoxFNomMu` (same
  absorption, with `CA + E'·CW` in place of `CA + 1·CW`);
* `Work.BoseB1Cube.nodeB1B_of_windows` (PROVED) assembles the two windows into `NodeB1B`.

Everything here is a copy-edit of `Submission/Work/BoseB1Cube/particleWindowMu.lean` and
`Submission/Work/BoseB1Cube/nodeB1B_of_perBoxFNomMu.lean`; the only new ingredient is the second
slot `E'` of `ledgerNomE`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseSWE

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB Work.BoseFixB1
  Work.SmallBoxSliding Work.BoseB1Cube

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "X" => Submission.BoseGases.X

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- The `Work.BoseB1Cube.PsiWeightFourIntegral` instance used by the slot doubling, from the
PROVED `Work.BoseB1Cube.psiWeight_integral_four_le`.  (Local, so that this module's cone avoids
`Work.BoseB1Cube.nominalPerBoxRow`, whose closure contains
`Work.BoseB1Cube.sq_integral_le_integral_sq` — a name that clashes with the one in
`Work.BoseB1Cube.devFTCDefs`, which the `massiveRegularNode_holds` cone carries.) -/
theorem psiWeightFourIntegral_holdsSWE : Work.BoseB1Cube.PsiWeightFourIntegral := by
  intro ℓ d μ u n Φ hℓ hd hμ hV hΦc
  exact Work.BoseB1Cube.psiWeight_integral_four_le hℓ hd hμ u Φ hV hΦc

/-! ## 1. The clean a-priori rows, with the slack absorbed by the count window -/

/-- **`NomAprioriUnif` from `PerBoxFNomMuE`.**  Twin of `Work.BoseB1Cube.nomCleanRowsMu`: the
ledger `ledgerNomE` gives the two a-priori rows at the nominal remainder with the error slot
`E'·μ(a v)κ·n‖Φ‖²`; the one-sided count window (`countWindowOfPerBoxFNomSlotsE`) is `n ≤ CW μℓ³`,
so that slot is `≤ (E'·CW)·(μ²(a v)ℓ³κ)·‖Φ‖²` and merges into `C_A`. -/
theorem nomCleanRowsMuE {v : E3 → ℝ} (h : ScatSol v) (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1)
    (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) (hav : 0 < a v)
    (hMu : PerBoxFNomMuE v h R) : NomAprioriUnif v h := by
  obtain ⟨εN, c₁, C, CE, hεN, hc₁, hC, hCE, hper⟩ := hMu
  have hperS : PerBoxFNomSlotsE v h R :=
    perBoxFNomSlotsE_of_perBoxFNomMuE h hv hvrad hR hv_supp psiWeightFourIntegral_holdsSWE
      ⟨εN, c₁, C, CE, hεN, hc₁, hC, hCE, hper⟩
  obtain ⟨εN', c₁', C', CE', hεN', hc₁', hC', hCE', hper'⟩ := hperS
  have hS : SlidingGoodCube v h := slidingGoodCube h hv hv1 hvrad hR hv_supp hav
  obtain ⟨εL, CA, E', hεL, hCA, hE', hled⟩ :=
    ledgerNomE (v := v) (h := h) (R := R) hv hv1 hvrad hR hv_supp hav
      (c₁ := c₁') (C := C') (E := 1) (CE := CE') hc₁' hC' one_pos hCE'
      ⟨εN', hεN', hper'⟩ hS
  obtain ⟨εW, CW, hεW, hCW, hwin⟩ :=
    countWindowOfPerBoxFNomSlotsE (v := v) h hv hv1 hvrad hR hv_supp hav hS
      (fun c₁ C E CE h1 h2 h3 h4 row hSg =>
        ledgerNomE (v := v) (h := h) (R := R) hv hv1 hvrad hR hv_supp hav h1 h2 h3 h4 row hSg)
      ⟨εN', c₁', C', CE', hεN', hc₁', hC', hCE', hper'⟩
  have hCAW0 : 0 ≤ CA + E' * CW :=
    add_nonneg hCA (mul_nonneg hE' hCW)
  set CA' : ℝ := max ((CA + E' * CW) / c₁') (CA + E' * CW) + 1 with hCA'def
  have hCA'pos : 0 < CA' := by
    rw [hCA'def]
    exact add_pos_of_nonneg_of_pos (le_trans hCAW0 (le_max_right _ _)) one_pos
  have hle1 : (CA + E' * CW) / c₁' ≤ CA' := by
    rw [hCA'def]
    exact le_trans (le_max_left _ _) (le_add_of_nonneg_right zero_le_one)
  have hle2 : CA + E' * CW ≤ CA' := by
    rw [hCA'def]
    exact le_trans (le_max_right _ _) (le_add_of_nonneg_right zero_le_one)
  refine ⟨CA', min εL εW, hCA'pos, lt_min hεL hεW, ?_⟩
  intro J μ hAdm hJK n Φ hN hlow
  have hμ : 0 < μ := Work.BoseFixB1.adm_mu_pos hAdm
  have hav0 : 0 ≤ a v := (Work.BoseFixB1.adm_a_pos hAdm).le
  have hℓ : 0 < sideAt μ (a v) := Work.BoseFixB1.adm_ell_pos hAdm
  have hAdmL : Adm v εL μ := Work.BoseFixB1.Adm.mono hAdm (min_le_left _ _)
  have hAdmW : Adm v εW μ := Work.BoseFixB1.Adm.mono hAdm (min_le_right _ _)
  have hNnn : 0 ≤ normB v μ n (Φ : X n → ℝ) := Work.BoseFixB1.normB_nonneg _
  have hκnn : 0 ≤ kappa v μ := kappa_nonneg hμ hav
  obtain ⟨hrow1, hrow2⟩ := hled J μ hAdmL hJK n Φ hN hlow
  have hn : (n : ℝ) ≤ CW * μ * (sideAt μ (a v)) ^ 3 := hwin J μ hAdmW hJK n Φ hN hlow
  have hE : (E' * (μ * a v * kappa v μ)) * (n : ℝ) * normB v μ n (Φ : X n → ℝ)
      ≤ (E' * CW) * (μ ^ 2 * a v * (sideAt μ (a v)) ^ 3 * kappa v μ)
          * normB v μ n (Φ : X n → ℝ) := by
    have h1 : (μ * a v * kappa v μ) * (n : ℝ)
        ≤ (μ * a v * kappa v μ) * (CW * μ * (sideAt μ (a v)) ^ 3) :=
      mul_le_mul_of_nonneg_left hn (mul_nonneg (mul_nonneg hμ.le hav0) hκnn)
    calc (E' * (μ * a v * kappa v μ)) * (n : ℝ) * normB v μ n (Φ : X n → ℝ)
        ≤ (E' * ((μ * a v * kappa v μ) * (CW * μ * (sideAt μ (a v)) ^ 3)))
            * normB v μ n (Φ : X n → ℝ) := by
          refine mul_le_mul_of_nonneg_right ?_ hNnn
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left h1 hE'
      _ = (E' * CW) * (μ ^ 2 * a v * (sideAt μ (a v)) ^ 3 * kappa v μ)
            * normB v μ n (Φ : X n → ℝ) := by ring
  have hclean : CA * (μ ^ 2 * a v * (sideAt μ (a v)) ^ 3 * kappa v μ)
            * normB v μ n (Φ : X n → ℝ)
          + (E' * CW) * (μ ^ 2 * a v * (sideAt μ (a v)) ^ 3 * kappa v μ)
            * normB v μ n (Φ : X n → ℝ)
        = (CA + E' * CW) * (μ ^ 2 * a v * (sideAt μ (a v)) ^ 3 * kappa v μ)
            * normB v μ n (Φ : X n → ℝ) := by ring
  have hsum1 : c₁' * nomRPsi h μ (Φ : X n → ℝ)
      ≤ (CA + E' * CW) * (μ ^ 2 * a v * (sideAt μ (a v)) ^ 3 * kappa v μ)
          * normB v μ n (Φ : X n → ℝ) := by linarith [hrow1, hE, hclean]
  have hDnn : 0 ≤ μ ^ 2 * a v * (sideAt μ (a v)) ^ 3 * kappa v μ :=
    mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg μ) hav0) (pow_nonneg hℓ.le 3)) hκnn
  constructor
  · have h2 : nomRPsi h μ (Φ : X n → ℝ)
        ≤ ((CA + E' * CW) * (μ ^ 2 * a v * (sideAt μ (a v)) ^ 3 * kappa v μ)
              * normB v μ n (Φ : X n → ℝ)) / c₁' := by
      rw [le_div_iff₀ hc₁']
      rw [mul_comm]
      exact hsum1
    calc nomRPsi h μ (Φ : X n → ℝ)
        ≤ ((CA + E' * CW) * (μ ^ 2 * a v * (sideAt μ (a v)) ^ 3 * kappa v μ)
              * normB v μ n (Φ : X n → ℝ)) / c₁' := h2
      _ = ((CA + E' * CW) / c₁') * (μ ^ 2 * a v * (sideAt μ (a v)) ^ 3 * kappa v μ)
            * normB v μ n (Φ : X n → ℝ) := by ring
      _ ≤ CA' * (μ ^ 2 * a v * (sideAt μ (a v)) ^ 3 * kappa v μ)
            * normB v μ n (Φ : X n → ℝ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle1 hDnn) hNnn
  · have hsum2 : ((paramsAt μ (a v)).b / (2 * (sideAt μ (a v)) ^ 2))
          * cnPlus (sideAt μ (a v)) (Φ : X n → ℝ)
        ≤ (CA + E' * CW) * (μ ^ 2 * a v * (sideAt μ (a v)) ^ 3 * kappa v μ)
            * normB v μ n (Φ : X n → ℝ) := by linarith [hrow2, hE, hclean]
    calc ((paramsAt μ (a v)).b / (2 * (sideAt μ (a v)) ^ 2))
          * cnPlus (sideAt μ (a v)) (Φ : X n → ℝ)
        ≤ (CA + E' * CW) * (μ ^ 2 * a v * (sideAt μ (a v)) ^ 3 * kappa v μ)
            * normB v μ n (Φ : X n → ℝ) := hsum2
      _ ≤ CA' * (μ ^ 2 * a v * (sideAt μ (a v)) ^ 3 * kappa v μ)
            * normB v μ n (Φ : X n → ℝ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle2 hDnn) hNnn

/-! ## 2. The two windows -/

/-- **The sharp particle window from `PerBoxFNomMuE`** — `nomCleanRowsMuE` followed by the PROVED
`Work.BoseB1Cube.nomWindowBridgeMu`. -/
theorem particleWindowMuE {v : E3 → ℝ} (h : ScatSol v) (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1)
    (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) (hav : 0 < a v)
    (hMu : PerBoxFNomMuE v h R) : ParticleWindowMu v h R :=
  nomWindowBridgeMu h hv hvrad hR hv_supp hav (nomCleanRowsMuE h hv hv1 hvrad hR hv_supp hav hMu)

/-- **The excited-particle window from `PerBoxFNomMuE`.**  Twin of
`Work.BoseB1Cube.nPlusWindowMu_of_perBoxFNomMu` with `(CA + E'·CW)` in place of

`(CA + 1·CW)`: the ledger's error slot is absorbed by the count window. -/
theorem nPlusWindowMuE {v : E3 → ℝ} (h : ScatSol v) (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1)
    (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) (hav : 0 < a v)
    (hMu : PerBoxFNomMuE v h R) : NPlusWindowMu v h R := by
  obtain ⟨εμ, c₁, C, CE, hεμ, hc₁, hC, hCE, hrowμ⟩ := hMu
  have hperS : PerBoxFNomSlotsE v h R :=
    perBoxFNomSlotsE_of_perBoxFNomMuE h hv hvrad hR hv_supp psiWeightFourIntegral_holdsSWE
      ⟨εμ, c₁, C, CE, hεμ, hc₁, hC, hCE, hrowμ⟩
  obtain ⟨ε₀', c₁', C', CE', hε₀', hc₁', hC', hCE', hbody⟩ := hperS
  have hperS' : PerBoxFNomSlotsE v h R := ⟨ε₀', c₁', C', CE', hε₀', hc₁', hC', hCE', hbody⟩
  have hS : SlidingGoodCube v h := slidingGoodCube h hv hv1 hvrad hR hv_supp hav
  obtain ⟨εL, CA, E', hεL, hCA0, hE'0, hled⟩ :=
    ledgerNomE (v := v) (h := h) (R := R) hv hv1 hvrad hR hv_supp hav
      (c₁ := c₁') (C := C') (E := 1) (CE := CE') hc₁' hC' one_pos hCE' ⟨ε₀', hε₀', hbody⟩ hS
  obtain ⟨εW, CW, hεW, hCW0, hwin⟩ :=
    countWindowOfPerBoxFNomSlotsE (v := v) h hv hv1 hvrad hR hv_supp hav hS
      (fun c₁ C E CE h1 h2 h3 h4 row hSg =>
        ledgerNomE (v := v) (h := h) (R := R) hv hv1 hvrad hR hv_supp hav h1 h2 h3 h4 row hSg)
      hperS'
  refine ⟨min εL εW, 2 * (CA + E' * CW) / Work.BoseBox.bValue, lt_min hεL hεW, ?_, ?_⟩
  · have hb : (0 : ℝ) < Work.BoseBox.bValue := by norm_num [Work.BoseBox.bValue]
    exact div_nonneg (by positivity) hb.le
  · intro J μ hAdm hJK n Φ hNB hlow
    have hμ : 0 < μ := adm_mu_pos hAdm
    have hav0 : 0 ≤ a v := (adm_a_pos hAdm).le
    have hℓ : 0 < sideAt μ (a v) := adm_ell_pos hAdm
    have hb : (0 : ℝ) < (paramsAt μ (a v)).b := paramsAt_b_pos μ (a v)
    have hN : 0 ≤ normB v μ n (Φ : X n → ℝ) := by
      rw [Work.BoseBoxFix.normB, Work.BoseKinLoc.sqNormB]
      exact integral_nonneg fun x => sq_nonneg _
    have hKB : 0 ≤ (paramsAt μ (a v)).KB := by
      rw [KB_eq_fsXp μ (a v)]
      exact Work.BoseBox.fsXp_nonneg (t := μ * (a v) ^ 3) (c := -6) (by positivity)
    have hκ : 0 ≤ kappa v μ := by
      unfold kappa
      exact mul_nonneg (pow_nonneg hKB 3) (Real.rpow_nonneg (by positivity) _)
    have hD : 0 ≤ μ ^ 2 * (a v) * (sideAt μ (a v)) ^ 3 * kappa v μ :=
      mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg μ) hav0) (pow_nonneg hℓ.le 3)) hκ
    have hAdmL : Adm v εL μ := Adm.mono hAdm (min_le_left _ _)
    have hAdmW : Adm v εW μ := Adm.mono hAdm (min_le_right _ _)
    obtain ⟨-, hgap⟩ := hled J μ hAdmL hJK n Φ hNB hlow
    have hn : (n : ℝ) ≤ CW * μ * (sideAt μ (a v)) ^ 3 := hwin J μ hAdmW hJK n Φ hNB hlow
    have hrow2 : (E' * (μ * a v * kappa v μ)) * (n : ℝ) * normB v μ n (Φ : X n → ℝ)
        ≤ (E' * CW) * (μ ^ 2 * a v * (sideAt μ (a v)) ^ 3 * kappa v μ)
            * normB v μ n (Φ : X n → ℝ) := by
      have h1 : (μ * a v * kappa v μ) * (n : ℝ)
          ≤ (μ * a v * kappa v μ) * (CW * μ * (sideAt μ (a v)) ^ 3) :=
        mul_le_mul_of_nonneg_left hn (mul_nonneg (mul_nonneg hμ.le hav0) hκ)
      calc (E' * (μ * a v * kappa v μ)) * (n : ℝ) * normB v μ n (Φ : X n → ℝ)
          ≤ (E' * ((μ * a v * kappa v μ) * (CW * μ * (sideAt μ (a v)) ^ 3)))
              * normB v μ n (Φ : X n → ℝ) := by
            refine mul_le_mul_of_nonneg_right ?_ hN
            rw [mul_assoc]
            exact mul_le_mul_of_nonneg_left h1 hE'0
        _ = (E' * CW) * (μ ^ 2 * a v * (sideAt μ (a v)) ^ 3 * kappa v μ)
              * normB v μ n (Φ : X n → ℝ) := by ring
    have hmain : (paramsAt μ (a v)).b / (2 * (sideAt μ (a v)) ^ 2)
          * Submission.BoseGases.cnPlus (sideAt μ (a v)) (Φ : X n → ℝ)
        ≤ (CA + E' * CW) * (μ ^ 2 * a v * (sideAt μ (a v)) ^ 3 * kappa v μ)
            * normB v μ n (Φ : X n → ℝ) := by
      have hsum : CA * (μ ^ 2 * a v * (sideAt μ (a v)) ^ 3 * kappa v μ)
              * normB v μ n (Φ : X n → ℝ)
            + (E' * CW) * (μ ^ 2 * a v * (sideAt μ (a v)) ^ 3 * kappa v μ)
              * normB v μ n (Φ : X n → ℝ)
          = (CA + E' * CW) * (μ ^ 2 * a v * (sideAt μ (a v)) ^ 3 * kappa v μ)
              * normB v μ n (Φ : X n → ℝ) := by ring
      linarith [hgap, hrow2, hsum]
    have hstep : Submission.BoseGases.cnPlus (sideAt μ (a v)) (Φ : X n → ℝ)
        ≤ (2 * (sideAt μ (a v)) ^ 2 / (paramsAt μ (a v)).b)
            * ((CA + E' * CW) * (μ ^ 2 * a v * (sideAt μ (a v)) ^ 3 * kappa v μ)
                * normB v μ n (Φ : X n → ℝ)) := by
      have hne : (0 : ℝ) < 2 * (sideAt μ (a v)) ^ 2 / (paramsAt μ (a v)).b := by positivity
      have h2 := mul_le_mul_of_nonneg_left hmain hne.le
      have heq : (2 * (sideAt μ (a v)) ^ 2 / (paramsAt μ (a v)).b)
            * ((paramsAt μ (a v)).b / (2 * (sideAt μ (a v)) ^ 2)
              * Submission.BoseGases.cnPlus (sideAt μ (a v)) (Φ : X n → ℝ))
          = Submission.BoseGases.cnPlus (sideAt μ (a v)) (Φ : X n → ℝ) := by
        field_simp
      linarith [h2, heq.le, heq.ge]
    refine le_trans hstep (le_of_eq ?_)
    have hKl : μ * a v * (sideAt μ (a v)) ^ 2 = (paramsAt μ (a v)).Kl ^ 2 :=
      mu_mul_a_mul_ell_sq μ (a v) hμ hav
    have hk : kappa v μ
        = (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ) := rfl
    rw [hk, Work.BoseBox.nPlusWindow, ← hKl, ← Work.BoseBox.sideAt,
      Work.BoseFixB1.paramsAt_b_eq μ (a v)]
    ring_nf

/-! ## 3. The node -/

/-- **`Work.BoseBoxFix.NodeB1B v h J` from `PerBoxFNomMuE`** — the `E`-route's endgame. -/
theorem nodeB1B_of_perBoxFNomMuE {v : E3 → ℝ} (h : ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) (hav : 0 < a v) {J : ℝ}
    (hMu : PerBoxFNomMuE v h R) : Work.BoseBoxFix.NodeB1B v h J :=
  Work.BoseB1Cube.nodeB1B_of_windows
    (particleWindowMuE h hv hv1 hvrad hR hv_supp hav hMu)
    (nPlusWindowMuE h hv hv1 hvrad hR hv_supp hav hMu)

end Work.BoseSWE
