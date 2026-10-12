import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1.bqPotsplit
import Submission.Work.BoseFixB1B.matchedWindowDefs
import Submission.Work.BoseFixB1B.perBoxFTotalDefs
import Submission.Work.BoseFixB1S.a0A2PaymentAdm
import Submission.Work.BoseFixB1S.countWindowUnif_of_aprioriUnif
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1S.LowCountWindowAllJCube` — the **matched-window (single cube
# cutoff) interface** of the count window, and the ledger that closes the target from it

Written by the holder of `Submission/Work/BoseFixB1S/LowCountWindowAllJ.lean`.

## Why this module exists

The count window (the target of `LowCountWindowAllJ`) is closed by the frozen chain

    target  ⟸  `AprioriUnif`  ⟸  { `CollectedUnif`, `SlidingB` }                (all proved)

(the first step is `countWindowUnif_of_aprioriUnif`, the second `aprioriUnifOfCollectedUnif`).
The remaining content of the node is therefore the single frozen predicate `CollectedUnif`, i.e.
FS `thm:smallbox` collected with one triple of constants over all thresholds — read at the frozen
sliding word `sbWord`.

**That spelling is blocked by the two-cutoff mismatch** (`FINDING_wholeBoxSocket.md` §2/(R-I),
`matchedWindowDefs.lean`): the frozen word's kinetic slot carries the *ball* window `chiB` while
its potential/pairing slot carries the *cube* window `chiSmallB`; both instruments that *pay* the
pairing (the rung-4 payment `a0A2PaymentAdm_holds` and the Bogoliubov port `slidingBogPort_proved`)
are stated at the cube window, and the window comparison that would transfer them to `chiB` is
*not* an independent input (its only route consumes the a-priori supply, i.e. this very node).

The fleet's clean route is to run the chapter at the **single cube cutoff** — FS's own modelling
(`eq:chiBdefinition`: one `χ_B` for both slots), whose vocabulary is
`Submission/Work/BoseFixB1B/matchedWindowDefs.lean`:

* `sbKinCube = bGapCoeff·n₊ + cubeSpectral` — the frozen `sbKin` with its spectral slot at
  `chiSmallB`;
* `sbWordCube = sbKinCube + sbPot` — the matched sliding word;
* `SlidingBCube` — FS `eq:BSsliding2` / Bratteli–Solovej Thm 3.10 at the cube cutoff (the
  matched analogue of the *proved* `Work.BoseFixB1.SlidingB`).

## What this module banks

* `CollectedUnifCube v h` — FS `thm:smallbox` collected at one triple of constants over all
  thresholds `J ≤ K_B³`, with the word slot read at `sbWordCube`.  **The demand side is
  unchanged**: `Work.BoseFixB1.RPsi` is the window-independent state remainder, so this predicate
  is *strictly weaker* than the frozen `CollectedUnif` (which bounds the same `RPsi` by the
  integral of the *smaller* word `sbWord`).
* `aprioriUnifOfCollectedUnifCube` — `{SlidingBCube, CollectedUnifCube} ⟹ AprioriUnif`, the
  matched twin of the proved `aprioriUnifOfCollectedUnif`.  The ledger is *pure real arithmetic*
  and does not depend on the window: only the two inequalities
  `c·R ≤ I + X(1 + CC·κ)N` and `(b/2ℓ²)cP + (1/CS)·I ≤ W` and the low-state bound `W ≤ −X(1−κ)N`
  are used, with `I` now the integral of `sbWordCube`.
* `countWindowUnif_of_collectedUnifCube` — the target's **conclusion** from those two cube inputs,
  via the proved `countWindowUnif_of_aprioriUnif`.

So the node's residual is re-pointed from the (blocked) frozen `CollectedUnif` onto the live cube
frontier `{CollectedUnifCube, SlidingBCube}`: the first is supplied by the cube per-box bound
(whose per-box input is the *matched* one, hence payable by the proved port), the second by FS's
localisation re-run at the cube cutoff.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Real Topology BigOperators

namespace Work.BoseFixB1S

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBoxFix Work.BoseBox
open Work.BoseFixB1B

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## 1. The matched-window interface -/

/-- **FS `thm:smallbox` collected over the small boxes with one triple of constants for all
thresholds `J ≤ K_B³`, at the single cube cutoff** — the exact matched-window analogue of
`Work.BoseFixB1S.CollectedUnif`: same `∃ ε₀ C c`, same demand
(`0 ≤ R_Ψ` and `c·R_Ψ ≤ ∫ H_{B(u)} + 4πμ²(a v)ℓ³(1 + Cκ)‖Φ‖²`), the word slot being
`sbWordCube` (`Work.BoseFixB1B.sbWordCube`) instead of the frozen `sbWord`.

Since `RPsi` does not involve the cutoff and `sbWordCube ≥ sbWord` pointwise (the cube window
dominates the ball window on the box fibres), this is *strictly weaker* than `CollectedUnif`. -/
def CollectedUnifCube (v : E3 → ℝ) (h : ScatSol v) : Prop :=
  ∃ ε₀ C c : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧ 0 < c ∧
    ∀ J : ℝ, ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      J ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3 →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))),
        Work.BoseBoxFix.IsLowB v h J μ n Φ →
          0 ≤ Work.BoseFixB1.RPsi v h μ (Φ : Submission.BoseGases.X n → ℝ) ∧
          c * Work.BoseFixB1.RPsi v h μ (Φ : Submission.BoseGases.X n → ℝ)
            ≤ (∫ u : E3, sbWordCube v h μ u (Φ : Submission.BoseGases.X n → ℝ))
              + 4 * π * μ ^ 2 * (_root_.BoseGases.a v)
                  * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3
                  * (1 + C * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
                      * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ))
                  * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)

/-! ## 2. The ledger: `AprioriUnif` from the cube localisation and the cube collected bound

The two arithmetic ledgers are the ones of `aprioriUnifOfCollectedUnif.lean` (verbatim: they are
*bare real inequalities* and therefore window-free); only the inputs change. -/

/-- Real-arithmetic ledger for the `R_Ψ` bound (the first a-priori inequality of FS
`eq:aprioriRn+`).  From the collected bound `c·R ≤ I + X(1 + CCκ)N`, the sliding bound
`C_S⁻¹ I ≤ W` and the low-state bound `W ≤ −X(1 − κ)N` with `C_S ≥ 1`, `κ ≥ 0`, `X ≥ 0`,
`N ≥ 0`, one gets `c·R ≤ (CC + C_S)(Xκ)N`. -/
private lemma ledger_R_cube {c CS CC R I W X κ N : ℝ}
    (hCS : 1 ≤ CS) (hX : 0 ≤ X) (hκ : 0 ≤ κ) (hN : 0 ≤ N)
    (hcol : c * R ≤ I + X * (1 + CC * κ) * N)
    (hslide : (1 / CS) * I ≤ W)
    (hW : W ≤ -(X * (1 - κ)) * N) :
    c * R ≤ (CC + CS) * (X * κ) * N := by
  have hCSpos : 0 < CS := lt_of_lt_of_le one_pos hCS
  have h1 : (1 / CS) * I ≤ -(X * (1 - κ)) * N := le_trans hslide hW
  have h2 : I ≤ CS * (-(X * (1 - κ)) * N) := by
    have hh := mul_le_mul_of_nonneg_left h1 (le_of_lt hCSpos)
    have he : CS * ((1 / CS) * I) = I := by field_simp
    linarith [hh, he]
  have h3 : c * R ≤ CS * (-(X * (1 - κ)) * N) + X * (1 + CC * κ) * N := by linarith
  have h4 : CS * (-(X * (1 - κ)) * N) + X * (1 + CC * κ) * N ≤ (CC + CS) * (X * κ) * N := by
    have h5 : (CC + CS) * (X * κ) * N - (CS * (-(X * (1 - κ)) * N) + X * (1 + CC * κ) * N)
        = (CS - 1) * (X * N) := by ring
    have h6 : 0 ≤ (CS - 1) * (X * N) := mul_nonneg (by linarith) (mul_nonneg hX hN)
    linarith [h5, h6]
  linarith [h3, h4]

/-- Real-arithmetic ledger for the `⟨n₊⟩` bound (the second a-priori inequality of FS
`eq:aprioriRn+`). -/
private lemma ledger_cn_cube {b2 c CS CC R I W X κ N cP : ℝ}
    (hc : 0 < c) (hCS : 1 ≤ CS) (hCC : 0 ≤ CC) (hb2 : 0 ≤ b2) (hX : 0 ≤ X) (hκ : 0 ≤ κ)
    (hN : 0 ≤ N) (hcP : 0 ≤ cP) (hR0 : 0 ≤ R)
    (hcol : c * R ≤ I + X * (1 + CC * κ) * N)
    (hslide : b2 * cP + (1 / CS) * I ≤ W)
    (hW : W ≤ -(X * (1 - κ)) * N) :
    b2 * cP ≤ (CC + 1) * (X * κ) * N := by
  have hCSpos : 0 < CS := lt_of_lt_of_le one_pos hCS
  have hfac : 0 < 1 + CC * κ := by nlinarith
  have hI : -(X * (1 + CC * κ) * N) ≤ I := by nlinarith [hcol, hR0, hc]
  have hIS : -(1 / CS) * I ≤ (1 / CS) * (X * (1 + CC * κ) * N) := by
    have hh := mul_le_mul_of_nonneg_left hI (by positivity : (0:ℝ) ≤ 1 / CS)
    linarith [hh]
  have h3 : b2 * cP ≤ -(X * (1 - κ)) * N + (1 / CS) * (X * (1 + CC * κ) * N) := by
    linarith [hslide, hW, hIS]
  have h4 : -(X * (1 - κ)) * N + (1 / CS) * (X * (1 + CC * κ) * N)
      ≤ (CC + 1) * (X * κ) * N := by
    have hdiv : (1 + CC * κ) / CS ≤ 1 + CC * κ := by
      rw [div_le_iff₀ hCSpos]
      nlinarith [hCS, hfac]
    have h5 : (CC + 1) * (X * κ) * N
        - (-(X * (1 - κ)) * N + (1 / CS) * (X * (1 + CC * κ) * N))
        = (X * N) * ((CC + 1) * κ + (1 - κ) - (1 + CC * κ) / CS) := by ring
    have h6 : 0 ≤ (X * N) * ((CC + 1) * κ + (1 - κ) - (1 + CC * κ) / CS) :=
      mul_nonneg (mul_nonneg hX hN) (by nlinarith [hdiv, hκ, hCC])
    linarith [h5, h6]
  linarith [h3, h4]

/-- **The `J`-uniform a-priori inequality from the matched-window localisation and the
matched-window collected per-box bound.**  FS `eq:BSsliding2` at the single cube cutoff
(`SlidingBCube`) plus FS `thm:smallbox` collected at the cube cutoff with a *single* constant for
all `J ≤ K_B³` (`CollectedUnifCube`) give FS `eq:aprioriRn+` with a single constant for all
`J ≤ K_B³` (`AprioriUnif`).

This is the verbatim ledger of `Work.BoseFixB1S.aprioriUnifOfCollectedUnif` (`Work.BoseFixB1.SlidingB`
replaced by `SlidingBCube`, `∫sbWord` by `∫sbWordCube`); no analysis enters. -/
theorem aprioriUnifOfCollectedUnifCube {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    {h : Work.UBB.ScatSol v} (hS : SlidingBCube v h) (hC : CollectedUnifCube v h) :
    Work.BoseFixB1S.AprioriUnif v h := by
  obtain ⟨εS, CS, hCS1, hεS, hSfun⟩ := hS
  obtain ⟨εC, CC, c, hεC, hCC, hc, hCfun⟩ := hC
  refine ⟨max 1 (max (4 * π * (CC + CS) / c) (4 * π * (CC + 1))), min εS εC,
    le_max_left _ _, lt_min hεS hεC, ?_⟩
  intro J μ hAdm hJ n Φ hLow
  have hAdmS : Work.BoseBoxFix.Adm v εS μ := Work.BoseFixB1.Adm.mono hAdm (min_le_left _ _)
  have hAdmC : Work.BoseBoxFix.Adm v εC μ := Work.BoseFixB1.Adm.mono hAdm (min_le_right _ _)
  have hμ : 0 < μ := Work.BoseFixB1.adm_mu_pos hAdm
  have hav : 0 < _root_.BoseGases.a v := Work.BoseFixB1.adm_a_pos hAdm
  have hLpos : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := Work.BoseFixB1.adm_ell_pos hAdm
  have hKBpos : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB :=
    Work.BoseFixB1.paramsAt_KB_pos hAdm
  have hbpos : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).b :=
    Work.BoseFixB1.paramsAt_b_pos μ (_root_.BoseGases.a v)
  have ht0 : 0 ≤ μ * (_root_.BoseGases.a v) ^ 3 := (mul_pos hμ (pow_pos hav 3)).le
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB := ⟨_, rfl⟩
  obtain ⟨bb, hbb⟩ : ∃ bb : ℝ, bb = (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).b := ⟨_, rfl⟩
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = 4 * π * μ ^ 2 * (_root_.BoseGases.a v)
      * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3 := ⟨_, rfl⟩
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
      * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ) := ⟨_, rfl⟩
  obtain ⟨NN, hNN⟩ : ∃ NN : ℝ, NN = Work.BoseBoxFix.normB v μ n
      (Φ : Submission.BoseGases.X n → ℝ) := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = Work.BoseFixB1.RPsi v h μ
      (Φ : Submission.BoseGases.X n → ℝ) := ⟨_, rfl⟩
  obtain ⟨I, hI⟩ : ∃ I : ℝ, I = ∫ u : EuclideanSpace ℝ (Fin 3), sbWordCube v h μ u
      (Φ : Submission.BoseGases.X n → ℝ) := ⟨_, rfl⟩
  obtain ⟨cP, hcP⟩ : ∃ cP : ℝ, cP = Submission.BoseGases.cnPlus
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) (Φ : Submission.BoseGases.X n → ℝ) := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W : ℝ, W = Work.BoseBoxFix.wordB v h μ n Φ := ⟨_, rfl⟩
  obtain ⟨A0, hA0⟩ : ∃ A0 : ℝ, A0 = μ ^ 2 * (_root_.BoseGases.a v)
      * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3
      * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
      * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ) := ⟨_, rfl⟩
  obtain ⟨Cfin, hCfin⟩ : ∃ Cfin : ℝ,
      Cfin = max 1 (max (4 * π * (CC + CS) / c) (4 * π * (CC + 1))) := ⟨_, rfl⟩
  have hX0 : 0 ≤ X := by
    rw [hX]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (le_of_lt Real.pi_pos))
      (sq_nonneg μ)) hav.le) (pow_nonneg hLpos.le 3)
  have hκ0 : 0 ≤ κ := by
    rw [hκ]
    exact mul_nonneg (pow_nonneg hKBpos.le 3) (Real.rpow_nonneg ht0 _)
  have hNN0 : 0 ≤ NN := by rw [hNN]; exact Work.BoseFixB1.normB_nonneg _
  have hcP0 : 0 ≤ cP := by rw [hcP]; exact Submission.BoseGases.cnPlus_nonneg
  have hA00 : 0 ≤ A0 := by
    rw [hA0]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg μ) hav.le)
      (pow_nonneg hLpos.le 3)) (pow_nonneg hKBpos.le 3)) (Real.rpow_nonneg ht0 _)
  have hb20 : 0 ≤ bb / (2 * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 2) := by
    have h2 : (0:ℝ) < 2 * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 2 := by positivity
    rw [hbb]
    exact div_nonneg hbpos.le h2.le
  have hcol : c * R ≤ I + X * (1 + CC * κ) * NN := by
    have hh := (hCfun J μ hAdmC hJ n Φ hLow).2
    rw [← hR, ← hI, ← hX, ← hNN] at hh
    have hfix : CC * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
        * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ) = CC * κ := by
      rw [hκ]; ring
    rw [hfix] at hh
    exact hh
  have hR0 : 0 ≤ R := by rw [hR]; exact (hCfun J μ hAdmC hJ n Φ hLow).1
  have hslide : (bb / (2 * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 2)) * cP
      + (1 / CS) * I ≤ W := by
    have hh := hSfun μ hAdmS n Φ
    rw [← hcP, ← hbb, ← hI, ← hW] at hh
    exact hh
  have hJsqrt : J * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ) ≤ κ := by
    rw [hκ]
    exact mul_le_mul_of_nonneg_right hJ (Real.rpow_nonneg ht0 _)
  have hWU : W ≤ -(X * (1 - κ)) * NN := by
    have hh := (Work.BoseFixB1.isLowB_iff (v := v) (h := h) (J := J) (μ := μ) (n := n)
      (Φ := (Φ : Submission.BoseGases.X n → ℝ)) hav).mp hLow
    rw [← hW, ← hX, ← hNN, Real.sqrt_eq_rpow] at hh
    have hT : (1 : ℝ) - κ ≤ 1 - J * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ) := by
      linarith [hJsqrt]
    have h2 : X * (1 - κ) * NN
        ≤ X * (1 - J * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ)) * NN :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hT hX0) hNN0
    have h3 : -(X * (1 - J * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ)) * NN)
        ≤ -(X * (1 - κ) * NN) := neg_le_neg h2
    have h4 : -(X * (1 - J * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ))) * NN
        = -(X * (1 - J * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ)) * NN) := by ring
    have h5 : -(X * (1 - κ)) * NN = -(X * (1 - κ) * NN) := by ring
    calc W ≤ -(X * (1 - J * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ))) * NN := hh
      _ = -(X * (1 - J * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ)) * NN) := h4
      _ ≤ -(X * (1 - κ) * NN) := h3
      _ = -(X * (1 - κ)) * NN := h5.symm
  have hslide1 : (1 / CS) * I ≤ W := by
    have hterm : 0 ≤ (bb / (2 * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 2)) * cP :=
      mul_nonneg hb20 hcP0
    linarith [hslide, hterm]
  have hBA : X * κ = 4 * π * A0 := by rw [hX, hκ, hA0]; ring
  rw [← hCfin, ← hA0, ← hR, ← hNN, ← hcP, ← hbb]
  refine ⟨hR0, ?_, ?_⟩
  · have hled0 := ledger_R_cube (c := c) (CS := CS) (CC := CC) (R := R) (I := I) (W := W)
      (X := X) (κ := κ) (N := NN) hCS1 hX0 hκ0 hNN0 hcol hslide1 hWU
    have hled : c * R ≤ (CC + CS) * (4 * π * A0) * NN := by
      have hh := hled0
      rw [hBA] at hh
      exact hh
    have h2 : R * c ≤ (CC + CS) * (4 * π * A0) * NN := by linarith [hled]
    have h3 : R ≤ ((CC + CS) * (4 * π * A0) * NN) / c := (le_div_iff₀ hc).mpr h2
    have hval : ((CC + CS) * (4 * π * A0) * NN) / c
        = (4 * π * (CC + CS) / c) * A0 * NN := by
      field_simp
      try ring
    rw [hval] at h3
    have hCle : 4 * π * (CC + CS) / c ≤ Cfin := by
      rw [hCfin]
      exact le_trans (le_max_left _ _) (le_max_right _ _)
    calc R ≤ (4 * π * (CC + CS) / c) * A0 * NN := h3
      _ ≤ Cfin * A0 * NN := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCle hA00) hNN0
  · have hled0 := ledger_cn_cube
      (b2 := bb / (2 * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 2))
      (c := c) (CS := CS) (CC := CC) (R := R) (I := I) (W := W) (X := X) (κ := κ) (N := NN)
      (cP := cP) hc hCS1 hCC hb20 hX0 hκ0 hNN0 hcP0 hR0 hcol hslide hWU
    have hled : (bb / (2 * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 2)) * cP
        ≤ (CC + 1) * (4 * π * A0) * NN := by
      have hh := hled0
      rw [hBA] at hh
      exact hh
    have heq : (CC + 1) * (4 * π * A0) * NN = (4 * π * (CC + 1)) * A0 * NN := by ring
    rw [heq] at hled
    have hCle2 : 4 * π * (CC + 1) ≤ Cfin := by
      rw [hCfin]
      exact le_trans (le_max_right _ _) (le_max_right _ _)
    calc (bb / (2 * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 2)) * cP
        ≤ (4 * π * (CC + 1)) * A0 * NN := hled
      _ ≤ Cfin * A0 * NN := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCle2 hA00) hNN0

/-! ## 3. The count window from the two matched-window inputs -/

/-- **The count window `∀ J ≤ K_B³` (the conclusion of the target) from the matched-window
localisation and the matched-window collected per-box bound.** -/
theorem countWindowUnif_of_collectedUnifCube {v : E3 → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hav : 0 < _root_.BoseGases.a v)
    (hS : SlidingBCube v h) (hC : CollectedUnifCube v h) :
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧
      ∀ (J : ℝ), ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        J ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3 →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))),
          0 < Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) →
          Work.BoseBoxFix.IsLowB v h J μ n Φ →
            (n : ℝ) ≤ C * μ * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3 :=
  Work.BoseFixB1S.countWindowUnif_of_aprioriUnif h hv hv1 hvrad hR hv_supp hav
    (aprioriUnifOfCollectedUnifCube hS hC)

/-- **The matched-window (cube-cutoff) pointwise per-box bound**: `Work.BoseFixB1.PerBoxF`
with the word slot read at `sbWordCube`.  Since `sbWord ≤ sbWordCube`, the frozen `PerBoxF`
*implies* this one; it is the input of the matched collection chain
(`collectedUnifOfPerBoxInterior`'s cube twin). -/
def PerBoxFCube (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v) (R c₁ C : ℝ) (μ : ℝ) (n : ℕ)
    (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))) (u : EuclideanSpace ℝ (Fin 3)) : Prop :=
  c₁ * (Work.BoseFixB1.w1MassB h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u *
        (∫ x in abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)), (Φ x) ^ 2 *
          Work.SmallBoxSliding.psiWeight 1 μ (Work.BoseFixB1.nCountB (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u x /
            Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)))
    - (1 / 2) * μ ^ 2 * Work.BoseFixB1.w1MassB h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u *
        normB v μ n (Φ : X n → ℝ)
    - C * (μ ^ 2 * (a v) * ((R / (Work.BoseBox.sideAt μ (_root_.BoseGases.a v) * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)) ^ 2
            + (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
          * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u *
          normB v μ n (Φ : X n → ℝ)
        + μ * (a v) * normB v μ n (Φ : X n → ℝ))
  ≤ sbWordCube v h μ u (Φ : X n → ℝ)

/-! ## 3bis. FS `thm:smallbox` at the sliding box, cube cutoff, total-density spelling -/

/-- **FS `thm:smallbox` at the sliding box `B(u)`, in the total-density (`∫Φ²`) spelling** — the
form the corpus is missing.  Compare `Work.BoseFixB1.PerBoxF`: the only difference is that the
mean-field weight is read at the *total* density `chiDensB` instead of pointwise. -/
def PerBoxFTotalCube (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (R c₁ C : ℝ) (μ : ℝ) (n : ℕ)
    (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
    (u : E3) : Prop :=
  c₁ * (Work.BoseFixB1.w1MassB h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
        * Work.SmallBoxSliding.psiWeight 1 μ (chiDensB (v := v) μ u (Φ : Submission.BoseGases.X n → ℝ)))
      * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
    - (1 / 2) * μ ^ 2 * Work.BoseFixB1.w1MassB h
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
      * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
    - C * (μ ^ 2 * (_root_.BoseGases.a v)
          * ((R / (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
                    * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)) ^ 2
              + (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
                * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ)))
        * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
        * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
    - C * μ * (_root_.BoseGases.a v)
        * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
  ≤ sbWordCube v h μ u (Φ : Submission.BoseGases.X n → ℝ)

/-- **The in-box form of `PerBoxFTotal`**: the target's inequality restricted to states that are
*normalised* and *localised in the sliding box* (`∀ᵐ x, Φ x ≠ 0 → ∀ i, x i ∈ B(u)`), i.e. the
hypotheses under which the corpus's proved sharp box estimates
(`Work.BoseFixB1S.sbWord_ge_a0Main_add_boxA2`, `Work.BoseFixB1S.a0A2PaymentAdm_holds`) apply.

The target `PerBoxFTotalCube` is this statement with the localisation hypothesis removed (the
normalisation is free: `PerBoxFTotal` is homogeneous of degree `2` in `Φ`).  The removal of the
localisation hypothesis is the sector/Fubini (`arity`) step: the word is additive over the
`n_A`-sectors (`Work.BoseFixB1.sbWordSectorAdditiveAdm`), each sector piece is localised on its
in-box slots by construction, and the total-density `F`-weight is compared sectorwise (Jensen plus
`F(λt) ≤ C(F(t) + μ²)`). -/
def InBoxTotalCube (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (R : ℝ) : Prop :=
  ∃ c₁ C ε₀ : ℝ, 0 < c₁ ∧ 0 ≤ C ∧ 0 < ε₀ ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
        (u : E3),
        0 < Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) →
        u ∈ Work.SmallBoxSliding.goodSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ →
        (∀ᵐ x ∂(MeasureTheory.volume.restrict
            (Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))),
          (Φ : Submission.BoseGases.X n → ℝ) x ≠ 0 →
            ∀ i : Fin n, x i ∈ Submission.BoseGases.dlBox
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) →
        (∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
            ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2) = 1 →
        PerBoxFTotalCube v h R c₁ C μ n Φ u

/-! ## 4. The matched-window rung

The rung's proof is *free*: the payment `Work.BoseFixB1S.a0A2PaymentAdm_holds` is stated purely on the
*potential* word (`boxQSum`), so no window enters; only the kinetic slot of the word changes.
-/

theorem sbWordCube_ge_a0Main_add_boxA2 {v : E3 → ℝ} (h : Work.UBB.ScatSol v) {R : ℝ}
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v)
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) (hav : 0 < _root_.BoseGases.a v) :
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
          (u : E3),
          0 < Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u →
          (1 : ℝ) ≤ μ * Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u →
          (∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
              ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2) = 1 →
          (∀ᵐ x ∂(MeasureTheory.volume.restrict
              (Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))),
            (Φ : Submission.BoseGases.X n → ℝ) x ≠ 0 →
              ∀ i : Fin n, x i ∈ Submission.BoseGases.dlBox
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) →
          0 ≤ Work.BoseFixB1S.boxM1 (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                (Submission.BoseGases.wSmall1Pair h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                  (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) →
          Work.BoseFixB1S.boxM1 (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                (Submission.BoseGases.wSmall1Pair h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                  (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
            ≤ Work.BoseFixB1S.boxM2 (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                (Submission.BoseGases.wSmallPair (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                  (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u (Submission.BoseGases.g2 v h)) →
          0 ≤ Work.BoseFixB1S.boxPairCount (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) (Φ : Submission.BoseGases.X n → ℝ) →
          Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) (Φ : Submission.BoseGases.X n → ℝ)
              * Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) (Φ : Submission.BoseGases.X n → ℝ)
            - Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) (Φ : Submission.BoseGases.X n → ℝ)
            ≤ Work.BoseFixB1S.boxPairCount (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) (Φ : Submission.BoseGases.X n → ℝ) →
          Work.BoseFixB1.a0MainLocBox (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) μ
              (Work.BoseFixB1S.boxM1 (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                (Submission.BoseGases.wSmall1Pair h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                  (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u))
              (Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) (Φ : Submission.BoseGases.X n → ℝ))
            + Work.BoseFixB1.boxA2 (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                (Submission.BoseGases.wSmall1Pair h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                  (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                (Φ : Submission.BoseGases.X n → ℝ)
            + sbKinCube v μ u
                (Φ : Submission.BoseGases.X n → ℝ)
            - C * (_root_.BoseGases.a v)
                * (μ + Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                      (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) (Φ : Submission.BoseGases.X n → ℝ)
                    / Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                * Work.BoseFixB1S.boxQCount (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                    (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) (Φ : Submission.BoseGases.X n → ℝ)
          ≤ sbWordCube v h μ u (Φ : Submission.BoseGases.X n → ℝ) := by
  obtain ⟨εp, C, hεp, hC, hpay⟩ := a0A2PaymentAdm_holds h hv hv1 hvrad hR hv_supp hav
  obtain ⟨εg, hεg, hreg⟩ := Work.BoseFixB1.regime_sideAt_ge (v := v) hav hR
  refine ⟨min εp εg, C, lt_min hεp hεg, hC, ?_⟩
  intro μ hAdm n Φ u hvol hμv hnorm hsupp hM1nn hM2 hPcnn hcS2
  have hAdmp : Work.BoseBoxFix.Adm v εp μ := Work.BoseFixB1.Adm.mono hAdm (min_le_left _ _)
  have hAdmg : Work.BoseBoxFix.Adm v εg μ := Work.BoseFixB1.Adm.mono hAdm (min_le_right _ _)
  obtain ⟨hR16, hRχ⟩ := hreg μ hAdm.1 (Work.BoseFixB1.adm_dilute hAdmg)
  have hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d := Work.BoseFixB1.adm_d_pos hAdm
  have hMv : 1 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M := by
    rw [Work.BoseFixB1.M_eq_mValue]; norm_num [Work.BoseBox.mValue]
  have hpay' := hpay μ hAdmp n Φ u hvol hμv hnorm hsupp hM1nn hM2 hPcnn hcS2
  have hpot := Work.BoseFixB1.bqPotsplit (v := v) (R0 := R) hv_supp hR hv hvrad hv1 h
    (M := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M) hMv
    (ℓ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (d := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) (μ := μ)
    hℓ hd hR16 hRχ u hvol (N := n) (Φ := (Φ : Submission.BoseGases.X n → ℝ)) Φ.contDiff.continuous
  rw [sbWordCube, Work.BoseFixB1.sbPot, Work.SmallBoxSliding.qLHSwordB]
  linarith [hpay', hpot]

end Work.BoseFixB1S
