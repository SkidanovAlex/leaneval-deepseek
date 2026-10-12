import ChallengeDeps
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.BoseB1Cube.sbCut_cube_le_mu
import Submission.Work.BoseB1Cube.smallWinNodes
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB1Cube.swhRegSR2Node_holds` — Node N2 (`RegularSR2Node`) of the small-window split

The node (`Work.BoseB1Cube.swhRegSR2Node v h`, `smallWinNodes.lean`) is FS's `SharpRow2`-row

    (1/18)·μ·(n/|B|)·W ≤ a0MainLocBox |B| μ W S + bA2 + bSpectralCube
                            + ½((M₂−W)/|B|²)·Pc + C·(a v)·μ·n₊

for *every* state of the count window `[Cn μ|B|, 2Cn μ|B|]` on a **regular** box
(`Work.BoseB1Cube.swhRegular`: `W ≥ (49/50)·8πa·χ_m`, `M₂ − W ≥ (49/50)·(g₀ω₀-mass)·χ_m`,
`1000 ≤ μ|B|`).

## The proof

The only analytic input is the PROVED Bogoliubov port `Work.BoseB1Cube.cubeBogPortRefinedR3`,
which absorbs `bA2 + bSpectralCube` at the price of three rows,

    −[ ½(1+κΓ)·g₀ω₀·((n+1)n/|B|²)·χ_m + C·a·(μ + n/|B|)·n₊ + C·a·c³·(n/|B|)·χ_m ]
        ≤ bA2 + bSpectralCube .

Everything else is the *ledger arithmetic* (`swhLedgerArith`): the row's **free** constant `C`
pays the credit (and the port's `μ·n₊`-proportional rows), the pair square
`½(M₂−W)Pc/|B|² ≥ ½(M₂−W)(S²−S)/|B|²` (with `Pc ≥ S² − S`, the PROVED `boxFlatSqJensen`) pays the
mass row, and `a0MainLocBox` at the box density `S/|B|` pays the demand.  The two mass comparisons

    M₂ ≤ 2·M₁ = 2W   (`boxM2_le_two_mul_boxM1`, i.e. `0 ≤ ω ≤ 1`)   and
    0 ≤ M₂ − M₁      (`boxM2_sub_boxM1_nonneg_slidingB1`)

give `m := M₂ − W ∈ [0, W]`, which is exactly what makes the ledger close on the *whole* count
window (no split into `n₊ ⋛ n/2` is needed, unlike the `RichRow`/`PoorRow` route).

The two diluteness thresholds `κ·PBΓ ≤ 1/20` and `Cq·(sbCut)³ ≤ μ` are the only `ε₀`-bookkeeping:
both are positive powers of the diluteness `t = μ(a v)³`, namely `PBΓ = t^{287/646}` and
`(sbCut μ (a v))³ = μ·t^{145/323}`, so any prescribed constant is absorbed by a small `ε₀`
(`Work.BoseB1S.fsXp_mul_log_le_one`).

`#print axioms Work.BoseB1Cube.swhRegSR2Node_holds = [propext, Classical.choice, Quot.sound]`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseB1Cube

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "X" => Submission.BoseGases.X

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 3200000

/-! ## 1. The two diluteness thresholds -/

lemma PBGamma_eq_rpow {v : E3 → ℝ} (hav : 0 < _root_.BoseGases.a v) (μ : ℝ)
    (hμ : 0 < μ) :
    Work.BoseFixB1B.PBΓ v μ
      = (μ * (_root_.BoseGases.a v) ^ 3) ^ (287 / 646 : ℝ) := by
  have ht : (0 : ℝ) < μ * (_root_.BoseGases.a v) ^ 3 := by positivity
  simp only [Work.BoseFixB1B.PBΓ, Work.BoseFixB1B.PBKB, Work.FockBridge.dlGamma,
    Work.BoseBox.paramsAt, Work.BoseBox.fsParams, Work.BoseBox.fsXp]
  have h1 : ((μ * (_root_.BoseGases.a v) ^ 3) ^ ((-6 : ℝ) / 323)) ^ 3
      = (μ * (_root_.BoseGases.a v) ^ 3) ^ (((-6 : ℝ) / 323) * (3 : ℝ)) := by
    rw [← Real.rpow_natCast ((μ * (_root_.BoseGases.a v) ^ 3) ^ ((-6 : ℝ) / 323)) 3,
      ← Real.rpow_mul ht.le]
    norm_num
  rw [h1, ← Real.rpow_add ht]
  norm_num

theorem exists_kappa_mul_PBGamma_le {v : E3 → ℝ} (hav : 0 < _root_.BoseGases.a v)
    {κ : ℝ} (hκ : 0 ≤ κ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, 0 < μ → μ * (_root_.BoseGases.a v) ^ 3 ≤ ε₀ →
      κ * Work.BoseFixB1B.PBΓ v μ ≤ 1 / 20 := by
  obtain ⟨δ, hδpos, hδ⟩ :=
    Work.BoseFixB1S.fsXp_mul_log_le_one (K := 20 * max 1 κ) (c := 287 / 2) (M := 0)
      (by positivity) (by norm_num) (le_refl 0)
  refine ⟨min δ 1, lt_min hδpos one_pos, fun μ hμ ht => ?_⟩
  have ht0 : (0 : ℝ) < μ * (_root_.BoseGases.a v) ^ 3 := by positivity
  have htδ : μ * (_root_.BoseGases.a v) ^ 3 ≤ δ := le_trans ht (min_le_left _ _)
  have h' : 20 * max 1 κ * Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) (287 / 2) ≤ 1 := by
    have hh := hδ _ ht0 htδ
    simpa using hh
  have h : max 1 κ * (μ * (_root_.BoseGases.a v) ^ 3) ^ (287 / 646 : ℝ) ≤ 1 / 20 := by
    have h2 : Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) (287 / 2)
        = (μ * (_root_.BoseGases.a v) ^ 3) ^ (287 / 646 : ℝ) := by
      simp only [Work.BoseBox.fsXp]
      norm_num
    rw [h2] at h'
    linarith [h']
  rw [PBGamma_eq_rpow hav μ hμ]
  have hrp : 0 ≤ (μ * (_root_.BoseGases.a v) ^ 3) ^ (287 / 646 : ℝ) :=
    Real.rpow_nonneg ht0.le _
  have hmax : max 1 κ * (μ * (_root_.BoseGases.a v) ^ 3) ^ (287 / 646 : ℝ) ≤ 1 / 20 := by
    linarith [h]
  have hκmax : κ ≤ max 1 κ := le_max_right _ _
  have h1 := mul_le_mul_of_nonneg_right hκmax hrp
  linarith [h1]

theorem exists_Cq_sbCut_cube_le {v : E3 → ℝ} (hav : 0 < _root_.BoseGases.a v) (Cq : ℝ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, 0 < μ → μ * (_root_.BoseGases.a v) ^ 3 ≤ ε₀ →
      Cq * (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) ^ 3 ≤ μ := by
  obtain ⟨δ, hδpos, hδ⟩ :=
    Work.BoseFixB1S.fsXp_mul_log_le_one (K := max 1 Cq) (c := 145) (M := 0)
      (by positivity) (by norm_num) (le_refl 0)
  refine ⟨min δ 1, lt_min hδpos one_pos, fun μ hμ ht => ?_⟩
  have ht0 : (0 : ℝ) < μ * (_root_.BoseGases.a v) ^ 3 := by positivity
  have htδ : μ * (_root_.BoseGases.a v) ^ 3 ≤ δ := le_trans ht (min_le_left _ _)
  have h : max 1 Cq * Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) 145 ≤ 1 := by
    have hh := hδ _ ht0 htδ
    simpa using hh
  have hcut := Work.BoseB1Cube.sbCut_cube_eq_mul (μ := μ) (a := _root_.BoseGases.a v) hμ hav
  have hrp : 0 ≤ Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) 145 :=
    Work.BoseBox.fsXp_nonneg ht0.le
  have hCqmax : Cq ≤ max 1 Cq := le_max_right _ _
  have hCqf : Cq * Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) 145 ≤ 1 :=
    le_trans (mul_le_mul_of_nonneg_right hCqmax hrp) h
  rw [hcut]
  nlinarith [hCqf, hμ.le]

/-! ## 2. The ledger arithmetic -/

theorem swhFlatLedger {Cn μ V W m τ n : ℝ} (hCn : 4 ≤ Cn) (hμ : 0 < μ) (hV : 0 < V)
    (hWnn : 0 ≤ W) (hmnn : 0 ≤ m) (hmW : m ≤ W)
    (hμV : 1000 ≤ μ * V) (hτV : τ * V = n) (hn1 : Cn * μ * V ≤ n) :
    (1 / 18) * μ * τ * W + (15 / 28) * m * (((n + 1) * n) / V ^ 2) + (1 / 16) * μ * τ * W
      ≤ Work.BoseFixB1.a0MainLocBox V μ W n + (1 / 2) * (m / V ^ 2) * (n * n - n) := by
  have hVne : V ≠ 0 := ne_of_gt hV
  have hn : n = τ * V := by rw [← hτV]
  have hn0 : 0 ≤ n := by nlinarith [hn1, hCn, hμ, hV]
  have hτ0 : 0 ≤ τ := by
    have h1 : 0 ≤ τ * V := by rw [hτV]; exact hn0
    exact (mul_nonneg_iff_of_pos_right hV).mp h1
  have hτge : 4 * μ ≤ τ := by
    have h1 : Cn * μ ≤ τ := by
      have h2 : Cn * μ * V ≤ τ * V := by rw [← hn]; exact hn1
      exact (mul_le_mul_iff_of_pos_right hV).mp h2
    nlinarith [h1, hCn, hμ]
  have hlam4 : 4 ≤ τ / μ := by rw [le_div_iff₀ hμ]; linarith
  have hnu0 : (0 : ℝ) < 1 / (μ * V) := by positivity
  have hnu1000 : 1 / (μ * V) ≤ 1 / 1000 := one_div_le_one_div_of_le (by norm_num) hμV
  have hkey : 0 ≤ (3 / 14) * (τ / μ) ^ 2 - (89 / 144) * (τ / μ) - 1 / 4
      - (57 / 28) * (τ / μ) * (1 / (μ * V)) - (1 / (μ * V)) / 2
      - (1 / (μ * V)) ^ 2 / 4 := by
    have h1 : 4 * (τ / μ) ≤ (τ / μ) ^ 2 := by nlinarith [hlam4]
    have h2 : (τ / μ) * (1 / (μ * V)) ≤ (τ / μ) / 1000 := by
      have hh := mul_le_mul_of_nonneg_left hnu1000 (by linarith : (0 : ℝ) ≤ τ / μ)
      linarith [hh]
    have h3 : (1 / (μ * V)) ^ 2 ≤ (1 / (μ * V)) / 1000 := by
      have hh := mul_le_mul_of_nonneg_left hnu1000 hnu0.le
      nlinarith [hh]
    nlinarith [h1, h2, h3]
  have hident : (1 / 4) * (τ - μ) ^ 2 - (1 / 2) * μ ^ 2 - τ / V - μ / (2 * V)
        - 1 / (4 * V ^ 2) - (17 / 144) * μ * τ + (-(1 / 28) * τ ^ 2 - (29 / 28) * τ / V)
      = μ ^ 2 * ((3 / 14) * (τ / μ) ^ 2 - (89 / 144) * (τ / μ) - 1 / 4
          - (57 / 28) * (τ / μ) * (1 / (μ * V)) - (1 / (μ * V)) / 2
          - (1 / (μ * V)) ^ 2 / 4) := by
    field_simp
    ring
  have hmain : 0 ≤ (1 / 4) * (τ - μ) ^ 2 - (1 / 2) * μ ^ 2 - τ / V - μ / (2 * V)
      - 1 / (4 * V ^ 2) - (17 / 144) * μ * τ + (-(1 / 28) * τ ^ 2 - (29 / 28) * τ / V) := by
    have h := mul_nonneg (sq_nonneg μ) hkey
    linarith [hident, h]
  have hmbrk : -(1 / 28) * τ ^ 2 - (29 / 28) * τ / V ≤ 0 := by
    have h : 0 ≤ (1 / 28) * τ ^ 2 + (29 / 28) * τ / V :=
      add_nonneg (mul_nonneg (by norm_num) (sq_nonneg τ))
        (div_nonneg (mul_nonneg (by norm_num) hτ0) hV.le)
    linarith
  have hgoal : (1 / 18) * μ * τ * W + (15 / 28) * m * (τ ^ 2 + τ / V) + (1 / 16) * μ * τ * W
      ≤ (1 / 4) * (τ - μ) ^ 2 * W - (1 / 2) * μ ^ 2 * W - τ * W / V - μ * W / (2 * V)
        - W / (4 * V ^ 2) + (1 / 2) * m * (τ ^ 2 - τ / V) := by
    have hWG : 0 ≤ W * ((1 / 4) * (τ - μ) ^ 2 - (1 / 2) * μ ^ 2 - τ / V - μ / (2 * V)
        - 1 / (4 * V ^ 2) - (17 / 144) * μ * τ + (-(1 / 28) * τ ^ 2 - (29 / 28) * τ / V)) :=
      mul_nonneg hWnn hmain
    have hmW' : 0 ≤ (m - W) * (-(1 / 28) * τ ^ 2 - (29 / 28) * τ / V) :=
      mul_nonneg_of_nonpos_of_nonpos (by linarith) hmbrk
    have hid : W * ((1 / 4) * (τ - μ) ^ 2 - (1 / 2) * μ ^ 2 - τ / V - μ / (2 * V) - 1 / (4 * V ^ 2)
          - (17 / 144) * μ * τ + (-(1 / 28) * τ ^ 2 - (29 / 28) * τ / V))
        + (m - W) * (-(1 / 28) * τ ^ 2 - (29 / 28) * τ / V)
        = ((1 / 4) * (τ - μ) ^ 2 * W - (1 / 2) * μ ^ 2 * W - τ * W / V - μ * W / (2 * V)
            - W / (4 * V ^ 2) + (1 / 2) * m * (τ ^ 2 - τ / V))
          - ((1 / 18) * μ * τ * W + (15 / 28) * m * (τ ^ 2 + τ / V) + (1 / 16) * μ * τ * W) := by
      ring
    linarith [hWG, hmW', hid]
  have e1 : (((τ * V) + 1) * (τ * V)) / V ^ 2 = τ ^ 2 + τ / V := by
    field_simp
  have e2 : (1 / 2) * (m / V ^ 2) * ((τ * V) * (τ * V) - τ * V)
      = (1 / 2) * m * (τ ^ 2 - τ / V) := by
    field_simp
  have e3 : Work.BoseFixB1.a0MainLocBox V μ W (τ * V)
      = (1 / 4) * (τ - μ) ^ 2 * W - (1 / 2) * μ ^ 2 * W - τ * W / V - μ * W / (2 * V)
        - W / (4 * V ^ 2) := by
    rw [Work.BoseFixB1.a0MainLocBox]
    field_simp
    ring
  rw [hn, e1, e2, e3]
  exact hgoal

theorem swhLedgerArith {Cn μ V W S Q m τ n av Cp Cq G χm Pc A2 Spec : ℝ}
    (hCn : 4 ≤ Cn) (hμ : 0 < μ) (hav : 0 ≤ av) (hV : 0 < V)
    (hWnn : 0 ≤ W) (hmnn : 0 ≤ m) (hmW : m ≤ W)
    (hμV : 1000 ≤ μ * V) (hQnn : 0 ≤ Q) (hSnn : 0 ≤ S)
    (hCqnn : 0 ≤ Cq) (hCpnn : 0 ≤ Cp)
    (hSQ : S + Q = n) (hn1 : Cn * μ * V ≤ n) (hn2 : n ≤ 2 * Cn * μ * V)
    (hτV : τ * V = n)
    (hCp : 3 * Cn * W ≤ Cp * av * V)
    (hGχ : (49 / 50) * G * χm ≤ m)
    (hPC : S * S - S ≤ Pc)
    (hport : -((1 / 2) * (1 + 1 / 20) * G * (((n + 1) * n) / V ^ 2) * χm
        + Cq * av * (μ + τ) * Q + (1 / 16) * μ * τ * W) ≤ A2 + Spec) :
    (1 / 18) * μ * τ * W ≤
      Work.BoseFixB1.a0MainLocBox V μ W S + A2 + Spec
        + (1 / 2) * (m / V ^ 2) * Pc
        + (Cq * (1 + 2 * Cn) + Cp) * av * μ * Q := by
  have hn0 : 0 ≤ n := by linarith
  have hτ0 : 0 ≤ τ := by
    have h1 : 0 ≤ τ * V := by rw [hτV]; exact hn0
    exact (mul_nonneg_iff_of_pos_right hV).mp h1
  have hτle : τ ≤ 2 * Cn * μ := by
    have h1 : τ * V ≤ 2 * Cn * μ * V := by rw [hτV]; exact hn2
    exact (mul_le_mul_iff_of_pos_right hV).mp h1
  -- (1) the bounded mass row
  have hfac : 0 ≤ ((n + 1) * n) / V ^ 2 := by
    refine div_nonneg ?_ (by positivity)
    exact mul_nonneg (by linarith) hn0
  have hGχ' : G * χm ≤ (50 / 49) * m := by nlinarith [hGχ]
  have h12 : (1 / 2) * (1 + 1 / 20) * ((50 / 49) * m) = (15 / 28) * m := by ring
  have hmass : (1 / 2) * (1 + 1 / 20) * G * (((n + 1) * n) / V ^ 2) * χm
      ≤ (15 / 28) * m * (((n + 1) * n) / V ^ 2) := by
    have h1 : (1 / 2) * (1 + 1 / 20) * (G * χm) ≤ (15 / 28) * m := by
      have hh := mul_le_mul_of_nonneg_left hGχ' (by norm_num : (0 : ℝ) ≤ (1 / 2) * (1 + 1 / 20))
      linarith [hh, h12]
    have h3 : (1 / 2) * (1 + 1 / 20) * G * (((n + 1) * n) / V ^ 2) * χm
        = ((1 / 2) * (1 + 1 / 20) * (G * χm)) * (((n + 1) * n) / V ^ 2) := by ring
    rw [h3]
    exact mul_le_mul_of_nonneg_right h1 hfac
  -- (2) the credit is dominated by the `Cq(1+2Cn)` slot
  have hcred : Cq * av * (μ + τ) * Q ≤ Cq * (1 + 2 * Cn) * av * μ * Q := by
    have h1 : μ + τ ≤ (1 + 2 * Cn) * μ := by linarith
    have h2 : 0 ≤ Cq * av * Q := mul_nonneg (mul_nonneg hCqnn hav) hQnn
    have hh := mul_le_mul_of_nonneg_left h1 h2
    linarith [hh]
  -- (3) the port row, mass row and credit replaced by their bounds
  have hA2row : -((15 / 28) * m * (((n + 1) * n) / V ^ 2) + Cq * (1 + 2 * Cn) * av * μ * Q
        + (1 / 16) * μ * τ * W) ≤ A2 + Spec := by
    linarith [hport, hmass, hcred]
  -- (4) the monotonicity `H(Q) ≤ H(0) + Cp·a·μ·Q`
  have hdiff : -(Work.BoseFixB1.a0MainLocBox V μ W S) + Work.BoseFixB1.a0MainLocBox V μ W n
        - (1 / 2) * (m / V ^ 2) * (S * S - S) + (1 / 2) * (m / V ^ 2) * (n * n - n)
      = (Q / V) * (W * ((1 / 4) * (n / V + S / V - 2 * μ) - 1 / V))
        + (1 / 2) * (m / V ^ 2) * Q * (n + S - 1) := by
    rw [← hSQ]
    simp only [Work.BoseFixB1.a0MainLocBox]
    field_simp
    ring
  have hQV : 0 ≤ Q / V := div_nonneg hQnn hV.le
  have hnV : n / V = τ := by rw [← hτV]; field_simp
  have hb1 : (1 / 4) * (n / V + S / V - 2 * μ) - 1 / V ≤ τ / 2 := by
    have h1 : S / V ≤ τ := by
      rw [div_le_iff₀ hV]
      linarith [hSQ, hQnn, hτV]
    rw [hnV]
    have h3 : (0 : ℝ) < 1 / V := one_div_pos.mpr hV
    linarith [h1, hμ]
  have hb2 : n + S - 1 ≤ 2 * n := by linarith [hSQ, hQnn]
  have hsq : (Q / V) * (W * ((1 / 4) * (n / V + S / V - 2 * μ) - 1 / V))
      ≤ (Q / V) * (W * (τ / 2)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb1 hWnn) hQV
  have hsq2 : (1 / 2) * (m / V ^ 2) * Q * (n + S - 1) ≤ (1 / 2) * (m / V ^ 2) * Q * (2 * n) := by
    have h1 : 0 ≤ (1 / 2) * (m / V ^ 2) * Q := by
      have : 0 ≤ m / V ^ 2 := div_nonneg hmnn (by positivity)
      positivity
    nlinarith [hb2, h1]
  have hQn : (1 / 2) * (m / V ^ 2) * Q * (2 * n) = (Q / V) * (m * τ) := by
    rw [← hnV]
    field_simp
  have hmono : -(Work.BoseFixB1.a0MainLocBox V μ W S) + Work.BoseFixB1.a0MainLocBox V μ W n
        - (1 / 2) * (m / V ^ 2) * (S * S - S) + (1 / 2) * (m / V ^ 2) * (n * n - n)
      ≤ Cp * av * μ * Q := by
    have h4 : W * (τ / 2) + m * τ ≤ Cp * av * μ * V := by
      have h5 : m * τ ≤ W * τ := mul_le_mul_of_nonneg_right hmW hτ0
      have h7 : 3 * W * τ ≤ 3 * Cn * W * (2 * μ) := by nlinarith [hτle, hWnn, hCn]
      have h8 : 3 * Cn * W * μ ≤ Cp * av * μ * V := by
        have hh := mul_le_mul_of_nonneg_right hCp hμ.le
        linarith [hh]
      linarith [h5, h7, h8]
    have h3 : (Q / V) * (W * (τ / 2)) + (Q / V) * (m * τ) ≤ (Q / V) * (Cp * av * μ * V) := by
      have hh := mul_le_mul_of_nonneg_left h4 hQV
      nlinarith [hh]
    have h9 : (Q / V) * (Cp * av * μ * V) = Cp * av * μ * Q := by
      field_simp
    rw [hdiff]
    linarith [hsq, hsq2, hQn, h3, h9]
  -- (5) the flat case and the ledger
  have hflat := swhFlatLedger (Cn := Cn) (μ := μ) (V := V) (W := W) (m := m) (τ := τ) (n := n)
    hCn hμ hV hWnn hmnn hmW hμV hτV hn1
  have hkey : (1 / 18) * μ * τ * W + (15 / 28) * m * (((n + 1) * n) / V ^ 2)
        + (1 / 16) * μ * τ * W
      ≤ Work.BoseFixB1.a0MainLocBox V μ W S + (1 / 2) * (m / V ^ 2) * (S * S - S)
        + Cp * av * μ * Q := by
    linarith [hflat, hmono]
  have hpairsq : (1 / 2) * (m / V ^ 2) * (S * S - S) ≤ (1 / 2) * (m / V ^ 2) * Pc :=
    mul_le_mul_of_nonneg_left hPC (by positivity)
  linarith [hkey, hA2row, hpairsq]

end Work.BoseB1Cube

namespace Work.BoseB1Cube

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "X" => Submission.BoseGases.X

set_option maxHeartbeats 6400000

theorem swhRegSR2Node_holds {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) :
    Work.BoseB1Cube.swhRegSR2Node v h := by
  intro Cn hCn
  obtain ⟨εq, κ, Cq, hεq, hκ0, hCq0, hport⟩ :=
    Work.BoseB1Cube.cubeBogPortRefinedR3 (v := v) h hv hv1 hvrad hR hv_supp hav
  obtain ⟨εκ, hεκ, hκΓ⟩ := exists_kappa_mul_PBGamma_le (v := v) hav hκ0
  obtain ⟨εc, hεc, hCc⟩ := exists_Cq_sbCut_cube_le (v := v) hav Cq
  obtain ⟨εw, hεw, hWs⟩ := Work.BoseB1Cube.w1MassB_le_sharp (v := v) h hv hv1 hvrad hR hv_supp hav
      (δ := 1 / 50) (by norm_num)
  obtain ⟨εr, hεr, hregime⟩ := Work.BoseFixB1.regime_sideAt_ge (v := v) hav hR
  have hCn0 : 0 ≤ Cn := by linarith
  have hav0 : 0 ≤ _root_.BoseGases.a v := le_of_lt hav
  set C1 : ℝ := (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay Work.BoseBox.mValue) ^ 2 with hC1def
  have hC10 : 0 ≤ C1 := by rw [hC1def]; positivity
  set Cw : ℝ := (1 + 1 / 50) * (8 * Real.pi) * C1 with hCwdef
  have hCw0 : 0 ≤ Cw := by rw [hCwdef]; positivity
  set Cp : ℝ := 3 * Cn * Cw with hCpdef
  have hCp0 : 0 ≤ Cp := by rw [hCpdef]; positivity
  set ε0 : ℝ := min (min (min εq εκ) (min εc εw)) (min εr 1) with hε0def
  have hε0pos : 0 < ε0 := by
    rw [hε0def]
    exact lt_min (lt_min (lt_min hεq hεκ) (lt_min hεc hεw)) (lt_min hεr one_pos)
  have hε0q : ε0 ≤ εq := le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_left _ _))
  have hε0κ : ε0 ≤ εκ := le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _))
  have hε0c : ε0 ≤ εc := le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hε0w : ε0 ≤ εw := le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have hε0r : ε0 ≤ εr := le_trans (min_le_right _ _) (min_le_left _ _)
  refine ⟨ε0, Cq * (1 + 2 * Cn) + Cp, hε0pos, ?_, ?_⟩
  · have h1 : (0 : ℝ) ≤ Cq * (1 + 2 * Cn) := mul_nonneg hCq0 (by linarith)
    linarith [h1, hCp0]
  · intro μ hAdm n Ψ u hu hΨc hsupp hnorm hn1 hn2 hReg
    have hμ : 0 < μ := hAdm.1
    have htε : μ * (_root_.BoseGases.a v) ^ 3 ≤ ε0 := hAdm.2.1
    have hAdmq : Work.BoseBoxFix.Adm v εq μ := Work.BoseFixB1.Adm.mono hAdm hε0q
    have hAdmw : Work.BoseBoxFix.Adm v εw μ := Work.BoseFixB1.Adm.mono hAdm hε0w
    have hAdmr : Work.BoseBoxFix.Adm v εr μ := Work.BoseFixB1.Adm.mono hAdm hε0r
    have hℓ : 0 < Work.BoseFixB1.bSide v μ := Work.BoseFixB1.adm_ell_pos hAdm
    have hd : 0 < Work.BoseFixB1.bD v μ := Work.BoseFixB1.adm_d_pos hAdm
    have hVpos : 0 < Work.BoseFixB1.bV v μ u := Work.BoseFixB1.boxMass_pos_of_goodSet hℓ hd hμ hu
    have hVne : Work.BoseFixB1.bV v μ u ≠ 0 := ne_of_gt hVpos
    have hμ3 : 1000 ≤ μ * Work.BoseFixB1.bV v μ u := hReg.2.2
    have hWnn : 0 ≤ Work.BoseFixB1.bW v h μ u :=
      Work.BoseFixB1.w1MassB_nonneg h hv hvrad hR hv_supp hℓ hd u
    have hMv : 1 ≤ Work.BoseFixB1.bM v μ := by
      show 1 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
      rw [Work.BoseFixB1.M_eq_mValue]; norm_num [Work.BoseBox.mValue]
    have hAmeas : MeasurableSet (Work.BoseFixB1.bA v μ u) :=
      Work.SmallBoxSliding.measurableSet_dlBox (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) u
    have hVeq : Work.BoseFixB1.bV v μ u
        = (MeasureTheory.volume (Work.BoseFixB1.bA v μ u)).toReal :=
      Work.SmallBoxSliding.boxMass_eq_measureReal (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) u
    have hAc : Work.BoseFixB1.bA v μ u ⊆ Submission.BoseGases.acube (Work.BoseFixB1.bSide v μ) :=
      Work.SmallBoxSliding.dlBox_subset_acube (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) u
    have hΨc' : Continuous Ψ := hΨc.continuous
    -- the component notation
    have hSnn : 0 ≤ Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
        (Work.BoseFixB1.bA v μ u) Ψ := by
      rw [Work.BoseFixB1S.boxFlatCount]
      exact Finset.sum_nonneg fun i _ => integral_nonneg fun x => sq_nonneg _
    have hQnn : 0 ≤ Work.BoseFixB1S.boxQCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
        (Work.BoseFixB1.bA v μ u) Ψ := Work.BoseFixB1S.boxQCount_nonneg _ _ _ _
    have hχmnn : 0 ≤ Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
        (Work.BoseFixB1.bD v μ) u := Work.SmallBoxSliding.chiMass_nonneg _ _ _ _
    have hGnn : 0 ≤ Submission.BoseGases.g0w0Mass h :=
      Work.BoseB1Cube.g0w0Mass_nonneg (v := v) hR hv hvrad hv_supp h
    -- `M₂ ≥ W`
    have hWbridge : Work.BoseFixB1.bM1 v h μ u = Work.BoseFixB1.bW v h μ u := by
      simp only [Work.BoseFixB1.bM1, Work.BoseFixB1.bW, Work.BoseFixB1.bSide, Work.BoseFixB1.bD,
        Work.BoseFixB1.bA, Work.BoseFixB1.bM, Work.BoseFixB1S.mfW]
      exact (Work.BoseFixB1S.mfW_eq_mfM1 (v := v) (h := h) (μ := μ) (u := u) hMv hℓ hd).symm
    obtain ⟨hRd, hRχ⟩ := hregime μ hμ (le_trans htε hε0r)
    have hmnn : 0 ≤ Work.BoseFixB1.bM2 v h μ u - Work.BoseFixB1.bW v h μ u := by
      have h0 := Work.BoseFixB1S.boxM2_sub_boxM1_nonneg_slidingB1 (v := v) (R := R) hv_supp hR hv
        hvrad hv1 h hav hMv hℓ hd hRd hRχ u
      rw [← hWbridge]
      simpa only [Work.BoseFixB1.bM2, Work.BoseFixB1.bM1, Work.BoseFixB1.bV, Work.BoseFixB1.bA,
        Work.BoseFixB1.bM, Work.BoseFixB1.bSide, Work.BoseFixB1.bD] using h0
    have hmW : Work.BoseFixB1.bM2 v h μ u - Work.BoseFixB1.bW v h μ u ≤ Work.BoseFixB1.bW v h μ u := by
      have h2 := Work.BoseFixB1.boxM2_le_two_mul_boxM1 (v := v) (R0 := R) hv_supp hR hv hvrad hv1 h
        hMv hℓ hd hRd hRχ u
      rw [← hWbridge]
      simp only [Work.BoseFixB1.bM2, Work.BoseFixB1.bM1, Work.BoseFixB1.bV, Work.BoseFixB1.bA,
        Work.BoseFixB1.bM, Work.BoseFixB1.bSide, Work.BoseFixB1.bD] at h2 ⊢
      linarith [h2]
    -- `W ≤ Cw·(a v)·|B|`
    have hWb : Work.BoseFixB1.bW v h μ u ≤ Cw * (_root_.BoseGases.a v) * Work.BoseFixB1.bV v μ u := by
      have h1 : Work.BoseFixB1.bW v h μ u ≤ (1 + 1 / 50) * (8 * Real.pi * (_root_.BoseGases.a v))
          * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bD v μ) u := by
        simpa only [Work.BoseFixB1.bW, Work.BoseFixB1.bM, Work.BoseFixB1.bSide, Work.BoseFixB1.bD,
          Work.BoseFixB1.pM, Work.BoseFixB1.pL, Work.BoseFixB1.pD] using hWs μ hAdmw u
      have h2 : Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
          (Work.BoseFixB1.bD v μ) u ≤ C1 * Work.BoseFixB1.bV v μ u := by
        have hh := Work.BoseFixB1S.chiMass_le_const_mul_boxMass (M := Work.BoseFixB1.bM v μ) hMv hℓ hd u
        have hMeq : Work.BoseFixB1.bM v μ = Work.BoseBox.mValue := Work.BoseFixB1.M_eq_mValue μ (_root_.BoseGases.a v)
        rw [hC1def]
        rw [← hMeq]
        simpa only [Work.BoseFixB1.bV] using hh
      rw [hCwdef]
      have h3 : (1 + 1 / 50) * (8 * Real.pi * (_root_.BoseGases.a v)) * (C1 * Work.BoseFixB1.bV v μ u)
          = (1 + 1 / 50) * (8 * Real.pi) * C1 * ((_root_.BoseGases.a v) * Work.BoseFixB1.bV v μ u) := by ring
      have h4 : 0 ≤ (1 + 1 / 50) * (8 * Real.pi * (_root_.BoseGases.a v)) := by positivity
      have h5 := mul_le_mul_of_nonneg_left h2 h4
      linarith [h1, h5, h3]
    -- `3Cn·W ≤ Cp·a·|B|`
    have hCp' : 3 * Cn * Work.BoseFixB1.bW v h μ u ≤ Cp * (_root_.BoseGases.a v) * Work.BoseFixB1.bV v μ u := by
      have h1 : 3 * Cn * Work.BoseFixB1.bW v h μ u
          ≤ 3 * Cn * (Cw * (_root_.BoseGases.a v) * Work.BoseFixB1.bV v μ u) := by
        have hh := mul_le_mul_of_nonneg_left hWb (by linarith : (0 : ℝ) ≤ 3 * Cn)
        linarith [hh]
      have h2 : 3 * Cn * (Cw * (_root_.BoseGases.a v) * Work.BoseFixB1.bV v μ u)
          = Cp * (_root_.BoseGases.a v) * Work.BoseFixB1.bV v μ u := by
        rw [hCpdef]
        ring
      linarith [h1, h2]
    -- the count split
    have hsplit := Work.BoseFixB1S.b1sCountSplit (N := n) hℓ hVpos hAmeas hVeq hAc (Φ := Ψ) hΨc' hsupp
    have hSQ : Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
          (Work.BoseFixB1.bA v μ u) Ψ
        + Work.BoseFixB1S.boxQCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
          (Work.BoseFixB1.bA v μ u) Ψ = (n : ℝ) := by
      rw [hsplit, hnorm, mul_one]
    -- the pair square
    have hPC : Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bA v μ u) Ψ * Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1.bV v μ u)
            (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u) Ψ
          - Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bA v μ u) Ψ
        ≤ Work.BoseFixB1S.boxPairCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bA v μ u) Ψ := by
      have hj := Work.BoseFixB1S.boxFlatSqJensen (N := n) hℓ hVpos hAmeas hVeq hAc (Φ := Ψ) hΨc'
      rw [hnorm] at hj
      linarith [hj]
    -- the port
    have hn1' : (1 : ℕ) ≤ n := by
      have h2 : (4 : ℝ) * μ * Work.BoseFixB1.bV v μ u ≤ (n : ℝ) := by nlinarith [hn1, hCn]
      have h1 : (1 : ℝ) ≤ (n : ℝ) := by nlinarith [h2, hμ3]
      exact_mod_cast h1
    have hq := hport μ hAdmq n Ψ u hu hn1' hΨc hnorm
    have htκ : μ * (_root_.BoseGases.a v) ^ 3 ≤ εκ := le_trans htε hε0κ
    have htc : μ * (_root_.BoseGases.a v) ^ 3 ≤ εc := le_trans htε hε0c
    have hkap : κ * Work.BoseFixB1B.PBΓ v μ ≤ 1 / 20 := hκΓ μ hμ htκ
    -- the mass row
    have hmassrow : (1 / 2) * (1 + κ * Work.BoseFixB1B.PBΓ v μ) * Submission.BoseGases.g0w0Mass h
          * ((((n : ℝ) + 1) * (n : ℝ)) / (Work.BoseFixB1.bV v μ u) ^ 2)
          * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bD v μ) u
        ≤ (1 / 2) * (1 + 1 / 20) * Submission.BoseGases.g0w0Mass h
          * ((((n : ℝ) + 1) * (n : ℝ)) / (Work.BoseFixB1.bV v μ u) ^ 2)
          * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bD v μ) u := by
      have hX : 0 ≤ (1 / 2) * Submission.BoseGases.g0w0Mass h
          * ((((n : ℝ) + 1) * (n : ℝ)) / (Work.BoseFixB1.bV v μ u) ^ 2)
          * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bD v μ) u := by
        have h1 : 0 ≤ (((n : ℝ) + 1) * (n : ℝ)) / (Work.BoseFixB1.bV v μ u) ^ 2 := by
          refine div_nonneg ?_ (by positivity)
          exact mul_nonneg (by linarith) (by linarith)
        exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hGnn) h1) hχmnn
      have h2 : (1 : ℝ) + κ * Work.BoseFixB1B.PBΓ v μ ≤ 1 + 1 / 20 := by linarith
      have h3 := mul_le_mul_of_nonneg_right h2 hX
      nlinarith [h3]
    -- the band row
    have hband : Cq * (_root_.BoseGases.a v) * (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) ^ 3
          * ((n : ℝ) / Work.BoseFixB1.bV v μ u)
          * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bD v μ) u
        ≤ (1 / 16) * μ * ((n : ℝ) / Work.BoseFixB1.bV v μ u) * Work.BoseFixB1.bW v h μ u := by
      have h1 : Cq * (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) ^ 3 ≤ μ := hCc μ hμ htc
      have h2 : (_root_.BoseGases.a v) * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ)
          (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) u
          ≤ (50 / (49 * 8 * Real.pi)) * Work.BoseFixB1.bW v h μ u := by
        have hh := hReg.1
        have hc : (0 : ℝ) < (49 / 50) * (8 * Real.pi) := by positivity
        have h3 : ((_root_.BoseGases.a v) * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ)
            (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) u) * ((49 / 50) * (8 * Real.pi))
            ≤ Work.BoseFixB1.bW v h μ u := by linarith [hh]
        have h4 := (le_div_iff₀ hc).mpr h3
        have h5 : Work.BoseFixB1.bW v h μ u / ((49 / 50) * (8 * Real.pi))
            = (50 / (49 * 8 * Real.pi)) * Work.BoseFixB1.bW v h μ u := by
          field_simp
        linarith [h4, h5]
      have h3 : 0 ≤ (_root_.BoseGases.a v) * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ)
          (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) u := mul_nonneg hav0 hχmnn
      have h5 : 0 ≤ ((n : ℝ) / Work.BoseFixB1.bV v μ u) :=
        div_nonneg (by nlinarith [hn1, hCn, hμ, hVpos]) hVpos.le
      have h4 := mul_le_mul h1 h2 h3 hμ.le
      have h6 := mul_le_mul_of_nonneg_right h4 h5
      have h8 : μ * ((50 / (49 * 8 * Real.pi)) * Work.BoseFixB1.bW v h μ u)
            * ((n : ℝ) / Work.BoseFixB1.bV v μ u)
          ≤ (1 / 16) * μ * ((n : ℝ) / Work.BoseFixB1.bV v μ u) * Work.BoseFixB1.bW v h μ u := by
        have hk : (50 / (49 * 8 * Real.pi)) ≤ 1 / 16 := by
          rw [div_le_iff₀ (by positivity)]
          nlinarith [Real.pi_gt_three]
        have hμτW : 0 ≤ μ * ((n : ℝ) / Work.BoseFixB1.bV v μ u) * Work.BoseFixB1.bW v h μ u :=
          mul_nonneg (mul_nonneg hμ.le h5) hWnn
        have hh := mul_le_mul_of_nonneg_right hk hμτW
        linarith [hh]
      have h9 : Cq * (_root_.BoseGases.a v) * (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) ^ 3
            * ((n : ℝ) / Work.BoseFixB1.bV v μ u)
            * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                (Work.BoseFixB1.bD v μ) u
          = (Cq * (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) ^ 3)
            * ((_root_.BoseGases.a v) * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ)
                (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) u)
            * ((n : ℝ) / Work.BoseFixB1.bV v μ u) := by ring
      linarith [h6, h8, h9]
    have hport' : -((1 / 2) * (1 + 1 / 20) * Submission.BoseGases.g0w0Mass h
          * ((((n : ℝ) + 1) * (n : ℝ)) / (Work.BoseFixB1.bV v μ u) ^ 2)
          * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bD v μ) u
        + Cq * (_root_.BoseGases.a v) * (μ + (n : ℝ) / Work.BoseFixB1.bV v μ u)
          * Work.BoseFixB1.bQ v μ Ψ u
        + (1 / 16) * μ * ((n : ℝ) / Work.BoseFixB1.bV v μ u) * Work.BoseFixB1.bW v h μ u)
        ≤ Work.BoseFixB1.bA2 v h μ Ψ u + Work.BoseFixB1S.bSpectralCube v μ Ψ u := by
      have hbQ : Work.UBBInputs8.cnPlusBoxInd (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u)
          (Work.BoseFixB1.bV v μ u) Ψ = Work.BoseFixB1.bQ v μ Ψ u := rfl
      rw [hbQ] at hq
      linarith [hq, hmassrow, hband]
    -- the ledger
    have hτV : ((n : ℝ) / Work.BoseFixB1.bV v μ u) * Work.BoseFixB1.bV v μ u = (n : ℝ) := by
      field_simp
    have hGχ : (49 / 50) * Submission.BoseGases.g0w0Mass h
        * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bD v μ) u
        ≤ Work.BoseFixB1.bM2 v h μ u - Work.BoseFixB1.bW v h μ u := hReg.2.1
    have hmain := swhLedgerArith (Cn := Cn) (μ := μ) (V := Work.BoseFixB1.bV v μ u)
      (W := Work.BoseFixB1.bW v h μ u)
      (S := Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
        (Work.BoseFixB1.bA v μ u) Ψ)
      (Q := Work.BoseFixB1S.boxQCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
        (Work.BoseFixB1.bA v μ u) Ψ)
      (m := Work.BoseFixB1.bM2 v h μ u - Work.BoseFixB1.bW v h μ u)
      (τ := (n : ℝ) / Work.BoseFixB1.bV v μ u) (n := (n : ℝ)) (av := _root_.BoseGases.a v)
      (Cp := Cp) (Cq := Cq) (G := Submission.BoseGases.g0w0Mass h)
      (χm := Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
        (Work.BoseFixB1.bD v μ) u)
      (Pc := Work.BoseFixB1S.boxPairCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
        (Work.BoseFixB1.bA v μ u) Ψ)
      (A2 := Work.BoseFixB1.bA2 v h μ Ψ u)
      (Spec := Work.BoseFixB1S.bSpectralCube v μ Ψ u)
      hCn hμ hav0 hVpos hWnn hmnn hmW
      hμ3 hQnn hSnn hCq0 hCp0 hSQ hn1 hn2 hτV hCp' hGχ hPC hport'
    rw [Work.BoseB1Cube.swhDem, Work.BoseB1Cube.swhSR2Rhs]
    exact hmain

end Work.BoseB1Cube
