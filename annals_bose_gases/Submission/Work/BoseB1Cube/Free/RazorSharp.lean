import ChallengeDeps
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB1Cube.ConeC.BoseFixB1S_crossJointSteps
import Submission.Work.BoseB1Cube.Free.Props
import Submission.Work.BoseB1Cube.Free.RazorSharpDefs
import Submission.Work.BoseFixB1.Up.PairRowOper
import Submission.Work.BoseFixB1.boxMass_pos_of_goodSet
import Submission.Work.BoseFixB1S.PerBoxGapAbsorbB1
import Submission.Work.BoseFixB1S.boxFlatCount_le_NB1
import Submission.Work.BoseFixB1S.fibSum_le_manifest
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB1Cube.Free.RazorSharp` — **`RazorSharpF` ⟹ the node's small-window row**

Holder: `Submission/Work/BoseB1Cube/nomRowLinWindowRow.lean` (session 11).

This module proves the two things that make the sharp razor `RazorSharpF`
(`Free/RazorSharpDefs.lean`) a *usable* instrument for this node:

* **`sbWordCube_eq_pair_cube`** — the identity (★)
  `sbWordCube = bGapCoeff·n₊ + cubeSpectral + pairSum − μ·fibSum` in the holder-free `Free` cone
  (it is what `(★)` is in the holder: `sbWordCube = sbKinCube + sbPot` by definition and
  `sbPot = pairSum − μ·fibSum` by the PROVED `Work.BoseFixB1.sbPot_split`);
* **`razorSharpF_imp_smallWinPropF`** — **(RAZOR) ⟹ `SmallWinPropF`**, i.e. the razor closes the
  node's *small-window* case **unconditionally**: no `n₊`-threshold, no `FlatArm37`, no
  pair-deadness, no corner `μ|B| < 32`, no box-geometry restriction.

## The deduction (all inputs PROVED except the razor itself)

With (★), the node's clause at a normalised in-box state is

    (NODE)   (1/18)·μ·τ·W + μ·fibSum  ≤  bGapCoeff·n₊ + cubeSpectral + pairSum ,   τ = n/|B(u)| .

The three rows of the **manifest fibre bound** (`Work.BoseFixB1S.fibSum_le_manifest`)

    fibSum ≤ (M₁/|B|)·S + Cm·(a v)·(√(n₊·(M₁/|B|)·S) + n₊) ,     S = boxFlatCount ≤ n
                                                                  (`boxFlatCount_le_NB1`),

are handled as follows (`M₁ = boxM1 = w1MassB = W`, the PROVED `boxM1_eq_PBW`):

1. the flat row: `(W/|B|)·S ≤ τ·W`, which together with the demand `(1/18)μτW` is exactly the
   `(19/18)μτW` that `RazorNom`'s left-hand side over-covers by the surplus
   `Wμ²κ(λ)`, `κ(λ) = ¼λ² − 5λ/9 − ¼ ≥ 1.5277` at `λ = 4` (`Work.BoseB1Cube.razorCoversDemandFibre`);
2. the `√`-row: Young at the *gate's own scale*, `μ·Cm a√(n₊τW) ≤ (Kg/4)μa·n₊ + μCm²aτW/Kg`, the
   first term paid by the gate `bGapCoeff·n₊ ≥ Kg·(a v)·μ·n₊` (`PerBoxGapAbsorbB1`, **any** fixed
   `Kg`) and the second by the surplus (`Kg ≥ 4Cm²(a v)`, together with `λ/κ(λ) ≤ 4` for `λ ≥ 4`);
3. the `∝ n₊` row and the razor's own `C₀·(a v)·(μ+τ)·n₊` row: also gate-paid, since
   `Kg ≥ max (4Cm) (4C₀(1+2Cn))` and the count window gives `τ ≤ 2Cn·μ`.

All three conditions on `Kg` are **fixed constants** (depending only on `v`, `Cn`), so the gate's
`ε₀` absorbs them.  The pure-real content is `razorArithCore` below.

## Why this matters

`RazorSharpF` is therefore a *strictly stronger but cleaner* sufficient statement than the chapter's
`SmallWinHolePD`: it needs no dichotomy at all, and — unlike `RazorNom`/`HoleRow`, whose
state-independent credit row `C(μ²(a v)Γχ + μ(a v))·I` forces `C ≤ 1.53` and is therefore
unpayable inside an error-free row — it is the *sharp* FS form.  See
`FINDING_nomRowLinWindowRow_session11.md`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseB1Cube

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB Work.BoseFixB1
  Work.SmallBoxSliding

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "X" => Submission.BoseGases.X

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-- **The `boxM1 = bW` bridge**, re-proved here in a cone that is compatible with the holder
`Submission/Work/BoseB1Cube/nomRowLinWindowRow.lean` (the original `Work.BoseFixB1S.boxM1_eq_PBW`
lives in `condensedArmForWindow`, whose cone carries `Submission.Work.BoseFixB1S.boxMuSumAgree` —
already clashing with the holder's `boxComp_sum_eq`).  The proof is the same: `boxM1` at a kernel
supported in the sliding box is the global nested integral (`boxM1_eq_nested`), which is
`w1MassB`. -/
theorem boxM1_eq_bW {v : E3 → ℝ} (h : Work.UBB.ScatSol v) {μ : ℝ}
    (hM : 1 ≤ Work.BoseFixB1.bM v μ) (hℓ : 0 < Work.BoseFixB1.bSide v μ)
    (hd : 0 < Work.BoseFixB1.bD v μ) (u : E3) :
    Work.BoseFixB1S.boxM1 (Work.BoseFixB1.bSide v μ)
        (Submission.BoseGases.dlBox (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) u)
        (Submission.BoseGases.wSmall1Pair h (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
          (Work.BoseFixB1.bD v μ) u)
      = Work.BoseFixB1.bW v h μ u := by
  rw [Work.BoseFixB1.bW, Work.BoseFixB1.w1MassB]
  refine Work.BoseFixB1S.boxM1_eq_nested u ?_
  intro x y hxy
  simpa only [Submission.BoseGases.wSmall1Pair] using
    Work.BoseFixB1S.wSmallPair_eq_zero_of_notMem_dlBox hM hℓ hd u
      (v := Submission.BoseGases.g0 v h) hxy

/-- **⭐ (★) in the holder-free cone** — the pair/fibre decomposition of the matched word, with the
`cubeSpectral` spelling of the spectral slot (so that no `BoseFixB1S.boxBogPortSliding`-like
module is needed).  Definitional, plus the PROVED `Work.BoseFixB1.sbPot_split`. -/
theorem sbWordCube_eq_pair_cube {v : E3 → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    {εr μ : ℝ} (hadmr : Work.BoseBoxFix.Adm v εr μ)
    {n : ℕ} {Ψ : X n → ℝ} (hΨc : Continuous Ψ) (u : E3)
    (hR16 : R ≤ Work.BoseFixB1.bSide v μ * Work.BoseFixB1.bD v μ / 16)
    (hRχ : R ≤ Work.BoseFixB1.bSide v μ * Submission.BoseGases.chiR0) :
    Work.BoseFixB1B.sbWordCube v h μ u Ψ
      = Work.BoseFixB1.bGapCoeff v μ * Work.BoseFixB1.bQ v μ Ψ u
        + Work.BoseFixB1B.cubeSpectral v μ Ψ u
        + Work.BoseFixB1.pairSum v (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bD v μ) u Ψ
        - μ * Work.BoseFixB1.fibSum h (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bD v μ) u Ψ := by
  rw [Work.BoseFixB1B.sbWordCube, Work.BoseFixB1B.sbKinCube,
    Work.BoseFixB1.sbPot_split (v := v) (h := h) (R := R) hv_supp hR hv hvrad hv1 hadmr hΨc u
      (by simpa only [Work.BoseFixB1.bSide, Work.BoseFixB1.bD] using hR16)
      (by simpa only [Work.BoseFixB1.bSide] using hRχ)]
  simp only [Work.BoseFixB1.bQ, Work.UBBInputs8.cnPlusBoxInd, Work.BoseFixB1S.boxQCount,
    Work.BoseFixB1.bSide, Work.BoseFixB1.bD, Work.BoseFixB1.bM, Work.BoseFixB1.bA,
    Work.BoseFixB1.bV]
  ring

/-- **The pure-real core of the razor route.**  The rows the manifest fibre bound produces
(the `∝ Q` row, the razor's own `C₀·(a v)·(μ+τ)·Q` row and the `√` row) are paid by the gate column
`bg·Q ≥ Kg·μ·a·Q` and by the razor's surplus `W·μ²·kpar`; the flat fibre row is buried in the
surplus.  Every constant condition on `Kg` is *fixed* in `v` and `Cn`. -/
theorem razorArithCore {μ τ S n V W Q cs pp fb bg a Cm C₀ Kg Cn E kpar : ℝ}
    (hμ : 0 < μ) (ha : 0 < a) (hV : 0 < V) (hW0 : 0 ≤ W) (hQ0 : 0 ≤ Q)
    (hSle : S ≤ n) (hVn : n = τ * V) (hτ0 : 0 ≤ τ) (hτm : τ ≤ 2 * Cn * μ) (hlam4 : 4 ≤ τ / μ)
    (hCm0 : 0 ≤ Cm) (hC₀0 : 0 ≤ C₀)
    (hkpar : kpar = (1 / 4) * (τ / μ) ^ 2 - (5 / 9) * (τ / μ) - (1 / 4))
    (hKg1 : 4 * Cm ≤ Kg) (hKg2 : 4 * C₀ * (1 + 2 * Cn) ≤ Kg) (hKg3 : 4 * Cm ^ 2 * a ≤ Kg)
    (hgate : Kg * μ * a ≤ bg)
    (hfb : fb ≤ (W / V) * S + Cm * a * (Real.sqrt (Q * ((W / V) * S)) + Q))
    (hE : E ≤ cs + pp + C₀ * a * (μ + τ) * Q)
    (hE2 : (19 / 18) * μ * τ * W + W * μ ^ 2 * kpar ≤ E) :
    (1 / 18) * μ * τ * W + μ * fb ≤ bg * Q + cs + pp := by
  -- τ > 0 and the fibre row at τ
  have hτpos : 0 < τ := by
    have h := (le_div_iff₀ hμ).mp hlam4
    linarith
  have hQτW : 0 ≤ Q * (τ * W) := mul_nonneg hQ0 (mul_nonneg hτ0 hW0)
  -- ## 1. the flat fibre row
  have hWS : (W / V) * S ≤ τ * W := by
    have h1 : (W / V) * S ≤ (W / V) * n := mul_le_mul_of_nonneg_left hSle (div_nonneg hW0 hV.le)
    rw [hVn] at h1
    have h2 : (W / V) * (τ * V) = τ * W := by field_simp
    linarith [h1, h2]
  -- ## 2. the `√` row: monotonicity in the `S` slot
  have hSmono : Real.sqrt (Q * ((W / V) * S)) ≤ Real.sqrt (Q * (τ * W)) :=
    Real.sqrt_le_sqrt (by nlinarith [hQ0, hWS])
  have hstep2 : μ * fb ≤ μ * (τ * W + Cm * a * (Real.sqrt (Q * (τ * W)) + Q)) := by
    have hA : fb ≤ (W / V) * S + Cm * a * (Real.sqrt (Q * ((W / V) * S)) + Q) := hfb
    have hB : (W / V) * S + Cm * a * (Real.sqrt (Q * ((W / V) * S)) + Q)
        ≤ τ * W + Cm * a * (Real.sqrt (Q * (τ * W)) + Q) := by
      have := mul_le_mul_of_nonneg_left hSmono (mul_nonneg hCm0 ha.le)
      linarith [hWS, this]
    calc μ * fb ≤ μ * ((W / V) * S + Cm * a * (Real.sqrt (Q * ((W / V) * S)) + Q)) :=
          mul_le_mul_of_nonneg_left hA hμ.le
      _ ≤ μ * (τ * W + Cm * a * (Real.sqrt (Q * (τ * W)) + Q)) :=
          mul_le_mul_of_nonneg_left hB hμ.le
  -- ## 3. the row budget: the three rows against the gate and the surplus
  have hkpar0 : 0 < kpar := by
    rw [hkpar]
    nlinarith [hlam4, sq_nonneg (τ / μ - 4)]
  have hlamk4 : (τ / μ) / kpar ≤ 4 := by
    rw [div_le_iff₀ hkpar0, hkpar]
    nlinarith [hlam4, sq_nonneg (τ / μ - 4)]
  have hKg3' : Cm ^ 2 * a * (τ / μ) ≤ Kg * kpar := by
    have h1 : τ / μ ≤ 4 * kpar := by
      have h := (div_le_iff₀ hkpar0).mp hlamk4
      linarith
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0:ℝ) ≤ Cm ^ 2 * a)
    nlinarith [h2, hKg3, hkpar0]
  -- the `√` row, by Young at the gate's own scale
  have hKg0 : 0 ≤ Kg := le_trans (by positivity : (0:ℝ) ≤ 4 * Cm ^ 2 * a) hKg3
  have hsqrt : μ * (Cm * a * Real.sqrt (Q * (τ * W)))
      ≤ (Kg / 4) * μ * a * Q + W * μ ^ 2 * kpar := by
    -- `Cm·√(QτW) ≤ (Kg/4)·Q + Cm²τW/Kg`
    have hmain : Cm * Real.sqrt (Q * (τ * W)) ≤ (Kg / 4) * Q + Cm ^ 2 * τ * W / Kg := by
      rcases eq_or_lt_of_le hKg0 with hKgz | hKgpos
      · -- `Kg = 0` forces `Cm = 0`
        have hCmz : Cm = 0 := by
          have h1 : Cm ^ 2 * a = 0 := by
            have h := hKg3; rw [← hKgz] at h; nlinarith [h, ha]
          nlinarith [h1, ha]
        have hKgz' : Kg = 0 := hKgz.symm
        rw [hCmz, hKgz']; norm_num
      · -- Young: `Kg·Cm·√(QτW) ≤ Kg²Q/4 + Cm²τW` (division-free)
        have hkey : Kg * (Cm * Real.sqrt (Q * (τ * W)))
            ≤ Kg * ((Kg / 4) * Q) + Cm ^ 2 * τ * W := by
          have hsq : (Kg * (Cm * Real.sqrt (Q * (τ * W)))) ^ 2
              ≤ (Kg * ((Kg / 4) * Q) + Cm ^ 2 * τ * W) ^ 2 := by
            rw [mul_pow, mul_pow, Real.sq_sqrt hQτW]
            nlinarith [sq_nonneg (Kg * ((Kg / 4) * Q) - Cm ^ 2 * τ * W)]
          have h1 : 0 ≤ Kg * (Cm * Real.sqrt (Q * (τ * W))) := by positivity
          have h2 : 0 ≤ Kg * ((Kg / 4) * Q) + Cm ^ 2 * τ * W := by positivity
          have := sq_le_sq.mp hsq
          rwa [abs_of_nonneg h1, abs_of_nonneg h2] at this
        have hcleared : (Cm * Real.sqrt (Q * (τ * W))) * Kg
            ≤ ((Kg / 4) * Q + Cm ^ 2 * τ * W / Kg) * Kg := by
          have hred : ((Kg / 4) * Q + Cm ^ 2 * τ * W / Kg) * Kg
              = Kg * ((Kg / 4) * Q) + Cm ^ 2 * τ * W := by
            field_simp
          rw [hred]
          linarith [hkey]
        exact le_of_mul_le_mul_right hcleared hKgpos
    -- multiply by `μ·a` and absorb the second term in the razor's surplus
    have hmul := mul_le_mul_of_nonneg_left hmain (mul_nonneg hμ.le ha.le)
    have hlast : μ * a * (Cm ^ 2 * τ * W / Kg) ≤ W * μ ^ 2 * kpar := by
      rcases eq_or_lt_of_le hKg0 with hKgz | hKgpos
      · have hCmz : Cm = 0 := by
          have h1 : Cm ^ 2 * a = 0 := by
            have h := hKg3; rw [← hKgz] at h; nlinarith [h, ha]
          nlinarith [h1, ha]
        have hKgz' : Kg = 0 := hKgz.symm
        rw [hCmz, hKgz']
        have hz : μ * a * (0 ^ 2 * τ * W / 0) = 0 := by simp
        rw [hz]
        exact mul_nonneg (mul_nonneg hW0 (by positivity)) hkpar0.le
      · have h2 : Cm ^ 2 * a * τ ≤ Kg * μ * kpar := by
          have h2' := mul_le_mul_of_nonneg_right hKg3' hμ.le
          have h3 : Cm ^ 2 * a * (τ / μ) * μ = Cm ^ 2 * a * τ := by
            field_simp
          linarith [h2', h3]
        have hmul2 : μ * a * (Cm ^ 2 * τ * W) ≤ W * μ ^ 2 * kpar * Kg := by
          have h3 := mul_le_mul_of_nonneg_left h2 (mul_nonneg hμ.le hW0)
          nlinarith [h3]
        have hrew : μ * a * (Cm ^ 2 * τ * W / Kg) = μ * a * (Cm ^ 2 * τ * W) / Kg := by ring
        rw [hrew, div_le_iff₀ hKgpos]
        linarith [hmul2]
    calc μ * (Cm * a * Real.sqrt (Q * (τ * W)))
        = (μ * a) * (Cm * Real.sqrt (Q * (τ * W))) := by ring
      _ ≤ (μ * a) * ((Kg / 4) * Q + Cm ^ 2 * τ * W / Kg) := hmul
      _ ≤ (Kg / 4) * μ * a * Q + W * μ ^ 2 * kpar := by linarith [hlast]
  -- the `∝ Q` rows
  have hCQ : C₀ * a * (μ + τ) * Q ≤ (Kg / 4) * μ * a * Q := by
    have h1 : C₀ * (μ + τ) ≤ (Kg / 4) * μ := by
      have h2 : C₀ * (μ + τ) ≤ C₀ * μ * (1 + 2 * Cn) := by
        nlinarith [hτm, hC₀0, hμ]
      nlinarith [h2, hKg2]
    have h1' := mul_le_mul_of_nonneg_right h1 (mul_nonneg ha.le hQ0)
    calc C₀ * a * (μ + τ) * Q = (C₀ * (μ + τ)) * (a * Q) := by ring
      _ ≤ ((Kg / 4) * μ) * (a * Q) := h1'
      _ = (Kg / 4) * μ * a * Q := by ring
  have hCmQ : μ * (Cm * a * Q) ≤ (Kg / 4) * μ * a * Q := by
    have h1 := mul_le_mul_of_nonneg_right hKg1 (mul_nonneg hμ.le (mul_nonneg ha.le hQ0))
    nlinarith [h1]
  have hnn : 0 ≤ Kg * μ * a * Q := by positivity
  -- ## 4. assemble
  have hrows : C₀ * a * (μ + τ) * Q + μ * (Cm * a * (Real.sqrt (Q * (τ * W)) + Q))
      ≤ Kg * μ * a * Q + W * μ ^ 2 * kpar := by
    have hsplit : μ * (Cm * a * (Real.sqrt (Q * (τ * W)) + Q))
        = μ * (Cm * a * Real.sqrt (Q * (τ * W))) + μ * (Cm * a * Q) := by ring
    linarith [hsqrt, hCmQ, hCQ, hsplit, hnn]
  have hfin : (1 / 18) * μ * τ * W + μ * (τ * W + Cm * a * (Real.sqrt (Q * (τ * W)) + Q))
      ≤ bg * Q + cs + pp := by
    have h2 : (19 / 18) * μ * τ * W + μ * (Cm * a * (Real.sqrt (Q * (τ * W)) + Q))
        ≤ cs + pp + Kg * μ * a * Q := by linarith [hE, hE2, hrows]
    have h3 : (1 / 18) * μ * τ * W + μ * (τ * W + Cm * a * (Real.sqrt (Q * (τ * W)) + Q))
        = (19 / 18) * μ * τ * W + μ * (Cm * a * (Real.sqrt (Q * (τ * W)) + Q)) := by ring
    have h4 := mul_le_mul_of_nonneg_right hgate hQ0
    rw [h3]
    linarith [h2, h4]
  linarith [hstep2, hfin]


/-- **⭐ `RazorSharpF` implies the node's small-window row.**  The assembly of the sharp razor
with the PROVED identity (star), the PROVED manifest fibre bound
`Work.BoseFixB1S.fibSum_le_manifest`, the *distributive* gate `PerBoxGapAbsorbB1` and the pure-real
core `razorArithCore`.  No `n₊`-threshold, no `FlatArm37`, no pair-deadness and no box-size
restriction is used. -/
theorem razorSharpF_imp_smallWinPropF {v : E3 → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hav : 0 < _root_.BoseGases.a v)
    (hRz : RazorSharpF v h R) : SmallWinPropF v h R := by
  intro Cn hCn
  obtain ⟨εrz, Crz, hεrz, hCrz0, hrz⟩ := hRz Cn hCn
  obtain ⟨ Cm, hCm0, hman⟩ :=
    Work.BoseFixB1S.fibSum_le_manifest (v := v) h hv hv1 hvrad hR hv_supp hav
      (M := Work.BoseBox.mValue) (by norm_num [Work.BoseBox.mValue])
  set Kg : ℝ := max (max (4 * Cm) (4 * Crz * (1 + 2 * Cn)))
      (4 * Cm ^ 2 * (_root_.BoseGases.a v)) with hKgdef
  have hKg1 : 4 * Cm ≤ Kg := le_trans (le_max_left _ _) (le_max_left _ _)
  have hKg2 : 4 * Crz * (1 + 2 * Cn) ≤ Kg := le_trans (le_max_right _ _) (le_max_left _ _)
  have hKg3 : 4 * Cm ^ 2 * (_root_.BoseGases.a v) ≤ Kg := le_max_right _ _
  have hKg0 : 0 ≤ Kg := le_trans (by positivity) hKg3
  obtain ⟨ εg, hεg, hgateRaw⟩ := Work.BoseFixB1S.PerBoxGapAbsorbB1 (v := v) hav Kg hKg0
  obtain ⟨ εrg, hεrg, hreg⟩ := Work.BoseFixB1.regime_sideAt_ge (v := v) hav hR
  refine ⟨min (min εrz εg) εrg, lt_min (lt_min hεrz hεg) hεrg, ?_⟩
  intro μ hAdm n Ψ u hu hμW hΨc hsupp hnorm hn1 hn2
  have hAdmR : Work.BoseBoxFix.Adm v εrz μ :=
    Work.BoseFixB1.Adm.mono hAdm (le_trans (min_le_left _ _) (min_le_left _ _))
  have hAdmG : Work.BoseBoxFix.Adm v εg μ :=
    Work.BoseFixB1.Adm.mono hAdm (le_trans (min_le_left _ _) (min_le_right _ _))
  have hAdmReg : Work.BoseBoxFix.Adm v εrg μ := Work.BoseFixB1.Adm.mono hAdm (min_le_right _ _)
  have hμpos : 0 < μ := hAdm.1
  have hℓ : 0 < Work.BoseFixB1.bSide v μ := Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < Work.BoseFixB1.bD v μ := Work.BoseFixB1.adm_d_pos hAdm
  have hM1 : 1 ≤ Work.BoseFixB1.bM v μ := by
    simp only [Work.BoseFixB1.bM, Work.BoseBox.paramsAt, Work.BoseBox.fsParams,
      Work.BoseBox.mValue]
    norm_num
  have hAr : μ * (_root_.BoseGases.a v) ^ 3 ≤ εrg := le_trans hAdm.2.1 (min_le_right _ _)
  obtain ⟨hR16, hRχ⟩ := hreg μ hμpos hAr
  have hV : 0 < Work.BoseFixB1.bV v μ u :=
    Work.BoseFixB1.boxMass_pos_of_goodSet hℓ hd hμpos hu
  have hΨcc : Continuous Ψ := hΨc.continuous
  have hstar := sbWordCube_eq_pair_cube (v := v) h hv hv1 hvrad hR hv_supp hAdmR hΨcc u hR16 hRχ
  have hrz' := hrz μ hAdmR n Ψ u hu hΨc hsupp hnorm hn1 hn2
  have hman' := hman (ℓ := Work.BoseFixB1.bSide v μ) (d := Work.BoseFixB1.bD v μ) (μ := μ)
    hℓ hd hR16 hRχ u hV hΨcc
  have hboxM1 := boxM1_eq_bW (v := v) h hM1 hℓ hd u
  have hW0 : 0 ≤ Work.BoseFixB1.bW v h μ u := by
    rw [← hboxM1]
    exact Work.BoseFixB1S.boxM1_nonneg_wSmall (v := v) hv_supp hR hv hvrad h
      (M := Work.BoseFixB1.bM v μ) (ℓ := Work.BoseFixB1.bSide v μ)
      (d := Work.BoseFixB1.bD v μ) u
  have hQ0 : 0 ≤ Work.BoseFixB1.bQ v μ Ψ u := by
    simpa only [Work.BoseFixB1.bQ] using
      Work.BoseFixB1S.boxQCount_nonneg (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
        (Work.BoseFixB1.bA v μ u) Ψ
  have hvol : Work.BoseFixB1.bV v μ u
      = (MeasureTheory.volume (Work.BoseFixB1.bA v μ u)).toReal := by
    rw [Work.BoseFixB1.bV, Work.BoseFixB1.bA]
    exact Work.SmallBoxSliding.boxMass_eq_measureReal (Work.BoseFixB1.bSide v μ)
      (Work.BoseFixB1.bD v μ) u
  have hSle : Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
      (Work.BoseFixB1.bA v μ u) Ψ ≤ (n : ℝ) := by
    have h1 := Work.BoseFixB1S.boxFlatCount_le_NB1 (N := n) hℓ hV
      (Ac := Work.BoseFixB1.bA v μ u)
      (Work.SmallBoxSliding.measurableSet_dlBox (Work.BoseFixB1.bSide v μ)
        (Work.BoseFixB1.bD v μ) u)
      (Work.SmallBoxSliding.dlBox_subset_acube (Work.BoseFixB1.bSide v μ)
        (Work.BoseFixB1.bD v μ) u)
      hvol hΨcc
    rw [hnorm, mul_one] at h1
    exact h1
  have hVn : (n : ℝ) = ((n : ℝ) / Work.BoseFixB1.bV v μ u) * Work.BoseFixB1.bV v μ u := by
    field_simp
  have hτ0 : 0 ≤ (n : ℝ) / Work.BoseFixB1.bV v μ u := div_nonneg (Nat.cast_nonneg n) hV.le
  have hτm : (n : ℝ) / Work.BoseFixB1.bV v μ u ≤ 2 * Cn * μ := by
    rw [div_le_iff₀ hV]
    linarith [hn2]
  have hlam4 : 4 ≤ ((n : ℝ) / Work.BoseFixB1.bV v μ u) / μ := by
    rw [le_div_iff₀ hμpos]
    have hn1' : 4 * μ * Work.BoseFixB1.bV v μ u ≤ (n : ℝ) := by
      have h4 : 4 * μ ≤ Cn * μ := by nlinarith [hμpos, hCn]
      nlinarith [mul_le_mul_of_nonneg_right h4 hV.le, hn1]
    rw [le_div_iff₀ hV]
    linarith [hn1']
  have hgate : Kg * μ * (_root_.BoseGases.a v) ≤ Work.BoseFixB1.bGapCoeff v μ := by
    simpa only [Work.BoseFixB1.bGapCoeff, Work.BoseFixB1.bSide, Work.BoseFixB1.bD, mul_comm]
      using hgateRaw μ hAdmG
  have hfb : Work.BoseFixB1.fibSum h (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
      (Work.BoseFixB1.bD v μ) u Ψ
      ≤ (Work.BoseFixB1.bW v h μ u / Work.BoseFixB1.bV v μ u)
          * Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bA v μ u) Ψ
        + Cm * (_root_.BoseGases.a v) * (Real.sqrt (Work.BoseFixB1.bQ v μ Ψ u
            * ((Work.BoseFixB1.bW v h μ u / Work.BoseFixB1.bV v μ u)
              * Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1.bV v μ u)
                  (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u) Ψ))
          + Work.BoseFixB1.bQ v μ Ψ u) := by
    have h := hman'
    have hbM : Work.BoseFixB1.bM v μ = Work.BoseBox.mValue := rfl
    rw [← hbM] at h
    rw [hboxM1] at h
    simpa only [Work.BoseFixB1.bW, Work.BoseFixB1.bV, Work.BoseFixB1.bA,
      Work.BoseFixB1.bQ, Work.UBBInputs8.cnPlusBoxInd, Work.BoseFixB1S.boxQCount] using h
  have hEkpar : (1 / 4) * ((n : ℝ) / Work.BoseFixB1.bV v μ u) ^ 2
        + (1 / 2) * (((n : ℝ) / Work.BoseFixB1.bV v μ u) * μ) - (1 / 4) * μ ^ 2
      - ((19 / 18) * μ * ((n : ℝ) / Work.BoseFixB1.bV v μ u) + μ ^ 2
          * ((1 / 4) * (((n : ℝ) / Work.BoseFixB1.bV v μ u) / μ) ^ 2
            - (5 / 9) * (((n : ℝ) / Work.BoseFixB1.bV v μ u) / μ) - (1 / 4))) = 0 := by
    field_simp
    ring
  have hE2 : (19 / 18) * μ * ((n : ℝ) / Work.BoseFixB1.bV v μ u) * Work.BoseFixB1.bW v h μ u
        + Work.BoseFixB1.bW v h μ u * μ ^ 2
          * ((1 / 4) * (((n : ℝ) / Work.BoseFixB1.bV v μ u) / μ) ^ 2
            - (5 / 9) * (((n : ℝ) / Work.BoseFixB1.bV v μ u) / μ) - (1 / 4))
      ≤ ((1 / 4) * ((n : ℝ) / Work.BoseFixB1.bV v μ u) ^ 2
          + (1 / 2) * (((n : ℝ) / Work.BoseFixB1.bV v μ u) * μ) - (1 / 4) * μ ^ 2)
        * Work.BoseFixB1.bW v h μ u := by
    nlinarith [hEkpar, hW0]
  have hcore :=
    razorArithCore (μ := μ) (τ := (n : ℝ) / Work.BoseFixB1.bV v μ u)
      (S := Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
        (Work.BoseFixB1.bA v μ u) Ψ)
      (n := (n : ℝ)) (V := Work.BoseFixB1.bV v μ u) (W := Work.BoseFixB1.bW v h μ u)
      (Q := Work.BoseFixB1.bQ v μ Ψ u) (cs := Work.BoseFixB1B.cubeSpectral v μ Ψ u)
      (pp := Work.BoseFixB1.pairSum v (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
        (Work.BoseFixB1.bD v μ) u Ψ)
      (fb := Work.BoseFixB1.fibSum h (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
        (Work.BoseFixB1.bD v μ) u Ψ)
      (bg := Work.BoseFixB1.bGapCoeff v μ) (a := _root_.BoseGases.a v) (Cm := Cm) (C₀ := Crz)
      (Kg := Kg) (Cn := Cn)
      (E := ((1 / 4) * ((n : ℝ) / Work.BoseFixB1.bV v μ u) ^ 2
              + (1 / 2) * (((n : ℝ) / Work.BoseFixB1.bV v μ u) * μ) - (1 / 4) * μ ^ 2)
            * Work.BoseFixB1.bW v h μ u)
      (kpar := (1 / 4) * (((n : ℝ) / Work.BoseFixB1.bV v μ u) / μ) ^ 2
        - (5 / 9) * (((n : ℝ) / Work.BoseFixB1.bV v μ u) / μ) - (1 / 4))
      hμpos hav hV hW0 hQ0 hSle hVn hτ0 hτm hlam4 hCm0 hCrz0 rfl hKg1 hKg2 hKg3 hgate hfb
      hrz' hE2
  rw [hstar]
  linarith [hcore]

/-- **⭐ (DEMAND) implies the node's small-window row** — the *minimal* razor route.  With (★) the
node's clause `(1/18)μτW ≤ sbWordCube` is equivalent to
`(1/18)μτW + μ·fibSum ≤ bGapCoeff·n₊ + cs + pairSum`; the gap column pays the row
`C₀·(a v)·(μ+τ)·n₊` as soon as `C₀(1+2Cn) ≤ Kg` (the count window gives `τ ≤ 2Cn·μ`), and
`Kg` is *arbitrary but fixed* (`PerBoxGapAbsorbB1`).  So no manifest fibre bound, no Young step and
no razor surplus is needed here — this is the shortest of the razor routes. -/
theorem razorDemandF_imp_smallWinPropF {v : E3 → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hav : 0 < _root_.BoseGases.a v)
    (hRz : RazorDemandF v h R) : SmallWinPropF v h R := by
  intro Cn hCn
  obtain ⟨ εrz, C0a, hεrz, hC0a0, hrz⟩ := hRz Cn hCn
  set Kg : ℝ := max (C0a * (1 + 2 * Cn)) 1 with hKgdef
  have hKg1 : C0a * (1 + 2 * Cn) ≤ Kg := le_max_left _ _
  have hKg0 : 0 ≤ Kg := le_trans (by positivity) hKg1
  obtain ⟨ εg, hεg, hgateRaw⟩ := Work.BoseFixB1S.PerBoxGapAbsorbB1 (v := v) hav Kg hKg0
  obtain ⟨ εrg, hεrg, hreg⟩ := Work.BoseFixB1.regime_sideAt_ge (v := v) hav hR
  refine ⟨min (min εrz εg) εrg, lt_min (lt_min hεrz hεg) hεrg, ?_⟩
  intro μ hAdm n Ψ u hu hμW hΨc hsupp hnorm hn1 hn2
  have hAdmR : Work.BoseBoxFix.Adm v εrz μ :=
    Work.BoseFixB1.Adm.mono hAdm (le_trans (min_le_left _ _) (min_le_left _ _))
  have hAdmReg : Work.BoseBoxFix.Adm v εrg μ := Work.BoseFixB1.Adm.mono hAdm (min_le_right _ _)
  have hμpos : 0 < μ := hAdm.1
  have hℓ : 0 < Work.BoseFixB1.bSide v μ := Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < Work.BoseFixB1.bD v μ := Work.BoseFixB1.adm_d_pos hAdm
  have hAr : μ * (_root_.BoseGases.a v) ^ 3 ≤ εrg := le_trans hAdm.2.1 (min_le_right _ _)
  obtain ⟨hR16, hRχ⟩ := hreg μ hμpos hAr
  have hV : 0 < Work.BoseFixB1.bV v μ u :=
    Work.BoseFixB1.boxMass_pos_of_goodSet hℓ hd hμpos hu
  have hΨcc : Continuous Ψ := hΨc.continuous
  have hstar := sbWordCube_eq_pair_cube (v := v) h hv hv1 hvrad hR hv_supp hAdmR hΨcc u hR16 hRχ
  have hrz' := hrz μ hAdmR n Ψ u hu hΨc hsupp hnorm hn1 hn2
  have hgate : Kg * μ * (_root_.BoseGases.a v) ≤ Work.BoseFixB1.bGapCoeff v μ := by
    simpa only [Work.BoseFixB1.bGapCoeff, Work.BoseFixB1.bSide, Work.BoseFixB1.bD, mul_comm]
      using hgateRaw μ (Work.BoseFixB1.Adm.mono hAdm (le_trans (min_le_left _ _) (min_le_right _ _)))
  have hQ0 : 0 ≤ Work.BoseFixB1.bQ v μ Ψ u := by
    simpa only [Work.BoseFixB1.bQ] using
      Work.BoseFixB1S.boxQCount_nonneg (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
        (Work.BoseFixB1.bA v μ u) Ψ
  have hτm : (n : ℝ) / Work.BoseFixB1.bV v μ u ≤ 2 * Cn * μ := by
    rw [div_le_iff₀ hV]
    linarith [hn2]
  have hCrow : C0a * (_root_.BoseGases.a v) * (μ + (n : ℝ) / Work.BoseFixB1.bV v μ u)
        * Work.BoseFixB1.bQ v μ Ψ u
      ≤ Work.BoseFixB1.bGapCoeff v μ * Work.BoseFixB1.bQ v μ Ψ u := by
    have h1 : C0a * (μ + (n : ℝ) / Work.BoseFixB1.bV v μ u) ≤ Kg * μ := by
      nlinarith [hKg1, hτm, hμpos, hC0a0]
    have h2 : C0a * (_root_.BoseGases.a v) * (μ + (n : ℝ) / Work.BoseFixB1.bV v μ u)
          * Work.BoseFixB1.bQ v μ Ψ u
        ≤ Kg * μ * (_root_.BoseGases.a v) * Work.BoseFixB1.bQ v μ Ψ u := by
      have h3 := mul_le_mul_of_nonneg_right h1 (mul_nonneg hav.le hQ0)
      nlinarith [h3]
    have h4 : Kg * μ * (_root_.BoseGases.a v) * Work.BoseFixB1.bQ v μ Ψ u
        ≤ Work.BoseFixB1.bGapCoeff v μ * Work.BoseFixB1.bQ v μ Ψ u :=
      mul_le_mul_of_nonneg_right hgate hQ0
    linarith [h2, h4]
  rw [hstar]
  linarith [hrz', hCrow]

end Work.BoseB1Cube

