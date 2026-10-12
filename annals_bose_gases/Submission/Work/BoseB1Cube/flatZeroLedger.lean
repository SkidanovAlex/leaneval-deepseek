import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB1Cube.flatPairJensenCube
import Submission.Work.BoseB1Cube.flatPairRowCube
import Submission.Work.BoseB1Cube.flatZeroAux
import Submission.Work.BoseFixB1S.LowCountWindowAllJCube
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB1Cube.flatZeroLedger` — the exactly-flat branch at the cube cutoff

Cone-restricted port of `Work.BoseFixB1.Up.perBoxF_of_flatZero`
(`Submission/Work/BoseFixB1/Up/FlatZeroLedger.lean`) to the matched (single cube cutoff) word
`sbWordCube`.  The final theorem `perBoxF_of_flatZeroCube` is the frozen statement with
`sbWord ↦ sbWordCube`, `sbKin ↦ sbKinCube` and `PerBoxF ↦ Work.BoseFixB1S.PerBoxFCube`; the
consistency of the words is exactly the *flatness* of the state (`sbKin = sbKinCube` is not used:
only `0 ≤ sbKinCube` is needed on the right, and the two windows agree on the *state rows*).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseB1Cube.CubeFlat

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding Work.BoseFixB1

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-! ## 1. `0 ≤ sbKinCube` -/

/-- **`0 ≤ sbKinCube`** at an admissible `μ` (the cube twin of `Work.BoseFixB1.Up.sbKin_nonneg` /
`Work.BoseB1Cube.sbKinCube_nonneg`). -/
theorem sbKinCube_nonneg {v : E3 → ℝ} {ε₀ μ : ℝ} (hadm : Adm v ε₀ μ) {n : ℕ}
    (u : E3) (Φ : Submission.BoseGases.X n → ℝ) :
    0 ≤ Work.BoseFixB1B.sbKinCube v μ u Φ := by
  have heT : 0 ≤ (paramsAt μ (_root_.BoseGases.a v)).eT :=
    (Work.BoseFixB1.adm_eT_bounds hadm).1
  have hgap : 0 ≤ Work.BoseFixB1.bGapCoeff v μ *
      Work.UBBInputs8.cnPlusBoxInd (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u)
        (Work.BoseFixB1.bV v μ u) Φ :=
    mul_nonneg (Work.SmallBoxTBWord.tbGapCoeff_nonneg heT) (by
      unfold Work.UBBInputs8.cnPlusBoxInd
      exact Finset.sum_nonneg fun i _ => integral_nonneg fun x => sq_nonneg _)
  have hspec : 0 ≤ Work.BoseFixB1B.cubeSpectral v μ Φ u :=
    Work.BoseFixB1.tBwordKinInd_nonneg Φ
  rw [Work.BoseFixB1B.sbKinCube]
  linarith

/-! ## 2. The pair-condensate count at general parameters -/

/-- The pair-condensate sum at general parameters (copy of the `FlatZeroLedger` local). -/
noncomputable def flatXpSum (M : ℕ) (ℓ d : ℝ) (u : E3) {n : ℕ}
    (Φ : Submission.BoseGases.X n → ℝ) : ℝ :=
  (chiMass M ℓ d u)⁻¹ ^ 2 *
    ∑ i : Fin n, ∑ j ∈ (Finset.univ.erase i),
      ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 *
        (Submission.BoseGases.chiSmallB M ℓ d u (x i)) ^ 2 *
        (Submission.BoseGases.chiSmallB M ℓ d u (x j)) ^ 2

/-- `flatXp` is `flatXpSum` at FS's parameters (definitional). -/
theorem flatXp_eq_flatXpSum {v : E3 → ℝ} {μ : ℝ} {n : ℕ}
    (Φ : Submission.BoseGases.X n → ℝ) (u : E3) :
    flatXp v μ Φ u = flatXpSum (pM v μ) (pL v μ) (pD v μ) u Φ := rfl

/-- **The pair-condensate Jensen row** `τ² − τ/|B| ≤ Xp/‖Φ‖²`. -/
theorem flatPairJensenUp {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    {u : E3} {n : ℕ} {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ)
    (hflat : ∀ i : Fin n, Work.UBBInputs8.boxQInd (boxMass ℓ d u)
        (Submission.BoseGases.dlBox ℓ d u) i Φ
        =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)] 0) :
    flatTau M ℓ d u Φ ^ 2 - flatTau M ℓ d u Φ / boxMass ℓ d u
      ≤ flatXpSum M ℓ d u Φ / flatMass ℓ Φ := by
  have hj := Work.BoseB1Cube.flatPairJensenCube (M := M) hM hℓ hd hΦc hflat
  dsimp only at hj
  rw [← flatScountB_eq_sum (M := M) (ℓ := ℓ) (d := d) (u := u) (n := n) hℓ hΦc] at hj
  simpa only [flatTau, flatMass, flatXpSum] using hj

/-- **The exactly-flat pair identity in pair-condensate form.** -/
theorem flatPairSum_eq_flatXp_cube {v : E3 → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR16 : R ≤ ℓ * d / 16) (hRχ : R ≤ ℓ * Submission.BoseGases.chiR0)
    (u : E3) {n : ℕ} {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ)
    (hflat : Work.UBBInputs8.cnPlusBoxInd ℓ (Submission.BoseGases.dlBox ℓ d u)
      (boxMass ℓ d u) Φ = 0) :
    flatPairSum v M ℓ d u Φ = (1 / 2) * flatPairMass v M ℓ d u * flatXpSum M ℓ d u Φ :=
  Work.BoseB1Cube.flatPairRowCube h hv hv1 hR hv_supp hM hℓ hd hR16 hRχ u hΦc hflat

/-! ## 3. The payer arithmetic -/

/-- **The payer arithmetic** (verbatim copy of `Work.BoseFixB1.Up.flatZeroPayers`). -/
theorem flatZeroPayers {μ a κ A W₁ W₂ Cχ Γ C₁ C₂ c₁ : ℝ}
    (hμ : 0 < μ) (ha : 0 < a) (hκ : 0 ≤ κ) (hA : 0 < A) (hCχ : 0 ≤ Cχ)
    (hΓ : 0 ≤ Γ) (hW₁ : 0 ≤ W₁) (hW₂ : 0 ≤ W₂)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hW₁C : W₁ ≤ C₁ * a * κ) (hW₂C : W₂ ≤ C₂ * a * κ)
    (hκA : κ ≤ Cχ ^ 2 * A) (hμA : 1 ≤ μ * A)
    (hc₁ : 0 < c₁) (hc₁8 : c₁ ≤ 1 / 8) :
    W₂ * μ / A + 8 * c₁ * W₁ * Cχ ^ 2 * μ / κ + 3 * W₂ / (5 * A ^ 2)
        + c₁ * W₁ * Cχ ^ 2 * μ / κ
      ≤ Cχ ^ 2 * (2 * C₁ + 2 * C₂ + 1) * (μ ^ 2 * a * Γ * κ + μ * a) := by
  have hκA' : κ / A ≤ Cχ ^ 2 := by
    rw [div_le_iff₀ hA]; linarith
  have hAinv : 1 / A ≤ μ := by
    rw [div_le_iff₀ hA]; linarith
  have hμA0 : 0 ≤ μ / A := div_nonneg hμ.le hA.le
  have hW₁div : W₁ / κ ≤ C₁ * a :=
    div_le_of_le_mul_of_nonneg hW₁ hκ (by positivity) (by linarith)
  have h1 : W₂ * μ / A ≤ C₂ * Cχ ^ 2 * a * μ := by
    have hstep : W₂ * μ / A = W₂ * (μ / A) := by ring
    rw [hstep]
    have h2 : W₂ * (μ / A) ≤ (C₂ * a * κ) * (μ / A) :=
      mul_le_mul_of_nonneg_right hW₂C hμA0
    have h3 : (C₂ * a * κ) * (μ / A) ≤ C₂ * a * μ * Cχ ^ 2 := by
      have he : (C₂ * a * κ) * (μ / A) = C₂ * a * μ * (κ / A) := by ring
      rw [he]
      exact mul_le_mul_of_nonneg_left hκA' (by positivity)
    linarith [h2, h3]
  have h2 : 3 * W₂ / (5 * A ^ 2) ≤ (3 / 5) * (C₂ * Cχ ^ 2 * a * μ) := by
    have hW₂A : 0 ≤ W₂ / A := div_nonneg hW₂ hA.le
    have hstep : W₂ / A ^ 2 ≤ W₂ * μ / A := by
      have he : W₂ / A ^ 2 = (W₂ / A) * (1 / A) := by ring
      rw [he]
      have h := mul_le_mul_of_nonneg_left hAinv hW₂A
      have h2 : W₂ / A * μ = W₂ * μ / A := by ring
      linarith [h, h2]
    have he2 : 3 * W₂ / (5 * A ^ 2) = (3 / 5) * (W₂ / A ^ 2) := by ring
    rw [he2]
    exact mul_le_mul_of_nonneg_left (le_trans hstep h1) (by norm_num)
  have h3 : 8 * c₁ * W₁ * Cχ ^ 2 * μ / κ ≤ 8 * c₁ * C₁ * Cχ ^ 2 * a * μ := by
    have he : 8 * c₁ * W₁ * Cχ ^ 2 * μ / κ = (8 * c₁ * Cχ ^ 2 * μ) * (W₁ / κ) := by ring
    rw [he]
    have := mul_le_mul_of_nonneg_left hW₁div (by positivity : (0:ℝ) ≤ 8 * c₁ * Cχ ^ 2 * μ)
    nlinarith [this]
  have h4 : c₁ * W₁ * Cχ ^ 2 * μ / κ ≤ c₁ * C₁ * Cχ ^ 2 * a * μ := by
    have he : c₁ * W₁ * Cχ ^ 2 * μ / κ = (c₁ * Cχ ^ 2 * μ) * (W₁ / κ) := by ring
    rw [he]
    have := mul_le_mul_of_nonneg_left hW₁div (by positivity : (0:ℝ) ≤ c₁ * Cχ ^ 2 * μ)
    nlinarith [this]
  have hsum : W₂ * μ / A + 8 * c₁ * W₁ * Cχ ^ 2 * μ / κ + 3 * W₂ / (5 * A ^ 2)
        + c₁ * W₁ * Cχ ^ 2 * μ / κ
      ≤ C₂ * Cχ ^ 2 * a * μ + 8 * c₁ * C₁ * Cχ ^ 2 * a * μ
        + (3 / 5) * (C₂ * Cχ ^ 2 * a * μ) + c₁ * C₁ * Cχ ^ 2 * a * μ := by
    linarith [h1, h2, h3, h4]
  have hcoef : C₂ + 8 * c₁ * C₁ + 3 / 5 * C₂ + c₁ * C₁ ≤ 2 * C₁ + 2 * C₂ + 1 := by
    nlinarith [hc₁8, hC₁, hC₂]
  have hfin : C₂ * Cχ ^ 2 * a * μ + 8 * c₁ * C₁ * Cχ ^ 2 * a * μ
        + (3 / 5) * (C₂ * Cχ ^ 2 * a * μ) + c₁ * C₁ * Cχ ^ 2 * a * μ
      ≤ Cχ ^ 2 * (2 * C₁ + 2 * C₂ + 1) * (μ ^ 2 * a * Γ * κ + μ * a) := by
    have h0 : 0 ≤ Cχ ^ 2 * a * μ := by positivity
    have hG : 0 ≤ μ ^ 2 * a * Γ * κ := by positivity
    have e : C₂ * Cχ ^ 2 * a * μ + 8 * c₁ * C₁ * Cχ ^ 2 * a * μ
        + (3 / 5) * (C₂ * Cχ ^ 2 * a * μ) + c₁ * C₁ * Cχ ^ 2 * a * μ
        = (C₂ + 8 * c₁ * C₁ + 3 / 5 * C₂ + c₁ * C₁) * (Cχ ^ 2 * a * μ) := by ring
    rw [e]
    have h1' : (C₂ + 8 * c₁ * C₁ + 3 / 5 * C₂ + c₁ * C₁) * (Cχ ^ 2 * a * μ)
        ≤ (2 * C₁ + 2 * C₂ + 1) * (Cχ ^ 2 * a * μ) :=
      mul_le_mul_of_nonneg_right hcoef h0
    have h2' : (2 * C₁ + 2 * C₂ + 1) * (Cχ ^ 2 * a * μ)
        ≤ Cχ ^ 2 * (2 * C₁ + 2 * C₂ + 1) * (μ ^ 2 * a * Γ * κ + μ * a) := by
      have hc : 0 ≤ Cχ ^ 2 * (2 * C₁ + 2 * C₂ + 1) := by positivity
      have hle : μ * a ≤ μ ^ 2 * a * Γ * κ + μ * a := by linarith
      nlinarith [hc, hle]
    linarith [h1', h2']
  linarith [hsum, hfin]

/-! ## 4. The final arithmetic of the flat branch -/

/-- **The final arithmetic of the exactly-flat branch** (verbatim copy of
`Work.BoseFixB1.Up.flatZeroFinalArith`). -/
theorem flatZeroFinalArith {μ W₁ W₂ κ A τ D Xp Fterm N Cχ c₁ Cp errb : ℝ}
    (hμ : 0 < μ) (hτ : 0 ≤ τ) (hκ : 0 ≤ κ) (hA : 0 < A) (hCχ : 0 ≤ Cχ)
    (hW₁ : 0 ≤ W₁) (hW₁₂ : W₁ ≤ W₂) (hW₂ : 0 ≤ W₂)
    (hD : 0 ≤ D) (hXp : 0 ≤ Xp) (hN : 0 < N)
    (hc₁ : 0 < c₁) (hc₁4 : c₁ ≤ 1 / 4) (hc₁8 : 8 * c₁ * W₁ ≤ W₂)
    (hF : Fterm ≤ N * (μ * (τ - μ) ^ 2 / (τ + μ))
        + (4 * μ ^ 2 / (τ + μ) ^ 2) * (D + Xp - τ ^ 2 * N))
    (hDle : D / N ≤ Cχ ^ 2 * τ / κ)
    (hY : τ ^ 2 - τ / A ≤ Xp / N)
    (hPay : W₂ * μ / A + 8 * c₁ * W₁ * Cχ ^ 2 * μ / κ + 3 * W₂ / (5 * A ^ 2)
        + c₁ * W₁ * Cχ ^ 2 * μ / κ ≤ Cp * errb) :
    c₁ * W₁ * Fterm - (1 / 2) * μ ^ 2 * W₁ * N - Cp * errb * N
      ≤ -(μ * W₁ * τ * N) + (1 / 2) * W₂ * Xp := by
  have hNne : N ≠ 0 := ne_of_gt hN
  have hτμ : 0 < τ + μ := by linarith
  set F1 : ℝ := μ * (τ - μ) ^ 2 / (τ + μ) with hF1def
  set ρ : ℝ := 4 * c₁ * W₁ * μ ^ 2 / (τ + μ) ^ 2 with hρdef
  have hΩ := Work.BoseFixB1.Up.flatZeroOmega_le (μ := μ) (W₁ := W₁) (W₂ := W₂) (κ := κ)
    (A := A) (τ := τ) (Y := Xp / N) (Dn := D / N) (Cχ := Cχ) (c₁ := c₁)
    hμ hW₁ hW₁₂ hW₂ hA hτ hκ hCχ (div_nonneg hD hN.le) hDle hc₁ hc₁4 hc₁8 hY
  have hstep1 : c₁ * W₁ * Fterm - (1 / 2) * μ ^ 2 * W₁ * N - Cp * errb * N
      ≤ c₁ * W₁ * (N * (μ * (τ - μ) ^ 2 / (τ + μ))
            + (4 * μ ^ 2 / (τ + μ) ^ 2) * (D + Xp - τ ^ 2 * N))
          - (1 / 2) * μ ^ 2 * W₁ * N - Cp * errb * N := by
    have h := mul_le_mul_of_nonneg_left hF (by positivity : (0:ℝ) ≤ c₁ * W₁)
    linarith [h]
  have hstep2 : c₁ * W₁ * (N * (μ * (τ - μ) ^ 2 / (τ + μ))
          + (4 * μ ^ 2 / (τ + μ) ^ 2) * (D + Xp - τ ^ 2 * N))
        - (1 / 2) * μ ^ 2 * W₁ * N - Cp * errb * N
      = (N * (c₁ * W₁ * F1 + μ * W₁ * τ - (1 / 2) * μ ^ 2 * W₁
            + ρ * (D / N) + (ρ - (1 / 2) * W₂) * (Xp / N) - ρ * τ ^ 2)
          - N * (μ * W₁ * τ) + (1 / 2) * W₂ * Xp) - Cp * errb * N := by
    rw [hF1def, hρdef]
    field_simp
    ring
  have hstep3 : N * (c₁ * W₁ * F1 + μ * W₁ * τ - (1 / 2) * μ ^ 2 * W₁
        + ρ * (D / N) + (ρ - (1 / 2) * W₂) * (Xp / N) - ρ * τ ^ 2)
      ≤ N * (W₂ * μ / A + 8 * c₁ * W₁ * Cχ ^ 2 * μ / κ + 3 * W₂ / (5 * A ^ 2)
        + c₁ * W₁ * Cχ ^ 2 * μ / κ) := by
    rw [← hF1def, ← hρdef] at hΩ
    exact mul_le_mul_of_nonneg_left hΩ hN.le
  have hstep4 : N * (W₂ * μ / A + 8 * c₁ * W₁ * Cχ ^ 2 * μ / κ + 3 * W₂ / (5 * A ^ 2)
        + c₁ * W₁ * Cχ ^ 2 * μ / κ) ≤ Cp * errb * N := by
    have h := mul_le_mul_of_nonneg_left hPay hN.le
    linarith [h]
  linarith [hstep1, hstep2.le, hstep3, hstep4]

/-! ## 5. The assembly: the exactly-flat branch at the cube cutoff

The cone-restricted port of `Work.BoseFixB1.Up.perBoxF_of_flatZero`, with the word
`sbWord ↦ sbWordCube` and the kinetic slot `sbKin ↦ sbKinCube`. -/

theorem perBoxF_of_flatZeroCube {v : E3 → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hav : 0 < _root_.BoseGases.a v)
    {ε₀ μ C₁ C₂ : ℝ} (hAdm : Work.BoseBoxFix.Adm v ε₀ μ) (hε₁ : ε₀ ≤ 1) (u : E3)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hW₁C : w1MassB h (pM v μ) (pL v μ) (pD v μ) u ≤ C₁ * (_root_.BoseGases.a v)
        * chiMass (pM v μ) (pL v μ) (pD v μ) u)
    (hW₂C : flatPairMass v (pM v μ) (pL v μ) (pD v μ) u ≤ C₂ * (_root_.BoseGases.a v)
        * chiMass (pM v μ) (pL v μ) (pD v μ) u)
    (hR16 : R ≤ pL v μ * pD v μ / 16) (hRχ : R ≤ pL v μ * Submission.BoseGases.chiR0)
    {n : ℕ} (Φ : Work.BoseKinLoc.BoxState n (pL v μ))
    (hu : u ∈ Work.SmallBoxSliding.goodSet (pL v μ) (pD v μ) μ)
    (hflat : Work.UBBInputs8.cnPlusBoxInd (pL v μ)
        (Submission.BoseGases.dlBox (pL v μ) (pD v μ) u)
        (Work.SmallBoxSliding.boxMass (pL v μ) (pD v μ) u)
        (Φ : Submission.BoseGases.X n → ℝ) = 0) :
    Work.BoseFixB1S.PerBoxFCube v h R (1 / 16)
      ((Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay (pM v μ)) ^ 2
        * (2 * C₁ + 2 * C₂ + 1)) μ n Φ u := by
  have hμ : 0 < μ := hAdm.1
  have ha : 0 < _root_.BoseGases.a v := hav
  have hM : 1 ≤ pM v μ := by
    rw [pM, M_eq_mValue]; norm_num [Work.BoseBox.mValue]
  have hℓ : 0 < pL v μ := by
    rw [pL]; exact adm_ell_pos hAdm
  have hd : 0 < pD v μ := by
    rw [pD]; exact adm_d_pos hAdm
  have hΦc : Continuous (Φ : Submission.BoseGases.X n → ℝ) := Φ.contDiff.continuous
  -- ## the box facts
  have hεa : μ * (_root_.BoseGases.a v) ^ 3 ≤ 1 := le_trans hAdm.2.1 hε₁
  have hbox : 1 ≤ μ * Work.SmallBoxSliding.boxMass (pL v μ)
      (pD v μ) u :=
    Work.BoseFixB1.SectorAux.one_le_mu_boxMassGood ha hμ hεa hu
  have hApos : 0 < Work.SmallBoxSliding.boxMass (pL v μ)
      (pD v μ) u := by nlinarith [hbox, hμ]
  have hvol : Work.SmallBoxSliding.boxMass (pL v μ)
      (pD v μ) u ≠ 0 := ne_of_gt hApos
  -- ## the flatness hypothesis of the Jensen row
  have hAmeas : MeasurableSet (Submission.BoseGases.dlBox (pL v μ)
      (pD v μ) u) := Work.SmallBoxSliding.measurableSet_dlBox _ _ _
  have hVeq : Work.SmallBoxSliding.boxMass (pL v μ) (pD v μ) u
      = (volume (Submission.BoseGases.dlBox (pL v μ) (pD v μ) u)).toReal := by
    rw [Work.SmallBoxSliding.boxMass_eq_measureReal, MeasureTheory.Measure.real_def]
  have hAc : Submission.BoseGases.dlBox (pL v μ) (pD v μ) u
      ⊆ Submission.BoseGases.acube (pL v μ) :=
    Work.SmallBoxSliding.dlBox_subset_acube _ _ _
  have hQ : Work.BoseFixB1S.boxQCount (Work.SmallBoxSliding.boxMass (pL v μ)
      (pD v μ) u) (pL v μ)
      (Submission.BoseGases.dlBox (pL v μ) (pD v μ) u)
      (Φ : Submission.BoseGases.X n → ℝ) = 0 := by
    simp only [Work.BoseFixB1S.boxQCount, Work.UBBInputs8.cnPlusBoxInd]
    exact hflat
  have hqae : ∀ i : Fin n, Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass
      (pL v μ) (pD v μ) u)
      (Submission.BoseGases.dlBox (pL v μ) (pD v μ) u) i
      (Φ : Submission.BoseGases.X n → ℝ)
      =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox n (pL v μ))] 0 :=
    fun i => Work.BoseFixB1S.boxQInd_ae_zero_of_boxQCount_eq_zero hℓ hApos hAmeas hVeq hAc hΦc hQ i
  -- ## the local abbreviations
  set W₁ : ℝ := w1MassB h (pM v μ) (pL v μ) (pD v μ) u with hW₁def
  set W₂ : ℝ := flatPairMass v (pM v μ) (pL v μ) (pD v μ) u with hW₂def
  set κ : ℝ := chiMass (pM v μ) (pL v μ) (pD v μ) u with hκdef
  set A : ℝ := Work.SmallBoxSliding.boxMass (pL v μ) (pD v μ) u with hAdef
  set N : ℝ := normB v μ n (Φ : Submission.BoseGases.X n → ℝ) with hNdef
  set S : ℝ := flatScountB (pM v μ) (pL v μ) (pD v μ) u (Φ : Submission.BoseGases.X n → ℝ)
      with hSdef
  set τ : ℝ := flatTau (pM v μ) (pL v μ) (pD v μ) u (Φ : Submission.BoseGases.X n → ℝ)
      with hτdef
  set Xp : ℝ := flatXp v μ (Φ : Submission.BoseGases.X n → ℝ) u with hXpdef
  set D : ℝ := flatD v μ (Φ : Submission.BoseGases.X n → ℝ) u with hDdef
  set Fterm : ℝ := ∫ x in Submission.BoseGases.abox n (pL v μ),
      (Φ x) ^ 2 * Work.SmallBoxSliding.psiWeight 1 μ
        (nCountB (pM v μ) (pL v μ) (pD v μ) u x
          / chiMass (pM v μ) (pL v μ) (pD v μ) u) with hFtermdef
  set Cχ : ℝ := Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay
      (pM v μ) with hCχdef
  set Γg : ℝ := (R / (pL v μ * pD v μ)) ^ 2
      + (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
        * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ) with hΓdef
  set Cp : ℝ := (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay
      (pM v μ)) ^ 2 * (2 * C₁ + 2 * C₂ + 1) with hCpdef
  set errb : ℝ := μ ^ 2 * (_root_.BoseGases.a v) * Γg * κ + μ * (_root_.BoseGases.a v)
      with herrbdef
  have hFterm_eq : flatFterm (pM v μ) (pL v μ)
      (pD v μ) μ u (Φ : Submission.BoseGases.X n → ℝ) = Fterm := rfl
  -- ## elementary nonnegativities
  have hNnn : 0 ≤ N := by
    rw [hNdef, Work.BoseBoxFix.normB, Work.BoseKinLoc.sqNormB]
    exact integral_nonneg (fun x => sq_nonneg _)
  have hSnn : 0 ≤ S := by
    simp only [hSdef, flatScountB, nCountB]
    exact integral_nonneg (fun x => mul_nonneg (sq_nonneg _)
      (Finset.sum_nonneg (fun i _ => by positivity)))
  have hκnn : 0 ≤ κ := by rw [hκdef]; exact Work.SmallBoxSliding.chiMass_nonneg _ _ _ _
  have hW₁nn : 0 ≤ W₁ := by
    rw [hW₁def]
    exact w1MassB_nonneg (v := v) h hv hvrad hR hv_supp hℓ hd u
  have hCχnn : 0 ≤ Cχ := by
    rw [hCχdef]
    exact mul_nonneg Submission.BoseGases.chiSupAbs_nonneg
      (Submission.BoseGases.chiSmallDecay_nonneg _)
  have hD0 : 0 ≤ D := by
    rw [hDdef, flatD]
    exact mul_nonneg (sq_nonneg _) (integral_nonneg (fun x => mul_nonneg (sq_nonneg _)
      (Finset.sum_nonneg (fun i _ => by positivity))))
  have hXpnn : 0 ≤ Xp := by
    rw [hXpdef, flatXp]
    refine mul_nonneg (sq_nonneg _) (Finset.sum_nonneg (fun i _ =>
      Finset.sum_nonneg (fun j _ => ?_)))
    exact integral_nonneg (fun x =>
      mul_nonneg (mul_nonneg (sq_nonneg _) (by positivity)) (by positivity))
  have hΓnn : 0 ≤ Γg := by
    rw [hΓdef]
    exact add_nonneg (sq_nonneg _) (mul_nonneg
      (pow_nonneg (le_of_lt (Work.BoseFixB1.paramsAt_KB_pos hAdm)) 3)
      (Real.rpow_nonneg (mul_nonneg hμ.le (pow_nonneg ha.le 3)) _))
  -- ## the mass-law facts in the local vocabulary
  have hW₁₂ : W₁ ≤ W₂ := by
    rw [hW₁def, hW₂def]
    exact Work.BoseFixB1S.w1MassB_le_flatPairMassB1 h hv hvrad hv1 hR hv_supp hM hℓ hd hR16 hRχ u
  have hW₂nn : 0 ≤ W₂ := le_trans hW₁nn hW₁₂
  have hW₁C' : W₁ ≤ C₁ * (_root_.BoseGases.a v) * κ := by
    rw [hW₁def, hκdef]; exact hW₁C
  have hW₂C' : W₂ ≤ C₂ * (_root_.BoseGases.a v) * κ := by
    rw [hW₂def, hκdef]; exact hW₂C
  have hκA : κ ≤ Cχ ^ 2 * A := by
    rw [hκdef, hAdef, hCχdef]
    exact Work.BoseFixB1S.chiMass_le_const_mul_boxMass hM hℓ hd u
  have hμA : 1 ≤ μ * A := by rw [hAdef]; exact hbox
  -- ## the four rows
  have hDle : D / N ≤ Cχ ^ 2 * τ / κ := by
    rw [hDdef, hNdef, hτdef, hκdef, hCχdef]
    exact flatD_div_le hΦc hℓ u (fun z => chiSmallB_abs_le_const hM _ _ u z)
  have hY : τ ^ 2 - τ / A ≤ Xp / N := by
    rw [hXpdef, hNdef, hτdef, hAdef]
    rw [flatXp_eq_flatXpSum]
    exact flatPairJensenUp hM hℓ hd hΦc hqae
  have hVar : Work.BoseFixB1.Up.flatVar v μ (Φ : Submission.BoseGases.X n → ℝ) u
      = D + Xp - τ ^ 2 * N := by
    rw [flatVar_eq_flatD_add_flatXp_sub h hΦc hℓ u, hDdef, hXpdef, hτdef, hNdef]
  have hFrow : Fterm ≤ N * (μ * (τ - μ) ^ 2 / (τ + μ))
      + (4 * μ ^ 2 / (τ + μ) ^ 2) * (D + Xp - τ ^ 2 * N) := by
    have h1 := Work.BoseFixB1.Up.flatFterm_sharp_row (v := v) h hAdm Φ u
    rw [hFterm_eq, ← hNdef, ← hτdef, hVar] at h1
    exact h1
  have hPay : W₂ * μ / A + 8 * (1 / 16) * W₁ * Cχ ^ 2 * μ / κ + 3 * W₂ / (5 * A ^ 2)
      + (1 / 16) * W₁ * Cχ ^ 2 * μ / κ ≤ Cp * errb := by
    have h := flatZeroPayers (μ := μ) (a := _root_.BoseGases.a v) (κ := κ) (A := A)
      (W₁ := W₁) (W₂ := W₂) (Cχ := Cχ) (Γ := Γg) (C₁ := C₁) (C₂ := C₂) (c₁ := 1 / 16)
      hμ ha hκnn hApos hCχnn hΓnn hW₁nn hW₂nn hC₁ hC₂ hW₁C' hW₂C' hκA hμA
      (by norm_num) (by norm_num)
    have hCp : Cχ ^ 2 * (2 * C₁ + 2 * C₂ + 1) = Cp := by rw [hCpdef, hCχdef]
    rw [hCp] at h
    exact h
  -- ## the two `sbPot` rows
  have hSdiv : S / κ = τ * N := by
    rw [hSdef, hκdef, hτdef, hNdef]
    exact flatScountB_div_eq_flatTau_mul_normB (v := v) (μ := μ) (n := n)
      (Φ := (Φ : Submission.BoseGases.X n → ℝ)) hℓ hΦc u
  have hint := Work.BoseFixB1.Up.integrableOn_fibSum_abox (v := v) h hR hv_supp hv hvrad hav
    hM hℓ hd hR16 hRχ u (Φ := (Φ : Submission.BoseGases.X n → ℝ)) hΦc
  have hfibsum : flatFibSum h (pM v μ) (pL v μ)
      (pD v μ) u (Φ : Submission.BoseGases.X n → ℝ) = (W₁ / κ) * S := by
    rw [hW₁def, hκdef, hSdef]
    exact Work.BoseFixB1S.flatFibreMeanFieldB1Oper h hM hℓ hd u hvol hΦc hflat hint
  have hfibrow : Work.BoseFixB1.Up.fibSum h (pM v μ) (pL v μ)
      (pD v μ) u (Φ : Submission.BoseGases.X n → ℝ) = W₁ * τ * N := by
    rw [show Work.BoseFixB1.Up.fibSum h (pM v μ) (pL v μ)
          (pD v μ) u (Φ : Submission.BoseGases.X n → ℝ)
        = flatFibSum h (pM v μ) (pL v μ)
          (pD v μ) u (Φ : Submission.BoseGases.X n → ℝ) from rfl, hfibsum]
    rw [show (W₁ / κ) * S = W₁ * (S / κ) from by ring, hSdiv]
    ring
  have hpairrow : Work.BoseFixB1.Up.pairSum v (pM v μ) (pL v μ)
      (pD v μ) u (Φ : Submission.BoseGases.X n → ℝ) = (1 / 2) * W₂ * Xp := by
    rw [show Work.BoseFixB1.Up.pairSum v (pM v μ) (pL v μ)
          (pD v μ) u (Φ : Submission.BoseGases.X n → ℝ)
        = flatPairSum v (pM v μ) (pL v μ)
          (pD v μ) u (Φ : Submission.BoseGases.X n → ℝ) from rfl]
    rw [flatPairSum_eq_flatXp_cube h hv hv1 hR hv_supp hM hℓ hd hR16 hRχ u hΦc hflat]
    rw [hW₂def, hXpdef, flatXp_eq_flatXpSum]
  -- ## the kinetic row
  have hkin : 0 ≤ Work.BoseFixB1B.sbKinCube v μ u (Φ : Submission.BoseGases.X n → ℝ) :=
    sbKinCube_nonneg hAdm u (Φ : Submission.BoseGases.X n → ℝ)
  -- ## conclude
  rw [Work.BoseFixB1S.PerBoxFCube, Work.BoseFixB1B.sbWordCube,
    Work.BoseFixB1.Up.sbPot_split (v := v) (h := h) (R := R) hv_supp hR hv hvrad hv1 hAdm hΦc u
      hR16 hRχ, hfibrow, hpairrow]
  rw [← hW₁def, ← hFtermdef, ← hNdef]
  have herr : (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay
      (pM v μ)) ^ 2 * (2 * C₁ + 2 * C₂ + 1)
      * (μ ^ 2 * (_root_.BoseGases.a v) * Γg * κ * N + μ * (_root_.BoseGases.a v) * N)
      = Cp * errb * N := by
    rw [hCpdef, herrbdef]; ring
  rw [herr]
  by_cases hN0 : N = 0
  · -- ## the degenerate case `N = 0`: the state vanishes a.e. on the box
    have hΦae : (fun x : Submission.BoseGases.X n => (Φ x) ^ 2)
        =ᵐ[(volume : Measure (Submission.BoseGases.X n)).restrict
            (Submission.BoseGases.abox n (pL v μ))] 0 := by
      have hfint : Integrable (fun x : Submission.BoseGases.X n => (Φ x) ^ 2)
          ((volume : Measure (Submission.BoseGases.X n)).restrict
            (Submission.BoseGases.abox n (pL v μ))) :=
        integrableOn_abox_local hℓ (hΦc.pow 2)
      have hNv : N = (∫ x in Submission.BoseGases.abox n (pL v μ),
          (Φ x) ^ 2) := by
        rw [hNdef, Work.BoseBoxFix.normB, Work.BoseKinLoc.sqNormB]
      have hz : (∫ x in Submission.BoseGases.abox n (pL v μ),
          (Φ x) ^ 2) = 0 := by rw [← hNv, hN0]
      exact (MeasureTheory.integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg (Φ x))
        hfint).mp hz
    have hF0 : Fterm = 0 := by
      rw [hFtermdef, MeasureTheory.integral_congr_ae (by
        filter_upwards [hΦae] with x hx
        simp only [Pi.zero_apply] at hx ⊢
        rw [hx, zero_mul])]
      simp
    rw [hF0, hN0]
    have hRHS : 0 ≤ Work.BoseFixB1B.sbKinCube v μ u (Φ : Submission.BoseGases.X n → ℝ)
        + (1 / 2) * W₂ * Xp := by
      have h2 : 0 ≤ (1 / 2) * W₂ * Xp := by positivity
      linarith [hkin, h2]
    linarith [hRHS]
  · -- ## the main case `N > 0`
    have hNpos : 0 < N := lt_of_le_of_ne hNnn (Ne.symm hN0)
    have hτnn : 0 ≤ τ := by
      rw [hτdef, flatTau]
      rw [flatMass_pL_eq_normB]
      rw [← hSdef, ← hκdef, ← hNdef]
      exact div_nonneg hSnn (mul_nonneg hκnn hNnn)
    have hfin := flatZeroFinalArith (μ := μ) (W₁ := W₁) (W₂ := W₂) (κ := κ) (A := A) (τ := τ)
      (D := D) (Xp := Xp) (Fterm := Fterm) (N := N) (Cχ := Cχ) (c₁ := 1 / 16) (Cp := Cp)
      (errb := errb) hμ hτnn hκnn hApos hCχnn hW₁nn hW₁₂ hW₂nn hD0 hXpnn hNpos
      (by norm_num) (by norm_num) (by linarith [hW₁₂, hW₁nn]) hFrow hDle hY hPay
    linarith [hfin, hkin]

end Work.BoseB1Cube.CubeFlat
