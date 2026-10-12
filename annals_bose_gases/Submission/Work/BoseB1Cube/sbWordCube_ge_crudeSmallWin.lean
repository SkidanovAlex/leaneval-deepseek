import ChallengeDeps
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB1Cube.NomRowDefs
import Submission.Work.BoseB1Cube.bM2_le_two_mul_bW
import Submission.Work.BoseB1Cube.boxMassGateLower
import Submission.Work.BoseB1Cube.flatArm37RowOneBadL
import Submission.Work.BoseB1Cube.flatArm37RowOneGoodLower
import Submission.Work.BoseB1Cube.gammaSmallAt
import Submission.Work.BoseB1Cube.sbWordCubePairArm
import Submission.Work.BoseB1Cube.smallRowsBundle
import Submission.Work.BoseFixB1.boxM1_le_aV
import Submission.Work.BoseFixB1S.SharpMassLedger
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB1Cube.sbWordCube_ge_crudeSmallWin` — the crude small-window lower bound at a
# prescribed count window `n ≤ Cn·μ|B(u)|`

This is the **small-window crude row** of the per-box ledger `Work.BoseB1Cube.nomRowSqWindowRow`
(see `FINDING_nomRowSqWindowRow_session4.md` §1): under the small-window hypothesis
`μ·PBW h μ u ≤ a v` the matched word `sbWordCube` dominates a *negative* multiple of the box mass,

    sbWordCube v h μ u Ψ ≥ −K·(Cn·(a v)·μ)·∫_{B(u)}Ψ²        for every `n ≤ Cn·μ·|B(u)|`,

so that the demand's positive part `≤ ¼Cn²μ²W ≤ ¼Cn²·(a v)·μ·∫Ψ²` can be absorbed by the free
constant `Ct` of the per-box credit.

Nothing here is sharp: the proof is the `S`-column of the manifest fibre bound
`Work.BoseFixB1S.fibSum_le_manifest` (`fibSum ≤ (W/|B|)·S + Cm·(a v)(√(n₊·(W/|B|)S) + n₊)`), in
which

* the Young split `√(xy) ≤ ε·x + y/(4ε)` of the cross term is **paid by the free gap coefficient**
  (`Work.BoseB1Cube.bGapCoeff_gate`: `Kg·μ(a v) ≤ bGapCoeff v μ` for *every* prescribed `Kg`),
* the remaining `S`-column `−2μ·(W/|B|)·S` is closed by the two elementary bounds
  `S ≤ n·∫Ψ²` (`b1sCountSplit`, the excited count is `≥ 0`) and `μ·W ≤ (a v)`, which give
  `μ·(W/|B|)·S ≤ (a v)·Cn·μ·∫Ψ²`.

This generalises the `crude` bound of the PROVED `Work.BoseB1Cube.rowsOfSmallWindow` from its
`n ≤ 8μ|B(u)|` window to the target's `n ≤ Cn·μ|B(u)|`; the general case is the *weaker*
hypothesis, so the constant must be allowed to grow with `Cn` — which is exactly the shape of the
target.  The output constant is `K = 2`.

All constants (`Cm`, `εη`, `Kg`, `K = 2`) are fixed, independent of `μ`, `u`, `n` and the state;
only `ε₀` is chosen small (the min of the thresholds of the gap gate and of the box regime).
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
set_option maxHeartbeats 4000000

/-- **The pure-real arithmetic of the crude count-window bound.**

With `θ := (W₁/V₁)·S₁`, `fib ≤ θ + Cm·A·(√(n₊θ) + n₊)`, Young `√(n₊θ) ≤ εη·n₊ + θ/(4εη)`, the gap
column `bg·n₊ ≥ Kg·μ·A·n₊ ≥ μ·Cm·A·(εη+1)·n₊`, and the `S`-column closed by `μ·W₁ ≤ A`,
`S₁ ≤ n·∫Ψ²`, `n ≤ Cn·μ·V₁`:

    Wd = (bg·n₊ + spec) + (−(μ·fib) + pp)  ≥  −2·Cn·A·μ·∫Ψ² .

This is `crudeArith` of `Submission/Work/BoseB1Cube/rowsOfSmallWindow.lean` with the count window
`n ≤ 8μV₁` relaxed to `n ≤ Cn·μ·V₁` (hence the constant `Cn`) — i.e. precisely the `S`-column
`−2μ·(W₁/V₁)·S₁ ≥ −2·Cn·A·μ·∫Ψ²`. -/
private theorem crudeArithGen {μ Cm A εη Kg bg Q W₁ S₁ V₁ fib pp spec Wd n J Kc : ℝ}
    (hμ : 0 < μ) (hCm0 : 0 ≤ Cm) (hA0 : 0 ≤ A) (hεηpos : 0 < εη)
    (hεηbig : Cm * A / 4 ≤ εη) (hKg : (εη + 1) * Cm ≤ Kg) (hbg : Kg * (μ * A) ≤ bg)
    (hQ : 0 ≤ Q) (hW : 0 ≤ W₁) (hS : 0 ≤ S₁) (hV : 0 < V₁) (hJ : 0 ≤ J) (hKc : 0 ≤ Kc)
    (hfib : fib ≤ (W₁ / V₁) * S₁ + Cm * A * (Real.sqrt (Q * ((W₁ / V₁) * S₁)) + Q))
    (hwd : Wd = (bg * Q + spec) + (-(μ * fib) + pp))
    (hpp : 0 ≤ pp) (hspec : 0 ≤ spec)
    (hSle : S₁ ≤ n * J) (hn : n ≤ Kc * μ * V₁) (hWle : μ * W₁ ≤ A) :
    - 2 * Kc * A * μ * J ≤ Wd := by
  have hθ0 : 0 ≤ (W₁ / V₁) * S₁ := mul_nonneg (div_nonneg hW hV.le) hS
  have hVne : V₁ ≠ 0 := ne_of_gt hV
  have hεηne : εη ≠ 0 := ne_of_gt hεηpos
  -- the Young inequality
  have hyoung : Real.sqrt (Q * ((W₁ / V₁) * S₁)) ≤ εη * Q + ((W₁ / V₁) * S₁) / (4 * εη) := by
    have hR : 0 ≤ εη * Q + ((W₁ / V₁) * S₁) / (4 * εη) :=
      add_nonneg (mul_nonneg hεηpos.le hQ) (div_nonneg hθ0 (by positivity))
    have hle : Q * ((W₁ / V₁) * S₁) ≤ (εη * Q + ((W₁ / V₁) * S₁) / (4 * εη)) ^ 2 := by
      have hid : (εη * Q + ((W₁ / V₁) * S₁) / (4 * εη)) ^ 2 - Q * ((W₁ / V₁) * S₁)
          = (εη * Q - ((W₁ / V₁) * S₁) / (4 * εη)) ^ 2 := by
        field_simp
        ring
      nlinarith [sq_nonneg (εη * Q - ((W₁ / V₁) * S₁) / (4 * εη)), hid]
    calc Real.sqrt (Q * ((W₁ / V₁) * S₁))
        ≤ Real.sqrt ((εη * Q + ((W₁ / V₁) * S₁) / (4 * εη)) ^ 2) := Real.sqrt_le_sqrt hle
      _ = εη * Q + ((W₁ / V₁) * S₁) / (4 * εη) := Real.sqrt_sq hR
  -- the fibre column, after Young
  have hfib2 : fib ≤ (1 + Cm * A / (4 * εη)) * ((W₁ / V₁) * S₁) + Cm * A * (εη + 1) * Q := by
    have h1 : (W₁ / V₁) * S₁ + Cm * A * (Real.sqrt (Q * ((W₁ / V₁) * S₁)) + Q)
        ≤ (W₁ / V₁) * S₁ + Cm * A * ((εη * Q + ((W₁ / V₁) * S₁) / (4 * εη)) + Q) := by
      have h2 : Real.sqrt (Q * ((W₁ / V₁) * S₁)) + Q
          ≤ εη * Q + ((W₁ / V₁) * S₁) / (4 * εη) + Q := by linarith [hyoung]
      have h2b := mul_le_mul_of_nonneg_left h2 (mul_nonneg hCm0 hA0)
      linarith [h2b]
    have h3 : (W₁ / V₁) * S₁ + Cm * A * ((εη * Q + ((W₁ / V₁) * S₁) / (4 * εη)) + Q)
        = (1 + Cm * A / (4 * εη)) * ((W₁ / V₁) * S₁) + Cm * A * (εη + 1) * Q := by ring
    linarith [hfib, h1, h3]
  have hcoef : 1 + Cm * A / (4 * εη) ≤ 2 := by
    have h5 : Cm * A / (4 * εη) ≤ 1 := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < 4 * εη)]
      linarith [hεηbig]
    linarith
  have h3 : μ * fib ≤ 2 * (μ * ((W₁ / V₁) * S₁)) + μ * Cm * A * (εη + 1) * Q := by
    have h1 : μ * fib
        ≤ μ * ((1 + Cm * A / (4 * εη)) * ((W₁ / V₁) * S₁) + Cm * A * (εη + 1) * Q) :=
      mul_le_mul_of_nonneg_left hfib2 hμ.le
    have h2 : μ * ((1 + Cm * A / (4 * εη)) * ((W₁ / V₁) * S₁))
        ≤ μ * (2 * ((W₁ / V₁) * S₁)) := by
      have h2a := mul_le_mul_of_nonneg_left hcoef hθ0
      exact mul_le_mul_of_nonneg_left (by linarith [h2a]) hμ.le
    linarith [h1, h2]
  have h4 : μ * Cm * A * (εη + 1) * Q ≤ bg * Q := by
    have h1 : μ * Cm * A * (εη + 1) ≤ Kg * (μ * A) := by
      have h2 : μ * Cm * A * (εη + 1) = ((εη + 1) * Cm) * (μ * A) := by ring
      rw [h2]; exact mul_le_mul_of_nonneg_right hKg (mul_nonneg hμ.le hA0)
    have h2 := mul_le_mul_of_nonneg_right hbg hQ
    have h3b := mul_le_mul_of_nonneg_right h1 hQ
    linarith [h2, h3b]
  have h5 : - 2 * (μ * ((W₁ / V₁) * S₁)) ≤ Wd := by
    rw [hwd]
    linarith [h3, h4, hpp, hspec]
  -- the `S`-column, closed by `μ·W₁ ≤ A` and the count window `n ≤ Kc·μ·V₁`
  have h6 : μ * ((W₁ / V₁) * S₁) ≤ Kc * A * μ * J := by
    have hdiv : S₁ / V₁ ≤ Kc * μ * J := by
      have h1 : S₁ / V₁ ≤ (n * J) / V₁ := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right hSle (by positivity)
      have h2 : (n * J) / V₁ ≤ (Kc * μ * V₁) * J / V₁ := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hn hJ) (by positivity)
      have h3b : (Kc * μ * V₁) * J / V₁ = Kc * μ * J := by
        rw [div_eq_mul_inv]; field_simp
      linarith [h1, h2, h3b]
    have hθ : (W₁ / V₁) * S₁ = W₁ * (S₁ / V₁) := by ring
    rw [hθ]
    calc μ * (W₁ * (S₁ / V₁)) ≤ μ * (W₁ * (Kc * μ * J)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hdiv hW) hμ.le
      _ = Kc * μ * J * (μ * W₁) := by ring
      _ ≤ Kc * μ * J * A := mul_le_mul_of_nonneg_left hWle (by positivity)
      _ = Kc * A * μ * J := by ring
  linarith [h5, h6]

theorem sbWordCube_ge_crudeSmallWin {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) (Cn : ℝ) (hCn : 1 ≤ Cn) :
    ∃ ε₀ K : ℝ, 0 < ε₀ ∧ 0 ≤ K ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ u : EuclideanSpace ℝ (Fin 3), u ∈ Work.SmallBoxSliding.goodSet
          (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBd v μ) μ →
        μ * Work.BoseFixB1B.PBW h μ u ≤ _root_.BoseGases.a v →
        ∀ (n : ℕ) (Ψ : Submission.BoseGases.X n → ℝ), ContDiff ℝ (⊤ : ℕ∞) Ψ →
          Work.BoseFixB1B.InBox v μ u Ψ →
          (n : ℝ) ≤ Cn * μ * Work.BoseFixB1B.PBBV v μ u →
          -K * (Cn * (_root_.BoseGases.a v) * μ)
              * (∫ x in Submission.BoseGases.abox n (Work.BoseFixB1B.PBℓ v μ), (Ψ x) ^ 2)
            ≤ Work.BoseFixB1B.sbWordCube v h μ u Ψ := by
  classical
  set A : ℝ := _root_.BoseGases.a v with hAdef
  have hA0 : 0 < A := hav
  -- ## the ingredients
  obtain ⟨Cm, hCm0, hman⟩ :=
    Work.BoseFixB1S.fibSum_le_manifest (v := v) h hv hv1 hvrad hR hv_supp hav
      (M := Work.BoseBox.mValue) (by norm_num [Work.BoseBox.mValue])
  obtain ⟨ε_r, hε_r, hreg⟩ := Work.BoseFixB1.regime_sideAt_ge (v := v) hav hR
  set εη : ℝ := max (Cm * A / 4) 1 with hεηdef
  have hεηpos : 0 < εη := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hεηbig : Cm * A / 4 ≤ εη := le_max_left _ _
  set Kg : ℝ := (εη + 1) * Cm with hKgdef
  have hKg0 : 0 ≤ Kg := by rw [hKgdef]; positivity
  obtain ⟨ε_g, hε_g, hgate⟩ := Work.BoseB1Cube.bGapCoeff_gate (v := v) hav Kg hKg0
  -- ## the constants of the target (`K = 2`)
  refine ⟨min ε_g ε_r, 2, lt_min hε_g hε_r, by norm_num, ?_⟩
  intro μ hAdm u hu hμW n Ψ hΨ hIn hn
  have hμ : 0 < μ := hAdm.1
  have hℓ : 0 < Work.BoseFixB1B.PBℓ v μ := Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < Work.BoseFixB1B.PBd v μ := Work.BoseFixB1.adm_d_pos hAdm
  have hM : 1 ≤ Work.BoseFixB1B.PBM v μ := by
    show (1 : ℕ) ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
    rw [Work.BoseFixB1.M_eq_mValue, Work.BoseBox.mValue]
    norm_num
  have hVpos : 0 < Work.BoseFixB1B.PBBV v μ u :=
    Work.BoseFixB1.boxMass_pos_of_goodSet hℓ hd hμ hu
  have hWnn : 0 ≤ Work.BoseFixB1B.PBW h μ u :=
    Work.BoseFixB1.w1MassB_nonneg h hv hvrad hR hv_supp hℓ hd u
  -- the regime facts (`R ≤ ℓd/16`, `R ≤ ℓχ₀`) and the free gap gate
  obtain ⟨hR16, hRχ⟩ := hreg μ hμ (le_trans hAdm.2.1 (min_le_right _ _))
  have hgateμ : Kg * (μ * A) ≤ Work.BoseFixB1.bGapCoeff v μ := by
    rw [hAdef]
    exact hgate μ (Work.BoseFixB1.Adm.mono hAdm (min_le_left _ _))
  -- the bridge `boxM1 = PBW`
  have hbridge : Work.BoseFixB1S.boxM1 (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBB v μ u)
      (Submission.BoseGases.wSmall1Pair h (Work.BoseFixB1B.PBM v μ) (Work.BoseFixB1B.PBℓ v μ)
        (Work.BoseFixB1B.PBd v μ) u) = Work.BoseFixB1B.PBW h μ u :=
    (Work.BoseB1Cube.PBW_eq_boxM1 (v := v) (h := h) (μ := μ) hℓ hd hM (u := u)).symm
  have hWle : μ * Work.BoseFixB1S.boxM1 (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBB v μ u)
      (Submission.BoseGases.wSmall1Pair h (Work.BoseFixB1B.PBM v μ) (Work.BoseFixB1B.PBℓ v μ)
        (Work.BoseFixB1B.PBd v μ) u) ≤ A := by
    rw [hbridge]; exact hμW
  -- ## the fibres, the count split and the word identity
  have hsplitC := Work.BoseFixB1S.b1sCountSplit (N := n) (ℓ := Work.BoseFixB1B.PBℓ v μ)
    (volA := Work.BoseFixB1B.PBBV v μ u) hℓ hVpos
    (Work.SmallBoxSliding.measurableSet_dlBox _ _ _)
    (by simp only [Work.BoseFixB1B.PBBV, Work.SmallBoxSliding.boxMass_eq_measureReal,
      MeasureTheory.Measure.real_def])
    (Work.SmallBoxSliding.dlBox_subset_acube _ _ _) hΨ.continuous hIn
  have hSle : Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1B.PBBV v μ u) (Work.BoseFixB1B.PBℓ v μ)
      (Work.BoseFixB1B.PBB v μ u) Ψ
      ≤ (n : ℝ) * (∫ x in Submission.BoseGases.abox n (Work.BoseFixB1B.PBℓ v μ), (Ψ x) ^ 2) := by
    have hQ0' : 0 ≤ Work.BoseFixB1S.boxQCount (Work.BoseFixB1B.PBBV v μ u)
        (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBB v μ u) Ψ :=
      Finset.sum_nonneg (fun i _ => integral_nonneg (fun x => sq_nonneg _))
    linarith [hsplitC, hQ0']
  have hfib := hman (μ := μ) hℓ hd hR16 hRχ u hVpos hΨ.continuous
  have hsplit := Work.BoseFixB1.sbPot_split (v := v) (h := h) (R := R) hv_supp hR hv hvrad hv1
    hAdm hΨ.continuous u hR16 hRχ
  have hpair : 0 ≤ Work.BoseFixB1.pairSum v (Work.BoseFixB1B.PBM v μ) (Work.BoseFixB1B.PBℓ v μ)
      (Work.BoseFixB1B.PBd v μ) u Ψ := Work.BoseFixB1.pairSum_nonneg hv u Ψ
  have hspec : 0 ≤ Work.BoseFixB1B.cubeSpectral v μ Ψ u := by
    rw [Work.BoseFixB1B.cubeSpectral]
    exact Work.BoseFixB1.tBwordKinInd_nonneg Ψ
  have hword1 : Work.BoseFixB1B.sbWordCube v h μ u Ψ
      = Work.BoseFixB1B.sbKinCube v μ u Ψ + Work.BoseFixB1.sbPot h μ u Ψ := rfl
  have hword2 : Work.BoseFixB1B.sbKinCube v μ u Ψ
      = Work.BoseFixB1.bGapCoeff v μ * Work.UBBInputs8.cnPlusBoxInd (Work.BoseFixB1B.PBℓ v μ)
            (Work.BoseFixB1B.PBB v μ u) (Work.BoseFixB1B.PBBV v μ u) Ψ
          + Work.BoseFixB1B.cubeSpectral v μ Ψ u := rfl
  have hword3 : Work.BoseFixB1.sbPot h μ u Ψ
      = -(μ * Work.BoseFixB1.fibSum h (Work.BoseFixB1B.PBM v μ) (Work.BoseFixB1B.PBℓ v μ)
            (Work.BoseFixB1B.PBd v μ) u Ψ)
          + Work.BoseFixB1.pairSum v (Work.BoseFixB1B.PBM v μ) (Work.BoseFixB1B.PBℓ v μ)
              (Work.BoseFixB1B.PBd v μ) u Ψ := hsplit
  have hword : Work.BoseFixB1B.sbWordCube v h μ u Ψ
      = (Work.BoseFixB1.bGapCoeff v μ * Work.UBBInputs8.cnPlusBoxInd (Work.BoseFixB1B.PBℓ v μ)
            (Work.BoseFixB1B.PBB v μ u) (Work.BoseFixB1B.PBBV v μ u) Ψ
          + Work.BoseFixB1B.cubeSpectral v μ Ψ u)
        + (-(μ * Work.BoseFixB1.fibSum h (Work.BoseFixB1B.PBM v μ) (Work.BoseFixB1B.PBℓ v μ)
              (Work.BoseFixB1B.PBd v μ) u Ψ)
            + Work.BoseFixB1.pairSum v (Work.BoseFixB1B.PBM v μ) (Work.BoseFixB1B.PBℓ v μ)
                (Work.BoseFixB1B.PBd v μ) u Ψ) := by
    rw [hword1, hword2, hword3]
  -- ## the crude arithmetic
  have hcr := crudeArithGen (μ := μ) (Cm := Cm) (A := A) (εη := εη) (Kg := Kg)
    (bg := Work.BoseFixB1.bGapCoeff v μ)
    (Q := Work.UBBInputs8.cnPlusBoxInd (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBB v μ u)
      (Work.BoseFixB1B.PBBV v μ u) Ψ)
    (W₁ := Work.BoseFixB1S.boxM1 (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBB v μ u)
      (Submission.BoseGases.wSmall1Pair h (Work.BoseFixB1B.PBM v μ) (Work.BoseFixB1B.PBℓ v μ)
        (Work.BoseFixB1B.PBd v μ) u))
    (S₁ := Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1B.PBBV v μ u) (Work.BoseFixB1B.PBℓ v μ)
      (Work.BoseFixB1B.PBB v μ u) Ψ)
    (V₁ := Work.BoseFixB1B.PBBV v μ u)
    (fib := Work.BoseFixB1.fibSum h (Work.BoseFixB1B.PBM v μ) (Work.BoseFixB1B.PBℓ v μ)
      (Work.BoseFixB1B.PBd v μ) u Ψ)
    (pp := Work.BoseFixB1.pairSum v (Work.BoseFixB1B.PBM v μ) (Work.BoseFixB1B.PBℓ v μ)
      (Work.BoseFixB1B.PBd v μ) u Ψ)
    (spec := Work.BoseFixB1B.cubeSpectral v μ Ψ u)
    (Wd := Work.BoseFixB1B.sbWordCube v h μ u Ψ)
    (n := (n : ℝ))
    (J := ∫ x in Submission.BoseGases.abox n (Work.BoseFixB1B.PBℓ v μ), (Ψ x) ^ 2)
    (Kc := Cn)
    hμ hCm0 hA0.le hεηpos hεηbig (le_of_eq hKgdef.symm) hgateμ
    (Work.BoseFixB1S.cnPlusBoxInd_nonneg _ _ _ _)
    (by rw [hbridge]; exact hWnn)
    (Finset.sum_nonneg (fun i _ => integral_nonneg (fun x => sq_nonneg _)))
    hVpos (integral_nonneg (fun x => sq_nonneg _)) (le_trans zero_le_one hCn)
    hfib hword hpair hspec hSle hn hWle
  linarith [hcr]

end Work.BoseB1Cube
