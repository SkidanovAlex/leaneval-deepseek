import ChallengeDeps
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB1Cube.sbWordCube_ge_crudeSmallWin
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB1Cube.smallWinGapArmGen` — the gap arm of the small-window rows, at a general
# count window `[Cn·μ|B|, 2Cn·μ|B|]` and at the corpus vocabulary

This is the **general-window** form of the PROVED `Work.BoseB1Cube.cubeSmallWinGapArm`, phrased in
the `PerBoxNames` vocabulary (`bSide, bD, bA, bV, bW, bQ`) instead of the `PB*` abbreviations, and
with both demand rows replaced by the single row (FS `thm:smallbox`, item (1))

    (1/18)·μ·(n/|B(u)|)·∬w_{1,B(u)}   ≤   sbWordCube v h μ u Ψ ,

under the count window `Cn·μ·|B(u)| ≤ n ≤ 2·Cn·μ·|B(u)|` with a general `Cn ≥ 4`, the small-window
hypothesis `μ·∬w_{1,B(u)} ≤ (a v)`, the normalised state `∫Ψ² = 1` and the *supply*
`c₀ ≤ n₊(B(u))` on the box-excited count.

## Why it is true (and how the constants are spent)

`sbWordCube = sbKinCube + sbPot`, `sbKinCube = bGapCoeff·n₊ + cubeSpectral` with
`cubeSpectral ≥ 0`, and `sbPot = pairSum − μ·fibSum` with `pairSum ≥ 0`
(`Work.BoseFixB1.sbPot_split`, PROVED).  So only two objects can hurt: the fibre line `−μ·fibSum`
and the demand `(1/18)μ(n/|B|)W`.

* the manifest fibre bound `Work.BoseFixB1S.fibSum_le_manifest` (PROVED) gives
  `fibSum ≤ (W/V)·S + Cm·(a v)·(√(n₊·(W/V)·S) + n₊)`, and Young's inequality turns the cross
  term into `εη·n₊ + θ/(4εη)`;
* the gap column `bGapCoeff·n₊` with `bGapCoeff ≥ (Kg + extra)·μ(a v)`
  (`Work.BoseB1Cube.bGapCoeff_gate`, PROVED — any prescribed `Kg` at a smaller `ε₀`) pays BOTH the
  fibre column (`Kg ≥ (εη+1)Cm`) and the `S`-column `μ(W/V)S`, the latter via
  `S ≤ n·∫Ψ² = n`, `n ≤ 2Cn·μ·V` and `μW ≤ (a v)`, which give `μ(W/V)S ≤ 2Cn·(a v)·μ`;
* the supply `n₊ ≥ c₀` then leaves the surplus `extra·c₀·(a v)·μ`, and the demand is at most
  `(1/18)·2Cn·μ·(a v) = (Cn/9)·μ·(a v)`, so `extra := (4Cn + Cn/9)/c₀` closes the row exactly.

Nothing in the proof is sharp; the only thresholds are those of `bGapCoeff_gate` and of the regime
`Work.BoseFixB1.regime_sideAt_ge`.
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

/-- **The pure-real arithmetic of the general-window gap arm.**

With `θ := (W₁/V₁)·S₁`, `fib ≤ θ + Cm·A·(√(Q θ) + Q)`, Young `√(Q θ) ≤ εη·Q + θ/(4εη)`, the gap
column `bg·Q ≥ (Kg + extra)·μA·Q ≥ μ·Cm·A·(εη+1)·Q + extra·μA·Q` (so the fibre column is paid *and*
the surplus `extra·μA·Q` is left over), the supply `c₀·J ≤ Q`, and the `S`-column closed by
`μ·W₁ ≤ A`, `S₁ ≤ n·J`, `n ≤ Kc·μ·V₁`:

    (extra·c₀ − 2·Kc)·A·μ·J ≤ Wd .

This is `Work.BoseB1Cube.gapArithGen` (`Submission/Work/BoseB1Cube/cubeSmallWinGapArm.lean`, where
it is `private`) with the count constant `Kc` and the surplus `extra` left free, so that the
conclusion can be tuned to an arbitrary count window. -/
private theorem gapArithGenCnF {μ Cm A εη Kg bg Q W₁ S₁ V₁ fib pp spec Wd n J extra c₀ Kc : ℝ}
    (hμ : 0 < μ) (hCm0 : 0 ≤ Cm) (hA0 : 0 ≤ A) (hεηpos : 0 < εη)
    (hεηbig : Cm * A / 4 ≤ εη) (hKg : (εη + 1) * Cm ≤ Kg)
    (hextra : 0 ≤ extra) (hbg : (Kg + extra) * (μ * A) ≤ bg)
    (hQ : 0 ≤ Q) (hW : 0 ≤ W₁) (hS : 0 ≤ S₁) (hV : 0 < V₁) (hJ : 0 ≤ J) (hKc : 0 ≤ Kc)
    (hc₀ : 0 < c₀) (hQJ : c₀ * J ≤ Q)
    (hfib : fib ≤ (W₁ / V₁) * S₁ + Cm * A * (Real.sqrt (Q * ((W₁ / V₁) * S₁)) + Q))
    (hwd : Wd = (bg * Q + spec) + (-(μ * fib) + pp))
    (hpp : 0 ≤ pp) (hspec : 0 ≤ spec)
    (hSle : S₁ ≤ n * J) (hn : n ≤ Kc * μ * V₁) (hWle : μ * W₁ ≤ A) :
    (extra * c₀ - 2 * Kc) * A * μ * J ≤ Wd := by
  have hθ0 : 0 ≤ (W₁ / V₁) * S₁ := mul_nonneg (div_nonneg hW hV.le) hS
  have hVne : V₁ ≠ 0 := ne_of_gt hV
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
  -- the gap column pays the fibre column and leaves the surplus `extra·μA·Q`
  have h4 : μ * Cm * A * (εη + 1) * Q + extra * (μ * A) * Q ≤ bg * Q := by
    have h1 : μ * Cm * A * (εη + 1) + extra * (μ * A) ≤ (Kg + extra) * (μ * A) := by
      have h2 : μ * Cm * A * (εη + 1) = ((εη + 1) * Cm) * (μ * A) := by ring
      have h3' : ((εη + 1) * Cm) * (μ * A) ≤ Kg * (μ * A) :=
        mul_le_mul_of_nonneg_right hKg (mul_nonneg hμ.le hA0)
      linarith [h2, h3', hbg]
    have hle := mul_le_mul_of_nonneg_right h1 hQ
    have hbQ := mul_le_mul_of_nonneg_right hbg hQ
    have heq : (μ * Cm * A * (εη + 1) + extra * (μ * A)) * Q
        = μ * Cm * A * (εη + 1) * Q + extra * (μ * A) * Q := by ring
    linarith [hle, heq, hbQ]
  have h5 : extra * (μ * A) * Q - 2 * (μ * ((W₁ / V₁) * S₁)) ≤ Wd := by
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
  -- the supply `c₀·J ≤ Q` converts the surplus into `extra·c₀·A·μ·J`
  have h7 : extra * c₀ * (A * μ * J) ≤ extra * (μ * A) * Q := by
    have heq : extra * c₀ * (A * μ * J) = extra * (μ * A) * (c₀ * J) := by ring
    rw [heq]
    exact mul_le_mul_of_nonneg_left hQJ (mul_nonneg hextra (mul_nonneg hμ.le hA0))
  have h6' : 2 * (μ * ((W₁ / V₁) * S₁)) ≤ 2 * Kc * (A * μ * J) := by
    have h2 := mul_le_mul_of_nonneg_left h6 (by norm_num : (0 : ℝ) ≤ 2)
    have heq : 2 * Kc * (A * μ * J) = 2 * (Kc * A * μ * J) := by ring
    linarith [h2, heq]
  have hfin : extra * c₀ * (A * μ * J) - 2 * Kc * (A * μ * J) ≤ Wd := by
    linarith [h5, h7, h6']
  have hgoal : (extra * c₀ - 2 * Kc) * A * μ * J
      = extra * c₀ * (A * μ * J) - 2 * Kc * (A * μ * J) := by ring
  linarith [hfin, hgoal]

theorem smallWinGapArmGenF {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) (Cn : ℝ) (hCn : 4 ≤ Cn) (c₀ : ℝ) (hc₀ : 0 < c₀) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        ∀ (n : ℕ) (Ψ : Submission.BoseGases.X n → ℝ) (u : EuclideanSpace ℝ (Fin 3)),
          u ∈ Work.SmallBoxSliding.goodSet (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) μ →
          μ * Work.BoseFixB1.bW v h μ u ≤ _root_.BoseGases.a v →
          ContDiff ℝ (⊤ : ℕ∞) Ψ →
          (∀ᵐ x ∂(MeasureTheory.volume.restrict
              (Submission.BoseGases.abox n (Work.BoseFixB1.bSide v μ))),
            Ψ x ≠ 0 → ∀ i : Fin n, x i ∈ Work.BoseFixB1.bA v μ u) →
          (∫ x in Submission.BoseGases.abox n (Work.BoseFixB1.bSide v μ), (Ψ x) ^ 2) = 1 →
          Cn * μ * Work.BoseFixB1.bV v μ u ≤ (n : ℝ) →
          (n : ℝ) ≤ 2 * Cn * μ * Work.BoseFixB1.bV v μ u →
          c₀ ≤ Work.BoseFixB1.bQ v μ Ψ u →
          (1 / 18) * μ * ((n : ℝ) / Work.BoseFixB1.bV v μ u) * Work.BoseFixB1.bW v h μ u
            ≤ Work.BoseFixB1B.sbWordCube v h μ u Ψ := by
  classical
  set A : ℝ := _root_.BoseGases.a v with hAdef
  have hA0' : 0 < A := hav
  have hA0 : 0 ≤ A := hA0'.le
  have hCn0 : 0 < Cn := by linarith
  -- ## the manifest fibre bound, the regime and the free gap constant
  obtain ⟨Cm, hCm0, hman⟩ :=
    Work.BoseFixB1S.fibSum_le_manifest (v := v) h hv hv1 hvrad hR hv_supp hav
      (M := Work.BoseBox.mValue) (by norm_num [Work.BoseBox.mValue])
  obtain ⟨ε_r, hε_r, hreg⟩ := Work.BoseFixB1.regime_sideAt_ge (v := v) hav hR
  set εη : ℝ := max (Cm * A / 4) 1 with hεηdef
  have hεηpos : 0 < εη := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hεηbig : Cm * A / 4 ≤ εη := le_max_left _ _
  set Kg : ℝ := (εη + 1) * Cm with hKgdef
  have hKg0 : 0 ≤ Kg := by rw [hKgdef]; positivity
  set extra : ℝ := (4 * Cn + Cn / 9) / c₀ with hextradef
  have hextra0 : 0 ≤ extra := by
    rw [hextradef]
    exact div_nonneg (by linarith) hc₀.le
  have hextra1 : extra * c₀ = 4 * Cn + Cn / 9 := by
    rw [hextradef]; field_simp
  have hkey : extra * c₀ - 2 * (2 * Cn) = Cn / 9 := by rw [hextra1]; ring
  obtain ⟨ε_g, hε_g, hgate⟩ :=
    Work.BoseB1Cube.bGapCoeff_gate (v := v) hav (Kg + extra) (by linarith [hKg0, hextra0])
  refine ⟨min ε_g ε_r, lt_min hε_g hε_r, ?_⟩
  intro μ hAdm n Ψ u hu hμW hΨc hsupp hΨnorm hn1 hn2 hQc
  have hμ : 0 < μ := hAdm.1
  have hμ0 : 0 ≤ μ := hμ.le
  have hℓ : 0 < Work.BoseFixB1.bSide v μ := Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < Work.BoseFixB1.bD v μ := Work.BoseFixB1.adm_d_pos hAdm
  have hM : 1 ≤ Work.BoseFixB1.bM v μ := by
    show (1 : ℕ) ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
    rw [Work.BoseFixB1.M_eq_mValue, Work.BoseBox.mValue]
    norm_num
  have hVpos : 0 < Work.BoseFixB1.bV v μ u :=
    Work.BoseFixB1.boxMass_pos_of_goodSet hℓ hd hμ hu
  have hV0 : 0 ≤ Work.BoseFixB1.bV v μ u := hVpos.le
  have hWnn : 0 ≤ Work.BoseFixB1.bW v h μ u :=
    Work.BoseFixB1.w1MassB_nonneg h hv hvrad hR hv_supp hℓ hd u
  obtain ⟨hR16, hRχ⟩ := hreg μ hμ (le_trans hAdm.2.1 (min_le_right _ _))
  have hgateμ : (Kg + extra) * (μ * A) ≤ Work.BoseFixB1.bGapCoeff v μ := by
    rw [hAdef]
    exact hgate μ (Work.BoseFixB1.Adm.mono hAdm (min_le_left _ _))
  -- ## the bridge `bW = boxM1`
  have hbridge : Work.BoseFixB1.bW v h μ u
      = Work.BoseFixB1S.boxM1 (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u)
          (Submission.BoseGases.wSmall1Pair h (Work.BoseFixB1.bM v μ)
            (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) u) :=
    Work.BoseB1Cube.PBW_eq_boxM1 (v := v) (h := h) (μ := μ) hℓ hd hM (u := u)
  have hWle : μ * Work.BoseFixB1S.boxM1 (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u)
      (Submission.BoseGases.wSmall1Pair h (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
        (Work.BoseFixB1.bD v μ) u) ≤ A := by
    rw [← hbridge]
    exact hμW
  -- ## the count split of the state
  have hsplitC := Work.BoseFixB1S.b1sCountSplit (N := n) (ℓ := Work.BoseFixB1.bSide v μ)
    (volA := Work.BoseFixB1.bV v μ u) hℓ hVpos
    (Work.SmallBoxSliding.measurableSet_dlBox (Work.BoseFixB1.bSide v μ)
      (Work.BoseFixB1.bD v μ) u)
    (by simp only [Work.BoseFixB1.bV, Work.SmallBoxSliding.boxMass_eq_measureReal,
        MeasureTheory.Measure.real_def])
    (Work.SmallBoxSliding.dlBox_subset_acube (Work.BoseFixB1.bSide v μ)
      (Work.BoseFixB1.bD v μ) u) hΨc.continuous hsupp
  have hSle : Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
      (Work.BoseFixB1.bA v μ u) Ψ
      ≤ (n : ℝ) * (∫ x in Submission.BoseGases.abox n (Work.BoseFixB1.bSide v μ), (Ψ x) ^ 2) := by
    have hQ0' : 0 ≤ Work.BoseFixB1S.boxQCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
        (Work.BoseFixB1.bA v μ u) Ψ :=
      Finset.sum_nonneg (fun i _ => integral_nonneg (fun x => sq_nonneg _))
    have hsplitC' : Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1.bV v μ u)
          (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u) Ψ
        + Work.BoseFixB1S.boxQCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
          (Work.BoseFixB1.bA v μ u) Ψ
        = (n : ℝ) * (∫ x in Submission.BoseGases.abox n (Work.BoseFixB1.bSide v μ),
            (Ψ x) ^ 2) := hsplitC
    linarith [hsplitC', hQ0']
  -- ## the word identity
  have hsplit := Work.BoseFixB1.sbPot_split (v := v) (h := h) (R := R) hv_supp hR hv hvrad hv1
    hAdm hΨc.continuous u hR16 hRχ
  have hword : Work.BoseFixB1B.sbWordCube v h μ u Ψ
      = (Work.BoseFixB1.bGapCoeff v μ * Work.UBBInputs8.cnPlusBoxInd (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bA v μ u) (Work.BoseFixB1.bV v μ u) Ψ
          + Work.BoseFixB1B.cubeSpectral v μ Ψ u)
        + (-(μ * Work.BoseFixB1.fibSum h (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bD v μ) u Ψ)
            + Work.BoseFixB1.pairSum v (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                (Work.BoseFixB1.bD v μ) u Ψ) := by
    rw [Work.BoseFixB1B.sbWordCube, Work.BoseFixB1B.sbKinCube, hsplit]
    simp only [Work.BoseFixB1.bM, Work.BoseFixB1.bSide, Work.BoseFixB1.bD]
  -- ## the inputs of the arithmetic
  have hJ0 : 0 ≤ ∫ x in Submission.BoseGases.abox n (Work.BoseFixB1.bSide v μ), (Ψ x) ^ 2 :=
    integral_nonneg (fun x => sq_nonneg _)
  have hpair : 0 ≤ Work.BoseFixB1.pairSum v (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
      (Work.BoseFixB1.bD v μ) u Ψ := Work.BoseFixB1.pairSum_nonneg hv u Ψ
  have hspec : 0 ≤ Work.BoseFixB1B.cubeSpectral v μ Ψ u := by
    rw [Work.BoseFixB1B.cubeSpectral]
    exact Work.BoseFixB1.tBwordKinInd_nonneg Ψ
  have hQnn : 0 ≤ Work.UBBInputs8.cnPlusBoxInd (Work.BoseFixB1.bSide v μ)
      (Work.BoseFixB1.bA v μ u) (Work.BoseFixB1.bV v μ u) Ψ :=
    Work.BoseFixB1S.cnPlusBoxInd_nonneg _ _ _ _
  have hQJ : c₀ * (∫ x in Submission.BoseGases.abox n (Work.BoseFixB1.bSide v μ), (Ψ x) ^ 2)
      ≤ Work.UBBInputs8.cnPlusBoxInd (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u)
          (Work.BoseFixB1.bV v μ u) Ψ := by
    rw [hΨnorm, mul_one]
    exact hQc
  -- ## the arithmetic
  have hcr := gapArithGenCnF (μ := μ) (Cm := Cm) (A := A) (εη := εη) (Kg := Kg)
    (bg := Work.BoseFixB1.bGapCoeff v μ)
    (Q := Work.UBBInputs8.cnPlusBoxInd (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u)
      (Work.BoseFixB1.bV v μ u) Ψ)
    (W₁ := Work.BoseFixB1S.boxM1 (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u)
      (Submission.BoseGases.wSmall1Pair h (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
        (Work.BoseFixB1.bD v μ) u))
    (S₁ := Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
      (Work.BoseFixB1.bA v μ u) Ψ)
    (V₁ := Work.BoseFixB1.bV v μ u)
    (fib := Work.BoseFixB1.fibSum h (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
      (Work.BoseFixB1.bD v μ) u Ψ)
    (pp := Work.BoseFixB1.pairSum v (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
      (Work.BoseFixB1.bD v μ) u Ψ)
    (spec := Work.BoseFixB1B.cubeSpectral v μ Ψ u)
    (Wd := Work.BoseFixB1B.sbWordCube v h μ u Ψ)
    (n := (n : ℝ))
    (J := ∫ x in Submission.BoseGases.abox n (Work.BoseFixB1.bSide v μ), (Ψ x) ^ 2)
    (Kc := 2 * Cn)
    hμ hCm0 hA0 hεηpos hεηbig (le_of_eq hKgdef.symm) hextra0 hgateμ
    hQnn (by rw [← hbridge]; exact hWnn)
    (Finset.sum_nonneg (fun i _ => integral_nonneg (fun x => sq_nonneg _)))
    hVpos hJ0 (by linarith) hc₀ hQJ
    (hman (μ := μ) hℓ hd hR16 hRχ u hVpos hΨc.continuous)
    hword hpair hspec hSle hn2 hWle
  -- ## the demand row
  have hmain : (Cn / 9) * A * μ ≤ Work.BoseFixB1B.sbWordCube v h μ u Ψ := by
    rw [hkey] at hcr
    rw [hΨnorm, mul_one] at hcr
    exact hcr
  have hfac : (1 / 18) * μ * ((n : ℝ) / Work.BoseFixB1.bV v μ u) * Work.BoseFixB1.bW v h μ u
      ≤ (Cn / 9) * A * μ := by
    have hratio : (n : ℝ) / Work.BoseFixB1.bV v μ u ≤ 2 * Cn * μ := by
      rw [div_le_iff₀ hVpos]
      linarith [hn2]
    have h2Cn0 : 0 ≤ 2 * Cn * μ := by
      have h1 : (0 : ℝ) ≤ Cn := hCn0.le
      positivity
    have h1 : ((n : ℝ) / Work.BoseFixB1.bV v μ u) * (μ * Work.BoseFixB1.bW v h μ u)
        ≤ (2 * Cn * μ) * A := mul_le_mul hratio hμW (mul_nonneg hμ0 hWnn) h2Cn0
    have heq : (1 / 18) * μ * ((n : ℝ) / Work.BoseFixB1.bV v μ u) * Work.BoseFixB1.bW v h μ u
        = (1 / 18) * (((n : ℝ) / Work.BoseFixB1.bV v μ u)
            * (μ * Work.BoseFixB1.bW v h μ u)) := by ring
    have h3 : (1 / 18) * ((2 * Cn * μ) * A) = (Cn / 9) * A * μ := by ring
    calc (1 / 18) * μ * ((n : ℝ) / Work.BoseFixB1.bV v μ u) * Work.BoseFixB1.bW v h μ u
        = (1 / 18) * (((n : ℝ) / Work.BoseFixB1.bV v μ u)
            * (μ * Work.BoseFixB1.bW v h μ u)) := heq
      _ ≤ (1 / 18) * ((2 * Cn * μ) * A) := mul_le_mul_of_nonneg_left h1 (by norm_num)
      _ = (Cn / 9) * A * μ := h3
  linarith [hfac, hmain]

end Work.BoseB1Cube

end
