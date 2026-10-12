import ChallengeDeps
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.BoseB1Cube.flatArm37RowOneBadL
import Submission.Work.BoseB1Cube.rowOneArith
import Submission.Work.BoseFixB1B.bandPairLe
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB1Cube.flatArm37RowNode` — the FLAT ARM of the small-window row

The row of `Work.BoseB1Cube.SmallWinProp` at the frozen box window
`[Cn·μ·|B(u)|, 2·Cn·μ·|B(u)|]` (`Cn ≥ 4`), the small window `μ·∬w_{1,B(u)} ≤ a v`, the in-box
normalisation `∫Ψ² = 1`, the near-condensate hypothesis `bQ < 10⁻⁶` and the **flat-arm
hypothesis** `Work.BoseB1Cube.FlatArm37 v h μ n Ψ u` (the pair kernel is `(10/37)`-condensed).
Nothing else: in particular **no box-size gate** `12 ≤ μ·|B(u)|`.

**Where the gate goes.**  The ledger itself (`rowOneLedgerF`/`rowOneMainF`, the shape of the PROVED
`Work.BoseB1Cube.flatArm37RowOneGoodLower`) needs the gate in exactly one place: `rowOneArith`'s
`12 ≤ X`, `X = μ·|B(u)|`.  Without it the geometry collapses: at `μ·|B(u)| < 12` the sliding box is
a sliver at a corner of the big box, so the *whole kernel* vanishes on it
(`Work.BoseB1Cube.chiScaleZeroSmallBox` + `Work.BoseB1Cube.pairSumZeroOfChiScaleZero`), `FlatArm37`
forces `Pc = 0`, `boxFlatSqJensen` gives `S ≤ ∫Ψ²`, and the count split `S + n₊ = n∫Ψ²` contradicts
`n₊ < 10⁻⁶∫Ψ²` because `n ≥ Cn·μ|B(u)| ≥ 4·1`.  So on the bad region the **hypotheses are
inconsistent** — the PROVED `Work.BoseB1Cube.flatArm37RowOneBadL` supplies exactly this `False`.

**Structure of the proof.**  Split on `12 ≤ μ·|B(u)|`.

* **Good case** — the ledger: `sbWordCube = sbKinCube + sbPot` (`rfl` + the PROVED `sbPot_split`),
  `sbKinCube = bGapCoeff·n₊ + cubeSpectral` with `cubeSpectral ≥ 0`
  (`tBwordKinInd_nonneg`), so `sbWordCube ≥ bGapCoeff·n₊ + pairSum − μ·fibSum`.  The pair income is
  `FlatArm37` + the PROVED square-keeping row `Work.BoseFixB1S.Q0C.count_ge`
  (`S² − S ≤ Pc`, legitimate because the state is normalised), the manifest fibre bound is
  `Work.BoseFixB1S.fibSum_le_manifest`, the gap row is the free gate
  `Work.BoseB1Cube.bGapCoeff_gate` (at a constant chosen *after* the manifest constant `Cm`), and
  the extremal arithmetic is the PROVED `Work.BoseB1Cube.rowOneArith`.  The local objects use the
  box volume `U = |B(u)| = boxMass`, which equals the normaliser appearing in the manifest (the
  box masses are the `w1MassB`/`boxM2` inputs of the manifest via
  `Work.BoseB1Cube.PBW_eq_boxM1`, `boxM2_g2_le_v_box` and
  `boxM2_sub_boxM1_nonneg_slidingB1` (`M₁ ≤ M₂`, the slack spent on `L²`)).

* **Bad case** — `Work.BoseB1Cube.flatArm37RowOneBadL` at `c₀ = 10⁻⁶`, applied to the same state:
  the near-condensate hypothesis `bQ < 10⁻⁶` *is* `n₊/N < c₀` at `∫Ψ² = 1`.

**Consumers.**  `Work.BoseB1Cube.SmallWinProp`/`NormNode` (via
`Submission/Work/BoseB1Cube/SmallWinNode.lean`); the import cone is chosen to be compatible with
`smallWinDefs` (which carries the `ConeC` copies of the duplicated `BoseFixB1S` modules).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseB1Cube

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB Work.BoseFixB1
  Work.SmallBoxSliding Work.BoseFixB1B

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

/-- **Young for `√(Qθ)`**: `√(Qθ) ≤ ηQ + θ/(4η)`. -/
private lemma sqrt_mul_le_add_divF {Q θ η : ℝ} (hQ : 0 ≤ Q) (hθ : 0 ≤ θ) (hη : 0 < η) :
    Real.sqrt (Q * θ) ≤ η * Q + θ / (4 * η) := by
  rw [Real.sqrt_mul hQ]
  have h1 : Real.sqrt Q ^ 2 = Q := Real.sq_sqrt hQ
  have h2 : Real.sqrt θ ^ 2 = θ := Real.sq_sqrt hθ
  have h4 : 0 < 4 * η := by linarith
  have key : (Real.sqrt Q * Real.sqrt θ) * (4 * η) ≤ (η * Q + θ / (4 * η)) * (4 * η) := by
    have hh : (η * Q + θ / (4 * η)) * (4 * η) = 4 * η ^ 2 * Q + θ := by field_simp
    rw [hh]
    nlinarith [sq_nonneg (2 * η * Real.sqrt Q - Real.sqrt θ)]
  exact le_of_mul_le_mul_right key h4

/-- **The flat-arm ledger (pure real).** -/
private lemma rowOneLedgerF {S Q J U M1 M2 P F bG sbW Cm a μ : ℝ}
    (hU : 0 < U) (hS : 0 ≤ S) (hQ : 0 ≤ Q) (ha : 0 ≤ a) (hμ : 0 ≤ μ) (hCm : 0 ≤ Cm)
    (hθ : (M1 / U) * S ≤ (M2 / U) * S)
    (hG : (2500 * Cm ^ 2 * a + Cm) * μ * a * Q ≤ bG * Q)
    (hP0 : (M2 / U ^ 2) * S * ((10 / 37) * (S / J - 1)) ≤ P)
    (hF0 : F ≤ (M1 / U) * S + Cm * a * (Real.sqrt (Q * ((M1 / U) * S)) + Q))
    (hY : μ * Cm * a * Real.sqrt (Q * ((M1 / U) * S))
      ≤ μ * (1 / 10000) * ((M1 / U) * S) + μ * (2500 * Cm ^ 2 * a ^ 2) * Q)
    (hbed : bG * Q + P - μ * F ≤ sbW) :
    (M2 / U ^ 2) * (S * ((10 / 37) * (S / J - 1) - (1 + 1 / 10000) * (μ * U))) ≤ sbW := by
  have hF1 : μ * F ≤ μ * ((M1 / U) * S) + μ * Cm * a * Real.sqrt (Q * ((M1 / U) * S))
      + μ * Cm * a * Q := by
    have h1 : μ * F ≤ μ * ((M1 / U) * S + Cm * a * (Real.sqrt (Q * ((M1 / U) * S)) + Q)) :=
      mul_le_mul_of_nonneg_left hF0 hμ
    nlinarith [h1]
  have hQpay : μ * ((M1 / U) * S) + μ * Cm * a * Real.sqrt (Q * ((M1 / U) * S))
      + μ * Cm * a * Q ≤ μ * (1 + 1 / 10000) * ((M1 / U) * S) + bG * Q := by
    nlinarith [hY, hG, hQ, hμ, ha, hCm]
  have hθ' : μ * (1 + 1 / 10000) * ((M1 / U) * S)
      ≤ μ * (1 + 1 / 10000) * ((M2 / U) * S) :=
    mul_le_mul_of_nonneg_left hθ (by positivity)
  have key : (M2 / U ^ 2) * S * ((10 / 37) * (S / J - 1)) - μ * (1 + 1 / 10000) * ((M2 / U) * S)
      ≤ sbW := by
    have h1 : (M2 / U ^ 2) * S * ((10 / 37) * (S / J - 1)) - μ * (1 + 1 / 10000) * ((M2 / U) * S)
        ≤ (M2 / U ^ 2) * S * ((10 / 37) * (S / J - 1))
          - μ * (1 + 1 / 10000) * ((M1 / U) * S) := by linarith [hθ']
    have h2 : (M2 / U ^ 2) * S * ((10 / 37) * (S / J - 1))
        - μ * (1 + 1 / 10000) * ((M1 / U) * S) ≤ sbW := by
      nlinarith [hbed, hP0, hF1, hQpay]
    linarith [h1, h2]
  have hE : (M2 / U ^ 2) * (S * ((10 / 37) * (S / J - 1) - (1 + 1 / 10000) * (μ * U)))
      = (M2 / U ^ 2) * S * ((10 / 37) * (S / J - 1))
        - μ * (1 + 1 / 10000) * ((M2 / U) * S) := by
    rw [mul_assoc]
    field_simp
    try ring
  linarith [key, hE.le, hE.ge]

/-- **The final bookkeeping (pure real).** -/
private lemma rowOneFinalF {S J U W M2 br μ n' : ℝ}
    (hU : 0 < U) (hJ : 0 ≤ J) (hS : 0 ≤ S) (hW : 0 ≤ W) (hWM2 : W ≤ M2)
    (hbr : 0 ≤ br) (hSbr : J * (μ * U * n' / 18) ≤ S * br) :
    (1 / 18) * μ * (n' / U) * W * J ≤ (M2 / U ^ 2) * (S * br) := by
  have hWU : 0 ≤ W / U ^ 2 := div_nonneg hW (by positivity)
  have hSb : 0 ≤ S * br := mul_nonneg hS hbr
  have h1 : (1 / 18) * μ * (n' / U) * W * J = (W / U ^ 2) * (J * (μ * U * n' / 18)) := by
    field_simp
    try ring
  have h2 : (W / U ^ 2) * (J * (μ * U * n' / 18)) ≤ (W / U ^ 2) * (S * br) :=
    mul_le_mul_of_nonneg_left hSbr hWU
  have h3 : (W / U ^ 2) * (S * br) ≤ (M2 / U ^ 2) * (S * br) := by
    have hdiv := div_le_div_of_nonneg_right hWM2 (by positivity : (0 : ℝ) ≤ U ^ 2)
    exact mul_le_mul_of_nonneg_right hdiv hSb
  linarith [h1.le, h1.ge, h2, h3]

/-- **The row-1 core.** -/
private lemma rowOneMainF {S Q J U W M1 M2 P F bG sbW br : ℝ} {Cm a μ n' c₀ : ℝ}
    (hU : 0 < U) (hJ : 0 < J) (hS : 0 ≤ S) (hQ : 0 ≤ Q) (ha : 0 ≤ a) (hμ : 0 ≤ μ)
    (hCm : 0 ≤ Cm) (hW : 0 ≤ W) (hM1W : M1 = W) (hWM2 : W ≤ M2)
    (hG : (2500 * Cm ^ 2 * a + Cm) * μ * a * Q ≤ bG * Q)
    (hP0 : (M2 / U ^ 2) * S * ((10 / 37) * (S / J - 1)) ≤ P)
    (hF0 : F ≤ (M1 / U) * S + Cm * a * (Real.sqrt (Q * ((M1 / U) * S)) + Q))
    (hY : μ * Cm * a * Real.sqrt (Q * ((M1 / U) * S))
      ≤ μ * (1 / 10000) * ((M1 / U) * S) + μ * (2500 * Cm ^ 2 * a ^ 2) * Q)
    (hbed : bG * Q + P - μ * F ≤ sbW)
    (hcount : S + Q = n' * J) (hQc : Q < c₀ * J) (hc₀0 : 0 < c₀) (hc₀ : c₀ ≤ 1 / 10 ^ 6)
    (hX12 : 12 ≤ μ * U) (h4 : 4 * (μ * U) ≤ n')
    (hbrdef : br = (10 / 37) * (S / J - 1) - (1 + 1 / 10000) * (μ * U)) :
    (1 / 18) * μ * (n' / U) * W * J ≤ sbW := by
  have hsJ : n' - c₀ ≤ S / J := by
    rw [le_div_iff₀ hJ]
    nlinarith [hcount, hQc]
  obtain ⟨hbrnn, harith⟩ :=
    Work.BoseB1Cube.rowOneArith (X := μ * U) (n := n') (s := S / J) (c₀ := c₀)
      (ρ := 1 + 1 / 10000) hX12 h4 hsJ hc₀0 hc₀ (by norm_num) (by norm_num)
  have hSbr : J * (μ * U * n' / 18) ≤ S * br := by
    have h1 := mul_le_mul_of_nonneg_left harith hJ.le
    have h2 : J * ((S / J) * ((10 / 37) * (S / J - 1) - (μ * U) * (1 + 1 / 10000)))
        = S * br := by
      rw [hbrdef]
      field_simp
      try ring
    linarith [h1, h2.le, h2.ge]
  have hbr0 : 0 ≤ br := by rw [hbrdef]; linarith [hbrnn]
  have hθ : (M1 / U) * S ≤ (M2 / U) * S := by
    rw [hM1W]
    exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hWM2 hU.le) hS
  have hledger : (M2 / U ^ 2) * (S * br) ≤ sbW := by
    have h := rowOneLedgerF (S := S) (Q := Q) (J := J) (U := U) (M1 := M1) (M2 := M2) (P := P)
      (F := F) (bG := bG) (sbW := sbW) (Cm := Cm) (a := a) (μ := μ)
      hU hS hQ ha hμ hCm hθ hG hP0 hF0 hY hbed
    rw [hbrdef]
    exact h
  have hfin := rowOneFinalF (S := S) (J := J) (U := U) (W := W) (M2 := M2) (br := br) (μ := μ)
    (n' := n') hU hJ.le hS hW hWM2 hbr0 hSbr
  linarith [hledger, hfin]

/-- **`M₂` of the `g₂`-kernel is at most `M_v` of the `v`-kernel.** -/
theorem boxM2_g2_le_v_boxF {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR16 : R ≤ ℓ * d / 16) (hRχ : R ≤ ℓ * Submission.BoseGases.chiR0)
    (u : EuclideanSpace ℝ (Fin 3)) :
    Work.BoseFixB1S.boxM2 (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.dlBox ℓ d u)
        (Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h))
      ≤ Work.BoseFixB1S.boxM2 (Work.SmallBoxSliding.boxMass ℓ d u)
        (Submission.BoseGases.dlBox ℓ d u) (Submission.BoseGases.wSmallPair M ℓ d u v) := by
  rw [Work.BoseFixB1S.boxM2, Work.BoseFixB1S.boxM2]
  have hA : Submission.BoseGases.dlBox ℓ d u ×ˢ Submission.BoseGases.dlBox ℓ d u
      ⊆ Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ :=
    Set.prod_mono (Work.SmallBoxSliding.dlBox_subset_acube ℓ d u)
      (Work.SmallBoxSliding.dlBox_subset_acube ℓ d u)
  have hInt2 : MeasureTheory.IntegrableOn
      (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h) p.1 p.2)
      (Submission.BoseGases.dlBox ℓ d u ×ˢ Submission.BoseGases.dlBox ℓ d u) :=
    (Work.BoseFixB1.integrableOn_wSmallPair_cube
      (Submission.BoseGases.g2_integrable hR hv hvrad hv_supp h)
      (fun z hz => Submission.BoseGases.g2_zero_of_norm_ge hv_supp hz h) hM hℓ hd hR16 hRχ u
      ).mono_set hA
  have hIntv : MeasureTheory.IntegrableOn
      (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.wSmallPair M ℓ d u v p.1 p.2)
      (Submission.BoseGases.dlBox ℓ d u ×ˢ Submission.BoseGases.dlBox ℓ d u) :=
    (Work.BoseFixB1.integrableOn_wSmallPair_cube
      (MeasureTheory.memLp_one_iff_integrable.mp hv1)
      (fun z hz => by
        by_contra hne
        have hz1 : z ∈ tsupport v := subset_tsupport v (Function.mem_support.mpr hne)
        have hz2 : z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R := hv_supp hz1
        rw [Metric.mem_ball, dist_zero_right] at hz2
        exact absurd hz2 (not_lt.mpr hz)) hM hℓ hd hR16 hRχ u).mono_set hA
  exact MeasureTheory.setIntegral_mono_ae hInt2 hIntv
    (Filter.Eventually.of_forall
      (fun p => Work.BoseFixB1B.wSmallPair_g2_le_v h hv M ℓ d u p.1 p.2))

theorem flatArm37RowNodeF {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) (Cn : ℝ) (hCn : 4 ≤ Cn) :
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
          Work.BoseFixB1.bQ v μ Ψ u < 1 / 10 ^ 6 →
          Work.BoseB1Cube.FlatArm37 v h μ n Ψ u →
          (1 / 18) * μ * ((n : ℝ) / Work.BoseFixB1.bV v μ u) * Work.BoseFixB1.bW v h μ u
            ≤ Work.BoseFixB1B.sbWordCube v h μ u Ψ := by
  classical
  obtain ⟨Cm, hCm0, hman⟩ := Work.BoseFixB1S.fibSum_le_manifest (v := v) h hv hv1 hvrad hR
    hv_supp hav (M := Work.BoseBox.mValue) (by rw [Work.BoseBox.mValue]; norm_num)
  obtain ⟨εR, hεR, hreg⟩ := Work.BoseFixB1.regime_sideAt_ge (v := v) hav hR
  obtain ⟨εK, hεK, hgate⟩ := Work.BoseB1Cube.bGapCoeff_gate (v := v) hav
    (2500 * (Cm + 1) ^ 2 * (_root_.BoseGases.a v) + (Cm + 1) + 1) (by positivity)
  -- the diluteness budget: the two ledger thresholds together with the four gates of the
  -- bad (corner) case of `flatArm37RowOneBadL`
  set ε₀ : ℝ := min (min εK εR) (min (min 1 ((_root_.BoseGases.a v) ^ 3))
      (min ((1000000 : ℝ) ^ (-(323 / 166 : ℝ))) ((1000000 : ℝ) ^ (-(323 / 148 : ℝ)))))
    with hε₀def
  have hε₀pos : 0 < ε₀ := by
    rw [hε₀def]
    exact lt_min (lt_min hεK hεR) (lt_min (lt_min one_pos (pow_pos hav 3))
      (lt_min (Real.rpow_pos_of_pos (by norm_num) _) (Real.rpow_pos_of_pos (by norm_num) _)))
  refine ⟨ε₀, hε₀pos, ?_⟩
  intro μ hAdm n Ψ u hu hWmu hΨc hsupp hnorm hn1 hn2 hQhole hFlat
  have hAdmK : Work.BoseBoxFix.Adm v εK μ :=
    Work.BoseFixB1.Adm.mono hAdm (by rw [hε₀def]; exact le_trans (min_le_left _ _) (min_le_left _ _))
  have hAdmR : Work.BoseBoxFix.Adm v εR μ :=
    Work.BoseFixB1.Adm.mono hAdm (by rw [hε₀def]; exact le_trans (min_le_left _ _) (min_le_right _ _))
  have hμ0 : 0 < μ := hAdm.1
  have ha0 : 0 ≤ _root_.BoseGases.a v := hav.le
  by_cases hg : 12 ≤ μ * Work.BoseFixB1.bV v μ u
  · -- ## the good case: the flat-arm ledger at the box gate `12 ≤ μ·|B(u)|`
    obtain ⟨hR16, hRχ⟩ := hreg μ hAdmR.1 hAdmR.2.1
    have hΦcont : Continuous Ψ := hΨc.continuous
    have hℓb : 0 < Work.BoseFixB1.bSide v μ := Work.BoseFixB1.adm_ell_pos hAdm
    have hdb : 0 < Work.BoseFixB1.bD v μ := Work.BoseFixB1.adm_d_pos hAdm
    have hMvb : 1 ≤ Work.BoseFixB1.bM v μ := by
      rw [Work.BoseFixB1.bM, Work.BoseFixB1.M_eq_mValue, Work.BoseBox.mValue]
      norm_num
    have hX12 : 12 ≤ μ * Work.BoseFixB1.bV v μ u := hg
    simp only [Work.BoseFixB1.bSide, Work.BoseFixB1.bD, Work.BoseFixB1.bV, Work.BoseFixB1.bA,
      Work.BoseFixB1.bW, Work.BoseFixB1.bM, Work.BoseFixB1.bQ, Work.BoseB1Cube.FlatArm37,
      Work.BoseFixB1B.PBBV, Work.BoseFixB1B.PBB, Work.BoseFixB1B.PBℓ, Work.BoseFixB1B.PBd,
      Work.BoseFixB1B.PBM, Work.BoseBox.mValue, Work.BoseFixB1.M_eq_mValue]
      at hℓb hdb hMvb hu hWmu hsupp hX12 hQhole hFlat hnorm
    have hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := hℓb
    have hd : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d := hdb
    have hMle : 1 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M := hMvb
    -- ### the local objects (in the corpus spelling)
    set U : ℝ := Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u with hUdef
    set W : ℝ := Work.BoseFixB1.w1MassB h Work.BoseBox.mValue
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u with hWdef
    set S : ℝ := Work.BoseFixB1S.boxFlatCount
      (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) Ψ with hSdef
    set Q : ℝ := Work.BoseFixB1S.boxQCount
      (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) Ψ with hQdef
    set M1 : ℝ := Work.BoseFixB1S.boxM1 (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
      (Submission.BoseGases.wSmall1Pair h Work.BoseBox.mValue
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) with hM1def
    set M2 : ℝ := Work.BoseFixB1S.boxM2
      (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
      (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
      (Submission.BoseGases.wSmallPair Work.BoseBox.mValue
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u v) with hM2def
    set P : ℝ := Work.BoseFixB1.pairSum v Work.BoseBox.mValue
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u Ψ with hPdef
    set F : ℝ := Work.BoseFixB1.fibSum h Work.BoseBox.mValue
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u Ψ with hFdef
    set Pc : ℝ := Work.BoseFixB1S.boxPairCount
      (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) Ψ with hPcdef
    -- ### basic signs
    have hUpos : 0 < U := by
      rw [hUdef]
      exact Work.BoseFixB1.boxMass_pos_of_goodSet hℓ hd hμ0 hu
    have hQ0 : 0 ≤ Q := by
      rw [hQdef, Work.BoseFixB1S.boxQCount]
      exact Finset.sum_nonneg (fun i _ => integral_nonneg (fun x => sq_nonneg _))
    have hS0 : 0 ≤ S := by
      rw [hSdef, Work.BoseFixB1S.boxFlatCount]
      exact Finset.sum_nonneg (fun i _ => integral_nonneg (fun x => sq_nonneg _))
    have hW0 : 0 ≤ W := by
      rw [hWdef]
      exact Work.BoseFixB1.w1MassB_nonneg h hv hvrad hR hv_supp hℓ hd u
    have h4' : 4 * (μ * U) ≤ ((n : ℕ) : ℝ) := by
      have hX : 4 * (μ * U) ≤ Cn * (μ * U) :=
        mul_le_mul_of_nonneg_right hCn (mul_nonneg hμ0.le (le_of_lt hUpos))
      have hY : Cn * μ * U ≤ ((n : ℕ) : ℝ) := by
        simpa only [hUdef, Work.BoseFixB1.bV, Work.BoseFixB1.bSide, Work.BoseFixB1.bD] using hn1
      nlinarith [hX, hY]
    -- ### the gate `(2500·Cc²a + Cc)·μa·Q ≤ bGapCoeff·Q`
    have hG : (2500 * (Cm + 1) ^ 2 * (_root_.BoseGases.a v) + (Cm + 1)) * μ
          * (_root_.BoseGases.a v) * Q ≤ Work.BoseFixB1.bGapCoeff v μ * Q := by
      have h3 : (2500 * (Cm + 1) ^ 2 * (_root_.BoseGases.a v) + (Cm + 1))
            * (μ * (_root_.BoseGases.a v))
          ≤ (2500 * (Cm + 1) ^ 2 * (_root_.BoseGases.a v) + (Cm + 1) + 1)
            * (μ * (_root_.BoseGases.a v)) := by
        have hle : (2500 * (Cm + 1) ^ 2 * (_root_.BoseGases.a v) + (Cm + 1))
            ≤ (2500 * (Cm + 1) ^ 2 * (_root_.BoseGases.a v) + (Cm + 1) + 1) := by linarith
        exact mul_le_mul_of_nonneg_right hle (mul_nonneg hμ0.le ha0)
      have h4 : (2500 * (Cm + 1) ^ 2 * (_root_.BoseGases.a v) + (Cm + 1) + 1)
            * (μ * (_root_.BoseGases.a v)) ≤ Work.BoseFixB1.bGapCoeff v μ := hgate μ hAdmK
      have h5 : (2500 * (Cm + 1) ^ 2 * (_root_.BoseGases.a v) + (Cm + 1)) * μ
            * (_root_.BoseGases.a v) * Q ≤ Work.BoseFixB1.bGapCoeff v μ * Q := by
        have h3' : (2500 * (Cm + 1) ^ 2 * (_root_.BoseGases.a v) + (Cm + 1)) * μ
              * (_root_.BoseGases.a v) * Q
            = (2500 * (Cm + 1) ^ 2 * (_root_.BoseGases.a v) + (Cm + 1))
              * (μ * (_root_.BoseGases.a v)) * Q := by ring
        rw [h3']
        exact mul_le_mul_of_nonneg_right (le_trans h3 h4) hQ0
      exact h5
    -- ### the word decomposition
    have hkin : Work.BoseFixB1.bGapCoeff v μ * Q ≤ Work.BoseFixB1B.sbKinCube v μ u Ψ := by
      have hnn : 0 ≤ Work.UBBInputs8.tBwordKinInd (Work.BoseFixB1.bSide v μ)
          (Work.BoseFixB1.bA v μ u) (Work.BoseFixB1.bV v μ u)
          (Submission.BoseGases.chiSmallB (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bD v μ) u) (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) Ψ :=
        Work.BoseFixB1.tBwordKinInd_nonneg Ψ
      have hsplit : Work.BoseFixB1B.sbKinCube v μ u Ψ
          = Work.BoseFixB1.bGapCoeff v μ * Q
            + Work.UBBInputs8.tBwordKinInd (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u)
                (Work.BoseFixB1.bV v μ u)
                (Submission.BoseGases.chiSmallB (Work.BoseFixB1.bM v μ)
                  (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) u)
                (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) Ψ := rfl
      linarith [hsplit, hnn]
    have hpot : Work.BoseFixB1.sbPot h μ u Ψ = P - μ * F := by
      have hs := Work.BoseFixB1.sbPot_split (v := v) (h := h) (R := R) hv_supp hR hv hvrad hv1
        hAdm hΦcont u hR16 hRχ
      simp only [Work.BoseFixB1.M_eq_mValue] at hs
      rw [hPdef, hFdef, hs]
      ring
    have hbed : Work.BoseFixB1.bGapCoeff v μ * Q + P - μ * F
        ≤ Work.BoseFixB1B.sbWordCube v h μ u Ψ := by
      have hword : Work.BoseFixB1B.sbWordCube v h μ u Ψ
          = Work.BoseFixB1B.sbKinCube v μ u Ψ + Work.BoseFixB1.sbPot h μ u Ψ := rfl
      rw [hword, hpot]
      linarith [hkin]
    -- ### the pair row
    have hFlat' : Pc ≤ (37 / 10) * (U ^ 2 / M2) * P := hFlat
    have hvolA : Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
        = (MeasureTheory.volume (Submission.BoseGases.dlBox
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)).toReal := by
      rw [Work.SmallBoxSliding.boxMass_eq_measureReal, MeasureTheory.Measure.real_def]
    have hpairPay : S ^ 2 / 1 - S ≤ Pc := by
      rw [hSdef, hPcdef]
      simpa using Work.BoseFixB1S.Q0C.count_ge hℓ hUpos
          (Work.SmallBoxSliding.measurableSet_dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) hvolA
          (Work.SmallBoxSliding.dlBox_subset_acube (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) hΦcont hnorm
    have hM1W : M1 = W := by
      have hb := (Work.BoseB1Cube.PBW_eq_boxM1 (h := h) (μ := μ) (u := u) hℓ hd hMle).symm
      simp only [Work.BoseFixB1.M_eq_mValue] at hb
      rw [hM1def, hWdef]
      exact hb
    have hWM2 : W ≤ M2 := by
      rw [← hM1W, hM1def, hM2def]
      have h2 := Work.BoseFixB1S.boxM2_sub_boxM1_nonneg_slidingB1 (v := v) (R := R) hv_supp hR
        hv hvrad hv1 h hav (M := Work.BoseBox.mValue) (by norm_num [Work.BoseBox.mValue])
        (ℓ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (d := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) hℓ hd hR16 hRχ u
      have h3 := boxM2_g2_le_v_boxF (v := v) (h := h) (R := R) hv hv1 hvrad hR hv_supp
        (M := Work.BoseBox.mValue) (by norm_num [Work.BoseBox.mValue]) hℓ hd hR16 hRχ u
      linarith [h2, h3]
    have hM2nn : 0 ≤ M2 := le_trans hW0 hWM2
    have hnn37 : 0 ≤ (10 / 37) * (M2 / U ^ 2) :=
      mul_nonneg (by norm_num) (div_nonneg hM2nn (by positivity))
    have hPcP : (10 / 37) * (M2 / U ^ 2) * Pc ≤ P := by
      have h1 := mul_le_mul_of_nonneg_left hFlat' hnn37
      rcases eq_or_lt_of_le hM2nn with h2 | h2
      · have hL : (10 / 37) * (M2 / U ^ 2) * Pc = 0 := by rw [h2.symm]; simp
        rw [hL]
        exact Work.BoseFixB1.pairSum_nonneg hv (M := (Work.BoseBox.paramsAt μ
            (_root_.BoseGases.a v)).M) (ℓ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (d := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) u Ψ
      · have heq : (10 / 37) * (M2 / U ^ 2) * ((37 / 10) * (U ^ 2 / M2) * P) = P := by
          field_simp
        linarith [h1, heq.le, heq.ge]
    have hP0 : (M2 / U ^ 2) * S * ((10 / 37) * (S / 1 - 1)) ≤ P := by
      have h2 : (10 / 37) * (M2 / U ^ 2) * (S ^ 2 / 1 - S)
          ≤ (10 / 37) * (M2 / U ^ 2) * Pc := mul_le_mul_of_nonneg_left hpairPay hnn37
      have h3 : (M2 / U ^ 2) * S * ((10 / 37) * (S / 1 - 1))
          = (10 / 37) * (M2 / U ^ 2) * (S ^ 2 / 1 - S) := by
        field_simp
        try ring
        try ring_nf
      linarith [h2, h3, hPcP]
    -- ### the manifest fibre row
    have hFraw : F ≤ (M1 / U) * S + Cm * (_root_.BoseGases.a v)
        * (Real.sqrt (Q * ((M1 / U) * S)) + Q) :=
      hman (μ := μ) hℓ hd hR16 hRχ u hUpos hΦcont
    have hF0 : F ≤ (M1 / U) * S + (Cm + 1) * (_root_.BoseGases.a v)
        * (Real.sqrt (Q * ((M1 / U) * S)) + Q) := by
      have h2 : Cm * (_root_.BoseGases.a v) * (Real.sqrt (Q * ((M1 / U) * S)) + Q)
          ≤ (Cm + 1) * (_root_.BoseGases.a v) * (Real.sqrt (Q * ((M1 / U) * S)) + Q) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_right (by linarith) ha0
      linarith [hFraw, h2]
    -- ### Young
    have hθnn : 0 ≤ (M1 / U) * S := by
      rw [hM1W]
      exact mul_nonneg (div_nonneg hW0 (by positivity)) hS0
    have hY : μ * (Cm + 1) * (_root_.BoseGases.a v) * Real.sqrt (Q * ((M1 / U) * S))
        ≤ μ * (1 / 10000) * ((M1 / U) * S)
          + μ * (2500 * (Cm + 1) ^ 2 * (_root_.BoseGases.a v) ^ 2) * Q := by
      rcases eq_or_lt_of_le (mul_nonneg (by positivity : (0 : ℝ) ≤ Cm + 1) ha0) with hz | hpos
      · have h0 : μ * (Cm + 1) * (_root_.BoseGases.a v) = 0 := by
          rw [mul_assoc, hz.symm, mul_zero]
        rw [h0, zero_mul]
        have ha1 : 0 ≤ μ * (1 / 10000) * ((M1 / U) * S) :=
          mul_nonneg (mul_nonneg hμ0.le (by norm_num)) hθnn
        have hb1 : 0 ≤ μ * (2500 * (Cm + 1) ^ 2 * (_root_.BoseGases.a v) ^ 2) * Q :=
          mul_nonneg (mul_nonneg hμ0.le (by positivity)) hQ0
        linarith
      · have hη : 0 < 2500 * (Cm + 1) * (_root_.BoseGases.a v) := by positivity
        have hy := sqrt_mul_le_add_divF (Q := Q) (θ := (M1 / U) * S)
          (η := 2500 * (Cm + 1) * (_root_.BoseGases.a v)) hQ0 hθnn hη
        have hm : μ * (Cm + 1) * (_root_.BoseGases.a v) * Real.sqrt (Q * ((M1 / U) * S))
            ≤ μ * (Cm + 1) * (_root_.BoseGases.a v)
              * (2500 * (Cm + 1) * (_root_.BoseGases.a v) * Q
                + ((M1 / U) * S) / (4 * (2500 * (Cm + 1) * (_root_.BoseGases.a v)))) :=
          mul_le_mul_of_nonneg_left hy
            (mul_nonneg (mul_nonneg hμ0.le (by positivity : (0 : ℝ) ≤ Cm + 1)) ha0)
        have heq : μ * (Cm + 1) * (_root_.BoseGases.a v)
              * (2500 * (Cm + 1) * (_root_.BoseGases.a v) * Q
                + ((M1 / U) * S) / (4 * (2500 * (Cm + 1) * (_root_.BoseGases.a v))))
            = μ * (1 / 10000) * ((M1 / U) * S)
              + μ * (2500 * (Cm + 1) ^ 2 * (_root_.BoseGases.a v) ^ 2) * Q := by
          field_simp
          try ring
          try ring_nf
        linarith [hm, heq.le, heq.ge]
    -- ### assemble
    have hQc : Q < (1 / 10 ^ 6) * 1 := by
      simpa only [mul_one, Work.BoseFixB1.bQ, Work.BoseFixB1S.boxQCount] using hQhole
    have hcount : S + Q = ((n : ℕ) : ℝ) * 1 := by
      have hb := Work.BoseFixB1S.b1sCountSplit (N := n) hℓ hUpos
        (Work.SmallBoxSliding.measurableSet_dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) hvolA
        (Work.SmallBoxSliding.dlBox_subset_acube (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) hΦcont hsupp
      rw [hnorm, mul_one] at hb
      rw [hSdef, hQdef, mul_one]
      exact hb
    have hmain := rowOneMainF (S := S) (Q := Q) (J := 1) (U := U) (W := W) (M1 := M1) (M2 := M2)
      (P := P) (F := F) (bG := Work.BoseFixB1.bGapCoeff v μ)
      (sbW := Work.BoseFixB1B.sbWordCube v h μ u Ψ)
      (br := (10 / 37) * (S / 1 - 1) - (1 + 1 / 10000) * (μ * U)) (Cm := Cm + 1)
      (a := _root_.BoseGases.a v) (μ := μ) (n' := ((n : ℕ) : ℝ)) (c₀ := 1 / 10 ^ 6)
      hUpos (by norm_num) hS0 hQ0 ha0 hμ0.le (by positivity) hW0 hM1W hWM2 hG hP0 hF0 hY hbed
      hcount hQc (by norm_num) (by norm_num) hX12 h4' rfl
    simpa only [hUdef, hWdef, mul_one, Work.BoseFixB1.bV, Work.BoseFixB1.bW,
      Work.BoseFixB1.bM, Work.BoseFixB1.M_eq_mValue, Work.BoseFixB1.bSide, Work.BoseFixB1.bD]
      using hmain
  · -- ## the bad case: the corner region `μ·|B(u)| < 12` is inconsistent
    exfalso
    have hε1 : ε₀ ≤ 1 := by
      rw [hε₀def]
      exact le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_left _ _))
    have hεa : ε₀ ≤ (_root_.BoseGases.a v) ^ 3 := by
      rw [hε₀def]
      exact le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_right _ _))
    have hεA : ε₀ ≤ (1000000 : ℝ) ^ (-(323 / 166 : ℝ)) := by
      rw [hε₀def]
      exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
    have hεB : ε₀ ≤ (1000000 : ℝ) ^ (-(323 / 148 : ℝ)) := by
      rw [hε₀def]
      exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
    have hℓb : 0 < Work.BoseFixB1.bSide v μ := Work.BoseFixB1.adm_ell_pos hAdm
    have hdb : 0 < Work.BoseFixB1.bD v μ := Work.BoseFixB1.adm_d_pos hAdm
    have hVpos : 0 < Work.BoseFixB1.bV v μ u :=
      Work.BoseFixB1.boxMass_pos_of_goodSet hℓb hdb hμ0 hu
    have hu' : u ∈ Work.SmallBoxSliding.goodSet (Work.BoseFixB1B.PBℓ v μ)
        (Work.BoseFixB1B.PBd v μ) μ := by
      simpa only [Work.BoseFixB1B.PBℓ, Work.BoseFixB1B.PBd, Work.BoseFixB1.bSide,
        Work.BoseFixB1.bD] using hu
    have hsmall : μ * Work.BoseFixB1B.PBBV v μ u < 12 := by
      have h := lt_of_not_ge hg
      simpa only [Work.BoseFixB1B.PBBV, Work.BoseFixB1B.PBℓ, Work.BoseFixB1B.PBd,
        Work.BoseFixB1.bV, Work.BoseFixB1.bSide, Work.BoseFixB1.bD] using h
    have h4 : 4 * μ * Work.BoseFixB1B.PBBV v μ u ≤ ((n : ℕ) : ℝ) := by
      have hVnn : 0 ≤ μ * Work.BoseFixB1.bV v μ u := mul_nonneg hμ0.le hVpos.le
      have h1 : 4 * (μ * Work.BoseFixB1.bV v μ u) ≤ Cn * (μ * Work.BoseFixB1.bV v μ u) :=
        mul_le_mul_of_nonneg_right hCn hVnn
      have h2 : 4 * (μ * Work.BoseFixB1.bV v μ u) = 4 * μ * Work.BoseFixB1.bV v μ u := by ring
      have h3 : 4 * μ * Work.BoseFixB1B.PBBV v μ u = 4 * μ * Work.BoseFixB1.bV v μ u := by
        simp only [Work.BoseFixB1B.PBBV, Work.BoseFixB1B.PBℓ, Work.BoseFixB1B.PBd,
          Work.BoseFixB1.bV, Work.BoseFixB1.bSide, Work.BoseFixB1.bD]
      rw [h3, ← h2]
      linarith
    have hIn : Work.BoseFixB1B.InBox v μ u Ψ := by
      simpa only [Work.BoseFixB1B.InBox, Work.BoseFixB1B.PBB, Work.BoseFixB1B.PBℓ,
        Work.BoseFixB1B.PBd, Work.BoseFixB1.bA, Work.BoseFixB1.bSide, Work.BoseFixB1.bD]
        using hsupp
    have hQbad : Work.UBBInputs8.cnPlusBoxInd (Work.BoseFixB1.bSide v μ)
        (Work.BoseFixB1.bA v μ u) (Work.BoseFixB1.bV v μ u) Ψ
        < (1 / 10 ^ 6) * (∫ x in Submission.BoseGases.abox n (Work.BoseFixB1B.PBℓ v μ),
            (Ψ x) ^ 2) := by
      have hQ0 : Work.UBBInputs8.cnPlusBoxInd (Work.BoseFixB1.bSide v μ)
          (Work.BoseFixB1.bA v μ u) (Work.BoseFixB1.bV v μ u) Ψ
          = Work.BoseFixB1.bQ v μ Ψ u := by
        simp only [Work.BoseFixB1.bQ, Work.BoseFixB1S.boxQCount, Work.UBBInputs8.cnPlusBoxInd]
      have hidx : (∫ x in Submission.BoseGases.abox n (Work.BoseFixB1B.PBℓ v μ), (Ψ x) ^ 2)
          = ∫ x in Submission.BoseGases.abox n (Work.BoseFixB1.bSide v μ), (Ψ x) ^ 2 := by
        simp only [Work.BoseFixB1B.PBℓ, Work.BoseFixB1.bSide]
      rw [hQ0, hidx, hnorm, mul_one]
      exact hQhole
    exact Work.BoseB1Cube.flatArm37RowOneBadL (v := v) h hav hε₀pos hε1 hεa hεA hεB
      (by norm_num) (by norm_num) hAdm hu' hsmall h4 hΨc.continuous hIn hFlat hQbad

end Work.BoseB1Cube
