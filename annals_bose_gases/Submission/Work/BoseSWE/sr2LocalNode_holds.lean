import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseSWE.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseSWE

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- **Node N1 of the `BoseSWE` route**: the per-point form of the PROVED
`Work.BoseB1Cube.normNode_of_sharpRow2` (`Submission/Work/BoseB1Cube/nomRowLinWindowRow.lean`).
Recipe (pure copy; see `Submission/Work/BoseSWE/BRIEF.md` §1): run the same proof with the global
`SharpRow2` hypothesis replaced by the pointwise hypothesis `Dem v h μ n u ≤ SR2Rhs v h C μ Ψ u`
and the gate constant `(Cp+1)*(1+2*Cn) + C`. -/
theorem sr2LocalNode_holds {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) : Work.BoseSWE.SR2LocalNode v h := by
  intro Cn hCn C hC
  -- ## the thresholds, all produced *before* `ε₀` is chosen
  obtain ⟨εp, Cp, hεp, hCp, hpay⟩ :=
    Work.BoseB1Cube.paySurplusSlotFreeContDiff (v := v) h hv hv1 hvrad hR hv_supp hav
  obtain ⟨εt, hεt, hreg⟩ := Work.BoseFixB1.regime_sideAt_ge (v := v) hav hR
  obtain ⟨εd, hεd, hgates⟩ :=
    Work.BoseB1Cube.boxDataGatesContDiff (v := v) h hv hv1 hvrad hR hv_supp hav
  have hKnn : 0 ≤ (Cp + 1) * (1 + 2 * Cn) + C := by
    have h1 : 0 ≤ (Cp + 1) * (1 + 2 * Cn) := by nlinarith [hCp, hCn]
    linarith
  obtain ⟨εg, hεg, hgate⟩ :=
    Work.BoseFixB1S.PerBoxGapAbsorbB1 (v := v) hav ((Cp + 1) * (1 + 2 * Cn) + C) hKnn
  set E0 : ℝ := min εp (min εt (min εd (min εg 1))) with hE0
  have hb1 : E0 ≤ εp := by rw [hE0]; exact min_le_left _ _
  have hb2 : E0 ≤ εt := by rw [hE0]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hb3 : E0 ≤ εd := by
    rw [hE0]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hb4 : E0 ≤ εg := by
    rw [hE0]
    exact le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hb5 : E0 ≤ 1 := by
    rw [hE0]
    exact le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (min_le_right _ _)))
  refine ⟨E0, lt_min hεp (lt_min hεt (lt_min hεd (lt_min hεg one_pos))), ?_⟩
  intro μ hAdm n Ψ u hu hΨ hsupp hnorm hn1 hn2 hrow
  -- ## threshold extraction
  have hAdmp : Work.BoseBoxFix.Adm v εp μ := Work.BoseFixB1.Adm.mono hAdm hb1
  have hAdmt : Work.BoseBoxFix.Adm v εt μ := Work.BoseFixB1.Adm.mono hAdm hb2
  have hAdmd : Work.BoseBoxFix.Adm v εd μ := Work.BoseFixB1.Adm.mono hAdm hb3
  have hAdmg : Work.BoseBoxFix.Adm v εg μ := Work.BoseFixB1.Adm.mono hAdm hb4
  have hAdm1 : Work.BoseBoxFix.Adm v 1 μ := Work.BoseFixB1.Adm.mono hAdm hb5
  have hμ : 0 < μ := hAdm.1
  have ha : 0 ≤ _root_.BoseGases.a v := le_of_lt hav
  have hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d := Work.BoseFixB1.adm_d_pos hAdm
  obtain ⟨hRd, hRχ⟩ := hreg μ hμ hAdmt.2.1
  -- ## the gates and the geometry
  obtain ⟨hvol, hW, hM1nn, hM2, hPcnn, hcS2⟩ := hgates μ hAdmd n Ψ hΨ u hu hnorm
  have hμV : 1 ≤ μ * Work.BoseFixB1.bV v μ u :=
    Work.BoseFixB1.SectorAux.one_le_mu_boxMassGood (a := _root_.BoseGases.a v) (μ := μ) hav
      hAdm.1 hAdm1.2.1 hu
  -- ## the payment rung at the slot `μp = μ`
  have hpay' := hpay μ hAdmp μ (le_refl μ) n Ψ hΨ u hu hvol hμV hsupp hnorm hW hM1nn hM2 hPcnn hcS2
  -- ## the telescope (the PROVED `sbWordSlotTelescopeContDiff`)
  have htel := Work.BoseB1Cube.sbWordSlotTelescopeContDiff (v := v) h hv_supp hR hv hvrad hv1
    (μp := μ) (μ := μ) hℓ hd hRd hRχ u hvol Ψ hΨ
  -- ## `sbWordCube = sbWordSlot v h μ μ u Ψ`
  have hcube : Work.BoseFixB1B.sbWordCube v h μ u Ψ = Work.BoseB1Cube.sbWordSlot v h μ μ u Ψ := by
    rw [Work.BoseFixB1C.sbWordCube_eq_add u Ψ,
      Work.BoseFixB1.sbPot_split (v := v) (h := h) (R := R) hv_supp hR hv hvrad hv1 hAdmp
        (ContDiff.continuous hΨ) u hRd hRχ]
    unfold Work.BoseB1Cube.sbWordSlot
    ring
  -- ## the count split and the window
  have hcount : Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
        (Work.BoseFixB1.bA v μ u) Ψ ≤ (n : ℝ) := by
    have h := Work.BoseFixB1S.boxFlatCount_le_NB1 (N := n)
      (ℓ := Work.BoseFixB1.bSide v μ) (volA := Work.BoseFixB1.bV v μ u)
      (Ac := Work.BoseFixB1.bA v μ u) hℓ hvol
      (Work.SmallBoxSliding.measurableSet_dlBox _ _ _)
      (Work.SmallBoxSliding.dlBox_subset_acube _ _ _)
      (by rw [Work.BoseFixB1.bV, Work.BoseFixB1.bA,
        Work.SmallBoxSliding.boxMass_eq_measureReal, MeasureTheory.Measure.real_def])
      (ContDiff.continuous hΨ)
    rw [hnorm, mul_one] at h
    exact h
  -- ## the arithmetic
  have hQnn : 0 ≤ Work.BoseFixB1S.boxQCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
      (Work.BoseFixB1.bA v μ u) Ψ := Work.BoseFixB1S.boxQCount_nonneg _ _ _ _
  have hSV : Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
        (Work.BoseFixB1.bA v μ u) Ψ / Work.BoseFixB1.bV v μ u ≤ 2 * Cn * μ := by
    rw [div_le_iff₀ hvol]
    nlinarith [hcount, hn2, hμ, hCn, hvol]
  have hslack : Work.BoseFixB1.bGapCoeff v μ * Work.BoseFixB1S.boxQCount
        (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u) Ψ
      - Cp * (_root_.BoseGases.a v)
        * (μ + Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bA v μ u) Ψ / Work.BoseFixB1.bV v μ u)
        * Work.BoseFixB1S.boxQCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
          (Work.BoseFixB1.bA v μ u) Ψ
      ≥ C * (_root_.BoseGases.a v) * μ * Work.BoseFixB1S.boxQCount (Work.BoseFixB1.bV v μ u)
          (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u) Ψ := by
    -- `bGapCoeff ≥ K(μa)` with `K = (Cp+1)(1+2Cn) + C`
    have hgb : ((Cp + 1) * (1 + 2 * Cn) + C) * (μ * (_root_.BoseGases.a v))
        ≤ Work.BoseFixB1.bGapCoeff v μ := by
      have h := hgate μ hAdmg
      have hgc : Work.BoseFixB1.bGapCoeff v μ
          = Work.SmallBoxTBWord.tbGapCoeff
              ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
                * Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT := by
        rw [Work.BoseFixB1.bGapCoeff, Work.BoseFixB1.bSide, Work.BoseFixB1.bD, mul_comm]
      rw [hgc]
      linarith [h]
    -- the credit is a fixed multiple of `(μa)·n₊`
    have hcred' : Cp * (_root_.BoseGases.a v)
        * (μ + Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bA v μ u) Ψ / Work.BoseFixB1.bV v μ u)
        ≤ (Cp * (1 + 2 * Cn)) * (μ * (_root_.BoseGases.a v)) := by
      have h0 : 0 ≤ Cp * (_root_.BoseGases.a v) := mul_nonneg hCp ha
      have h2 : μ + Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1.bV v μ u)
            (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u) Ψ / Work.BoseFixB1.bV v μ u
          ≤ (1 + 2 * Cn) * μ := by linarith
      have := mul_le_mul_of_nonneg_left h2 h0
      linarith [this]
    have h1 : Work.BoseFixB1.bGapCoeff v μ * Work.BoseFixB1S.boxQCount
          (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u) Ψ
        ≥ (((Cp + 1) * (1 + 2 * Cn) + C) * (μ * (_root_.BoseGases.a v)))
            * Work.BoseFixB1S.boxQCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bA v μ u) Ψ :=
      mul_le_mul_of_nonneg_right hgb hQnn
    have h2 : Cp * (_root_.BoseGases.a v)
          * (μ + Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
                (Work.BoseFixB1.bA v μ u) Ψ / Work.BoseFixB1.bV v μ u)
          * Work.BoseFixB1S.boxQCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bA v μ u) Ψ
        ≤ ((Cp * (1 + 2 * Cn)) * (μ * (_root_.BoseGases.a v)))
            * Work.BoseFixB1S.boxQCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bA v μ u) Ψ :=
      mul_le_mul_of_nonneg_right hcred' hQnn
    have hkey : ((Cp + 1) * (1 + 2 * Cn) + C) * (μ * (_root_.BoseGases.a v))
          * Work.BoseFixB1S.boxQCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bA v μ u) Ψ
        - (Cp * (1 + 2 * Cn)) * (μ * (_root_.BoseGases.a v))
          * Work.BoseFixB1S.boxQCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bA v μ u) Ψ
        = C * (_root_.BoseGases.a v) * μ * Work.BoseFixB1S.boxQCount (Work.BoseFixB1.bV v μ u)
            (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u) Ψ
          + (1 + 2 * Cn) * (μ * (_root_.BoseGases.a v))
            * Work.BoseFixB1S.boxQCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bA v μ u) Ψ := by ring
    have hnn2 : 0 ≤ (1 + 2 * Cn) * (μ * (_root_.BoseGases.a v))
        * Work.BoseFixB1S.boxQCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
          (Work.BoseFixB1.bA v μ u) Ψ :=
      mul_nonneg (mul_nonneg (by linarith) (mul_nonneg hμ.le ha)) hQnn
    linarith [h1, h2, hkey, hnn2]
  -- ## `SR2Rhs ≤ sbWordCube` (the payment rung + telescope + gap gate)
  have hSR2 : SR2Rhs v h C μ Ψ u ≤ Work.BoseFixB1B.sbWordCube v h μ u Ψ := by
    show Work.BoseFixB1.a0MainLocBox (Work.BoseFixB1.bV v μ u) μ (Work.BoseFixB1.bW v h μ u)
        (Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
          (Work.BoseFixB1.bA v μ u) Ψ)
      + Work.BoseFixB1.bA2 v h μ Ψ u
      + Work.BoseFixB1S.bSpectralCube v μ Ψ u
      + (1 / 2) * ((Work.BoseFixB1S.boxM2 (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bA v μ u)
              (Submission.BoseGases.wSmallPair (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                (Work.BoseFixB1.bD v μ) u (Submission.BoseGases.g2 v h))
            - Work.BoseFixB1.bW v h μ u)
          / (Work.BoseFixB1.bV v μ u) ^ 2)
          * Work.BoseFixB1S.boxPairCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bA v μ u) Ψ
      + C * (_root_.BoseGases.a v) * μ
          * Work.BoseFixB1S.boxQCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bA v μ u) Ψ
      ≤ Work.BoseFixB1B.sbWordCube v h μ u Ψ
    rw [hcube, htel]
    linarith [hpay', hslack]
  -- ## the pointwise row closes the node
  exact le_trans hrow hSR2

end

end Work.BoseSWE
