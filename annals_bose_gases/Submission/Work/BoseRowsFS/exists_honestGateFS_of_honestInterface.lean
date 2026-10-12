import ChallengeDeps
import Submission.Work.BoseBoxFock.exists_honestModes
import Submission.Work.BoseRowsFS.HonestInterface
import Submission.Work.BoseRowsFS.RowIntOneRegime_honest
import Submission.Work.BoseRowsFS.exists_honestGateFS_of_regime_rows
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseRowsFS

open scoped Real BigOperators Topology
open MeasureTheory Metric

theorem exists_honestGateFS_of_honestInterface
    {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} (R : ℝ) (hR : 0 < R)
    (hav : 0 < _root_.BoseGases.a v)
    (hv_nonneg : ∀ x : EuclideanSpace ℝ (Fin 3), 0 ≤ v x)
    (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R)
    (hthr : Work.BoseGateFS.GateThresholds v h fc fu R)
    (H : Work.BoseRowsFS.HonestInterface R hthr)
    (hrow3 : ∀ (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ),
      (∀ μ, hthr.Ng μ ≤ (HM μ).N) →
      ∀ μ : ℝ, 0 < μ → μ * _root_.BoseGases.a v ^ 3 ≤ hthr.εg →
      ∀ ρ : ℝ, Work.BoseGateFS.AdmRho (Work.BoseRowsFS.honE v h fc fu HM μ) ρ →
      ∀ Ψ : (Work.BoseRowsFS.honF v h fc fu HM μ).H,
        2 * ρ * (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0
            * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
                ((Work.BoseRowsFS.honT v h fc fu HM μ).Gop
                  (Work.BoseRowsFS.honE v h fc fu HM μ))
          ≤ (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
              ((Work.BoseRowsFS.honF v h fc fu HM μ).Q2ex
                (Work.BoseFixR.KzEnvAt (Work.BoseRowsFS.honE v h fc fu HM μ) ρ))
            + ((Work.BoseRowsFS.honE v h fc fu HM μ).b / 400)
                * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
                    ((Work.BoseRowsFS.honT v h fc fu HM μ).gapOpT
                      (Work.BoseFixR.KzEnvAt (Work.BoseRowsFS.honE v h fc fu HM μ) ρ))
            + (1 / 2) * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
                ((Work.BoseRowsFS.honF v h fc fu HM μ).dNumOpR
                  (Work.BoseFixR.KzEnvAt (Work.BoseRowsFS.honE v h fc fu HM μ) ρ)
                  (fun k => Work.BoseGateFS.rHi (Work.BoseRowsFS.honF v h fc fu HM μ)
                    (Work.BoseRowsFS.honE v h fc fu HM μ) k
                    ∧ ¬ (Work.BoseRowsFS.honF v h fc fu HM μ).PHq
                        (Work.BoseRowsFS.honE v h fc fu HM μ).KH
                        (Work.BoseRowsFS.honE v h fc fu HM μ).aScat k))) :
    ∃ K₀ b₀ : ℝ, 0 ≤ K₀ ∧ 0 < b₀ ∧ Work.BoseBoxFock.HonestGateFS v h fc fu K₀ b₀ := by
  classical
  -- ## 0. The `HM`-independent régime rows.
  --
  -- Two of the rows (`1 ≤ ℓ`, `R ≤ ℓ χ_{R₀}`) are free of the mode choice `HM`;
  -- to read them out of `hthr.dil` we exhibit one mode choice with `N ≥ Ng`.
  obtain ⟨HM0, hHM0⟩ : ∃ HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ,
      ∀ μ, hthr.Ng μ ≤ (HM μ).N := by
    choose HM hN using fun μ => Work.BoseBoxFock.exists_honestModes v μ (hthr.Ng μ)
    exact ⟨HM, fun μ => le_of_eq (hN μ).symm⟩
  have hrége : ∀ μ : ℝ, 0 < μ → μ * _root_.BoseGases.a v ^ 3 ≤ hthr.εg →
      1 ≤ Work.BoseBoxFock.ellH v μ
        ∧ R ≤ Work.BoseBoxFock.ellH v μ * Submission.BoseGases.chiR0 := by
    intro μ hμ hε
    obtain ⟨h1, _h2, h3, _h4, _h5, _h6⟩ := hthr.dil HM0 hHM0 μ hμ hε
    exact ⟨h1, h3⟩
  -- ## 1. The two diluteness-restricted rows at the interface's threshold.
  --  Row 1 (FS `eq:I2-integral`) and row 2 (FS `lem:EstimateIntegral`) are the
  --  contents of the corpus theorems `RowSumW1sq_regime`, `RowIntOneRegime_honest`,
  --  which consume exactly the `HonestInterface` fields.
  obtain ⟨Cws, hCws0, hrow1⟩ :=
    RowSumW1sq_regime (v := v) (h := h) (fc := fc) (fu := fu) (R := R)
      hR hav hv_nonneg hvrad hv_supp hthr.εg hrége
  obtain ⟨ε₀, Kint, hε₀pos, hε₀le, hKint0, hrow2⟩ :=
    RowIntOneRegime_honest (v := v) (h := h) (fc := fc) (fu := fu) R hR hav hv_nonneg
      hvrad hv_supp H.Cw H.Cw_nonneg H.decayW H.decayg hthr.Ng hthr.εg hthr.pos hrége
      H.cut H.tail H.fsp H.fspKz H.rkh H.a16
  -- ## 2. Assembly at the shrunk threshold `min εg ε₀`.
  --
  --  Row 2 is only available below the internally produced threshold `ε₀`, while
  --  rows 1 and 3 hold below `εg`; `GateThresholds.mono` (whose every field is
  --  monotone in the threshold) moves the whole bundle to `min εg ε₀`.
  refine exists_honestGateFS_of_regime_rows R hR hav hv_nonneg hvrad hv_supp
    (hthr.mono (εg' := min hthr.εg ε₀) (lt_min hthr.pos hε₀pos) (min_le_left _ _))
    Cws hCws0 ?_ Kint hKint0 ?_ ?_
  · -- row 1 below the shrunk threshold
    intro HM hN μ hμ hε
    exact hrow1 HM μ hμ (le_trans hε (min_le_left _ _))
  · -- row 2 below the shrunk threshold (`ε₀`-availability suffices)
    intro HM hN μ hμ hε ρ hρ
    exact hrow2 HM hN μ hμ (le_trans hε (min_le_right _ _)) ρ hρ
  · -- row 3 below the shrunk threshold
    intro HM hN μ hμ hε ρ hρ Ψ
    exact hrow3 HM hN μ hμ (le_trans hε (min_le_left _ _)) ρ hρ Ψ

end Work.BoseRowsFS
