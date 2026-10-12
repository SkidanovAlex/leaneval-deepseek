import ChallengeDeps
import Submission.Work.BoseBogFS.honestFsCutoffRows
import Submission.Work.BoseBogFS.honestFsEpsEta
import Submission.Work.BoseBogFS.honestFsEpsLog
import Submission.Work.BoseBogFS.honestFsI2
import Submission.Work.BoseBogFS.honestFsLogRows
import Submission.Work.BoseBogFS.honestFsParamsRows
import Submission.Work.BoseBogFS.honestFsSupp
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBogFS

/-- **The honest parameter regime of `lem:BogIntegral` is inhabited.**  There is `ε₀ > 0`
such that for every admissible `μ` (`Work.BoseBoxFix.Adm v ε₀ μ`) and every `ρ` with
`Work.BoseBoxFock.CloseCondFS v μ ρ`, the affine kernel `bogKernel v R ρ μ` (defined in
`Work.BoseBogFS.BogFSKernel` as `honKernel (max 0 (bogEta v R ρ)) (max 0 (bogT v R μ))`, i.e.
`β(r) = 8π + max 0 (16πR√(ρa))·r` on `[0, max 0 (10⁶(1+log(1/dil))/lhyEps)]` and `0` beyond)
satisfies FS's `FsI1Regime` at the honest data `(a v, R, ρ, μ)`, FS's kinetic cutoffs
`c₁ = bogC1 v ρ μ = (2 s ℓ √(ρa))⁻¹`, `c₂ = bogC2 v ρ μ = (2 d s ℓ √(ρa))⁻¹`, and the parameter
block `ε_T, K_ℓ, s, d` of `paramsAt μ (a v)`.

All fields are arithmetic in the parameter block: with `D = μ(a v)³`, `X = D^{1/323}`,
`K_ℓ = X^{-3/2}`, `s = X`, `d = X⁶`, `ε_T = X^{23/4}`,
`lhyEps = (μa)^{1/4}√R + X^{23/4} + X^{1/2}(1 + (162/323)log(1/D)) +
X^{1/4}(1 + (156/323)log(1/D))` (`Work.BoseBogFS.lhyEps_diluteness`) and
`ℓ = a·D^{-163/323}` (`Work.BoseBox.sideAt_eq_rpow`).  `Adm` gives `D ≤ ε₀`, `μ > 0` and
`ParamsOK` (hence `0 ≤ ε_T ≤ 1/2`, `d ≤ 1`, `1 ≤ K_ℓs`), and `CloseCondFS` gives
`|ρ − μ| ≤ μK_ℓ^{-2}/(2¹⁴π)` hence `9/10 μ ≤ ρ ≤ 11/10 μ`.  Each dominance field then holds
for small `ε₀` since the only unbounded quantities are negative powers of `D`, dominated by
the `1 + c·log(1/D)` slots of `lhyEps`; the `η`-fields use
`lhyEps ≥ (μa)^{1/4}√R` (giving `η ≤ lhyEps` and `ηT ≤ 1` jointly with
`(μa)^{1/4}√R ≤ 1/(16π√(11/10))`, absorbable in `ε₀`).  Note `hEpsEta` and `hηT` refer to
`max 0 (bogEta v R ρ)`, and `hI2` needs the kernel bound
`fsI2 (bogKernel v R ρ μ) ≤ 2π(8π + ηT)²T` (`Work.BoseB6Est.fsI2_le_bound`). -/
theorem honestFsI1Regime {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R : ℝ} (hR : 0 < R)
    (hav : 0 < _root_.BoseGases.a v) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ → ∀ ρ : ℝ,
      Work.BoseBoxFock.CloseCondFS v μ ρ →
      Work.BoseB6Est.FsI1Regime (Work.BoseBogFS.bogKernel v R ρ μ) (_root_.BoseGases.a v) R ρ μ
        ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT)
        (Work.BoseBogFS.bogC1 v ρ μ) (Work.BoseBogFS.bogC2 v ρ μ)
        ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl)
        ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s)
        ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) := by
  obtain ⟨e1, he1, row1⟩ := honestFsParamsRows hR hav
  obtain ⟨e2, he2, row2⟩ := honestFsCutoffRows hR hav
  obtain ⟨e3, he3, row3⟩ := honestFsEpsEta hR hav
  obtain ⟨e4, he4, row4⟩ := honestFsEtaT hR hav
  obtain ⟨e5, he5, row5⟩ := honestFsSupp hR hav
  obtain ⟨e6, he6, row6⟩ := honestFsI2 hR hav
  obtain ⟨e7, he7, row7⟩ := honestFsEpsLog hR hav
  obtain ⟨e8, he8, row8⟩ := honestFsLogRows hR hav
  set E8 : ℝ := min e8 (coreBound v R) with hE8
  set E7 : ℝ := min e7 E8 with hE7
  set E6 : ℝ := min e6 E7 with hE6
  set E5 : ℝ := min e5 E6 with hE5
  set E4 : ℝ := min e4 E5 with hE4
  set E3 : ℝ := min e3 E4 with hE3
  set E2 : ℝ := min e2 E3 with hE2
  set E : ℝ := min e1 E2 with hE
  have hle1 : E ≤ e1 := by rw [hE]; exact min_le_left _ _
  have hEE2 : E ≤ E2 := by rw [hE]; exact min_le_right _ _
  have hle2 : E2 ≤ e2 := by rw [hE2]; exact min_le_left _ _
  have hE2E3 : E2 ≤ E3 := by rw [hE2]; exact min_le_right _ _
  have hle3 : E3 ≤ e3 := by rw [hE3]; exact min_le_left _ _
  have hE3E4 : E3 ≤ E4 := by rw [hE3]; exact min_le_right _ _
  have hle4 : E4 ≤ e4 := by rw [hE4]; exact min_le_left _ _
  have hE4E5 : E4 ≤ E5 := by rw [hE4]; exact min_le_right _ _
  have hle5 : E5 ≤ e5 := by rw [hE5]; exact min_le_left _ _
  have hE5E6 : E5 ≤ E6 := by rw [hE5]; exact min_le_right _ _
  have hle6 : E6 ≤ e6 := by rw [hE6]; exact min_le_left _ _
  have hE6E7 : E6 ≤ E7 := by rw [hE6]; exact min_le_right _ _
  have hle7 : E7 ≤ e7 := by rw [hE7]; exact min_le_left _ _
  have hE7E8 : E7 ≤ E8 := by rw [hE7]; exact min_le_right _ _
  have hle8 : E8 ≤ e8 := by rw [hE8]; exact min_le_left _ _
  have hleC : E8 ≤ coreBound v R := by rw [hE8]; exact min_le_right _ _
  have hE8pos : 0 < E8 := by rw [hE8]; exact lt_min he8 (coreBound_pos hR hav)
  have hE7pos : 0 < E7 := by rw [hE7]; exact lt_min he7 hE8pos
  have hE6pos : 0 < E6 := by rw [hE6]; exact lt_min he6 hE7pos
  have hE5pos : 0 < E5 := by rw [hE5]; exact lt_min he5 hE6pos
  have hE4pos : 0 < E4 := by rw [hE4]; exact lt_min he4 hE5pos
  have hE3pos : 0 < E3 := by rw [hE3]; exact lt_min he3 hE4pos
  have hE2pos : 0 < E2 := by rw [hE2]; exact lt_min he2 hE3pos
  have hEpos : 0 < E := by rw [hE]; exact lt_min he1 hE2pos
  refine ⟨E, hEpos, ?_⟩
  intro μ hAdm ρ hclose
  have hA1 : Work.BoseBoxFix.Adm v e1 μ := adm_mono hle1 hAdm
  have hA2 : Work.BoseBoxFix.Adm v e2 μ := adm_mono (le_trans hEE2 hle2) hAdm
  have hA3 : Work.BoseBoxFix.Adm v e3 μ := adm_mono (le_trans hEE2 (le_trans hE2E3 hle3)) hAdm
  have hA4 : Work.BoseBoxFix.Adm v e4 μ := adm_mono (le_trans hEE2 (le_trans hE2E3 (le_trans hE3E4 hle4))) hAdm
  have hA5 : Work.BoseBoxFix.Adm v e5 μ := adm_mono (le_trans hEE2 (le_trans hE2E3 (le_trans hE3E4 (le_trans hE4E5 hle5)))) hAdm
  have hA6 : Work.BoseBoxFix.Adm v e6 μ := adm_mono (le_trans hEE2 (le_trans hE2E3 (le_trans hE3E4 (le_trans hE4E5 (le_trans hE5E6 hle6))))) hAdm
  have hA7 : Work.BoseBoxFix.Adm v e7 μ := adm_mono (le_trans hEE2 (le_trans hE2E3 (le_trans hE3E4 (le_trans hE4E5 (le_trans hE5E6 (le_trans hE6E7 hle7)))))) hAdm
  have hA8 : Work.BoseBoxFix.Adm v e8 μ := adm_mono (le_trans hEE2 (le_trans hE2E3 (le_trans hE3E4 (le_trans hE4E5 (le_trans hE5E6 (le_trans hE6E7 (le_trans hE7E8 hle8))))))) hAdm
  have hcore : Core v R μ ρ :=
    core_bounds (δ := E) hR hav (le_trans hEE2 (le_trans hE2E3 (le_trans hE3E4
      (le_trans hE4E5 (le_trans hE5E6 (le_trans hE6E7 (le_trans hE7E8 hleC)))))))
      μ ρ hAdm.1 hAdm.2.1 hclose
  obtain ⟨hKl, hs, hd, hεT0, hεT1, hd1, hKl1, hlog1, hEpsT, hEpsR, hEpsKl, hT1, hc1T⟩ :=
    row1 μ hA1 ρ hclose
  obtain ⟨hc1nn, hc12, hcc1⟩ := row2 μ hA2 ρ hclose
  obtain ⟨hηT, hB⟩ := row4 μ hA4 ρ hclose
  obtain ⟨hTsupp, hTm⟩ := row5 μ hA5 ρ hclose
  exact
    { ha := hav
      hR := hR.le
      hρz := hcore.hρ0
      hμ := hAdm.1
      hKl := hKl
      hs := hs
      hd := hd
      hε0 := hεT0
      hε1 := hεT1
      hc1 := hc1nn
      hc12 := hc12
      hcc1 := hcc1
      hc1val := bogC1_eq v ρ μ hav hAdm.1 hcore.hρ0
      hc2val := bogC2_eq v ρ μ hav hAdm.1 hcore.hρ0
      hclose1 := hcore.hρlo
      hclose2 := hcore.hρhi
      hKl1 := hKl1
      hd1 := hd1
      hlog1 := hlog1
      hB := hB
      hηT := hηT
      hT1 := hT1
      hc1T := hc1T
      hTsupp := hTsupp
      hTm := hTm
      hsmall := hcore.hsmall
      hI2 := row6 μ hA6 ρ hclose
      hEpsEta := row3 μ hA3 ρ hclose
      hEpsT := hEpsT
      hEpsR := hEpsR
      hEpsKl := hEpsKl
      hEpsLog := row7 μ hA7 ρ hclose
      hEpsLogT := (row8 μ hA8 ρ hclose).1
      hEpsTlog := (row8 μ hA8 ρ hclose).2.1
      hTtail := (row8 μ hA8 ρ hclose).2.2 }

end Work.BoseBogFS
