import ChallengeDeps
import Submission.Work.BoseBogFS.CleanRiemScaled
import Submission.Work.BoseBogFS.betaSc_sub_le
import Submission.Work.BoseBogFS.phiC_osc_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBogFS

set_option maxHeartbeats 1000000

/-- **The master per-cell bound of the scaled clean bracket.**

`psiSc = phiC (τ_s) (β_s) ‖·‖` (`psiSc_eq_phiC_of`) on the branch `τ_s + 2β_s ≥ 0`, so the whole
content is the three-variable oscillation `phiC_osc_le`.  The only genuinely new input is that the
box hypotheses (`hbox`) force `r_lo = ‖tSca n‖ − Δ > 0`: `u_lo = τ_s(r_lo) > 0` while `τ̃ = 0` on
`(−∞,1]` and `c_i > 0`, so a nonpositive `r_lo` would make both `τ̃(r_lo/c_i)` vanish. -/
theorem psiSc_sub_le_master {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {R ρ μ : ℝ}
    (hR : 0 < R) (hρ : 0 < ρ) (hav : 0 < _root_.BoseGases.a v) (hv : ∀ x, 0 ≤ v x)
    (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hRℓ : R ≤ Work.BoseFixR.ell v μ * Submission.BoseGases.chiR0)
    (hμ : 0 < μ) (hdil : Work.BoseFixR.dil v μ ≤ 1)
    (hc1 : 0 < Work.BoseBogFS.bogC1 v ρ μ) (hc2 : 0 < Work.BoseBogFS.bogC2 v ρ μ)
    (heT0 : 0 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT)
    (heT1 : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT ≤ 1)
    {n : Fin 3 → ℤ} {x : EuclideanSpace ℝ (Fin 3)} {Δ oscβ : ℝ}
    (hΔ : 0 < Δ) (hx : ‖x - Work.BoseBogFS.tSca v ρ μ n‖ ≤ Δ)
    (hosc : ∀ y : EuclideanSpace ℝ (Fin 3), ‖y - Work.BoseBogFS.tSca v ρ μ n‖ ≤ Δ →
        |Work.BoseBogFS.betaSc v h ρ μ y
          - Work.BoseBogFS.betaSc v h ρ μ (Work.BoseBogFS.tSca v ρ μ n)| ≤ oscβ)
    (hbox : let r_lo := ‖Work.BoseBogFS.tSca v ρ μ n‖ - Δ
            let r_hi := ‖Work.BoseBogFS.tSca v ρ μ n‖ + Δ
            let u_lo := Work.BoseBogFS.tauScRad v ρ μ r_lo
            let u_hi := Work.BoseBogFS.tauScRad v ρ μ r_hi
            let v_lo := Work.BoseBogFS.betaSc v h ρ μ (Work.BoseBogFS.tSca v ρ μ n) - oscβ
            let W_lo := Real.sqrt (u_lo ^ 2 + 2 * u_lo * v_lo)
            let S_lo := u_lo + v_lo + W_lo
            0 < u_lo ∧ u_hi ≤ r_lo ^ 2 ∧ 0 < u_lo + 2 * v_lo ∧ 0 < S_lo ∧ 0 < W_lo)
    (hxu : 0 ≤ Work.BoseBogFS.tauSc v ρ μ x)
    (hxu2 : 0 ≤ Work.BoseBogFS.tauSc v ρ μ x + 2 * Work.BoseBogFS.betaSc v h ρ μ x) :
    Work.BoseBogFS.psiSc v h ρ μ (Work.BoseBogFS.tSca v ρ μ n)
        - Work.BoseBogFS.psiSc v h ρ μ x
      ≤ (let r_lo := ‖Work.BoseBogFS.tSca v ρ μ n‖ - Δ
         let r_hi := ‖Work.BoseBogFS.tSca v ρ μ n‖ + Δ
         let u_lo := Work.BoseBogFS.tauScRad v ρ μ r_lo
         let u_hi := Work.BoseBogFS.tauScRad v ρ μ r_hi
         let v_lo := Work.BoseBogFS.betaSc v h ρ μ (Work.BoseBogFS.tSca v ρ μ n) - oscβ
         let v_hi := Work.BoseBogFS.betaSc v h ρ μ (Work.BoseBogFS.tSca v ρ μ n) + oscβ
         let W_lo := Real.sqrt (u_lo ^ 2 + 2 * u_lo * v_lo)
         let S_lo := u_lo + v_lo + W_lo
         let V := max |v_lo| |v_hi|
         let D := max 0 (r_hi ^ 2 - u_lo)
         2 * (V ^ 2 / (S_lo * W_lo)) * (u_hi - u_lo)
           + 2 * (V * (2 * D + 2 * V) / (r_lo ^ 2 * S_lo)
               + V ^ 2 * (1 + u_hi / W_lo) / S_lo ^ 2) * (v_hi - v_lo)
           + 2 * (V ^ 2 / 2) * (1 / r_lo ^ 2 - 1 / r_hi ^ 2)) := by
  have hP : 0 < ρ * _root_.BoseGases.a v := mul_pos hρ hav
  -- the `hbox` components, at the raw expressions
  obtain ⟨hb1, hb2, hb3, hb4, _hb5⟩ := hbox
  -- `oscβ ≥ 0` (witnessed by `y = x`)
  have hoscβ : 0 ≤ oscβ := le_trans (abs_nonneg _) (hosc x hx)
  -- the box lower radius is positive: a nonpositive `r_lo` kills the kinetic symbol
  have hrlopos : 0 < ‖Work.BoseBogFS.tSca v ρ μ n‖ - Δ := by
    by_contra hcon
    push_neg at hcon
    have hzero : Work.BoseBogFS.tauScRad v ρ μ (‖Work.BoseBogFS.tSca v ρ μ n‖ - Δ) = 0 := by
      rw [tauScRad_eq v hP]
      have h1 : Work.BoseBoxFock.tauProf
          ((‖Work.BoseBogFS.tSca v ρ μ n‖ - Δ) / bogC1 v ρ μ) = 0 :=
        Work.BoseBoxFock.tauProf_eq_zero_of_le_one
          (by have := div_nonpos_of_nonpos_of_nonneg hcon hc1.le; linarith)
      have h2 : Work.BoseBoxFock.tauProf
          ((‖Work.BoseBogFS.tSca v ρ μ n‖ - Δ) / bogC2 v ρ μ) = 0 :=
        Work.BoseBoxFock.tauProf_eq_zero_of_le_one
          (by have := div_nonpos_of_nonpos_of_nonneg hcon hc2.le; linarith)
      rw [h1, h2]
      ring
    rw [hzero] at hb1
    exact lt_irrefl 0 hb1
  -- monotonicity of the scaled kinetic symbol
  have hmono : Monotone (Work.BoseBogFS.tauScRad v ρ μ) := tauScRad_mono hP heT0 heT1 hc1 hc2
  -- radius bounds for the two points
  have hrn : ‖Work.BoseBogFS.tSca v ρ μ n‖ - Δ ≤ ‖Work.BoseBogFS.tSca v ρ μ n‖ := by linarith [hΔ]
  have hrn2 : ‖Work.BoseBogFS.tSca v ρ μ n‖ ≤ ‖Work.BoseBogFS.tSca v ρ μ n‖ + Δ := by
    linarith [hΔ]
  have hrx : ‖Work.BoseBogFS.tSca v ρ μ n‖ - Δ ≤ ‖x‖ := by
    have h1 : ‖Work.BoseBogFS.tSca v ρ μ n‖ - ‖x‖
        ≤ ‖Work.BoseBogFS.tSca v ρ μ n - x‖ := norm_sub_norm_le _ _
    rw [norm_sub_rev] at h1
    linarith [h1, hx]
  have hrx2 : ‖x‖ ≤ ‖Work.BoseBogFS.tSca v ρ μ n‖ + Δ := by
    have h1 : ‖x‖ - ‖Work.BoseBogFS.tSca v ρ μ n‖
        ≤ ‖x - Work.BoseBogFS.tSca v ρ μ n‖ := norm_sub_norm_le _ _
    linarith [h1, hx]
  -- the kinetic-symbol ranges
  have hun : Work.BoseBogFS.tauScRad v ρ μ (‖Work.BoseBogFS.tSca v ρ μ n‖ - Δ)
      ≤ Work.BoseBogFS.tauSc v ρ μ (Work.BoseBogFS.tSca v ρ μ n) := by
    rw [tauSc_eq_tauScRad]; exact hmono hrn
  have hun2 : Work.BoseBogFS.tauSc v ρ μ (Work.BoseBogFS.tSca v ρ μ n)
      ≤ Work.BoseBogFS.tauScRad v ρ μ (‖Work.BoseBogFS.tSca v ρ μ n‖ + Δ) := by
    rw [tauSc_eq_tauScRad]; exact hmono hrn2
  have hux : Work.BoseBogFS.tauScRad v ρ μ (‖Work.BoseBogFS.tSca v ρ μ n‖ - Δ)
      ≤ Work.BoseBogFS.tauSc v ρ μ x := by
    rw [tauSc_eq_tauScRad]; exact hmono hrx
  have hux2 : Work.BoseBogFS.tauSc v ρ μ x
      ≤ Work.BoseBogFS.tauScRad v ρ μ (‖Work.BoseBogFS.tSca v ρ μ n‖ + Δ) := by
    rw [tauSc_eq_tauScRad]; exact hmono hrx2
  -- the pairing-coefficient ranges
  have hbx := hosc x hx
  rw [abs_le] at hbx
  have hvx : Work.BoseBogFS.betaSc v h ρ μ (Work.BoseBogFS.tSca v ρ μ n) - oscβ
      ≤ Work.BoseBogFS.betaSc v h ρ μ x := by linarith [hbx.1]
  have hvx2 : Work.BoseBogFS.betaSc v h ρ μ x
      ≤ Work.BoseBogFS.betaSc v h ρ μ (Work.BoseBogFS.tSca v ρ μ n) + oscβ := by
    linarith [hbx.2]
  have hvn : Work.BoseBogFS.betaSc v h ρ μ (Work.BoseBogFS.tSca v ρ μ n) - oscβ
      ≤ Work.BoseBogFS.betaSc v h ρ μ (Work.BoseBogFS.tSca v ρ μ n) := by linarith [hoscβ]
  have hvn2 : Work.BoseBogFS.betaSc v h ρ μ (Work.BoseBogFS.tSca v ρ μ n)
      ≤ Work.BoseBogFS.betaSc v h ρ μ (Work.BoseBogFS.tSca v ρ μ n) + oscβ := by
    linarith [hoscβ]
  -- the remaining `phiC_osc_le` hypotheses
  have hulh : Work.BoseBogFS.tauScRad v ρ μ (‖Work.BoseBogFS.tSca v ρ μ n‖ - Δ)
      ≤ Work.BoseBogFS.tauScRad v ρ μ (‖Work.BoseBogFS.tSca v ρ μ n‖ + Δ) :=
    hmono (by linarith [hΔ])
  have hvlh : Work.BoseBogFS.betaSc v h ρ μ (Work.BoseBogFS.tSca v ρ μ n) - oscβ
      ≤ Work.BoseBogFS.betaSc v h ρ μ (Work.BoseBogFS.tSca v ρ μ n) + oscβ := by
    linarith [hoscβ]
  have hW : 0 < Work.BoseBogFS.tauScRad v ρ μ (‖Work.BoseBogFS.tSca v ρ μ n‖ - Δ) ^ 2
      + 2 * Work.BoseBogFS.tauScRad v ρ μ (‖Work.BoseBogFS.tSca v ρ μ n‖ - Δ)
          * (Work.BoseBogFS.betaSc v h ρ μ (Work.BoseBogFS.tSca v ρ μ n) - oscβ) := by
    have hp := mul_pos hb1 hb3
    nlinarith [hp]
  -- the master oscillation bound
  have key := phiC_osc_le
    (u_lo := Work.BoseBogFS.tauScRad v ρ μ (‖Work.BoseBogFS.tSca v ρ μ n‖ - Δ))
    (u_hi := Work.BoseBogFS.tauScRad v ρ μ (‖Work.BoseBogFS.tSca v ρ μ n‖ + Δ))
    (v_lo := Work.BoseBogFS.betaSc v h ρ μ (Work.BoseBogFS.tSca v ρ μ n) - oscβ)
    (v_hi := Work.BoseBogFS.betaSc v h ρ μ (Work.BoseBogFS.tSca v ρ μ n) + oscβ)
    (r_lo := ‖Work.BoseBogFS.tSca v ρ μ n‖ - Δ)
    (r_hi := ‖Work.BoseBogFS.tSca v ρ μ n‖ + Δ)
    (u_n := Work.BoseBogFS.tauSc v ρ μ (Work.BoseBogFS.tSca v ρ μ n))
    (v_n := Work.BoseBogFS.betaSc v h ρ μ (Work.BoseBogFS.tSca v ρ μ n))
    (r_n := ‖Work.BoseBogFS.tSca v ρ μ n‖)
    (u_x := Work.BoseBogFS.tauSc v ρ μ x) (v_x := Work.BoseBogFS.betaSc v h ρ μ x)
    (r_x := ‖x‖)
    hb1 hulh hvlh hrlopos (by linarith [hΔ]) hW hb4 hb2
    hun hun2 hux hux2 hvn hvn2 hvx hvx2 hrn hrn2 hrx hrx2
  -- the branch hypotheses of `psiSc_eq_phiC_of` at the two points
  have htn0 : 0 ≤ Work.BoseBogFS.tauSc v ρ μ (Work.BoseBogFS.tSca v ρ μ n) := by
    rw [tauSc_eq_tauScRad]
    exact tauScRad_nonneg v hP heT0 heT1 _
  have htn2 : 0 ≤ Work.BoseBogFS.tauSc v ρ μ (Work.BoseBogFS.tSca v ρ μ n)
      + 2 * Work.BoseBogFS.betaSc v h ρ μ (Work.BoseBogFS.tSca v ρ μ n) := by
    have h4 : Work.BoseBogFS.betaSc v h ρ μ (Work.BoseBogFS.tSca v ρ μ n) - oscβ
        ≤ Work.BoseBogFS.betaSc v h ρ μ (Work.BoseBogFS.tSca v ρ μ n) := by linarith [hoscβ]
    linarith [hb3, hun, h4]
  rw [psiSc_eq_phiC_of (v := v) (h := h) (ρ := ρ) (μ := μ)
        (t := Work.BoseBogFS.tSca v ρ μ n) htn0 htn2,
      psiSc_eq_phiC_of (v := v) (h := h) (ρ := ρ) (μ := μ) (t := x) hxu hxu2]
  exact le_trans (le_abs_self _) key

end Work.BoseBogFS
