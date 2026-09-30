import Mathlib
import Submission.Work.BMF.mr_core_defs
import Submission.Work.BMF.mr_direct_range_defs
import Submission.Work.BMF.mr_core.badPartAux.remPointwiseRange
import Submission.Work.BMF.mr_direct.dist_scale_transfer_wide
import Submission.Work.BMF.mr_direct.D_mono
import Submission.Work.BMF.mr_core.bpcell_remWindows
import Submission.Work.BMF.mr_core.bpcell_dist
import Submission.Work.BMF.mr_core.bpcell_logratio

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mr_core

/-- Pointwise bound for the coarse-cell remainder polynomial, in the form
`‖R_j(t)‖ ≤ C·Ac B·((1+B²/2)e^{-B²/8} + 1/√T₀)`.

ROUTE (verified by reviewers): apply `Work.BMF.mr_direct.remPointwiseRange` with
`P := Pc Y`, `Q := Qc B Y`, `X₁ := Y * exp(-((j:ℝ)+1)/K)`, `X₂ := 3*Y*exp(-(j:ℝ)/K)`,
`X := X₂` (so `X/4 ≤ X₁` because `exp(1/K) ≤ 4/3` when `K ≥ 4`, `X ≤ X₂ ≤ 4X`),
`T₀ := T₀`, `t := t`, and with the parameter `B' := Real.sqrt (B^2/2)`.
* the sieve hypothesis is exactly `B'^2/8 = B^2/16`;
* the distance hypothesis at scales `x ∈ [X^{1/4}/16, 16X]` follows from the given hypothesis at
  scale `Y` via `Work.BMF.mr_direct.dist_scale_transfer_wide` (with `M := 4*T₀`; needs
  `8 ≤ B` and `16^8 ≤ Y`, both available) applied to `x ∈ [Y^{1/8}, 16*Y]`, and then
  `Work.BMF.mr_direct.D_mono` extends the same bound to all `x ≥ 16*Y`;
  `X^{1/4}/16 ≥ Y^{1/8}` and `16*X ≥ Y^{1/8}` use `j ∈ indexSet K (Pc Y) (Qc B Y)`
  (so `e^{j/K} ≤ Qc B Y`) together with `exp (logQc B Y) ≤ Y^{1/2}/16^4`;
  the remaining window conditions (`16 ≤ X`, `1 ≤ T₀`) are immediate.
* finally `Real.log (Qc B Y) / Real.log (Pc Y) = Ac B` (from `logQc = Ac B * logPc`) and
  `B'^2/4 = B^2/8`, `1 + B'^2 = 1 + B^2/2`. -/
theorem badPartCell_remBound :
    ∃ C : ℝ, 0 < C ∧ ∀ B : ℝ, 8 ≤ B → ∀ K : ℝ, 4 ≤ K →
      ∀ (T₀ : ℝ) (g : ℕ → ℂ) (Y : ℝ) (j : ℕ) (t : ℝ),
        1 ≤ T₀ →
        (16 : ℝ) ^ 8 ≤ Y →
        g 1 = 1 →
        (∀ m n : ℕ, m.Coprime n → g (m * n) = g m * g n) → (∀ n, ‖g n‖ ≤ 1) →
        Real.exp (Work.BMF.mrCore.logQc B Y) ≤ Y ^ (1 / 2 : ℝ) / 16 ^ 4 →
        (∑ p ∈ Work.BMF.primesIn (Work.BMF.mrCore.Pc Y) (Work.BMF.mrCore.Qc B Y),
            1 / (p : ℝ)) ≤ B ^ 2 / 16 →
        (∀ u : ℝ, |u| ≤ 4 * T₀ →
          B ≤ BoundedMultiplicativeFunctions.𝔻 g (fun n ↦ (n : ℂ) ^ (Complex.I * u)) Y) →
        j ∈ Work.BMF.mrDirect.indexSet K (Work.BMF.mrCore.Pc Y) (Work.BMF.mrCore.Qc B Y) →
        |t| ≤ 2 * T₀ →
        ‖Work.BMF.mrDirect.remPolyR g (Work.BMF.mrCore.Pc Y) (Work.BMF.mrCore.Qc B Y) K Y (3 * Y) j t‖
          ≤ C * (Work.BMF.mrCore.Ac B) *
              ((1 + B ^ 2 / 2) * Real.exp (-(B ^ 2 / 8)) + 1 / Real.sqrt T₀) := by
  obtain ⟨C, hC, hrm⟩ := Work.BMF.mr_direct.remPointwiseRange
  refine ⟨C, hC, ?_⟩
  intro B hB K hK T₀ g Y j t hT₀ hY8 hg1 hgmul hgb hlogQc hsievesum hdist hj ht
  have hYpos : (0 : ℝ) < Y := by
    have : (0 : ℝ) < (16 : ℝ) ^ 8 := by norm_num
    linarith
  -- the window arithmetic at the scale `X = Y * exp (-(j/K))`
  obtain ⟨hX16, hlow, hX4, hX12, hX2⟩ := bpcell_remWindows hK hY8 hlogQc hj
  -- the parameter `B' = √(B²/2)`
  have hB'1 : (1 : ℝ) ≤ Real.sqrt (B ^ 2 / 2) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hB'2 : Real.sqrt (B ^ 2 / 2) ^ 2 = B ^ 2 / 2 := Real.sq_sqrt (by positivity)
  -- the distance hypothesis at all scales of the window
  have hdistX : ∀ x : ℝ, (Y * Real.exp (-(j : ℝ) / K)) ^ (1 / 4 : ℝ) / 16 ≤ x →
      x ≤ 16 * (Y * Real.exp (-(j : ℝ) / K)) → ∀ u : ℝ, |u| ≤ 4 * T₀ →
      Real.sqrt (B ^ 2 / 2) ≤
        BoundedMultiplicativeFunctions.𝔻 g (fun n ↦ (n : ℂ) ^ (Complex.I * u)) x :=
    bpcell_dist (B := B) (T₀ := T₀) (Y := Y) (X := Y * Real.exp (-(j : ℝ) / K)) (g := g)
      hB hY8 hgb hdist (mul_nonneg hYpos.le (Real.exp_pos _).le) hlow
  -- the sieve hypothesis with the parameter `B'`
  have hsieve' : (∑ p ∈ Work.BMF.primesIn (Work.BMF.mrCore.Pc Y) (Work.BMF.mrCore.Qc B Y),
      1 / (p : ℝ)) ≤ Real.sqrt (B ^ 2 / 2) ^ 2 / 8 := by
    rw [hB'2]; linarith
  -- the two coarse parameters are in range
  have h16le : (16 : ℝ) ≤ Y := by
    have : (16 : ℝ) ≤ (16 : ℝ) ^ 8 := by norm_num
    linarith
  have hlogY : (1 : ℝ) ≤ Real.log Y := by
    have h1 : Real.log 16 ≤ Real.log Y := Real.log_le_log (by norm_num) h16le
    have h2 : Real.log (16 : ℝ) = 4 * Real.log 2 := by
      have := Real.log_pow (2 : ℝ) 4
      norm_num at this
      exact this
    have h3 : (1 : ℝ) ≤ 4 * Real.log 2 := by nlinarith [Real.log_two_gt_d9]
    linarith
  have hPcge2 : (2 : ℝ) ≤ Work.BMF.mrCore.Pc Y := by
    have hlogPc1 : (1 : ℝ) ≤ Work.BMF.mrCore.logPc Y := by
      rw [Work.BMF.mrCore.logPc]
      exact Real.one_le_rpow hlogY (by norm_num)
    have hlog2le : Real.log 2 ≤ Work.BMF.mrCore.logPc Y := by
      have h2le1 : Real.log 2 ≤ 1 := by
        have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
      linarith
    have h := Real.exp_le_exp.mpr hlog2le
    rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)] at h
    simpa [Work.BMF.mrCore.Pc] using h
  have hPleQ : Work.BMF.mrCore.Pc Y ≤ Work.BMF.mrCore.Qc B Y := by
    have hlogPc_nn : 0 ≤ Work.BMF.mrCore.logPc Y := by
      rw [Work.BMF.mrCore.logPc]
      exact Real.rpow_nonneg (by linarith) _
    have hAc1 : (1 : ℝ) ≤ Work.BMF.mrCore.Ac B := by
      rw [Work.BMF.mrCore.Ac]; exact Real.one_le_exp (by positivity)
    have hlogle : Real.log (Work.BMF.mrCore.Pc Y) ≤ Real.log (Work.BMF.mrCore.Qc B Y) := by
      rw [Work.BMF.mrCore.Pc, Work.BMF.mrCore.Qc, Real.log_exp, Real.log_exp,
        Work.BMF.mrCore.logQc]
      linarith [mul_le_mul_of_nonneg_right hAc1 hlogPc_nn]
    exact (Real.log_le_log_iff (Real.exp_pos _) (Real.exp_pos _)).mp hlogle
  -- the general-range remainder bound at the window scale
  have hmain := hrm (Real.sqrt (B ^ 2 / 2)) hB'1 g (Work.BMF.mrCore.Pc Y)
      (Work.BMF.mrCore.Qc B Y) (Y * Real.exp (-(j : ℝ) / K))
      (Y * Real.exp (-((j : ℝ) + 1) / K)) (3 * Y * Real.exp (-(j : ℝ) / K))
      T₀ t hg1 hgmul hgb hPcge2 hPleQ hX16 hX4 hX12 hX2 hT₀ hdistX hsieve' ht
  -- convert `log Q / log P` into `Ac B` and `B'` into `B`
  have hratio : Real.log (Work.BMF.mrCore.Qc B Y) / Real.log (Work.BMF.mrCore.Pc Y)
      = Work.BMF.mrCore.Ac B := bpcell_logratio hY8
  have hbracket : (1 + Real.sqrt (B ^ 2 / 2) ^ 2) * Real.exp (-(Real.sqrt (B ^ 2 / 2) ^ 2 / 4))
      = (1 + B ^ 2 / 2) * Real.exp (-(B ^ 2 / 8)) := by
    rw [hB'2]; ring_nf
  rw [hratio, hbracket] at hmain
  simpa only [Work.BMF.mrDirect.remPolyR] using hmain

end Work.BMF.mr_core
