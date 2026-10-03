import Mathlib
import Submission.Work.Peluse.ladderA_defs

namespace Work.Peluse.LadderA

theorem L_ge_one {γ γ' M₁ M₂ Cbig : ℝ} {Kbig : ℕ} (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hγ' : 0 < γ') (hC : 2 ≤ Cbig) (hK : 1 ≤ Kbig)
    (hM₂ : 1 ≤ M₂) (hM₁ : M₂ ≤ M₁)
    (hi : Cbig * γ' ≤ γ ^ Kbig) (hii : Cbig ≤ M₂ * (γ * γ') ^ Kbig) :
    1 ≤ γ' * M₁ * M₂ := by
  have hγnn : 0 ≤ γ := le_of_lt hγ
  have hγ'nn : 0 ≤ γ' := le_of_lt hγ'
  -- `γ ^ Kbig ≤ 1` since `0 < γ ≤ 1`.
  have hgpow : γ ^ Kbig ≤ 1 := pow_le_one₀ hγnn hγ1
  -- `Cbig * γ' ≤ 1`, hence `γ' ≤ 1/Cbig ≤ 1`.
  have hCg' : Cbig * γ' ≤ 1 := le_trans hi hgpow
  have hγ'1 : γ' ≤ 1 := by nlinarith [hCg', hC, hγ'nn]
  -- `γ * γ' ∈ (0, 1]`, so `(γ * γ') ^ Kbig ≤ γ * γ'` for `Kbig ≥ 1`.
  have hbase0 : 0 ≤ γ * γ' := mul_nonneg hγnn hγ'nn
  have hbase1 : γ * γ' ≤ 1 := by
    have := mul_le_mul hγ1 hγ'1 hγ'nn (by norm_num : (0:ℝ) ≤ 1)
    simpa using this
  have hpow : (γ * γ') ^ Kbig ≤ γ * γ' := by
    have := pow_le_pow_of_le_one hbase0 hbase1 hK
    simpa using this
  have hM₂nn : 0 ≤ M₂ := le_trans (by norm_num) hM₂
  -- `M₂ * (γ * γ') ^ Kbig ≤ M₂ * γ'`, and `γ * γ' ≤ γ'`.
  have hstep1 : M₂ * (γ * γ') ^ Kbig ≤ M₂ * (γ * γ') :=
    mul_le_mul_of_nonneg_left hpow hM₂nn
  have hgg' : γ * γ' ≤ γ' := mul_le_of_le_one_left hγ'nn hγ1
  have hstep2 : M₂ * (γ * γ') ≤ M₂ * γ' := mul_le_mul_of_nonneg_left hgg' hM₂nn
  -- Hence `Cbig ≤ M₂ * γ'`, i.e. `γ' * M₂ ≥ 2`.
  have hkey : 2 ≤ γ' * M₂ := by
    have h1 : (2:ℝ) ≤ M₂ * γ' := le_trans (le_trans hC hii) (le_trans hstep1 hstep2)
    nlinarith [h1]
  -- `γ' * M₁ * M₂ ≥ 2 * M₂ ≥ 2 ≥ 1` since `M₂ ≥ 1` and `M₁ ≥ M₂`.
  have hfinal : (2:ℝ) * M₂ ≤ (γ' * M₂) * M₁ :=
    mul_le_mul hkey hM₁ hM₂nn (by nlinarith [hkey])
  nlinarith [hfinal, hM₂]

end Work.Peluse.LadderA
