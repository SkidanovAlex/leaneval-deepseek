import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseFixB1.WB.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1.WB

open Submission.BoseGases

/-- **Global `L^∞` bound of the repointed two-factor cutoff**:

    χ_{B(u)}(x)² ≤ (chiSupAbs · chiSmallDecay M · (1/2)^M)² .

The `ℓ`-scale factor is the corpus bump, bounded by its absolute sup `chiSupAbs`
(`chiScale_abs_le_sup`); the `ℓd`-scale factor is the cosine-power bump
`χ_M((ℓd)⁻¹•x − u)`, whose coordinate face decay
`chiSmall_decay_coord` at the box *centre* gives the sharp factor
`(1/2)^M = ((1/2 − |0|)₊)^M`.  No hypothesis on `ℓ`, `d` is needed: both factors
admit their absolute bounds for arbitrary (possibly vanishing) scale. -/
theorem chiSmallB_sq_le {M : ℕ} (hM : 1 ≤ M) (ℓ d : ℝ) (u x : EuclideanSpace ℝ (Fin 3)) :
    (Submission.BoseGases.chiSmallB M ℓ d u x) ^ 2
      ≤ (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M
          * (1 / 2) ^ M) ^ 2 := by
  have hdec := chiSmall_decay_coord hM ((ℓ * d)⁻¹ • x - u) 0
  have hmax_le : max (1 / 2 - |(((ℓ * d)⁻¹ • x - u)).ofLp 0|) 0 ≤ 1 / 2 :=
    max_le (by linarith [abs_nonneg ((((ℓ * d)⁻¹ • x - u)).ofLp 0)]) (by norm_num)
  have hpow : (max (1 / 2 - |(((ℓ * d)⁻¹ • x - u)).ofLp 0|) 0) ^ M ≤ (1 / 2) ^ M :=
    pow_le_pow_left₀ (le_max_right _ _) hmax_le M
  have hdec' : |chiSmall M ((ℓ * d)⁻¹ • x - u)| ≤ chiSmallDecay M * (1 / 2) ^ M :=
    le_trans hdec (mul_le_mul_of_nonneg_left hpow (chiSmallDecay_nonneg M))
  have hscale := chiScale_abs_le_sup ℓ x
  have habs : |chiSmallB M ℓ d u x| ≤ chiSupAbs * chiSmallDecay M * (1 / 2) ^ M := by
    rw [chiSmallB, abs_mul]
    calc |chiScale ℓ x| * |chiSmall M ((ℓ * d)⁻¹ • x - u)|
        ≤ chiSupAbs * (chiSmallDecay M * (1 / 2) ^ M) :=
          mul_le_mul hscale hdec' (abs_nonneg _) chiSupAbs_nonneg
      _ = chiSupAbs * chiSmallDecay M * (1 / 2) ^ M := by ring
  rw [← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) habs 2

end Work.BoseFixB1.WB
