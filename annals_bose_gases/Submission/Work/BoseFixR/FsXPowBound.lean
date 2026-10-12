import ChallengeDeps
import Submission.Work.BoseFixR.RB5FSDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixR

open _root_.BoseGases

/-- Numeric core of `FsXPowBound`, stated for a bare real `t`:
`t ^ (17/152) ≤ 10^{-400}` as soon as `0 < t ≤ 10^{-4000}`.

(The exponent comes from `(1/323) · (289/8) = 17/152`, and
`10^{-4000 · 17/152} = 10^{-8500/19} ≤ 10^{-400}` because `8500/19 > 400`.) -/
lemma rpow_17_152_le {t : ℝ} (ht0 : 0 < t) (ht : t ≤ (10 : ℝ) ^ (-(4000 : ℤ))) :
    t ^ ((17 : ℝ) / 152) ≤ (10 : ℝ) ^ (-(400 : ℤ)) := by
  have hmono : t ^ ((17 : ℝ) / 152) ≤ ((10 : ℝ) ^ (-(4000 : ℤ))) ^ ((17 : ℝ) / 152) :=
    Real.rpow_le_rpow ht0.le ht (by norm_num)
  refine le_trans hmono ?_
  have hc4000 : (10 : ℝ) ^ (-(4000 : ℤ)) = (10 : ℝ) ^ ((-(4000 : ℤ) : ℤ) : ℝ) :=
    (Real.rpow_intCast 10 (-4000)).symm
  have hc400 : (10 : ℝ) ^ (-(400 : ℤ)) = (10 : ℝ) ^ ((-(400 : ℤ) : ℤ) : ℝ) :=
    (Real.rpow_intCast 10 (-400)).symm
  rw [hc4000, hc400,
    ← Real.rpow_mul (show (0 : ℝ) ≤ 10 by norm_num)
      ((-(4000 : ℤ) : ℤ) : ℝ) ((17 : ℝ) / 152)]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
    (by norm_num : ((-(4000 : ℤ) : ℤ) : ℝ) * ((17 : ℝ) / 152) ≤ ((-(400 : ℤ) : ℤ) : ℝ))

theorem FsXPowBound {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ : ℝ}
    (hav : 0 < BoseGases.a v) (hμ : 0 < μ)
    (ht : Work.BoseFixR.dil v μ ≤ (10 : ℝ) ^ (-(4000 : ℤ))) :
    (Work.BoseFixR.fsX v μ) ^ (289 / 8 : ℝ) ≤ (10 : ℝ) ^ (-(400 : ℤ)) := by
  have ht0 : 0 < dil v μ := by rw [dil]; positivity
  have hpow : (fsX v μ) ^ (289 / 8 : ℝ) = (dil v μ) ^ ((17 : ℝ) / 152) := by
    rw [fsX, Work.BoseBox.fsXp,
      ← Real.rpow_mul (le_of_lt ht0) ((1 : ℝ) / 323) ((289 : ℝ) / 8)]
    rw [show ((1 : ℝ) / 323) * ((289 : ℝ) / 8) = (17 : ℝ) / 152 by norm_num]
  rw [hpow]
  exact rpow_17_152_le ht0 ht

end Work.BoseFixR
