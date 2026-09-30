import Mathlib
import Submission.Work.BMF.vkford51_defs
import Submission.Work.BMF.TentDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Ford kernel dominates `1` on `1 ≤ c ≤ K`

`kern K c = (π² K / 2) · tentCoeff (1/(2K)) c`; a direct computation gives

  `kern K c = (K / c)² · sin (π c / (2K))²`  for `c ≠ 0`,

and the classical inequality `sin (π t / 2) ≥ t` on `[0,1]` (Jordan's inequality, Mathlib's
`Real.le_sin_mul`) yields `sin (π c / (2K)) ≥ c / K` for `1 ≤ c ≤ K`, whence
`kern K c ≥ ((K/c)·(c/K))² = 1`.
-/

namespace Work.BMF

theorem one_le_kern (K : ℕ) (hK : 1 ≤ K) {c : ℕ} (hc1 : 1 ≤ c) (hc2 : c ≤ K) :
    1 ≤ kern K (c : ℤ) := by
  have hKpos : (0:ℝ) < (K:ℝ) := by exact_mod_cast hK
  have hcpos : (0:ℝ) < (c:ℝ) := by exact_mod_cast hc1
  have hcle : (c:ℝ) ≤ (K:ℝ) := by exact_mod_cast hc2
  have hcZ : (c:ℤ) ≠ 0 := by omega
  -- Jordan's inequality at `t = c/K ∈ (0,1]`.
  have hs : (c:ℝ)/(K:ℝ) ≤ Real.sin (Real.pi / 2 * ((c:ℝ)/(K:ℝ))) :=
    Real.le_sin_mul (div_nonneg hcpos.le hKpos.le) ((div_le_one hKpos).mpr hcle)
  have hKc_nonneg : (0:ℝ) ≤ (K:ℝ)/(c:ℝ) := div_nonneg hKpos.le hcpos.le
  have hone : (1:ℝ) ≤ ((K:ℝ)/(c:ℝ)) * Real.sin (Real.pi / 2 * ((c:ℝ)/(K:ℝ))) := by
    have h1 : ((K:ℝ)/(c:ℝ)) * ((c:ℝ)/(K:ℝ)) = 1 := by field_simp
    calc (1:ℝ) = ((K:ℝ)/(c:ℝ)) * ((c:ℝ)/(K:ℝ)) := h1.symm
      _ ≤ ((K:ℝ)/(c:ℝ)) * Real.sin (Real.pi / 2 * ((c:ℝ)/(K:ℝ))) :=
          mul_le_mul_of_nonneg_left hs hKc_nonneg
  -- the closed form of `kern` at a nonzero frequency
  have hkern : kern K (c:ℤ) = ((K:ℝ)/(c:ℝ))^2 * Real.sin (Real.pi/2 * ((c:ℝ)/(K:ℝ)))^2 := by
    unfold kern tentCoeff
    rw [if_neg hcZ]
    push_cast
    field_simp
  rw [hkern]
  calc (1:ℝ) ≤ (((K:ℝ)/(c:ℝ)) * Real.sin (Real.pi / 2 * ((c:ℝ)/(K:ℝ))))^2 := by
        simpa using pow_le_pow_left₀ (zero_le_one' ℝ) hone 2
    _ = ((K:ℝ)/(c:ℝ))^2 * Real.sin (Real.pi/2 * ((c:ℝ)/(K:ℝ)))^2 := by ring

end Work.BMF
