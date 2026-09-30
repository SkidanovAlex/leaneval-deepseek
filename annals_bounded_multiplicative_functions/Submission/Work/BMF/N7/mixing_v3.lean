import Mathlib
import Submission.Work.BMF.N7.vk_interface
import Submission.Work.BMF.VKStripDefs
import Submission.Work.BMF.v7chi_VKGrowth
import Submission.Work.BMF.L_growth_VK
import Submission.Work.BMF.LFunction_strip_VK
import Submission.Work.BMF.VKPrimeSums.zeroFree_LVK
import Submission.Work.BMF.zeroFree_bounded_height_chi

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! ## Node V3 (`ZFVKN7`) from V2 and the two proved leaves of the fleet's V3

`Submission/Work/BMF/LFunction_zeroFree_VK.lean` (H743) proves everything except the final
instantiation: its public `zeroFree_of_VKStrip` turns a `VKStrip` bound into a zero-free region for
`|t| ≥ 10`, and `Work.BMF.zeroFree_bounded_height_chi` (H743-L833, sorry-free) supplies
`3 ≤ |t| ≤ 10`.  `Work.BMF.LFunction_strip_VK` (H743-L804, sorry-free) turns `VKGrowth A c` into
`VKStrip (c/4) E`.  The only missing input is V2, which is supplied here as the conditional
`Work.BMF.N7.L_growth_VK_of_V1`.  Hence this file completes V3 (modulo V1) without copying the
526-line file, and gives exactly the hypothesis `Work.BMF.ZFVKN7` used by V4. -/

namespace Work.BMF.N7

open Complex

/-- Monotonicity of the growth predicate: enlarge `A` to `max A 1` and shrink `c` to `min c 1`. -/
lemma VKGrowth_mono {A c : ℝ} (h : VKGrowth A c) : VKGrowth (max A 1) (min c 1) := by
  obtain ⟨hA, hc, hgrV⟩ := h
  refine ⟨lt_of_lt_of_le one_pos (le_max_right _ _), lt_min hc one_pos, ?_⟩
  intro N hN χ σ t ht hσ hσ2
  have hlogpos : 0 < Real.log (|t| + 3) := Real.log_pos (by have := abs_nonneg t; linarith)
  have hlogp : 0 < Real.log (|t| + 3) ^ (-(6 / 7 : ℝ)) := Real.rpow_pos_of_pos hlogpos _
  have hle : min c 1 ≤ c := min_le_left _ _
  have hσ' : 1 - c * Real.log (|t| + 3) ^ (-(6 / 7 : ℝ)) ≤ σ := by
    nlinarith [hσ, hle, hlogp]
  have hbound := hgrV N χ σ t ht hσ' hσ2
  have h1 : A * (N : ℝ) ≤ max A 1 * (N : ℝ) :=
    mul_le_mul_of_nonneg_right (le_max_left A 1) (by positivity)
  have h2 : A * (N : ℝ) * Real.log (|t| + 3) ^ (6 / 7 : ℝ) ≤
      max A 1 * (N : ℝ) * Real.log (|t| + 3) ^ (6 / 7 : ℝ) :=
    mul_le_mul_of_nonneg_right h1 (by positivity)
  linarith [hbound, h2]

/-- **V3 from a growth bound**: the Vinogradov–Korobov shaped zero-free region for primitive
characters mod `N`, `|t| ≥ 3` — the type `Work.BMF.ZFVKN7`, i.e. exactly the conclusion of
`Work.BMF.LFunction_zeroFree_VK`. -/
theorem zf_of_growth {A c : ℝ} (hgr : VKGrowth A c) : Work.BMF.ZFVKN7 := by
  have hgr' : VKGrowth (max A 1) (min c 1) := VKGrowth_mono hgr
  obtain ⟨E, hE, hstrip⟩ := LFunction_strip_VK (max A 1) (min c 1) hgr'
  have hcpos : 0 < c := hgr.2.1
  have hc4 : (0 : ℝ) < min c 1 / 4 := by
    have h : (0 : ℝ) < min c 1 := lt_min hcpos one_pos
    linarith
  have hc41 : min c 1 / 4 ≤ 1 := by
    have h : min c 1 ≤ 1 := min_le_right _ _
    linarith
  obtain ⟨c₁, hc₁, hzf₁⟩ := zeroFree_of_VKStrip ((min c 1) / 4) E hc4 hc41 hE hstrip
  obtain ⟨c₂, hc₂, hzf₂⟩ := zeroFree_bounded_height_chi
  refine ⟨min c₁ c₂, lt_min hc₁ hc₂, ?_⟩
  intro N hN χ hprim σ t ht hσ
  haveI : NeZero N := hN
  have hlogTpos : 0 < Real.log (|t| + 3) := Real.log_pos (by have := abs_nonneg t; linarith)
  have hlogT1 : 1 ≤ Real.log (|t| + 3) := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1)
      (by have := abs_nonneg t; linarith [Real.exp_one_lt_three])
  have hloglog0 : 0 ≤ Real.log (Real.log (|t| + 3)) := Real.log_nonneg hlogT1
  have hN2 : 1 ≤ Real.log ((N : ℝ) + 2) := by
    rw [← Real.log_exp 1]
    apply Real.log_le_log (Real.exp_pos 1)
    have h2 : (1 : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
    linarith [Real.exp_one_lt_three]
  have hQpos : 0 < Real.log (|t| + 3) ^ (6 / 7 : ℝ) *
      (Real.log ((N : ℝ) + 2) + Real.log (Real.log (|t| + 3))) := by positivity
  by_cases hle : |t| ≤ 10
  · refine hzf₂ N χ hprim σ t ht hle ?_
    have hm : min c₁ c₂ ≤ c₂ := min_le_right _ _
    have h3 : c₂ / (Real.log (|t| + 3) ^ (6 / 7 : ℝ) *
        (Real.log ((N : ℝ) + 2) + Real.log (Real.log (|t| + 3)))) ≥
        min c₁ c₂ / (Real.log (|t| + 3) ^ (6 / 7 : ℝ) *
        (Real.log ((N : ℝ) + 2) + Real.log (Real.log (|t| + 3)))) :=
      div_le_div_of_nonneg_right hm hQpos.le
    linarith [hσ, h3]
  · push_neg at hle
    refine hzf₁ N χ hprim σ t (by linarith) ?_
    have hm : min c₁ c₂ ≤ c₁ := min_le_left _ _
    have h3 : c₁ / (Real.log (|t| + 3) ^ (6 / 7 : ℝ) *
        (Real.log ((N : ℝ) + 2) + Real.log (Real.log (|t| + 3)))) ≥
        min c₁ c₂ / (Real.log (|t| + 3) ^ (6 / 7 : ℝ) *
        (Real.log ((N : ℝ) + 2) + Real.log (Real.log (|t| + 3)))) :=
      div_le_div_of_nonneg_right hm hQpos.le
    linarith [hσ, h3]

/-- **V3 from the fleet's public V2** (`Work.BMF.v7chi_VKGrowth`), through the assembled
`Work.BMF.VKPrimeSums.zeroFree_LVK.LFunction_zeroFree_VK_of_growth` (which is sorry-free and
avoids the currently non-building `Work.BMF.LFunction_zeroFree_VK`). -/
theorem zf_VK_N7_fleet : Work.BMF.ZFVKN7 :=
  show Work.BMF.ZFVKN7 from
    Work.BMF.LFunction_zeroFree_VK_of_growth v7chi_VKGrowth

end Work.BMF.N7
