import Mathlib
import Submission.Work.BMF.ztw_defs
import Submission.Work.BMF.VKStripDefs
import Submission.Work.BMF.N7.vk_interface
import Submission.Work.BMF.LFunction_strip_VK
import Submission.Work.BMF.zpt.zeroFree_VK_copy
import Submission.Work.BMF.zeroFree_bounded_height_chi
import Submission.Work.BMF.N7.logDeriv_LFunction_VK_of_growth_zf
import Submission.Work.BMF.zpt.vkgrowth_of_vkExpInput
import Submission.Work.BMF.vk_exp_sum

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

open scoped Real Topology

noncomputable section

/-! ## Assembling the `6/7`-shaped Vinogradov–Korobov data for `ζ`

The heavy inputs are the sibling nodes of the `V`-chain, all `sorry`-free in this workspace:
`Work.BMF.vk_exp_sum` (V1) and
`Work.BMF.zpt.vkgrowth_of_vkExpInput` (V2: `VKGrowth` from V1) supply the strip growth bound for
Dirichlet `L`-functions, `Work.BMF.LFunction_strip_VK` turns it into the strip
logarithmic-derivative bounds `VKStrip (c/4) E`, the `3-4-1` argument
`Work.BMF.zeroFree_of_VKStrip` plus the bounded-height region
`Work.BMF.zeroFree_bounded_height_chi` give the zero-free region `Work.BMF.ZFVKN7`, and
`Work.BMF.N7.logDeriv_LFunction_VK_of_growth_zf` then gives, at the trivial character mod `1`,
both the non-vanishing and the logarithmic-derivative bound in exactly the `6/7`-shape used
below. -/

/-- Monotonicity of `Work.BMF.VKGrowth`: enlarge `A` to `max A 1`, shrink `c` to `min c 1`. -/
private lemma VKGrowth_mono_zpt {A c : ℝ} (h : VKGrowth A c) : VKGrowth (max A 1) (min c 1) := by
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

/-- **The `6/7`-shaped Vinogradov–Korobov zero-free region from the growth bound.** -/
private lemma zf_VK_of_growth_zpt (A c : ℝ) (hgr : VKGrowth A c) : ZFVKN7 := by
  have hgr' : VKGrowth (max A 1) (min c 1) := VKGrowth_mono_zpt hgr
  obtain ⟨hA, hc, _⟩ := hgr
  obtain ⟨E, hE, hstrip⟩ := LFunction_strip_VK (max A 1) (min c 1) hgr'
  have hc4 : (0 : ℝ) < min c 1 / 4 := by
    have : (0 : ℝ) < min c 1 := lt_min hc one_pos
    linarith
  have hc41 : min c 1 / 4 ≤ 1 := by
    have : min c 1 ≤ 1 := min_le_right _ _
    linarith
  obtain ⟨c₁, hc₁, hzf₁⟩ := zeroFree_of_VKStrip ((min c 1) / 4) E hc4 hc41 hE hstrip
  obtain ⟨c₂, hc₂, hzf₂⟩ := zeroFree_bounded_height_chi
  refine ⟨min c₁ c₂, lt_min hc₁ hc₂, ?_⟩
  intro N hN χ hprim σ t ht hσ
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

/-- **The `6/7`-shaped Vinogradov–Korobov data for `ζ`**: zero-free region and
logarithmic-derivative bound at heights `≥ 4`, with `ztD h = (log (h+3))^{6/7}(log 3 + log log (h+3))`.

Route (all inputs are `sorry`-free in this workspace): `Work.BMF.vk_exp_sum` supplies the
Vinogradov–Korobov exponential-sum input `VKExpInput`; `Work.BMF.VKGrowth` turns it into the
Hurwitz-zeta growth bound and (`LFunction_growth_of_hurwitz`) into `VKGrowth A c` for Dirichlet
`L`-functions, hence for `ζ = L(·, 1)` (trivial character mod `1`); `Work.BMF.LFunction_strip_VK`
converts `VKGrowth A c` into the strip logarithmic-derivative bounds `VKStrip (c/4) E`; the
`3-4-1` zero detection argument `Work.BMF.zeroFree_of_VKStrip` (in
`Submission/Work/BMF/LFunction_zeroFree_VK.lean`, conditional on `VKStrip`, its module being
transiently blocked by a broken sibling import) gives the zero-free region, and the regular form
of `VKStrip` gives the logarithmic-derivative bound in it. Heights `4 ≤ |t| ≤ 10` are covered by
the bounded-height non-vanishing (`Work.BMF.zeroFree_bounded_height_chi`,
`Work.BMF.zeta_zeroFree_compact`).

Shortcut (reviewer 2): `Work.BMF.zeta_vk_region_of_growth` (0 sorries in file) already produces
`∃ c₁ > 0, ζ(σ+it) ≠ 0` for `1 - c₁/VKd(|t|+3) ≤ σ` (heights `≥ 3`) together with
`‖ζ'/ζ(σ+it)‖ ≤ B (log(|t|+3))^2`; since `VKd(|t|+3) ≤ ztD |t|` for `|t| ≥ 4` with a uniform
*positive* bound on the ratio over `|t| ≥ 4` (it is `≥ 2` for `|t|+3 ≥ 7`), a smaller constant `c`
gives exactly the `6/7`-shaped statement above, and `(log)^2 ≤ (log)^4` on `|t| ≥ 4`. -/
theorem zpt_zeta_data :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      (∀ t σ : ℝ, 4 ≤ |t| → 1 - c / Work.BMF.ztD |t| ≤ σ → σ ≤ 2 →
        riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0) ∧
      (∀ t σ : ℝ, 4 ≤ |t| → 1 - c / Work.BMF.ztD |t| ≤ σ → σ ≤ 2 →
        ‖deriv riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) /
          riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
          C * (Real.log (|t| + 3)) ^ 4) := by
  -- V2 from V1, then V3, then V4 at the trivial character mod `1`.
  obtain ⟨A, clg, hgr⟩ := zpt.vkgrowth_of_vkExpInput Work.BMF.vk_exp_sum
  have hzf : ZFVKN7 := zf_VK_of_growth_zpt A clg hgr
  obtain ⟨CV, κV, hCV, hκV, hLVK⟩ := N7.logDeriv_LFunction_VK_of_growth_zf hgr hzf
  refine ⟨κV, CV, hκV, hCV, ?_, ?_⟩
  · intro t σ ht hσ hσ2
    have hden : Work.BMF.ztD |t| = (Real.log (|t| + 3)) ^ (6 / 7 : ℝ) *
        (Real.log ((1 : ℕ) + 2) + Real.log (Real.log (|t| + 3))) := by
      rw [ztD]; norm_num
    have hσ' : 1 - κV / ((Real.log (|t| + 3)) ^ (6 / 7 : ℝ) *
        (Real.log ((1 : ℕ) + 2) + Real.log (Real.log (|t| + 3)))) ≤ σ := by
      rw [← hden]; exact hσ
    have h := (hLVK 1 (1 : DirichletCharacter ℂ 1)
      DirichletCharacter.isPrimitive_one_level_one σ t ht hσ' hσ2).1
    rwa [DirichletCharacter.LFunction_modOne_eq] at h
  · intro t σ ht hσ hσ2
    have hden : Work.BMF.ztD |t| = (Real.log (|t| + 3)) ^ (6 / 7 : ℝ) *
        (Real.log ((1 : ℕ) + 2) + Real.log (Real.log (|t| + 3))) := by
      rw [ztD]; norm_num
    have hσ' : 1 - κV / ((Real.log (|t| + 3)) ^ (6 / 7 : ℝ) *
        (Real.log ((1 : ℕ) + 2) + Real.log (Real.log (|t| + 3)))) ≤ σ := by
      rw [← hden]; exact hσ
    have h := (hLVK 1 (1 : DirichletCharacter ℂ 1)
      DirichletCharacter.isPrimitive_one_level_one σ t ht hσ' hσ2).2
    rw [DirichletCharacter.LFunction_modOne_eq, logDeriv_apply] at h
    simpa using h

end

end Work.BMF
