import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.BoseBox.Windows
import Submission.Work.BoseBox.paramsOK_fsParams
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBox.paramsAtSmall`

The parameters `paramsAt μ a = fsParams (μa³)` are admissible, with all the
dimensionless small parameters bounded by `1/16` and strictly positive, for the
diluteness `μa³` sufficiently small — which, for fixed `a > 0`, is eventual as
`μ → 0⁺`.

The content is bookkeeping on `fsXp t c = t^{c/323}`:

* `eventually_fsXp_le` — `X^c = t^{c/323} → 0⁺` as `t → 0⁺` (`c > 0`), so it is
  eventually below any positive bound;
* `paramsOK_fsParams` (imported) supplies the whole `ParamsOK` bundle once
  `t = μa³` is small;
* `t ↦ μa³` maps `nhdsWithin 0 (Ioi 0)` into itself because `a³ > 0`.
-/

noncomputable section

open scoped Real Topology BigOperators

namespace Work.BoseBox

/-- `X^c = t^{c/323} → 0⁺` as `t → 0⁺`: for every `r > 0` and `c > 0`,
`fsXp t c ≤ r` eventually. Just take `t ≤ r^{323/c}`. -/
lemma eventually_fsXp_le {c r : ℝ} (hc : 0 < c) (hr : 0 < r) :
    ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), fsXp t c ≤ r := by
  have hc0 : (0 : ℝ) < c / 323 := by positivity
  have hT : (0 : ℝ) < r ^ (323 / c) := Real.rpow_pos_of_pos hr _
  have hmul : 323 / c * (c / 323) = 1 := by
    field_simp
  filter_upwards [Ioo_mem_nhdsGT hT] with t ht
  have ht0 : (0 : ℝ) < t := ht.1
  have htT : t ≤ r ^ (323 / c) := le_of_lt ht.2
  calc fsXp t c = t ^ (c / 323) := rfl
    _ ≤ (r ^ (323 / c)) ^ (c / 323) := Real.rpow_le_rpow ht0.le htT hc0.le
    _ = r ^ (323 / c * (c / 323)) := (Real.rpow_mul hr.le (323 / c) (c / 323)).symm
    _ = r := by rw [hmul, Real.rpow_one]

theorem paramsAtSmall {a : ℝ} (ha : 0 < a) :
    ∀ᶠ μ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      Work.BoseBox.ParamsOK (Work.BoseBox.paramsAt μ a) (μ * a ^ 3)
      ∧ (Work.BoseBox.paramsAt μ a).d ≤ 1 / 16
      ∧ (Work.BoseBox.paramsAt μ a).s ≤ 1 / 16
      ∧ (Work.BoseBox.paramsAt μ a).eT ≤ 1 / 16
      ∧ 0 < (Work.BoseBox.paramsAt μ a).d
      ∧ 0 < (Work.BoseBox.paramsAt μ a).s
      ∧ 0 < (Work.BoseBox.paramsAt μ a).eT
      ∧ 0 < (Work.BoseBox.paramsAt μ a).b
      ∧ (Work.BoseBox.paramsAt μ a).b = 1 / 16 := by
  have ha3 : (0 : ℝ) < a ^ 3 := by positivity
  -- the diluteness map `μ ↦ μa³` sends `0⁺` to `0⁺`
  have hg_nhds : Filter.Tendsto (fun μ : ℝ => μ * a ^ 3) (nhds (0 : ℝ)) (nhds (0 * a ^ 3)) :=
    Filter.tendsto_id.mul tendsto_const_nhds
  have hg : Filter.Tendsto (fun μ : ℝ => μ * a ^ 3) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · simpa using hg_nhds.mono_left
        (nhdsWithin_le_nhds : nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤ nhds (0 : ℝ))
    · filter_upwards [self_mem_nhdsWithin] with μ hμ
      exact mul_pos hμ ha3
  have hs1 : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), (fsParams t).s ≤ 1 / 16 :=
    eventually_fsXp_le (c := 1) (by norm_num) (by norm_num)
  have hd1 : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), (fsParams t).d ≤ 1 / 16 :=
    eventually_fsXp_le (c := 6) (by norm_num) (by norm_num)
  have he1 : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), (fsParams t).eT ≤ 1 / 16 :=
    eventually_fsXp_le (c := 23 / 4) (by norm_num) (by norm_num)
  have hQ : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ParamsOK (fsParams t) t
      ∧ (fsParams t).d ≤ 1 / 16 ∧ (fsParams t).s ≤ 1 / 16 ∧ (fsParams t).eT ≤ 1 / 16
      ∧ 0 < (fsParams t).d ∧ 0 < (fsParams t).s ∧ 0 < (fsParams t).eT
      ∧ 0 < (fsParams t).b ∧ (fsParams t).b = 1 / 16 := by
    filter_upwards [paramsOK_fsParams, hd1, hs1, he1, self_mem_nhdsWithin] with
      t hOK hd hs he ht
    refine ⟨hOK, hd, hs, he, ?_, ?_, ?_, ?_, ?_⟩
    · exact fsXp_pos ht
    · exact fsXp_pos ht
    · exact fsXp_pos ht
    · norm_num [fsParams, bValue]
    · norm_num [fsParams, bValue]
  filter_upwards [hg.eventually hQ] with μ hμ
  simpa [paramsAt] using hμ

end Work.BoseBox
