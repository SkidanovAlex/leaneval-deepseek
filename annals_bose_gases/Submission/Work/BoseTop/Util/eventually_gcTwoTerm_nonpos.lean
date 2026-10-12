import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Submission.Work.BoseTop.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `gcTwoTerm` is eventually nonpositive near `ρ = 0⁺`

With `c := 128/(15√π)` and
`gcTwoTerm A Cw s ρ = 4πAρ²·(−1 + c·√(ρA³) − Cw·(ρA³)^s)`, the bracket
tends to `−1 < 0` as `ρ → 0⁺` (for `0 < A`, `0 ≤ Cw`, `0 < s`), while the
prefactor `4πAρ² > 0`.  Hence `gcTwoTerm A Cw s ρ < 0` for all sufficiently
small positive `ρ`.
-/

namespace Work.BoseTop.Util

open Filter Real
open scoped Topology

theorem eventually_gcTwoTerm_nonpos {A Cw s : ℝ} (hA : 0 < A) (hCw : 0 ≤ Cw) (hs : 0 < s) :
    Filter.Eventually (fun ρ : ℝ => Submission.BoseGases.gcTwoTerm A Cw s ρ ≤ 0)
      (nhdsWithin 0 (Set.Ioi 0)) := by
  -- `ρ·A³ → 0`, hence `√(ρA³) → 0` and `(ρA³)^s → 0` along `ρ → 0⁺`.
  have hbase : Filter.Tendsto (fun ρ : ℝ => ρ * A ^ 3) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have hid : Filter.Tendsto (fun ρ : ℝ => ρ) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
    have hc : Filter.Tendsto (fun _ : ℝ => A ^ 3) (nhdsWithin 0 (Set.Ioi 0)) (nhds (A ^ 3)) :=
      tendsto_const_nhds
    simpa using hid.mul hc
  have hsqrt : Filter.Tendsto (fun ρ : ℝ => Real.sqrt (ρ * A ^ 3))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa [Real.sqrt_zero] using hbase.sqrt
  have hrpow : Filter.Tendsto (fun ρ : ℝ => (ρ * A ^ 3) ^ s)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have h := hbase.rpow tendsto_const_nhds (Or.inr hs)
    simpa [Real.zero_rpow (ne_of_gt hs)] using h
  -- the bracket tends to `-1 + c·0 - Cw·0 = -1`
  have hlim : Filter.Tendsto
      (fun ρ : ℝ => -1 + (128 / (15 * Real.sqrt π)) * Real.sqrt (ρ * A ^ 3)
        - Cw * (ρ * A ^ 3) ^ s) (nhdsWithin 0 (Set.Ioi 0)) (nhds (-1)) := by
    have h1 : Filter.Tendsto (fun _ : ℝ => (-1 : ℝ)) (nhdsWithin 0 (Set.Ioi 0)) (nhds (-1)) :=
      tendsto_const_nhds
    have h2 : Filter.Tendsto (fun _ : ℝ => (128 / (15 * Real.sqrt π)))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (128 / (15 * Real.sqrt π))) := tendsto_const_nhds
    have h3 : Filter.Tendsto (fun _ : ℝ => Cw)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds Cw) := tendsto_const_nhds
    simpa using (h1.add (h2.mul hsqrt)).sub (h3.mul hrpow)
  have hneg : ∀ᶠ ρ in nhdsWithin 0 (Set.Ioi 0),
      -1 + (128 / (15 * Real.sqrt π)) * Real.sqrt (ρ * A ^ 3)
        - Cw * (ρ * A ^ 3) ^ s < 0 :=
    hlim.eventually (isOpen_Iio.mem_nhds (by norm_num : (-1 : ℝ) < 0))
  -- multiply the negative bracket by the positive prefactor `4πAρ²`
  filter_upwards [hneg, self_mem_nhdsWithin] with ρ hlt hρ
  have hρpos : 0 < ρ := hρ
  unfold Submission.BoseGases.gcTwoTerm
  exact le_of_lt (mul_neg_of_pos_of_neg (by positivity) hlt)

end Work.BoseTop.Util
