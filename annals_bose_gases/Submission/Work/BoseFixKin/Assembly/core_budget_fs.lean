import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixKin.Assembly.region_far_far
import Submission.Work.BoseFixKin.Assembly.region_mixed
import Submission.Work.BoseFixKin.Assembly.region_near_near
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixKin.Assembly.core_budget_fs` — the scalar three-region budget (node N1)

The momentum-space budget of the coupled (`b`-clash) kinetic regime, in the box momentum
`q = ℓ‖p‖` at `β = 1/2`:

```
A εT q²/(1+d²q²) + 2b q²/(q²+1/2) + (1-εT) tprR (2s) C q + εT tprR (2ds) C q ≤ q²,
A = (1+K)/2,
```

for `0 < d ≤ 1`, `0 < s ≤ cFS K C`, `0 ≤ εT ≤ cFS K C`, `εT s ≤ cFS K C d`, `0 ≤ b ≤ 1/16`.

## Decomposition

`tprR σ C q = if (5/6)σ⁻¹ ≤ q then (q − (2σ)⁻¹)² else C σ³ q²`
(`Work.BoseKinLoc.Assembly`).  Since `d ≤ 1` the switch `5/(12s)` of the `2s` cut-off lies
below the switch `5/(12ds)` of the `2ds` cut-off, so there are exactly three regions, and
each one is an elementary real-arithmetic statement proved in its own module:

| region | `q` | proved in |
|---|---|---|
| I (both branches near) | `q < 5/(12s)` | `Work.BoseFixKin.Assembly.region_near_near` |
| II (mixed) | `5/(12s) ≤ q < 5/(12ds)` | `Work.BoseFixKin.Assembly.region_mixed` |
| III (both branches far) | `5/(12ds) ≤ q` | `Work.BoseFixKin.Assembly.region_far_far` |

Each of those three lemmas states the *same* sum ≤ q² with the *same* hypotheses, restricted
to one region (expressed as the two branch conditions of `tprR` at `σ = 2s` and `σ = 2ds`);
the present file supplies the case split and the threshold ordering — including the fact that
region I is contained in region II of the `2ds` cut-off, which is where `d ≤ 1` enters.

An independent, self-contained re-proof of the same statement (not using the three region
modules) is `Submission/Work/BoseFixKin/Assembly/core_budget_fs_selfcontained.lean`.

Templates: `Work.BoseKinLoc.Assembly.budget_near_near`, `budget_mixed`, `far_far_core`.
-/

noncomputable section

namespace Work.BoseFixKin.Assembly

open Work.BoseFixKin

/-- **The scalar three-region budget of the coupled regime** (`BOSE_BCLASH_LEAD.md` §3, node N1).

Plan: split on the two `tprR` thresholds `q = 5/(12 s)` (from `σ = 2s`) and `q = 5/(12 d s)`
(from `σ = 2 d s`).  Region I (`q < 5/(12s)`): both `tprR` on the near branch, giving
`T3 + T4 ≤ 8 C s³ q²`, and `T2 ≤ 4 b q²`; Region II (`5/(12s) ≤ q < 5/(12ds)`): first `tprR` far,
`q² − T3 ≥ ε_T q² + (1−ε_T)(7/20)(q/s)`, `T4 = 8 C ε_T d³s³q² ≤ ε_T q²`, `T1 ≤ A ε_T q/(2d)`
(AM–GM), which uses the coupling `ε_T ≤ cFS · d/s`; Region III (`q ≥ 5/(12ds)`): both far, and
`q² − T3 − T4 ≥ (1−ε_T)(7/20)(q/s) + ε_T (7/20)(q/(ds))`.  Templates:
`Submission/Work/BoseKinLoc/Assembly/two_regime_core.lean`, `far_far_core.lean`,
`budget_mixed.lean`.

Useful derived facts from `s ≤ cFS K C` and `ε_T ≤ cFS K C`: `A ε_T ≤ 1/128` (`A := (1+K)/2`),
`(K+1) s²/2 ≤ 7/48`, `8 C s³ ≤ 7/8`, `1 − ε_T ≥ 3/4`, `s ≤ 1/4`. -/
theorem core_budget_fs {K C q d s εT b : ℝ} (hK : 0 ≤ K) (hC : 0 < C)
    (hq : 0 ≤ q) (hd : 0 < d) (hd1 : d ≤ 1) (hs : 0 < s) (hsc : s ≤ cFS K C)
    (hε : 0 ≤ εT) (hεc : εT ≤ cFS K C)
    (hcpl : εT * s ≤ cFS K C * d)
    (hb : 0 ≤ b) (hb16 : b ≤ 1 / 16) :
    (1 + K) / 2 * εT * q ^ 2 / (1 + d ^ 2 * q ^ 2)
        + b * (1 / 2 : ℝ)⁻¹ * (q ^ 2 / (q ^ 2 + 1 / 2))
        + (1 - εT) * Work.BoseKinLoc.Assembly.tprR (2 * s) C q
        + εT * Work.BoseKinLoc.Assembly.tprR (2 * (d * s)) C q
      ≤ q ^ 2 := by
  by_cases h1 : (5 / 6) * (2 * s)⁻¹ ≤ q
  · by_cases h2 : (5 / 6) * (2 * (d * s))⁻¹ ≤ q
    · -- region III: both branches far
      exact region_far_far hK hC hq hd hd1 hs hsc hε hεc hcpl hb hb16 h1 h2
    · -- region II: first branch far, second near
      exact region_mixed hK hC hq hd hd1 hs hsc hε hεc hcpl hb hb16 h1 h2
  · -- region I: both branches near.  `d ≤ 1` puts the second switch to the right of the
    -- first one, so the negation of the first branch condition implies the second one.
    have h2 : ¬ ((5 / 6) * (2 * (d * s))⁻¹ ≤ q) := by
      intro hc
      apply h1
      have hds : (2 * s)⁻¹ ≤ (2 * (d * s))⁻¹ := by
        rw [inv_le_inv₀ (by positivity) (by positivity)]
        nlinarith [hd1, hs]
      exact le_trans (mul_le_mul_of_nonneg_left hds (by norm_num)) hc
    exact region_near_near hK hC hq hd hd1 hs hsc hε hεc hcpl hb hb16 h1 h2

end Work.BoseFixKin.Assembly
