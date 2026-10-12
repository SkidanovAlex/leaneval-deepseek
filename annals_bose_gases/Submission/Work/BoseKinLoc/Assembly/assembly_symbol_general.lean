import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Submission.Work.BoseKinLoc.Assembly.budget_far_far
import Submission.Work.BoseKinLoc.Assembly.budget_mixed
import Submission.Work.BoseKinLoc.Assembly.budget_near_near
import Submission.Work.BoseKinLoc.Assembly.exists_small_czero
import Submission.Work.BoseKinLoc.Assembly.slack_conditions
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseKinLoc.Assembly.assembly_symbol_general`

`AssemblySymbol β C` (`Submission/Work/BoseKinLoc/Residuals.lean`, BS `lm:Tu`) is the
pointwise momentum-space budget of the localised kinetic word `𝒯_u`:

```
εT (dℓ)⁻² raSym ℓ d p + b β⁻¹ ‖p‖²/(ℓ²‖p‖²+β)
  + (1-εT) tprSym ℓ (2s) C p + εT tprSym ℓ (2ds) C p  ≤  ‖p‖²      (∀ ℓ d s εT b, ∀p)
```

over the regime `KinRegime c₀ ℓ d s εT b` (FS `eq:BSlidingassp`: `ℓ > 0` free and
`0 < d,s,εT,b ≤ c₀` for a universal constant `c₀`).

`Assembly/assembly_two_regime.lean` proves this budget for the *fixed* constants
`β = 1/2`, `C = 1`, `c₀ = 1/100`.  The present module proves the **general** statement:
for **every** `β ∈ (0,1)` and **every** `C > 0` there is `c₀ > 0` (depending on `β` and
`C`) for which the budget holds — which is the form `lem:LocKinEn` is consumed in.

## Route

The budget is homogeneous in the box momentum `q := ℓ‖p‖`:

* `tprSym_scale`  : `ℓ² tprSym ℓ σ C p = tprR σ C (ℓ‖p‖)`;
* `raTerm_scale`  : `ℓ² ((dℓ)⁻² raSym ℓ d p) = (ℓ‖p‖)²/(1+d²(ℓ‖p‖)²)`;
* `gapTerm_scale` : `ℓ² (‖p‖²/(ℓ²‖p‖²+β)) = (ℓ‖p‖)²/((ℓ‖p‖)²+β)`.

Multiplying by `ℓ² > 0` and putting `q = ℓ‖p‖` therefore reduces the budget to the pure
real inequality `core_budget`:

```
εT q²/(1+d²q²) + b β⁻¹ q²/(q²+β) + (1-εT) tprR (2s) C q + εT tprR (2ds) C q ≤ q².
```

`core_budget` splits on which branch of the two-regime kernel is active.  Because
`d ≤ 1` the switch `(5/6)(2s)⁻¹` of the `s`-cut-off is below the switch
`(5/6)(2ds)⁻¹` of the `ds`-cut-off, so there are exactly three regions:

| region | `q` | kernel values | lemma |
|---|---|---|---|
| A (both near) | `q < (5/6)(2s)⁻¹` | `8Cs³q²`, `8Cd³s³q²` | `budget_near_near` |
| B (mixed) | `(5/6)(2s)⁻¹ ≤ q < (5/6)(2ds)⁻¹` | `(q−(4s)⁻¹)²`, `8Cd³s³q²` | `budget_mixed` |
| C (both far) | `(5/6)(2ds)⁻¹ ≤ q` | `(q−(4s)⁻¹)²`, `(q−(4ds)⁻¹)²` | `budget_far_far` |

The region A coefficient budget is `εT + bβ⁻² + 8Cs³ ≤ 1`; in region B the quadratic
saving `2qA − A² ≥ (7/3)A²` (`A = (4s)⁻¹`) of the far cut-off pays for the residual gap
term `bβ⁻¹` and for the near branch of the `ds`-cut-off, bounded by `(25/18)Cds`; in
region C the two savings `(7/3)[(1−εT)A² + εT B²]` (`B = (4ds)⁻¹`) pay for
`εT/d² + bβ⁻¹`.  All three slack conditions are consequences of the smallness of `c₀`
(`slack_conditions`, `exists_small_czero`), the constants being chosen so that
`c₀ ≤ min(1/4, β²/4, 1/(64(1+C)))`.

In particular the budget is *not* proved at a fixed universal `c₀`: `c₀` must shrink with
`C` (the near branch of `tprSym` grows linearly in `C`) and with `β` (the gap symbol
`β⁻¹q²/(q²+β)` behaves like `β⁻²q²` at small momenta).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseKinLoc.Assembly

open Work.BoseKinLoc
open Submission.BoseGases

/-- **The general-`(β,C)` box-momentum budget.**  Given the six smallness conditions on
`c₀` produced by `exists_small_czero`, the pointwise budget holds in the box momentum
`q = ℓ‖p‖` for all `0 < d,s,εT,b ≤ c₀`.

The proof is the three-region case split of the two branches of the two-regime kernel
(`tprR_near`, `tprR_far_gen`), dispatching to `budget_near_near` / `budget_mixed` /
`budget_far_far` with the slack conditions supplied by `slack_conditions`. -/
lemma core_budget (β C c₀ q d s εT b : ℝ) (hβ : 0 < β) (hC : 0 < C)
    (hc₁ : c₀ ≤ 1 / 4) (hc₂ : c₀ ≤ β ^ 2 / 4) (hc₃ : 8 * C * c₀ ^ 3 ≤ 1 / 4)
    (hc₄ : 128 * c₀ ^ 3 ≤ 7 * β) (hc₅ : (1600 / 9) * C * c₀ ^ 5 ≤ 7) (hc₆ : 48 * c₀ ^ 2 ≤ 7)
    (hd : 0 < d) (hdc : d ≤ c₀) (hs : 0 < s) (hsc : s ≤ c₀)
    (hε : 0 ≤ εT) (hεc : εT ≤ c₀) (hb : 0 ≤ b) (hbc : b ≤ c₀) :
    εT * q ^ 2 / (1 + d ^ 2 * q ^ 2) + b * β⁻¹ * (q ^ 2 / (q ^ 2 + β))
      + (1 - εT) * tprR (2 * s) C q + εT * tprR (2 * (d * s)) C q ≤ q ^ 2 := by
  have hc₀pos : 0 < c₀ := lt_of_lt_of_le hs hsc
  have hd1 : d ≤ 1 := by linarith
  have hε1 : εT ≤ 1 := by linarith
  obtain ⟨hA, hB, hC'⟩ :=
    slack_conditions β C c₀ d s εT b hβ hC hc₀pos hc₁ hc₂ hc₃ hc₄ hc₅ hc₆
      hd hdc hs hsc hε hεc hb hbc
  have h2s : (0 : ℝ) < 2 * s := by linarith
  have h2ds : (0 : ℝ) < 2 * (d * s) := by positivity
  by_cases h1 : (5 / 6) * (2 * s)⁻¹ ≤ q
  · -- the first cut-off is already far
    by_cases h2 : (5 / 6) * (2 * (d * s))⁻¹ ≤ q
    · -- ===== region C : both branches far =====
      rw [tprR_far_gen h2s h1, tprR_far_gen h2ds h2]
      exact budget_far_far β q d s εT b hβ hd hd1 hs hε hε1 hb h1 h2 hC'
    · -- ===== region B : first far, second near =====
      rw [tprR_far_gen h2s h1, tprR_near h2]
      exact budget_mixed β C q d s εT b hβ hC.le hd hd1 hs hε hε1 hb h1 h2 hB
  · -- ===== region A : both branches near =====
    have h2' : ¬ ((5 / 6) * (2 * (d * s))⁻¹ ≤ q) := by
      intro hcon
      apply h1
      have hle : (2 * s)⁻¹ ≤ (2 * (d * s))⁻¹ :=
        (inv_le_inv₀ h2s h2ds).mpr (by nlinarith [hd1, hs])
      nlinarith [hle, hcon]
    rw [tprR_near h1, tprR_near h2']
    exact budget_near_near β C q d s εT b hβ hC.le hd hd1 hs hε hb hA

/-- **The general two-regime momentum budget** `AssemblySymbol β C` for arbitrary
`β ∈ (0,1)` and `C > 0`: there is `c₀ > 0` (namely `min(1/4, β²/4, 1/(64(1+C)))`,
`exists_small_czero`) such that the box-momentum budget of `core_budget` holds for all
`0 < d,s,εT,b ≤ c₀`. -/
theorem assembly_symbol_general (β C : ℝ) (hβ : 0 < β) (hβ1 : β < 1) (hC : 0 < C) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ Work.BoseKinLoc.AssemblySymbol β C := by
  obtain ⟨c₀, hc₀pos, hc₁, hc₂, hc₃, hc₄, hc₅, hc₆⟩ := exists_small_czero β C hβ hβ1 hC
  refine ⟨c₀, hc₀pos, ?_⟩
  unfold AssemblySymbol
  refine ⟨c₀, hc₀pos, ?_⟩
  intro ℓ d s εT b hreg p
  unfold KinRegime at hreg
  obtain ⟨hℓ, hd, hdc, hd1, hs, hsc, hε, hεc, hb, hbc⟩ := hreg
  set q : ℝ := ℓ * ‖p‖ with hqdef
  have hℓ2 : 0 < ℓ ^ 2 := by positivity
  have hcore : εT * q ^ 2 / (1 + d ^ 2 * q ^ 2) + b * β⁻¹ * (q ^ 2 / (q ^ 2 + β))
      + (1 - εT) * tprR (2 * s) C q + εT * tprR (2 * (d * s)) C q ≤ q ^ 2 :=
    core_budget β C c₀ q d s εT b hβ hC hc₁ hc₂ hc₃ hc₄ hc₅ hc₆
      hd hdc hs hsc hε.le hεc hb.le hbc
  have e1 : ℓ ^ 2 * (εT * (d * ℓ) ^ (-2 : ℤ) * raSym ℓ d p)
      = εT * q ^ 2 / (1 + d ^ 2 * q ^ 2) := by
    have h := raTerm_scale ℓ d hℓ hd p
    rw [← hqdef] at h
    rw [show ℓ ^ 2 * (εT * (d * ℓ) ^ (-2 : ℤ) * raSym ℓ d p)
        = εT * (ℓ ^ 2 * ((d * ℓ) ^ (-2 : ℤ) * raSym ℓ d p)) by ring, h]
    ring
  have e2 : ℓ ^ 2 * (b * β⁻¹ * (‖p‖ ^ 2 / (ℓ ^ 2 * ‖p‖ ^ 2 + β)))
      = b * β⁻¹ * (q ^ 2 / (q ^ 2 + β)) := by
    have h := gapTerm_scale ℓ β hℓ p
    rw [← hqdef] at h
    rw [show ℓ ^ 2 * (b * β⁻¹ * (‖p‖ ^ 2 / (ℓ ^ 2 * ‖p‖ ^ 2 + β)))
        = b * β⁻¹ * (ℓ ^ 2 * (‖p‖ ^ 2 / (ℓ ^ 2 * ‖p‖ ^ 2 + β))) by ring, h]
  have e3 : ℓ ^ 2 * ((1 - εT) * tprSym ℓ (2 * s) C p) = (1 - εT) * tprR (2 * s) C q := by
    have h := tprSym_scale ℓ (2 * s) C hℓ p
    rw [← hqdef] at h
    rw [show ℓ ^ 2 * ((1 - εT) * tprSym ℓ (2 * s) C p)
        = (1 - εT) * (ℓ ^ 2 * tprSym ℓ (2 * s) C p) by ring, h]
  have e4 : ℓ ^ 2 * (εT * tprSym ℓ (2 * (d * s)) C p) = εT * tprR (2 * (d * s)) C q := by
    have h := tprSym_scale ℓ (2 * (d * s)) C hℓ p
    rw [← hqdef] at h
    rw [show ℓ ^ 2 * (εT * tprSym ℓ (2 * (d * s)) C p)
        = εT * (ℓ ^ 2 * tprSym ℓ (2 * (d * s)) C p) by ring, h]
  have e5 : ℓ ^ 2 * ‖p‖ ^ 2 = q ^ 2 := by rw [hqdef]; ring
  apply (mul_le_mul_iff_of_pos_left hℓ2).mp
  rw [mul_add, mul_add, mul_add, e1, e2, e3, e4, e5]
  linarith [hcore]

end Work.BoseKinLoc.Assembly
