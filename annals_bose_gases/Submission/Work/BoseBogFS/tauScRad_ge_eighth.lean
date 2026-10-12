import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBogFS.psiSc_tail_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBogFS.tauScRad_ge_eighth` — the symbol never drops below `r²/8`

The scaled kinetic symbol `τ_s,r = tauScRad v ρ μ r` is the two-term convex combination

`τ_s,r = (1-ε_T)·c₁²·τ̃(r/c₁) + ε_T·c₂²·τ̃(r/c₂)`,   `cᵢ = bogCᵢ v ρ μ`
(`tauScRad_eq`), of the rescaled profile `τ̃ = Work.BoseBoxFock.tauProf`, whose only lower
bound that is available for the opaque `tauProf` is
`τ̃ u ≥ (max 0 (u-2))²` (`exists_tauProf`).  Hence, for every `c > 0`,

`c²·τ̃(r/c) ≥ (max 0 (r - 2c))²`

(the *kink* domination, `sq_mul_tauProf_ge`).

Unlike the sharper sibling `tauScRad_ge_twelfth` — which uses the parameter relation
`ε_T = d^{23/24}`, `c₂ = c₁/d` to let the *second* kink pay when `ε_T` is large, and therefore
needs `0 < μ` and `0 < bogC2` — the constant `1/8` is paid by the **first** term alone:

* the hypothesis `4c₁ ≤ r` gives `r - 2c₁ ≥ r/2 ≥ 0` (and `r > 0`), so the first kink is at
  least `(r/2)² = r²/4`;
* the weight satisfies `1 - ε_T ≥ 1/2` because `ε_T ≤ 1/2` (`heT1`);
* the second summand is nonnegative (`ε_T ≥ 0`, `τ̃ ≥ 0`).

So `τ_s,r ≥ (1-ε_T)·r²/4 ≥ r²/8`, and no use at all is made of `μ`, `ε_T = d^{23/24}`, `d ≤ 1`
or of the basis `c₂ > 0` — which is what makes the statement available at the (weaker)
hypothesis set below.

This is the lower bound on the kinetic symbol used by the "tail" row `psiSc_tail_le` of the
clean-bracket comparison (cf. the sharper `tauScRad_ge_hundredth_local`,
`tauScRad_ge_twelfth`).
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox Work.BoseBoxFix Work.BoseFixR

namespace Work.BoseBogFS

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The first kink alone pays `r²/8`.**  Under `0 < c₁`, `0 ≤ ε_T`, `ε_T ≤ 1/2` and
`4c₁ ≤ r`,

`r²/8 ≤ (1-ε_T)·c₁²·τ̃(r/c₁)`.

The second kink is never touched, so neither a bound on `c₂` nor the parameter relation
`c₂ = c₁/d` is needed. -/
lemma eighth_le_one_kink {c₁ eT r : ℝ}
    (hc1 : 0 < c₁) (heT0 : 0 ≤ eT) (heT1 : eT ≤ 1 / 2) (hr : 4 * c₁ ≤ r) :
    r ^ 2 / 8 ≤ (1 - eT) * c₁ ^ 2 * Work.BoseBoxFock.tauProf (r / c₁) := by
  have hr0 : 0 < r := lt_of_lt_of_le (by linarith : (0 : ℝ) < 4 * c₁) hr
  -- the kink `(r - 2c₁)` dominates `r/2`
  have hmax : (r / 2) ^ 2 ≤ (max 0 (r - 2 * c₁)) ^ 2 := by
    have h0 : 0 ≤ r / 2 := by linarith
    have h1 : r / 2 ≤ r - 2 * c₁ := by linarith
    exact pow_le_pow_left₀ h0 (le_trans h1 (le_max_right _ _)) 2
  -- the kink is paid by the first profile term
  have hterm : (max 0 (r - 2 * c₁)) ^ 2 ≤ c₁ ^ 2 * Work.BoseBoxFock.tauProf (r / c₁) :=
    sq_mul_tauProf_ge hc1
  have hw : 0 ≤ 1 - eT := by linarith
  have h1 : (1 - eT) * (r / 2) ^ 2 ≤ (1 - eT) * (c₁ ^ 2 * Work.BoseBoxFock.tauProf (r / c₁)) :=
    mul_le_mul_of_nonneg_left (le_trans hmax hterm) hw
  -- `ε_T ≤ 1/2` gives the numerical factor `1/8`
  have hnum : eT * r ^ 2 ≤ (1 / 2) * r ^ 2 :=
    mul_le_mul_of_nonneg_right heT1 (sq_nonneg r)
  nlinarith [h1, hnum]

/-- **The kinetic symbol is not small**: `τ_s,r ≥ r²/8` (`τ_s,r = tauScRad v ρ μ r`),
from the single kink bound `(max 0 (r - 2c₁))² ≤ c₁²τ̃(r/c₁)`, the weight
`1 - ε_T ≥ 1/2` and the nonnegativity of the second summand. -/
theorem tauScRad_ge_eighth {v : EuclideanSpace ℝ (Fin 3) → ℝ} {ρ μ : ℝ}
    (hP : 0 < ρ * _root_.BoseGases.a v)
    (hc1 : 0 < Work.BoseBogFS.bogC1 v ρ μ)
    (heT0 : 0 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT)
    (heT1 : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT ≤ 1 / 2)
    {r : ℝ} (hr : 4 * Work.BoseBogFS.bogC1 v ρ μ ≤ r) :
    r ^ 2 / 8 ≤ Work.BoseBogFS.tauScRad v ρ μ r := by
  rw [Work.BoseBogFS.tauScRad_eq v hP r]
  set c₁ : ℝ := Work.BoseBogFS.bogC1 v ρ μ with hc1def
  set eT : ℝ := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT with heTdef
  -- the first summand pays `r²/8`
  have hone : r ^ 2 / 8 ≤ (1 - eT) * c₁ ^ 2 * Work.BoseBoxFock.tauProf (r / c₁) :=
    eighth_le_one_kink hc1 heT0 heT1 hr
  -- the second summand is nonnegative
  have htwo : 0 ≤ eT * (Work.BoseBogFS.bogC2 v ρ μ) ^ 2
      * Work.BoseBoxFock.tauProf (r / Work.BoseBogFS.bogC2 v ρ μ) :=
    mul_nonneg (mul_nonneg heT0 (sq_nonneg _)) (Work.BoseBoxFock.tauProf_nonneg _)
  linarith

end Work.BoseBogFS
