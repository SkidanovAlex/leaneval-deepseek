import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBogFS.bogParamsData
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBogFS.bogD_le_one_of_eT_le_one`

The cutoff `c₂ = bogC2 v ρ μ` of the honest FS kernel is `c₁/d` with `c₁ = bogC1 v ρ μ`
and `d = (paramsAt μ (a v)).d`, and `0 < d ≤ 1` as soon as `0 < c₁` and `ε_T ≤ 1`.

The two structural facts (both at the diluteness `t = μ·(a v)³`):

* `d = t^{6/323} > 0` requires `t > 0`; this is *not* a hypothesis: the box side is
  `ℓ = K_ℓ (μa)^{-1/2}`, which vanishes for `μ·(a v) ≤ 0` (for a nonpositive base the real
  `rpow` is `|x|^y cos(πy)` and `cos(-π/2) = 0`, while `0^{-1/2} = 0`), so `c₁ = 0` and
  `hc1` rules it out.  Then `t = (μ·(a v))·(a v)² > 0` because `a v ≠ 0`;
* `d ≤ 1` follows from `ε_T = t^{23/1292} ≤ 1`, since raising to the `1292/23`-th power
  (a nonnegative exponent, `Real.rpow_le_rpow`) gives `t ≤ 1`, whence `t^{6/323} ≤ 1`.

The identity `c₂ = c₁/d` is pure commutativity of the product in a field: no positivity
is needed.  The statement is `Work.BoseBogFS.bogParamsData` with the two extra hypotheses
`0 < μ` and `0 < bogC2` and the extra conjunct `ε_T = d^{23/24}` removed.
-/

namespace Work.BoseBogFS

theorem bogD_le_one_of_eT_le_one {v : EuclideanSpace ℝ (Fin 3) → ℝ} {ρ μ : ℝ}
    (hc1 : 0 < Work.BoseBogFS.bogC1 v ρ μ)
    (heT1 : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT ≤ 1) :
    0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d ∧
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d ≤ 1 ∧
      Work.BoseBogFS.bogC2 v ρ μ
        = Work.BoseBogFS.bogC1 v ρ μ
          / (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d := by
  -- The diluteness `t = μ·(a v)³` and the two readings of the parameter block.
  have hd_def : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
      = (μ * (_root_.BoseGases.a v) ^ 3) ^ ((6 : ℝ) / 323) := rfl
  have heT_def : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
      = (μ * (_root_.BoseGases.a v) ^ 3) ^ (((23 : ℝ) / 4) / 323) := rfl
  -- Step 1: `hc1` forces `μ·(a v) > 0` (otherwise `ℓ = 0` and `c₁ = 0`).
  have hx : 0 < μ * _root_.BoseGases.a v := by
    rcases le_or_gt (μ * _root_.BoseGases.a v) 0 with h | h
    · have h0 := bogC1_eq_zero_of_nonpos (v := v) (ρ := ρ) h
      rw [h0] at hc1
      exact absurd hc1 (lt_irrefl 0)
    · exact h
  -- Step 2: hence the diluteness `t = (μ·(a v))·(a v)²` is positive.
  have ht : 0 < μ * (_root_.BoseGases.a v) ^ 3 := by
    have hne : _root_.BoseGases.a v ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hx
      exact absurd hx (lt_irrefl 0)
    have hsq : 0 < (_root_.BoseGases.a v) ^ 2 := sq_pos_of_ne_zero hne
    rw [show μ * (_root_.BoseGases.a v) ^ 3
        = (μ * _root_.BoseGases.a v) * (_root_.BoseGases.a v) ^ 2 by ring]
    exact mul_pos hx hsq
  have hdpos : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d := by
    rw [hd_def]
    exact Real.rpow_pos_of_pos ht _
  -- Step 3: `ε_T ≤ 1` gives `t ≤ 1`, hence `d = t^{6/323} ≤ 1`.
  have ht1 : μ * (_root_.BoseGases.a v) ^ 3 ≤ 1 := by
    have hle : (μ * (_root_.BoseGases.a v) ^ 3) ^ (((23 : ℝ) / 4) / 323) ≤ 1 := by
      rw [← heT_def]
      exact heT1
    have h := Real.rpow_le_rpow (Real.rpow_nonneg ht.le _) hle (by norm_num : (0 : ℝ) ≤ 1292 / 23)
    rw [Real.one_rpow, ← Real.rpow_mul ht.le] at h
    rwa [show (((23 : ℝ) / 4) / 323) * (1292 / 23) = 1 by norm_num, Real.rpow_one] at h
  have hd1 : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d ≤ 1 := by
    rw [hd_def]
    exact Real.rpow_le_one ht.le ht1 (by norm_num)
  -- Step 4: `c₂ = c₁ / d`, a pure field identity.
  have hC2 : Work.BoseBogFS.bogC2 v ρ μ
      = Work.BoseBogFS.bogC1 v ρ μ
        / (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d := by
    rw [bogC2, bogC1]
    rw [show 2 * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
            * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s * Work.BoseFixR.ell v μ
            * Real.sqrt (ρ * _root_.BoseGases.a v)
          = (2 * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s * Work.BoseFixR.ell v μ
              * Real.sqrt (ρ * _root_.BoseGases.a v))
            * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d from by ring]
    rw [mul_inv]
    ring
  exact ⟨hdpos, hd1, hC2⟩

end Work.BoseBogFS
