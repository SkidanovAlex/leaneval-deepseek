import ChallengeDeps
import Submission.Work.BoseBogFS.BogFSCompare
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBogFS.bogParamsData` — the parameter data of `fsParams (μ·(a v)³)`

The parameter block `P = paramsAt μ (a v) = fsParams (μ·(a v)³)` of the box word
satisfies, at any chemical potential `μ > 0` for which the two kinetic cutoffs
`bogC1`, `bogC2` are positive (i.e. `ℓ > 0` and `√(ρa) ≠ 0`),

* `0 < P.d` and `P.d ≤ 1`,
* `P.eT = P.d ^ (23/24)` — the `sec:params` relation `ε_T = d^{23/24}` at
  `d = (μa³)^{6/323}`, `ε_T = (μa³)^{(23/4)/323}`,
* `bogC2 = bogC1 / P.d` (`c₂ = c₁/d`, from `c₁ = (2sℓ√(ρa))⁻¹`).

The two structural inputs are:

* `ε_T = d^{23/24}` is `Real.rpow_mul` at the diluteness `t = μ(a v)³ ≥ 0`
  (`(t^{6/323})^{23/24} = t^{23/1292} = t^{(23/4)/323}`);
* `t ≥ 0` is **not** a hypothesis: it is forced by `0 < bogC1`.  Indeed if
  `μ·(a v) ≤ 0` then `(μ·(a v)) ^ (-1/2) = 0` (for a negative base the real
  `rpow` is `|x|^y cos(πy)`, and `cos(π/2) = 0`; for `x = 0` it is `0`), whence
  `ℓ = K_ℓ·(μa)^{-1/2} = 0` and `bogC1 = 0`, contradicting `hc1`.
-/

open Work.BoseFixR

namespace Work.BoseBogFS

/-- For a nonpositive base, the real power `x ^ (-1/2)` vanishes: for `x < 0` the
definition gives `|x|^{-1/2}·cos(-π/2) = 0`, and `0 ^ (-1/2) = 0` since `-1/2 ≠ 0`. -/
lemma rpow_neg_half_eq_zero_of_nonpos {x : ℝ} (hx : x ≤ 0) : x ^ (-(1 / 2 : ℝ)) = 0 := by
  rcases lt_or_eq_of_le hx with h | h
  · rw [Real.rpow_def_of_neg h]
    have hpi : -(1 / 2 : ℝ) * Real.pi = -(Real.pi / 2) := by ring
    rw [hpi, Real.cos_neg, Real.cos_pi_div_two, mul_zero]
  · subst h
    exact Real.zero_rpow (by norm_num)

/-- `ℓ = K_ℓ·(μa)^{-1/2}`: the box side of the frozen vocabulary, unfolded. -/
lemma ell_eq_kl_mul_rpow_neg_half (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ) :
    ell v μ = (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
      * (μ * _root_.BoseGases.a v) ^ (-(1 / 2 : ℝ)) := rfl

/-- If the diluteness were nonpositive the box side `ℓ` would vanish and hence
`bogC1 = 0`, contradicting `hc1`: so `0 < μ·(a v)`. -/
lemma bogC1_eq_zero_of_nonpos {v : EuclideanSpace ℝ (Fin 3) → ℝ} {ρ μ : ℝ}
    (h : μ * _root_.BoseGases.a v ≤ 0) : bogC1 v ρ μ = 0 := by
  have hEll := ell_eq_kl_mul_rpow_neg_half v μ
  have hz : (μ * _root_.BoseGases.a v) ^ (-(1 / 2 : ℝ)) = 0 :=
    rpow_neg_half_eq_zero_of_nonpos h
  rw [bogC1, hEll, hz]
  simp

theorem bogParamsData {v : EuclideanSpace ℝ (Fin 3) → ℝ} {ρ μ : ℝ}
    (hμ : 0 < μ)
    (hc1 : 0 < Work.BoseBogFS.bogC1 v ρ μ) (hc2 : 0 < Work.BoseBogFS.bogC2 v ρ μ)
    (heT1 : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT ≤ 1) :
    0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d ∧
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d ≤ 1 ∧
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
        = ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) ^ (23 / 24 : ℝ) ∧
      Work.BoseBogFS.bogC2 v ρ μ
        = Work.BoseBogFS.bogC1 v ρ μ / (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d := by
  -- The diluteness `t = μ·(a v)³` and the two parameter readings.
  have hd_def : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
      = (μ * (_root_.BoseGases.a v) ^ 3) ^ ((6 : ℝ) / 323) := rfl
  have heT_def : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
      = (μ * (_root_.BoseGases.a v) ^ 3) ^ (((23 : ℝ) / 4) / 323) := rfl
  -- Step 1: `hc1` forces the diluteness to be positive, hence `a v > 0`.
  have hx : 0 < μ * _root_.BoseGases.a v := by
    rcases le_or_gt (μ * _root_.BoseGases.a v) 0 with h | h
    · exact absurd (bogC1_eq_zero_of_nonpos h ▸ hc1) (lt_irrefl 0)
    · exact h
  have ha : 0 < _root_.BoseGases.a v := pos_of_mul_pos_right hx hμ.le
  have ht : 0 < μ * (_root_.BoseGases.a v) ^ 3 := by positivity
  -- Step 2: `0 < d`.
  have hdpos : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d := by
    rw [hd_def]
    exact Real.rpow_pos_of_pos ht _
  -- Step 3: `eT = d ^ (23/24)`.
  have heTd : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
      = ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) ^ (23 / 24 : ℝ) := by
    rw [heT_def, hd_def, ← Real.rpow_mul ht.le]
    congr 1
    norm_num
  -- Step 4: `t ≤ 1` from `eT ≤ 1`, hence `d ≤ 1`.
  have ht1 : μ * (_root_.BoseGases.a v) ^ 3 ≤ 1 := by
    have hle : (μ * (_root_.BoseGases.a v) ^ 3) ^ (((23 : ℝ) / 4) / 323) ≤ 1 := by
      rw [← heT_def]; exact heT1
    have h := Real.rpow_le_rpow (Real.rpow_nonneg ht.le _) hle (by norm_num : (0 : ℝ) ≤ 1292 / 23)
    rw [Real.one_rpow, ← Real.rpow_mul ht.le] at h
    rwa [show (((23 : ℝ) / 4) / 323) * (1292 / 23) = 1 by norm_num, Real.rpow_one] at h
  have hd1 : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d ≤ 1 := by
    rw [hd_def]
    exact Real.rpow_le_one ht.le ht1 (by norm_num)
  -- Step 5: `c₂ = c₁ / d`, a pure field identity.
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
  exact ⟨hdpos, hd1, heTd, hC2⟩

end Work.BoseBogFS
