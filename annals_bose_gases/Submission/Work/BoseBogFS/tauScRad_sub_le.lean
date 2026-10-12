import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBogFS.bogCellDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBogFS.tauScRad_sub_le` — the increment of the scaled kinetic symbol

The scaled kinetic symbol is the two-term convex combination

`τ_s(r) = tauScRad v ρ μ r = (1−ε_T)·c₁²·τ̃(r/c₁) + ε_T·c₂²·τ̃(r/c₂)`,

`cᵢ = bogCᵢ v ρ μ`, `ε_T = (paramsAt μ (a v)).eT`, `τ̃ = Work.BoseBoxFock.tauProf`
(`tauScRad_eq`), of the rescaled profile `τ̃`.  The target bounds the increment of `τ_s`
between `r ≤ r'` by the increment of the *quadratic* `x ↦ x²` plus a `9c₁²` room:

  `τ_s(r') − τ_s(r) ≤ (r'−r)(r'+r) + 9c₁²`,

under `0 ≤ r`, `r ≤ r' ≤ c₂`, `r' − r ≤ c₁`.

## The two facts that make it true

* **the `c₂` slot is empty**: `τ̃ u = 0` for `u ≤ 1` (`tauProf_eq_zero_of_le_one`), and
  `r ≤ r' ≤ c₂` puts both `r/c₂, r'/c₂ ≤ 1`.  So only the `c₁` slot survives.
* **`τ̃` is an exact quadratic beyond `2`**: `τ̃ u = (u − 3/2)² + c₀` for `u ≥ 2`
  (`tauProf_quad`).  Writing `x = r/c₁`, `x' = r'/c₁ = x + t` with `t = (r'−r)/c₁ ∈ [0,1]`,
  the claim becomes `c₁²(τ̃(x+t) − τ̃ x) ≤ t(x+x')c₁² + 9c₁²`, i.e. the *profile* inequality

    `τ̃ (x+t) − τ̃ x ≤ t(2x+t) + 9    (x ≥ 0, 0 ≤ t ≤ 1)`

  (`tauProf_diff_le`): in the quadratic region `x ≥ 2` the left-hand side is
  `t(2x − 3 + t) ≤ t(2x+t) + 9`; below `x ≤ 2` the upper bound `τ̃ ≤ (max 0 (·−1))²`
  (`tauProf_le_max_sq`) caps the increment at `4 ≤ 9`.

## Where the room is used

The `9` is far from tight: below `2c₁` the increment is at most `4` (in units of `c₁²`), and
in the quadratic region the deficit `−3t` of the hinge is absorbed by the `9`.  The bound
therefore holds with any constant `≥ 4`; `9` is the (frozen) statement's choice.
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox Work.BoseBoxFix Work.BoseFixR

namespace Work.BoseBogFS

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. The profile increment -/

/-- **The increment of the profile is at most the increment of its hinge, plus `9`**: for
`x ≥ 0` and `0 ≤ t ≤ 1`,

  `τ̃ (x+t) − τ̃ x ≤ t(2x+t) + 9`.

For `x ≥ 2` both arguments are in the exact quadratic region of `τ̃`
(`tauProf_quad`), where the increment is `t(2x − 3 + t) ≤ t(2x+t)`; for `x ≤ 2` the upper
bound `τ̃ s ≤ (max 0 (s−1))²` at `s = x+t ≤ 3` caps the increment by `4`. -/
private lemma tauProf_diff_le {x t : ℝ} (hx : 0 ≤ x) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Work.BoseBoxFock.tauProf (x + t) - Work.BoseBoxFock.tauProf x
      ≤ t * (2 * x + t) + 9 := by
  rcases le_or_gt 2 x with h2 | h2
  · -- both arguments lie in the exact quadratic tail
    rw [Work.BoseBoxFock.tauProf_quad h2,
      Work.BoseBoxFock.tauProf_quad (by linarith : (2 : ℝ) ≤ x + t)]
    ring_nf
    linarith
  · -- `x < 2`: the increment is capped by `4`
    have h0 : 0 ≤ Work.BoseBoxFock.tauProf x := by
      have h := Work.BoseBoxFock.tauProf_spec.2.2.1 x
      nlinarith [sq_nonneg (max 0 (x - 2))]
    have hle : Work.BoseBoxFock.tauProf (x + t) ≤ 4 := by
      have h := Work.BoseBoxFock.tauProf_le_max_sq (x + t)
      have hb : max 0 (x + t - 1) ≤ 2 := by
        rw [max_le_iff]; exact ⟨by norm_num, by linarith⟩
      have hp : (max 0 (x + t - 1)) ^ 2 ≤ (2 : ℝ) ^ 2 :=
        pow_le_pow_left₀ (le_max_left (0 : ℝ) (x + t - 1)) hb 2
      calc Work.BoseBoxFock.tauProf (x + t) ≤ (max 0 (x + t - 1)) ^ 2 := h
        _ ≤ (2 : ℝ) ^ 2 := hp
        _ = 4 := by norm_num
    have hpos : 0 ≤ t * (2 * x + t) := by
      apply mul_nonneg ht0; linarith
    linarith

/-- **The scaled form of the profile increment**: for `C > 0`, `0 ≤ r ≤ r'`,
`r' − r ≤ C`,

  `C²(τ̃ (r'/C) − τ̃ (r/C)) ≤ (r'−r)(r'+r) + 9C²`.

This is `tauProf_diff_le` at `x = r/C`, `t = (r'−r)/C`, multiplied by `C²`; the identity
`C²·t(2x+t) = (r'−r)(r'+r)` uses `C(2r + r' − r)/C = r' + r`. -/
private lemma tauProf_scale_diff_le {C : ℝ} (hC : 0 < C) {r r' : ℝ}
    (hr : 0 ≤ r) (hrr : r ≤ r') (hsm : r' - r ≤ C) :
    C ^ 2 * (Work.BoseBoxFock.tauProf (r' / C) - Work.BoseBoxFock.tauProf (r / C))
      ≤ (r' - r) * (r' + r) + 9 * C ^ 2 := by
  have hx0 : 0 ≤ r / C := div_nonneg hr hC.le
  have ht0 : 0 ≤ (r' - r) / C := div_nonneg (by linarith) hC.le
  have ht1 : (r' - r) / C ≤ 1 := by
    rw [div_le_one hC]; exact hsm
  have hkey := tauProf_diff_le (x := r / C) (t := (r' - r) / C) hx0 ht0 ht1
  have harg : r / C + (r' - r) / C = r' / C := by field_simp; ring
  rw [harg] at hkey
  have h1 := mul_le_mul_of_nonneg_left hkey (sq_nonneg C)
  have heq : C ^ 2 *
      ((r' - r) / C * (2 * (r / C) + (r' - r) / C) + 9)
      = (r' - r) * (r' + r) + 9 * C ^ 2 := by
    field_simp; ring
  rw [heq] at h1
  exact h1

/-! ## 2. The target -/

theorem tauScRad_sub_le {v : EuclideanSpace ℝ (Fin 3) → ℝ} {ρ μ : ℝ}
    (hP : 0 < ρ * _root_.BoseGases.a v)
    (hc1 : 0 < Work.BoseBogFS.bogC1 v ρ μ) (hc2 : 0 < Work.BoseBogFS.bogC2 v ρ μ)
    (heT0 : 0 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT)
    (heT1 : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT ≤ 1)
    {r r' : ℝ} (hr : 0 ≤ r) (hrr : r ≤ r') (hrc : r' ≤ Work.BoseBogFS.bogC2 v ρ μ)
    (hsm : r' - r ≤ Work.BoseBogFS.bogC1 v ρ μ) :
    Work.BoseBogFS.tauScRad v ρ μ r' - Work.BoseBogFS.tauScRad v ρ μ r
      ≤ (r' - r) * (r' + r) + 9 * (Work.BoseBogFS.bogC1 v ρ μ) ^ 2 := by
  -- the `c₂` slot vanishes: `r/c₂ ≤ r'/c₂ ≤ 1`
  have hzr' : Work.BoseBoxFock.tauProf (r' / Work.BoseBogFS.bogC2 v ρ μ) = 0 := by
    apply Work.BoseBoxFock.tauProf_eq_zero_of_le_one
    rw [div_le_one hc2]; exact hrc
  have hzr : Work.BoseBoxFock.tauProf (r / Work.BoseBogFS.bogC2 v ρ μ) = 0 := by
    apply Work.BoseBoxFock.tauProf_eq_zero_of_le_one
    rw [div_le_one hc2]; linarith
  -- the `c₁` slot is monotone in `r`, so its increment is nonnegative
  have hnonneg : 0 ≤ Work.BoseBoxFock.tauProf (r' / Work.BoseBogFS.bogC1 v ρ μ)
      - Work.BoseBoxFock.tauProf (r / Work.BoseBogFS.bogC1 v ρ μ) := by
    have h := Work.BoseBoxFock.tauProf_mono
      (div_le_div_of_nonneg_right hrr hc1.le)
    linarith
  have hkey := tauProf_scale_diff_le (C := Work.BoseBogFS.bogC1 v ρ μ) hc1 hr hrr hsm
  -- the symbol difference is exactly the weighted `c₁`-slot increment
  have hdecomp : Work.BoseBogFS.tauScRad v ρ μ r' - Work.BoseBogFS.tauScRad v ρ μ r
      = (1 - (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT)
          * ((Work.BoseBogFS.bogC1 v ρ μ) ^ 2
              * (Work.BoseBoxFock.tauProf (r' / Work.BoseBogFS.bogC1 v ρ μ)
                  - Work.BoseBoxFock.tauProf (r / Work.BoseBogFS.bogC1 v ρ μ))) := by
    rw [tauScRad_eq v hP r, tauScRad_eq v hP r', hzr', hzr]
    ring
  rw [hdecomp]
  have hX : 0 ≤ (Work.BoseBogFS.bogC1 v ρ μ) ^ 2
      * (Work.BoseBoxFock.tauProf (r' / Work.BoseBogFS.bogC1 v ρ μ)
          - Work.BoseBoxFock.tauProf (r / Work.BoseBogFS.bogC1 v ρ μ)) :=
    mul_nonneg (sq_nonneg _) hnonneg
  have hE : 1 - (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT ≤ 1 := by linarith
  calc (1 - (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT)
        * ((Work.BoseBogFS.bogC1 v ρ μ) ^ 2
            * (Work.BoseBoxFock.tauProf (r' / Work.BoseBogFS.bogC1 v ρ μ)
                - Work.BoseBoxFock.tauProf (r / Work.BoseBogFS.bogC1 v ρ μ)))
      ≤ 1 * ((Work.BoseBogFS.bogC1 v ρ μ) ^ 2
            * (Work.BoseBoxFock.tauProf (r' / Work.BoseBogFS.bogC1 v ρ μ)
                - Work.BoseBoxFock.tauProf (r / Work.BoseBogFS.bogC1 v ρ μ))) :=
        mul_le_mul_of_nonneg_right hE hX
    _ = (Work.BoseBogFS.bogC1 v ρ μ) ^ 2
            * (Work.BoseBoxFock.tauProf (r' / Work.BoseBogFS.bogC1 v ρ μ)
                - Work.BoseBoxFock.tauProf (r / Work.BoseBogFS.bogC1 v ρ μ)) := by ring
    _ ≤ (r' - r) * (r' + r) + 9 * (Work.BoseBogFS.bogC1 v ρ μ) ^ 2 := hkey

end Work.BoseBogFS
