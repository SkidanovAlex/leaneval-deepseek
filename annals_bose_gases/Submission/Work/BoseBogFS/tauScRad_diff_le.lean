import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBogFS.bogCellDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBogFS.tauScRad_diff_le` — the one-sided increment bound for `τ_s` on the bulk

The scaled kinetic symbol is the two-slot convex combination
(`Work.BoseBogFS.tauScRad_eq`)

`τ_s(r) = tauScRad v ρ μ r = (1−ε_T)·c₁²·τ̃(r/c₁) + ε_T·c₂²·τ̃(r/c₂)`,

`cᵢ = bogCᵢ v ρ μ`, `ε_T = (paramsAt μ (a v)).eT`, `τ̃ = Work.BoseBoxFock.tauProf`.  The target
bounds the increment of `τ_s` from above by the increment of `x ↦ x²` plus one slot of room,
`y² − x² + ε_T·(max 0 (y − c₂))²`, assuming only that the *left* end `x` lies beyond the first
cut-off, `2c₁ ≤ x`.

## The mathematics: the two deficits `r² − c²τ̃(r/c)`

Write `G_c(r) = r² − c²·τ̃(r/c) ≥ 0` for the *deficit* of a single slot; then

`τ_s(y) − τ_s(x) = (y² − x²) − [(1−ε_T)(G_{c₁}(y) − G_{c₁}(x)) + ε_T(G_{c₂}(y) − G_{c₂}(x))]`,

so the target is equivalent to

`(1−ε_T)(G_{c₁}(y) − G_{c₁}(x)) + ε_T(G_{c₂}(y) − G_{c₂}(x)) ≥ − ε_T·(max 0 (y − c₂))²`.

This is the sum of two independent statements, and *both* are elementary given the exact
quadratic tail `τ̃(s) = (s−3/2)² + c₀` for `s ≥ 2` (`Work.BoseBoxFock.tauProf_quad`,
`Work.BoseBoxFock.tauChi_tail`) and the upper bound `τ̃(s) ≤ (max 0 (s−1))²`
(`Work.BoseBoxFock.tauProf_le_max_sq`):

* **the `c₁` slot is monotone**: for `r ≥ 2c` the deficit is *linear*,
  `G_c(r) = 3cr − (9/4+c₀)c²` (`deficit_eq_hinge`), hence increasing; the hypothesis `2c₁ ≤ x`
  is exactly what puts both `x` and `y` past the hinge.  So the `c₁` term contributes
  `≥ 0 ≥ −(max 0 (y−c₁))²` and needs *no* room.  This is `slot_le_sq`.
* **the `c₂` slot is paid by the room**: `G_{c₂}(x) ≤ x²` (as `τ̃ ≥ 0`) and `x² ≤ y²` give
  `G_{c₂}(y) − G_{c₂}(x) ≥ −c₂²τ̃(y/c₂)`, and `c₂²τ̃(y/c₂) ≤ (max 0 (y−c₂))²` is exactly (P4)
  rescaled.  This is `slot_le_sq_add`, and it needs no hypothesis on `x` beyond `0 ≤ x`.

Note that no ordering of `c₁, c₂` is used, and `y` need not lie beyond `2c₂`: the `c₂` slot is
handled over the whole range.  The two statements are combined in `tauScRad_diff_le` with the
weights `1−ε_T ≥ 0`, `ε_T ≥ 0` summing to one.

## Relation to the neighbours

`Work.BoseBogFS.tauScRad_diff_le_quad` is the special case in which both ends are past `2c₂`
(hence no room is needed); `Work.BoseBogFS.tauScRad_sub_le` is the small-step version.
-/

namespace Work.BoseBogFS

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. The profile is nonnegative -/

/-- `τ̃ ≥ 0`: by (P5) it vanishes at `1` and by (P2) it is monotone. -/
private lemma tauProf_nonneg_local (s : ℝ) : 0 ≤ Work.BoseBoxFock.tauProf s := by
  rcases le_or_gt s 1 with h | h
  · rw [Work.BoseBoxFock.tauProf_eq_zero_of_le_one h]
  · have hle := Work.BoseBoxFock.tauProf_mono h.le
    rw [Work.BoseBoxFock.tauProf_eq_zero_of_le_one le_rfl] at hle
    exact hle

/-! ## 2. The deficit of one slot -/

/-- **The deficit of the rescaled profile is a hinge**: for `c > 0` and `r ≥ 2c`,

  `r² − c²·τ̃(r/c) = 3cr − (9/4 + c₀)c²`.

In particular it is *increasing* in `r` past `2c`. -/
private lemma deficit_eq_hinge {c r : ℝ} (hc : 0 < c) (hr : 2 * c ≤ r) :
    r ^ 2 - c ^ 2 * Work.BoseBoxFock.tauProf (r / c)
      = 3 * c * r - (9 / 4 + Work.BoseBoxFock.tauC0) * c ^ 2 := by
  rw [Work.BoseBoxFock.tauChi_tail hc hr]
  ring

/-- **The `c`-slot increment is dominated by the quadratic increment**, as soon as the left end
lies past the hinge `2c`:

  `c²(τ̃(y/c) − τ̃(x/c)) ≤ y² − x²`  for `c > 0`, `2c ≤ x ≤ y`. -/
private lemma slot_le_sq {c x y : ℝ} (hc : 0 < c) (h2c : 2 * c ≤ x) (hxy : x ≤ y) :
    c ^ 2 * (Work.BoseBoxFock.tauProf (y / c) - Work.BoseBoxFock.tauProf (x / c))
      ≤ y ^ 2 - x ^ 2 := by
  have hy2 : 2 * c ≤ y := le_trans h2c hxy
  have hx := deficit_eq_hinge (c := c) (r := x) hc h2c
  have hy := deficit_eq_hinge (c := c) (r := y) hc hy2
  rw [mul_sub]
  nlinarith [hx, hy, hc, hxy]

/-- **The `c`-slot increment, with the cut-off room**: for `c > 0`, `0 ≤ x ≤ y`,

  `c²(τ̃(y/c) − τ̃(x/c)) ≤ (y² − x²) + (max 0 (y − c))²`.

No hypothesis beyond `0 ≤ x` is needed: the deficit of the slot is bounded below by
`−(max 0 (y−c))²` on the whole range. -/
private lemma slot_le_sq_add {c x y : ℝ} (hc : 0 < c) (hx : 0 ≤ x) (hxy : x ≤ y) :
    c ^ 2 * (Work.BoseBoxFock.tauProf (y / c) - Work.BoseBoxFock.tauProf (x / c))
      ≤ (y ^ 2 - x ^ 2) + (max 0 (y - c)) ^ 2 := by
  -- the rescaled (P4)
  have hmax : max 0 (y / c - 1) * c = max 0 (y - c) := by
    rw [max_mul_of_nonneg 0 (y / c - 1) hc.le, zero_mul]
    congr 1
    field_simp
  have hsq : (max 0 (y / c - 1)) ^ 2 * c ^ 2 = (max 0 (y - c)) ^ 2 := by
    rw [← hmax, mul_pow]
  have hτy : c ^ 2 * Work.BoseBoxFock.tauProf (y / c) ≤ (max 0 (y - c)) ^ 2 := by
    have h := Work.BoseBoxFock.tauProf_le_max_sq (y / c)
    have h2 := mul_le_mul_of_nonneg_left h (sq_nonneg c)
    calc c ^ 2 * Work.BoseBoxFock.tauProf (y / c)
        ≤ c ^ 2 * (max 0 (y / c - 1)) ^ 2 := h2
      _ = (max 0 (y - c)) ^ 2 := by rw [mul_comm, hsq]
  have hτx : 0 ≤ c ^ 2 * Work.BoseBoxFock.tauProf (x / c) :=
    mul_nonneg (sq_nonneg c) (tauProf_nonneg_local _)
  have hsq' : 0 ≤ y ^ 2 - x ^ 2 := by nlinarith [hx, hxy]
  rw [mul_sub]
  linarith [hτy, hτx]

/-! ## 3. The target -/

theorem tauScRad_diff_le {v : EuclideanSpace ℝ (Fin 3) → ℝ} {ρ μ : ℝ}
    (hP : 0 < ρ * _root_.BoseGases.a v)
    (heT0 : 0 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT)
    (heT1 : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT ≤ 1)
    (hc1 : 0 < Work.BoseBogFS.bogC1 v ρ μ) (hc2 : 0 < Work.BoseBogFS.bogC2 v ρ μ)
    {x y : ℝ} (h2c1 : 2 * Work.BoseBogFS.bogC1 v ρ μ ≤ x) (hxy : x ≤ y) :
    Work.BoseBogFS.tauScRad v ρ μ y - Work.BoseBogFS.tauScRad v ρ μ x
      ≤ (y ^ 2 - x ^ 2)
        + (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
          * (max 0 (y - Work.BoseBogFS.bogC2 v ρ μ)) ^ 2 := by
  have hx0 : 0 ≤ x := le_trans (by linarith : (0 : ℝ) ≤ 2 * Work.BoseBogFS.bogC1 v ρ μ) h2c1
  -- the two slot increments
  have h1 : (Work.BoseBogFS.bogC1 v ρ μ) ^ 2
      * (Work.BoseBoxFock.tauProf (y / Work.BoseBogFS.bogC1 v ρ μ)
          - Work.BoseBoxFock.tauProf (x / Work.BoseBogFS.bogC1 v ρ μ))
      ≤ y ^ 2 - x ^ 2 :=
    slot_le_sq hc1 h2c1 hxy
  have h2 : (Work.BoseBogFS.bogC2 v ρ μ) ^ 2
      * (Work.BoseBoxFock.tauProf (y / Work.BoseBogFS.bogC2 v ρ μ)
          - Work.BoseBoxFock.tauProf (x / Work.BoseBogFS.bogC2 v ρ μ))
      ≤ (y ^ 2 - x ^ 2) + (max 0 (y - Work.BoseBogFS.bogC2 v ρ μ)) ^ 2 :=
    slot_le_sq_add hc2 hx0 hxy
  -- the symbol difference is the weighted sum of the two slot increments
  have hdec : Work.BoseBogFS.tauScRad v ρ μ y - Work.BoseBogFS.tauScRad v ρ μ x
      = (1 - (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT)
          * ((Work.BoseBogFS.bogC1 v ρ μ) ^ 2
              * (Work.BoseBoxFock.tauProf (y / Work.BoseBogFS.bogC1 v ρ μ)
                  - Work.BoseBoxFock.tauProf (x / Work.BoseBogFS.bogC1 v ρ μ)))
        + (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
          * ((Work.BoseBogFS.bogC2 v ρ μ) ^ 2
              * (Work.BoseBoxFock.tauProf (y / Work.BoseBogFS.bogC2 v ρ μ)
                  - Work.BoseBoxFock.tauProf (x / Work.BoseBogFS.bogC2 v ρ μ))) := by
    rw [Work.BoseBogFS.tauScRad_eq (v := v) (ρ := ρ) (μ := μ) hP y,
      Work.BoseBogFS.tauScRad_eq (v := v) (ρ := ρ) (μ := μ) hP x]
    ring
  rw [hdec]
  have hA : 0 ≤ 1 - (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT := by linarith
  have hs1 := mul_le_mul_of_nonneg_left h1 hA
  have hs2 := mul_le_mul_of_nonneg_left h2 heT0
  have hcomb : (1 - (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT) * (y ^ 2 - x ^ 2)
        + (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
          * ((y ^ 2 - x ^ 2) + (max 0 (y - Work.BoseBogFS.bogC2 v ρ μ)) ^ 2)
      = (y ^ 2 - x ^ 2)
        + (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
          * (max 0 (y - Work.BoseBogFS.bogC2 v ρ μ)) ^ 2 := by
    ring
  linarith [hs1, hs2, hcomb.le, hcomb.ge]

end Work.BoseBogFS
