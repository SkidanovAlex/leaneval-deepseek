import ChallengeDeps
import Submission.Work.BoseBogFS.bogCellDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBogFS.tauScRad_diff_le_quad` — the increment of `τ_s` in the quadratic region

The scaled kinetic symbol is the two-term convex combination

`τ_s(r) = tauScRad v ρ μ r = (1−ε_T)·c₁²·τ̃(r/c₁) + ε_T·c₂²·τ̃(r/c₂)`,

`cᵢ = bogCᵢ v ρ μ`, `ε_T = (paramsAt μ (a v)).eT`, `τ̃ = Work.BoseBoxFock.tauProf`
(`tauScRad_eq`).  The target bounds the *increment* `τ_s(y) − τ_s(x)` by the increment of the
quadratic `x ↦ x²`:

  `τ_s(y) − τ_s(x) ≤ y² − x²`   for  `2c₂ ≤ x ≤ y`.

## Why it is true

The hypothesis `x ≥ 2c₂` (together with `c₁ ≤ c₂`) puts **both** arguments `x/c₁`, `y/c₁ ≥ 2` and
`x/c₂`, `y/c₂ ≥ 2` inside the exact quadratic tail of the profile,
`τ̃ u = (u − 3/2)² + c₀` for `u ≥ 2` (`tauProf_quad`, equivalently `tauChi_tail`).  Hence on
`[2c₂, ∞)` the scaled symbol is the *exact* two-slot quadratic

  `τ_s(r) = (1−ε_T)(r − 3c₁/2)² + ε_T(r − 3c₂/2)² + ((1−ε_T)c₁² + ε_Tc₂²)c₀`,

whose increment is affine in `r`:

  `τ_s(y) − τ_s(x) = (y−x)(y+x − 3κ)`,   `κ = (1−ε_T)c₁ + ε_T c₂ ≥ 0`,

while `y² − x² = (y−x)(y+x)`.  The claim is therefore exactly the statement that the deficit
`r ↦ r² − τ_s(r) = 3κr − ((1−ε_T)c₁² + ε_Tc₂²)c₀` is **nondecreasing** on the quadratic region —
indeed it is exactly affine there.  (The wedge `9c₁²` of the sibling `tauScRad_sub_le`, which
handles the *transition* region `r' ≤ c₂`, is not needed here: below `2c₂` the profile has not
yet reached its quadratic tail and the deficit can genuinely decrease.)
-/

namespace Work.BoseBogFS

/-- **The scaled symbol on the exact quadratic region `[2c₂, ∞)`.**  For
`r ≥ 2c₂ ≥ 2c₁` both rescaled profiles are in their exact quadratic tail
(`Work.BoseBoxFock.tauChi_tail`), so

  `τ_s(r) = (1−ε_T)(r − 3c₁/2)² + ε_T(r − 3c₂/2)² + ((1−ε_T)c₁² + ε_Tc₂²)c₀`. -/
private lemma tauScRad_eq_quad {v : EuclideanSpace ℝ (Fin 3) → ℝ} {ρ μ : ℝ}
    (hP : 0 < ρ * _root_.BoseGases.a v)
    (hc1 : 0 < Work.BoseBogFS.bogC1 v ρ μ) (hc2 : 0 < Work.BoseBogFS.bogC2 v ρ μ)
    (hc12 : Work.BoseBogFS.bogC1 v ρ μ ≤ Work.BoseBogFS.bogC2 v ρ μ)
    {r : ℝ} (hr : 2 * Work.BoseBogFS.bogC2 v ρ μ ≤ r) :
    Work.BoseBogFS.tauScRad v ρ μ r
      = (1 - (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT)
          * (r - 3 * Work.BoseBogFS.bogC1 v ρ μ / 2) ^ 2
        + (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
          * (r - 3 * Work.BoseBogFS.bogC2 v ρ μ / 2) ^ 2
        + ((1 - (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT)
              * (Work.BoseBogFS.bogC1 v ρ μ) ^ 2
            + (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
              * (Work.BoseBogFS.bogC2 v ρ μ) ^ 2) * Work.BoseBoxFock.tauC0 := by
  have hr1 : 2 * Work.BoseBogFS.bogC1 v ρ μ ≤ r := by linarith
  have h1 : (Work.BoseBogFS.bogC1 v ρ μ) ^ 2
        * Work.BoseBoxFock.tauProf (r / Work.BoseBogFS.bogC1 v ρ μ)
      = (r - 3 * Work.BoseBogFS.bogC1 v ρ μ / 2) ^ 2
        + Work.BoseBoxFock.tauC0 * (Work.BoseBogFS.bogC1 v ρ μ) ^ 2 :=
    Work.BoseBoxFock.tauChi_tail (c := Work.BoseBogFS.bogC1 v ρ μ) (r := r) hc1 hr1
  have h2 : (Work.BoseBogFS.bogC2 v ρ μ) ^ 2
        * Work.BoseBoxFock.tauProf (r / Work.BoseBogFS.bogC2 v ρ μ)
      = (r - 3 * Work.BoseBogFS.bogC2 v ρ μ / 2) ^ 2
        + Work.BoseBoxFock.tauC0 * (Work.BoseBogFS.bogC2 v ρ μ) ^ 2 :=
    Work.BoseBoxFock.tauChi_tail (c := Work.BoseBogFS.bogC2 v ρ μ) (r := r) hc2 hr
  have h1' : (1 - (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT)
        * (Work.BoseBogFS.bogC1 v ρ μ) ^ 2
        * Work.BoseBoxFock.tauProf (r / Work.BoseBogFS.bogC1 v ρ μ)
      = (1 - (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT)
        * ((r - 3 * Work.BoseBogFS.bogC1 v ρ μ / 2) ^ 2
          + Work.BoseBoxFock.tauC0 * (Work.BoseBogFS.bogC1 v ρ μ) ^ 2) := by
    rw [mul_assoc, h1]
  have h2' : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
        * (Work.BoseBogFS.bogC2 v ρ μ) ^ 2
        * Work.BoseBoxFock.tauProf (r / Work.BoseBogFS.bogC2 v ρ μ)
      = (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
        * ((r - 3 * Work.BoseBogFS.bogC2 v ρ μ / 2) ^ 2
          + Work.BoseBoxFock.tauC0 * (Work.BoseBogFS.bogC2 v ρ μ) ^ 2) := by
    rw [mul_assoc, h2]
  rw [tauScRad_eq (v := v) (ρ := ρ) (μ := μ) hP r, h1', h2']
  ring

theorem tauScRad_diff_le_quad {v : EuclideanSpace ℝ (Fin 3) → ℝ} {ρ μ : ℝ}
    (hP : 0 < ρ * _root_.BoseGases.a v)
    (heT0 : 0 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT)
    (heT1 : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT ≤ 1)
    (hc1 : 0 < Work.BoseBogFS.bogC1 v ρ μ) (hc2 : 0 < Work.BoseBogFS.bogC2 v ρ μ)
    (hc12 : Work.BoseBogFS.bogC1 v ρ μ ≤ Work.BoseBogFS.bogC2 v ρ μ)
    {x y : ℝ} (h2c2 : 2 * Work.BoseBogFS.bogC2 v ρ μ ≤ x) (hxy : x ≤ y) :
    Work.BoseBogFS.tauScRad v ρ μ y - Work.BoseBogFS.tauScRad v ρ μ x ≤ y ^ 2 - x ^ 2 := by
  have hxq := tauScRad_eq_quad (v := v) (ρ := ρ) (μ := μ) hP hc1 hc2 hc12 (r := x) h2c2
  have hyq := tauScRad_eq_quad (v := v) (ρ := ρ) (μ := μ) hP hc1 hc2 hc12 (r := y)
    (le_trans h2c2 hxy)
  -- the increment is `(y−x)(y+x) − 3κ(y−x)`, `κ = (1−ε_T)c₁ + ε_Tc₂ ≥ 0`
  have key : Work.BoseBogFS.tauScRad v ρ μ y - Work.BoseBogFS.tauScRad v ρ μ x
      = (y - x) * (y + x)
        - 3 * ((1 - (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT)
              * Work.BoseBogFS.bogC1 v ρ μ
            + (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
              * Work.BoseBogFS.bogC2 v ρ μ) * (y - x) := by
    rw [hxq, hyq]
    ring
  have hyx : 0 ≤ y - x := by linarith
  have hk1 : 0 ≤ (1 - (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT)
        * Work.BoseBogFS.bogC1 v ρ μ
      + (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
        * Work.BoseBogFS.bogC2 v ρ μ :=
    add_nonneg (mul_nonneg (by linarith) hc1.le) (mul_nonneg heT0 hc2.le)
  have hk : 0 ≤ 3 * ((1 - (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT)
          * Work.BoseBogFS.bogC1 v ρ μ
        + (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
          * Work.BoseBogFS.bogC2 v ρ μ) * (y - x) :=
    mul_nonneg (mul_nonneg (by norm_num) hk1) hyx
  rw [key]
  calc (y - x) * (y + x)
        - 3 * ((1 - (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT)
              * Work.BoseBogFS.bogC1 v ρ μ
            + (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
              * Work.BoseBogFS.bogC2 v ρ μ) * (y - x)
      ≤ (y - x) * (y + x) := by linarith
    _ = y ^ 2 - x ^ 2 := by ring

end Work.BoseBogFS
