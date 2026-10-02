import Mathlib
import Submission.Work.Escape.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The Böttcher ratio of the holomorphic unicritical family `z ↦ z^d + c`

Let `Tpoly d c z = z^d + c` be the holomorphic unicritical polynomial of degree `d`.  For the
Böttcher coordinate of `Tpoly d c` at infinity one needs to know that the ratio

`(Tpoly d c) w / w^d`

is close to `1` as soon as `w` is large: indeed the ratio differs from `1` exactly by `c / w^d`,
whose modulus is `‖c‖ / ‖w‖^d`, and this tends to `0` as `‖w‖ → ∞` (for `d ≥ 1`).  Consequently
the ratio is small *uniformly along the orbit* of every point `z` whose `k`-th iterate is large,
which is the form in which the estimate is used:

`poly_ratio_tendsto` produces a single radius `ρ` such that for every `k` and every `z`, if the
`k`-th iterate of `z` lies outside the disk of radius `ρ`, then the ratio at that iterate is
within `ε` of `1`.

The radius can be taken explicitly as `ρ = ‖c‖ / ε + 1`; the factor `+ 1` makes `ρ ≥ 1`, so
that `‖w‖^d ≥ ‖w‖` (here `d ≥ 1` is used) and the iterate `w` is automatically nonzero.
-/

namespace Work.Escape

open Function

/-- Exact value of the ratio: for `w ≠ 0`, `(Tpoly d c w) / w^d - 1 = c / w^d`. -/
theorem Tpoly_ratio_sub_one (d : ℕ) (c w : ℂ) (hw : w ≠ 0) :
    (Tpoly d c w) / w ^ d - 1 = c / w ^ d := by
  have hwd : w ^ d ≠ 0 := pow_ne_zero d hw
  rw [Tpoly]
  field_simp
  ring

/-- The modulus of the ratio: `‖(Tpoly d c w) / w^d - 1‖ = ‖c‖ / ‖w‖^d`. -/
theorem norm_Tpoly_ratio_sub_one (d : ℕ) (c w : ℂ) (hw : w ≠ 0) :
    ‖(Tpoly d c w) / w ^ d - 1‖ = ‖c‖ / ‖w‖ ^ d := by
  rw [Tpoly_ratio_sub_one d c w hw, norm_div, norm_pow]

theorem poly_ratio_tendsto (d : ℕ) (c : ℂ) (hd : 1 ≤ d) (ε : ℝ) (hε : 0 < ε) :
    ∃ ρ : ℝ, ∀ k : ℕ, ∀ z : ℂ, ρ ≤ ‖(Tpoly d c)^[k] z‖ →
      ‖(Tpoly d c)^[k + 1] z / ((Tpoly d c)^[k] z) ^ d - 1‖ ≤ ε := by
  -- The explicit radius `ρ = ‖c‖ / ε + 1 ≥ 1` forces `‖c‖ / ‖w‖^d ≤ ‖c‖ / ‖w‖ ≤ ε`.
  refine ⟨‖c‖ / ε + 1, ?_⟩
  intro k z hz
  -- Unfold one iterate: `(Tpoly d c)^[k+1] z = ((Tpoly d c)^[k] z)^d + c`.
  have hiter : (Tpoly d c)^[k + 1] z = ((Tpoly d c)^[k] z) ^ d + c := by
    rw [Function.iterate_succ_apply']; rfl
  rw [hiter]
  set w := (Tpoly d c)^[k] z with hw
  have hρ1 : (1 : ℝ) ≤ ‖c‖ / ε + 1 := by
    have : 0 ≤ ‖c‖ / ε := div_nonneg (norm_nonneg c) hε.le
    linarith
  have hw1 : (1 : ℝ) ≤ ‖w‖ := le_trans hρ1 hz
  have hw0 : w ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hw1
    linarith
  change ‖(Tpoly d c w) / w ^ d - 1‖ ≤ ε
  rw [norm_Tpoly_ratio_sub_one d c w hw0]
  -- `‖w‖ ≤ ‖w‖^d` because `‖w‖ ≥ 1` and `d ≥ 1`, hence `‖c‖/‖w‖^d ≤ ‖c‖/‖w‖`.
  have hnorm_pos : 0 < ‖w‖ := lt_of_lt_of_le zero_lt_one hw1
  have hwd_ge : ‖w‖ ≤ ‖w‖ ^ d := le_self_pow₀ hw1 (by omega)
  have hstep1 : ‖c‖ / ‖w‖ ^ d ≤ ‖c‖ / ‖w‖ :=
    div_le_div_of_nonneg_left (norm_nonneg c) hnorm_pos hwd_ge
  -- `‖c‖/‖w‖ ≤ ‖c‖/ρ` because `‖w‖ ≥ ρ`.
  have hstep2 : ‖c‖ / ‖w‖ ≤ ‖c‖ / (‖c‖ / ε + 1) :=
    div_le_div_of_nonneg_left (norm_nonneg c) (by linarith) hz
  -- `‖c‖/ρ ≤ ε` by the choice of `ρ`.
  have hstep3 : ‖c‖ / (‖c‖ / ε + 1) ≤ ε := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < ‖c‖ / ε + 1)]
    have h : ε * (‖c‖ / ε) = ‖c‖ := by field_simp
    nlinarith [norm_nonneg c]
  linarith

end Work.Escape
