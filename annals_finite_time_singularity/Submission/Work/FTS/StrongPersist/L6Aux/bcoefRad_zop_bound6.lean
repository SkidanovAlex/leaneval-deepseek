/-
# The weighted `Zop`-iterates of the radial profile `2z²/(1+z)³`, up to order six

`Work.Spaces.Zop u = (z ↦ z·u'(z))` is the radial derivation `D_z`, and
`bcoefRad z = 2z²/(1+z)³` is the radial half of the projector coefficient
(`Submission/Work/FTS/StrongPersist/L3Aux/bcoefPrep.lean`).

The level-three statement `|(Zop^[j] bcoefRad) z · w z| ≤ 120/(1+z)` for `j ≤ 3`,
`z ≥ 0` (`Work.FTS.StrongPersist.L3Aux.bcoefRad_zop_bound`, in `bcoefRadBound.lean`)
is proved there by explicit closed forms.  Here we extend the same computation three
more steps, to `j ≤ 6`, with the constant `40320`.

ROUTE.  The closed forms of the `Zop`-iterates are

  `(Zop^[j] bcoefRad) z = 2z²P_j(z)/(1+z)^(3+j)`  (`z ≠ -1`),

with `P_0 = 1`, `P_1 = 2-z`, `P_2 = z²-7z+4`, `P_3 = -z³+18z²-33z+8` (the three
already available in `bcoefRadBound.lean`), and, from the recursion
`P_{j+1} = (1+z)(2P_j + zP_j') - (3+j)zP_j`,

  `P_4 = z⁴-41z³+171z²-131z+16`,
  `P_5 = -z⁵+88z⁴-718z³+1208z²-473z+32`,
  `P_6 = z⁶-183z⁵+2682z⁴-8422z³+7197z²-1611z+64`.

The three new closed forms (`Zop_four_eq`, `Zop_five_eq`, `Zop_six_eq`) are obtained
from the previous one by `Filter.EventuallyEq.deriv_eq` together with the explicit
derivatives `radZop_deriv4/5/6` of the rational functions
`y ↦ 2y²P_j(y)/(1+y)^(3+j)` on `(-1,∞)`.

Multiplying by the weight `w z = (1+z)²/z²` cancels `z²` and one power of `1+z`
(for `z > 0`), leaving `2P_j(z)/(1+z)^(j+1)`; a crude polynomial bound
`|P_j(z)| ≤ (Σ|c_k|)(1+z)^j` on `z ≥ 0` then gives `|…| ≤ 2(Σ|c_k|)/(1+z)`.  The
coefficient sums of `P_4, P_5, P_6` are `360, 2520, 20160`, so `40320` is a valid
constant for `j = 4, 5, 6`; for `j ≤ 3` we simply take the `max` with the constant of
the level-three theorem.  (The sharp constant is `2^{j+1} = 128` at level six, but the
crude bound is all that is needed.)
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Order.Lattice
import Submission.Work.FTS.StrongPersist.L3Aux.bcoefRadBound
import Submission.Work.FTS.StrongPersist.L6Aux.radZop_deriv4
import Submission.Work.FTS.StrongPersist.L6Aux.radZop_deriv5
import Submission.Work.FTS.StrongPersist.L6Aux.radZop_deriv6
import Submission.Work.FTS.StrongPersist.L6Aux.abs_le_quartic
import Submission.Work.FTS.StrongPersist.L6Aux.abs_le_quintic
import Submission.Work.FTS.StrongPersist.L6Aux.abs_le_sextic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.L6Aux

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

/-! ## The `Zop`-iterates of the radial profile

The level-three closed form is `Work.FTS.StrongPersist.L3Aux.Zop_three_eq` of
`bcoefRadBound.lean`; the next three levels are derived here from the explicit
derivatives `radZop_deriv4/5/6` of the sibling modules of this directory. -/

/-- The fourth `Zop`-iterate of `bcoefRad`, sixth-degree-quartic closed form. -/
lemma Zop_four_eq {z : ℝ} (hz : -1 < z) :
    Work.Spaces.Zop^[4] Work.FTS.StrongPersist.L3Aux.bcoefRad z
      = 2 * z ^ 2 * (z ^ 4 - 41 * z ^ 3 + 171 * z ^ 2 - 131 * z + 16) / (1 + z) ^ 7 := by
  have hzne : z ≠ -1 := by linarith
  have hev : Work.Spaces.Zop^[3] Work.FTS.StrongPersist.L3Aux.bcoefRad =ᶠ[𝓝 z]
      (fun y : ℝ => 2 * y ^ 2 * (-y ^ 3 + 18 * y ^ 2 - 33 * y + 8) / (1 + y) ^ 6) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with y hy
    exact Work.FTS.StrongPersist.L3Aux.Zop_three_eq hy
  change Work.Spaces.Zop (Work.Spaces.Zop^[3] Work.FTS.StrongPersist.L3Aux.bcoefRad) z
    = 2 * z ^ 2 * (z ^ 4 - 41 * z ^ 3 + 171 * z ^ 2 - 131 * z + 16) / (1 + z) ^ 7
  show z * deriv (Work.Spaces.Zop^[3] Work.FTS.StrongPersist.L3Aux.bcoefRad) z
    = 2 * z ^ 2 * (z ^ 4 - 41 * z ^ 3 + 171 * z ^ 2 - 131 * z + 16) / (1 + z) ^ 7
  rw [hev.deriv_eq, (radZop_deriv4 z hzne).deriv]
  field_simp

/-- The fifth `Zop`-iterate of `bcoefRad`. -/
lemma Zop_five_eq {z : ℝ} (hz : -1 < z) :
    Work.Spaces.Zop^[5] Work.FTS.StrongPersist.L3Aux.bcoefRad z
      = 2 * z ^ 2 * (-z ^ 5 + 88 * z ^ 4 - 718 * z ^ 3 + 1208 * z ^ 2 - 473 * z + 32)
          / (1 + z) ^ 8 := by
  have hzne : z ≠ -1 := by linarith
  have hev : Work.Spaces.Zop^[4] Work.FTS.StrongPersist.L3Aux.bcoefRad =ᶠ[𝓝 z]
      (fun y : ℝ => 2 * y ^ 2 * (y ^ 4 - 41 * y ^ 3 + 171 * y ^ 2 - 131 * y + 16) / (1 + y) ^ 7) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with y hy
    exact Zop_four_eq hy
  change Work.Spaces.Zop (Work.Spaces.Zop^[4] Work.FTS.StrongPersist.L3Aux.bcoefRad) z
    = 2 * z ^ 2 * (-z ^ 5 + 88 * z ^ 4 - 718 * z ^ 3 + 1208 * z ^ 2 - 473 * z + 32) / (1 + z) ^ 8
  show z * deriv (Work.Spaces.Zop^[4] Work.FTS.StrongPersist.L3Aux.bcoefRad) z
    = 2 * z ^ 2 * (-z ^ 5 + 88 * z ^ 4 - 718 * z ^ 3 + 1208 * z ^ 2 - 473 * z + 32) / (1 + z) ^ 8
  rw [hev.deriv_eq, (radZop_deriv5 z hzne).deriv]
  field_simp

/-- The sixth `Zop`-iterate of `bcoefRad`. -/
lemma Zop_six_eq {z : ℝ} (hz : -1 < z) :
    Work.Spaces.Zop^[6] Work.FTS.StrongPersist.L3Aux.bcoefRad z
      = 2 * z ^ 2 * (z ^ 6 - 183 * z ^ 5 + 2682 * z ^ 4 - 8422 * z ^ 3 + 7197 * z ^ 2
          - 1611 * z + 64) / (1 + z) ^ 9 := by
  have hzne : z ≠ -1 := by linarith
  have hev : Work.Spaces.Zop^[5] Work.FTS.StrongPersist.L3Aux.bcoefRad =ᶠ[𝓝 z]
      (fun y : ℝ => 2 * y ^ 2 * (-y ^ 5 + 88 * y ^ 4 - 718 * y ^ 3 + 1208 * y ^ 2 - 473 * y + 32)
        / (1 + y) ^ 8) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with y hy
    exact Zop_five_eq hy
  change Work.Spaces.Zop (Work.Spaces.Zop^[5] Work.FTS.StrongPersist.L3Aux.bcoefRad) z
    = 2 * z ^ 2 * (z ^ 6 - 183 * z ^ 5 + 2682 * z ^ 4 - 8422 * z ^ 3 + 7197 * z ^ 2
        - 1611 * z + 64) / (1 + z) ^ 9
  show z * deriv (Work.Spaces.Zop^[5] Work.FTS.StrongPersist.L3Aux.bcoefRad) z
    = 2 * z ^ 2 * (z ^ 6 - 183 * z ^ 5 + 2682 * z ^ 4 - 8422 * z ^ 3 + 7197 * z ^ 2
        - 1611 * z + 64) / (1 + z) ^ 9
  rw [hev.deriv_eq, (radZop_deriv6 z hzne).deriv]
  field_simp

/-! ## The weighted bound -/

/-- Given the closed form `Zop^[j] bcoefRad z = 2z²P(z)/(1+z)^(3+j)` at a point
`z > 0`, together with `|P z| ≤ C(1+z)^j`, the weighted iterate at `z` is at most
`2C/(1+z)`. -/
lemma weighted_le_of_form (j : ℕ) (C : ℝ) (P : ℝ → ℝ) {z : ℝ} (hz : 0 < z)
    (hform : Work.Spaces.Zop^[j] Work.FTS.StrongPersist.L3Aux.bcoefRad z
      = 2 * z ^ 2 * P z / (1 + z) ^ (3 + j))
    (hP : |P z| ≤ C * (1 + z) ^ j) :
    |Work.Spaces.Zop^[j] Work.FTS.StrongPersist.L3Aux.bcoefRad z * Work.Spaces.w z|
      ≤ 2 * C / (1 + z) := by
  have h1z : (0 : ℝ) < 1 + z := by linarith
  have hw : Work.Spaces.w z = (1 + z) ^ 2 / z ^ 2 := rfl
  rw [hform, hw]
  have hAB : 2 * z ^ 2 * P z / (1 + z) ^ (3 + j) * ((1 + z) ^ 2 / z ^ 2)
      = 2 * P z / (1 + z) ^ (j + 1) := by
    field_simp
    ring
  rw [hAB]
  rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
    abs_of_pos (pow_pos h1z (j + 1))]
  rw [div_le_iff₀ (pow_pos h1z (j + 1))]
  have h2 : 2 * |P z| ≤ 2 * C * (1 + z) ^ j := by
    have := mul_le_mul_of_nonneg_left hP (by norm_num : (0 : ℝ) ≤ 2)
    linarith
  calc 2 * |P z| ≤ 2 * C * (1 + z) ^ j := h2
    _ = 2 * C / (1 + z) * (1 + z) ^ (j + 1) := by
        rw [pow_succ]
        field_simp

/-- `|P_4| ≤ 360(1+z)^4` on `z ≥ 0`; `360` is the sum of the absolute values of the
coefficients of `P_4 = z⁴-41z³+171z²-131z+16`. -/
lemma quart_bound {z : ℝ} (hz : 0 ≤ z) :
    |z ^ 4 - 41 * z ^ 3 + 171 * z ^ 2 - 131 * z + 16| ≤ 360 * (1 + z) ^ 4 := by
  have h := abs_le_quartic z 1 (-41) 171 (-131) 16 hz
  rw [show (1 : ℝ) * z ^ 4 + (-41) * z ^ 3 + 171 * z ^ 2 + (-131) * z + 16
        = z ^ 4 - 41 * z ^ 3 + 171 * z ^ 2 - 131 * z + 16 by ring,
      show |(1 : ℝ)| + |(-41 : ℝ)| + |(171 : ℝ)| + |(-131 : ℝ)| + |(16 : ℝ)| = 360 by norm_num]
    at h
  exact h

/-- `|P_5| ≤ 2520(1+z)^5` on `z ≥ 0`, the sum of the absolute values of the
coefficients of `P_5 = -z⁵+88z⁴-718z³+1208z²-473z+32`. -/
lemma quint_bound {z : ℝ} (hz : 0 ≤ z) :
    |-z ^ 5 + 88 * z ^ 4 - 718 * z ^ 3 + 1208 * z ^ 2 - 473 * z + 32|
      ≤ 2520 * (1 + z) ^ 5 := by
  have h := abs_le_quintic z (-1) 88 (-718) 1208 (-473) 32 hz
  rw [show (-1 : ℝ) * z ^ 5 + 88 * z ^ 4 + (-718) * z ^ 3 + 1208 * z ^ 2 + (-473) * z + 32
        = -z ^ 5 + 88 * z ^ 4 - 718 * z ^ 3 + 1208 * z ^ 2 - 473 * z + 32 by ring,
      show |(-1 : ℝ)| + |(88 : ℝ)| + |(-718 : ℝ)| + |(1208 : ℝ)| + |(-473 : ℝ)| + |(32 : ℝ)|
        = 2520 by norm_num] at h
  exact h

/-- `|P_6| ≤ 20160(1+z)^6` on `z ≥ 0`, the sum of the absolute values of the
coefficients of `P_6 = z⁶-183z⁵+2682z⁴-8422z³+7197z²-1611z+64`. -/
lemma sext_bound {z : ℝ} (hz : 0 ≤ z) :
    |z ^ 6 - 183 * z ^ 5 + 2682 * z ^ 4 - 8422 * z ^ 3 + 7197 * z ^ 2 - 1611 * z + 64|
      ≤ 20160 * (1 + z) ^ 6 := by
  have h := abs_le_sextic z 1 (-183) 2682 (-8422) 7197 (-1611) 64 hz
  rw [show (1 : ℝ) * z ^ 6 + (-183) * z ^ 5 + 2682 * z ^ 4 + (-8422) * z ^ 3 + 7197 * z ^ 2
        + (-1611) * z + 64
        = z ^ 6 - 183 * z ^ 5 + 2682 * z ^ 4 - 8422 * z ^ 3 + 7197 * z ^ 2 - 1611 * z + 64 by ring,
      show |(1 : ℝ)| + |(-183 : ℝ)| + |(2682 : ℝ)| + |(-8422 : ℝ)| + |(7197 : ℝ)|
        + |(-1611 : ℝ)| + |(64 : ℝ)| = 20160 by norm_num] at h
  exact h

-- The weighted `Zop`-iterates of the radial profile `bcoefRad z = 2z²/(1+z)³` are bounded by
-- `K/(1+z)` uniformly for `j ≤ 6`, `z ≥ 0`.  (The `j ≤ 3` case is `L3Aux.bcoefRad_zop_bound`,
-- proved in the imported `bcoefRadBound.lean` by explicit closed forms; the same route works.)
-- Route: `(Zop^[j] bcoefRad) z = 2z²P_j(z)/(1+z)^(3+j)` with `P_0 = 1`, `P_1 = 2-z`,
-- `P_2 = z²-7z+4`, `P_3 = -z³+18z²-33z+8`, `P_4 = z⁴-41z³+171z²-131z+16`,
-- `P_5 = -z⁵+88z⁴-718z³+1208z²-473z+32`, `P_6 = z⁶-183z⁵+2682z⁴-8422z³+7197z²-1611z+64`
-- (recursion `P_{j+1} = (1+z)(2P_j + zP_j') - (3+j)zP_j`), so that multiplying by
-- `w z = (1+z)²/z²` leaves `2P_j(z)/(1+z)^(j+1)`; a `j`-th degree polynomial bound of `P_j`
-- on `z ≥ 0` gives `K` (explicitly `K = 40320 = 2·∑|coeffs of P_6|` works; the sharp constant
-- is `2^(j+1)`, i.e. `128`).
theorem bcoefRad_zop_bound6 : ∃ K : ℝ, 0 < K ∧ ∀ (j : ℕ), j ≤ 6 → ∀ z ∈ Set.Ici (0 : ℝ),
    |(Work.Spaces.Zop^[j] Work.FTS.StrongPersist.L3Aux.bcoefRad) z * Work.Spaces.w z|
      ≤ K / (1 + z) := by
  obtain ⟨K0, hK0pos, hK0⟩ := Work.FTS.StrongPersist.L3Aux.bcoefRad_zop_bound
  refine ⟨max 40320 K0, lt_max_of_lt_left (by norm_num), ?_⟩
  intro j hj z hz
  have hz0 : (0 : ℝ) ≤ z := hz
  have h1z : (0 : ℝ) < 1 + z := by linarith
  by_cases hj3 : j ≤ 3
  · exact le_trans (hK0 j hj3 z hz)
      (div_le_div_of_nonneg_right (le_max_right 40320 K0) (le_of_lt h1z))
  · -- `3 < j ≤ 6`
    have hj4 : 3 < j := by omega
    have hw0 : Work.Spaces.w 0 = 0 := by rw [Work.Spaces.w]; norm_num
    rcases eq_or_lt_of_le hz0 with hz' | hzpos
    · rw [← hz', hw0, mul_zero, abs_zero, add_zero, div_one]
      exact le_of_lt (lt_max_of_lt_left (by norm_num : (0 : ℝ) < 40320))
    · have hzIoi : z ∈ Set.Ioi (-1 : ℝ) := Set.mem_Ioi.mpr (by linarith)
      have hj46 : j = 4 ∨ j = 5 ∨ j = 6 := by omega
      rcases hj46 with h4 | h5 | h6
      · subst h4
        have h := weighted_le_of_form 4 360
            (fun t : ℝ => t ^ 4 - 41 * t ^ 3 + 171 * t ^ 2 - 131 * t + 16)
            hzpos (Zop_four_eq hzIoi) (quart_bound hz0)
        calc |(Work.Spaces.Zop^[4] Work.FTS.StrongPersist.L3Aux.bcoefRad) z * Work.Spaces.w z|
            ≤ 2 * 360 / (1 + z) := h
          _ = 720 / (1 + z) := by norm_num
          _ ≤ max 40320 K0 / (1 + z) :=
              div_le_div_of_nonneg_right (by norm_num) (le_of_lt h1z)
      · subst h5
        have h := weighted_le_of_form 5 2520
            (fun t : ℝ => -t ^ 5 + 88 * t ^ 4 - 718 * t ^ 3 + 1208 * t ^ 2 - 473 * t + 32)
            hzpos (Zop_five_eq hzIoi) (quint_bound hz0)
        calc |(Work.Spaces.Zop^[5] Work.FTS.StrongPersist.L3Aux.bcoefRad) z * Work.Spaces.w z|
            ≤ 2 * 2520 / (1 + z) := h
          _ = 5040 / (1 + z) := by norm_num
          _ ≤ max 40320 K0 / (1 + z) :=
              div_le_div_of_nonneg_right (by norm_num) (le_of_lt h1z)
      · subst h6
        have h := weighted_le_of_form 6 20160
            (fun t : ℝ => t ^ 6 - 183 * t ^ 5 + 2682 * t ^ 4 - 8422 * t ^ 3 + 7197 * t ^ 2
              - 1611 * t + 64)
            hzpos (Zop_six_eq hzIoi) (sext_bound hz0)
        calc |(Work.Spaces.Zop^[6] Work.FTS.StrongPersist.L3Aux.bcoefRad) z * Work.Spaces.w z|
            ≤ 2 * 20160 / (1 + z) := h
          _ = 40320 / (1 + z) := by norm_num
          _ ≤ max 40320 K0 / (1 + z) :=
              div_le_div_of_nonneg_right (le_max_left 40320 K0) (le_of_lt h1z)

end

end Work.FTS.StrongPersist.L6Aux
