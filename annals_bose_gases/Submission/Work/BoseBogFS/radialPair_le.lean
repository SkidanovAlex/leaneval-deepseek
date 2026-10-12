import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBogFS.cellSplitDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBogFS

/-- The purely radial part of the two-point oscillation of `gFun`:

if `r, r' ∈ [r_lo, r_hi]` with `r_lo > 0`, and `|b|, |b'| ≤ V`, `|b - b'| ≤ o`, then

`-b²/(2r²) + b'²/(2r'²) ≤ o·V/r_lo² + V²·(1/(2r_lo²) - 1/(2r_hi²))`.

The proof splits the left-hand side at the intermediate point `b'`:

* `b'²/(2r'²) - b'²/(2r²) ≤ V²·(1/(2r_lo²) - 1/(2r_hi²))` — the extremal case of
  a *single* value `b'² ≤ V²` against two radii, which is why we may discard the
  `r'²/(2r_lo²)` term entirely (if `r' ≤ r` both factors are monotone, if `r ≥ r'`
  the difference is negative while the right-hand side is not);
* `b'²/(2r²) - b²/(2r²) = (b' - b)(b' + b)/(2r²) ≤ o·(2V)/(2r²) ≤ o·V/r_lo²`,
  using `|b' + b| ≤ |b'| + |b| ≤ 2V` and `|b' - b| = |b - b'| ≤ o`. -/
theorem radialPair_le {b b' o V r_lo r_hi r r' : ℝ}
    (hr0 : 0 < r_lo) (hrl : r_lo ≤ r) (hrh : r ≤ r_hi) (hr'l : r_lo ≤ r') (hr'h : r' ≤ r_hi)
    (hb : |b| ≤ V) (hb' : |b'| ≤ V) (ho : |b - b'| ≤ o) :
    -(b ^ 2 / (2 * r ^ 2)) + b' ^ 2 / (2 * r' ^ 2)
      ≤ o * V / r_lo ^ 2 + V ^ 2 * (1 / (2 * r_lo ^ 2) - 1 / (2 * r_hi ^ 2)) := by
  have hV : 0 ≤ V := le_trans (abs_nonneg b) hb
  have ho0 : 0 ≤ o := le_trans (abs_nonneg (b - b')) ho
  have hr : 0 < r := lt_of_lt_of_le hr0 hrl
  have hr' : 0 < r' := lt_of_lt_of_le hr0 hr'l
  have hlh : r_lo ≤ r_hi := le_trans hrl hrh
  have hbV : b ^ 2 ≤ V ^ 2 := sq_le_sq' (abs_le.mp hb).1 (abs_le.mp hb).2
  have hb'V : b' ^ 2 ≤ V ^ 2 := sq_le_sq' (abs_le.mp hb').1 (abs_le.mp hb').2
  -- Part A : the two `r`-dependent halves at the *same* `b'`.
  have hA : b' ^ 2 / (2 * r' ^ 2) - b' ^ 2 / (2 * r ^ 2)
      ≤ V ^ 2 * (1 / (2 * r_lo ^ 2) - 1 / (2 * r_hi ^ 2)) := by
    rcases le_or_gt r' r with hle | hlt
    · -- `r' ≤ r`: both factors of `1/(2r'²) - 1/(2r²)` are monotone
      have hsq : r' ^ 2 ≤ r ^ 2 := sq_le_sq' (by linarith) hle
      have hD0 : 0 ≤ 1 / (2 * r' ^ 2) - 1 / (2 * r ^ 2) := by
        have h1 : 1 / (2 * r ^ 2) ≤ 1 / (2 * r' ^ 2) :=
          div_le_div_of_nonneg_left zero_le_one (by positivity) (by linarith)
        linarith
      have hDE : 1 / (2 * r' ^ 2) - 1 / (2 * r ^ 2)
          ≤ 1 / (2 * r_lo ^ 2) - 1 / (2 * r_hi ^ 2) := by
        have hm1 : r_lo ^ 2 ≤ r' ^ 2 := sq_le_sq' (by linarith) hr'l
        have hm2 : r ^ 2 ≤ r_hi ^ 2 := sq_le_sq' (by linarith) hrh
        have h1 : 1 / (2 * r' ^ 2) ≤ 1 / (2 * r_lo ^ 2) :=
          div_le_div_of_nonneg_left zero_le_one (by positivity) (by linarith)
        have h2 : 1 / (2 * r_hi ^ 2) ≤ 1 / (2 * r ^ 2) :=
          div_le_div_of_nonneg_left zero_le_one (by positivity) (by linarith)
        linarith
      calc b' ^ 2 / (2 * r' ^ 2) - b' ^ 2 / (2 * r ^ 2)
          = b' ^ 2 * (1 / (2 * r' ^ 2) - 1 / (2 * r ^ 2)) := by ring
        _ ≤ V ^ 2 * (1 / (2 * r' ^ 2) - 1 / (2 * r ^ 2)) :=
            mul_le_mul_of_nonneg_right hb'V hD0
        _ ≤ V ^ 2 * (1 / (2 * r_lo ^ 2) - 1 / (2 * r_hi ^ 2)) :=
            mul_le_mul_of_nonneg_left hDE (sq_nonneg V)
    · -- `r < r'`: the radial difference is negative, the right-hand side is not
      have hsq : r ^ 2 ≤ r' ^ 2 := sq_le_sq' (by linarith) (le_of_lt hlt)
      have hD0 : 1 / (2 * r' ^ 2) - 1 / (2 * r ^ 2) ≤ 0 := by
        have h1 : 1 / (2 * r' ^ 2) ≤ 1 / (2 * r ^ 2) :=
          div_le_div_of_nonneg_left zero_le_one (by positivity) (by linarith)
        linarith
      have hE0 : 0 ≤ 1 / (2 * r_lo ^ 2) - 1 / (2 * r_hi ^ 2) := by
        have hm : r_lo ^ 2 ≤ r_hi ^ 2 := sq_le_sq' (by linarith) hlh
        have h1 : 1 / (2 * r_hi ^ 2) ≤ 1 / (2 * r_lo ^ 2) :=
          div_le_div_of_nonneg_left zero_le_one (by positivity) (by linarith)
        linarith
      have h1 : b' ^ 2 * (1 / (2 * r' ^ 2) - 1 / (2 * r ^ 2)) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (sq_nonneg b') hD0
      have h2 : 0 ≤ V ^ 2 * (1 / (2 * r_lo ^ 2) - 1 / (2 * r_hi ^ 2)) :=
        mul_nonneg (sq_nonneg V) hE0
      have hfac : b' ^ 2 / (2 * r' ^ 2) - b' ^ 2 / (2 * r ^ 2)
          = b' ^ 2 * (1 / (2 * r' ^ 2) - 1 / (2 * r ^ 2)) := by ring
      linarith [hfac, h1, h2]
  -- Part B : the `b`-difference at the *same* `r`.
  have hB : b' ^ 2 / (2 * r ^ 2) - b ^ 2 / (2 * r ^ 2) ≤ o * V / r_lo ^ 2 := by
    have hnum : (b' - b) * (b' + b) ≤ o * (2 * V) := by
      have hab : |b' - b| ≤ o := by rw [abs_sub_comm]; exact ho
      have hsum : |b' + b| ≤ 2 * V := by
        have h := abs_add_le b' b
        have h2 : |b'| + |b| ≤ V + V := add_le_add hb' hb
        linarith
      calc (b' - b) * (b' + b) ≤ |(b' - b) * (b' + b)| := le_abs_self _
        _ = |b' - b| * |b' + b| := abs_mul _ _
        _ ≤ o * (2 * V) := mul_le_mul hab hsum (abs_nonneg _) ho0
    have hnum' : b' ^ 2 - b ^ 2 ≤ o * (2 * V) := by nlinarith [hnum]
    have hsq : r_lo ^ 2 ≤ r ^ 2 := sq_le_sq' (by linarith) hrl
    rw [div_sub_div_same]
    calc (b' ^ 2 - b ^ 2) / (2 * r ^ 2)
        ≤ (o * (2 * V)) / (2 * r ^ 2) := div_le_div_of_nonneg_right hnum' (by positivity)
      _ = o * V / r ^ 2 := by ring
      _ ≤ o * V / r_lo ^ 2 :=
          div_le_div_of_nonneg_left (mul_nonneg ho0 hV) (by positivity) (by linarith)
  -- assemble: split the left-hand side at the intermediate point `b'`
  have hrw : -(b ^ 2 / (2 * r ^ 2)) + b' ^ 2 / (2 * r' ^ 2)
      = (b' ^ 2 / (2 * r' ^ 2) - b' ^ 2 / (2 * r ^ 2))
        + (b' ^ 2 / (2 * r ^ 2) - b ^ 2 / (2 * r ^ 2)) := by ring
  linarith [hA, hB, hrw]

end Work.BoseBogFS
