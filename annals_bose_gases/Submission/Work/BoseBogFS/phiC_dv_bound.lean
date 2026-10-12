import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBogFS.phiC_defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBogFS

set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

/-- **Pointwise box bound for the `v`-derivative of `phiC`.**  On the box
`u ∈ [u_lo,u_hi]`, `v ∈ [v_lo,v_hi]`, `r ∈ [r_lo,r_hi]` with `0 < u_lo`, `u_lo² + 2u_lo v_lo > 0`
and `u_hi ≤ r_lo²`, the `v`-derivative of the clean bracket is bounded by the box data

  `M(2(r_hi² − u_lo) + 3M)/(r_lo² S_lo) + M²(1 + u_hi/D_lo)/S_lo²`,

`M = max |v_lo| |v_hi|`, `D_lo = √(u_lo²+2u_lo v_lo)`, `S_lo = u_lo + v_lo + D_lo`.

Route: write the derivative as `v(2r² − S)/(S r²) − v²(1 + u/D)/S²`.  The **second** piece is
`≤ M²(1+u_hi/D_lo)/S_lo²` because `|v| ≤ M`, `u ≤ u_hi`, `D ≥ D_lo`, `S ≥ S_lo`.  For the
**first** piece use `2r² − S = 2(r²−u) + (u−D) − v`, `0 ≤ r²−u ≤ r_hi²−u_lo`, `|v| ≤ M`, and the
key algebraic fact `|u − D| ≤ 2|v|` (for `u > 0`, `u+2v > 0`: if `v ≥ 0` then `D ≥ u` and
`D − u = 2uv/(D+u) ≤ v`; if `v ≤ 0` then `D ≤ u` and `u − D = 2u|v|/(u+D) ≤ 2|v|`), giving
`|2r²−S| ≤ 2(r_hi²−u_lo) + 3M`.  Combined with `|v| ≤ M`, `S ≥ S_lo > 0`, `r ≥ r_lo > 0` this
gives the first term.  (Note the constant is `3M`, not `2M`: `|u−D| ≤ |v|` is false for `v < 0`.)
`r_hi² − u_lo ≥ 0` holds under `u_hi ≤ r_lo² ≤ r_hi²`, so the plain difference is used. -/
theorem phiC_dv_bound {u_lo u_hi v_lo v_hi r_lo r_hi u v r : ℝ}
    (hul : 0 < u_lo) (hulh : u_lo ≤ u_hi) (hvlh : v_lo ≤ v_hi)
    (hrl : 0 < r_lo) (hrlh : r_lo ≤ r_hi)
    (hW : 0 < u_lo ^ 2 + 2 * u_lo * v_lo)
    (hur : u_hi ≤ r_lo ^ 2)
    (hu : u_lo ≤ u) (hu2 : u ≤ u_hi) (hv : v_lo ≤ v) (hv2 : v ≤ v_hi)
    (hr : r_lo ≤ r) (hr2 : r ≤ r_hi) :
    |2 * v / (u + v + Real.sqrt (u ^ 2 + 2 * u * v))
        - v ^ 2 * (1 + u / Real.sqrt (u ^ 2 + 2 * u * v))
            / (u + v + Real.sqrt (u ^ 2 + 2 * u * v)) ^ 2
        - v / r ^ 2|
      ≤ (max |v_lo| |v_hi|) * (2 * (r_hi ^ 2 - u_lo) + 3 * (max |v_lo| |v_hi|))
            / (r_lo ^ 2 * (u_lo + v_lo + Real.sqrt (u_lo ^ 2 + 2 * u_lo * v_lo)))
        + (max |v_lo| |v_hi|) ^ 2
            * (1 + u_hi / Real.sqrt (u_lo ^ 2 + 2 * u_lo * v_lo))
            / (u_lo + v_lo + Real.sqrt (u_lo ^ 2 + 2 * u_lo * v_lo)) ^ 2 := by
  set M := max |v_lo| |v_hi| with hM
  set D := Real.sqrt (u ^ 2 + 2 * u * v) with hD
  set Dlo := Real.sqrt (u_lo ^ 2 + 2 * u_lo * v_lo) with hDlo
  set S := u + v + D with hS
  set Slo := u_lo + v_lo + Dlo with hSlo
  have hfac : u_lo * (u_lo + 2 * v_lo) = u_lo ^ 2 + 2 * u_lo * v_lo := by ring
  have hprod : 0 < u_lo * (u_lo + 2 * v_lo) := by rw [hfac]; exact hW
  have hvll : 0 < u_lo + 2 * v_lo := pos_of_mul_pos_right hprod (le_of_lt hul)
  have hulv : 0 < u_lo + v_lo := by linarith
  have huv : 0 < u + 2 * v := by linarith
  have huvnn : 0 ≤ u + v := by linarith
  have hu_pos : 0 < u := by linarith
  have hr_pos : 0 < r := by linarith
  have hDlo_pos : 0 < Dlo := by rw [hDlo]; exact Real.sqrt_pos.mpr hW
  have hSlo_pos : 0 < Slo := by rw [hSlo]; linarith
  have hargpos : 0 < u ^ 2 + 2 * u * v := by
    have : u ^ 2 + 2 * u * v = u * (u + 2 * v) := by ring
    rw [this]; exact mul_pos hu_pos huv
  have hDpos : 0 < D := by rw [hD]; exact Real.sqrt_pos.mpr hargpos
  have hSpos : 0 < S := by rw [hS]; linarith
  have hargle : u_lo ^ 2 + 2 * u_lo * v_lo ≤ u ^ 2 + 2 * u * v := by
    have hkey : u ^ 2 + 2 * u * v - (u_lo ^ 2 + 2 * u_lo * v_lo)
        = (u - u_lo) * (u + u_lo + 2 * v) + 2 * u_lo * (v - v_lo) := by ring
    have h1 : 0 ≤ u - u_lo := by linarith
    have h2 : 0 ≤ u + u_lo + 2 * v := by linarith
    have h3 : 0 ≤ (u - u_lo) * (u + u_lo + 2 * v) := mul_nonneg h1 h2
    have h4 : 0 ≤ 2 * u_lo * (v - v_lo) := by
      have : 0 ≤ v - v_lo := by linarith
      positivity
    linarith [hkey, h3, h4]
  have hDge : Dlo ≤ D := by rw [hDlo, hD]; exact Real.sqrt_le_sqrt hargle
  have hSge : Slo ≤ S := by rw [hSlo, hS]; linarith
  have hMnn : 0 ≤ M := by rw [hM]; exact le_trans (abs_nonneg v_lo) (le_max_left _ _)
  have hvM : |v| ≤ M := by
    rw [hM, abs_le]
    constructor
    · exact le_trans (neg_le_neg (le_max_left _ _)) (le_trans (neg_abs_le v_lo) hv)
    · exact le_trans hv2 (le_trans (le_abs_self v_hi) (le_max_right _ _))
  have hrhi2_ge_ulo : u_lo ≤ r_hi ^ 2 := by
    have h1 : r_lo ^ 2 ≤ r_hi ^ 2 := pow_le_pow_left₀ (le_of_lt hrl) hrlh 2
    linarith
  have hDsq : D ^ 2 = u ^ 2 + 2 * u * v := by rw [hD]; exact Real.sq_sqrt (le_of_lt hargpos)
  have hsum_pos : 0 < u + D := by linarith
  have hmul : |u - D| * (u + D) = 2 * u * |v| := by
    have h2 : (u - D) * (u + D) = -(2 * u * v) := by nlinarith [hDsq]
    have h4 : |u + D| = u + D := abs_of_pos hsum_pos
    have h5 : |2 * u * v| = 2 * u * |v| := by
      rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2), abs_of_pos hu_pos]
    calc |u - D| * (u + D) = |u - D| * |u + D| := by rw [h4]
      _ = |(u - D) * (u + D)| := (abs_mul _ _).symm
      _ = |-(2 * u * v)| := by rw [h2]
      _ = |2 * u * v| := by rw [abs_neg]
      _ = 2 * u * |v| := h5
  have hF8 : |u - D| ≤ 2 * |v| := by
    have hdiv : |u - D| = 2 * u * |v| / (u + D) := by
      rw [eq_div_iff (ne_of_gt hsum_pos)]
      linarith [hmul]
    rw [hdiv, div_le_iff₀ hsum_pos]
    have hpos : 0 ≤ |v| * D := mul_nonneg (abs_nonneg v) (le_of_lt hDpos)
    nlinarith [hpos]
  have hr2_ge_u : u ≤ r ^ 2 := by
    calc u ≤ u_hi := hu2
      _ ≤ r_lo ^ 2 := hur
      _ ≤ r ^ 2 := pow_le_pow_left₀ (le_of_lt hrl) hr 2
  have hr2u_nn : 0 ≤ r ^ 2 - u := by linarith
  have hr2u_ub : r ^ 2 - u ≤ r_hi ^ 2 - u_lo := by
    have h1 : r ^ 2 ≤ r_hi ^ 2 := pow_le_pow_left₀ (le_of_lt hr_pos) hr2 2
    linarith
  have htwo_nn : 0 ≤ 2 * (r ^ 2 - u) := by linarith
  have hF9 : |2 * r ^ 2 - S| ≤ 2 * (r_hi ^ 2 - u_lo) + 3 * M := by
    have hident : 2 * r ^ 2 - S = 2 * (r ^ 2 - u) + (u - D) + (-v) := by rw [hS, hD]; ring
    rw [hident]
    have h3 := abs_add_le (2 * (r ^ 2 - u) + (u - D)) (-v)
    have h3b := abs_add_le (2 * (r ^ 2 - u)) (u - D)
    have h_abs : |2 * (r ^ 2 - u)| = 2 * (r ^ 2 - u) := abs_of_nonneg htwo_nn
    have h_absv : |(-v)| = |v| := abs_neg v
    have hB : |u - D| ≤ 2 * M := by linarith [hF8, hvM]
    linarith [h3, h3b, h_abs, h_absv, hr2u_ub, hB, hvM]
  have hfirst : |2 * v / S - v / r ^ 2|
      ≤ M * (2 * (r_hi ^ 2 - u_lo) + 3 * M) / (r_lo ^ 2 * Slo) := by
    have hA : 2 * v / S - v / r ^ 2 = v * (2 * r ^ 2 - S) / (S * r ^ 2) := by
      have hSne : S ≠ 0 := ne_of_gt hSpos
      have hrne : r ≠ 0 := ne_of_gt hr_pos
      field_simp
    rw [hA]
    have hSr2pos : 0 < S * r ^ 2 := mul_pos hSpos (pow_pos hr_pos 2)
    rw [abs_div, abs_mul, abs_of_pos hSr2pos]
    have hCnn : 0 ≤ 2 * (r_hi ^ 2 - u_lo) + 3 * M := by linarith
    have hnumb : |v| * |2 * r ^ 2 - S| ≤ M * (2 * (r_hi ^ 2 - u_lo) + 3 * M) :=
      mul_le_mul hvM hF9 (abs_nonneg _) hMnn
    have hdenpos : 0 < r_lo ^ 2 * Slo := mul_pos (pow_pos hrl 2) hSlo_pos
    have hdenle : r_lo ^ 2 * Slo ≤ S * r ^ 2 := by
      have h := mul_le_mul hSge (pow_le_pow_left₀ (le_of_lt hrl) hr 2)
        (sq_nonneg r_lo) (le_of_lt hSpos)
      nlinarith [h]
    calc |v| * |2 * r ^ 2 - S| / (S * r ^ 2)
        ≤ (M * (2 * (r_hi ^ 2 - u_lo) + 3 * M)) / (S * r ^ 2) :=
          div_le_div_of_nonneg_right hnumb (le_of_lt hSr2pos)
      _ ≤ (M * (2 * (r_hi ^ 2 - u_lo) + 3 * M)) / (r_lo ^ 2 * Slo) :=
          div_le_div_of_nonneg_left (mul_nonneg hMnn hCnn) hdenpos hdenle
  have hYnn : 0 ≤ v ^ 2 * (1 + u / D) / S ^ 2 := by
    have huD : 0 < u / D := div_pos hu_pos hDpos
    exact div_nonneg (mul_nonneg (sq_nonneg v) (by linarith)) (le_of_lt (pow_pos hSpos 2))
  have hsecond : |v ^ 2 * (1 + u / D) / S ^ 2| ≤ M ^ 2 * (1 + u_hi / Dlo) / Slo ^ 2 := by
    have huD : 0 < u / D := div_pos hu_pos hDpos
    rw [abs_of_nonneg hYnn]
    have hS2pos : 0 < S ^ 2 := pow_pos hSpos 2
    have hSlo2pos : 0 < Slo ^ 2 := pow_pos hSlo_pos 2
    have hnum_le : v ^ 2 * (1 + u / D) ≤ M ^ 2 * (1 + u_hi / Dlo) := by
      have hv2 : v ^ 2 ≤ M ^ 2 := by rw [← sq_abs v]; exact pow_le_pow_left₀ (abs_nonneg v) hvM 2
      refine mul_le_mul hv2 ?_ ?_ (sq_nonneg M)
      · have : u / D ≤ u_hi / Dlo := div_le_div₀ (by linarith : (0:ℝ) ≤ u_hi) hu2 hDlo_pos hDge
        linarith
      · linarith
    have hdenle : Slo ^ 2 ≤ S ^ 2 := pow_le_pow_left₀ (le_of_lt hSlo_pos) hSge 2
    have hrhs_nn : 0 ≤ M ^ 2 * (1 + u_hi / Dlo) := by
      have : 0 ≤ u_hi / Dlo := div_nonneg (by linarith) (le_of_lt hDlo_pos)
      exact mul_nonneg (sq_nonneg M) (by linarith)
    calc v ^ 2 * (1 + u / D) / S ^ 2
        ≤ (M ^ 2 * (1 + u_hi / Dlo)) / S ^ 2 :=
          div_le_div_of_nonneg_right hnum_le (le_of_lt hS2pos)
      _ ≤ (M ^ 2 * (1 + u_hi / Dlo)) / Slo ^ 2 :=
          div_le_div_of_nonneg_left hrhs_nn hSlo2pos hdenle
  have hEq : 2 * v / S - v ^ 2 * (1 + u / D) / S ^ 2 - v / r ^ 2
      = (2 * v / S - v / r ^ 2) - v ^ 2 * (1 + u / D) / S ^ 2 := by ring
  rw [hEq]
  have htri : |(2 * v / S - v / r ^ 2) - v ^ 2 * (1 + u / D) / S ^ 2|
      ≤ |2 * v / S - v / r ^ 2| + |v ^ 2 * (1 + u / D) / S ^ 2| := by
    rw [abs_sub_le_iff]
    constructor <;>
      linarith [le_abs_self (2 * v / S - v / r ^ 2), neg_le_abs (2 * v / S - v / r ^ 2),
        le_abs_self (v ^ 2 * (1 + u / D) / S ^ 2), neg_le_abs (v ^ 2 * (1 + u / D) / S ^ 2)]
  rw [abs_of_nonneg hYnn] at htri
  have hsecond' : v ^ 2 * (1 + u / D) / S ^ 2 ≤ M ^ 2 * (1 + u_hi / Dlo) / Slo ^ 2 := by
    have := hsecond
    rwa [abs_of_nonneg hYnn] at this
  linarith [htri, hfirst, hsecond']

end Work.BoseBogFS
