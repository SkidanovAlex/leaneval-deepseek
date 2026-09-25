import Mathlib
import Submission.Work.RHContract.A.regionII.caNet2_defs

/-!
# `Work.RHContract.A.regionII.netMassB`

The upper bound `netNuB L ≤ netMasslb s L * (s-4)/s²` for the loss coefficient of the
`Net₂` argument of Region II, on the range `s ≥ 1000`, `L ≥ 11.5`.

The whole content is the numerical fact that the two auxiliary quantities
`F(s) = (0.26421 s − 1 − 1.96189 √s)(s−4)/s² − 0.20036` and
`G(s) = F(s) + (0.48817 − 0.49013 + 1.96052/s)/11.5`
are nonnegative for `s ≥ 1000`. They are proved by writing `s = u²`, clearing
denominators, and expanding the resulting quartic at `u = 316227/10000 < √1000`,
where every coefficient of the expansion in `u − 316227/10000` is positive.
-/

namespace Work.RHContract.A.regionII

noncomputable section

set_option maxHeartbeats 0

/-- `P(u) = (c−a)u⁴ − e u³ − (4c+1)u² + 4e u + 4` is nonnegative on `u ≥ 316227/10000`,
where `c = 26421/100000`, `a = 20036/100000`, `e = 196189/100000`.  This is the quartic
whose quotient by `u⁴` is the auxiliary quantity `F(u²)`. -/
private lemma netMassB_polyP_nonneg (u : ℝ) (hu : (316227/10000 : ℝ) ≤ u) :
    0 ≤ ((26421:ℝ)/100000 - 20036/100000) * u^4 - (196189/100000) * u^3
        - (4 * ((26421:ℝ)/100000) + 1) * u^2 + 4 * (196189/100000) * u + 4 := by
  set w : ℝ := u - 316227/10000 with hwdef
  have hw : 0 ≤ w := by rw [hwdef]; linarith
  have hu' : u = 316227/10000 + w := by rw [hwdef]; ring
  rw [hu']
  ring_nf
  positivity

/-- `Q(u) = ((c−a) + (b−d)/11.5)u⁴ − e u³ + (4d/11.5 − (4c+1))u² + 4e u + 4` is
nonnegative on `u ≥ 316227/10000`, where `b = 48817/100000`, `d = 49013/100000`.
This is the quartic whose quotient by `u⁴` is the auxiliary quantity `G(u²)`. -/
private lemma netMassB_polyQ_nonneg (u : ℝ) (hu : (316227/10000 : ℝ) ≤ u) :
    0 ≤ (((26421:ℝ)/100000 - 20036/100000) + (48817/100000 - 49013/100000)/11.5) * u^4
        - (196189/100000) * u^3
        + (4 * (49013/100000) / 11.5 - (4 * ((26421:ℝ)/100000) + 1)) * u^2
        + 4 * (196189/100000) * u + 4 := by
  set w : ℝ := u - 316227/10000 with hwdef
  have hw : 0 ≤ w := by rw [hwdef]; linarith
  have hu' : u = 316227/10000 + w := by rw [hwdef]; ring
  rw [hu']
  ring_nf
  positivity

/-- `F(s) ≥ 0` for `s ≥ 1000`. -/
private lemma netMassB_F_nonneg (s : ℝ) (hs : (1000:ℝ) ≤ s) :
    0 ≤ (26421/100000 * s - 1 - 196189/100000 * Real.sqrt s) * (s - 4) / s^2
        - 20036/100000 := by
  have hs0 : 0 < s := by linarith
  set u : ℝ := Real.sqrt s with hudef
  have hu2 : u^2 = s := by rw [hudef]; exact Real.sq_sqrt (le_of_lt hs0)
  have hu_ge : (316227/10000 : ℝ) ≤ u := by
    rw [hudef]
    have h1 : (316227/10000 : ℝ) ≤ Real.sqrt 1000 := by
      rw [Real.le_sqrt (by norm_num) (by norm_num)]
      norm_num
    exact le_trans h1 (Real.sqrt_le_sqrt hs)
  have hP := netMassB_polyP_nonneg u hu_ge
  have hkey : (26421/100000 * s - 1 - 196189/100000 * u) * (s - 4) / s^2 - 20036/100000
      = (((26421:ℝ)/100000 - 20036/100000) * u^4 - (196189/100000) * u^3
        - (4 * ((26421:ℝ)/100000) + 1) * u^2 + 4 * (196189/100000) * u + 4) / u^4 := by
    rw [← hu2]
    field_simp
    ring
  rw [hkey]
  positivity

/-- `G(s) ≥ 0` for `s ≥ 1000`. -/
private lemma netMassB_G_nonneg (s : ℝ) (hs : (1000:ℝ) ≤ s) :
    0 ≤ (26421/100000 * s - 1 - 196189/100000 * Real.sqrt s) * (s - 4) / s^2
        - 20036/100000
        + (48817/100000 - 49013/100000 + 4 * (49013/100000) / s) / 11.5 := by
  have hs0 : 0 < s := by linarith
  set u : ℝ := Real.sqrt s with hudef
  have hu2 : u^2 = s := by rw [hudef]; exact Real.sq_sqrt (le_of_lt hs0)
  have hu_ge : (316227/10000 : ℝ) ≤ u := by
    rw [hudef]
    have h1 : (316227/10000 : ℝ) ≤ Real.sqrt 1000 := by
      rw [Real.le_sqrt (by norm_num) (by norm_num)]
      norm_num
    exact le_trans h1 (Real.sqrt_le_sqrt hs)
  have hQ := netMassB_polyQ_nonneg u hu_ge
  have hkey : (26421/100000 * s - 1 - 196189/100000 * u) * (s - 4) / s^2
        - 20036/100000
        + (48817/100000 - 49013/100000 + 4 * (49013/100000) / s) / 11.5
      = ((((26421:ℝ)/100000 - 20036/100000) + (48817/100000 - 49013/100000)/11.5) * u^4
        - (196189/100000) * u^3
        + (4 * (49013/100000) / 11.5 - (4 * ((26421:ℝ)/100000) + 1)) * u^2
        + 4 * (196189/100000) * u + 4) / u^4 := by
    rw [← hu2]
    field_simp
    ring
  rw [hkey]
  positivity

theorem netMassB (s L : ℝ) (hs : (1000 : ℝ) ≤ s) (hL : (11.5 : ℝ) ≤ L) :
    netNuB L ≤ netMasslb s L * (s - 4) / s ^ 2 := by
  unfold netNuB netMasslb
  have hL0 : 0 < L := by linarith
  have hF := netMassB_F_nonneg s hs
  have hG := netMassB_G_nonneg s hs
  have hdecomp :
      (26421/100000 * s - 49013/100000 * s / L - 1 - 196189/100000 * Real.sqrt s)
          * (s - 4) / s^2 - (20036/100000 - 48817/100000 / L)
        = ((26421/100000 * s - 1 - 196189/100000 * Real.sqrt s) * (s - 4) / s^2
              - 20036/100000)
          + (48817/100000 - 49013/100000 + 4 * (49013/100000) / s) / L := by
    field_simp
    ring
  rw [← sub_nonneg, hdecomp]
  rcases le_or_gt 0 (48817/100000 - 49013/100000 + 4 * (49013/100000) / s) with hY | hY
  · have : 0 ≤ (48817/100000 - 49013/100000 + 4 * (49013/100000) / s) / L :=
      div_nonneg hY (le_of_lt hL0)
    linarith
  · have h1 : (1:ℝ)/L ≤ 1/11.5 := one_div_le_one_div_of_le (by norm_num) hL
    have h2 : (48817/100000 - 49013/100000 + 4 * (49013/100000) / s) * (1/11.5)
        ≤ (48817/100000 - 49013/100000 + 4 * (49013/100000) / s) * (1/L) :=
      mul_le_mul_of_nonpos_left h1 (le_of_lt hY)
    have he1 : (48817/100000 - 49013/100000 + 4 * (49013/100000) / s) * (1/11.5)
        = (48817/100000 - 49013/100000 + 4 * (49013/100000) / s) / 11.5 := by ring
    have he2 : (48817/100000 - 49013/100000 + 4 * (49013/100000) / s) * (1/L)
        = (48817/100000 - 49013/100000 + 4 * (49013/100000) / s) / L := by ring
    linarith

end

end Work.RHContract.A.regionII
