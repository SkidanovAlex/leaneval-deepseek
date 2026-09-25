import Mathlib

namespace Work.RHContract.A.regionII

theorem caNet2_arith_B (L : ℝ) (h1 : (138155 / 10000 : ℝ) ≤ L) (h2 : L ≤ 1845 / 100) :
    (1 / 3) * (L / 2 + 15 / 100) * ((45 / 10000) / L) ≤
      ((7075 / 100000 * L + 90181 / 1000000) / ((L + 941 / 10000) * (L / 2 + 1397 / 10000)))
        * (20036 / 100000 - 48817 / 100000 / L) := by
  -- Core polynomial inequality obtained by clearing denominators
  -- (L > 0 and the quadratic factor are positive on the interval).
  have hpoly : 150 * (L / 2 + 15 / 100) * ((L + 941 / 10000) * (L / 2 + 1397 / 10000)) ≤
      (7075 / 100000 * L + 90181 / 1000000) * (20036 * L - 48817) := by
    -- The difference is a concave cubic; write it as an endpoint value plus two
    -- nonnegative pieces.
    have hLa : 0 ≤ L - 138155 / 10000 := by linarith
    have hbL : 0 ≤ 1845 / 100 - L := by linarith
    have hw : 0 ≤ 75 / 2 * L - 364669 / 2000 := by linarith
    have hprod : 0 ≤ (L - 138155 / 10000) * (1845 / 100 - L) * (75 / 2 * L - 364669 / 2000) :=
      mul_nonneg (mul_nonneg hLa hbL) hw
    have hid : (7075 / 100000 * L + 90181 / 1000000) * (20036 * L - 48817)
          - 150 * (L / 2 + 15 / 100) * ((L + 941 / 10000) * (L / 2 + 1397 / 10000))
        = 558524290709241 / 4000000000 + (27579177661 / 2000000) * (L - 138155 / 10000)
          + (L - 138155 / 10000) * (1845 / 100 - L) * (75 / 2 * L - 364669 / 2000) := by
      ring
    have hsLa : 0 ≤ (27579177661 / 2000000) * (L - 138155 / 10000) :=
      mul_nonneg (by norm_num) hLa
    linarith [hprod, hsLa]
  have hL : 0 < L := by linarith
  have h1' : 0 < L + 941 / 10000 := by linarith
  have h2' : 0 < L / 2 + 1397 / 10000 := by linarith
  have h3' : 0 < (L + 941 / 10000) * (L / 2 + 1397 / 10000) := mul_pos h1' h2'
  have hE : 0 ≤ 20036 / 100000 - 48817 / 100000 / L := by
    rw [sub_nonneg, div_le_iff₀ hL]
    linarith
  field_simp
  nlinarith [hpoly]

end Work.RHContract.A.regionII
