/-
# A modulus bound for the quartic `p_c

If `p_c(z) = (z^2 + conj c)^2 + c = u` and `‖u‖` is at least `8 (1 + ‖c‖)^2`,
then `‖z‖^4 ≤ 2 ‖u‖`.  Equivalently: a point `z` whose `p_c`-image is far out in
modulus must itself be far out, with a clean constant.

The proof uses the reverse triangle inequality twice.  Writing `w = z^2 + conj c`
and `b = ‖c‖`:

* `u = w^2 + c`, so `‖w‖^2 = ‖w^2‖ ≤ ‖u‖ + b`   (`w` is not much bigger than `u`);
* `z^2 = w - conj c`, so `‖z‖^2 ≤ ‖w‖ + b`.

If `‖z‖^2 ≤ 4 (1 + b)` the bound follows from the hypothesis alone.  Otherwise
`‖w‖ ≥ ‖z‖^2 - b`, whence `‖u‖ ≥ (‖z‖^2 - b)^2 - b`, and the elementary
inequality `a^2 ≤ 2 ((a - b)^2 - b)` for `a ≥ 4 (1 + b) ≥ 0`, `b ≥ 0` closes it.
-/
import Mathlib
import Submission.Work.Bottcher.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open ComplexConjugate

namespace Work.Bottcher.Contraction

theorem norm_pow_four_le_of_pMap_eq (c u z : ℂ) (hz : Work.Bottcher.pMap c z = u)
    (hu : 8 * (1 + ‖c‖) ^ 2 ≤ ‖u‖) : ‖z‖ ^ 4 ≤ 2 * ‖u‖ := by
  set w : ℂ := z ^ 2 + conj c with hwd
  have hu' : u = w ^ 2 + c := by rw [hwd, ← hz, Work.Bottcher.pMap_apply]
  have hb : (0 : ℝ) ≤ ‖c‖ := norm_nonneg c
  -- `‖w‖^2 = ‖w^2‖ ≤ ‖u‖ + ‖c‖`
  have hstep1 : ‖w‖ ^ 2 ≤ ‖u‖ + ‖c‖ := by
    have h2 : ‖w ^ 2‖ ≤ ‖u‖ + ‖c‖ := by
      have : w ^ 2 = u - c := by rw [hu']; ring
      rw [this]; exact norm_sub_le u c
    rwa [norm_pow] at h2
  -- `‖z‖^2 ≤ ‖w‖ + ‖c‖`
  have hstep2 : ‖z‖ ^ 2 ≤ ‖w‖ + ‖c‖ := by
    have h2 : ‖z ^ 2‖ ≤ ‖w‖ + ‖c‖ := by
      calc ‖z ^ 2‖ = ‖w - conj c‖ := by rw [show z ^ 2 = w - conj c by rw [hwd]; ring]
        _ ≤ ‖w‖ + ‖conj c‖ := norm_sub_le w (conj c)
        _ = ‖w‖ + ‖c‖ := by rw [Complex.norm_conj]
    rwa [norm_pow] at h2
  by_cases ha : ‖z‖ ^ 2 ≤ 4 * (1 + ‖c‖)
  · -- small `z`: the hypothesis on `u` alone suffices
    have h1 : (‖z‖ ^ 2) ^ 2 ≤ (4 * (1 + ‖c‖)) ^ 2 := by
      simpa only [pow_two] using mul_self_le_mul_self (by positivity : (0 : ℝ) ≤ ‖z‖ ^ 2) ha
    have h2 : (4 * (1 + ‖c‖)) ^ 2 ≤ 2 * ‖u‖ := by nlinarith [hu]
    have h3 : (‖z‖ ^ 2) ^ 2 = ‖z‖ ^ 4 := by ring
    linarith [h1, h2, h3.le, h3.ge]
  · -- large `z`: use the reverse triangle inequality on `w = z^2 + conj c`
    have ha' : 4 * (1 + ‖c‖) < ‖z‖ ^ 2 := lt_of_not_ge ha
    have hbc : ‖c‖ ≤ ‖z‖ ^ 2 := by nlinarith [hb, ha']
    have hwge : ‖z‖ ^ 2 - ‖c‖ ≤ ‖w‖ := by linarith [hstep2]
    have hsq : (‖z‖ ^ 2 - ‖c‖) ^ 2 ≤ ‖w‖ ^ 2 := by
      apply sq_le_sq'
      · linarith [norm_nonneg w]
      · exact hwge
    have hUge : (‖z‖ ^ 2 - ‖c‖) ^ 2 - ‖c‖ ≤ ‖u‖ := by linarith [hstep1, hsq]
    have hkey : (‖z‖ ^ 2) ^ 2 ≤ 2 * ((‖z‖ ^ 2 - ‖c‖) ^ 2 - ‖c‖) := by
      nlinarith [sq_nonneg (‖z‖ ^ 2 - 4 * ‖c‖ - 4),
        mul_nonneg (by linarith : (0 : ℝ) ≤ ‖z‖ ^ 2 - 4 * ‖c‖ - 4) hb]
    have hfin : (‖z‖ ^ 2) ^ 2 ≤ 2 * ‖u‖ := by linarith
    have h3 : ‖z‖ ^ 4 = (‖z‖ ^ 2) ^ 2 := by ring
    linarith [hfin, h3.le, h3.ge]

end Work.Bottcher.Contraction
