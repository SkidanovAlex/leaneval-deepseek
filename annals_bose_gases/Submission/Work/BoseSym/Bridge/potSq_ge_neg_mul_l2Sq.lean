import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseSym.Form.l2Sq_eq_integral
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# BoseSym.Bridge — the potential energy is bounded below by `-C ‖u‖²`

If the potential `W` on configuration space is bounded in absolute value by
the constant `C` (`BddBy N W C`), then the potential energy `potSq W p`
of any ambient state `p` is bounded below by `-C * l2Sq p`, i.e. by
`-C` times the squared `L²` norm of the function part of `p`.

The pointwise input is that `|W x| ≤ C` gives `W x ≥ -C`, hence
`W x * u x² ≥ -C * u x²`; the integral of the right-hand side is
`-C * ‖u‖² = -C * l2Sq p` by `Form.l2Sq_eq_integral`.

The only care needed is that the integrand `W · u²` need not be
(Strongly) measurable, since `W` is an arbitrary bounded function: we split on
whether `W · u²` is integrable. If it is, the integral inequality follows from
`integral_mono`; if it is not, the Bochner integral is `0` by `integral_undef`
and the claim reduces to `-C ‖u‖² ≤ 0`, i.e. `0 ≤ C`.
-/

namespace Work.BoseSym.Bridge

open MeasureTheory

theorem potSq_ge_neg_mul_l2Sq {N : ℕ} {W : Work.BoseSym.Conf N → ℝ}
    {C : ℝ} (hW : Work.BoseSym.BddBy N W C) (p : Work.BoseSym.Amb N) :
    -C * Work.BoseSym.l2Sq p ≤ Work.BoseSym.potSq W p := by
  -- `C` is nonnegative: `|W x| ≤ C` and `0 ≤ |W x|` for any `x`.
  have hC : 0 ≤ C := (abs_nonneg (W 0)).trans (hW 0)
  -- the function part of `p` is an `L²` function, hence its square is integrable
  have hg : MemLp ((p.1 : Work.BoseSym.Conf N → ℝ)) 2 (Work.BoseSym.volC N) :=
    Lp.memLp p.1
  have hsq : Integrable (fun x => ((p.1 : Work.BoseSym.Conf N → ℝ) x) ^ 2) :=
    hg.integrable_sq
  -- the pointwise lower bound
  have hpt : ∀ x, -C * ((p.1 : Work.BoseSym.Conf N → ℝ) x) ^ 2
      ≤ W x * ((p.1 : Work.BoseSym.Conf N → ℝ) x) ^ 2 :=
    fun x => mul_le_mul_of_nonneg_right (abs_le.mp (hW x)).1 (sq_nonneg _)
  -- `∫ u² = l2Sq p`
  have hl2 : ∫ x, ((p.1 : Work.BoseSym.Conf N → ℝ) x) ^ 2 = Work.BoseSym.l2Sq p := by
    rw [Work.BoseSym.Form.l2Sq_eq_integral p, Work.BoseSym.intC]
  by_cases hint : Integrable (fun x => W x * ((p.1 : Work.BoseSym.Conf N → ℝ) x) ^ 2)
  · -- if the potential energy is integrable, integrate the pointwise bound
    have h1 : ∫ x, -C * ((p.1 : Work.BoseSym.Conf N → ℝ) x) ^ 2
        ≤ ∫ x, W x * ((p.1 : Work.BoseSym.Conf N → ℝ) x) ^ 2 :=
      integral_mono (hsq.const_mul (-C)) hint hpt
    rw [integral_const_mul, hl2] at h1
    exact h1
  · -- otherwise the Bochner integral of the potential energy is `0`
    rw [Work.BoseSym.potSq, integral_undef hint]
    refine mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hC) ?_
    rw [Work.BoseSym.l2Sq]
    exact sq_nonneg _

end Work.BoseSym.Bridge
