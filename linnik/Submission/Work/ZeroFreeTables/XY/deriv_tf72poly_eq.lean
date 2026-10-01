import Mathlib
import Submission.Work.ZeroFreeTables.tf72Fc_decay

namespace Work.ZeroFreeTables.XY

lemma deriv_tf72poly_eq (lam t : ℝ) :
    deriv (tf72poly lam) t = (lam / 30) * (2 - lam * t) ^ 2 *
      (3 * (-lam) * (4 + 6 * lam * t + lam ^ 2 * t ^ 2)
        + (2 - lam * t) * (6 * lam + 2 * lam ^ 2 * t)) := by
  -- derivative of the inner linear factor `s ↦ 2 - lam * s`
  have hu : HasDerivAt (fun s : ℝ => 2 - lam * s) (-lam) t :=
    ((hasDerivAt_const (x := t) (2 : ℝ)).sub
        ((hasDerivAt_const (x := t) lam).mul (hasDerivAt_id' t))).congr_deriv (by ring)
  -- its cube
  have hp : HasDerivAt (fun s : ℝ => (2 - lam * s) ^ 3)
      (3 * (2 - lam * t) ^ 2 * (-lam)) t := hu.pow 3
  -- multiplied by the constant `lam / 30`
  have hpm : HasDerivAt (fun s : ℝ => (lam / 30) * (2 - lam * s) ^ 3)
      ((lam / 30) * (3 * (2 - lam * t) ^ 2 * (-lam))) t := hp.const_mul (lam / 30)
  -- the quadratic factor `s ↦ 4 + 6 * lam * s + lam ^ 2 * s ^ 2`
  have hlin : HasDerivAt (fun s : ℝ => 6 * lam * s) (6 * lam) t :=
    ((hasDerivAt_const (x := t) (6 * lam)).mul (hasDerivAt_id' t)).congr_deriv (by ring)
  have h2 : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by
    have h : HasDerivAt (fun s : ℝ => s ^ 2) ((2 : ℝ) * t ^ (2 - 1)) t := hasDerivAt_pow 2 t
    rwa [show (2 : ℕ) - 1 = 1 by norm_num, pow_one] at h
  have hquad : HasDerivAt (fun s : ℝ => lam ^ 2 * s ^ 2) (lam ^ 2 * (2 * t)) t :=
    ((hasDerivAt_const (x := t) (lam ^ 2)).mul h2).congr_deriv (by ring)
  have hv : HasDerivAt (fun s : ℝ => 4 + 6 * lam * s + lam ^ 2 * s ^ 2)
      (6 * lam + 2 * lam ^ 2 * t) t :=
    (((hasDerivAt_const (x := t) (4 : ℝ)).add hlin).add hquad).congr_deriv (by ring)
  -- product rule, then rewrite the derivative into the requested normal form
  have hmain := hpm.mul hv
  have hgoal : HasDerivAt (tf72poly lam)
      ((lam / 30) * (2 - lam * t) ^ 2 *
        (3 * (-lam) * (4 + 6 * lam * t + lam ^ 2 * t ^ 2)
          + (2 - lam * t) * (6 * lam + 2 * lam ^ 2 * t))) t := by
    unfold tf72poly
    exact hmain.congr_deriv (by ring)
  exact hgoal.deriv

end Work.ZeroFreeTables.XY
