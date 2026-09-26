import Mathlib
import Submission.Work.Modular.ThetaImagAxis

namespace Work.Modular

open Work.Modular

/-- Solving the Gaussian functional equation `F t = t^{-n/2} F (1/t)` for `F (1/t)`.  Here `F` is
the Gaussian sum `gaussSum L`; the hypothesis repeats the two sums rather than naming `F` so that
the statement can be applied directly to the functional equation of the main result.  The
hypothesis `2 ∣ n` is what makes the natural power `t ^ (n / 2)` agree with the real power
`t ^ ((n : ℝ) / 2)` appearing in the functional equation. -/
lemma gaussSum_inv_of_functionalEquation {n : ℕ}
    (L : Submodule ℤ (EuclideanSpace ℝ (Fin n))) (h2 : 2 ∣ n)
    (hfun : ∀ t : ℝ, 0 < t →
      gaussSum L t = ((t ^ (-(n : ℝ) / 2) : ℝ) : ℂ) *
        (∑' x : L,
          Complex.exp (-(↑(Real.pi / t * ‖(x : EuclideanSpace ℝ (Fin n))‖ ^ 2) : ℂ)))) :
    ∀ t : ℝ, 0 < t → gaussSum L (1 / t) = ((t ^ (n / 2) : ℝ) : ℂ) * gaussSum L t := by
  -- The summation appearing in the functional equation is `gaussSum L (1 / t)`.
  have hsum : ∀ t : ℝ, (∑' x : L,
        Complex.exp (-(↑(Real.pi / t * ‖(x : EuclideanSpace ℝ (Fin n))‖ ^ 2) : ℂ)))
      = gaussSum L (1 / t) := by
    intro t
    unfold gaussSum
    apply tsum_congr
    intro x
    congr 1
    ring_nf
  intro t ht
  have h := hfun t ht
  rw [hsum t] at h
  -- so `gaussSum L t = t^{-n/2} * gaussSum L (1/t)`.
  -- The factor `t ^ (n/2) * t ^ (-(n:ℝ)/2)` equals `1` because `2 ∣ n`.
  have hn : (n : ℝ) = 2 * ((n / 2 : ℕ) : ℝ) := by
    have h' := Nat.mul_div_cancel' h2
    exact_mod_cast h'.symm
  have hpowr : t ^ (((n / 2 : ℕ) : ℝ)) * t ^ (-(n : ℝ) / 2) = 1 := by
    rw [← Real.rpow_add ht]
    have hz : ((n / 2 : ℕ) : ℝ) + (-(n : ℝ) / 2) = 0 := by rw [hn]; ring
    rw [hz, Real.rpow_zero]
  have hpow : t ^ (n / 2) * t ^ (-(n : ℝ) / 2) = 1 := by
    rw [← Real.rpow_natCast]; exact hpowr
  have hc : ((t ^ (n / 2) : ℝ) : ℂ) * ((t ^ (-(n : ℝ) / 2) : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, hpow, Complex.ofReal_one]
  -- Multiply the functional equation by `t ^ (n/2)`; the constants collapse to `1`.
  have hgoal : ((t ^ (n / 2) : ℝ) : ℂ) * gaussSum L t = gaussSum L (1 / t) := by
    calc ((t ^ (n / 2) : ℝ) : ℂ) * gaussSum L t
        = ((t ^ (n / 2) : ℝ) : ℂ) *
            (((t ^ (-(n : ℝ) / 2) : ℝ) : ℂ) * gaussSum L (1 / t)) := by rw [h]
      _ = (((t ^ (n / 2) : ℝ) : ℂ) * ((t ^ (-(n : ℝ) / 2) : ℝ) : ℂ)) *
            gaussSum L (1 / t) := by ring
      _ = gaussSum L (1 / t) := by rw [hc, one_mul]
  exact hgoal.symm

end Work.Modular
