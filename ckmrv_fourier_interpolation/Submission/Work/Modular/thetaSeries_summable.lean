import Mathlib
import Submission.Work.Modular.Lattice

namespace Work.Modular

open Work.Modular
open UpperHalfPlane

set_option maxHeartbeats 800000

/-- The modulus of the theta summand `thetaTerm τ x = exp (π i τ ‖x‖²)` is the Gaussian
`exp (-π (Im τ) ‖x‖²)`. -/
private lemma norm_thetaTerm {n : ℕ} (τ : ℍ) (x : EuclideanSpace ℝ (Fin n)) :
    ‖thetaTerm τ x‖ = Real.exp (-(Real.pi * τ.im * ‖x‖ ^ 2)) := by
  rw [thetaTerm, Complex.norm_exp]
  congr 1
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  ring

/-- The Gaussian `exp (-c t²)` is bounded by `(k!/cᵏ) * t^{-2k}` for positive `t`.  This is the
quantitative form of the statement that the Gaussian decays faster than any polynomial, proved
from the elementary bound `xᵏ ≤ k! * exp x`. -/
private lemma exp_neg_mul_sq_le {c : ℝ} (hc : 0 < c) (k : ℕ) {t : ℝ} (ht : 0 < t) :
    Real.exp (-(c * t ^ 2)) ≤ (Nat.factorial k : ℝ) / c ^ k * t ^ (-(2 * (k : ℝ))) := by
  have hc' : 0 < c ^ k := pow_pos hc k
  have hfac : 0 < (Nat.factorial k : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have hx : 0 ≤ c * t ^ 2 := by positivity
  have h := Real.pow_div_factorial_le_exp (c * t ^ 2) hx k
  rw [div_le_iff₀ hfac] at h
  have h2 : (c * t ^ 2) ^ k * Real.exp (-(c * t ^ 2)) ≤ (Nat.factorial k : ℝ) := by
    have h' := mul_le_mul_of_nonneg_right h (Real.exp_nonneg (-(c * t ^ 2)))
    have heq : Real.exp (c * t ^ 2) * (↑k.factorial * Real.exp (-(c * t ^ 2))) =
        (↑k.factorial : ℝ) := by
      rw [← mul_assoc, mul_comm (Real.exp (c * t ^ 2)) (↑k.factorial), mul_assoc, ← Real.exp_add,
        add_neg_cancel, Real.exp_zero, mul_one]
    rw [mul_assoc, heq] at h'
    exact h'
  have hp : (c * t ^ 2) ^ k = c ^ k * t ^ (2 * k) := by
    rw [mul_pow c (t ^ 2) k, ← pow_mul t 2 k]
  rw [hp] at h2
  rw [mul_assoc] at h2
  have h3 : t ^ (2 * k) * Real.exp (-(c * t ^ 2)) ≤ (Nat.factorial k : ℝ) / c ^ k := by
    rw [le_div_iff₀ hc', mul_comm (t ^ (2 * k) * Real.exp (-(c * t ^ 2))) (c ^ k)]
    exact h2
  have hfin : Real.exp (-(c * t ^ 2)) =
      t ^ (-(2 * (k : ℝ))) * (t ^ (2 * k) * Real.exp (-(c * t ^ 2))) := by
    rw [Real.rpow_neg ht.le]
    have hexp : 2 * (k : ℝ) = ((2 * k : ℕ) : ℝ) := by push_cast; ring
    rw [hexp, Real.rpow_natCast, inv_mul_cancel_left₀ (pow_ne_zero _ (ne_of_gt ht))]
  rw [hfin]
  calc t ^ (-(2 * (k : ℝ))) * (t ^ (2 * k) * Real.exp (-(c * t ^ 2)))
      ≤ t ^ (-(2 * (k : ℝ))) * ((Nat.factorial k : ℝ) / c ^ k) :=
        mul_le_mul_of_nonneg_left h3 (Real.rpow_nonneg ht.le _)
    _ = (Nat.factorial k : ℝ) / c ^ k * t ^ (-(2 * (k : ℝ))) := by ring

/-- The theta series of a discrete submodule `L ⊆ ℝⁿ` is absolutely summable at every point of
the upper half plane: the modulus of the summand `thetaTerm τ x = exp (π i τ ‖x‖²)` is
`exp (-π (Im τ) ‖x‖²)`, which decays faster than any negative power of `‖x‖` on the discrete
lattice `L`. -/
theorem thetaSeries_summable {n : ℕ} (L : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    [DiscreteTopology L] (τ : ℍ) :
    Summable (fun x : L => thetaTerm τ (x : EuclideanSpace ℝ (Fin n))) := by
  -- The exponent `k = finrank L + 1` is chosen so that `2k > finrank L`, i.e. the polynomial
  -- decay `t^{-2k}` beats the `p`-series threshold of the lattice.
  set k : ℕ := Module.finrank ℤ L + 1 with hk
  have hr : (-(2 * (k : ℝ))) < -(Module.finrank ℤ L : ℝ) := by
    have hfr : (0 : ℝ) ≤ Module.finrank ℤ L := Nat.cast_nonneg _
    rw [hk]; push_cast; linarith
  -- The dominating polynomial times a Gaussian, summable by `ZLattice.summable_norm_rpow`.
  have hsum : Summable (fun z : L =>
      (Nat.factorial k : ℝ) / (Real.pi * τ.im) ^ k * ‖z‖ ^ (-(2 * (k : ℝ)))) :=
    Summable.mul_left ((Nat.factorial k : ℝ) / (Real.pi * τ.im) ^ k)
      (ZLattice.summable_norm_rpow L (-(2 * (k : ℝ))) hr)
  -- It dominates the theta summand away from the origin, which is a cofinite condition since
  -- `{0}` is finite.
  refine Summable.of_norm_bounded_eventually hsum ?_
  refine Filter.mem_of_superset
    (Set.Finite.compl_mem_cofinite (Set.finite_singleton (0 : L))) ?_
  intro z hz
  rw [Set.mem_compl_iff, Set.mem_singleton_iff] at hz
  simp only [Set.mem_ofPred_eq]
  have hc : 0 < Real.pi * τ.im := by have := τ.im_pos; positivity
  have hzE : 0 < ‖(z : EuclideanSpace ℝ (Fin n))‖ := by
    rw [norm_pos_iff]; intro h; exact hz (Subtype.ext h)
  rw [norm_thetaTerm, ← Submodule.norm_coe z]
  exact exp_neg_mul_sq_le hc k hzE

end Work.Modular
