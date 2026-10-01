import Mathlib

namespace Work.LinnikBurgess

open Polynomial

/-- A polynomial over `ZMod p` (with `p ≥ 5` prime) whose derivative vanishes and whose degree is
at most `4` is constant.

Indeed, if its degree `d` were positive, then `d` is the index of the coefficient of `X^{d-1}` in
the derivative: that coefficient is `d * leadingCoeff`. Here `leadingCoeff ≠ 0`, so `d = 0` in
`ZMod p`, i.e. `p ∣ d`; but `0 < d ≤ 4 < p`, a contradiction. So `natDegree = 0`. -/
theorem eq_C_of_deriv_eq_zero_of_natDegree_le_four {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p)
    {R : Polynomial (ZMod p)} (hdeg : R.natDegree ≤ 4) (h : R.derivative = 0) :
    R = Polynomial.C (R.coeff 0) := by
  have hnd0 : R.natDegree = 0 := by
    by_contra hne
    have hR0 : R ≠ 0 := by
      intro h0
      rw [h0, Polynomial.natDegree_zero] at hne
      exact hne rfl
    have hd1 : 1 ≤ R.natDegree := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hne)
    have hlead : R.coeff R.natDegree ≠ 0 := by
      rw [Polynomial.coeff_natDegree]
      exact Polynomial.leadingCoeff_ne_zero.mpr hR0
    have hc : (R.derivative).coeff (R.natDegree - 1) = 0 := by
      rw [h, Polynomial.coeff_zero]
    rw [Polynomial.coeff_derivative, Nat.sub_add_cancel hd1] at hc
    have hzero : (((R.natDegree - 1 : ℕ)) : ZMod p) + 1 = 0 := by
      rcases mul_eq_zero.mp hc with h1 | h1
      · exact absurd h1 hlead
      · exact h1
    have hcast : (((R.natDegree - 1 : ℕ)) : ZMod p) + 1 = (R.natDegree : ZMod p) := by
      rw [Nat.cast_sub hd1]; ring
    have hd0 : (R.natDegree : ZMod p) = 0 := by rw [← hcast]; exact hzero
    have hdvd : (p : ℤ) ∣ (R.natDegree : ℤ) := by
      have hthis : ((R.natDegree : ℤ) : ZMod p) = 0 := by push_cast; exact hd0
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd (R.natDegree : ℤ) p).mp hthis
    have hpos : 0 < (R.natDegree : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero hne
    have hle : (p : ℤ) ≤ (R.natDegree : ℤ) := Int.le_of_dvd hpos hdvd
    have hlt : (R.natDegree : ℤ) < (p : ℤ) := by
      have hp' : R.natDegree < p := by omega
      exact_mod_cast hp'
    omega
  exact Polynomial.eq_C_of_natDegree_eq_zero hnd0

theorem eval_not_dvd_of_deriv_eq_zero {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p) {Q : Polynomial ℤ}
    (hdeg : Q.natDegree ≤ 4)
    (hQ : Q.map (Int.castRingHom (ZMod p)) ≠ 0)
    (hgz : Q.derivative.map (Int.castRingHom (ZMod p)) = 0) (y : ℤ) :
    ¬ ((p : ℤ) ∣ Q.eval y) := by
  intro hdvd
  -- Reduce the divisibility to a vanishing statement in `ZMod p`.
  have hz : ((Q.eval y : ℤ) : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd (Q.eval y) p).mpr hdvd
  -- The reduction of `Q` is a polynomial with vanishing derivative and degree `≤ 4`.
  have hder : (Q.map (Int.castRingHom (ZMod p))).derivative = 0 := by
    rw [Polynomial.derivative_map (p := Q) (f := Int.castRingHom (ZMod p))]
    exact hgz
  have hdeg' : (Q.map (Int.castRingHom (ZMod p))).natDegree ≤ 4 :=
    le_trans (Polynomial.natDegree_map_le (f := Int.castRingHom (ZMod p)) (p := Q)) hdeg
  have hconst := eq_C_of_deriv_eq_zero_of_natDegree_le_four hp hdeg' hder
  -- It is therefore constant, and nonzero, so its constant term is nonzero.
  have hc0 : (Q.map (Int.castRingHom (ZMod p))).coeff 0 ≠ 0 := by
    intro h0
    exact hQ (by rw [hconst, h0]; simp)
  -- But evaluating the reduction of `Q` at `y` gives this constant term, which must be `0`.
  have heval : (Q.map (Int.castRingHom (ZMod p))).eval ((y : ℤ) : ZMod p) = 0 := by
    have h1 : (Q.map (Int.castRingHom (ZMod p))).eval ((y : ℤ) : ZMod p)
        = ((Q.eval y : ℤ) : ZMod p) := by
      simpa using Polynomial.eval_map_apply (p := Q) (f := Int.castRingHom (ZMod p)) y
    rw [h1, hz]
  rw [hconst] at heval
  rw [Polynomial.eval_C] at heval
  exact hc0 heval

end Work.LinnikBurgess
