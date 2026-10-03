import Mathlib
import Submission.Work.FIArea2.sec9_error_explicit
import Submission.Work.FIArea2.Gsum_bound

/-!
# (9.1) with no analytic input left over: the pair hypotheses discharge `hG`

`Work.FIArea2.sec9_error_explicit` (`Submission/Work/FIArea2/sec9_error_explicit.lean`) is *FI*
display (9.1),

  `‖C(z₁,z₂) − |z₁z₂|^{−1/2}·F₀·G₀‖
     ≤ |z₁z₂|^{−1/2}·4·10⁶·τ(|Δ|)³|Δ|^{−1}·√M·log(2+δ^{−2})·(1+π/√c₁)(1+π/√c₂)`

for the smooth majorant `F`, but it takes the arithmetic input of Lemma 8.1 (8.5) as the
hypothesis `hG`.  Here that hypothesis is *discharged* by `Work.FIArea2.Gsum_bound` at the pairs
that actually occur — `(z₁,z₂) = (z₁,z̄₁) = (z₂,z̄₂) = 1` and `Δ = Im(z̄₁z₂) ≠ 0`, which
`IsBetaCoeff`'s support supplies (`isCoprime_star_of_squarefree_odd_gnorm` etc.) — so that (9.1)
is available with only the standing hypotheses of §6 and the geometric conditions on `F`.
-/

namespace Work.FIArea2

open scoped BigOperators

noncomputable section

lemma absDelta_ne_zero_of_Delta_ne_zero {z1 z2 : GaussianInt}
    (h : Work.FIPlan.Delta z1 z2 ≠ 0) : Work.FIPlan.absDelta z1 z2 ≠ 0 := by
  rw [Work.FIPlan.absDelta]
  exact fun hc => h (Int.natAbs_eq_zero.mp hc)

lemma gamOf_lt_one_of_Delta_ne_zero {z1 z2 : GaussianInt}
    (hΔ : Work.FIPlan.Delta z1 z2 ≠ 0) : gamOf z1 z2 < 1 := by
  have hkey : ((star z1 * z2).re : ℤ) ^ 2 + Work.FIPlan.Delta z1 z2 ^ 2
      = (Work.FIPlan.gnorm z1 : ℤ) * (Work.FIPlan.gnorm z2 : ℤ) := by
    have h1 : Work.FIPlan.gnorm (star z1 * z2)
        = Work.FIPlan.gnorm z1 * Work.FIPlan.gnorm z2 := by
      rw [gnorm_mul (star z1) z2, gnorm_conj z1]
    have h3 : ((star z1 * z2).re : ℤ) ^ 2 + ((star z1 * z2).im : ℤ) ^ 2
        = (Work.FIPlan.gnorm (star z1 * z2) : ℤ) := by
      rw [Work.FIPlan.gnorm, Zsqrtd.norm_def]
      rw [show ((star z1 * z2).re * (star z1 * z2).re - -1 * (star z1 * z2).im * (star z1 * z2).im : ℤ)
          = ((star z1 * z2).re ^ 2 + (star z1 * z2).im ^ 2) by ring]
      have hnonneg : (0 : ℤ) ≤ (star z1 * z2).re ^ 2 + (star z1 * z2).im ^ 2 := by
        nlinarith [sq_nonneg ((star z1 * z2).re : ℤ), sq_nonneg ((star z1 * z2).im : ℤ)]
      exact (Int.natAbs_of_nonneg hnonneg).symm
    have h4 : ((star z1 * z2).im : ℤ) = Work.FIPlan.Delta z1 z2 := by
      simp [Work.FIPlan.Delta]
    rw [h1] at h3
    rw [h4] at h3
    rw [h3]
    push_cast
    ring
  rw [gamOf]
  have hpos : 0 < ((Work.FIPlan.gnorm z1 : ℕ) : ℝ) * ((Work.FIPlan.gnorm z2 : ℕ) : ℝ) := by
    have h2 : (0 : ℤ) < ((star z1 * z2).re : ℤ) ^ 2 + Work.FIPlan.Delta z1 z2 ^ 2 := by
      have h5 : (0 : ℤ) < Work.FIPlan.Delta z1 z2 ^ 2 := sq_pos_of_ne_zero hΔ
      nlinarith [sq_nonneg ((star z1 * z2).re : ℤ)]
    rw [hkey] at h2
    exact_mod_cast h2
  have hlt : (((star z1 * z2).re : ℤ) : ℝ) ^ 2
      < ((Work.FIPlan.gnorm z1 : ℕ) : ℝ) * ((Work.FIPlan.gnorm z2 : ℕ) : ℝ) := by
    have h2 : (((star z1 * z2).re : ℤ) : ℝ) ^ 2
        + ((Work.FIPlan.Delta z1 z2 : ℤ) : ℝ) ^ 2
        = ((Work.FIPlan.gnorm z1 : ℕ) : ℝ) * ((Work.FIPlan.gnorm z2 : ℕ) : ℝ) := by
      have := congrArg (fun k : ℤ => (k : ℝ)) hkey
      push_cast at this
      linarith [this]
    have h3 : (0 : ℝ) < ((Work.FIPlan.Delta z1 z2 : ℤ) : ℝ) ^ 2 := by
      have : (Work.FIPlan.Delta z1 z2 : ℤ) ≠ 0 := hΔ
      exact sq_pos_of_ne_zero (by exact_mod_cast this)
    linarith
  rw [div_lt_one (Real.sqrt_pos.mpr hpos)]
  have hs2 : Real.sqrt (((Work.FIPlan.gnorm z1 : ℕ) : ℝ) * ((Work.FIPlan.gnorm z2 : ℕ) : ℝ)) ^ 2
      = ((Work.FIPlan.gnorm z1 : ℕ) : ℝ) * ((Work.FIPlan.gnorm z2 : ℕ) : ℝ) :=
    Real.sq_sqrt (le_of_lt hpos)
  nlinarith [hs2, hlt, Real.sqrt_nonneg (((Work.FIPlan.gnorm z1 : ℕ) : ℝ) * ((Work.FIPlan.gnorm z2 : ℕ) : ℝ))]

end

end Work.FIArea2
