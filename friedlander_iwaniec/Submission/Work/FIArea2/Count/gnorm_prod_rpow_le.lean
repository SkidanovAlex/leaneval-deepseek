import Mathlib
import Submission.Work.FIArea2.area2_r3
import Submission.Work.FIPlan.Interface

namespace Work.FIArea2.Count

/-- `gnorm` is multiplicative: `|z₁z₂|² = |z₁|²·|z₂|²` (the norm `Zsqrtd.norm` of `ℤ[i]` is a ring
homomorphism, and passing to `natAbs` preserves products). -/
private lemma gnorm_mul_local (z1 z2 : GaussianInt) :
    Work.FIPlan.gnorm (z1 * z2) = Work.FIPlan.gnorm z1 * Work.FIPlan.gnorm z2 := by
  simp only [Work.FIPlan.gnorm, Zsqrtd.norm_mul, Int.natAbs_mul]

/-- The elementary size comparison behind the quadratic-remainder bound: for any `N ≥ 1` and any
`z₁, z₂` with `|zⱼ|² > N`, the factor `|z₁z₂|^{-1/4}` coming from the Poisson main term is already
dominated by `N^{-1/2}`.  Indeed `|z₁z₂|² = |z₁|²|z₂|² > N²`, and the map `t ↦ t^{-1/4}` is
strictly antitone on `(0,∞)`, while `(N²)^{-1/4} = N^{-1/2}`. -/
theorem gnorm_prod_rpow_le (Pa : Work.FITop.Params) (z1 z2 : GaussianInt)
    (h1 : Pa.N < ((Work.FIPlan.gnorm z1 : ℕ) : ℝ))
    (h2 : Pa.N < ((Work.FIPlan.gnorm z2 : ℕ) : ℝ)) :
    (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ) ^ (-(1 : ℝ) / 4))
      ≤ Pa.N ^ (-(1 : ℝ) / 2) := by
  have hNpos : 0 < Pa.N := lt_of_lt_of_le (by norm_num) Pa.hN1
  have hgmul : ((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ)
      = ((Work.FIPlan.gnorm z1 : ℕ) : ℝ) * ((Work.FIPlan.gnorm z2 : ℕ) : ℝ) := by
    rw [gnorm_mul_local, Nat.cast_mul]
  have ha0 : 0 < ((Work.FIPlan.gnorm z1 : ℕ) : ℝ) := lt_trans hNpos h1
  have hb0 : 0 < ((Work.FIPlan.gnorm z2 : ℕ) : ℝ) := lt_trans hNpos h2
  have hprod : Pa.N ^ 2
      < ((Work.FIPlan.gnorm z1 : ℕ) : ℝ) * ((Work.FIPlan.gnorm z2 : ℕ) : ℝ) := by
    nlinarith [h1, h2, hNpos]
  have hneg : (-(1 : ℝ) / 4) < 0 := by norm_num
  rw [hgmul, show (-(1 : ℝ) / 2) = 2 * (-(1 : ℝ) / 4) by norm_num,
      Real.rpow_mul (le_of_lt hNpos) 2 (-(1 : ℝ) / 4)]
  rw [Real.rpow_le_rpow_iff_of_neg (mul_pos ha0 hb0) (Real.rpow_pos_of_pos hNpos 2) hneg]
  rw [Real.rpow_two]
  exact le_of_lt hprod

end Work.FIArea2.Count
