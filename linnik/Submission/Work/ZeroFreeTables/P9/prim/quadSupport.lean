/-
# ZeroFreeTables/P9/prim/quadSupport

The two remaining support lemmas of the quadratic near/far split of the `P9` engine, made
independent of the pre-existing `quadFarBound`/`quadInvSqSummable` stubs (the fleet was
saturated when they were requested, so they are proved here).

* `quadFar_re_bound`: outside the near disk the real part of `(1/(s-u))²` is bounded below by
  `-((1+4/δ²)/(1+‖s-u‖²))`.  This is immediate from the already-proved local bound
  `Work.ZeroFreeTables.P9.zetaQuadLocalBound` once one observes that the near-centre distance
  `‖1 + i·Im s - u‖` is at most `‖s-u‖` (the real part `1 - u.re` is smaller than `s.re - u.re`
  while the imaginary parts agree).
* `quadInvSq_summable`: the multiplicity-weighted Lorentzian sum is summable, by comparison with
  the (norm of the) summable quadratic zero sum; the only exceptional index `u = s` is handled by
  `zeroMult χ s = 0`, since `completedLFunction` has no zero in `Re s > 1`.
-/
import Mathlib
import Submission.Work.LinnikContract.Defs
import Submission.Commons.NumberTheory.DirichletCharacter.completedLFunction_ne_zero_of_one_lt_re
import Submission.Work.ZeroFreeTables.P9.zetaQuadLocalBound

open DirichletCharacter Complex

namespace Work.ZeroFreeTables.P9.prim

/-- `‖1 + i·Im s - u‖ ≤ ‖s - u‖` when `1 < Re s` and `Re u < 1`. -/
private lemma nearCenter_norm_le {s u : ℂ} (hs : 1 < s.re) (hu : u.re < 1) :
    ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ ‖s - u‖ := by
  have hre1 : ((1 : ℂ) + (s.im : ℂ) * Complex.I - u).re = 1 - u.re := by
    simp [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im]
  have him1 : ((1 : ℂ) + (s.im : ℂ) * Complex.I - u).im = s.im - u.im := by
    simp [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.I_re, Complex.I_im]
  have hre2 : (s - u).re = s.re - u.re := by simp
  have him2 : (s - u).im = s.im - u.im := by simp
  have hsq : ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ^ 2 < ‖s - u‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
      Complex.normSq_apply, Complex.normSq_apply, hre1, him1, hre2, him2]
    nlinarith [sq_nonneg (s.im - u.im)]
  have h : (fun z : ℂ => ‖z‖)
      ((1 : ℂ) + (s.im : ℂ) * Complex.I - u) ≤ ‖s - u‖ := by
    have h' := (sq_lt_sq.mp hsq).le
    rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)] at h'
  exact h

/-- **Quadratic far bound.**  For `1 < Re s`, `Re u < 1` and `u` outside the near disk,
`((1/(s-u))²).re ≥ -((1+4/δ²)/(1+‖s-u‖²))`. -/
theorem quadFar_re_bound {s u : ℂ} {δ : ℝ} (hδ : 0 < δ) (hs : 1 < s.re) (hu : u.re < 1)
    (hfar : δ < ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖) :
    -((1 + 4 / δ ^ 2) / (1 + ‖s - u‖ ^ 2)) ≤ ((1 / (s - u)) ^ 2).re := by
  have hle := nearCenter_norm_le hs hu
  have hw : δ / 2 ≤ ‖s - u‖ := by linarith
  have h := (Work.ZeroFreeTables.P9.zetaQuadLocalBound hδ 1 hw).1
  simp only [Nat.cast_one, one_mul] at h
  rw [Complex.neg_re, mul_one_div] at h
  linarith [h]

/-- **Summability of the Lorentzian zero sum.**  For a non-principal primitive character,
the multiplicity-weighted sum `∑_u zeroMult(χ,u)/(1+‖s-u‖²)` is summable on `Re s > 1`. -/
theorem quadInvSq_summable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hprim : χ.IsPrimitive) {s : ℂ} (hs : 1 < s.re)
    (hsum : Summable (fun u : ℂ => (Work.LinnikContract.zeroMult χ u : ℂ) * (1 / (s - u)) ^ 2)) :
    Summable (fun u : ℂ => (Work.LinnikContract.zeroMult χ u : ℝ) * (1 / (1 + ‖s - u‖ ^ 2))) := by
  haveI : NeZero χ.conductor := ⟨DirichletCharacter.conductor_ne_zero χ⟩
  -- the point `s` itself is not a zero
  have hzero : Work.LinnikContract.zeroMult χ s = 0 := by
    by_contra hne
    have hmult : analyticOrderNatAt
        (DirichletCharacter.completedLFunction χ.primitiveCharacter) s ≠ 0 := by
      simpa only [Work.LinnikContract.zeroMult] using hne
    have hcomp : DirichletCharacter.completedLFunction χ.primitiveCharacter s = 0 :=
      apply_eq_zero_of_analyticOrderNatAt_ne_zero hmult
    exact Commons.NumberTheory.DirichletCharacter.completedLFunction_ne_zero_of_one_lt_re
      χ.primitiveCharacter hs hcomp
  refine Summable.of_norm_bounded hsum.norm (fun u => ?_)
  rw [Real.norm_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (by positivity)), norm_mul,
    Complex.norm_natCast]
  rcases eq_or_ne u s with rfl | hus
  · rw [hzero]; simp
  · have hTpos : 0 < ‖s - u‖ ^ 2 := by
      have hne : s - u ≠ 0 := sub_ne_zero.mpr (Ne.symm hus)
      have hpos : 0 < ‖s - u‖ := norm_pos_iff.mpr hne
      positivity
    have hnorm : ‖(1 / (s - u)) ^ 2‖ = 1 / ‖s - u‖ ^ 2 := by
      rw [norm_pow, norm_div, norm_one, div_pow, one_pow]
    rw [hnorm]
    exact mul_le_mul_of_nonneg_left
      (one_div_le_one_div_of_le hTpos (by linarith [sq_nonneg ‖s - u‖]))
      (Nat.cast_nonneg _)

end Work.ZeroFreeTables.P9.prim
