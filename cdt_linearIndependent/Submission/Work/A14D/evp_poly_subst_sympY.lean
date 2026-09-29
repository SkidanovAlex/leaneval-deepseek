import Mathlib
import Submission.Work.A14.defs
import Submission.Work.C17I.evp_poly
import Submission.Work.C17I.evp_sum
import Submission.Work.C17I.evp_poly_mul
import Submission.Work.CPull.evp_sympPhi
import Submission.Work.CPull.evp_subst

/-!
# `evp` of a substituted polynomial at the symmetrising coordinate `y`

`Work.CPull.evp f z = ∑' n, (coeff n f : ℂ) * z ^ n` (`Submission.Work.CPull.defs`), and the
symmetrising series is `Submission.CDT.sympY = X²/(X−1)`, whose value at `z` with `‖z‖ < 1` is
`yC z = z²/(z−1)` (`Work.CPull.evp_sympPhi`).

For a *polynomial* `p : ℚ[X]`, the substituted series `p.subst sympY` is the series of
`z ↦ p(y(z))`, and this file proves the identification on the whole open unit disc:

`evp (p.subst sympY) z = pAtY p z`  (`= p.eval₂ (algebraMap ℚ ℂ) (yC z)`) for `‖z‖ < 1`.

The engine is the generic substitution theorem `Work.CPull.evp_subst`, which needs
(i) `constantCoeff sympY = 0` (`Submission.CDT.coeff_sympY_zero`),
(ii) the absolute summability of the coefficients of `sympY` at `z`, which follows from the
explicit coefficients `0, 0, −1, −1, …` (`Work.CPull.coeff_sympY_eq`) and `‖z‖ < 1`, and
(iii) the absolute summability of the coefficients of `p` at the ℓ¹-mass of `sympY` — automatic
since `p` has finite support.  The value `evp p (evp sympY z)` is then a polynomial evaluation
(`Work.C17I.evp_poly`), i.e. `pAtY`.
-/

namespace Work.A14D

open PowerSeries

/-- The coefficient series of `sympY` is absolutely summable at `z` for `‖z‖ < 1`: its
coefficients are `0, 0, −1, −1, …`, so the series is dominated by `∑ ‖z‖^n`. -/
private lemma summable_norm_coeff_sympY (z : ℂ) (hz : ‖z‖ < 1) :
    Summable fun j : ℕ => ‖((PowerSeries.coeff j Submission.CDT.sympY : ℚ) : ℂ)‖ * ‖z‖ ^ j := by
  have hgeo : Summable fun j : ℕ => ‖z‖ ^ j := by
    have h1 : ‖(‖z‖ : ℝ)‖ < 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg z)]
      exact hz
    simpa using summable_geometric_of_norm_lt_one h1
  refine Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_) hgeo
  have hle : ‖((PowerSeries.coeff j Submission.CDT.sympY : ℚ) : ℂ)‖ ≤ 1 := by
    rw [Work.CPull.coeff_sympY_eq j]
    split_ifs <;> simp
  exact mul_le_of_le_one_left (by positivity) hle

/-- The coefficient series of a polynomial, weighted by the ℓ¹-mass of `sympY` at `z`, is
absolutely summable: the polynomial has finite support. -/
private lemma summable_norm_coeff_poly_mul (p : Polynomial ℚ) {S : ℝ} (_hS : 0 ≤ S) :
    Summable fun n : ℕ => ‖((PowerSeries.coeff n (p : PowerSeries ℚ) : ℚ) : ℂ)‖ * S ^ n := by
  refine summable_of_ne_finset_zero (s := p.support) (fun n hn => ?_)
  have h0 : p.coeff n = 0 := Polynomial.notMem_support_iff.mp hn
  simp [Polynomial.coeff_coe, h0]

theorem evp_poly_subst_sympY (p : Polynomial ℚ) {z : ℂ} (hz : ‖z‖ < 1) :
    Work.CPull.evp ((p : PowerSeries ℚ).subst Submission.CDT.sympY) z
      = Work.A14D.pAtY p z := by
  have hb0 : PowerSeries.constantCoeff Submission.CDT.sympY = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact Submission.CDT.coeff_sympY_zero
  have hb := summable_norm_coeff_sympY z hz
  have hS : 0 ≤ ∑' j : ℕ, ‖((PowerSeries.coeff j Submission.CDT.sympY : ℚ) : ℂ)‖ * ‖z‖ ^ j :=
    tsum_nonneg fun j => by positivity
  obtain ⟨-, hval⟩ := Work.CPull.evp_subst (f := (p : PowerSeries ℚ))
    (b := Submission.CDT.sympY) z hb0 hb (summable_norm_coeff_poly_mul p hS)
  rw [hval, Work.C17I.evp_poly, (Work.CPull.evp_sympPhi z hz).2]
  rfl

end Work.A14D
