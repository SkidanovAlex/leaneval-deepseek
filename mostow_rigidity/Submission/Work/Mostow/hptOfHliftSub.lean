import Mathlib
import Submission.Work.Mostow.QIDefs
import Submission.Work.Mostow.hptOf_level
import Submission.Work.Mostow.StabHoroForm
import Submission.Work.Mostow.poAux
import Submission.Work.Mostow.Hyper

/-!
# The difference of the lifted horospherical points `hptOf ξ y D` and `hptOf ξ 0 D`

The point of ℍⁿ at horospherical level `D` at `ξ ∈ Sph n` with normalised flat coordinate `y`
is `hptOf ξ y D = A • ξ + D • y`, where `A = (1 + D²‖y‖²)/(2D) - D/2` and `y ⊥ ξ`.  Since the
spatial part of `hlift u` is `u` and its time part is `tpart u = √(1 + ‖u‖²)`, one computes

`hlift (hptOf ξ y D) = (A • ξ + D • y, A + D)`, `hlift (hptOf ξ 0 D) = (A₀ • ξ, A₀ + D)`

with `A₀ = 1/(2D) - D/2`.  Hence the difference has spatial part `(A - A₀) • ξ + D • y` and time
part `A - A₀`, and `A - A₀ = D‖y‖²/2`; this is exactly `(D‖y‖²/2) • θ_ξ + wvec (D • y)`.
-/

namespace Work.Mostow

open Submission.Mostow

theorem hptOfHliftSub {n : ℕ} (ξ y : Submission.Mostow.E n) (hξ : ξ ∈ Submission.Mostow.Sph n)
    (hy : inner ℝ y ξ = 0) (D : ℝ) (hD : 0 < D) :
    Submission.Mostow.hlift (Work.Mostow.hptOf ξ y D) - Submission.Mostow.hlift (Work.Mostow.hptOf ξ 0 D)
      = (D * ‖y‖ ^ 2 / 2) • Work.Mostow.theta ξ + Work.Mostow.wvec (D • y) := by
  -- `ξ` is a unit vector, and `y` is orthogonal to it.
  have hξ1 : inner ℝ ξ ξ = (1 : ℝ) := by
    have h1 : ‖ξ‖ = 1 := by simpa [Submission.Mostow.Sph, Metric.mem_sphere, dist_eq_norm] using hξ
    rw [real_inner_self_eq_norm_sq, h1]; norm_num
  have hyξ : inner ℝ ξ y = 0 := by rw [real_inner_comm]; exact hy
  have hξn : ‖ξ‖ ^ 2 = (1 : ℝ) := by rw [← real_inner_self_eq_norm_sq, hξ1]
  -- The time offset of `hptOf ξ y D`.
  set A : ℝ := (1 + D ^ 2 * ‖y‖ ^ 2) / (2 * D) - D / 2 with hA
  have hPt : Work.Mostow.hptOf ξ y D = A • ξ + D • y := by rw [Work.Mostow.hptOf, ← hA]
  have hnorm : ‖A • ξ + D • y‖ ^ 2 = A ^ 2 + D ^ 2 * ‖y‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      hξ1, hyξ, hy]
    rw [real_inner_self_eq_norm_sq y]
    ring
  have hkey : 1 + (A ^ 2 + D ^ 2 * ‖y‖ ^ 2) = (A + D) ^ 2 := by rw [hA]; field_simp; ring
  have hpos : 0 < A + D := by
    rw [hA]
    have h2 : (1 + D ^ 2 * ‖y‖ ^ 2) / (2 * D) - D / 2 + D =
        (1 + D ^ 2 * ‖y‖ ^ 2 + D ^ 2) / (2 * D) := by field_simp; ring
    rw [h2]; positivity
  have htpart : Submission.Mostow.tpart (Work.Mostow.hptOf ξ y D) = A + D := by
    rw [hPt, Submission.Mostow.tpart, hnorm, hkey, Real.sqrt_sq hpos.le]
  -- The same for `hptOf ξ 0 D = (1/(2D) - D/2) • ξ`.
  have hPt0 : Work.Mostow.hptOf ξ (0 : Submission.Mostow.E n) D = (1 / (2 * D) - D / 2) • ξ := by
    rw [Work.Mostow.hptOf]; simp
  have hnorm0 : ‖(1 / (2 * D) - D / 2) • ξ‖ ^ 2 = (1 / (2 * D) - D / 2) ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, mul_pow, hξn, mul_one, sq_abs]
  have hkey0 : 1 + (1 / (2 * D) - D / 2) ^ 2 = ((1 / (2 * D) - D / 2) + D) ^ 2 := by
    field_simp; ring
  have hpos0 : 0 < (1 / (2 * D) - D / 2) + D := by
    have h2 : (1 / (2 * D) - D / 2) + D = (1 + D ^ 2) / (2 * D) := by field_simp; ring
    rw [h2]; positivity
  have htpart0 : Submission.Mostow.tpart (Work.Mostow.hptOf ξ 0 D) = (1 / (2 * D) - D / 2) + D := by
    rw [hPt0, Submission.Mostow.tpart, hnorm0, hkey0, Real.sqrt_sq hpos0.le]
  -- Compare componentwise on `Fin n ⊕ Fin 1`.
  funext x
  rcases x with i | j
  · -- spatial component
    simp only [Pi.sub_apply, Submission.Mostow.hlift, Sum.elim_inl, hPt, hPt0,
      Pi.add_apply, Pi.smul_apply, WithLp.ofLp_add, WithLp.ofLp_smul,
      Work.Mostow.theta, Work.Mostow.wvec, smul_eq_mul]
    rw [hA]; field_simp; ring
  · -- time component
    simp only [Pi.sub_apply, Submission.Mostow.hlift, Sum.elim_inr, htpart, htpart0,
      Pi.add_apply, Pi.smul_apply, Work.Mostow.theta, Work.Mostow.wvec, smul_eq_mul]
    rw [hA]; field_simp; ring

end Work.Mostow
