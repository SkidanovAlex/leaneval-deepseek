import Mathlib
import Submission.Work.Mostow.QIDefs

/-!
# `levMid`: the Busemann level of the "midpoint" of two boundary points

For two distinct points `ξ ≠ η` of the boundary sphere `Sph n` of `ℍⁿ`, the point

`u = (√(2 (1 − ⟪ξ,η⟫)))⁻¹ • (ξ + η)`

(euclidean midpoint of `ξ` and `η`, rescaled) satisfies

`lev ξ u = lev η u = √((1 − ⟪ξ,η⟫)/2)`,

i.e. it is equidistant from the horospheres at `ξ` and at `η`; its common Busemann level is
`√((1−⟪ξ,η⟫)/2)`.

The proof is a direct computation in the chart: with `c = ⟪ξ,η⟫ < 1` one has
`⟪u,ξ⟫ = (1+c)/√(2(1−c))` and `tpart u = √(2/(1−c))`, hence
`lev ξ u = √(2/(1−c)) − (1+c)/√(2(1−c)) = √((1−c)/2)`.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

variable {n : ℕ}

/-- Elementary real identity behind `levMid`. -/
theorem levMid_arith (c : ℝ) (hc : c < 1) :
    Real.sqrt (2 / (1 - c)) - (1 + c) / Real.sqrt (2 * (1 - c)) = Real.sqrt ((1 - c) / 2) := by
  have h1 : (0:ℝ) < 1 - c := by linarith
  rw [Real.sqrt_div (by norm_num : (0:ℝ) ≤ 2) (1 - c),
      Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2) (1 - c),
      Real.sqrt_div (le_of_lt h1) (2:ℝ)]
  have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := by
    rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2) 2]; norm_num
  have hb2 : Real.sqrt (1 - c) * Real.sqrt (1 - c) = 1 - c := by
    rw [← Real.sqrt_mul (le_of_lt h1) (1 - c)]; rw [Real.sqrt_mul_self (le_of_lt h1)]
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  field_simp
  nlinarith [hsq, hb2]

/-- One half of `levMid`, stated with an arbitrary ordered pair of boundary points. -/
theorem levMid_aux {ξ η : E n} (hξ : ξ ∈ Sph n) (hη : η ∈ Sph n) (hne : ξ ≠ η) :
    lev ξ ((Real.sqrt (2 * (1 - inner ℝ ξ η)))⁻¹ • (ξ + η)) =
      Real.sqrt ((1 - inner ℝ ξ η) / 2) := by
  have hξn : ‖ξ‖ = 1 := by simpa [Sph, Metric.mem_sphere, dist_eq_norm] using hξ
  have hηn : ‖η‖ = 1 := by simpa [Sph, Metric.mem_sphere, dist_eq_norm] using hη
  have hc : inner ℝ ξ η < 1 := (inner_lt_one_iff_real_of_norm_eq_one hξn hηn).mpr hne
  have h1 : (0:ℝ) < 1 - inner ℝ ξ η := by linarith
  have ha_pos : 0 < Real.sqrt (2 * (1 - inner ℝ ξ η)) := Real.sqrt_pos.mpr (by linarith)
  have ha2 : Real.sqrt (2 * (1 - inner ℝ ξ η)) ^ 2 = 2 * (1 - inner ℝ ξ η) :=
    Real.sq_sqrt (by linarith)
  have hin : inner ℝ ((Real.sqrt (2 * (1 - inner ℝ ξ η)))⁻¹ • (ξ + η)) ξ
      = (1 + inner ℝ ξ η) / Real.sqrt (2 * (1 - inner ℝ ξ η)) := by
    rw [real_inner_smul_left, inner_add_left, real_inner_self_eq_norm_sq, hξn, real_inner_comm η ξ]
    ring
  have hnorm : ‖(Real.sqrt (2 * (1 - inner ℝ ξ η)))⁻¹ • (ξ + η)‖ ^ 2
      = 2 * (1 + inner ℝ ξ η) / (2 * (1 - inner ℝ ξ η)) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ha_pos), mul_pow,
        norm_add_sq_real, hξn, hηn, inv_pow, ha2]
    ring
  have htp : tpart ((Real.sqrt (2 * (1 - inner ℝ ξ η)))⁻¹ • (ξ + η))
      = Real.sqrt (2 / (1 - inner ℝ ξ η)) := by
    rw [tpart, hnorm]
    congr 1
    field_simp
    ring
  rw [lev, htp, hin]
  exact levMid_arith (inner ℝ ξ η) hc

theorem levMid {n : ℕ} {ξ η : Submission.Mostow.E n}
    (hξ : ξ ∈ Submission.Mostow.Sph n) (hη : η ∈ Submission.Mostow.Sph n) (hne : ξ ≠ η) :
    Work.Mostow.lev ξ ((Real.sqrt (2 * (1 - inner ℝ ξ η)))⁻¹ • (ξ + η)) =
        Real.sqrt ((1 - inner ℝ ξ η) / 2) ∧
    Work.Mostow.lev η ((Real.sqrt (2 * (1 - inner ℝ ξ η)))⁻¹ • (ξ + η)) =
        Real.sqrt ((1 - inner ℝ ξ η) / 2) := by
  refine ⟨levMid_aux hξ hη hne, ?_⟩
  simpa only [real_inner_comm ξ η, add_comm ξ η] using levMid_aux (n := n) hη hξ hne.symm

end Work.Mostow
