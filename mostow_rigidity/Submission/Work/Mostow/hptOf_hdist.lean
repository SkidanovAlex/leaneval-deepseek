import Mathlib
import Submission.Work.Mostow.QIDefs

/-!
# The hyperbolic distance between two points of a horosphere

`Work.Mostow.hptOf ξ y D = ((1 + D²‖y‖²)/(2D) - D/2) • ξ + D • y` is the point of the
horosphere of level `D` at `ξ` whose (scaled) flat coordinate is `y` (`lev ξ (hptOf ξ y D) = D`,
`yc ξ (hptOf ξ y D) = y` for `y ⊥ ξ`).

Two such points, at the same level `D` and with flat coordinates differing by `y - y'`, are at
hyperbolic distance `arcosh (1 + (D‖y - y'‖)²/2)`: the horosphere is intrinsically flat, its
hyperbolic metric is `D²` times the Euclidean metric of the flat coordinate `y`, and two points of
a horosphere at flat distance `w` are at hyperbolic distance `2 arcsinh (w/2)`.

The proof is the announced computation in the chart model. Writing `A` (resp. `B`) for the
time offset `(1 + D²‖y‖²)/(2D) - D/2` of `y` (resp. `y'`), the point `hptOf ξ y D = A • ξ + D • y`
has `tpart` equal to `D + A` (both coordinates are orthogonal, and `1 + A² + D²‖y‖² = (D + A)²`),
so

`cc (hptOf ξ y D) (hptOf ξ y' D) = (D + A)(D + B) - (A B + D²⟪y,y'⟫)`
`  = D² + D(A + B) - D²⟪y,y'⟫ = 1 + D²‖y - y'‖²/2 = 1 + (D‖y - y'‖)²/2`.
-/

namespace Work.Mostow

open Submission.Mostow

theorem hptOf_hdist {n : ℕ} (ξ : Submission.Mostow.E n) (hξ : ξ ∈ Submission.Mostow.Sph n)
    (D : ℝ) (hD : 0 < D) (y y' : Submission.Mostow.E n)
    (hy : inner ℝ y ξ = 0) (hy' : inner ℝ y' ξ = 0) :
    Submission.Mostow.hdist (Work.Mostow.hptOf ξ y D) (Work.Mostow.hptOf ξ y' D)
      = Real.arcosh (1 + (D * ‖y - y'‖) ^ 2 / 2) := by
  -- `ξ` is a unit vector, and both `y` and `y'` are orthogonal to it.
  have hξξ : inner ℝ ξ ξ = (1 : ℝ) := by
    have h1 : ‖ξ‖ = 1 := by simpa [Sph, Metric.mem_sphere, dist_eq_norm] using hξ
    rw [real_inner_self_eq_norm_sq, h1]; norm_num
  have hyξ : inner ℝ ξ y = 0 := by rw [real_inner_comm, hy]
  have hy'ξ : inner ℝ ξ y' = 0 := by rw [real_inner_comm, hy']
  -- the time offsets of the two points
  set A : ℝ := (1 + D ^ 2 * ‖y‖ ^ 2) / (2 * D) - D / 2 with hA
  set B : ℝ := (1 + D ^ 2 * ‖y'‖ ^ 2) / (2 * D) - D / 2 with hB
  have hPt : hptOf ξ y D = A • ξ + D • y := by rw [hptOf, ← hA]
  have hPt' : hptOf ξ y' D = B • ξ + D • y' := by rw [hptOf, ← hB]
  -- the norm of a point of the horosphere, expressed through `A`
  have hPP : inner ℝ (A • ξ + D • y) (A • ξ + D • y) = A ^ 2 + D ^ 2 * ‖y‖ ^ 2 := by
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
    rw [hξξ, hyξ, hy, real_inner_self_eq_norm_sq y]
    ring
  have hPn : ‖A • ξ + D • y‖ ^ 2 = A ^ 2 + D ^ 2 * ‖y‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]; exact hPP
  have hkey : 1 + (A ^ 2 + D ^ 2 * ‖y‖ ^ 2) = (D + A) ^ 2 := by
    rw [hA]; field_simp; ring
  have hposA : 0 < D + A := by
    rw [hA]
    have h2 : D + ((1 + D ^ 2 * ‖y‖ ^ 2) / (2 * D) - D / 2) =
        (D ^ 2 * (1 + ‖y‖ ^ 2) + 1) / (2 * D) := by
      field_simp; ring
    rw [h2]; positivity
  have hT : tpart (A • ξ + D • y) = D + A := by
    rw [tpart, hPn, hkey, Real.sqrt_sq (le_of_lt hposA)]
  -- the same for `y'`
  have hPP' : inner ℝ (A • ξ + D • y) (B • ξ + D • y') = A * B + D ^ 2 * inner ℝ y y' := by
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
    rw [hξξ, hy'ξ, hy]
    ring
  have hP'n : ‖B • ξ + D • y'‖ ^ 2 = B ^ 2 + D ^ 2 * ‖y'‖ ^ 2 := by
    have h : inner ℝ (B • ξ + D • y') (B • ξ + D • y') = B ^ 2 + D ^ 2 * ‖y'‖ ^ 2 := by
      simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
      rw [hξξ, hy'ξ, hy', real_inner_self_eq_norm_sq y']
      ring
    rw [← real_inner_self_eq_norm_sq]; exact h
  have hkey' : 1 + (B ^ 2 + D ^ 2 * ‖y'‖ ^ 2) = (D + B) ^ 2 := by
    rw [hB]; field_simp; ring
  have hposB : 0 < D + B := by
    rw [hB]
    have h2 : D + ((1 + D ^ 2 * ‖y'‖ ^ 2) / (2 * D) - D / 2) =
        (D ^ 2 * (1 + ‖y'‖ ^ 2) + 1) / (2 * D) := by
      field_simp; ring
    rw [h2]; positivity
  have hT' : tpart (B • ξ + D • y') = D + B := by
    rw [tpart, hP'n, hkey', Real.sqrt_sq (le_of_lt hposB)]
  -- the argument of `arcosh`
  have harg : (D + A) * (D + B) - (A * B + D ^ 2 * inner ℝ y y') = 1 + (D * ‖y - y'‖) ^ 2 / 2 := by
    have hmul : (D * ‖y - y'‖) ^ 2 / 2 = D ^ 2 * ‖y - y'‖ ^ 2 / 2 := by ring
    rw [hmul, norm_sub_sq_real, hA, hB]
    field_simp
    ring
  rw [hdist, hPt, hPt', hT, hT', hPP', harg]

end Work.Mostow
