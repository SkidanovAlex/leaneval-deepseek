import Mathlib
import Submission.Work.Mostow.QIDefs

/-!
# The point of prescribed level and flat coordinate at a boundary point

`Work.Mostow.hptOf ξ y D` is the point of ℍⁿ at horospherical level `D` at `ξ ∈ Sph n` whose
normalised flat coordinate in the horosphere at `ξ` is `y`:

`hptOf ξ y D = ((1 + D²‖y‖²)/(2D) - D/2) • ξ + D • y`.

This file proves that this is indeed the case, for `D > 0` and `y ⊥ ξ`: the Busemann level
`lev ξ (hptOf ξ y D)` equals `D` and the flat coordinate `yc ξ (hptOf ξ y D)` equals `y`.

Everything is the hyperboloid computation `cosh`-free: writing `A = (1 + D²‖y‖²)/(2D) - D/2`
and using `⟨ξ,ξ⟩ = 1`, `⟨y,ξ⟩ = 0`, one gets `⟨hptOf, ξ⟩ = A`, `‖hptOf‖² = A² + D²‖y‖²`, hence
`1 + ‖hptOf‖² = (A + D)²` with `A + D > 0`, so `tpart (hptOf) = A + D` and
`lev ξ (hptOf) = tpart (hptOf) - ⟨hptOf, ξ⟩ = D`; finally `wc ξ (hptOf) = hptOf - A • ξ = D • y`,
so `yc ξ (hptOf) = D⁻¹ • (D • y) = y`.
-/

namespace Work.Mostow

open Submission.Mostow

/-- The self-pairing of a point of the boundary sphere: `⟨ξ,ξ⟩ = 1`. -/
lemma hptOf_level_aux_inner_self {n : ℕ} {ξ : E n} (hξ : ξ ∈ Sph n) : inner ℝ ξ ξ = 1 := by
  rw [real_inner_self_eq_norm_sq]
  have h : ‖ξ‖ = 1 := by simpa [Sph, Metric.mem_sphere, dist_eq_norm] using hξ
  rw [h, one_pow]

theorem hptOf_level {n : ℕ} (ξ : Submission.Mostow.E n) (hξ : ξ ∈ Submission.Mostow.Sph n)
    (D : ℝ) (hD : 0 < D) (y : Submission.Mostow.E n) (hy : inner ℝ y ξ = 0) :
    Work.Mostow.lev ξ (Work.Mostow.hptOf ξ y D) = D ∧
      Work.Mostow.yc ξ (Work.Mostow.hptOf ξ y D) = y := by
  set A : ℝ := (1 + D ^ 2 * ‖y‖ ^ 2) / (2 * D) - D / 2 with hA
  have hDne : D ≠ 0 := ne_of_gt hD
  have hξ1 : inner ℝ ξ ξ = 1 := hptOf_level_aux_inner_self hξ
  have hy' : inner ℝ ξ y = 0 := by rw [real_inner_comm]; exact hy
  -- The explicit form of the point as a combination of `ξ` and `y`.
  have hpt : hptOf ξ y D = A • ξ + D • y := by rw [hptOf, ← hA]
  -- Its pairing with `ξ` is the coefficient of `ξ`.
  have hinner : inner ℝ (hptOf ξ y D) ξ = A := by
    rw [hpt]
    simp only [inner_add_left, real_inner_smul_left, hξ1, hy, mul_one, mul_zero, add_zero]
  -- Its squared norm.
  have h2 : inner ℝ (A • ξ + D • y) (A • ξ + D • y) = A ^ 2 + D ^ 2 * inner ℝ y y := by
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      hξ1, hy, hy']
    ring
  have hnorm : ‖hptOf ξ y D‖ ^ 2 = A ^ 2 + D ^ 2 * ‖y‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq (hptOf ξ y D), hpt, h2, real_inner_self_eq_norm_sq y]
  -- The Pythagorean identity `1 + ‖hptOf‖² = (A + D)²`, with `A + D > 0`.
  have hsq : 1 + ‖hptOf ξ y D‖ ^ 2 = (A + D) ^ 2 := by
    rw [hnorm, hA]; field_simp; ring
  have hpos : 0 < A + D := by
    have : A + D = (1 + D ^ 2 * ‖y‖ ^ 2) / (2 * D) + D / 2 := by rw [hA]; ring
    rw [this]
    positivity
  have htpart : tpart (hptOf ξ y D) = A + D := by
    rw [tpart, hsq, Real.sqrt_sq hpos.le]
  have hlev : lev ξ (hptOf ξ y D) = D := by rw [lev, htpart, hinner]; ring
  have hwc : wc ξ (hptOf ξ y D) = D • y := by
    rw [wc, hinner, hpt]; abel
  constructor
  · exact hlev
  · rw [yc, hlev, hwc, inv_smul_smul₀ hDne]

end Work.Mostow
