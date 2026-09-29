import Mathlib
import Submission.Work.APsi.defs
import Submission.Work.APsi.quad_neg_real

/-!
# The branch cut of the radicand of the slit map

For `0 < r < 1` the radicand

`slitQ r z = (1+r)^2 - 2(1-6r+r^2) z + (1+r)^2 z^2`

of the slit map `slit r` (see `Submission.Work.APsi.defs`, CDT arXiv:2408.15403) avoids the
branch cut `(-∞, 0]` on the closed unit disc, except for its two zeros, which lie on the unit
circle.  This is what makes `z ↦ (slitQ r z)^(1/2)` — and hence the slit map `slit r` — a
branch of a square root on the unit disc.

The key algebraic input is that the real quadratic `A z^2 - D z + A` with `A = (1+r)^2` and
`D = 2(1-6r+r^2)` has **negative discriminant**

`D^2 - 4A^2 = -64 r (1-r)^2 < 0`,

so that its two roots are a non-real conjugate pair of product `1`: if it takes a real
nonpositive value `-s` at `z`, then `z` is one of those roots and Vieta's relation
`z * conj z = 1 + s/A` gives `‖z‖^2 = 1 + s/A ≥ 1`.
-/

namespace Work.APsi

open Complex
open scoped ComplexConjugate

/-- `slitQ` is the real quadratic `A z^2 - D z + A` with `A = (1+r)^2`, `D = 2(1-6r+r^2)`. -/
theorem slitQ_quad (r : ℝ) (z : ℂ) :
    slitQ r z = (((1 + r) ^ 2 : ℝ) : ℂ) * z ^ 2 - ((2 * (1 - 6 * r + r ^ 2) : ℝ) : ℂ) * z
      + (((1 + r) ^ 2 : ℝ) : ℂ) := by
  simp only [slitQ]
  push_cast
  ring

/-- **Baseline analysis of `slitQ`.**  If `slitQ r z` is a nonpositive real, `slitQ r z = -s`
with `s ≥ 0`, then `‖z‖^2 = 1 + s/(1+r)^2 ≥ 1`:  `z` is on or outside the unit circle.

This is the "discriminant `4A^2 - D^2 = 64 r (1-r)^2 > 0`" computation for `0 < r < 1`. -/
theorem slitQ_neg_real (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) {z : ℂ} {s : ℝ}
    (h : slitQ r z = -(s : ℂ)) (hs : 0 ≤ s) : ‖z‖ ^ 2 = 1 + s / (1 + r) ^ 2 := by
  have hA : (0 : ℝ) < (1 + r) ^ 2 := by positivity
  have hD : (2 * (1 - 6 * r + r ^ 2)) ^ 2 < 4 * ((1 + r) ^ 2) ^ 2 := by
    have h1r : (0 : ℝ) < 1 - r := by linarith
    have key : ((1 + r) ^ 2) ^ 2 - (1 - 6 * r + r ^ 2) ^ 2 = 16 * r * (1 - r) ^ 2 := by ring
    have hpos : 0 < 16 * r * (1 - r) ^ 2 := by positivity
    linarith [key, hpos]
  rw [slitQ_quad] at h
  exact quad_neg_real hA hD h hs

/-- On the open unit disc the radicand `slitQ r` avoids the branch cut `(-∞, 0]`. -/
theorem slitQ_slitPlane_of_lt (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) {z : ℂ} (hz : ‖z‖ < 1) :
    slitQ r z ∈ Complex.slitPlane := by
  by_contra hmem
  rw [Complex.slitPlane, Set.mem_ofPred_eq, not_or] at hmem
  obtain ⟨hre, him⟩ := hmem
  have hre' : (slitQ r z).re ≤ 0 := le_of_not_gt hre
  have him' : (slitQ r z).im = 0 := not_not.mp him
  have hs : 0 ≤ -((slitQ r z).re) := by linarith
  have hval : slitQ r z = -(((-(slitQ r z).re : ℝ)) : ℂ) := by
    apply Complex.ext
    · simp
    · simp [him']
  have h1 := slitQ_neg_real r hr0 hr1 hval hs
  have h2 : ‖z‖ ^ 2 < 1 := by nlinarith [norm_nonneg z]
  rw [h1] at h2
  have h3 : 0 ≤ (-(slitQ r z).re) / (1 + r) ^ 2 := div_nonneg hs (by positivity)
  linarith

/-- On the closed unit disc the radicand `slitQ r` avoids the branch cut `(-∞, 0]`, except that
it may vanish (at the two points of the unit circle which are the zeros of `slitQ r`). -/
theorem slitQ_slitPlane_of_le_of_ne (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) {z : ℂ}
    (hz : ‖z‖ ≤ 1) (hne : slitQ r z ≠ 0) : slitQ r z ∈ Complex.slitPlane := by
  by_contra hmem
  rw [Complex.slitPlane, Set.mem_ofPred_eq, not_or] at hmem
  obtain ⟨hre, him⟩ := hmem
  have hre' : (slitQ r z).re ≤ 0 := le_of_not_gt hre
  have him' : (slitQ r z).im = 0 := not_not.mp him
  have hs : 0 ≤ -((slitQ r z).re) := by linarith
  have hval : slitQ r z = -(((-(slitQ r z).re : ℝ)) : ℂ) := by
    apply Complex.ext
    · simp
    · simp [him']
  have h1 := slitQ_neg_real r hr0 hr1 hval hs
  have hz2 : ‖z‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg z]
  have hApos : (0 : ℝ) < (1 + r) ^ 2 := by positivity
  have hs0 : -((slitQ r z).re) = 0 := by
    have hle : (-(slitQ r z).re) / (1 + r) ^ 2 ≤ 0 := by linarith [h1, hz2]
    rcases (div_nonpos_iff.mp hle) with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
    · linarith
    · linarith
  exact hne (by rw [hval, hs0, Complex.ofReal_zero, neg_zero])

/-- The zeros of `slitQ r` lie on the unit circle (they are the two critical values of the slit
map, `(D ± i√(4A²-D²))/(2A)` with `A = (1+r)^2`, `D = 2(1-6r+r^2)`). -/
theorem slitQ_eq_zero_norm (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) {z : ℂ}
    (h : slitQ r z = 0) : ‖z‖ = 1 := by
  have h1 := slitQ_neg_real r hr0 hr1 (s := 0) (by rw [h]; norm_num) le_rfl
  have h2 : ‖z‖ ^ 2 = 1 := by simpa using h1
  have h3 : (‖z‖ - 1) * (‖z‖ + 1) = 0 := by nlinarith [h2]
  have h4 : 0 < ‖z‖ + 1 := by linarith [norm_nonneg z]
  have h5 : ‖z‖ - 1 = 0 := (mul_eq_zero.mp h3).resolve_right (ne_of_gt h4)
  linarith

/-- `slitQ r` does not vanish on the open unit disc. -/
theorem slitQ_ne_zero_of_norm_lt_one (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) {z : ℂ}
    (hz : ‖z‖ < 1) : slitQ r z ≠ 0 := by
  intro h
  have h1 := slitQ_eq_zero_norm r hr0 hr1 h
  linarith

/-- **The branch cut of the slit radicand.**  For `0 < r < 1` the radicand `slitQ r` of the slit
map takes no value on the negative real axis: it maps the open unit disc into the slit plane and
the closed unit disc into the slit plane together with `0` (its two zeros, on the unit circle). -/
theorem slitQ_branch (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    (∀ z : ℂ, ‖z‖ < 1 → slitQ r z ∈ Complex.slitPlane) ∧
      (∀ z : ℂ, ‖z‖ ≤ 1 → slitQ r z ∈ Complex.slitPlane ∨ slitQ r z = 0) :=
  ⟨fun z hz => slitQ_slitPlane_of_lt r hr0 hr1 hz,
   fun z hz => by
    by_cases h : slitQ r z = 0
    · exact Or.inr h
    · exact Or.inl (slitQ_slitPlane_of_le_of_ne r hr0 hr1 hz h)⟩

end Work.APsi
