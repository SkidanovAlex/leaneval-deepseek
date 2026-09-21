import Mathlib
import Submission.Work.OddRadon.RadialDefs

/-!
# Injectivity of the two-power radial map on the positive quadrant

`radialMap n (R, r) = (R^{2n+2} + r^{2n+2}, R^{2n+1} - r^{2n+1})`, for the odd dimension
`d = 2n+1`.  The paper's Step 3 produces the radial functions `R, r` from the transformed
Radon data `(Φ, Ψ)` by *solving* this system; for that solution to be unique — hence for the
radial graph to be well defined — the map must be injective on the positive quadrant.

## The argument

Write `m = 2n+1` (odd, hence `x ↦ x^m` is strictly increasing on `ℝ`) and let

    S = R^{m+1} + r^{m+1},   D = R^m - r^m

be the two coordinates of the image.  Suppose `(R,r)` and `(R',r')` are two positive pairs
with the same image.  If `R < R'` then `R^m < R'^m`, and the equality `D = D'` forces
`r^m < r'^m`, hence `0 < r < r'`.  Then `R^{m+1} < R'^{m+1}` and `r^{m+1} < r'^{m+1}`
(powers with positive exponent are strictly increasing on the non-negative reals), summing to
`S < S'`, a contradiction.  The case `R' < R` is symmetric, so `R = R'`; then `D = D'` gives
`r^m = r'^m` and injectivity of `x ↦ x^m` gives `r = r'`.

No fractional powers are needed: everything is monotonicity of power maps.
-/

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace Pointwise Interval Topology

namespace Work.OddRadon

/-- **The two-power radial map is injective on the positive quadrant.**
For the odd dimension `d = 2n+1`, the data `(R^{d+1} + r^{d+1}, R^d - r^d)` determine the
positive pair `(R, r)`. -/
theorem radialMap_injOn (n : ℕ) :
    Set.InjOn (radialMap n) {p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2} := by
  rintro ⟨R, r⟩ ⟨hR, hr⟩ ⟨R', r'⟩ ⟨hR', hr'⟩ h
  simp only [radialMap, Prod.mk.injEq] at h
  obtain ⟨hS, hD⟩ := h
  -- `m = 2n+1` is odd, so `x ↦ x^m` is strictly increasing on `ℝ`.
  have hm : Odd (2 * n + 1) := ⟨n, by ring⟩
  have hmono : StrictMono (fun x : ℝ => x ^ (2 * n + 1)) := hm.strictMono_pow
  -- The first coordinates agree: a strict inequality in either direction is contradictory.
  have hR_eq : R = R' := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have h1 : R ^ (2 * n + 1) < R' ^ (2 * n + 1) := hmono hlt
      -- `D = D'` then forces `r^m < r'^m`, hence `r < r'`.
      have h2 : r ^ (2 * n + 1) < r' ^ (2 * n + 1) := by linarith
      have h3 : r < r' := hmono.lt_iff_lt.mp h2
      have h4 : R ^ (2 * n + 2) < R' ^ (2 * n + 2) :=
        pow_lt_pow_left₀ (n := 2 * n + 2) hlt (le_of_lt hR) (by omega)
      have h5 : r ^ (2 * n + 2) < r' ^ (2 * n + 2) :=
        pow_lt_pow_left₀ (n := 2 * n + 2) h3 (le_of_lt hr) (by omega)
      linarith
    · have h1 : R' ^ (2 * n + 1) < R ^ (2 * n + 1) := hmono hlt
      have h2 : r' ^ (2 * n + 1) < r ^ (2 * n + 1) := by linarith
      have h3 : r' < r := hmono.lt_iff_lt.mp h2
      have h4 : R' ^ (2 * n + 2) < R ^ (2 * n + 2) :=
        pow_lt_pow_left₀ (n := 2 * n + 2) hlt (le_of_lt hR') (by omega)
      have h5 : r' ^ (2 * n + 2) < r ^ (2 * n + 2) :=
        pow_lt_pow_left₀ (n := 2 * n + 2) h3 (le_of_lt hr') (by omega)
      linarith
  refine Prod.ext hR_eq ?_
  -- With `R = R'`, the second equation gives `r^m = r'^m`, and `x ↦ x^m` is injective.
  rw [hR_eq] at hD
  have h1 : r ^ (2 * n + 1) = r' ^ (2 * n + 1) := by linarith
  exact hmono.injective h1

end Work.OddRadon
