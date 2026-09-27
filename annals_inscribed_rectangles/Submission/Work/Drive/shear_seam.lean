import Mathlib
import Submission.Work.Drive.encodedShear

/-!
# The cross-shear commutes with the seam involution on the seam

`Work.Drive.shear` (`Submission/Work/Drive/encodedShear.lean`) is the cross-shear of the parameter square
by which the ends-clause genericity of the triple-intersection parity is transported
(`Drive/encodedGeneric.lean`, §2.1): its two triangular factors are

* `shear₁ q y = (y₀ + C(y₁) · hb y₀, y₁)` with `C(y₁) = a₀(1-2y₁) + a₂ hb y₁`,
* `shear₂ q z = (z₀, z₁ + D(z₀) · hb z₁)` with `D(z₀) = a₁(1-2z₀) + a₃ hb z₀`,

where `a = ballClamp q` and `hb x = x (1-x)`.

The geometric point of the whole construction is that the shear **descends to the quotient of the square
by the antipodal involution of its boundary**: it must commute with the seam involution
`seamInv2 y = (1-y₀, 1-y₁)` wherever `y` is on the seam `y₀ ∈ {0,1} ∨ y₁ ∈ {0,1}`.  This file proves
exactly that (`Work.Drive.shear_seam`), which is the hypothesis `hseam`-type input of the encoding.

The mechanism is the following pair of elementary identities, valid for **every** `x`:

* `hb (1-x) = hb x` (`hb_symm`, already in `encodedShear.lean`) and
  `(1-2(1-x)) = -(1-2x)`,

so that the coefficients `C`, `D` are **anti-symmetric**, `C(1-x) = -C(x)`, `D(1-x) = -D(x)`, at every
point where `hb x = 0` — and, by `hb_symm`, also at `1-x`:

  `C(1-x) + C(x) = 2 a₂ hb x`,  `D(1-x) + D(x) = 2 a₃ hb x`.

On the seam at least one of `hb y₀`, `hb y₁` vanishes, and `shear₁` maps the seam into the seam
(it changes `y₀` only by a multiple of `hb y₀`), so this anti-symmetry is available at **every** stage
of the composite.  That is why the shear moves *both* coordinates: the terms `a₂ hb y₁` in `C` are
exactly what would break the reflection identity `C(1-x) = -C(x)` off the seam, and they are killed by
the vanishing of `hb` in the other coordinate.
-/

namespace Work.Drive

/-- **A point of the seam has a vanishing `hb` in one of its two coordinates.**  The seam is
`y₀ ∈ {0,1} ∨ y₁ ∈ {0,1}` and `hb` vanishes at `0` and `1`.  This is the disjunction on which the
anti-symmetry of the shear coefficients is available. -/
lemma hb_disj_of_onSeam2 {y : EuclideanSpace ℝ (Fin 2)} (hy : onSeam2 y) :
    hb (y 0) = 0 ∨ hb (y 1) = 0 := by
  rcases hy with h | h | h | h <;> rw [h] <;> simp

/-- **The first factor of the shear preserves the seam** (in the form of the vanishing disjunction):
if `hb` vanishes in one coordinate of `z`, it vanishes in one coordinate of `shear₁ q z`, because
`shear₁` moves only the first coordinate, and only by a multiple of `hb` of that same coordinate. -/
lemma shear₁_hb_disj (q : EuclideanSpace ℝ (Fin 4)) (z : EuclideanSpace ℝ (Fin 2))
    (hz : hb (z 0) = 0 ∨ hb (z 1) = 0) :
    hb ((shear₁ q z) 0) = 0 ∨ hb ((shear₁ q z) 1) = 0 := by
  rcases hz with h | h
  · exact Or.inl (by simp only [shear₁_apply_zero, h, mul_zero, add_zero])
  · exact Or.inr (by rwa [shear₁_apply_one])

/-- **The first triangular factor commutes with the seam involution** wherever the vanishing
disjunction `hb z₀ = 0 ∨ hb z₁ = 0` holds: the identity `C(1-z₁) = -C(z₁)` that it needs is exactly
`2 a₂ hb z₁ = 0`, available by the disjunction. -/
lemma shear₁_seamInv2 (q : EuclideanSpace ℝ (Fin 4)) (z : EuclideanSpace ℝ (Fin 2))
    (hz : hb (z 0) = 0 ∨ hb (z 1) = 0) :
    shear₁ q (seamInv2 z) = seamInv2 (shear₁ q z) := by
  have h0 : (shear₁ q (seamInv2 z)) 0 = (seamInv2 (shear₁ q z)) 0 := by
    simp only [shear₁_apply_zero, seamInv2_apply_zero, seamInv2_apply_one, hb_symm]
    rcases hz with h | h <;> rw [h] <;> ring
  have h1 : (shear₁ q (seamInv2 z)) 1 = (seamInv2 (shear₁ q z)) 1 := by
    simp only [shear₁_apply_one, seamInv2_apply_one]
  ext i
  fin_cases i
  · exact h0
  · exact h1

/-- **The second triangular factor commutes with the seam involution** wherever the vanishing
disjunction holds: here the needed identity is `D(1-z₀) = -D(z₀)`, i.e. `2 a₃ hb z₀ = 0`. -/
lemma shear₂_seamInv2 (q : EuclideanSpace ℝ (Fin 4)) (z : EuclideanSpace ℝ (Fin 2))
    (hz : hb (z 0) = 0 ∨ hb (z 1) = 0) :
    shear₂ q (seamInv2 z) = seamInv2 (shear₂ q z) := by
  have h0 : (shear₂ q (seamInv2 z)) 0 = (seamInv2 (shear₂ q z)) 0 := by
    simp only [shear₂_apply_zero, seamInv2_apply_zero]
  have h1 : (shear₂ q (seamInv2 z)) 1 = (seamInv2 (shear₂ q z)) 1 := by
    simp only [shear₂_apply_one, seamInv2_apply_zero, seamInv2_apply_one, hb_symm]
    rcases hz with h | h <;> rw [h] <;> ring
  ext i
  fin_cases i
  · exact h0
  · exact h1

/-- **The cross-shear of the parameter square commutes with the seam involution on the seam**, i.e. it
descends to the antipodal quotient of the boundary of the square.  Both factors of `shear` commute with
`seamInv2` (by `shear₁_seamInv2`, `shear₂_seamInv2`), the intermediate point being again on the seam
by `shear₁_hb_disj`. -/
theorem shear_seam (q : EuclideanSpace ℝ (Fin 4)) {y : EuclideanSpace ℝ (Fin 2)}
    (hy : Work.Drive.onSeam2 y) :
    Work.Drive.shear q (Work.Drive.seamInv2 y) = Work.Drive.seamInv2 (Work.Drive.shear q y) := by
  have hz := hb_disj_of_onSeam2 hy
  have h1 := shear₁_seamInv2 q y hz
  have h2 := shear₂_seamInv2 q (shear₁ q y) (shear₁_hb_disj q y hz)
  calc shear q (seamInv2 y) = shear₂ q (shear₁ q (seamInv2 y)) := rfl
    _ = shear₂ q (seamInv2 (shear₁ q y)) := by rw [h1]
    _ = seamInv2 (shear₂ q (shear₁ q y)) := h2
    _ = seamInv2 (shear q y) := rfl

end Work.Drive
