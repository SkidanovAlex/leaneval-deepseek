import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The `n`-fold map on the circle is a local isometry scaling distances by `n`

On the unit additive circle `UnitAddCircle = ℝ / ℤ`, for `n : ℕ` and `z w : UnitAddCircle`
satisfying `n * dist z w < 1/2`, the `n`-fold sum map is an isometry onto its image up to the
factor `n`:

`dist (n • z) (n • w) = n * dist z w`.

The point is that the inequality rules out the wrap-around: with `d = dist z w < 1/(2n)`,
the difference `z - w` has a representative at distance `d` from an integer `r`; scaling by `n`
keeps the "new" fractional part `n (z - w - r)` inside `(-1/2, 1/2)`, so that rounding does not
move and the quotient norm is simply `n` times as large.

## Main results

* `Work.LandLeaves.abs_sub_round_nsmul` : the underlying real statement, phrased with `round`.
* `Work.LandLeaves.nsmul_coe_eq` : `n • x = ↑(n * x)` on the circle.
* `Work.LandLeaves.dist_nsmul_eq_of_lt_half` : the requested statement.
-/

namespace Work.LandLeaves

/-- Real form of the local isometry statement: if `n * |x - round x| < 1/2` then rounding
commutes with multiplication by the natural number `n`, in the form that the distance of
`n * x` from its nearest integer is `n` times the distance of `x` from its nearest integer. -/
lemma abs_sub_round_nsmul {n : ℕ} {x : ℝ}
    (h : (n : ℝ) * |x - (round x : ℝ)| < 1 / 2) :
    |(n : ℝ) * x - (round ((n : ℝ) * x) : ℝ)| = (n : ℝ) * |x - (round x : ℝ)| := by
  have habs : |(n : ℝ) * (x - (round x : ℝ))| < 1 / 2 := by
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg n)]
    exact h
  have hround : round ((n : ℝ) * (x - (round x : ℝ))) = 0 := by
    rw [round_eq_zero_iff]
    exact ⟨by linarith [(abs_lt.mp habs).1], (abs_lt.mp habs).2⟩
  have hkey : round ((n : ℝ) * x) = n * round x := by
    have : (n : ℝ) * x = (n : ℝ) * (x - (round x : ℝ)) + ((n * round x : ℤ) : ℝ) := by
      push_cast; ring
    rw [this, round_add_intCast, hround, zero_add]
  rw [hkey]
  have hsub : (n : ℝ) * x - ((n * round x : ℤ) : ℝ) = (n : ℝ) * (x - (round x : ℝ)) := by
    push_cast; ring
  rw [hsub, abs_mul, abs_of_nonneg (Nat.cast_nonneg n)]

/-- On the unit circle, the `n`-fold multiple of the class of `x` is the class of `n * x`. -/
lemma nsmul_coe_eq (n : ℕ) (x : ℝ) :
    n • (x : UnitAddCircle) = ((n : ℝ) * x : UnitAddCircle) := by
  rw [← AddCircle.coe_nsmul (1 : ℝ) (n := n) (x := x), nsmul_eq_mul]

/-- On the unit additive circle, if `n * dist z w < 1/2` then the `n`-fold map is an isometry
from the pair `(z, w)` to `(n • z, n • w)`, up to the factor `n`. -/
theorem dist_nsmul_eq_of_lt_half {n : ℕ} {z w : UnitAddCircle}
    (h : (n : ℝ) * dist z w < 1 / 2) :
    dist (n • z) (n • w) = (n : ℝ) * dist z w := by
  obtain ⟨x, -, rfl⟩ := AddCircle.eq_coe_Ico (p := (1 : ℝ)) z
  obtain ⟨y, -, rfl⟩ := AddCircle.eq_coe_Ico (p := (1 : ℝ)) w
  have hd : dist (↑x : UnitAddCircle) (↑y) = |x - y - (round (x - y) : ℝ)| := by
    rw [dist_eq_norm, ← AddCircle.coe_sub (1 : ℝ) x y, UnitAddCircle.norm_eq]
  rw [hd] at h
  have key := abs_sub_round_nsmul (n := n) (x := x - y) h
  rw [nsmul_coe_eq n x, nsmul_coe_eq n y]
  rw [dist_eq_norm, dist_eq_norm]
  rw [← AddCircle.coe_sub (1 : ℝ), ← AddCircle.coe_sub (1 : ℝ)]
  rw [← mul_sub]
  rw [UnitAddCircle.norm_eq, UnitAddCircle.norm_eq]
  exact key

end Work.LandLeaves
