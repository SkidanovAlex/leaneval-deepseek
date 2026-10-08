/-
# Solving `torusAct cu p * q₁ = torusAct c2u p * q₂` for `p`

Peterfalvi II, Ch. VII §3: the element `p ∈ Q` is determined by the equation

`(c w) · p * (0, w) = (c²) · p * (c A, c)`

in the model `Q = SZ E` (`E = GF(q²)`, `q` even), where `torusAct a p = (a x, a σ a y)`
and the composition law is `(x,z)(y,u) = (x+y, z+u+x σ y)`.  Comparing coordinates gives

* `x`-coord: `c w x = c² x + c A`, whence `(c + w) x = A` (division by `c ≠ 0`, and
  `w - c = w + c` in characteristic two);
* `y`-coord: `c w σ(c) σ(w) y + w = c² σ(c)² y + c + c² x σ(c) σ(A)`, and using
  `c σ c = 1`, `σ w = w` this is `w² y + w = y + c + c x σ A`, i.e.
  `(w+1)² y = c + w + c x σ A`.

Multiplying the second relation by `c + w` and substituting `(c+w) x = A`, then
`A σ A = c + c⁻¹` gives `(c+w) (w+1)² y = (c+w)² + cAσA = c² + w² + c² + 1 = (w+1)²`,
and `(w+1)² ≠ 0` (as `w ≠ 1`) yields `y = (c+w)⁻¹`.

All the arithmetic is `linear_combination` over `E` with the characteristic-two relation
`2 = 0` and the two field relations `c σ c = 1`, `A σ A = c + c⁻¹` supplied explicitly.
-/
import Mathlib
import Submission.Work.PSU3.FMap

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PSU3.StageC

theorem sz_solve_torusAct {E : Type*} [Field E] [FrobeniusInvolution E] [CharP E 2]
    (p q₁ q₂ : Work.PSU3.SZ E) (A c w : E) (cu c2u : Eˣ)
    (hcu : (cu : E) = c * w) (hc2u : (c2u : E) = c ^ 2)
    (hq₁x : q₁.x = 0) (hq₁y : q₁.y = w) (hq₂x : q₂.x = c * A) (hq₂y : q₂.y = c)
    (hc0 : c ≠ 0) (hw0 : w ≠ 0) (hw1 : w ≠ 1) (hcw : c + w ≠ 0)
    (hcσ : c * Work.PSU3.σE c = 1) (hA : A * Work.PSU3.σE A = c + c⁻¹)
    (hwfix : Work.PSU3.σE w = w)
    (h : Work.PSU3.SZ.torusAct cu p * q₁ = Work.PSU3.SZ.torusAct c2u p * q₂) :
    p.x = A / (c + w) ∧ p.y = (c + w)⁻¹ := by
  have h2 : (2 : E) = 0 := CharTwo.two_eq_zero
  -- The `x`-coordinate of the identity `torusAct cu p * q₁ = torusAct c2u p * q₂`.
  have hx : c * w * p.x = c ^ 2 * p.x + c * A := by
    have hh := congrArg Work.PSU3.SZ.x h
    simp only [Work.PSU3.SZ.mul_x, Work.PSU3.SZ.torusAct_x, hcu, hc2u, hq₁x, hq₂x,
      add_zero] at hh
    linear_combination hh
  -- The `y`-coordinate of the same identity, with `σ` expanded.
  have hy : c * w * (Work.PSU3.σE c * Work.PSU3.σE w) * p.y + w
      = c ^ 2 * (Work.PSU3.σE c) ^ 2 * p.y + c
        + (c ^ 2 * p.x) * (Work.PSU3.σE c * Work.PSU3.σE A) := by
    have hh := congrArg Work.PSU3.SZ.y h
    simp only [Work.PSU3.SZ.mul_y, Work.PSU3.SZ.torusAct_x, Work.PSU3.SZ.torusAct_y,
      hcu, hc2u, hq₁x, hq₁y, hq₂x, hq₂y] at hh
    simp only [map_mul, map_pow, map_zero, mul_zero, add_zero] at hh
    linear_combination hh
  -- `(c + w) * p.x = A`, by dividing the `x`-relation by `c` (and `w - c = w + c`).
  have hstep1 : (c + w) * p.x = A := by
    have h1 : c * ((c + w) * p.x) = c * A := by linear_combination hx + c ^ 2 * p.x * h2
    exact mul_left_cancel₀ hc0 h1
  -- `(w+1)² * p.y = c + w + c * p.x * σ A`, using `c σ c = 1` and `σ w = w`.
  rw [hwfix] at hy
  have hstep2 : (w + 1) ^ 2 * p.y = c + w + c * p.x * Work.PSU3.σE A := by
    linear_combination hy
      + (-w ^ 2 * p.y + p.y * (c * Work.PSU3.σE c + 1) + c * p.x * Work.PSU3.σE A) * hcσ
      + (w * p.y + p.y - w) * h2
  -- The norm relation, cleared of the inverse: `c A σ A = c² + 1`.
  have hA' : c * A * Work.PSU3.σE A = c ^ 2 + 1 := by
    have hh := congrArg (fun t => c * t) hA
    simp only [mul_add, mul_inv_cancel₀ hc0] at hh
    linear_combination hh
  -- `(c + w) * (c + w + c * p.x * σ A) = (w+1)²`.
  have hkey2 : (c + w) * (c + w + c * p.x * Work.PSU3.σE A) = (w + 1) ^ 2 := by
    linear_combination c * Work.PSU3.σE A * hstep1 + hA' + (c ^ 2 + c * w - w) * h2
  have hw1' : w + 1 ≠ 0 := by
    rw [← CharTwo.sub_eq_add w 1, sub_ne_zero]
    exact hw1
  -- Hence `(w+1)² * ((c+w) * p.y) = (w+1)²`.
  have hkey : (w + 1) ^ 2 * ((c + w) * p.y) = (w + 1) ^ 2 := by
    have hh := congrArg (fun t => (c + w) * t) hstep2
    rw [hkey2] at hh
    linear_combination hh
  have hdy : (c + w) * p.y = 1 :=
    mul_left_cancel₀ (pow_ne_zero 2 hw1') (by simpa using hkey)
  exact ⟨(eq_div_iff hcw).mpr (by linear_combination hstep1),
    eq_inv_of_mul_eq_one_right hdy⟩

end Work.PSU3.StageC
