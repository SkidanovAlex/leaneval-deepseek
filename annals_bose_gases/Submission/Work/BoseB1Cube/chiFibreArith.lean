import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# A three-variable arithmetic lemma for the cube-chapter fibre estimates

We prove, for `m j > 0`, `0 ≤ e j` and `e j ≤ (2/7) * m j`,

`∏ j, m j ≤ 4 * ∏ j, (m j - e j) - 3 * ∏ j, (m j - 2 * e j)`.

Writing `x j = e j / m j ∈ [0, 2/7]` and `M = ∏ j, m j > 0`, the claim is equivalent to

`1 ≤ 4 * ∏ j, (1 - x j) - 3 * ∏ j, (1 - 2 * x j)`.

The function `G x = 4 * ∏ (1 - x j) - 3 * ∏ (1 - 2 x j) - 1` is **multilinear**
(affine in each variable separately), hence its minimum on the box `[0, 2/7]^3` is
attained at a vertex, where `G = 4 (5/7)^k - 3 (3/7)^k - 1 ≥ 0` (`k = 0,1,2,3` gives
`0, 4/7, 24/49, 76/343`).  We make this explicit with the multilinear (Möbius)
interpolation identity on the cube `[0,1]^3`: for `t j = (7/2) x j ∈ [0,1]`,

`343 * (4 ∏ (1 - (2/7) t) - 3 ∏ (1 - (4/7) t))
   = 343 + 196 * (Σ t_i (1-t_j)(1-t_k)) + 168 * (Σ t_i t_j (1 - t_k)) + 76 * t_1 t_2 t_3`,

a polynomial identity (checked by `ring`) whose right-hand side is manifestly `≥ 343`
because every summand is a product of nonnegative factors.

Why `2/7`: the vertex values above are exactly `4 (5/7)^k - 3 (3/7)^k`; the corner
`k = 3` gives the smallest positive one, `419/343 > 1`.  (For `n ≥ 4` variables the
analogous statement is false, so the numerics `3` and `2/7` are genuinely coupled.)
-/

namespace Work.BoseB1Cube

/-- Pointwise clearing of the denominator `a`: `a - b = a * (1 - b / a)`. -/
private lemma fac1 (a b : ℝ) (ha : a ≠ 0) : a - b = a * (1 - b / a) := by
  field_simp

/-- Pointwise clearing of the denominator `a`: `a - 2 * b = a * (1 - 2 * (b / a))`. -/
private lemma fac2 (a b : ℝ) (ha : a ≠ 0) : a - 2 * b = a * (1 - 2 * (b / a)) := by
  field_simp

/-- The multilinear core, in the `t`-coordinates `t j = (7/2) x j ∈ [0,1]`:
`1 ≤ 4 ∏ (1 - (2/7) t) - 3 ∏ (1 - (4/7) t)`.

This is the interpolation identity of the module docstring: multiplying by `343`,
the difference of the two products equals `1 + (4/7)σ₁ - (32/49)σ₂ + (160/343)σ₃`,
whose vertex values `343, 539, 511, 419` (at `k = 0,1,2,3` coordinates equal to `1`)
are all `≥ 343`, and the interpolation weights `∏_{S} t ∏_{Sᶜ} (1-t)` are nonnegative
on `[0,1]^3`. -/
private lemma key_t (t1 t2 t3 : ℝ) (h1 : 0 ≤ t1) (h1' : t1 ≤ 1) (h2 : 0 ≤ t2) (h2' : t2 ≤ 1)
    (h3 : 0 ≤ t3) (h3' : t3 ≤ 1) :
    1 ≤ 4 * (1 - (2 / 7) * t1) * (1 - (2 / 7) * t2) * (1 - (2 / 7) * t3)
        - 3 * (1 - (4 / 7) * t1) * (1 - (4 / 7) * t2) * (1 - (4 / 7) * t3) := by
  -- the Möbius/multilinear interpolation identity, with vertex values `343, 539, 511, 419`
  have hid : 343 * (4 * (1 - (2 / 7) * t1) * (1 - (2 / 7) * t2) * (1 - (2 / 7) * t3)
        - 3 * (1 - (4 / 7) * t1) * (1 - (4 / 7) * t2) * (1 - (4 / 7) * t3))
      = 343 + 196 * (t1 * (1 - t2) * (1 - t3) + t2 * (1 - t1) * (1 - t3)
            + t3 * (1 - t1) * (1 - t2))
          + 168 * (t1 * t2 * (1 - t3) + t1 * t3 * (1 - t2) + t2 * t3 * (1 - t1))
          + 76 * (t1 * t2 * t3) := by
    ring
  -- every interpolation weight is a product of nonnegative factors
  have a1 : 0 ≤ t1 * (1 - t2) * (1 - t3) := by
    apply mul_nonneg; apply mul_nonneg <;> linarith; linarith
  have a2 : 0 ≤ t2 * (1 - t1) * (1 - t3) := by
    apply mul_nonneg; apply mul_nonneg <;> linarith; linarith
  have a3 : 0 ≤ t3 * (1 - t1) * (1 - t2) := by
    apply mul_nonneg; apply mul_nonneg <;> linarith; linarith
  have b1 : 0 ≤ t1 * t2 * (1 - t3) := by
    apply mul_nonneg; apply mul_nonneg <;> linarith; linarith
  have b2 : 0 ≤ t1 * t3 * (1 - t2) := by
    apply mul_nonneg; apply mul_nonneg <;> linarith; linarith
  have b3 : 0 ≤ t2 * t3 * (1 - t1) := by
    apply mul_nonneg; apply mul_nonneg <;> linarith; linarith
  have c : 0 ≤ t1 * t2 * t3 := by
    apply mul_nonneg; apply mul_nonneg <;> linarith; linarith
  nlinarith [hid, a1, a2, a3, b1, b2, b3, c]

/-- The `Fin 3` product form of the core inequality:
for `0 ≤ x j ≤ 2/7`, `1 ≤ 4 ∏ (1 - x j) - 3 ∏ (1 - 2 x j)`. -/
private lemma key_prod (x : Fin 3 → ℝ) (hx0 : ∀ j : Fin 3, 0 ≤ x j)
    (hxr : ∀ j : Fin 3, x j ≤ 2 / 7) :
    1 ≤ 4 * ∏ j : Fin 3, (1 - x j) - 3 * ∏ j : Fin 3, (1 - 2 * x j) := by
  have h := key_t (7 * x 0 / 2) (7 * x 1 / 2) (7 * x 2 / 2) (by linarith [hx0 0])
    (by linarith [hxr 0]) (by linarith [hx0 1]) (by linarith [hxr 1]) (by linarith [hx0 2])
    (by linarith [hxr 2])
  rw [Fin.prod_univ_three, Fin.prod_univ_three]
  ring_nf at h ⊢
  linarith

theorem chiFibreArith (m e : Fin 3 → ℝ) (hm : ∀ j : Fin 3, 0 < m j)
    (he0 : ∀ j : Fin 3, 0 ≤ e j) (he : ∀ j : Fin 3, e j ≤ (2 / 7) * m j) :
    ∏ j : Fin 3, m j ≤ 4 * ∏ j : Fin 3, (m j - e j) - 3 * ∏ j : Fin 3, (m j - 2 * e j) := by
  -- normalise: `x j = e j / m j ∈ [0, 2/7]`
  have hke := key_prod (fun j => e j / m j) (fun j => div_nonneg (he0 j) (le_of_lt (hm j)))
    (fun j => by
      rw [div_le_iff₀ (hm j)]
      linarith [he j])
  have hprod_pos : 0 < ∏ j : Fin 3, m j := Finset.prod_pos (fun j _ => hm j)
  -- factor `m j` out of both products
  have h1 : ∏ j : Fin 3, (m j - e j) = (∏ j : Fin 3, m j) * ∏ j : Fin 3, (1 - e j / m j) := by
    rw [Finset.prod_congr rfl (fun j _ => fac1 (m j) (e j) (ne_of_gt (hm j))),
      Finset.prod_mul_distrib]
  have h2 : ∏ j : Fin 3, (m j - 2 * e j)
      = (∏ j : Fin 3, m j) * ∏ j : Fin 3, (1 - 2 * (e j / m j)) := by
    rw [Finset.prod_congr rfl (fun j _ => fac2 (m j) (e j) (ne_of_gt (hm j))),
      Finset.prod_mul_distrib]
  rw [h1, h2]
  -- multiply the normalised inequality by the positive number `∏ m j`
  have := mul_le_mul_of_nonneg_left hke (le_of_lt hprod_pos)
  linarith

end Work.BoseB1Cube
