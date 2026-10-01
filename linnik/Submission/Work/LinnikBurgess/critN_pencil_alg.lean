import Mathlib

namespace Work.LinnikBurgess

/-- Expansion of a product of three factors `P + C (v l)`. -/
theorem prod_three_C_add {R : Type*} [CommRing R] (P : Polynomial R) (v : Fin 3 → R) :
    (∏ l : Fin 3, (P + Polynomial.C (v l)))
      = P ^ 3 + Polynomial.C (v 0 + v 1 + v 2) * P ^ 2
        + Polynomial.C (v 0 * v 1 + v 0 * v 2 + v 1 * v 2) * P
        + Polynomial.C (v 0 * v 1 * v 2) := by
  rw [Fin.prod_univ_three]; simp only [map_add, map_mul]; ring

theorem critN_pencil_alg {R : Type*} [CommRing R] (z : R) (r s : Fin 3 → R) (c : R)
    (h1 : r 0 + r 1 + r 2 = c * (s 0 + s 1 + s 2))
    (h2 : r 0 * r 1 + r 0 * r 2 + r 1 * r 2 = c * (s 0 * s 1 + s 0 * s 2 + s 1 * s 2))
    (h3 : r 0 * r 1 * r 2 = c * (s 0 * s 1 * s 2)) :
    (∏ l : Fin 3, (Polynomial.X - Polynomial.C z + Polynomial.C (r l)))
      = Polynomial.C c * (∏ l : Fin 3, (Polynomial.X - Polynomial.C z + Polynomial.C (s l)))
        + Polynomial.C (1 - c) * (Polynomial.X - Polynomial.C z) ^ 3 := by
  rw [prod_three_C_add (Polynomial.X - Polynomial.C z) r,
      prod_three_C_add (Polynomial.X - Polynomial.C z) s, h1, h2, h3]
  simp only [map_add, map_mul, map_sub, map_one]
  ring

end Work.LinnikBurgess
