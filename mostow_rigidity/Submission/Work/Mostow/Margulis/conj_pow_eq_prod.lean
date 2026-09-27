import Mathlib

namespace Work.Mostow.Margulis

/-- Conjugating a cyclic product: `(c * x)^m` expands as the ordered product of the
conjugates `x^i * c * (x^i)⁻¹` for `0 ≤ i < m`, followed by `x^m`. -/
theorem conj_pow_eq_prod {G : Type*} [Group G] (x c : G) (m : ℕ) :
    (c * x) ^ m = ((List.range m).map (fun i => x ^ i * c * (x ^ i)⁻¹)).prod * x ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, ih, List.range_succ, List.map_append, List.prod_append]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rw [pow_succ]
    group

end Work.Mostow.Margulis
