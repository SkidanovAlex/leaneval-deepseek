import Mathlib

namespace Work.LinnikBurgess

/-- Second-order Taylor expansion (Hensel form) of a polynomial over a commutative
ring, evaluated in an `R`-algebra: there is a remainder `c` such that
`p (x + y) = c * y ^ 2 + p'(x) * y + p x`. -/
lemma aeval_exists_quadratic_remainder {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (p : Polynomial R) (x y : S) :
    ∃ c : S, c * y ^ 2 + Polynomial.aeval x p.derivative * y + Polynomial.aeval x p
      = Polynomial.aeval (x + y) p := by
  obtain ⟨c, hc⟩ := Polynomial.exists_mul_sq_add_linear_part_eq_eval_add
      (p.map (algebraMap R S)) x y
  rw [Polynomial.derivative_map] at hc
  refine ⟨c, ?_⟩
  rw [Polynomial.eval_map, Polynomial.eval_map, Polynomial.eval_map] at hc
  exact hc

/-- If `z` is a root of `P` and `‖u - z‖ < ‖P'(z)‖`, then in the non-archimedean norm of
`ℤ_[p]` one has `‖u - z‖ * ‖P'(z)‖ = ‖P(u)‖`. -/
theorem aeval_dist_eq_norm {p : ℕ} [Fact p.Prime] (P : Polynomial ℤ) {u z : ℤ_[p]} (hz : Polynomial.aeval z P = 0) (hlt : ‖u - z‖ < ‖Polynomial.aeval z P.derivative‖) : ‖u - z‖ * ‖Polynomial.aeval z P.derivative‖ = ‖Polynomial.aeval u P‖ := by
  obtain ⟨c, hc⟩ := aeval_exists_quadratic_remainder P z (u - z)
  rw [add_sub_cancel] at hc
  rw [hz, add_zero] at hc
  have hfac : Polynomial.aeval u P =
      (u - z) * (Polynomial.aeval z P.derivative + c * (u - z)) := by
    rw [← hc]; ring
  rw [hfac, norm_mul]
  have hcy : ‖c * (u - z)‖ ≤ ‖u - z‖ := by
    rw [norm_mul]
    calc ‖c‖ * ‖u - z‖ ≤ 1 * ‖u - z‖ :=
          mul_le_mul_of_nonneg_right (PadicInt.norm_le_one c) (norm_nonneg _)
      _ = ‖u - z‖ := one_mul _
  have hlt' : ‖c * (u - z)‖ < ‖Polynomial.aeval z P.derivative‖ := lt_of_le_of_lt hcy hlt
  have hA : ‖Polynomial.aeval z P.derivative + c * (u - z)‖
      = ‖Polynomial.aeval z P.derivative‖ := by
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt'.ne', max_eq_left hlt'.le]
  rw [hA]

end Work.LinnikBurgess
