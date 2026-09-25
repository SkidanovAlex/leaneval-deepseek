import Mathlib

namespace Work.BourgainPlan.Maximal

open Polynomial Filter

/-- A nonzero integer polynomial of positive degree that is nonnegative on the naturals
has strictly positive leading coefficient. -/
theorem leadingCoeff_pos_of_nonneg (P : Polynomial ℤ)
    (hP : ∀ n : ℕ, 0 ≤ P.eval (n : ℤ)) (hd : 1 ≤ P.natDegree) :
    0 < P.leadingCoeff := by
  by_contra h
  push Not at h
  -- h : P.leadingCoeff ≤ 0
  -- Pass to `ℝ` by the injective ring hom `ℤ → ℝ`.
  set Q : Polynomial ℝ := P.map (Int.castRingHom ℝ) with hQ
  have hdeg : 0 < Q.degree := by
    rw [hQ, degree_map_eq_of_injective Int.cast_injective]
    exact natDegree_pos_iff_degree_pos.mp (by omega)
  have hlc : Q.leadingCoeff ≤ 0 := by
    rw [hQ, leadingCoeff_map_of_injective Int.cast_injective]
    change ((P.leadingCoeff : ℤ) : ℝ) ≤ 0
    exact_mod_cast h
  -- A real polynomial of positive degree with nonpositive leading coefficient
  -- tends to `atBot` at `+∞`; restricting to the naturals contradicts nonnegativity.
  have ht : Tendsto (fun n : ℕ => Q.eval (n : ℝ)) atTop atBot :=
    (Q.tendsto_atBot_of_leadingCoeff_nonpos hdeg hlc).comp tendsto_natCast_atTop_atTop
  obtain ⟨n, hn⟩ := (ht.eventually (eventually_lt_atBot (0 : ℝ))).exists
  have hnn : 0 ≤ Q.eval (n : ℝ) := by
    rw [hQ, eval_map]
    rw [show (n : ℝ) = ((n : ℤ) : ℝ) by push_cast; ring]
    rw [eval₂_at_intCast]
    change (0 : ℝ) ≤ ((P.eval (n : ℤ) : ℤ) : ℝ)
    exact_mod_cast hP n
  linarith

end Work.BourgainPlan.Maximal
