import Mathlib
import Submission.Work.WilC4aP.Basic
import Submission.Work.WilC4aP.PzAlg

namespace Work.WilC4aP

open Polynomial

/-! ## Two elementary algebraic helpers

Substituting `X ↦ c * X` in a linear factor `X - C (c * b)` pulls the scalar `c` out.
This is the algebraic heart of the Newton substitution `X ↦ t ^ a * X`: the leading
coefficient `t ^ (a * m)` on the right of the Newton identity is exactly what the `m`
scalars extracted from the `m` linear factors produce. -/

/-- `(X - C (c * b)).comp (C c * X) = C c * (X - C b)`. -/
lemma comp_C_mul_X_sub_C (c b : ℂ) :
    ((X - C (c * b)).comp (C c * X)) = C c * (X - C b : ℂ[X]) := by
  rw [Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp, mul_sub, ← Polynomial.C_mul]

/-- Composition of a product of `m` linear factors `X - C (c * b j)` with the substitution
`X ↦ c * X`: the scalar `c` is extracted from every factor. -/
lemma comp_prod_X_sub_C_mul (m : ℕ) (c : ℂ) (b : Fin m → ℂ) :
    (∏ j, (X - C (c * b j))).comp (C c * X) = (C c) ^ m * ∏ j, (X - C (b j) : ℂ[X]) := by
  rw [Polynomial.prod_comp Finset.univ (fun j : Fin m => X - C (c * b j)) (C c * X)]
  have hcongr : (∏ j : Fin m, (X - C (c * b j)).comp (C c * X)) =
      ∏ j : Fin m, C c * (X - C (b j) : ℂ[X]) :=
    Finset.prod_congr rfl (fun j _ => comp_C_mul_X_sub_C c (b j))
  rw [hcongr, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- For `0 ≤ x ≤ 1` and `N ≥ 1`, `x ^ N ≤ x`. -/
private lemma pow_le_self_of_le_one {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) {N : ℕ} (hN : 0 < N) :
    x ^ N ≤ x := by
  simpa using pow_le_pow_of_le_one (n := N) (m := 1) hx0 hx1 hN

lemma branches_newton {m : ℕ} {P Q : Polynomial (ℂ → ℂ)} {q a : ℕ} (hq : 0 < q) (ha : 0 < a)
    (h0 : Pz P 0 = Polynomial.X ^ m) {N : ℕ} (hN : 0 < N) (η : Fin m → ℂ → ℂ) {ρ : ℝ} (hρ : 0 < ρ)
    (hid : ∀ t ∈ Metric.ball (0 : ℂ) ρ,
      (Pz P (t ^ q)).comp (Polynomial.C (t ^ a) * Polynomial.X) =
        Polynomial.C (t ^ (a * m)) * Pz Q t)
    (hfact : ∀ t ∈ Metric.ball (0 : ℂ) ρ, Pz Q (t ^ N) = ∏ j, (Polynomial.X - Polynomial.C (η j t))) :
    ∃ ρ', 0 < ρ' ∧ ∀ u ∈ Metric.ball (0 : ℂ) ρ',
      Pz P (u ^ (q * N)) = ∏ j, (Polynomial.X - Polynomial.C (u ^ (a * N) * η j u)) := by
  -- The factorization holds on the disk of radius `min ρ 1`: for `‖u‖ ≤ 1`, `‖u ^ N‖ < ρ`.
  refine ⟨min ρ 1, lt_min hρ zero_lt_one, ?_⟩
  intro u hu
  have hu_lt : ‖u‖ < min ρ 1 := by
    have h := Metric.mem_ball.mp hu
    simpa [dist_eq_norm] using h
  have huρ : ‖u‖ < ρ := lt_of_lt_of_le hu_lt (min_le_left _ _)
  have hu1 : ‖u‖ ≤ 1 := le_of_lt (lt_of_lt_of_le hu_lt (min_le_right _ _))
  have hmem : u ∈ Metric.ball (0 : ℂ) ρ := by
    rw [Metric.mem_ball, dist_eq_norm]; simpa using huρ
  have hnorm : ‖u ^ N‖ ≤ ‖u‖ := by
    rw [norm_pow]
    exact pow_le_self_of_le_one (norm_nonneg u) hu1 hN
  have hpow_in : u ^ N ∈ Metric.ball (0 : ℂ) ρ := by
    rw [Metric.mem_ball, dist_eq_norm]
    simpa using lt_of_le_of_lt hnorm huρ
  rcases eq_or_ne u 0 with hu0 | hune
  · -- `u = 0`: both sides are `X ^ m`.
    subst hu0
    rw [show (0 : ℂ) ^ (q * N) = 0 from zero_pow (Nat.mul_ne_zero hq.ne' hN.ne'), h0]
    have hzero : (∏ j : Fin m,
        (Polynomial.X - Polynomial.C ((0 : ℂ) ^ (a * N) * η j 0) : ℂ[X])) = Polynomial.X ^ m := by
      have he : (0 : ℂ) ^ (a * N) = 0 := zero_pow (Nat.mul_ne_zero ha.ne' hN.ne')
      have hprod : (∏ j : Fin m,
          (Polynomial.X - Polynomial.C ((0 : ℂ) ^ (a * N) * η j 0) : ℂ[X])) =
          ∏ _j : Fin m, (Polynomial.X : ℂ[X]) := by
        refine Finset.prod_congr rfl (fun j _ => ?_)
        rw [he, zero_mul, Polynomial.C_0, sub_zero]
      rw [hprod, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [hzero]
  · -- `u ≠ 0`: cancel the injective substitution `X ↦ u ^ (a * N) * X`.
    have hcnz : u ^ (a * N) ≠ 0 := pow_ne_zero _ hune
    suffices hkey : (Pz P (u ^ (q * N))).comp (C (u ^ (a * N)) * X) =
        (∏ j, (X - C (u ^ (a * N) * η j u))).comp (C (u ^ (a * N)) * X) by
      exact comp_C_mul_X_injective hcnz hkey
    rw [comp_prod_X_sub_C_mul m (u ^ (a * N)) (fun j => η j u)]
    -- Newton's identity at `t = u ^ N`, together with the factorization of `Q` at `u`.
    have hh := hid (u ^ N) hpow_in
    have e1 : (u ^ N) ^ q = u ^ (q * N) := by
      rw [(pow_mul u N q).symm, Nat.mul_comm N q]
    have e2 : (u ^ N) ^ a = u ^ (a * N) := by
      rw [(pow_mul u N a).symm, Nat.mul_comm N a]
    have e3 : (u ^ N) ^ (a * m) = (u ^ (a * N)) ^ m := by
      rw [(pow_mul u N (a * m)).symm, show N * (a * m) = (a * N) * m from by ring,
        pow_mul u (a * N) m]
    rw [e1, e2, e3, hfact u hmem] at hh
    rw [hh, C_pow]

end Work.WilC4aP
