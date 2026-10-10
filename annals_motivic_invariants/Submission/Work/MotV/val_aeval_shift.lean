import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotV

open Polynomial

/-!
# Valuations of `p.aeval a` for `a` close to a constant

If `v` is a valuation of `B` trivial on the constants `A`, `c : A` and `a : B` with
`v (a - algebraMap A B c) < 1`, and `p : A[X]` is a nonzero polynomial, then
`v (p.aeval a) = v (a - algebraMap A B c) ^ (p.comp (X + C c)).natTrailingDegree`:
the value of `p(a)` is the value of `a - c` raised to the multiplicity of `c` as a root
of `p` (the exponent `(p.comp (X + C c)).natTrailingDegree` is the order of vanishing of
the Taylor shift of `p` at `c`).

The proof goes through the auxiliary statement that for any `w` with `v w < 1` the value
of `P.aeval w` is `(v w) ^ P.natTrailingDegree`; that is proved by induction on the
trailing degree using `Polynomial.divX`.
-/

/-- The value of a constant of `A` is at most `1`. -/
private theorem val_algebraMap_le_one {A B Γ₀ : Type*} [CommSemiring A] [Ring B] [Algebra A B]
    [LinearOrderedCommMonoidWithZero Γ₀] {v : Valuation B Γ₀} [v.IsTrivialOn A] (c : A) :
    v (algebraMap A B c) ≤ 1 := by
  by_cases hc : c = 0
  · rw [hc, map_zero, Valuation.map_zero]
    exact zero_le
  · rw [Valuation.IsTrivialOn.eq_one c hc]

/-- A polynomial in an element `w` of value `≤ 1`, with coefficients of value `≤ 1`,
has value `≤ 1`. -/
private theorem val_aeval_le_one {A B Γ₀ : Type*} [CommSemiring A] [Ring B] [Algebra A B]
    [LinearOrderedCommMonoidWithZero Γ₀] {v : Valuation B Γ₀} [v.IsTrivialOn A] {w : B}
    (hw : v w ≤ 1) (R : Polynomial A) : v (R.aeval w) ≤ 1 := by
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range]
  apply Valuation.map_sum_le
  intro i _
  rw [map_mul, map_pow, mul_comm]
  exact mul_le_one' (pow_le_one₀ (zero_le : (0 : Γ₀) ≤ v w) hw) (val_algebraMap_le_one (R.coeff i))

/-- **Value of `P.aeval w` for `v w < 1`.**  For a nonzero polynomial `P` and an element
`w` with `v w < 1`, the value of `P.aeval w` is `(v w) ^ P.natTrailingDegree`: the lowest
order term of `P` at `w` dominates. -/
private theorem val_aeval_of_lt_one {A B Γ₀ : Type*} [CommSemiring A] [Ring B] [Algebra A B]
    [LinearOrderedCommMonoidWithZero Γ₀] {v : Valuation B Γ₀} [v.IsTrivialOn A] {w : B}
    (hw : v w < 1) {P : Polynomial A} (hP : P ≠ 0) :
    v (P.aeval w) = (v w) ^ P.natTrailingDegree := by
  have key : ∀ m, ∀ P : Polynomial A, P.natTrailingDegree = m → P ≠ 0 →
      v (P.aeval w) = (v w) ^ m := by
    intro m
    induction m with
    | zero =>
      intro P hPm hPne
      have hc0 : P.coeff 0 ≠ 0 := by
        rcases (Polynomial.natTrailingDegree_eq_zero.mp hPm) with h | h
        · exact absurd h hPne
        · exact h
      have hwit : P.aeval w = (P.divX).aeval w * w + algebraMap A B (P.coeff 0) := by
        conv_lhs => rw [← Polynomial.divX_mul_X_add P]
        rw [Polynomial.aeval_add, Polynomial.aeval_mul,
          Polynomial.aeval_X, Polynomial.aeval_C]
      have hlt : v ((P.divX).aeval w * w) < v (algebraMap A B (P.coeff 0)) := by
        rw [map_mul, Valuation.IsTrivialOn.eq_one _ hc0]
        calc v ((P.divX).aeval w) * v w ≤ 1 * v w :=
              mul_le_mul_left (val_aeval_le_one (le_of_lt hw) P.divX) (v w)
          _ = v w := one_mul _
          _ < 1 := hw
      rw [hwit, add_comm, Valuation.map_add_eq_of_lt_left v hlt,
        Valuation.IsTrivialOn.eq_one _ hc0, pow_zero]
    | succ m ih =>
      intro P hPm hPne
      have hne : P.natTrailingDegree ≠ 0 := by rw [hPm]; exact Nat.succ_ne_zero m
      have hc0 : P.coeff 0 = 0 := by
        by_contra hc
        exact hne ((Polynomial.natTrailingDegree_eq_zero).mpr (Or.inr hc))
      have hPX : P = P.divX * Polynomial.X := by
        have h := Polynomial.divX_mul_X_add P
        rw [hc0, Polynomial.C_0, add_zero] at h
        exact h.symm
      have hdivne : P.divX ≠ 0 := by
        intro h
        have h1 : P.coeff P.natTrailingDegree = 0 := by
          rw [hPm, ← Polynomial.coeff_divX (p := P) (n := m), h, Polynomial.coeff_zero]
        exact (Polynomial.coeff_natTrailingDegree_ne_zero).mpr hPne h1
      have hdivtd : (P.divX).natTrailingDegree = m := by
        apply le_antisymm
        · apply Polynomial.natTrailingDegree_le_of_ne_zero (n := m)
          rw [Polynomial.coeff_divX, ← hPm]
          exact (Polynomial.coeff_natTrailingDegree_ne_zero).mpr hPne
        · refine Polynomial.le_natTrailingDegree (n := m) hdivne ?_
          intro k hk
          rw [Polynomial.coeff_divX]
          apply Polynomial.coeff_eq_zero_of_lt_natTrailingDegree
          rw [hPm]; omega
      rw [hPX, Polynomial.aeval_mul, Polynomial.aeval_X, map_mul,
        ih P.divX hdivtd hdivne, pow_succ]
  exact key P.natTrailingDegree P rfl hP

theorem val_aeval_shift {A B Γ₀ : Type*} [CommSemiring A] [Ring B] [Algebra A B]
    [LinearOrderedCommMonoidWithZero Γ₀] {v : Valuation B Γ₀} [v.IsTrivialOn A] {a : B} {c : A}
    (h : v (a - algebraMap A B c) < 1) {p : Polynomial A} (hp : p ≠ 0) :
    v (p.aeval a)
      = (v (a - algebraMap A B c)) ^ (p.comp (Polynomial.X + Polynomial.C c)).natTrailingDegree := by
  have hP : p.comp (Polynomial.X + Polynomial.C c) ≠ 0 := by
    rw [← Polynomial.taylor_apply]
    exact fun hh => hp ((Polynomial.taylor_eq_zero c p).mp hh)
  have key : (p.comp (Polynomial.X + Polynomial.C c)).aeval (a - algebraMap A B c)
      = p.aeval a := by
    rw [Polynomial.aeval_comp]
    congr 1
    rw [Polynomial.aeval_add, Polynomial.aeval_X, Polynomial.aeval_C, sub_add_cancel]
  rw [← key]
  exact val_aeval_of_lt_one h hP

end Work.MotV
