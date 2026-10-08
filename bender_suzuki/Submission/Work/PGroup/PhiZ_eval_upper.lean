import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PGroup

/-- Evaluating the `D`-th cyclotomic polynomial at an integer `M ≥ 2` gives a value
strictly smaller than `M ^ D`.

The point is that `Φ_D ∣ X ^ D - 1`, and for `M ≥ 2` the value `Φ_D(M)` is a positive
integer, hence a positive divisor of the positive number `M ^ D - 1`; therefore
`Φ_D(M) ≤ M ^ D - 1 < M ^ D`. -/
lemma PhiZ_eval_upper {D M : ℕ} (hD : 1 ≤ D) (hM : 2 ≤ M) :
    (Polynomial.cyclotomic D ℤ).eval (M : ℤ) < (M : ℤ) ^ D := by
  -- `Φ_D` divides `X ^ D - 1`, hence so do the evaluated values.
  have hdvd : Polynomial.cyclotomic D ℤ ∣ Polynomial.X ^ D - 1 :=
    Polynomial.cyclotomic.dvd_X_pow_sub_one D ℤ
  have hdiv : (Polynomial.cyclotomic D ℤ).eval (M : ℤ) ∣ (M : ℤ) ^ D - 1 := by
    obtain ⟨r, hr⟩ := hdvd
    refine ⟨r.eval (M : ℤ), ?_⟩
    have := congr_arg (Polynomial.eval (M : ℤ)) hr
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one,
      Polynomial.eval_mul] at this ⊢
    simpa using this
  -- `Φ_D(M) > 0` for `M > 1`.
  have hpos : 0 < (Polynomial.cyclotomic D ℤ).eval (M : ℤ) :=
    Polynomial.cyclotomic_pos' D (x := (M : ℤ)) (by exact_mod_cast hM)
  -- `M ^ D ≥ 2`, so `M ^ D - 1` is positive.
  have hMD : (2 : ℤ) ≤ (M : ℤ) ^ D := by
    have h1 : 1 < M ^ D := Nat.one_lt_pow (by omega) (by omega : 1 < M)
    exact_mod_cast (show (2 : ℕ) ≤ M ^ D from h1)
  have hle : (Polynomial.cyclotomic D ℤ).eval (M : ℤ) ≤ (M : ℤ) ^ D - 1 :=
    Int.le_of_dvd (by linarith) hdiv
  linarith

end Work.PGroup
