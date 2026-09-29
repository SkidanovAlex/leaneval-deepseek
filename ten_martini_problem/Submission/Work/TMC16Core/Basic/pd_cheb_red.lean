/-
# Reduction of a symmetric bivariate polynomial to one variable

Let `P ∈ ℂ[X][X]`, written `P(x, z)` with `x` the *outer* variable (the `sin` variable of the
Chebyshev setup) and `z` the coefficient variable (the `cos` variable).  Assume

* `P` is even in `x`: `P(-x, z) = P(x, z)`, and
* `P` has total degree at most `k`: the coefficient of `x^i` has `z`-degree at most `k - i`.

Then there is `Q ∈ ℂ[X]` of degree at most `k` with `Q(c) = P(s, c)` for every pair
`(c, s)` with `s² = 1 - c²`.

The proof is a strong induction on the outer degree.  Writing `n = P.natDegree`, symmetry
forces `n` to be even (`Q` must not contain odd powers of `x`); removing the leading term
`leadingCoeff · x^n` leaves an even polynomial of strictly smaller degree, to which the
induction hypothesis applies, and the removed term contributes `leadingCoeff · (1 - X²)^(n/2)`
to the answer.  The degree estimate uses `deg (c · (1 - X²)^m) ≤ deg c + 2m`.
-/
import Mathlib

namespace Work.TMC16Core.Basic

lemma pd_cheb_red_even_natDegree (P : Polynomial (Polynomial ℂ))
    (hsym : P.comp (-Polynomial.X) = P) (hP : P ≠ 0) : Even P.natDegree := by
  have hlc : P.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP
  have h1' : P.leadingCoeff = (-1 : Polynomial ℂ) ^ P.natDegree * P.leadingCoeff := by
    rw [← Polynomial.comp_neg_X_leadingCoeff_eq P, hsym]
  have h1 : (-1 : Polynomial ℂ) ^ P.natDegree * P.leadingCoeff = 1 * P.leadingCoeff := by
    rw [one_mul, ← h1']
  have hpow : (-1 : Polynomial ℂ) ^ P.natDegree = 1 := mul_right_cancel₀ hlc h1
  exact (neg_one_pow_eq_one_iff_even (by norm_num : (-1 : Polynomial ℂ) ≠ 1)).mp hpow

lemma pd_cheb_red_eraseLead_comp_neg_X (P : Polynomial (Polynomial ℂ))
    (hsym : P.comp (-Polynomial.X) = P) (h : Even P.natDegree) :
    (Polynomial.eraseLead P).comp (-Polynomial.X) = Polynomial.eraseLead P := by
  have hneg : (-Polynomial.X : Polynomial (Polynomial ℂ)) ^ P.natDegree
      = Polynomial.X ^ P.natDegree := h.neg_pow Polynomial.X
  rw [← Polynomial.self_sub_C_mul_X_pow P, Polynomial.sub_comp, Polynomial.mul_comp,
      Polynomial.C_comp, Polynomial.pow_comp, Polynomial.X_comp, hsym, hneg,
      Polynomial.self_sub_C_mul_X_pow]

lemma pd_cheb_red_natDegree_mul_one_sub_X_sq_pow (c : Polynomial ℂ) (m : ℕ) :
    (c * ((1 : Polynomial ℂ) - Polynomial.X ^ 2) ^ m).natDegree ≤ c.natDegree + 2 * m := by
  calc (c * ((1 : Polynomial ℂ) - Polynomial.X ^ 2) ^ m).natDegree
      ≤ c.natDegree + (((1 : Polynomial ℂ) - Polynomial.X ^ 2) ^ m).natDegree :=
        Polynomial.natDegree_mul_le
    _ ≤ c.natDegree + m * (((1 : Polynomial ℂ) - Polynomial.X ^ 2)).natDegree := by
        gcongr
        exact Polynomial.natDegree_pow_le
    _ ≤ c.natDegree + m * 2 := by
        gcongr
        calc (((1 : Polynomial ℂ) - Polynomial.X ^ 2)).natDegree
            ≤ max (1 : Polynomial ℂ).natDegree (Polynomial.X ^ 2).natDegree :=
              Polynomial.natDegree_sub_le _ _
          _ ≤ 2 := by simp
    _ = c.natDegree + 2 * m := by ring

lemma pd_cheb_red_eval_mul_one_sub_X_sq_pow (c : Polynomial ℂ) (m : ℕ) (c₀ s₀ : ℂ)
    (hs : s₀ ^ 2 = 1 - c₀ ^ 2) :
    (c * ((1 : Polynomial ℂ) - Polynomial.X ^ 2) ^ m).eval c₀ = c.eval c₀ * s₀ ^ (2 * m) := by
  rw [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_one,
      Polynomial.eval_pow, Polynomial.eval_X]
  rw [pow_mul, hs]

theorem pd_cheb_red (P : Polynomial (Polynomial ℂ)) (k : ℕ)
    (hsym : P.comp (-Polynomial.X) = P)
    (hdeg : ∀ i, i ≤ P.natDegree → (P.coeff i).natDegree + i ≤ k) :
    ∃ Q : Polynomial ℂ, Q.natDegree ≤ k ∧
      ∀ c₀ s₀ : ℂ, s₀ ^ 2 = 1 - c₀ ^ 2 →
        Q.eval c₀ = P.eval₂ (Polynomial.evalRingHom c₀) s₀ := by
  -- Strong induction on an upper bound for the outer degree.
  have key : ∀ d : ℕ, ∀ P : Polynomial (Polynomial ℂ), P.natDegree ≤ d →
      P.comp (-Polynomial.X) = P →
      (∀ i, i ≤ P.natDegree → (P.coeff i).natDegree + i ≤ k) →
      ∃ Q : Polynomial ℂ, Q.natDegree ≤ k ∧
        ∀ c₀ s₀ : ℂ, s₀ ^ 2 = 1 - c₀ ^ 2 →
          Q.eval c₀ = P.eval₂ (Polynomial.evalRingHom c₀) s₀ := by
    intro d
    induction d with
    | zero =>
        -- `P` is constant in the outer variable.
        intro P hd _ hdeg
        refine ⟨P.coeff 0, ?_, ?_⟩
        · have h0 := hdeg 0 (by omega)
          omega
        · intro c₀ s₀ _
          rw [Polynomial.eq_C_of_natDegree_le_zero hd]
          simp
    | succ d ih =>
        intro P hd hsym hdeg
        by_cases hle : P.natDegree ≤ d
        · exact ih P hle hsym hdeg
        · have hPn : P.natDegree = d + 1 := by omega
          have hPne : P ≠ 0 := by
            intro h0
            rw [h0] at hPn
            simp only [Polynomial.natDegree_zero] at hPn
            omega
          -- symmetry forces the outer degree to be even
          obtain ⟨m, hm⟩ := pd_cheb_red_even_natDegree P hsym hPne
          have h2m : P.natDegree = 2 * m := by rw [hm, two_mul]
          -- strip the leading term
          have hP'le : (Polynomial.eraseLead P).natDegree ≤ d := by
            rcases Polynomial.eraseLead_natDegree_lt_or_eraseLead_eq_zero P with h | h
            · omega
            · rw [h, Polynomial.natDegree_zero]; omega
          have hsym' : (Polynomial.eraseLead P).comp (-Polynomial.X) = Polynomial.eraseLead P :=
            pd_cheb_red_eraseLead_comp_neg_X P hsym ⟨m, hm⟩
          have hdeg' : ∀ i, i ≤ (Polynomial.eraseLead P).natDegree →
              ((Polynomial.eraseLead P).coeff i).natDegree + i ≤ k := by
            intro i hi
            have hine : i ≠ P.natDegree := by
              rcases Polynomial.eraseLead_natDegree_lt_or_eraseLead_eq_zero P with h | h
              · exact (lt_of_le_of_lt hi h).ne
              · rw [h, Polynomial.natDegree_zero] at hi; omega
            rw [Polynomial.eraseLead_coeff_of_ne i hine]
            exact hdeg i (le_trans hi Polynomial.eraseLead_natDegree_le_aux)
          obtain ⟨Q', hQ'deg, hQ'eval⟩ := ih (Polynomial.eraseLead P) hP'le hsym' hdeg'
          refine ⟨Q' + P.leadingCoeff * ((1 : Polynomial ℂ) - Polynomial.X ^ 2) ^ m, ?_, ?_⟩
          · -- degree estimate
            refine le_trans (Polynomial.natDegree_add_le _ _) (max_le hQ'deg ?_)
            refine le_trans (pd_cheb_red_natDegree_mul_one_sub_X_sq_pow P.leadingCoeff m) ?_
            have hlc := hdeg P.natDegree le_rfl
            rw [Polynomial.coeff_natDegree] at hlc
            omega
          · -- evaluation
            intro c₀ s₀ hs
            have hPeval : P.eval₂ (Polynomial.evalRingHom c₀) s₀
                = (Polynomial.eraseLead P).eval₂ (Polynomial.evalRingHom c₀) s₀
                  + P.leadingCoeff.eval c₀ * s₀ ^ (2 * m) := by
              conv_lhs => rw [← Polynomial.eraseLead_add_C_mul_X_pow P]
              rw [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_C,
                Polynomial.eval₂_X_pow]
              rw [show (Polynomial.evalRingHom c₀) P.leadingCoeff = P.leadingCoeff.eval c₀ from rfl]
              rw [h2m, pow_mul, hs]
            rw [Polynomial.eval_add,
              pd_cheb_red_eval_mul_one_sub_X_sq_pow P.leadingCoeff m c₀ s₀ hs,
              hQ'eval c₀ s₀ hs, hPeval]
  exact key P.natDegree P le_rfl hsym hdeg

end Work.TMC16Core.Basic
