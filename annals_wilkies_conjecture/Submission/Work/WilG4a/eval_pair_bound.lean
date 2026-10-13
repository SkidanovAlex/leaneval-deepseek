import Mathlib

namespace Work.WilG4a

/-- Coercing the value of a natural-valued multivariate polynomial to `ℝ` commutes with
coercing its coefficients. -/
private lemma eval_cast_map {σ : Type*} (x : σ → ℕ) (p : MvPolynomial σ ℕ) :
    ((MvPolynomial.eval x p : ℕ) : ℝ) =
      MvPolynomial.eval (fun i => (x i : ℝ)) (MvPolynomial.map (Nat.castRingHom ℝ) p) := by
  rw [← MvPolynomial.eval₂_eq_eval_map]
  exact MvPolynomial.eval₂_comp (Nat.castRingHom ℝ) x p

/-- Natural-valued form of `eval_pair_bound`: the composite

`bp (B(D,1), F(k,1))`

is bounded by a multivariate polynomial in `D` and `k` with natural coefficients.

The polynomials `D ↦ B(D,1)` and `k ↦ F(k,1)` are realised as the polynomials
`rename (0 ↦ 0, 1 ↦ 1) B` and `rename (0 ↦ 2, 1 ↦ 1) F` in three variables, evaluated
at `(D, 1, k)`; the induction on `bp` then only uses that all values are nonnegative. -/
private lemma eval_pair_bound_nat (bp B F : MvPolynomial (Fin 2) ℕ) :
    ∃ cc : MvPolynomial (Fin 3) ℕ, ∀ D k : ℕ,
      MvPolynomial.eval (![MvPolynomial.eval (![D, 1] : Fin 2 → ℕ) B,
          MvPolynomial.eval (![k, 1] : Fin 2 → ℕ) F] : Fin 2 → ℕ) bp
        ≤ MvPolynomial.eval (![D, 1, k] : Fin 3 → ℕ) cc := by
  have hB : ∀ D k : ℕ, MvPolynomial.eval (![D, 1] : Fin 2 → ℕ) B
      ≤ MvPolynomial.eval (![D, 1, k] : Fin 3 → ℕ)
          (MvPolynomial.rename (![0, 1] : Fin 2 → Fin 3) B) := by
    intro D k
    rw [MvPolynomial.eval_rename]
    have h2 : ((![D, 1, k] : Fin 3 → ℕ) ∘ (![0, 1] : Fin 2 → Fin 3)) = ![D, 1] := by
      funext i; fin_cases i <;> simp
    rw [h2]
  have hF : ∀ D k : ℕ, MvPolynomial.eval (![k, 1] : Fin 2 → ℕ) F
      ≤ MvPolynomial.eval (![D, 1, k] : Fin 3 → ℕ)
          (MvPolynomial.rename (![2, 1] : Fin 2 → Fin 3) F) := by
    intro D k
    rw [MvPolynomial.eval_rename]
    have h2 : ((![D, 1, k] : Fin 3 → ℕ) ∘ (![2, 1] : Fin 2 → Fin 3)) = ![k, 1] := by
      funext i; fin_cases i <;> simp
    rw [h2]
  induction bp using MvPolynomial.induction_on with
  | C a => exact ⟨MvPolynomial.C a, fun D k => by simp⟩
  | add p q hp hq =>
      obtain ⟨cp, hcp⟩ := hp
      obtain ⟨cq, hcq⟩ := hq
      exact ⟨cp + cq, fun D k => by
        simpa [MvPolynomial.eval_add] using add_le_add (hcp D k) (hcq D k)⟩
  | mul_X p n hp =>
      obtain ⟨cp, hcp⟩ := hp
      fin_cases n
      · exact ⟨cp * MvPolynomial.rename (![0, 1] : Fin 2 → Fin 3) B, fun D k => by
          simpa [MvPolynomial.eval_mul] using Nat.mul_le_mul (hcp D k) (hB D k)⟩
      · exact ⟨cp * MvPolynomial.rename (![2, 1] : Fin 2 → Fin 3) F, fun D k => by
          simpa [MvPolynomial.eval_mul] using Nat.mul_le_mul (hcp D k) (hF D k)⟩

theorem eval_pair_bound (bp B F : MvPolynomial (Fin 2) ℕ) :
    ∃ cc : MvPolynomial (Fin 3) ℝ, ∀ D k : ℕ,
      (MvPolynomial.eval ![MvPolynomial.eval ![D, 1] B, MvPolynomial.eval ![k, 1] F] bp : ℝ) ≤
        MvPolynomial.eval ![(D : ℝ), (1 : ℝ), (k : ℝ)] cc := by
  obtain ⟨cc, hcc⟩ := eval_pair_bound_nat bp B F
  refine ⟨MvPolynomial.map (Nat.castRingHom ℝ) cc, fun D k => ?_⟩
  have h2 := eval_cast_map (![D, 1, k] : Fin 3 → ℕ) cc
  have hfun : (fun i => (((![D, 1, k] : Fin 3 → ℕ) i : ℕ) : ℝ)) =
      ![(D : ℝ), (1 : ℝ), (k : ℝ)] := by
    funext i; fin_cases i <;> simp
  have hR : MvPolynomial.eval ![(D : ℝ), (1 : ℝ), (k : ℝ)]
        (MvPolynomial.map (Nat.castRingHom ℝ) cc)
      = (MvPolynomial.eval (![D, 1, k] : Fin 3 → ℕ) cc : ℝ) := by
    rw [← hfun]
    exact h2.symm
  rw [hR]
  exact_mod_cast hcc D k

end Work.WilG4a
