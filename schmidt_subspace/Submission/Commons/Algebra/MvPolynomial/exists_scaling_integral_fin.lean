import Mathlib
import Submission.Commons.Algebra.MvPolynomial.exists_scaling_integral

namespace Commons.Algebra.MvPolynomial

theorem exists_scaling_integral_fin {n : ℕ}
    (U₁ : MvPolynomial (Fin 1) ℚ) (U₂ : MvPolynomial (Fin n) ℚ)
    (h₁ : U₁ ≠ 0) (h₂ : U₂ ≠ 0) (V : MvPolynomial (Fin (n + 1)) ℤ)
    (hV : V.map (Int.castRingHom ℚ) =
      MvPolynomial.rename (fun _ : Fin 1 => (0 : Fin (n + 1))) U₁ *
        MvPolynomial.rename Fin.succ U₂) :
    ∃ (c : ℚ), c ≠ 0 ∧
      (∃ W₁ : MvPolynomial (Fin 1) ℤ,
        W₁.map (Int.castRingHom ℚ) = MvPolynomial.C c⁻¹ * U₁) ∧
      (∃ W₂ : MvPolynomial (Fin n) ℤ,
        W₂.map (Int.castRingHom ℚ) = MvPolynomial.C c * U₂) := by
  -- Reindex `Fin (n+1)` as `Fin 1 ⊕ Fin n`, splitting off the `0`-th variable.
  let g : Fin (n + 1) → Fin 1 ⊕ Fin n :=
    Fin.cases (Sum.inl (0 : Fin 1)) (fun j : Fin n => Sum.inr j)
  have hg0 : g (0 : Fin (n + 1)) = Sum.inl (0 : Fin 1) := Fin.cases_zero
  have hgS : ∀ j : Fin n, g (Fin.succ j) = Sum.inr j := fun j => Fin.cases_succ (i := j)
  have hcomp₀ : g ∘ (fun _ : Fin 1 => (0 : Fin (n + 1))) = Sum.inl := by
    funext i
    fin_cases i
    simpa using hg0
  have hcompS : g ∘ Fin.succ = (Sum.inr : Fin n → Fin 1 ⊕ Fin n) := by
    funext j
    exact hgS j
  have hV' : (MvPolynomial.rename g V).map (Int.castRingHom ℚ) =
      MvPolynomial.rename Sum.inl U₁ * MvPolynomial.rename Sum.inr U₂ := by
    rw [MvPolynomial.map_rename, hV, map_mul, MvPolynomial.rename_rename,
      MvPolynomial.rename_rename, hcomp₀, hcompS]
  obtain ⟨c, hc, ⟨W₁, hW₁⟩, ⟨W₂, hW₂⟩⟩ :=
    exists_scaling_integral U₁ U₂ h₁ h₂ (MvPolynomial.rename g V) hV'
  exact ⟨c, hc, ⟨W₁, hW₁⟩, ⟨W₂, hW₂⟩⟩

end Commons.Algebra.MvPolynomial
