import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.RB

/-- Auxiliary lemma: if an algebra endomorphism `ψ` of `MvPolynomial σ ℂ` fixes every variable
`X i` modulo an ideal `I`, then it fixes every polynomial modulo `I`. -/
lemma algHom_sub_mem_of_X_sub_mem {σ : Type*} (I : Ideal (MvPolynomial σ ℂ))
    (ψ : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial σ ℂ)
    (hX : ∀ i, ψ (MvPolynomial.X i) - MvPolynomial.X i ∈ I) :
    ∀ p, ψ p - p ∈ I := by
  intro p
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
      have h : ψ (p + q) - (p + q) = (ψ p - p) + (ψ q - q) := by simp; ring
      rw [h]
      exact I.add_mem hp hq
  | mul_X p n hp =>
      have h : ψ (p * MvPolynomial.X n) - p * MvPolynomial.X n =
          (ψ p - p) * ψ (MvPolynomial.X n) + p * (ψ (MvPolynomial.X n) - MvPolynomial.X n) := by
        simp; ring
      rw [h]
      exact I.add_mem (I.mul_mem_right _ hp) (I.mul_mem_left _ (hX n))

theorem rename_killCompl_sub_mem_span {σ : Type*} (v : σ) (a : MvPolynomial σ ℂ) :
    MvPolynomial.rename (Subtype.val : {x : σ // x ≠ v} → σ)
      (MvPolynomial.killCompl (f := Subtype.val) (Subtype.val_injective (p := fun x => x ≠ v)) a) - a ∈
      Ideal.span {MvPolynomial.X v} := by
  have hX : ∀ i : σ, ((MvPolynomial.rename (Subtype.val : {x : σ // x ≠ v} → σ)).comp
        (MvPolynomial.killCompl (f := Subtype.val) (Subtype.val_injective (p := fun x => x ≠ v))))
        (MvPolynomial.X i : MvPolynomial σ ℂ) - (MvPolynomial.X i : MvPolynomial σ ℂ) ∈
        Ideal.span {(MvPolynomial.X v : MvPolynomial σ ℂ)} := by
    intro i
    by_cases hi : i = v
    · subst i
      have hcomp : (MvPolynomial.rename (Subtype.val : {x : σ // x ≠ v} → σ))
          (MvPolynomial.killCompl (f := Subtype.val)
            (Subtype.val_injective (p := fun x => x ≠ v))
            (MvPolynomial.X v : MvPolynomial σ ℂ)) = 0 := by
        rw [MvPolynomial.killCompl, MvPolynomial.aeval_X]
        rw [dite_eq_right]
        · simp
        · rintro ⟨x, hx⟩
          exact x.2 hx
      rw [AlgHom.comp_apply, hcomp]
      simp
    · have hcomp : (MvPolynomial.rename (Subtype.val : {x : σ // x ≠ v} → σ))
          (MvPolynomial.killCompl (f := Subtype.val)
            (Subtype.val_injective (p := fun x => x ≠ v))
            (MvPolynomial.X i : MvPolynomial σ ℂ)) = MvPolynomial.X i := by
        rw [MvPolynomial.killCompl, MvPolynomial.aeval_X]
        rw [dite_eq_left ⟨⟨i, hi⟩, rfl⟩]
        rw [MvPolynomial.rename_X]
        congr 1
        exact congrArg Subtype.val (Equiv.ofInjective_symm_apply
          (Subtype.val_injective (p := fun x => x ≠ v)) ⟨i, hi⟩)
      rw [AlgHom.comp_apply, hcomp, sub_self]
      exact Ideal.zero_mem _
  have h := algHom_sub_mem_of_X_sub_mem
    (Ideal.span {(MvPolynomial.X v : MvPolynomial σ ℂ)}) _ hX a
  simpa [AlgHom.comp_apply] using h

end Work.RB
