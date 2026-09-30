import Mathlib
import Submission.Work.Pi6.EFACTS.qzAux
import Submission.Work.Pi6.EFACTS.qzFive
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

namespace Work.Pi6.EFACTS

theorem qzDual : Module.Baer ℤ ℚ ∧ Module.Baer ℤ (AddCircle (1 : ℚ)) ∧
    (∀ {A : Type} [AddCommGroup A], (∀ a : A, ∃ N : ℕ, 0 < N ∧ N • a = 0) →
      ∀ a : A, a ≠ 0 → ∃ f : A →ₗ[ℤ] AddCircle (1 : ℚ), f a ≠ 0) ∧
    (∀ (k : ℕ), 0 < k → Nonempty ((ZMod k →ₗ[ℤ] AddCircle (1 : ℚ)) ≃ₗ[ℤ] ZMod k)) ∧
    (∀ {A : Type} [AddCommGroup A], (∀ a : A, ∃ N : ℕ, 0 < N ∧ N • a = 0) →
      ∀ (k : ℕ), 0 < k → Nonempty ((A →ₗ[ℤ] AddCircle (1 : ℚ)) ≃ₗ[ℤ] ZMod k) →
        Nonempty (A ≃ₗ[ℤ] ZMod k)) ∧
    (∀ {A : Type} [AddCommGroup A], (∀ a : A, ∃ N : ℕ, 0 < N ∧ N • a = 0) →
      Subsingleton (A →ₗ[ℤ] AddCircle (1 : ℚ)) → Subsingleton A) :=
  ⟨QZ.baer_rat, QZ.baer_circle,
    (fun {A : Type} [AddCommGroup A] (_ : ∀ a : A, ∃ N : ℕ, 0 < N ∧ N • a = 0) (a : A)
      (ha : a ≠ 0) => QZ.exists_linearMap_apply_ne_zero ha),
    (fun (k : ℕ) (hk : 0 < k) => QZ.zmodDual k hk),
    (fun {A : Type} [AddCommGroup A] (htor : ∀ a : A, ∃ N : ℕ, 0 < N ∧ N • a = 0)
      (k : ℕ) (hk : 0 < k)
      (h : Nonempty ((A →ₗ[ℤ] AddCircle (1 : ℚ)) ≃ₗ[ℤ] ZMod k)) => qzFive htor k hk h),
    (fun {A : Type} [AddCommGroup A] (_ : ∀ a : A, ∃ N : ℕ, 0 < N ∧ N • a = 0)
      (h : Subsingleton (A →ₗ[ℤ] AddCircle (1 : ℚ))) =>
        QZ.subsingleton_of_subsingleton_character h)⟩

end Work.Pi6.EFACTS
