import Mathlib
import Submission.Work.ConCohomology.Setup

namespace Work.ConCohomology

/-- `invFun` really is a set-theoretic inverse of `f` on the image of `f`: if `b` lies in the
image then `S.f (S.invFun b) = b`. -/
lemma f_invFun_of_exists {G : Type*} [Group G] {A B C : Type*} [AddCommGroup A]
    [AddCommGroup B] [AddCommGroup C] [DistribMulAction G A] [DistribMulAction G B]
    [DistribMulAction G C] (S : CoeffSES G A B C) {b : B} (h : ∃ a : A, S.f a = b) :
    S.f (S.invFun b) = b := by
  rw [CoeffSES.invFun_eq, dite_eq_left h]
  exact Classical.choose_spec h

lemma invFun_add {G : Type*} [Group G] {A B C : Type*} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] [DistribMulAction G A] [DistribMulAction G B] [DistribMulAction G C]
    (S : CoeffSES G A B C) {b₁ b₂ : B} (h₁ : ∃ a : A, S.f a = b₁)
    (h₂ : ∃ a : A, S.f a = b₂) : S.invFun (b₁ + b₂) = S.invFun b₁ + S.invFun b₂ := by
  have h12 : ∃ a : A, S.f a = b₁ + b₂ := by
    obtain ⟨a₁, ha₁⟩ := h₁
    obtain ⟨a₂, ha₂⟩ := h₂
    exact ⟨a₁ + a₂, by rw [EqHom.map_add, ha₁, ha₂]⟩
  apply S.injective_f
  rw [EqHom.map_add, f_invFun_of_exists S h12, f_invFun_of_exists S h₁,
    f_invFun_of_exists S h₂]

end Work.ConCohomology
