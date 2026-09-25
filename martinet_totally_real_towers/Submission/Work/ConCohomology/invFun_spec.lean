import Mathlib
import Submission.Work.ConCohomology.Setup

namespace Work.ConCohomology

lemma invFun_spec {G : Type*} [Group G] {A B C : Type*} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] [DistribMulAction G A] [DistribMulAction G B] [DistribMulAction G C]
    (S : CoeffSES G A B C) (b : B) : S.f (S.invFun b) = b ↔ ∃ a : A, S.f a = b := by
  constructor
  · intro h
    by_cases hb : ∃ a : A, S.f a = b
    · exact hb
    · -- `b` is not in the image of `f`, so `invFun b = 0` and `f 0 = b` forces `b = 0`,
      -- which is a witness.
      refine ⟨0, ?_⟩
      have h0 : S.invFun b = 0 := by
        rw [CoeffSES.invFun_eq]
        simp only [dite_eq_right_iff]
        intro hc
        exact absurd hc hb
      rw [h0] at h
      exact h
  · -- `b` is in the image of `f`, so `invFun b` is the chosen preimage.
    rintro ⟨a, ha⟩
    have hex : ∃ a : A, S.f a = b := ⟨a, ha⟩
    simp only [CoeffSES.invFun_eq, hex, dite_true]
    exact Classical.choose_spec hex

end Work.ConCohomology
