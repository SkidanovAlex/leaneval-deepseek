import Mathlib
import Submission.Work.ConCohomology.Setup

namespace Work.ConCohomology

/-- The chosen set-theoretic inverse of `S.f` takes the value `σ • S.invFun b` at `σ • b`, for
every `b` in the image of `S.f`.  This is the equivariance of `CoeffSES.invFun` with respect to
the action of `G`. -/
lemma invFun_smul {G : Type*} [Group G] {A B C : Type*} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] [DistribMulAction G A] [DistribMulAction G B] [DistribMulAction G C]
    (S : CoeffSES G A B C) (σ : G) {b : B} (h : ∃ a : A, S.f a = b) :
    S.invFun (σ • b) = σ • S.invFun b := by
  -- `S.invFun b` really is a preimage of `b` under `S.f`.
  have hb : S.f (S.invFun b) = b := by
    rw [S.invFun_eq, dite_eq_left h]
    exact Classical.choose_spec h
  -- hence `σ • S.invFun b` is a preimage of `σ • b`, by equivariance of `S.f`.
  have hs : S.f (σ • S.invFun b) = σ • b := by rw [S.f.map_smul, hb]
  have hmem : ∃ a : A, S.f a = σ • b := ⟨σ • S.invFun b, hs⟩
  -- `S.invFun` is the unique preimage, by injectivity of `S.f`.
  rw [S.invFun_eq, dite_eq_left hmem]
  exact S.injective_f (by rw [Classical.choose_spec hmem, hs])

end Work.ConCohomology
