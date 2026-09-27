import Mathlib
import Submission.Work.Cohomology.Chains
import Submission.Work.Cohomology.Cohomology

namespace Work.Cohomology

/-- Evaluation of a cochain on a chain is linear in the cochain: `seval` is additive
(equivalently, `ℚ`-linear) in its cochain argument. -/
lemma seval_sub (S : SSet.{0}) (R : Type) [CommRing R] (n : ℕ)
    (u u' : Submission.Cohomology.Cochain S R n) (c : Submission.Cohomology.SChain S R n) :
    Submission.Cohomology.seval S R n (u - u') c
      = Submission.Cohomology.seval S R n u c - Submission.Cohomology.seval S R n u' c := by
  rw [Submission.Cohomology.seval_apply, Submission.Cohomology.seval_apply,
    Submission.Cohomology.seval_apply]
  rw [show c.sum (fun σ m => m * (u - u') σ)
        = c.sum (fun σ m => m * u σ - m * u' σ) from
      Finsupp.sum_congr (fun σ _ => by rw [Pi.sub_apply, mul_sub])]
  rw [Finsupp.sum_sub]

theorem seval_eq_of_sub_mem_boundaries {S : SSet.{0}} {p : ℕ} (c : Submission.Cohomology.SChain S ℚ p)
    (hc : c ∈ Submission.Cohomology.chainCycles S ℚ p) {u u' : Submission.Cohomology.Cochain S ℚ p}
    (h : u - u' ∈ Submission.Cohomology.boundaries S ℚ p) :
    Submission.Cohomology.seval S ℚ p u c = Submission.Cohomology.seval S ℚ p u' c := by
  have key : Submission.Cohomology.seval S ℚ p (u - u') c = 0 := by
    cases p with
    | zero =>
        -- In degree `0` there are no coboundaries, so `u - u' = 0`.
        have h0 : u - u' = 0 := (Submodule.mem_bot (R := ℚ)).mp h
        rw [h0]
        simp [Submission.Cohomology.seval_apply]
    | succ m =>
        -- In degree `m + 1`, `u - u'` is a coboundary, which pairs to zero with the cycle `c`.
        obtain ⟨v, hv⟩ := (Submission.Cohomology.mem_boundaries_succ (u - u')).mp h
        rw [← hv]
        exact Submission.Cohomology.seval_coboundary_eq_zero v c hc
  have hsub := seval_sub S ℚ p u u' c
  rw [hsub] at key
  exact sub_eq_zero.mp key

end Work.Cohomology
