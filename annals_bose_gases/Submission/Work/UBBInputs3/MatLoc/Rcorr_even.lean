import Mathlib.Analysis.Real.Sqrt
import Submission.Work.UBBInputs3.MatLoc.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.UBBInputs3.MatLoc

open scoped BigOperators
open Finset

/-- The triangle profile `tri` is even: `tri p (-s) = tri p s`. -/
lemma tri_neg (p : ℕ) (s : ℤ) : Work.UBBInputs3.tri p (-s) = Work.UBBInputs3.tri p s := by
  simp [Work.UBBInputs3.tri, abs_neg]

/-- The normalised profile `prof` is even: `prof p (-s) = prof p s`. -/
lemma prof_neg (p : ℕ) (s : ℤ) : Work.UBBInputs3.prof p (-s) = Work.UBBInputs3.prof p s := by
  simp [Work.UBBInputs3.prof, tri_neg]

/-- Reindexing a sum over the symmetric range `Icc (-p) p` by negation. -/
lemma sum_Icc_neg (f : ℤ → ℝ) (p : ℕ) :
    ∑ s ∈ Finset.Icc (-(p:ℤ)) (p:ℤ), f (-s) = ∑ s ∈ Finset.Icc (-(p:ℤ)) (p:ℤ), f s := by
  apply Finset.sum_nbij' (fun s => -s) (fun s => -s)
  · intro a ha; simp only [Finset.mem_Icc] at ha ⊢; omega
  · intro a ha; simp only [Finset.mem_Icc] at ha ⊢; omega
  · intro a ha; simp
  · intro a ha; simp
  · intro a ha; rfl

/-- The autocorrelation `Rcorr p k = Σ_s prof(s) prof(s+k)` is even in the shift `k`. -/
theorem Rcorr_even (p : ℕ) (k : ℤ) :
    Work.UBBInputs3.Rcorr p (-k) = Work.UBBInputs3.Rcorr p k := by
  unfold Work.UBBInputs3.Rcorr
  rw [(sum_Icc_neg (fun t => Work.UBBInputs3.prof p t * Work.UBBInputs3.prof p (t + -k)) p).symm]
  apply Finset.sum_congr rfl
  intro s hs
  rw [prof_neg p s, show -s + -k = -(s + k) by ring, prof_neg p (s + k)]

end Work.UBBInputs3.MatLoc
