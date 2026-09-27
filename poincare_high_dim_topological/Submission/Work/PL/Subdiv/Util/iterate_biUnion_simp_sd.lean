import Mathlib
import Submission.Work.PL.Subdiv.SdBasic

namespace Work.PL.Subdiv.Util

/-!
# Subcomplexes survive iterated barycentric subdivision

The one-step statement is `Work.PL.Subdiv.biUnion_simp_sd`: a finite union of faces of `K`
is a finite union of faces of `sd K`.  Here it is iterated: a finite union of faces of `K` is a
finite union of faces of the `r`-fold subdivision `sdIter r K`.

The only bookkeeping is the elementary commutation

`sdIter r (sd K) = sdIter (r + 1) K`   (`sdIter_sd_shift`),

which lets the induction peel one subdivision off `K` while keeping the recursion variable
`sdIter` well-formed (`sdIter` is structural in its first argument, so
`sdIter r (sd K)` and `sd (sdIter r K)` are *not* definitionally equal for a variable `r`).
-/

open Set

variable {N : ℕ}

/-- Shifting one subdivision across the iteration: `r`-fold subdivision of `sd K` is the
`(r+1)`-fold subdivision of `K`. -/
theorem sdIter_sd_shift (r : ℕ) (K : PL.Cx N) (hK : K.faces.Finite) :
    Work.PL.Subdiv.sdIter r (Work.PL.Subdiv.sd K) (Work.PL.Subdiv.sd_faces_finite hK)
      = Work.PL.Subdiv.sdIter (r + 1) K hK := by
  induction r with
  | zero => rfl
  | succ n ih =>
    show Work.PL.Subdiv.sd (Work.PL.Subdiv.sdIter n (Work.PL.Subdiv.sd K)
      (Work.PL.Subdiv.sd_faces_finite hK)) = _
    rw [ih]
    rfl

/-- **Subcomplexes are preserved by iterated subdivision.**  Any finite union of faces of `K`
is a finite union of faces of the `r`-fold barycentric subdivision `sdIter r K`. -/
theorem iterate_biUnion_simp_sd {N : ℕ} (r : ℕ) (K : PL.Cx N) (hK : K.faces.Finite)
    (T : Finset (Finset (PL.E N))) (hT : ∀ s ∈ T, s ∈ K.faces) :
    ∃ T' : Finset (Finset (PL.E N)),
      (∀ t ∈ T', t ∈ (Work.PL.Subdiv.sdIter r K hK).faces) ∧
      ⋃ s ∈ T, PL.simp s = ⋃ t ∈ T', PL.simp t := by
  classical
  induction r generalizing K hK T with
  | zero => exact ⟨T, hT, rfl⟩
  | succ n ih =>
    obtain ⟨T₁, hT₁, hU₁⟩ := Work.PL.Subdiv.biUnion_simp_sd hK T hT
    obtain ⟨T', hT', hU'⟩ := ih (Work.PL.Subdiv.sd K) (Work.PL.Subdiv.sd_faces_finite hK) T₁ hT₁
    refine ⟨T', ?_, hU₁.trans hU'⟩
    intro t ht
    rw [← sdIter_sd_shift]
    exact hT' t ht

end Work.PL.Subdiv.Util
