import Mathlib
import Submission.Work.PTCert.LetterAPI

namespace Work.PTCert.EdgeLap

/-- The `cEdge`-weighted sum over the letters expanded: `cEdge r e a = 8` at `a = 0`, `-1` on the
letters of the edge `e` (`edgeL r a = e`), `0` elsewhere.  Since `range (NB1 r) = insert 0
(Ico 1 (NB1 r))` (with `1 ≤ NB1 r`) and `b1 r 0 = 1`, `of 1 = 1`, the sum is
`8 • 1 - ∑_{a ∈ L} of (b1 r a)` with `L = (Ico 1 (NB1 r)).filter (fun a => edgeL r a = e)`. -/
theorem sum_cEdge_eq (r : ℕ) (e : ℕ × ℕ) :
    (∑ a ∈ Finset.range (Submission.PTCert.NB1 r),
        (Submission.PTCert.cEdge r e a : ℝ) •
          MonoidAlgebra.of ℝ (MulAut (FreeGroup (Fin r))) (Submission.PTCert.b1 r a))
      = (8 : ℝ) • (1 : MonoidAlgebra ℝ (MulAut (FreeGroup (Fin r))))
        - ∑ a ∈ (Finset.Ico 1 (Submission.PTCert.NB1 r)).filter
            (fun a => Submission.PTCert.edgeL r a = e),
          MonoidAlgebra.of ℝ (MulAut (FreeGroup (Fin r))) (Submission.PTCert.b1 r a) := by
  classical
  have hNB : 1 ≤ Submission.PTCert.NB1 r := by
    simp only [Submission.PTCert.NB1]; omega
  have hset : Finset.range (Submission.PTCert.NB1 r)
      = insert 0 (Finset.Ico 1 (Submission.PTCert.NB1 r)) := by
    rw [Finset.range_eq_Ico]
    ext x
    simp only [Finset.mem_Ico, Finset.mem_insert]
    constructor
    · rintro ⟨-, hx⟩
      rcases Nat.eq_zero_or_pos x with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h, hx⟩
    · rintro (rfl | ⟨h1, hx⟩)
      · exact ⟨le_refl 0, hNB⟩
      · exact ⟨Nat.zero_le x, hx⟩
  have hnotmem : (0 : ℕ) ∉ Finset.Ico 1 (Submission.PTCert.NB1 r) := by
    simp [Finset.mem_Ico]
  have h0 : (Submission.PTCert.cEdge r e 0 : ℝ) •
        MonoidAlgebra.of ℝ (MulAut (FreeGroup (Fin r))) (Submission.PTCert.b1 r 0)
      = (8 : ℝ) • (1 : MonoidAlgebra ℝ (MulAut (FreeGroup (Fin r)))) := by
    have hb : Submission.PTCert.b1 r 0 = (1 : MulAut (FreeGroup (Fin r))) := by
      rw [Submission.PTCert.b1, dif_pos rfl]
    have hc : (Submission.PTCert.cEdge r e 0 : ℝ) = (8 : ℝ) := by
      rw [Submission.PTCert.cEdge, if_pos rfl]; norm_num
    rw [hb, hc, map_one]
  have hterm : ∀ a ∈ Finset.Ico 1 (Submission.PTCert.NB1 r),
      (Submission.PTCert.cEdge r e a : ℝ) •
          MonoidAlgebra.of ℝ (MulAut (FreeGroup (Fin r))) (Submission.PTCert.b1 r a)
        = (if Submission.PTCert.edgeL r a = e then
            - MonoidAlgebra.of ℝ (MulAut (FreeGroup (Fin r))) (Submission.PTCert.b1 r a)
          else 0) := by
    intro a ha
    have ha0 : a ≠ 0 := by have := (Finset.mem_Ico.mp ha).1; omega
    rw [Submission.PTCert.cEdge, if_neg ha0]
    by_cases hP : Submission.PTCert.edgeL r a = e
    · rw [if_pos hP, if_pos hP]; simp
    · rw [if_neg hP, if_neg hP]; simp
  have hsum : (∑ a ∈ Finset.Ico 1 (Submission.PTCert.NB1 r),
        (Submission.PTCert.cEdge r e a : ℝ) •
          MonoidAlgebra.of ℝ (MulAut (FreeGroup (Fin r))) (Submission.PTCert.b1 r a))
      = - ∑ a ∈ (Finset.Ico 1 (Submission.PTCert.NB1 r)).filter
            (fun a => Submission.PTCert.edgeL r a = e),
          MonoidAlgebra.of ℝ (MulAut (FreeGroup (Fin r))) (Submission.PTCert.b1 r a) := by
    rw [Finset.sum_congr rfl hterm]
    rw [← Finset.sum_filter]
    rw [Finset.sum_neg_distrib]
  rw [hset, Finset.sum_insert hnotmem, h0, hsum, sub_eq_add_neg]

end Work.PTCert.EdgeLap
