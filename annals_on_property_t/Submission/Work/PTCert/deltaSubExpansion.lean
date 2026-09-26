import Mathlib
import Submission.Work.PTCert.LetterAPI

namespace Work.PTCert

open OnPropertyT Submission.FreeGroupAut Submission.RouteB Submission.RouteB.Edge
open scoped BigOperators

/-- `NB1 r = 1 + 4 r (r-1)` is positive (there is always the letter `0`, i.e. the identity). -/
lemma NB1_pos (r : ℕ) : 0 < Submission.PTCert.NB1 r := by simp [Submission.PTCert.NB1]

/-- The letter index range splits off the identity letter `0` from the transvection letters. -/
lemma range_NB1_eq_insert (r : ℕ) :
    Finset.range (Submission.PTCert.NB1 r) = insert 0 (Finset.Ico 1 (Submission.PTCert.NB1 r)) := by
  ext x
  simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]
  have := NB1_pos r
  omega

/-- `Δ_n` expanded in the letters: `Laplacian (SAutGen r) = ∑_{a < NB1 r} cDelta r a • of (b1 r a)`.
Proof route for `r ≥ 2`: `deltaSub r r = Laplacian (genSub r r) = Laplacian (SAutGen r)` (`genSub_top`),
`SAutGen r = (Ico 1 (NB1 r)).image (b1 r)` (`LetterAPI.SAutGen_eq_image`), `b1_injOn` (gives `Finset.sum_image`),
`card_SAutGen` (gives `(SAutGen r).card = NB1 r - 1`); split `range (NB1 r) = insert 0 (Ico 1 (NB1 r))`,
use `b1 r 0 = 1`, `cDelta r 0 = (NB1 r : ℚ) - 1`, `cDelta r a = -1` for `a ≠ 0`, and
`Laplacian S = (S.card : _) - ∑_{g ∈ S} of g`.  For `r ≤ 1`, `SAutGen r = ∅`, `NB1 r = 1`, `cDelta r 0 = 0`. -/
theorem deltaSubExpansion (r : ℕ) :
    Submission.RouteB.Edge.deltaSub r r =
      ∑ a ∈ Finset.range (Submission.PTCert.NB1 r),
        (Submission.PTCert.cDelta r a : ℝ) •
          MonoidAlgebra.of ℝ (MulAut (FreeGroup (Fin r))) (Submission.PTCert.b1 r a) := by
  -- The letter expansion of `(NB1 r - 1) • 1 - ∑_{1 ≤ a < NB1 r} of (b1 r a)`.
  have hsum : (∑ a ∈ Finset.range (Submission.PTCert.NB1 r),
        (Submission.PTCert.cDelta r a : ℝ) •
          MonoidAlgebra.of ℝ (MulAut (FreeGroup (Fin r))) (Submission.PTCert.b1 r a))
      = ((Submission.PTCert.NB1 r - 1 : ℕ) : MonoidAlgebra ℝ (MulAut (FreeGroup (Fin r))))
        - ∑ a ∈ Finset.Ico 1 (Submission.PTCert.NB1 r),
            MonoidAlgebra.of ℝ (MulAut (FreeGroup (Fin r))) (Submission.PTCert.b1 r a) := by
    rw [range_NB1_eq_insert r, Finset.sum_insert (by simp [Finset.mem_Ico])]
    have hof1 : MonoidAlgebra.of ℝ (MulAut (FreeGroup (Fin r)))
        (1 : MulAut (FreeGroup (Fin r))) = 1 := by
      simp [MonoidAlgebra.one_def]
    have h0 : (Submission.PTCert.cDelta r 0 : ℝ) •
          MonoidAlgebra.of ℝ (MulAut (FreeGroup (Fin r))) (Submission.PTCert.b1 r 0)
        = ((Submission.PTCert.NB1 r - 1 : ℕ) :
            MonoidAlgebra ℝ (MulAut (FreeGroup (Fin r)))) := by
      rw [show Submission.PTCert.b1 r 0 = 1 by simp [Submission.PTCert.b1],
          show Submission.PTCert.cDelta r 0 = (Submission.PTCert.NB1 r : ℚ) - 1 by
            simp [Submission.PTCert.cDelta],
          hof1]
      rw [Algebra.smul_def, mul_one]
      push_cast
      rw [Nat.cast_sub (by simp [Submission.PTCert.NB1])]
      simp
    have hI : (∑ a ∈ Finset.Ico 1 (Submission.PTCert.NB1 r),
          (Submission.PTCert.cDelta r a : ℝ) •
            MonoidAlgebra.of ℝ (MulAut (FreeGroup (Fin r))) (Submission.PTCert.b1 r a))
        = - ∑ a ∈ Finset.Ico 1 (Submission.PTCert.NB1 r),
              MonoidAlgebra.of ℝ (MulAut (FreeGroup (Fin r))) (Submission.PTCert.b1 r a) := by
      rw [Finset.sum_congr rfl (fun a ha => ?_), Finset.sum_neg_distrib]
      have ha0 : a ≠ 0 := by have := (Finset.mem_Ico.mp ha).1; omega
      simp [Submission.PTCert.cDelta, ha0]
    rw [h0, hI, sub_eq_add_neg]
  have hmain : Submission.RouteB.Edge.deltaSub r r
      = ((Submission.PTCert.NB1 r - 1 : ℕ) : MonoidAlgebra ℝ (MulAut (FreeGroup (Fin r))))
        - ∑ a ∈ Finset.Ico 1 (Submission.PTCert.NB1 r),
            MonoidAlgebra.of ℝ (MulAut (FreeGroup (Fin r))) (Submission.PTCert.b1 r a) := by
    by_cases hr : 2 ≤ r
    · rw [Submission.RouteB.Edge.deltaSub_top]
      simp only [OnPropertyT.Laplacian, Nat.card_eq_fintype_card, Fintype.card_coe]
      rw [Submission.PTCert.card_SAutGen r hr, Submission.PTCert.sum_SAutGen r hr]
    · have hE : SAutGen r = ∅ := by
        rw [SAutGen]
        have : IsEmpty (SAutIdx r) := ⟨fun p => by
          obtain ⟨⟨⟨i, j⟩, be⟩, hij⟩ := p
          exact hij (Fin.ext (by have := i.isLt; have := j.isLt; omega))⟩
        simp
      have hN : Submission.PTCert.NB1 r = 1 := by
        simp [Submission.PTCert.NB1]; omega
      rw [Submission.RouteB.Edge.deltaSub_top, hE, hN]
      simp [OnPropertyT.Laplacian]
  exact hmain.trans hsum.symm

end Work.PTCert
