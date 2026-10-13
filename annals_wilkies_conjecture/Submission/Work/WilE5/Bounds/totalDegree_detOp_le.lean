import Mathlib
import Submission.Work.WilE5.Basic
import Submission.Work.Wilkies.E.Spec
import Submission.Work.WilE2.Lift

namespace Work.WilE5.Bounds

/-- The rows of the determinant defining `detOp c h ι l f` are `h 0, …, h (j-1), f` and the
columns are the derivatives `∂_{ι 0}, …, ∂_{ι (j-1)}, ∂_l`. Each row therefore has total degree
`≤ d`, and since `eaD` raises the total degree by at most one (`totalDegree_eaD_le`), every entry
of the matrix has total degree `≤ d + 1`. The determinant is a sum of products of `j + 1` such
entries (`Matrix.det_totalDegree_le`), whence the bound `(j + 1) * (d + 1)`. -/
theorem totalDegree_detOp_le {k r j : ℕ} (c : WilkiesDesign.E.EAChain k r)
    (h : Fin j → WilkiesDesign.E.EAPoly k r) (ι : Fin j → Fin k) (l : Fin k)
    (f : WilkiesDesign.E.EAPoly k r) (d : ℕ)
    (hh : ∀ a, (h a).totalDegree ≤ d) (hf : f.totalDegree ≤ d) :
    (WilkiesDesign.E.detOp c h ι l f).totalDegree ≤ (j + 1) * (d + 1) := by
  classical
  -- Every row of the determinant has total degree `≤ d`.
  have hrow : ∀ a : Fin (j + 1),
      (Fin.lastCases f h a : WilkiesDesign.E.EAPoly k r).totalDegree ≤ d := by
    intro a
    rcases Fin.eq_castSucc_or_eq_last a with ⟨i, rfl⟩ | rfl
    · rw [Fin.lastCases_castSucc]
      exact hh i
    · rw [Fin.lastCases_last]
      exact hf
  -- Hence every entry of the matrix has total degree `≤ d + 1`.
  have key : ∀ a b : Fin (j + 1),
      (WilkiesDesign.E.eaD c (Fin.lastCases l ι b : Fin k)
        (Fin.lastCases f h a : WilkiesDesign.E.EAPoly k r)).totalDegree ≤ d + 1 :=
    fun a b => (totalDegree_eaD_le c _ _).trans (Nat.add_le_add_right (hrow a) 1)
  have hdet := Work.WilE2.Matrix.det_totalDegree_le
    (M := Matrix.of (fun (a b : Fin (j + 1)) =>
      WilkiesDesign.E.eaD c (Fin.lastCases l ι b) (Fin.lastCases f h a)))
    (b := fun _ => d + 1) key
  have hsum : (∑ _ : Fin (j + 1), (d + 1)) = (j + 1) * (d + 1) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul]
  rw [WilkiesDesign.E.detOp]
  exact hdet.trans (le_of_eq hsum)

end Work.WilE5.Bounds
