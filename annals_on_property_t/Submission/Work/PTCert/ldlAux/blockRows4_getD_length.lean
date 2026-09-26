import Mathlib
import Submission.Work.PTCert.ldlAux

namespace Work.PTCert.ldlAux

/-- The `ψ`-th list of a `List.range 4`-indexed family has the length of the family's `ψ`-th member. -/
theorem getD_range4_length {α : Type} (f : ℕ → List α) (d : List α) (ψ : ℕ) (hψ : ψ < 4) :
    (((List.range 4).map f).getD ψ d).length = (f ψ).length := by
  rw [List.getD_eq_getElem _ _ (by simp [hψ]), List.getElem_map, List.getElem_range]

/-- `blockRows4 … i` is a list of length `4` (one list of block entries per `ψ`), whose `ψ`-th
entry — for `ψ < 4` — is obtained by mapping the columns `ys.drop i` through the per-column
computation of `blockRow`; in particular its length is `(ys.drop i).length`. -/
theorem blockRows4_getD_length (cm eM repT repInfoT piIT : Submission.PTCert.NT)
    (piCodes : List ℕ) (rowTs : List Submission.PTCert.NT) (S : ℕ) (ks ys : List ℕ)
    (i ψ : ℕ) (hψ : ψ < 4) :
    ((Submission.PTCert.blockRows4 cm eM repT repInfoT piIT piCodes rowTs S ks ys i).getD ψ []).length =
      (ys.drop i).length := by
  simp only [Submission.PTCert.blockRows4, Submission.PTCert.blockRow]
  rw [List.getD_eq_getElem _ _ (by simp [hψ]), List.getElem_map, List.getElem_range]
  simp

end Work.PTCert.ldlAux
