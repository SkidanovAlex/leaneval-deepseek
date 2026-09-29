import Mathlib
import Submission.Work.Resample.auDefs
import Submission.Work.Resample.auAssemble
import Submission.Work.Resample.auPiWord
import Submission.Work.Resample.auWtWord
import Submission.Work.Resample.auPiBound
import Submission.Work.Resample.auWtErr
import Submission.Work.Resample.auTail
import Submission.Work.Resample.auFinal
import Submission.Work.Resample.auPrep
import Submission.Work.Resample.auConv

namespace Work.Resample

theorem sliceAu (KL : HvdH.KernelLib) (IL : HvdH.IntLib) (LL : HvdH.LayoutLib) (FL : HvdH.FxLib)
    (RM : HvdH.ResMath1DProp) :
    ∃ (prep q : HvdH.Cmd) (K : ℕ),
      ∀ (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t) (hcop : Nat.Coprime s t) (htp : t < 2 ^ p)
        (hα : 2 ≤ α) (hp : 100 ≤ p) (hαp : α ^ 2 < p)
        (hθ : (p : ℝ) / (α : ℝ) ^ 4 ≤ (t : ℝ) / s - 1),
      ∃ (Φ : (Fin s → ℤ × ℤ) → (Fin t → ℤ × ℤ)) (P : List HvdH.Val),
        (∀ (main : HvdH.Cmd) (N : ℕ) (Cm : ℕ → ℕ), Monotone Cm → HvdH.MulBelow main N Cm → K * p < N →
          HvdH.WordR main prep
            (fun vs => ∃ rest, vs = .int p :: .int α :: .int s :: .int t :: rest)
            (fun vs out => ∃ rest, vs = .int p :: .int α :: .int s :: .int t :: rest ∧
              out = P ++ rest)
            (fun _ => K * (t + 1) * (p + 1) ^ K)) ∧
        (∀ (main : HvdH.Cmd) (N : ℕ) (Cm : ℕ → ℕ), Monotone Cm → HvdH.MulBelow main N Cm → K * p < N →
          HvdH.WordR main q
            (fun vs => ∃ (u : List (ℤ × ℤ)) (rest : List HvdH.Val),
              vs = HvdH.ofList (u.map HvdH.cfxVal) :: P ++ rest ∧
              u.length = s ∧ (∀ z ∈ u, HvdH.inDisc p z))
            (fun vs out => ∃ (u : List (ℤ × ℤ)) (rest : List HvdH.Val) (w : List (ℤ × ℤ)),
              vs = HvdH.ofList (u.map HvdH.cfxVal) :: P ++ rest ∧
              out = HvdH.cvecVal w :: P ++ rest ∧ w.length = t ∧ (∀ z ∈ w, HvdH.inDisc p z) ∧
              (∀ k : Fin t, w.getD k (0,0) = Φ (fun j => u.getD j (0,0)) k))
            (fun _ => K * (t + 1) * (Nat.sqrt p + 1) * (α + 1) * (Cm (K * p) + p + 1))) ∧
        (∀ w : Fin s → ℤ × ℤ, (∀ j, HvdH.inDisc p (w j)) → ∀ k : Fin t, HvdH.inDisc p (Φ w k)) ∧
        (∀ w : Fin s → ℤ × ℤ, (∀ j, HvdH.inDisc p (w j)) → ∀ k : Fin t,
          ‖HvdH.fxC p (Φ w k) - (HvdH.resA s t α).mulVec (fun j => HvdH.fxC p (w j)) k‖ * (2 : ℝ) ^ p
            < (p : ℝ) ^ 2) := by
  exact sliceAu_of_pieces (fun KL IL => auPiWord KL IL) (fun KL IL => auWtWord KL IL)
    auPrep auConv auFinal auWtErr auTail auPiBound KL IL LL FL RM

end Work.Resample
