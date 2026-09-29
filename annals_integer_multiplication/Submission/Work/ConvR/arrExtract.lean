import Mathlib
import Submission.Work.ConvR.scaleFacts

namespace Work.ConvR

theorem arrExtract {As : List (List (ℤ × ℤ))} {ys : List HvdH.Val}
    {P : List (ℤ × ℤ) → List (ℤ × ℤ) → Prop}
    (h : List.Forall₂ (fun x y => ∃ v : List (ℤ × ℤ), y = HvdH.cvecVal v ∧
        ∀ u : List (ℤ × ℤ), x = HvdH.cvecVal u → P u v) (As.map HvdH.cvecVal) ys) :
    ∃ Bs : List (List (ℤ × ℤ)), ys = Bs.map HvdH.cvecVal ∧ Bs.length = As.length ∧
      ∀ i : ℕ, i < As.length → P (As.getD i []) (Bs.getD i []) := by
  induction As generalizing ys with
  | nil =>
    cases h with
    | nil =>
      exact ⟨[], rfl, rfl, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | cons a As ih =>
    cases h with
    | cons hhead htail =>
      rcases hhead with ⟨v, rfl, hv⟩
      obtain ⟨Bs, hys, hlen, hP⟩ := ih htail
      refine ⟨v :: Bs, by simp [hys], by simp [hlen], ?_⟩
      intro i hi
      cases i with
      | zero => simpa using hv a rfl
      | succ j =>
        simp at hi ⊢
        exact hP j hi

end Work.ConvR
