import Mathlib
import Submission.Work.SynFFT.kit2

namespace Work.SynFFT

open HvdH

/-- `cfxVal` is injective: `cfxVal z = .cons (.int z.1) (.int z.2)` and `Val.cons`, `Val.int`
are injective. -/
private theorem cfxVal_inj {a b : ℤ × ℤ} (h : cfxVal a = cfxVal b) : a = b := by
  have h' : a.1 = b.1 ∧ a.2 = b.2 := by
    simpa [cfxVal, Val.cons.injEq, Val.int.injEq] using h
  exact Prod.ext h'.1 h'.2

/-- `ofList` (the `cons`-chain encoding of a list of values) is injective. -/
private theorem ofList_inj {l₁ l₂ : List Val} (h : ofList l₁ = ofList l₂) : l₁ = l₂ := by
  induction l₁ generalizing l₂ with
  | nil =>
    cases l₂ with
    | nil => rfl
    | cons y ys => simp [ofList] at h
  | cons x xs ih =>
    cases l₂ with
    | nil => simp [ofList] at h
    | cons y ys =>
      have h' : x = y ∧ ofList xs = ofList ys := by
        simpa [ofList, Val.cons.injEq] using h
      rw [h'.1, ih h'.2]

/-- `cvecVal = ofList ∘ List.map cfxVal` is injective. -/
private theorem cvecVal_inj {u v : List (ℤ × ℤ)} (h : cvecVal u = cvecVal v) : u = v := by
  have h2 : u.map cfxVal = v.map cfxVal := ofList_inj (by simpa [cvecVal] using h)
  exact List.map_injective_iff.mpr (fun a b hab => cfxVal_inj hab) h2

/-- `cvecs = List.map cvecVal` is injective. -/
theorem cvecsInj : Function.Injective (Work.SynFFT.cvecs) := by
  intro a b h
  exact List.map_injective_iff.mpr (fun u v huv => cvecVal_inj huv) (by simpa [cvecs] using h)

end Work.SynFFT
