import Mathlib
import Submission.Work.ConvR.scaleFacts

/-!
# ConvR/`scaleArr`: injectivity of the value constructors and elementary size bounds

`cvecVal` and `cfxVal` are injective (they are `ofList` of a `map` of the injective `cfxVal`), and
the encoding-size functions `cfxSz`, `cvecSz`, `arrSz` of `Submission/Work/ConvR/basic.lean` are
controlled by the parameters, which is what turns the library cost bounds into the single number
`K * (M * r + 1) * (p + 1) ^ 2 + K` of `Work.ConvR.scaleArr`.
-/

set_option autoImplicit false

namespace Work.ConvR

open HvdH

/-! ## Injectivity -/

private theorem ofList_injective : Function.Injective ofList := by
  intro l
  induction l with
  | nil =>
    intro m h
    cases m with
    | nil => rfl
    | cons y ys => exact absurd h (by simp [ofList])
  | cons x xs ih =>
    intro m h
    cases m with
    | nil => exact absurd h.symm (by simp [ofList])
    | cons y ys =>
      have h' : x = y ∧ ofList xs = ofList ys := by
        simpa [ofList, Val.cons.injEq] using h
      rw [h'.1, ih h'.2]

theorem cfxVal_injective_scaleInject : Function.Injective cfxVal := by
  intro a b h
  have h' : a.1 = b.1 ∧ a.2 = b.2 := by
    simpa [cfxVal, Val.cons.injEq, Val.int.injEq] using h
  exact Prod.ext h'.1 h'.2

theorem cvecVal_injective_scaleInject : Function.Injective cvecVal := by
  have h1 : Function.Injective (fun u : List (ℤ × ℤ) => u.map cfxVal) :=
    List.map_injective_iff.mpr (fun _ _ h => cfxVal_injective_scaleInject h)
  intro u v h
  exact h1 (ofList_injective h)

theorem cvecVal_inj {u v : List (ℤ × ℤ)} (h : cvecVal u = cvecVal v) : u = v :=
  cvecVal_injective_scaleInject h

/-! ## Size bounds -/

theorem cfxSz_le (p : ℕ) : cfxSz p ≤ 10 * (p + 1) := by
  simp only [cfxSz]; omega

theorem cvecSz_le (p r : ℕ) : cvecSz p r ≤ (r + 1) * (cfxSz p + 1) := by
  simp only [cvecSz]; nlinarith [Nat.zero_le r, Nat.zero_le p]

theorem arrSz_le (p M r : ℕ) :
    arrSz p M r ≤ (M + 1) * ((r + 1) * (cfxSz p + 1) + 1) := by
  have h := cvecSz_le p r
  simp only [arrSz]
  nlinarith [Nat.zero_le M, h]

theorem isz_int_le (p : ℕ) : isz ((p : ℤ)) ≤ p + 2 := by
  have h : ((p : ℤ)).natAbs = p := by simp
  rw [isz, h]
  have : p.size ≤ p := by
    rw [Nat.size_le]
    exact Nat.lt_two_pow_self
  omega

theorem isz_pow_le {p c : ℕ} (h : c ≤ 2 ^ p) : isz ((c : ℤ)) ≤ p + 3 := by
  have h' : ((c : ℤ)).natAbs ≤ 2 ^ p := by
    rw [Int.natAbs_natCast]; exact h
  exact isz_le_of_natAbs_le h'

end Work.ConvR
