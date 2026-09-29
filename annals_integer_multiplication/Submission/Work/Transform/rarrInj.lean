import Mathlib
import Submission.HvdH.Interfaces

/-!
# Injectivity of the array encodings

`ofList`, `cfxVal`, `cvecVal` and `rarrVal` (from `HvdH.Interfaces`) are injective, so an equality
of two encoded arrays can be turned back into an equality of the underlying lists.  This is needed
in the `Transform` assembly to identify the `ConvR` output arrays with the `Φ`-images `ua`, `ub`.
(The same lemmas exist in `Submission.Work.ConvR.convR`, but that module currently clashes with
`Submission.Work.ConvR.scaleInject`, so we keep a local copy.)
-/

set_option autoImplicit false

namespace Work.Transform

open HvdH

theorem ofList_inj_aux {xs ys : List Val} (h : ofList xs = ofList ys) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons y ys => simp [ofList] at h
  | cons x xs ih =>
    cases ys with
    | nil => simp [ofList] at h
    | cons y ys =>
      rw [show ofList (x :: xs) = Val.cons x (ofList xs) from rfl] at h
      rw [show ofList (y :: ys) = Val.cons y (ofList ys) from rfl] at h
      simp only [Val.cons.injEq] at h
      rw [ih h.2, h.1]

theorem cfxVal_inj_aux {z z' : ℤ × ℤ} (h : cfxVal z = cfxVal z') : z = z' := by
  simp only [cfxVal, Val.cons.injEq, Val.int.injEq] at h
  exact Prod.ext h.1 h.2

theorem map_cfxVal_inj_aux {u v : List (ℤ × ℤ)} (h : u.map cfxVal = v.map cfxVal) : u = v := by
  induction u generalizing v with
  | nil => cases v <;> simp_all
  | cons a u ih =>
    cases v with
    | nil => simp at h
    | cons b v =>
      simp only [List.map_cons, List.cons.injEq] at h
      rw [ih h.2, cfxVal_inj_aux h.1]

theorem cvecVal_inj_aux {u v : List (ℤ × ℤ)} (h : cvecVal u = cvecVal v) : u = v :=
  map_cfxVal_inj_aux (ofList_inj_aux h)

theorem map_cvecVal_inj_aux {A B : List (List (ℤ × ℤ))}
    (h : A.map cvecVal = B.map cvecVal) : A = B := by
  induction A generalizing B with
  | nil => cases B <;> simp_all
  | cons a A ih =>
    cases B with
    | nil => simp at h
    | cons b B =>
      simp only [List.map_cons, List.cons.injEq] at h
      rw [ih h.2, cvecVal_inj_aux h.1]

/-- `rarrVal` is injective. -/
theorem rarrVal_inj_aux {A B : List (List (ℤ × ℤ))} (h : rarrVal A = rarrVal B) : A = B :=
  map_cvecVal_inj_aux (ofList_inj_aux h)

end Work.Transform
