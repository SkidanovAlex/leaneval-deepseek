import Mathlib
import Submission.Work.ConvR.basic

/-!
# ConvR pointwise map: shared definitions and elementary lemmas

Vocabulary used by `Submission/Work/ConvR/pointwise.lean` (the pointwise-product step of
Proposition 3.4) and by the delegated lemmas about it.

* `PWp p r x y` — the per-element input condition: `x = cvecVal u`, `y = cvecVal v` for two
  coefficient vectors `u, v ∈ C̃◦^r` (so that the Kronecker word of Lemma 2.5 can be applied).
* `PWq p r x y z` — the per-element output condition: `z = cvecVal w` with `w ∈ C̃◦^r` and
  `2^p ‖w̃ - (1/r) u * v‖ < 2`, the error bound of Lemma 2.5.

The `w` is placed *first* among the existential witnesses so that `Classical.choose` of an
inhabitant of `PWq` returns the output vector.
-/

set_option autoImplicit false

namespace Work.ConvR

open HvdH

/-- The per-element input condition of the ConvR pointwise map. -/
def PWp (p r : ℕ) (x y : Val) : Prop :=
  ∃ u v : List (ℤ × ℤ), x = cvecVal u ∧ y = cvecVal v ∧ InDiscVec p r u ∧ InDiscVec p r v

/-- The per-element output condition of the ConvR pointwise map (Lemma 2.5's error bound). -/
def PWq (p r : ℕ) (x y z : Val) : Prop :=
  ∃ w u v : List (ℤ × ℤ), z = cvecVal w ∧ x = cvecVal u ∧ y = cvecVal v ∧ InDiscVec p r w ∧
    ∀ j : Fin r, (2 : ℝ) ^ p * ‖fxC p (w.getD j (0, 0)) -
      ((r : ℂ))⁻¹ * negaMul r (fxVec p r u) (fxVec p r v) j‖ < 2

/-- `PWp` bounds the encoding size of both inputs by `cvecSz`. -/
theorem PWp.vsz_le {p r : ℕ} {x y : Val} (h : PWp p r x y) :
    vsz x ≤ cvecSz p r ∧ vsz y ≤ cvecSz p r := by
  obtain ⟨u, v, rfl, rfl, hu, hv⟩ := h
  exact ⟨vsz_cvecVal_le hu, vsz_cvecVal_le hv⟩

/-- `PWp` extracts the disc vectors. -/
theorem PWp.exists {p r : ℕ} {x y : Val} (h : PWp p r x y) :
    ∃ u v : List (ℤ × ℤ), x = cvecVal u ∧ y = cvecVal v ∧ InDiscVec p r u ∧ InDiscVec p r v := h

/-- `PWq` is defined with the output vector as its first witness. -/
theorem PWq.eq {p r : ℕ} {x y z : Val} (h : PWq p r x y z) : z = cvecVal h.choose :=
  h.choose_spec.choose_spec.choose_spec.1

/-- The remaining content of a `PWq` proof, with the output vector exposed. -/
theorem PWq.spec {p r : ℕ} {x y z : Val} (h : PWq p r x y z) :
    ∃ u v, x = cvecVal u ∧ y = cvecVal v ∧ InDiscVec p r h.choose ∧
      ∀ j : Fin r, (2 : ℝ) ^ p * ‖fxC p ((h.choose).getD j (0, 0)) -
        ((r : ℂ))⁻¹ * negaMul r (fxVec p r u) (fxVec p r v) j‖ < 2 := by
  obtain ⟨u, v, -, hx, hy, hd, he⟩ := h.choose_spec
  exact ⟨u, v, hx, hy, hd, he⟩

/-- `cfxVal` is injective. -/
theorem cfxVal_injective : Function.Injective cfxVal := by
  intro a b h
  have h' : a.1 = b.1 ∧ a.2 = b.2 := by
    simpa [cfxVal, Val.cons.injEq, Val.int.injEq] using h
  exact Prod.ext h'.1 h'.2

/-- `ofList` is injective. -/
theorem ofList_injective : Function.Injective ofList := by
  intro l
  induction l with
  | nil =>
    intro m h
    cases m with
    | nil => rfl
    | cons y ys => simp [ofList] at h
  | cons x xs ih =>
    intro m h
    cases m with
    | nil => simp [ofList] at h
    | cons y ys =>
      have h' : x = y ∧ ofList xs = ofList ys := by
        simpa [ofList, Val.cons.injEq] using h
      rw [h'.1, ih h'.2]

/-- `cvecVal` is injective. -/
theorem cvecVal_injective : Function.Injective cvecVal := by
  intro u v h
  have h2 : u.map cfxVal = v.map cfxVal := ofList_injective h
  exact List.map_injective_iff.mpr cfxVal_injective h2

/-- Value-level `cvecVal` is injective on `List Val` images: `ofList` of the images determines
the list.  (Used to read a `rarrVal` back.) -/
theorem ofList_map_cvecVal_injective {A B : List (List (ℤ × ℤ))}
    (h : ofList (A.map cvecVal) = ofList (B.map cvecVal)) : A = B :=
  List.map_injective_iff.mpr cvecVal_injective (ofList_injective h)

/-- Reading the `i`-th value of `As.map cvecVal` below its length. -/
theorem cvecVal_getD {l : List (List (ℤ × ℤ))} {i : ℕ} (h : i < l.length) :
    (l.map cvecVal).getD i .nil = cvecVal (l.getD i []) := by
  rw [List.getD_eq_getElem _ _ (by simpa using h), List.getElem_map, List.getD_eq_getElem _ _ h]

/-- Membership in `As.map cvecVal` gives an element of `As`. -/
theorem mem_map_cvecVal {l : List (List (ℤ × ℤ))} {x : Val} (h : x ∈ l.map cvecVal) :
    ∃ w ∈ l, cvecVal w = x := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp h
  have hi' : i < l.length := by simpa using hi
  exact ⟨l[i], List.getElem_mem hi', (List.getElem_map _).symm⟩

/-- `rarrVal` is injective (as a function of the list of coefficient vectors). -/
theorem rarrVal_injective : Function.Injective rarrVal := by
  intro A B h
  exact ofList_map_cvecVal_injective h

end Work.ConvR
