import Mathlib
import Submission.Work.ConvR.convDefs
import Submission.Work.DFT.dftDefs

/-!
# Linearity of `synExp` under componentwise difference of digit lists

`HvdH.synExp r ts js ks = Σᵢ (2r/tᵢ)·jᵢ·kᵢ` is a sum of *products* of the natural digits,
so as a function of the digit list it is only additive for the `ℤ`-valued signed form
`synExpZ r ts c ks = Σᵢ cᵢ·(2r/tᵢ)·kᵢ` (whose coefficients `cᵢ` are integers).

This file proves `Work.ConvR.synExp_sub3`: for digit lists of length `ts.length`,

`synExp r ts js ks - synExp r ts as ks - synExp r ts bs ks
   = synExpZ r ts (subNZ (subN js as) bs) ks`,

the `synExp`-analogue of `Work.DFT.phase_sub3`.  The route is
* `synExp_eq_synExpZ` : `synExp` with natural digits is `synExpZ` with the coerced digits;
* `synExpZ_subZZ`     : `synExpZ` is additive in its (integer) coefficient list;
* `subN_eq_subZZ`, `subNZ_eq_subZZ` : `subN`/`subNZ` are the componentwise subtraction of
  the coerced lists, so the inner difference is just an iterated `subZZ`.
-/

set_option autoImplicit false

namespace Work.ConvR

open scoped BigOperators

/-! ## Componentwise subtraction of integer lists, and coercion of digit lists -/

/-- Componentwise subtraction of two integer lists (the `ℤ`-analogue of `Work.DFT.subN`). -/
def subZZ (xs ys : List ℤ) : List ℤ := List.zipWith (fun x y => x - y) xs ys

@[simp] lemma subZZ_cons (x : ℤ) (xs : List ℤ) (y : ℤ) (ys : List ℤ) :
    subZZ (x :: xs) (y :: ys) = (x - y) :: subZZ xs ys := List.zipWith_cons_cons

@[simp] lemma subZZ_nil_left (ys : List ℤ) : subZZ [] ys = [] := List.zipWith_nil_left

@[simp] lemma subZZ_nil_right (xs : List ℤ) : subZZ xs [] = [] := List.zipWith_nil_right

/-- The coerced digit list `(j₁, …, jₙ) ↦ ((j₁ : ℤ), …, (jₙ : ℤ))`. -/
def toZ (js : List ℕ) : List ℤ := List.map (fun j => (j : ℤ)) js

@[simp] lemma toZ_nil : toZ [] = [] := rfl

@[simp] lemma toZ_cons (j : ℕ) (js : List ℕ) : toZ (j :: js) = (j : ℤ) :: toZ js :=
  List.map_cons

/-! ## Unfolding lemmas for `HvdH.synExp` -/

@[simp] lemma synExp_nil_left (r : ℕ) (js ks : List ℕ) : HvdH.synExp r [] js ks = 0 := rfl

@[simp] lemma synExp_nil_mid (r t : ℕ) (ts ks : List ℕ) :
    HvdH.synExp r (t :: ts) [] ks = 0 := rfl

@[simp] lemma synExp_nil_right (r t j : ℕ) (ts js : List ℕ) :
    HvdH.synExp r (t :: ts) (j :: js) [] = 0 := rfl

@[simp] lemma synExp_cons (r t : ℕ) (ts js ks : List ℕ) (j k : ℕ) :
    HvdH.synExp r (t :: ts) (j :: js) (k :: ks) =
      ((2 * r / t * j * k : ℕ) : ℤ) + HvdH.synExp r ts js ks := rfl

/-! ## The three ingredients -/

/-- `synExp` with natural digits is `synExpZ` with the coerced digits. -/
theorem synExp_eq_synExpZ (r : ℕ) : ∀ (ts js ks : List ℕ), js.length = ts.length →
    ks.length = ts.length → HvdH.synExp r ts js ks = synExpZ r ts (toZ js) ks := by
  intro ts
  induction ts with
  | nil =>
      intro js ks h1 h2
      have hj : js = [] := List.eq_nil_of_length_eq_zero h1
      have hk : ks = [] := List.eq_nil_of_length_eq_zero h2
      subst hj; subst hk
      simp
  | cons t ts ih =>
      intro js ks h1 h2
      obtain ⟨j, js', rfl⟩ : ∃ j js', js = j :: js' := by
        cases js with
        | nil => simp at h1
        | cons j js' => exact ⟨j, js', rfl⟩
      obtain ⟨k, ks', rfl⟩ : ∃ k ks', ks = k :: ks' := by
        cases ks with
        | nil => simp at h2
        | cons k ks' => exact ⟨k, ks', rfl⟩
      simp only [List.length_cons, Nat.succ.injEq] at h1 h2
      have ih' := ih js' ks' h1 h2
      simp only [synExp_cons, toZ_cons, synExpZ_cons]
      rw [ih']
      push_cast
      ring

/-- `synExpZ` is additive in its integer coefficient list (componentwise difference). -/
theorem synExpZ_subZZ (r : ℕ) : ∀ (ts : List ℕ) (xs ys : List ℤ) (ks : List ℕ),
    xs.length = ts.length → ys.length = ts.length → ks.length = ts.length →
    synExpZ r ts (subZZ xs ys) ks = synExpZ r ts xs ks - synExpZ r ts ys ks := by
  intro ts
  induction ts with
  | nil =>
      intro xs ys ks h1 h2 h3
      have hx : xs = [] := List.eq_nil_of_length_eq_zero h1
      have hy : ys = [] := List.eq_nil_of_length_eq_zero h2
      have hk : ks = [] := List.eq_nil_of_length_eq_zero h3
      subst hx; subst hy; subst hk
      simp
  | cons t ts ih =>
      intro xs ys ks h1 h2 h3
      obtain ⟨x, xs', rfl⟩ : ∃ x xs', xs = x :: xs' := by
        cases xs with
        | nil => simp at h1
        | cons x xs' => exact ⟨x, xs', rfl⟩
      obtain ⟨y, ys', rfl⟩ : ∃ y ys', ys = y :: ys' := by
        cases ys with
        | nil => simp at h2
        | cons y ys' => exact ⟨y, ys', rfl⟩
      obtain ⟨k, ks', rfl⟩ : ∃ k ks', ks = k :: ks' := by
        cases ks with
        | nil => simp at h3
        | cons k ks' => exact ⟨k, ks', rfl⟩
      simp only [List.length_cons, Nat.succ.injEq] at h1 h2 h3
      have ih' := ih xs' ys' ks' h1 h2 h3
      simp only [subZZ_cons, synExpZ_cons]
      rw [ih']
      ring

/-- `Work.DFT.subN` is the componentwise `subZZ` of the coerced lists. -/
theorem subN_eq_subZZ (js as : List ℕ) :
    Work.DFT.subN js as = subZZ (toZ js) (toZ as) := by
  induction js generalizing as with
  | nil => cases as <;> simp [Work.DFT.subN, subZZ]
  | cons j js ih =>
      cases as with
      | nil => simp [Work.DFT.subN, subZZ]
      | cons a as =>
          simp only [Work.DFT.subN_cons, toZ_cons, subZZ_cons]
          rw [ih]

/-- `Work.DFT.subNZ` is the componentwise `subZZ` of the coerced list. -/
theorem subNZ_eq_subZZ (c : List ℤ) (bs : List ℕ) :
    Work.DFT.subNZ c bs = subZZ c (toZ bs) := by
  induction bs generalizing c with
  | nil => cases c <;> simp [Work.DFT.subNZ, subZZ]
  | cons b bs ih =>
      cases c with
      | nil => simp [Work.DFT.subNZ, subZZ]
      | cons x cs =>
          simp only [Work.DFT.subNZ_cons, toZ_cons, subZZ_cons]
          rw [ih]

/-! ## The target -/

theorem synExp_sub3 (r : ℕ) (ts js as bs ks : List ℕ) (hjs : js.length = ts.length)
    (has : as.length = ts.length) (hbs : bs.length = ts.length) (hks : ks.length = ts.length) :
    HvdH.synExp r ts js ks - HvdH.synExp r ts as ks - HvdH.synExp r ts bs ks
      = synExpZ r ts (Work.DFT.subNZ (Work.DFT.subN js as) bs) ks := by
  have h1 := synExp_eq_synExpZ r ts js ks hjs hks
  have h2 := synExp_eq_synExpZ r ts as ks has hks
  have h3 := synExp_eq_synExpZ r ts bs ks hbs hks
  have hlen : (subZZ (toZ js) (toZ as)).length = ts.length := by
    rw [← subN_eq_subZZ]
    simp [Work.DFT.subN, List.length_zipWith, hjs, has]
  have hb1 : synExpZ r ts (subZZ (toZ js) (toZ as)) ks
      = synExpZ r ts (toZ js) ks - synExpZ r ts (toZ as) ks :=
    synExpZ_subZZ r ts (toZ js) (toZ as) ks (by simpa [toZ] using hjs)
      (by simpa [toZ] using has) hks
  have hb2 : synExpZ r ts (subZZ (subZZ (toZ js) (toZ as)) (toZ bs)) ks
      = synExpZ r ts (subZZ (toZ js) (toZ as)) ks - synExpZ r ts (toZ bs) ks :=
    synExpZ_subZZ r ts (subZZ (toZ js) (toZ as)) (toZ bs) ks hlen
      (by simpa [toZ] using hbs) hks
  rw [h1, h2, h3, subNZ_eq_subZZ, subN_eq_subZZ, ← hb1, ← hb2]

end Work.ConvR
