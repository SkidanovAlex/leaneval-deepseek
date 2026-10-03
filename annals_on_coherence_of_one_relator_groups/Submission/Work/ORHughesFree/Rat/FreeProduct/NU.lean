import Mathlib
import Submission.Work.ORHughesFree.Rat.SourceFrame
import Submission.Work.ORHughesFree.Rat.WordModel.Defs
import Submission.Work.ORHughesFree.Rat.Weak.SVPart
import Submission.Work.ORHughesFree.RatU.exists_decomp

/-!
# The free multiplicative monoid `U ♮ X` over the `U`-biset `X = Rat(U)`

The word model of `Rat(U)` in `Submission.Work.ORHughesFree.Rat.WordModel` is the monoid algebra of
`Mword`, a quotient of the free monoid on `U ⊔ PLetter`.  For the *first-letter* analysis one needs
the combinatorial model `U ♮ X` of [DHS04, Definition 4.4]: words whose letters are elements of the
group `U` or elements of the `U`-biset `X = Rat(U)`, with the two `U`-actions absorbed.

This file builds that monoid as `U ⊕ ({l : List (RatU U) // l ≠ []} ⧸ ~)`, where `~` is the
`U^{n-1}`-action `b · (x_1,…,x_n) = (b_1⁻¹x_1b_0, …, b_n⁻¹x_nb_{n-1})` of the `×_U`-product.

The two `U`-actions on `X = Rat(U)` are `u ▷ x = x * ofGroup u⁻¹` (`actL`) and
`x ◁ u = ofGroup u⁻¹ * x` (`actR`); they satisfy `ratOp (actL u x) = ofGroup u * ratOp x` and
`ratOp (actR u x) = ratOp x * ofGroup u`.
-/

set_option autoImplicit false

namespace Work.ORHughesFree.Rat
namespace FreeProduct

open Work.ORHughesFree

variable {U : Type} [Group U]

/-- `u ▷ x = x * u⁻¹`. -/
noncomputable def actL (u : U) (x : RatU U) : RatU U := x * RatU.ofGroup u⁻¹

/-- `x ◁ u = u⁻¹ * x`. -/
noncomputable def actR (u : U) (x : RatU U) : RatU U := RatU.ofGroup u⁻¹ * x

@[simp] theorem actL_one (x : RatU U) : actL (1 : U) x = x := by simp [actL]
@[simp] theorem actR_one (x : RatU U) : actR (1 : U) x = x := by simp [actR]

theorem actL_mul (u v : U) (x : RatU U) : actL (u * v) x = actL u (actL v x) := by
  simp [actL, RatU.ofGroup_mul, mul_assoc]

theorem actR_mul (u v : U) (x : RatU U) : actR (u * v) x = actR v (actR u x) := by
  simp [actR, RatU.ofGroup_mul, mul_assoc]

theorem actL_actR (u v : U) (x : RatU U) : actL u (actR v x) = actR v (actL u x) := by
  simp [actL, actR, mul_assoc]

theorem ratOp_actL (u : U) (x : RatU U) :
    RatU.ratOp (actL u x) = RatU.ofGroup u * RatU.ratOp x := by
  have h := RatU.ofGroup_mul_ratOp u x
  rw [actL]
  exact h.symm

theorem ratOp_actR (u : U) (x : RatU U) :
    RatU.ratOp (actR u x) = RatU.ratOp x * RatU.ofGroup u := by
  have h := RatU.ratOp_mul_ofGroup x u
  rw [actR]
  exact h.symm

/-- `shiftPad b l` applies the parameters `b` (`length b = length l + 1`) to `l`: its `i`-th entry
is `b_{i+1}⁻¹ · l_i · b_i`.  Only matching lengths are used; the other cases return `[]`. -/
noncomputable def shiftPad : List U → List (RatU U) → List (RatU U)
  | b₀ :: b₁ :: bs, x :: xs =>
      (RatU.ofGroup b₁⁻¹ * x * RatU.ofGroup b₀) :: shiftPad (b₁ :: bs) xs
  | _, _ => []

@[simp] theorem shiftPad_cons (b₀ b₁ : U) (bs : List U) (x : RatU U) (xs : List (RatU U)) :
    shiftPad (b₀ :: b₁ :: bs) (x :: xs)
      = (RatU.ofGroup b₁⁻¹ * x * RatU.ofGroup b₀) :: shiftPad (b₁ :: bs) xs := rfl

@[simp] theorem shiftPad_nil (b : List U) : shiftPad b ([] : List (RatU U)) = [] := by
  cases b with
  | nil => rfl
  | cons b₀ bs => cases bs <;> rfl

theorem shiftPad_length (b : List U) (l : List (RatU U)) (h : b.length = l.length + 1) :
    (shiftPad b l).length = l.length := by
  induction l generalizing b with
  | nil => simp
  | cons x xs ih =>
    cases b with
    | nil => simp at h
    | cons b₀ bs =>
      cases bs with
      | nil => simp at h
      | cons b₁ bs =>
        have h' : (b₁ :: bs).length = xs.length + 1 := by
          simp only [List.length_cons] at h ⊢; omega
        simp only [shiftPad_cons, List.length_cons]
        rw [ih (b₁ :: bs) h']

/-- Left multiplication of the first coordinate: `Xgen u * [x, …] = [actL u x, …]`. -/
noncomputable def mulFirst (u : U) : List (RatU U) → List (RatU U)
  | [] => []
  | x :: xs => actL u x :: xs

/-- Right multiplication of the last coordinate: `[…, x] * Xgen u = […, actR u x]`. -/
noncomputable def mulLast : List (RatU U) → U → List (RatU U)
  | [], _ => []
  | [x], u => [actR u x]
  | x :: y :: xs, u => x :: mulLast (y :: xs) u

@[simp] theorem mulFirst_nil (u : U) : mulFirst u ([] : List (RatU U)) = [] := rfl
@[simp] theorem mulFirst_cons (u : U) (x : RatU U) (xs : List (RatU U)) :
    mulFirst u (x :: xs) = actL u x :: xs := rfl
@[simp] theorem mulFirst_one (l : List (RatU U)) : mulFirst (1 : U) l = l := by
  cases l <;> simp [mulFirst]
theorem mulFirst_length (u : U) (l : List (RatU U)) : (mulFirst u l).length = l.length := by
  cases l <;> simp [mulFirst]
theorem mulFirst_ne_nil (u : U) {l : List (RatU U)} (hl : l ≠ []) : mulFirst u l ≠ [] := by
  obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil hl
  simp [mulFirst]

theorem mulLast_ne_nil (u : U) {l : List (RatU U)} (hl : l ≠ []) : mulLast l u ≠ [] := by
  obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil hl
  cases xs with
  | nil => simp [mulLast]
  | cons y ys => simp [mulLast]

theorem mulLast_length (l : List (RatU U)) (u : U) : (mulLast l u).length = l.length := by
  induction l with
  | nil => simp [mulLast]
  | cons x xs ih => cases xs with
    | nil => simp [mulLast]
    | cons y ys => simp [mulLast, ih]
@[simp] theorem mulLast_nil (u : U) : mulLast ([] : List (RatU U)) u = [] := rfl

/-- Identity law: the all-ones parameters act trivially. -/
theorem shiftPad_replicate_one (l : List (RatU U)) :
    shiftPad (List.replicate (l.length + 1) (1 : U)) l = l := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    rw [show List.replicate ((x :: xs).length + 1) (1 : U)
        = 1 :: 1 :: List.replicate xs.length (1 : U) by
      simp [List.replicate_succ]]
    rw [shiftPad_cons]
    simp only [RatU.ofGroup_one, inv_one, one_mul, mul_one]
    rw [show (1 : U) :: List.replicate xs.length 1 = List.replicate (xs.length + 1) 1 from
      (List.replicate_succ).symm]
    rw [ih]

/-- Composition law: `shiftPad` is an action of the group of parameter lists. -/
theorem shiftPad_comp (b b' : List U) (l : List (RatU U))
    (h : b.length = l.length + 1) (h' : b'.length = b.length) :
    shiftPad b' (shiftPad b l)
      = shiftPad (List.zipWith (· * ·) b b') l := by
  induction l generalizing b b' with
  | nil => simp
  | cons x xs ih =>
    cases b with
    | nil => simp at h
    | cons b₀ bs =>
      cases bs with
      | nil => simp at h
      | cons b₁ bs =>
        cases b' with
        | nil => simp at h'
        | cons c₀ cs =>
          cases cs with
          | nil => simp at h'
          | cons c₁ cs =>
            have h1 : (b₁ :: bs).length = xs.length + 1 := by
              simp only [List.length_cons] at h ⊢; omega
            have h2 : (c₁ :: cs).length = (b₁ :: bs).length := by
              simp only [List.length_cons] at h' ⊢; omega
            simp only [shiftPad_cons, List.zipWith_cons_cons]
            rw [ih (b₁ :: bs) (c₁ :: cs) h1 h2]
            simp only [List.zipWith_cons_cons, RatU.ofGroup_mul, mul_inv_rev, mul_assoc]

theorem zipWith_inv_self (b : List U) :
    List.zipWith (· * ·) b (b.map Inv.inv) = List.replicate b.length (1 : U) := by
  induction b with
  | nil => rfl
  | cons u us ih => simp [List.replicate_succ, ih]

/-- Inverse law: the componentwise inverse acts back. -/
theorem shiftPad_inv (b : List U) (l : List (RatU U)) (h : b.length = l.length + 1) :
    shiftPad (b.map Inv.inv) (shiftPad b l) = l := by
  have hlen : (b.map Inv.inv).length = b.length := List.length_map ..
  rw [shiftPad_comp b (b.map Inv.inv) l h (by rw [hlen]), zipWith_inv_self, h,
    shiftPad_replicate_one]


/-- Componentwise product of two parameter lists. -/
def compParams : List U → List U → List U
  | u :: us, v :: vs => (u * v) :: compParams us vs
  | _, _ => []

@[simp] theorem compParams_cons (u v : U) (us vs : List U) :
    compParams (u :: us) (v :: vs) = (u * v) :: compParams us vs := rfl

@[simp] theorem compParams_nil_left (l : List U) : compParams [] l = [] := by cases l <;> rfl
@[simp] theorem compParams_nil_right (l : List U) : compParams l [] = [] := by cases l <;> rfl

theorem compParams_length {l l' : List U} (h : l.length = l'.length) :
    (compParams l l').length = l.length := by
  induction l generalizing l' with
  | nil => simp
  | cons u us ih =>
    cases l' with
    | nil => simp at h
    | cons v vs =>
      simp only [compParams_cons, List.length_cons] at h ⊢
      rw [ih (by omega)]

theorem compParams_append {a b c d : List U} (h : a.length = b.length) :
    compParams (a ++ c) (b ++ d) = compParams a b ++ compParams c d := by
  induction a generalizing b with
  | nil => cases b with
    | nil => simp
    | cons _ _ => simp at h
  | cons u us ih =>
    cases b with
    | nil => simp at h
    | cons v vs =>
      simp only [List.cons_append, compParams_cons, List.length_cons] at h ⊢
      rw [ih (by omega)]

theorem compParams_inv (b : List U) :
    compParams b (b.map Inv.inv) = List.replicate b.length (1 : U) := by
  induction b with
  | nil => rfl
  | cons u us ih => simp [List.replicate_succ, ih]

theorem replicate_append_one (n : ℕ) :
    List.replicate n (1 : U) ++ [1] = List.replicate (n + 1) 1 := by
  rw [List.replicate_add]
  rfl

/-- The `X`-part of the monoid `U ♮ X`: nonempty lists of `X`-elements. -/
abbrev NEL := {l : List (RatU U) // l ≠ []}

theorem zipWith_eq_compParams (l l' : List U) :
    List.zipWith (· * ·) l l' = compParams l l' := by
  induction l generalizing l' with
  | nil => cases l' <;> rfl
  | cons u us ih => cases l' with
    | nil => rfl
    | cons v vs => simp [ih]

/-- The orbit relation on `X`-words: `l'` is obtained from `l` by the `U`-action of parameters
`b` (`length b = length l - 1`) sandwiched between trivial boundary parameters. -/
def relNE (l l' : NEL (U := U)) : Prop :=
  ∃ b : List U, b.length + 1 = l.1.length ∧ l'.1 = shiftPad (1 :: (b ++ [1])) l.1

theorem relNE_len {l l' : NEL (U := U)} (h : relNE l l') : l.1.length = l'.1.length := by
  obtain ⟨b, hlen, hb⟩ := h
  have hbnd : (1 :: (b ++ [1])).length = l.1.length + 1 := by
    simp only [List.length_cons, List.length_append, List.length_singleton, List.length_nil]; omega
  rw [hb, shiftPad_length (1 :: (b ++ [1])) l.1 hbnd]

theorem relNE_refl (l : NEL (U := U)) : relNE l l := by
  obtain ⟨lv, hl⟩ := l
  obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil hl
  refine ⟨List.replicate xs.length (1 : U), by simp, ?_⟩
  have hparams : (1 :: (List.replicate xs.length (1 : U) ++ [1]))
      = List.replicate ((x :: xs).length + 1) (1 : U) := by
    rw [List.length_cons, List.replicate_succ' (n := xs.length + 1) (a := (1 : U)),
      List.replicate_succ (n := xs.length) (a := (1 : U)), List.cons_append]
  rw [hparams, shiftPad_replicate_one]

theorem map_inv_cons (b : List U) :
    (1 : U) :: (b.map Inv.inv ++ [1]) = (1 :: (b ++ [1])).map Inv.inv := by
  simp [List.map_append]

theorem relNE_symm {l l' : NEL (U := U)} (h : relNE l l') : relNE l' l := by
  obtain ⟨b, hlen, hb⟩ := h
  have hbnd : (1 :: (b ++ [1])).length = l.1.length + 1 := by
    simp only [List.length_cons, List.length_append, List.length_singleton, List.length_nil]; omega
  have hlen' : l.1.length = l'.1.length := relNE_len ⟨b, hlen, hb⟩
  refine ⟨b.map Inv.inv, ?_, ?_⟩
  · rw [List.length_map]; omega
  · rw [hb, map_inv_cons b, shiftPad_inv (1 :: (b ++ [1])) l.1 hbnd]

theorem relNE_trans {l₁ l₂ l₃ : NEL (U := U)} (h₁ : relNE l₁ l₂) (h₂ : relNE l₂ l₃) :
    relNE l₁ l₃ := by
  obtain ⟨b₁, hlen₁, hb₁⟩ := h₁
  obtain ⟨b₂, hlen₂, hb₂⟩ := h₂
  have hlen : b₁.length = b₂.length := by
    have := relNE_len (l := l₁) (l' := l₂) ⟨b₁, hlen₁, hb₁⟩; omega
  have hbnd₁ : (1 :: (b₁ ++ [1])).length = l₁.1.length + 1 := by
    simp only [List.length_cons, List.length_append, List.length_singleton, List.length_nil]; omega
  have hbnd₂ : (1 :: (b₂ ++ [1])).length = (1 :: (b₁ ++ [1])).length := by
    simp only [List.length_cons, List.length_append, List.length_singleton, List.length_nil]; omega
  refine ⟨compParams b₁ b₂, ?_, ?_⟩
  · rw [compParams_length hlen]; omega
  · rw [hb₂, hb₁, shiftPad_comp (1 :: (b₁ ++ [1])) (1 :: (b₂ ++ [1])) l₁.1 hbnd₁ hbnd₂,
      show List.zipWith (· * ·) (1 :: (b₁ ++ [1])) (1 :: (b₂ ++ [1]))
        = 1 :: (compParams b₁ b₂ ++ [1]) by
      rw [zipWith_eq_compParams, compParams_cons, show (1 : U) * 1 = 1 by simp,
        compParams_append hlen,
        show compParams ([1] : List U) [1] = [1] by simp [compParams]]]

instance relNESetoid (U : Type) [Group U] : Setoid (NEL (U := U)) where
  r := relNE
  iseqv := ⟨relNE_refl, fun h => relNE_symm h, fun h₁ h₂ => relNE_trans h₁ h₂⟩

/-- The `X`-part of `U ♮ X`, i.e. `⨆_{n ≥ 1} X^{×_U n}`. -/
abbrev XPart (U : Type) [Group U] : Type := Quotient (relNESetoid U)

/-- The free multiplicative monoid `U ♮ X` over the `U`-biset `X = Rat(U)`: the disjoint union of
the group `U` and the `X`-part, with the `U`-actions absorbed. -/
abbrev NU (U : Type) [Group U] : Type := U ⊕ XPart U

namespace NU

variable {U : Type} [Group U]

/-- The group element `u`, as an element of `U ♮ X`. -/
abbrev Ugen (u : U) : NU U := Sum.inl u

/-- The `X`-letter `x`, as an element of `U ♮ X`. -/
abbrev Xgen (x : RatU U) : NU U := Sum.inr (Quotient.mk _ ⟨[x], by simp⟩)

@[simp] theorem Ugen_injective : Function.Injective (Ugen (U := U)) := Sum.inl_injective

theorem Ugen_eq_iff {u v : U} : Ugen u = Ugen v ↔ u = v := ⟨fun h => Sum.inl.inj h, fun h => by rw [h]⟩

theorem Xgen_injective : Function.Injective (Xgen (U := U)) := by
  intro x y h
  suffices hkey : ([x] : List (RatU U)) = [y] by simpa using hkey
  have h' : (Quotient.mk (relNESetoid U) ⟨[x], by simp⟩ : XPart U)
      = Quotient.mk _ ⟨[y], by simp⟩ := Sum.inr.inj h
  have h'' : relNE (⟨[x], by simp⟩ : NEL (U := U)) ⟨[y], by simp⟩ := Quotient.exact h'
  obtain ⟨b, hlen, hb⟩ := h''
  have hb' : ([y] : List (RatU U)) = shiftPad (1 :: (b ++ [1])) [x] := hb
  rw [hb']
  rcases b with _ | ⟨u, us⟩
  · simp [shiftPad]
  · simp [shiftPad] at hlen

theorem Ugen_ne_Xgen (u : U) (x : RatU U) : Ugen u ≠ Xgen x := by
  simp [Ugen, Xgen]

end NU


/-- `mulFirst` of a shifted list: for a parameter list `u :: bs`,
`mulFirst u (shiftPad (u :: bs) l) = shiftPad (1 :: bs) l`. -/
theorem mulFirst_shiftPad_cons (u : U) (bs : List U) (l : List (RatU U))
    (h : (u :: bs).length = l.length + 1) :
    mulFirst u (shiftPad (u :: bs) l) = shiftPad (1 :: bs) l := by
  cases l with
  | nil => simp
  | cons x xs =>
    cases bs with
    | nil => simp only [List.length_cons, List.length_nil] at h; omega
    | cons b₁ bs =>
      simp only [shiftPad_cons, mulFirst_cons, actL, RatU.ofGroup_one, mul_assoc,
        ← RatU.ofGroup_mul u u⁻¹, mul_inv_cancel, mul_one]

/-- **First-letter lemma** for the `X`-part of `U ♮ X`. -/
theorem relNE_first_letter (a a' : RatU U) (L L' : NEL (U := U))
    (h : relNE ⟨a :: L.1, by simp⟩ ⟨a' :: L'.1, by simp⟩) :
    ∃ v : U, a' = actR v a ∧ relNE L ⟨mulFirst v L'.1, mulFirst_ne_nil v L'.2⟩ := by
  obtain ⟨b, hlen, hb⟩ := h
  have hb'' : a' :: L'.1 = shiftPad (1 :: (b ++ [1])) (a :: L.1) := hb
  obtain ⟨v, bs, rfl⟩ : ∃ v bs, b = v :: bs := by
    cases b with
    | nil =>
      exfalso
      have h1 : L.1.length = 0 := by
        have h2 : (1 : ℕ) = L.1.length + 1 := by simpa using hlen
        omega
      exact L.2 (List.length_eq_zero_iff.mp h1)
    | cons v bs => exact ⟨v, bs, rfl⟩
  have hbs : bs.length + 1 = L.1.length := by
    simp only [List.length_cons] at hlen ⊢; omega
  have hb' : a' :: L'.1
      = (RatU.ofGroup v⁻¹ * a * RatU.ofGroup (1 : U)) :: shiftPad (v :: (bs ++ [1])) L.1 := by
    rw [hb'']
    simp only [List.cons_append, shiftPad_cons]
  injection hb' with h1 h2
  refine ⟨v, ?_, bs, hbs, ?_⟩
  · rw [h1]; simp [actR]
  · show mulFirst v L'.1 = shiftPad (1 :: (bs ++ [1])) L.1
    rw [h2, mulFirst_shiftPad_cons v (bs ++ [1]) L.1
      (by simp only [List.length_cons, List.length_append, List.length_singleton, List.length_nil]
          omega)]

end FreeProduct
end Work.ORHughesFree.Rat
