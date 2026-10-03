import Mathlib
import Submission.Work.ORHughesFree.Rat.FreeProduct.NU
import Submission.Work.ORHughesFree.Rat.FreeProduct.shiftPad_mulFirst
import Submission.Work.ORHughesFree.Rat.FreeProduct.shiftPad_mulLast
import Submission.Work.ORHughesFree.Rat.FreeProduct.shiftPad_append_right
import Submission.Work.ORHughesFree.Rat.FreeProduct.relNE_mulFirst
import Submission.Work.ORHughesFree.Rat.FreeProduct.relNE_mulLast
import Submission.Work.ORHughesFree.Rat.FreeProduct.relNE_append
import Submission.Work.ORHughesFree.Rat.FreeProduct.relNE_mulLast_append

/-!
# The monoid structure on `U ♮ X`

This file puts the monoid structure on `Work.ORHughesFree.Rat.FreeProduct.NU U = U ⊕ XPart U`,
together with the computation rules
`Ugen u * Ugen v = Ugen (u * v)`, `Ugen u * Xgen x = Xgen (actL u x)`,
`Xgen x * Ugen u = Xgen (actR u x)` and the product rules for two `X`-letters.
-/

set_option autoImplicit false

namespace Work.ORHughesFree.Rat
namespace FreeProduct

open Work.ORHughesFree

variable {U : Type} [Group U]

namespace NU

/-! ### Elementary list lemmas -/

theorem mulFirst_append (u : U) {L : List (RatU U)} (hL : L ≠ []) (M : List (RatU U)) :
    mulFirst u (L ++ M) = mulFirst u L ++ M := by
  obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil hL
  rfl

theorem mulFirst_mulFirst (u v : U) {L : List (RatU U)} (hL : L ≠ []) :
    mulFirst (u * v) L = mulFirst u (mulFirst v L) := by
  obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil hL
  simp [mulFirst, actL_mul]

theorem mulLast_cons_ne_nil (u : U) (a : RatU U) (ys : List (RatU U)) (h : ys ≠ []) :
    mulLast (a :: ys) u = a :: mulLast ys u := by
  obtain ⟨y, ys', rfl⟩ := List.exists_cons_of_ne_nil h
  rfl

theorem mulLast_append (u : U) (L : List (RatU U)) {M : List (RatU U)} (hM : M ≠ []) :
    mulLast (L ++ M) u = L ++ mulLast M u := by
  induction L with
  | nil => simp
  | cons x xs ih =>
    have hxs : xs ++ M ≠ [] := fun h => hM (List.append_eq_nil_iff.mp h).2
    rw [List.cons_append, mulLast_cons_ne_nil u x (xs ++ M) hxs, ih, List.cons_append]

theorem mulLast_mulLast (L : List (RatU U)) (u v : U) :
    mulLast (mulLast L u) v = mulLast L (u * v) := by
  induction L with
  | nil => simp [mulLast]
  | cons x xs ih =>
    cases xs with
    | nil => simp [mulLast, actR_mul]
    | cons y ys =>
      have h1 : (y :: ys) ≠ [] := by simp
      have h2 : mulLast (y :: ys) u ≠ [] := mulLast_ne_nil u h1
      rw [mulLast_cons_ne_nil u x (y :: ys) h1, mulLast_cons_ne_nil v x (mulLast (y :: ys) u) h2,
        mulLast_cons_ne_nil (u * v) x (y :: ys) h1, ih]

theorem mulFirst_mulLast {L : List (RatU U)} (hL : L ≠ []) (u v : U) :
    mulFirst u (mulLast L v) = mulLast (mulFirst u L) v := by
  obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil hL
  cases xs with
  | nil => simp [mulLast, mulFirst, actL_actR]
  | cons y ys => rfl

theorem mulLast_one (L : List (RatU U)) : mulLast L (1 : U) = L := by
  induction L with
  | nil => simp [mulLast]
  | cons x xs ih =>
    cases xs with
    | nil => simp [mulLast]
    | cons y ys =>
      rw [mulLast_cons_ne_nil 1 x (y :: ys) (by simp), ih]

/-! ### The multiplication -/

noncomputable instance instMul : Mul (NU U) where
  mul x y :=
    match x, y with
    | Sum.inl u, Sum.inl v => Sum.inl (u * v)
    | Sum.inl u, Sum.inr L =>
        Sum.inr (Quotient.map (fun M : NEL (U := U) =>
            (⟨mulFirst u M.1, mulFirst_ne_nil u M.2⟩ : NEL (U := U)))
          (fun _ _ h => relNE_mulFirst u h) L)
    | Sum.inr L, Sum.inl v =>
        Sum.inr (Quotient.map (fun M : NEL (U := U) =>
            (⟨mulLast M.1 v, mulLast_ne_nil v M.2⟩ : NEL (U := U)))
          (fun _ _ h => relNE_mulLast v h) L)
    | Sum.inr L, Sum.inr M =>
        Sum.inr (Quotient.map₂
          (fun (l : NEL (U := U)) (m : NEL (U := U)) =>
            (⟨l.1 ++ m.1, by simp [l.2]⟩ : NEL (U := U)))
          (fun _ _ h1 _ _ h2 => relNE_append h1 h2) L M)

instance instOne : One (NU U) := ⟨Sum.inl 1⟩

/-- Two quotient classes of `X`-words with the same underlying list are equal. -/
theorem mk_eq_mk_of_eq {L M : NEL (U := U)} (h : L.1 = M.1) :
    (Quotient.mk _ L : XPart U) = Quotient.mk _ M := by
  rw [show L = M from Subtype.ext h]

@[simp] theorem inl_mul_inl (u v : U) :
    (Sum.inl u : NU U) * Sum.inl v = Sum.inl (u * v) := rfl

@[simp] theorem inl_mul_mk (u : U) (L : NEL (U := U)) :
    (Sum.inl u : NU U) * (Sum.inr (Quotient.mk _ L) : NU U)
      = Sum.inr (Quotient.mk _ (⟨mulFirst u L.1, mulFirst_ne_nil u L.2⟩ : NEL (U := U))) := by
  show Sum.inr (Quotient.map
      (fun M : NEL (U := U) => (⟨mulFirst u M.1, mulFirst_ne_nil u M.2⟩ : NEL (U := U)))
      (fun _ _ h => relNE_mulFirst u h) (Quotient.mk _ L)) = _
  rw [Quotient.map_mk]

@[simp] theorem mk_mul_inl (L : NEL (U := U)) (u : U) :
    (Sum.inr (Quotient.mk _ L) : NU U) * Sum.inl u
      = Sum.inr (Quotient.mk _ (⟨mulLast L.1 u, mulLast_ne_nil u L.2⟩ : NEL (U := U))) := by
  show Sum.inr (Quotient.map
      (fun M : NEL (U := U) => (⟨mulLast M.1 u, mulLast_ne_nil u M.2⟩ : NEL (U := U)))
      (fun _ _ h => relNE_mulLast u h) (Quotient.mk _ L)) = _
  rw [Quotient.map_mk]

@[simp] theorem mk_mul_mk (L M : NEL (U := U)) :
    (Sum.inr (Quotient.mk _ L) : NU U) * Sum.inr (Quotient.mk _ M)
      = Sum.inr (Quotient.mk _ (⟨L.1 ++ M.1, by simp [L.2]⟩ : NEL (U := U))) := by
  show Sum.inr (Quotient.map₂
      (fun (l : NEL (U := U)) (m : NEL (U := U)) =>
        (⟨l.1 ++ m.1, by simp [l.2]⟩ : NEL (U := U)))
      (fun _ _ h1 _ _ h2 => relNE_append h1 h2) (Quotient.mk _ L) (Quotient.mk _ M)) = _
  rw [Quotient.map₂_mk]

@[simp] theorem Ugen_mul (u v : U) : Ugen u * Ugen v = Ugen (u * v) := rfl

@[simp] theorem Ugen_mul_Xgen (u : U) (x : RatU U) :
    Ugen u * Xgen x = Xgen (actL u x) := by
  show (Sum.inl u : NU U) * Sum.inr (Quotient.mk _ (⟨[x], by simp⟩ : NEL (U := U)))
      = Sum.inr (Quotient.mk _ (⟨[actL u x], by simp⟩ : NEL (U := U)))
  rw [inl_mul_mk]
  exact congrArg Sum.inr (mk_eq_mk_of_eq (by simp [mulFirst]))

@[simp] theorem Xgen_mul_Ugen (x : RatU U) (u : U) :
    Xgen x * Ugen u = Xgen (actR u x) := by
  show (Sum.inr (Quotient.mk _ (⟨[x], by simp⟩ : NEL (U := U))) : NU U) * Sum.inl u
      = Sum.inr (Quotient.mk _ (⟨[actR u x], by simp⟩ : NEL (U := U)))
  rw [mk_mul_inl]
  exact congrArg Sum.inr (mk_eq_mk_of_eq (by simp [mulLast]))

@[simp] theorem Xgen_mul_Xgen (x y : RatU U) :
    Xgen x * Xgen y
      = Sum.inr (Quotient.mk _ (⟨[x, y], by simp⟩ : NEL (U := U))) := by
  show (Sum.inr (Quotient.mk _ (⟨[x], by simp⟩ : NEL (U := U))) : NU U)
      * Sum.inr (Quotient.mk _ (⟨[y], by simp⟩ : NEL (U := U)))
      = Sum.inr (Quotient.mk _ (⟨[x, y], by simp⟩ : NEL (U := U)))
  rw [mk_mul_mk]
  exact congrArg Sum.inr (mk_eq_mk_of_eq (by simp))

@[simp] theorem Ugen_mul_mk (u : U) (L : NEL (U := U)) :
    Ugen u * Sum.inr (Quotient.mk _ L)
      = Sum.inr (Quotient.mk _ (⟨mulFirst u L.1, mulFirst_ne_nil u L.2⟩ : NEL (U := U))) :=
  inl_mul_mk u L

@[simp] theorem mk_mul_Ugen (L : NEL (U := U)) (u : U) :
    Sum.inr (Quotient.mk _ L) * Ugen u
      = Sum.inr (Quotient.mk _ (⟨mulLast L.1 u, mulLast_ne_nil u L.2⟩ : NEL (U := U))) :=
  mk_mul_inl L u

@[simp] theorem Xgen_mul_mk (x : RatU U) (M : NEL (U := U)) :
    Xgen x * Sum.inr (Quotient.mk _ M)
      = Sum.inr (Quotient.mk _ (⟨x :: M.1, by simp⟩ : NEL (U := U))) := by
  show (Sum.inr (Quotient.mk _ (⟨[x], by simp⟩ : NEL (U := U))) : NU U)
      * Sum.inr (Quotient.mk _ M)
      = Sum.inr (Quotient.mk _ (⟨x :: M.1, by simp⟩ : NEL (U := U)))
  rw [mk_mul_mk]
  exact congrArg Sum.inr (mk_eq_mk_of_eq (by simp))

/-! ### The monoid structure -/

noncomputable instance instMonoid : Monoid (NU U) where
  mul := (· * ·)
  one := 1
  one_mul x := by
    rcases x with u | L
    · show (Sum.inl (1 : U) : NU U) * Sum.inl u = Sum.inl u
      rw [inl_mul_inl, one_mul]
    · refine Quotient.inductionOn L (fun L0 => ?_)
      show (Sum.inl (1 : U) : NU U) * Sum.inr (Quotient.mk _ L0) = Sum.inr (Quotient.mk _ L0)
      rw [inl_mul_mk]
      exact congrArg Sum.inr (mk_eq_mk_of_eq (mulFirst_one L0.1))
  mul_one x := by
    rcases x with u | L
    · show (Sum.inl u : NU U) * Sum.inl (1 : U) = Sum.inl u
      rw [inl_mul_inl, mul_one]
    · refine Quotient.inductionOn L (fun L0 => ?_)
      show (Sum.inr (Quotient.mk _ L0) : NU U) * Sum.inl (1 : U) = Sum.inr (Quotient.mk _ L0)
      rw [mk_mul_inl]
      exact congrArg Sum.inr (mk_eq_mk_of_eq (mulLast_one L0.1))
  mul_assoc x y z := by
    rcases x with u | L
    · rcases y with v | M
      · rcases z with w | P
        · show (Sum.inl u : NU U) * Sum.inl v * Sum.inl w
              = Sum.inl u * (Sum.inl v * Sum.inl w)
          simp only [inl_mul_inl, mul_assoc]
        · refine Quotient.inductionOn P (fun P0 => ?_)
          simp only [inl_mul_inl, inl_mul_mk]
          exact congrArg Sum.inr (mk_eq_mk_of_eq (mulFirst_mulFirst u v P0.2))
      · refine Quotient.inductionOn M (fun M0 => ?_)
        rcases z with w | P
        · simp only [inl_mul_mk, mk_mul_inl]
          exact congrArg Sum.inr (mk_eq_mk_of_eq (mulFirst_mulLast M0.2 u w).symm)
        · refine Quotient.inductionOn P (fun P0 => ?_)
          simp only [inl_mul_mk, mk_mul_mk]
          exact congrArg Sum.inr (mk_eq_mk_of_eq (mulFirst_append u M0.2 P0.1).symm)
    · refine Quotient.inductionOn L (fun L0 => ?_)
      rcases y with v | M
      · rcases z with w | P
        · simp only [mk_mul_inl, inl_mul_inl]
          exact congrArg Sum.inr (mk_eq_mk_of_eq (mulLast_mulLast L0.1 v w))
        · refine Quotient.inductionOn P (fun P0 => ?_)
          simp only [mk_mul_inl, mk_mul_mk, inl_mul_mk]
          exact congrArg Sum.inr (Quotient.sound (relNE_mulLast_append L0 P0 v))
      · refine Quotient.inductionOn M (fun M0 => ?_)
        rcases z with w | P
        · simp only [mk_mul_mk, mk_mul_inl]
          exact congrArg Sum.inr (mk_eq_mk_of_eq (mulLast_append w L0.1 M0.2))
        · refine Quotient.inductionOn P (fun P0 => ?_)
          simp only [mk_mul_mk]
          exact congrArg Sum.inr (mk_eq_mk_of_eq (List.append_assoc L0.1 M0.1 P0.1))

end NU

end FreeProduct
end Work.ORHughesFree.Rat
