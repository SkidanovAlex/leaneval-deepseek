import Mathlib
import Submission.Work.ORHughesFree.Rat.Orbit

/-!
# Membership in the `V`-part `NUV V` of `U ♮ X` from a `relNE`-equivalent list

The `X`-part `XPart U = NEL ⧸ relNE` of the free product monoid `U ♮ X` is the quotient of the
nonempty lists of `Rat(U)`-letters by the `U`-action `relNE`.  Consequently `Xgen`-multiplication
computes the class of a concatenation, and a list and any `relNE`-translate of it represent the
*same* element of `U ♮ X`:

  `(l.map Xgen).prod = ⟦l⟧`

(`map_Xgen_prod_eq_mk`).  Therefore, if every letter of some translate `l'` of `l` lies in
`Rat.A V` (the image of `Rat(V)` in `Rat(U)`), then `⟦l⟧ = ⟦l'⟧` is a product of `Xgen`'s of letters
of `Rat.A V`, hence a product of generators of `Orbit.NUV V` — the main result of this file.
-/

namespace Work.ORHughesFree.Rat

open Work.ORHughesFree
open Work.ORHughesFree.Rat.FreeProduct

variable {U : Type} [Group U]

/-- A product of `Xgen`'s over a nonempty list is the class of that list in the `X`-part of
`U ♮ X`. -/
theorem map_Xgen_prod_eq_mk (l : List (RatU U)) (hl : l ≠ []) :
    (l.map NU.Xgen).prod =
      (Sum.inr (Quotient.mk (relNESetoid U) (⟨l, hl⟩ : NEL (U := U))) : NU U) := by
  revert hl
  induction l with
  | nil => intro hl; exact absurd rfl hl
  | cons x xs ih =>
    intro hl
    cases xs with
    | nil =>
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    | cons y ys =>
      have hxs : (y :: ys) ≠ ([] : List (RatU U)) := by simp
      rw [List.map_cons, List.prod_cons, ih hxs, NU.Xgen_mul_mk]

/-- A product of `Xgen`'s over a list is in `NUV V` as soon as every letter lies in `Rat.A V`. -/
theorem map_Xgen_prod_mem_NUV (V : Subgroup U) : ∀ (l : List (RatU U)),
    (∀ x ∈ l, x ∈ A V) → (l.map NU.Xgen).prod ∈ Orbit.NUV V := by
  intro l
  induction l with
  | nil => intro _; exact (Orbit.NUV V).one_mem
  | cons x xs ih =>
    intro hall
    rw [List.map_cons, List.prod_cons]
    exact (Orbit.NUV V).mul_mem (Orbit.Xgen_mem_NUV (hall x (by simp)))
      (ih (fun y hy => hall y (by simp [hy])))

theorem mem_NUV_of_relNE {U : Type} [Group U] (V : Subgroup U) {l l' : List (Work.ORHughesFree.RatU U)}
    (hl : l ≠ []) (hl' : l' ≠ [])
    (h : Work.ORHughesFree.Rat.FreeProduct.relNE ⟨l, hl⟩ ⟨l', hl'⟩)
    (hall : ∀ x ∈ l', x ∈ Work.ORHughesFree.Rat.A V) :
    ((Sum.inr (Quotient.mk (Work.ORHughesFree.Rat.FreeProduct.relNESetoid U) ⟨l, hl⟩) :
        Work.ORHughesFree.Rat.FreeProduct.NU U)) ∈ Work.ORHughesFree.Rat.Orbit.NUV V := by
  -- `l` and `l'` represent the same class of `XPart U`
  have hq : (Quotient.mk (FreeProduct.relNESetoid U) (⟨l, hl⟩ : FreeProduct.NEL (U := U)) :
        FreeProduct.XPart U) =
      Quotient.mk _ (⟨l', hl'⟩ : FreeProduct.NEL (U := U)) := Quotient.sound h
  -- the class of `l'` is a product of `Xgen`'s of letters of `Rat.A V`
  have hmem : ((Sum.inr (Quotient.mk (FreeProduct.relNESetoid U)
      (⟨l', hl'⟩ : FreeProduct.NEL (U := U))) : FreeProduct.NU U)) ∈ Orbit.NUV V := by
    rw [← map_Xgen_prod_eq_mk l' hl']
    exact map_Xgen_prod_mem_NUV V l' hall
  rw [hq]
  exact hmem

end Work.ORHughesFree.Rat
