import Mathlib
import Submission.Work.OROneRel.GaugeDefs

/-!
# Truncation of the gauge rewriting to the letters of non-trivial loop class

`gaugeMap W c (mk (decor c 0 (wordOf u))) = u` (`gauge_decor_zero`) says that the product of the
loop classes of *all* decorated letters of `u` is `u`.  Here we show that the letters whose loop
class is trivial may be deleted: the product of the loop classes of the decorated letters of
non-trivial loop class is still `u`.

This is the combinatorial input for the Magnus--Moldavanskii step in the case where no letter of the
relator has vanishing exponent sum: the decorated letters of non-trivial loop class form the
generating set `β` of the shorter one-relator group `⟨β | v ^ l⟩`, and `v ^ l` maps to `u ^ l = 1`.
-/

namespace Work.OROneRel

universe u

variable {α : Type u}

/-- **The product of the images of the letters of a word.**  If `φ : F β →* M` is a homomorphism,
then the images of the letters of a word `L` multiply to the image of the word: the letter `(a, b)`
contributes `φ a` if `b = true` and `φ a⁻¹` otherwise. -/
theorem map_prod_eq_of_mk {β : Type*} {M : Type*} [Group M] (φ : FreeGroup β →* M)
    (L : List (β × Bool)) :
    (L.map (fun p => φ (if p.2 then FreeGroup.of p.1 else (FreeGroup.of p.1)⁻¹))).prod
      = φ (FreeGroup.mk L) := by
  induction L with
  | nil => simp [show FreeGroup.mk ([] : List (β × Bool)) = (1 : FreeGroup β) from rfl]
  | cons p t ih =>
    obtain ⟨a, b⟩ := p
    cases b
    · have h : FreeGroup.mk ((a, false) :: t) = (FreeGroup.of a)⁻¹ * FreeGroup.mk t := by
        rw [FreeGroup.of, FreeGroup.inv_mk, FreeGroup.mul_mk]; rfl
      simp only [Bool.false_eq_true, ↓reduceIte, List.map_cons, List.prod_cons, ih, h, map_mul,
        map_inv]
    · have h : FreeGroup.mk ((a, true) :: t) = FreeGroup.of a * FreeGroup.mk t := by
        rw [FreeGroup.of, FreeGroup.mul_mk]; rfl
      simp only [↓reduceIte, List.map_cons, List.prod_cons, ih, h, map_mul]

/-- **Deleting the trivial factors does not change a product.**  If a `Bool`-valued predicate `P`
selects exactly the letters with `f p ≠ 1`, then filtering by `P` before mapping by `f` leaves the
product of the images unchanged. -/
theorem filter_map_prod_eq {β M : Type*} [Monoid M] (f : β → M) (P : β → Bool)
    (hP : ∀ p, P p = true ↔ f p ≠ 1) (L : List β) :
    ((L.filter P).map f).prod = (L.map f).prod := by
  induction L with
  | nil => simp
  | cons p t ih =>
    rw [List.filter_cons]
    by_cases hp : P p = true
    · rw [if_pos hp, List.map_cons, List.prod_cons, ih, List.map_cons, List.prod_cons]
    · rw [if_neg hp, ih, List.map_cons, List.prod_cons]
      have h1 : f p = 1 := by
        by_contra h
        exact hp ((hP p).mpr h)
      rw [h1, one_mul]

theorem gauge_truncation {α : Type*} (W : ℤ → FreeGroup α) (hW : W 0 = 1) {c : α → ℤ}
    {u : FreeGroup α} (hu : cohom c u = 1) (P : ((α × ℤ) × Bool) → Bool)
    (hP : ∀ p, P p = true ↔
      gaugeMap W c (if p.2 then FreeGroup.of p.1 else (FreeGroup.of p.1)⁻¹) ≠ 1) :
    (((decor c 0 (wordOf u)).filter P).map
        (fun p => gaugeMap W c (if p.2 then FreeGroup.of p.1 else (FreeGroup.of p.1)⁻¹))).prod = u := by
  rw [filter_map_prod_eq _ P hP]
  rw [map_prod_eq_of_mk]
  exact gauge_decor_zero W hW hu

end Work.OROneRel
