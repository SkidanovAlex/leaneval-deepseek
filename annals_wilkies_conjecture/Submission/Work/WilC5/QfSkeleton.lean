/-
  WilC5 — the quantifier-free skeleton of a formula, and its meaning in an empty structure.

  The target `Work.WilC5.HasQE` quantifies over *all* `L`-structures `M` with `M ⊨ T`, including
  the empty ones.  A structure with no elements satisfies every universally quantified formula, so
  the truth value of a formula in the empty structure is computed by replacing every universal
  quantifier by `⊤`.  `qfSkeleton` performs that replacement, is quantifier-free, and — in a
  structure with no elements — does not change the truth value of a formula.

  This is one of the two inputs to the reduction of the empty case of `HasQEOfQfTypeDetermines` to
  the nonempty case.
-/
import Mathlib

set_option autoImplicit false
noncomputable section
namespace Work.WilC5

open FirstOrder Language

/-- The quantifier-free skeleton of a bounded formula: every universal quantifier is replaced by
`⊤`. -/
def qfSkeleton {L : FirstOrder.Language} {α : Type} :
    ∀ {n : ℕ}, L.BoundedFormula α n → L.BoundedFormula α n
  | _, .falsum => .falsum
  | _, .equal t₁ t₂ => .equal t₁ t₂
  | _, .rel R ts => .rel R ts
  | _, .imp f₁ f₂ => .imp (qfSkeleton f₁) (qfSkeleton f₂)
  | _, .all _ => ⊤

/-- The skeleton is quantifier-free. -/
theorem isQF_qfSkeleton {L : FirstOrder.Language} {α : Type} :
    ∀ {n : ℕ} (φ : L.BoundedFormula α n), (qfSkeleton φ).IsQF
  | _, .falsum => BoundedFormula.IsQF.falsum
  | _, .equal _ _ => BoundedFormula.IsQF.of_isAtomic (BoundedFormula.IsAtomic.equal _ _)
  | _, .rel _ _ => BoundedFormula.IsQF.of_isAtomic (BoundedFormula.IsAtomic.rel _ _)
  | _, .imp a b => BoundedFormula.IsQF.imp (isQF_qfSkeleton a) (isQF_qfSkeleton b)
  | _, .all _ => BoundedFormula.IsQF.imp BoundedFormula.IsQF.falsum BoundedFormula.IsQF.falsum

/-- **The skeleton computes the truth value in an empty structure.**  If `M` has no elements, then
replacing the universal quantifiers of `φ` by `⊤` does not change the realization of `φ`. -/
theorem qfSkeleton_realize {L : FirstOrder.Language} {α : Type} {M : Type} [L.Structure M]
    [IsEmpty M] :
    ∀ {n : ℕ} (φ : L.BoundedFormula α n) (v : α → M) (xs : Fin n → M),
      (qfSkeleton φ).Realize v xs ↔ φ.Realize v xs
  | _, .falsum, v, xs => Iff.rfl
  | _, .equal t₁ t₂, v, xs => Iff.rfl
  | _, .rel R ts, v, xs => Iff.rfl
  | _, .imp a b, v, xs => by
      change (qfSkeleton a ⟹ qfSkeleton b).Realize v xs ↔ (a ⟹ b).Realize v xs
      rw [BoundedFormula.realize_imp, BoundedFormula.realize_imp]
      exact ⟨fun h ha => (qfSkeleton_realize b v xs).mp (h ((qfSkeleton_realize a v xs).mpr ha)),
             fun h ha => (qfSkeleton_realize b v xs).mpr (h ((qfSkeleton_realize a v xs).mp ha))⟩
  | _, .all f, v, xs => by
      change (⊤ : L.BoundedFormula α _).Realize v xs ↔ (∀' f).Realize v xs
      rw [BoundedFormula.realize_top]
      exact ⟨fun _ x => isEmptyElim x, fun _ => trivial⟩

/-- The `Formula.Realize` form of `qfSkeleton_realize`, for formulas with no free variables. -/
theorem qfSkeleton_realize_formula {L : FirstOrder.Language} {M : Type} [L.Structure M]
    [IsEmpty M] (φ : L.Formula (Fin 0)) (v : Fin 0 → M) :
    @Formula.Realize L M _ (Fin 0) (qfSkeleton φ) v ↔ @Formula.Realize L M _ (Fin 0) φ v :=
  qfSkeleton_realize φ v default

end Work.WilC5
