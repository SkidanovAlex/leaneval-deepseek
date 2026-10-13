/-
  WilC6 — C6: model completeness of `ℝ_exp` implies that `ExpExist` is closed under complement.

  This file sets up the *syntactic* notion used throughout the area: the class `IsEF` of
  "existential" formulas over a first-order language, i.e. formulas built from equations and
  inequations of terms by conjunctions, disjunctions and existential quantification.

  The key features of the class, all of which are needed by the argument, are:

  * it contains all quantifier-free formulas up to logical equivalence, and in particular it
    is closed under finite conjunctions and disjunctions (`IsEF.folds_inf`, `IsEF.folds_sup`);
  * it is closed under existential quantification (`IsEF.ex`);
  * over `ℝ` with the language `LEc`, every `IsEF` formula defines an `ExpExist` set
    (`Work.WilC6.IsEF.expExist`, proved in `Submission/Work/WilC6/Flatten.lean`).

  The mathematical content of C6 is the model-theoretic statement
  `Work.WilC6.exists_isEF_iff_of_modelComplete`: over all models of `TE = Th(ℝ_exp)`, every
  formula is equivalent to an `IsEF` formula.  Its proof (Robinson's test for model completeness
  followed by compactness) is assembled in `Submission/Work/WilC6/Main.lean` from

  * `Work.WilC6.transfer_of_isEF` (the amalgamation step, `Transfer.lean`),
  * `Work.WilC6.exists_model_of_isEF` (the compactness step, `Step3.lean`),
  * `Work.WilC6.exists_isEF_of_entails` (the finiteness extraction, `Extract.lean`).
-/
import Submission.Work.Wilkies.CG.Spec
import Mathlib.ModelTheory.Satisfiability
import Mathlib.ModelTheory.Types
import Mathlib.ModelTheory.ElementaryMaps

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open WilkiesDesign WilkiesDesign.CG

namespace Work.WilC6

/-- The class of *existential* formulas of a first-order language: Boolean combinations of
equations and inequations of terms, closed under existential quantification. -/
inductive IsEF {L : Language} {α : Type*} : {n : ℕ} → L.BoundedFormula α n → Prop
  | top {n} : IsEF (⊤ : L.BoundedFormula α n)
  | bot {n} : IsEF (⊥ : L.BoundedFormula α n)
  | bdEq {n} (t₁ t₂ : L.Term (α ⊕ Fin n)) : IsEF (Term.bdEqual t₁ t₂)
  | bdNe {n} (t₁ t₂ : L.Term (α ⊕ Fin n)) :
      IsEF (BoundedFormula.not (Term.bdEqual t₁ t₂))
  | inf {n} {φ ψ : L.BoundedFormula α n} : IsEF φ → IsEF ψ → IsEF (φ ⊓ ψ)
  | sup {n} {φ ψ : L.BoundedFormula α n} : IsEF φ → IsEF ψ → IsEF (φ ⊔ ψ)
  | ex {n} {φ : L.BoundedFormula α (n + 1)} : IsEF φ → IsEF (BoundedFormula.ex φ)

namespace IsEF

variable {L : Language} {α : Type*}

/-- Finite conjunctions of existential formulas are existential. -/
theorem folds_inf {n : ℕ} (l : List (L.BoundedFormula α n)) (h : ∀ φ ∈ l, IsEF φ) :
    IsEF (l.foldr (· ⊓ ·) ⊤) := by
  induction l with
  | nil => exact IsEF.top
  | cons φ l ih =>
      rw [List.foldr_cons]
      exact IsEF.inf (h φ (by simp)) (ih fun ψ hψ => h ψ (by simp [hψ]))

/-- Finite disjunctions of existential formulas are existential. -/
theorem folds_sup {n : ℕ} (l : List (L.BoundedFormula α n)) (h : ∀ φ ∈ l, IsEF φ) :
    IsEF (l.foldr (· ⊔ ·) ⊥) := by
  induction l with
  | nil => exact IsEF.bot
  | cons φ l ih =>
      rw [List.foldr_cons]
      exact IsEF.sup (h φ (by simp)) (ih fun ψ hψ => h ψ (by simp [hψ]))

/-- Existential quantification of all bound variables of an existential formula is existential. -/
theorem exs : ∀ {n : ℕ} {φ : L.BoundedFormula α n}, IsEF φ → IsEF φ.exs
  | 0, _, h => by simpa [BoundedFormula.exs] using h
  | n + 1, φ, h => by
      rw [BoundedFormula.exs]
      exact exs (n := n) (IsEF.ex h)

end IsEF

/-! ### Consequences over the theory `TE` and the associated subsets of `ℝⁿ` -/

/-- `EFCons φ ψ` says that `ψ` is a consequence of `φ` over *all* models of `TE`, where the
free variables of both formulas are the tuple `Fin n`. -/
def EFCons {n : ℕ} (φ ψ : LEc.Formula (Fin n)) : Prop :=
  ∀ (M : Type) [LEc.Structure M] [M ⊨ TE] (x : Fin n → M), φ.Realize x → ψ.Realize x

/-- The subset of `ℝⁿ` defined by a formula in the standard model. -/
def realizeSet {n : ℕ} (φ : LEc.Formula (Fin n)) : Set (Fin n → ℝ) := {x | φ.Realize x}

/-- The standard model is a model of `TE`. -/
instance instRealModelTE : ℝ ⊨ TE := inferInstanceAs (ℝ ⊨ LEc.completeTheory ℝ)

theorem EFCons.refl {n : ℕ} (φ : LEc.Formula (Fin n)) : EFCons φ φ := fun _ _ _ _ h => h

theorem EFCons.trans {n : ℕ} {φ ψ χ : LEc.Formula (Fin n)} (h1 : EFCons φ ψ)
    (h2 : EFCons ψ χ) : EFCons φ χ := fun M _ _ x h => h2 M x (h1 M x h)

theorem EFCons.folds_inf {n : ℕ} {φ : LEc.Formula (Fin n)} (l : List (LEc.Formula (Fin n)))
    (h : ∀ ψ ∈ l, EFCons φ ψ) : EFCons φ (l.foldr (· ⊓ ·) ⊤) := by
  intro M _ _ x hx
  rw [Formula.Realize, BoundedFormula.realize_foldr_inf]
  exact fun ψ hψ => h ψ hψ M x hx

theorem EFCons.folds_sup {n : ℕ} {φ ψ : LEc.Formula (Fin n)} (l : List (LEc.Formula (Fin n)))
    (h : ∀ χ ∈ ψ :: l, EFCons φ χ) : EFCons φ ((ψ :: l).foldr (· ⊔ ·) ⊥) := by
  intro M _ _ x hx
  rw [List.foldr_cons, Formula.Realize, BoundedFormula.realize_sup]
  exact Or.inl (h ψ (List.mem_cons_self ..) M x hx)

end Work.WilC6
