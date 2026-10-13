/-
  WilC5 — syntactic machinery for the transfinite construction of `κ`-saturated elementary
  extensions (part 2).

  This file sets up the *level-indexed constants* of the construction.

  * `SatTyp2 L C` — a "type over constants" whose *parameters are closed terms* of the language
    `L[[C]]`: a set `A` of closed terms together with a set of formulas with those parameters and
    one further free variable.  Using terms (rather than constants) as parameters is what makes the
    final argument work: every element of the term hull is named by a closed term, hence the type
    of a small set of elements of the hull translates directly into a type over the constants of a
    single level.
  * `SatCons2 T p` — consistency of the type `p` with the theory `T`: every finite fragment's
    sentence `∃y ⋀ F` belongs to `T`.
  * `SatNew L M κ x` — the constants created at level `x`: they are the types over the constants of
    the levels below `x`.
  * `SatC L M κ x` — the constants available at level `x`; the seed constants (indexed by the
    carrier `M` itself, used to record the elementary diagram of `M`) together with the constants of
    birth level `< x`.
  * `SatInc`/`SatIncTotal` — the (definitional) inclusions `C x → C y` for `x ≤ y` and
    `C x → C_total`.
-/
import Mathlib
import Submission.Work.WilC5.SatSetup

open FirstOrder Language
open scoped FirstOrder

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilC5

/-- A "type" over the constants `C`, with **term parameters**: a set `A` of closed terms of the
language `L[[C]]` together with a set of formulas whose free variables are the parameters `A` and
one further distinguished variable (the variable of the type). -/
def SatTyp2 (L : FirstOrder.Language.{0, 0}) (C : Type) : Type :=
  Σ (A : Set ((L[[C]]).Term Empty)), Set ((L[[C]]).Formula (A ⊕ Fin 1))

namespace SatTyp2

variable {L : FirstOrder.Language.{0, 0}} {C : Type}

/-- The conjunction of the (finitely many) formulas of a finite subset of a type. -/
def conj (p : SatTyp2 L C) (F : Finset ((L[[C]]).Formula (p.1 ⊕ Fin 1))) :
    (L[[C]]).Formula (p.1 ⊕ Fin 1) :=
  F.toList.foldr (fun φ acc => φ ⊓ acc) ⊤

/-- The formula `∃y ⋀ F` (with the parameters still free). -/
def ex (p : SatTyp2 L C) (F : Finset ((L[[C]]).Formula (p.1 ⊕ Fin 1))) :
    (L[[C]]).Formula p.1 :=
  (BoundedFormula.relabel (n := 1) (k := 0) (β := p.1) id (conj p F)).ex

/-- The sentence `∃y ⋀ F` obtained by replacing the parameters by the corresponding closed
terms. -/
def sent (p : SatTyp2 L C) (F : Finset ((L[[C]]).Formula (p.1 ⊕ Fin 1))) :
    (L[[C]]).Sentence :=
  (ex p F).subst (fun a => a.1)

end SatTyp2

variable {L : FirstOrder.Language.{0, 0}} {C : Type}

/-- A type `p` is *consistent* with a theory `T` when every finite fragment of `p` is satisfiable,
in the sense that the sentence `∃y ⋀ F` (with the parameters replaced by the corresponding terms)
belongs to `T`. -/
def SatCons2 (T : (L[[C]]).Theory) (p : SatTyp2 L C) : Prop :=
  ∀ F : Finset ((L[[C]]).Formula (p.1 ⊕ Fin 1)), (∀ φ ∈ F, φ ∈ p.2) → p.sent F ∈ T

/-- The witness sentence attached to a formula `φ` of a type `p`: the sentence saying that the
constant `cnew p` satisfies `φ` (with the parameters of `p` substituted as terms). -/
def SatWitSent2 {C' : Type} (inc : C → C') (cnew : SatTyp2 L C → C')
    (p : SatTyp2 L C) (φ : (L[[C]]).Formula (p.1 ⊕ Fin 1)) : (L[[C']]).Sentence :=
  ((SatLangMap inc).onFormula φ).subst fun i : p.1 ⊕ Fin 1 =>
    match i with
    | Sum.inl a => (SatLangMap inc).onTerm a.1
    | Sum.inr _ => (Constants.term (Sum.inr (cnew p)) : (L[[C']]).Term Empty)

/-- The set of witness sentences attached to a type `p`: all the sentences `cnew p ⊨ φ`,
`φ ∈ p`. -/
def SatWit2 {C' : Type} (inc : C → C') (cnew : SatTyp2 L C → C') (p : SatTyp2 L C) :
    (L[[C']]).Theory :=
  {σ | ∃ φ : (L[[C]]).Formula (p.1 ⊕ Fin 1), φ ∈ p.2 ∧ σ = SatWitSent2 inc cnew p φ}

/-! ## Level-indexed constants -/

variable (L : FirstOrder.Language.{0, 0}) (M : Type) (κ : Cardinal.{0})

/-- The constants created at level `x`: the types over the constants of the levels below `x`. -/
noncomputable def SatNew : SatIdx κ → Type :=
  (inferInstance : WellFounded (· < · : SatIdx κ → SatIdx κ → Prop)).fix
    fun x rec => SatTyp2 L (M ⊕ Σ (y : {y : SatIdx κ // y < x}), rec y.1 y.2)

/-- The constants available at level `x`: the seed constants (indexed by `M`) and the constants of
birth level `< x`. -/
noncomputable def SatC (x : SatIdx κ) : Type :=
  M ⊕ Σ (y : {y : SatIdx κ // y < x}), SatNew L M κ y.1

/-- The total set of constants: the seed constants and *all* the constants created at any level. -/
noncomputable def SatCTotal : Type :=
  M ⊕ Σ (y : SatIdx κ), SatNew L M κ y

theorem SatNew_eq (x : SatIdx κ) :
    SatNew L M κ x = SatTyp2 L (SatC L M κ x) := by
  rw [SatNew, WellFounded.fix_eq]
  simp only [SatC, SatNew]

/-- The inclusion of the constants of level `x` into those of level `y`, for `x ≤ y`. -/
noncomputable def SatInc {x y : SatIdx κ} (h : x ≤ y) : SatC L M κ x → SatC L M κ y
  | Sum.inl m => Sum.inl m
  | Sum.inr ⟨⟨u, hu⟩, a⟩ => Sum.inr ⟨⟨u, lt_of_lt_of_le hu h⟩, a⟩

/-- The inclusion of the constants of level `x` into the total set of constants. -/
noncomputable def SatIncTotal (x : SatIdx κ) : SatC L M κ x → SatCTotal L M κ
  | Sum.inl m => Sum.inl m
  | Sum.inr ⟨⟨u, _⟩, a⟩ => Sum.inr ⟨u, a⟩

@[simp]
theorem SatInc_inl {x y : SatIdx κ} (h : x ≤ y) (m : M) :
    SatInc L M κ h (Sum.inl m) = Sum.inl m := rfl

@[simp]
theorem SatInc_inr {x y : SatIdx κ} (h : x ≤ y) (u : SatIdx κ) (hu : u < x)
    (a : SatNew L M κ u) :
    SatInc L M κ h (Sum.inr ⟨⟨u, hu⟩, a⟩) = Sum.inr ⟨⟨u, lt_of_lt_of_le hu h⟩, a⟩ := rfl

@[simp]
theorem SatIncTotal_inl (x : SatIdx κ) (m : M) :
    SatIncTotal L M κ x (Sum.inl m) = Sum.inl m := rfl

@[simp]
theorem SatIncTotal_inr (x : SatIdx κ) (u : SatIdx κ) (hu : u < x) (a : SatNew L M κ u) :
    SatIncTotal L M κ x (Sum.inr ⟨⟨u, hu⟩, a⟩) = Sum.inr ⟨u, a⟩ := rfl

theorem SatIncTotal_injective (x : SatIdx κ) : Function.Injective (SatIncTotal L M κ x) := by
  intro c d h
  cases c with
  | inl m =>
    cases d with
    | inl m' =>
      exact congrArg Sum.inl (Sum.inl_injective h)
    | inr q =>
      obtain ⟨⟨u, hu⟩, a⟩ := q
      exact absurd h (by simp)
  | inr p =>
    obtain ⟨⟨u, hu⟩, a⟩ := p
    cases d with
    | inl m =>
      exact absurd h (by simp)
    | inr q =>
      obtain ⟨⟨u', hu'⟩, a'⟩ := q
      have h2 : (⟨u, a⟩ : Σ v : SatIdx κ, SatNew L M κ v) = ⟨u', a'⟩ := Sum.inr_injective h
      obtain ⟨rfl, rfl⟩ := h2
      rfl

theorem SatIncTotal_comp {x y : SatIdx κ} (h : x ≤ y) :
    (SatIncTotal L M κ y) ∘ (SatInc L M κ h) = SatIncTotal L M κ x := by
  funext c
  cases c with
  | inl m => rfl
  | inr p => obtain ⟨⟨u, hu⟩, a⟩ := p; rfl

theorem SatInc_injective {x y : SatIdx κ} (h : x ≤ y) : Function.Injective (SatInc L M κ h) := by
  intro c d hcd
  apply SatIncTotal_injective L M κ x
  rw [show SatIncTotal L M κ x c = SatIncTotal L M κ y (SatInc L M κ h c) from
        congrFun (SatIncTotal_comp L M κ h).symm c,
      show SatIncTotal L M κ x d = SatIncTotal L M κ y (SatInc L M κ h d) from
        congrFun (SatIncTotal_comp L M κ h).symm d,
      hcd]

@[simp]
theorem SatInc_id {x : SatIdx κ} : SatInc L M κ (le_refl x) = id := by
  funext c
  cases c with
  | inl m => rfl
  | inr p => obtain ⟨⟨u, hu⟩, a⟩ := p; rfl

theorem SatInc_comp {x y z : SatIdx κ} (hxy : x ≤ y) (hyz : y ≤ z) :
    (SatInc L M κ hyz) ∘ (SatInc L M κ hxy) = SatInc L M κ (le_trans hxy hyz) := by
  funext c
  cases c with
  | inl m => rfl
  | inr p => obtain ⟨⟨u, hu⟩, a⟩ := p; rfl

end Work.WilC5
