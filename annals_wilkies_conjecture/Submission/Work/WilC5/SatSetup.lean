/-
  WilC5 — the *syntactic* transfinite construction of `κ`-saturated elementary extensions.

  This file sets up the syntactic gadgets for the transfinite (Henkin-style) construction:

  * `SatIdx κ` — the well-ordered index set, of order type `(κ + ℵ₀)⁺⁺`;
  * `SatTyp L C` — the "types over the constants `C`": a set `A ⊆ C` of parameters together with a
    set of `L[[C]]`-formulas in the parameters `A` and one further free variable;
  * `SatTyp.conj`/`SatTyp.ex`/`SatTyp.sent` — the sentence `∃y ⋀ F` associated with a finite set of
    formulas of a type;
  * `SatCons T p` — the consistency of the type `p` with the theory `T` (every finite fragment is
    satisfiable in the strong sense that its sentence lies in `T`; for the complete theories used
    below this is the same as finite satisfiability).

  The construction proper (the recursion over `SatIdx κ`) and the final model live in
  `Work.WilC5.ExistsSaturated`.
-/
import Mathlib

open FirstOrder Language
open scoped FirstOrder

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilC5

/-- The index set of the transfinite construction: a well-ordered type of order type
`(κ + ℵ₀)⁺⁺`, the second successor cardinal of `κ + ℵ₀`.

Its relevant properties are `bddAbove_satIdx` (every set of fewer than `κ` elements is bounded
above) and `SatIdx.noMaxOrder` (every element has a successor). -/
noncomputable abbrev SatIdx (κ : Cardinal.{0}) : Type :=
  (Order.succ (Order.succ (κ + Cardinal.aleph0))).ord.ToType

instance (κ : Cardinal.{0}) : LinearOrder (SatIdx κ) := inferInstance

instance (κ : Cardinal.{0}) : WellFoundedLT (SatIdx κ) := inferInstance

instance (κ : Cardinal.{0}) : SuccOrder (SatIdx κ) := inferInstance

/-- The language `L[[C]]` of `L` expanded by constants indexed by `C`, written without notation so
that it can be used in theorem statements without any notation scope being open. -/
abbrev SatLang (L : FirstOrder.Language.{0, 0}) (C : Type) : FirstOrder.Language.{0, 0} :=
  FirstOrder.Language.withConstants L C

/-- A "type" over the constants `C` of the language `L[[C]]`: a set `A ⊆ C` of parameters together
with a set of `L[[C]]`-formulas with free variables the parameters `A` and one further free
variable.  (The parameter variables are meant to be interpreted by the corresponding constants and
the last variable by the element whose type it is.) -/
def SatTyp (L : FirstOrder.Language.{0, 0}) (C : Type) : Type :=
  Σ (A : Set C), Set ((L[[C]]).Formula (A ⊕ Fin 1))

namespace SatTyp

variable {L : FirstOrder.Language.{0, 0}} {C : Type}

/-- The conjunction of the (finitely many) formulas of a finite subset of a type. -/
def conj (p : SatTyp L C) (F : Finset ((L[[C]]).Formula (p.1 ⊕ Fin 1))) :
    (L[[C]]).Formula (p.1 ⊕ Fin 1) :=
  F.toList.foldr (fun φ acc => φ ⊓ acc) ⊤

/-- The formula `∃y ⋀ F` (with the parameters `p.1` still free). -/
def ex (p : SatTyp L C) (F : Finset ((L[[C]]).Formula (p.1 ⊕ Fin 1))) :
    (L[[C]]).Formula p.1 :=
  (BoundedFormula.relabel (n := 1) (k := 0) (β := p.1) id (conj p F)).ex

/-- The sentence `∃y ⋀ F` obtained by replacing the parameters by the corresponding constants. -/
def sent (p : SatTyp L C) (F : Finset ((L[[C]]).Formula (p.1 ⊕ Fin 1))) :
    (L[[C]]).Sentence :=
  (ex p F).subst (fun a => FirstOrder.Language.Constants.term (FirstOrder.Language.con L (a : C)))

end SatTyp

variable {L : FirstOrder.Language.{0, 0}} {C : Type}

/-- A type `p` is *consistent* with a theory `T` when every finite fragment of `p` is satisfiable,
in the sense that the sentence `∃y ⋀ F` (with the parameters replaced by constants) belongs to `T`.
For the complete theories used in the construction this is equivalent to finite satisfiability. -/
def SatCons (T : (L[[C]]).Theory) (p : SatTyp L C) : Prop :=
  ∀ F : Finset ((L[[C]]).Formula (p.1 ⊕ Fin 1)), (∀ φ ∈ F, φ ∈ p.2) → p.sent F ∈ T

/-- The language homomorphism `L[[C]] →ᴸ L[[C']]` induced by a map on the constants. -/
def SatLangMap {L : FirstOrder.Language.{0, 0}} {C C' : Type} (f : C → C') :
    L[[C]] →ᴸ L[[C']] :=
  LHom.sumMap (LHom.id L) (LHom.constantsOnMap f)

/-- The witness sentence attached to a formula `φ` of a type `p`: the sentence of the language with
one extra constant `c_p` saying that `c_p` satisfies `φ` (with the parameters of `p` replaced by the
corresponding constants). -/
def SatWitSent {L : FirstOrder.Language.{0, 0}} {C : Type} (T : (L[[C]]).Theory)
    (p : SatTyp L C) (hp : SatCons T p) (φ : (L[[C]]).Formula (p.1 ⊕ Fin 1)) :
    (L[[C ⊕ {q : SatTyp L C // SatCons T q}]]).Sentence :=
  ((SatLangMap (Sum.inl : C → C ⊕ {q : SatTyp L C // SatCons T q})).onFormula φ).subst
    (fun x : p.1 ⊕ Fin 1 =>
      match x with
      | Sum.inl a =>
        FirstOrder.Language.Constants.term
          (FirstOrder.Language.con L (Sum.inl a : C ⊕ {q : SatTyp L C // SatCons T q}))
      | Sum.inr _ =>
        FirstOrder.Language.Constants.term
          (FirstOrder.Language.con L (Sum.inr ⟨p, hp⟩ : C ⊕ {q : SatTyp L C // SatCons T q})))

/-- The set of witness sentences added at a successor stage: for each type `p` over the constants
`C` that is consistent with the theory `T`, and each formula `φ ∈ p`, the sentence saying that the
new constant `c_p` satisfies `φ`. -/
def SatWit {L : FirstOrder.Language.{0, 0}} {C : Type} (T : (L[[C]]).Theory) :
    (L[[C ⊕ {p : SatTyp L C // SatCons T p}]]).Theory :=
  {σ | ∃ (p : SatTyp L C) (hp : SatCons T p) (φ : (L[[C]]).Formula (p.1 ⊕ Fin 1)),
        φ ∈ p.2 ∧ σ = SatWitSent T p hp φ}

/-- The theory of the successor stage: the previous theory, transported to the expanded language,
together with the witness sentences. -/
def SatStepTheory {L : FirstOrder.Language.{0, 0}} {C : Type} (T : (L[[C]]).Theory) :
    (L[[C ⊕ {p : SatTyp L C // SatCons T p}]]).Theory :=
  (SatLangMap (Sum.inl : C → C ⊕ {p : SatTyp L C // SatCons T p})).onTheory T ∪ SatWit T

/-! ## Temporary probes (to be removed) -/

namespace Work.WilC5

section Probes

example (κ : Cardinal.{0}) : LinearOrder (SatIdx κ) := inferInstance
example (κ : Cardinal.{0}) : WellFoundedLT (SatIdx κ) := inferInstance
example (κ : Cardinal.{0}) : SuccOrder (SatIdx κ) := inferInstance
example (κ : Cardinal.{0}) (x : SatIdx κ) : x ≤ Order.succ x := Order.le_succ x
example (κ : Cardinal.{0}) : Cardinal.mk (SatIdx κ) = Order.succ (Order.succ (κ + Cardinal.aleph0)) :=
  Cardinal.mk_ord_toType _
example {C : Type} {L : FirstOrder.Language.{0,0}} (p : SatTyp L C) :
    (L[[C]]).Sentence := p.sent ∅
example {C : Type} {L : FirstOrder.Language.{0,0}} (p : SatTyp L C) : (L[[C]]).Formula p.1 :=
  p.ex ∅

end Probes

end Work.WilC5
