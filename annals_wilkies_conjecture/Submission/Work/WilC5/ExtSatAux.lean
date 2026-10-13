/-
  WilC5 — the vocabulary for the proof that an elementary embedding of a substructure of a
  structure `M` into a `κ`-saturated structure `N` (`κ > |M|`) extends to all of `M`.

  The construction is the classical one: build a *partial elementary map*

    `B ⊆ N`,  `τ : B → M`   such that  `N ⊨ φ(b̄) ⟺ M ⊨ φ(τ b̄)`

  for every formula with free variables indexed by `B` (i.e. every sentence of `L[[B]]`), starting
  from the inverse of the given elementary embedding `σ` and enlarging it one point at a time by
  realizing the type of the missing element; a Zorn argument produces a *maximal* such partial map,
  whose domain then has to exhaust `M`.

  This file only fixes the definition `ElemOn` and its first consequences; the steps of the
  construction live in the companion files.
-/
import Mathlib
import Submission.Work.WilC5.Saturation

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilC5

open FirstOrder Language

/-- **Partial elementary map.**  `ElemOn B τ` says that the map `τ : B → M`, defined on a subset
`B ⊆ N`, is *elementary*: for every formula `φ` with free variables indexed by `B` (equivalently
every sentence of the expanded language `L[[B]]`), the truth value of `φ` when the parameters are
interpreted by the inclusion `B ↪ N` equals its truth value when they are interpreted by `τ`. -/
def ElemOn {L : FirstOrder.Language.{0, 0}} {M N : Type} [L.Structure M] [L.Structure N]
    (B : Set N) (τ : B → M) : Prop :=
  ∀ φ : L.Formula B, φ.Realize (Subtype.val : B → N) ↔ φ.Realize τ

/-- An elementary map is injective: elementarity applied to the formula `x = y`. -/
theorem elemOn_injective {L : FirstOrder.Language.{0, 0}} {M N : Type} [L.Structure M]
    [L.Structure N] {B : Set N} {τ : B → M} (h : @ElemOn L M N _ _ B τ) : Function.Injective τ := by
  intro x y hxy
  have hφ := h (Term.equal (Term.var x) (Term.var y) : L.Formula B)
  rw [Formula.realize_equal, Formula.realize_equal, Term.realize_var, Term.realize_var] at hφ
  exact Subtype.ext (hφ.mpr hxy)

/-- The domain of a partial elementary map into `M` has cardinality at most `|M|`. -/
theorem mk_le_of_elemOn {L : FirstOrder.Language.{0, 0}} {M N : Type} [L.Structure M]
    [L.Structure N] {B : Set N} {τ : B → M} (h : @ElemOn L M N _ _ B τ) :
    Cardinal.mk B ≤ Cardinal.mk M :=
  Cardinal.mk_le_of_injective (elemOn_injective h)


/-- A **partial map** from a subset of `N` to `M`: the pair of its domain and its values. -/
abbrev PEM (L : FirstOrder.Language.{0, 0}) (M N : Type) [L.Structure M] [L.Structure N] : Type :=
  Σ B : Set N, B → M

namespace PEM

variable {L : FirstOrder.Language.{0, 0}} {M N : Type} [L.Structure M] [L.Structure N]

/-- `p ≤ q` when `q` extends `p`: the domain of `q` contains that of `p`, and the two maps agree
on the domain of `p`. -/
def le (p q : PEM L M N) : Prop :=
  ∃ h : p.1 ⊆ q.1, ∀ x : p.1, q.2 ⟨x.1, h x.2⟩ = p.2 x

instance : LE (PEM L M N) := ⟨le⟩

instance : Preorder (PEM L M N) where
  le := le
  lt p q := le p q ∧ ¬ le q p
  le_refl p := ⟨fun _ hx => hx, fun x => by simp⟩
  le_trans p q r hpq hqr := by
    obtain ⟨h1, h1'⟩ := hpq
    obtain ⟨h2, h2'⟩ := hqr
    exact ⟨h1.trans h2, fun x => by rw [h2' ⟨x.1, h1 x.2⟩, h1' x]⟩
  lt_iff_le_not_ge := fun a b => Iff.rfl

/-- A partial map is **valid** when its values form an elementary map on its domain. -/
def Valid (p : PEM L M N) : Prop := @ElemOn L M N _ _ p.1 p.2

/-- The map obtained from `τ` by adjoining the pair `n ↦ m` to its domain. -/
noncomputable def extendFun {B : Set N} (τ : B → M) (n : N) (m : M) :
    ↥(insert n B) → M :=
  fun a => if h : (a : N) ∈ B then τ ⟨a, h⟩ else m

@[simp]
theorem extendFun_apply_of_mem {B : Set N} (τ : B → M) {n : N} {m : M} (a : ↥(insert n B))
    (h : (a : N) ∈ B) : extendFun τ n m a = τ ⟨a, h⟩ := dite_eq_left h

@[simp]
theorem extendFun_apply_of_not_mem {B : Set N} (τ : B → M) {n : N} {m : M} (a : ↥(insert n B))
    (h : (a : N) ∉ B) : extendFun τ n m a = m := dite_eq_right h

end PEM

end Work.WilC5
