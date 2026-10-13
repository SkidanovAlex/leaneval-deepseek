/-
  WilC5 — saturated models.

  The vdDMM §4 route to model completeness of `Th(ℝ, exp)` runs through *saturated* models: their
  Theorem 4.1 extends an embedding `F₀ → L` from a log-closed submodel `F₀` of `K` to all of `K`,
  where `L` is `|K|⁺`-saturated; the extension lemmas 4.2–4.4 are the steps of that transfinite
  construction.  Mathlib has no notion of saturation, so this module supplies the definition and
  (in the companion module `Work.WilC5.ExistsSaturated`) the existence theorem: every structure
  has a `κ`-saturated elementary extension, for every cardinal `κ`.

  Saturation is stated for **1-types over subsets** (all that is needed); `n`-types follow by
  iterating the argument.  A type over a parameter set `A` is a set `p` of formulas of the
  expanded language `L[[A]]` with one free variable whose parameters are the elements of `A`
  (represented as free variables indexed by the subtype `A`), and `p` is realized at `x : M` when
  every member of `p` holds at `x` with the parameters interpreted by inclusion.
-/
import Mathlib.ModelTheory.ElementaryMaps
import Mathlib.SetTheory.Cardinal.Basic

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilC5

open FirstOrder Language

/-- **`κ`-saturation** (for 1-types).  A structure `M` is `κ`-saturated when every set of formulas
with one free variable and parameters from a subset `A ⊆ M` of cardinality `< κ`, which is
finitely satisfiable in `M`, is realized in `M`. -/
def IsSaturated {L : Language} {M : Type} [L.Structure M] (κ : Cardinal.{0}) : Prop :=
  ∀ (A : Set M), Cardinal.mk A < κ →
    ∀ (p : Set (L.Formula (A ⊕ Fin 1))),
      (∀ F : Finset (L.Formula (A ⊕ Fin 1)), (∀ φ ∈ F, φ ∈ p) →
        ∃ x : Fin 1 → M, ∀ φ ∈ F,
          @BoundedFormula.Realize L M _ (A ⊕ Fin 1) 0 φ (Sum.elim Subtype.val x)
            (fun i : Fin 0 => i.elim0)) →
      ∃ x : Fin 1 → M, ∀ φ ∈ p,
        @BoundedFormula.Realize L M _ (A ⊕ Fin 1) 0 φ (Sum.elim Subtype.val x)
          (fun i : Fin 0 => i.elim0)

/-- `κ`-saturation is monotone in `κ`: being `κ`-saturated is a *stronger* condition than being
`κ'`-saturated when `κ' ≤ κ`. -/
theorem IsSaturated.mono {L : Language} {M : Type} [L.Structure M] {κ κ' : Cardinal.{0}}
    (h : IsSaturated (L := L) (M := M) κ) (hκ : κ' ≤ κ) :
    IsSaturated (L := L) (M := M) κ' := fun A hA p hp =>
  h A (lt_of_lt_of_le hA hκ) p hp

end Work.WilC5
