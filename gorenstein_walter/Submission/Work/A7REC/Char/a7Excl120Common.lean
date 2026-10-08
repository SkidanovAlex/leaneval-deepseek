/-
Area `A7REC`, file `Char/a7Excl120Common.lean`: the hypothesis bundle shared by the four
case lemmas of the exclusion of `|H| = 120` (leaf `A7Excl120Prop`).

`Excl120Setup U S τ` is the local situation inside a finite group `C` of order `120`:

* `U ≤ C` has order `3`, `S ≤ C` has order `8`;
* `τ ∈ S` is an involution central in `S`, normalizing `U` (`U.map (conj τ) = U`) but *not*
  centralizing it (this is what `S ⊓ C_C(U) = ⊥` adds, since `τ ≠ 1`);
* `S ⊓ C_C(U) = ⊥`;
* every involution centralizer in `C` has order dividing `24` and contains at most one
  subgroup of order `3` (these are the consequences of `InvCent G` used by the argument).

Under `Excl120Setup`, `U` is a Sylow `3`-subgroup of `C` and the index of `N_C(U)` (= the
number of Sylow `3`-subgroups of `C`) is `1`, `4`, `10` or `40`; each of the four cases is
impossible.  The four case lemmas are proved separately in the sibling files
`a7Excl120IdxOne`, `a7Excl120IdxThree`… see `a7Excl120.lean`.
-/
import Mathlib

namespace Work.A7REC.Char

/-- The local `|H| = 120` situation: see the module docstring. -/
structure Excl120Setup {C : Type*} [Group C] (U S : Subgroup C) (τ : C) : Prop where
  card_eq : Nat.card C = 120
  card_U : Nat.card U = 3
  card_S : Nat.card S = 8
  tau_mem : τ ∈ S
  tau_order : orderOf τ = 2
  tau_central : ∀ x ∈ S, x * τ = τ * x
  tau_normalizes : U.map (MulAut.conj τ).toMonoidHom = U
  disj : S ⊓ Subgroup.centralizer (U : Set C) = ⊥
  cent_dvd : ∀ x : C, orderOf x = 2 → Nat.card (Subgroup.centralizer ({x} : Set C)) ∣ 24
  uniq_C3 : ∀ x : C, orderOf x = 2 → ∀ A B : Subgroup C,
    A ≤ Subgroup.centralizer ({x} : Set C) → B ≤ Subgroup.centralizer ({x} : Set C) →
    Nat.card A = 3 → Nat.card B = 3 → A = B

end Work.A7REC.Char
