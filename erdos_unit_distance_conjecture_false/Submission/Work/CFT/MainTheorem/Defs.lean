/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Global class field theory in the idèle-class-group formulation: vocabulary

This is the vocabulary layer for `Submission/Work/CFT/MainTheorem`, the formalisation of the main
theorems of global class field theory in the idèle-class-group formulation.  The "Main Theorem" of
class field theory is the existence of the reciprocity isomorphism
`C_F / N_{K/F} C_K ≅ Gal(K/F)^{ab}` together with the fundamental class in `H²(Gal(K/F), C_K)`.

## Main definitions

* `Work.CFT.MainTheorem.CK K` — the **idèle class group** `C_K = I_K / Kˣ` of the number field
  `K`, i.e. Mathlib's `NumberField.IdeleClassGroup (𝓞 K) K`.
* `Work.CFT.MainTheorem.repOfMulAut` — the `ℤ`-linear representation attached to a multiplicative
  action `ρ : G →* MulAut M`.  Mathlib does not construct the action of `Gal(K/F)` on `C_K` (the
  subject of the parallel area `Submission/Work/CFT/IdeleClassGroup`), so in this area the module
  structure is taken as an explicit parameter `A : Rep ℤ (Gal(K/F))` standing for "`C_K` together
  with its Galois action"; this definition is how such an action is turned into a `Rep`.
* `Work.CFT.MainTheorem.unitsRep` — the unit group `𝒪_K^×`, as a `Gal(K/F)`-module
  (Mathlib's `Rep.ofAlgebraAutOnUnits`).
* `Work.CFT.MainTheorem.H0`/`Hm1` — the Tate cohomology groups `Ĥ⁰` and `Ĥ⁻¹`.
* `Work.CFT.MainTheorem.herbrandQuotient` — `h(G, A) = |Ĥ⁰(G, A)| / |Ĥ⁻¹(G, A)|`.

## Conventions

All groups acting are finite (so that Tate cohomology is available) and live in `Type` (universe
`0`), matching `Submission/Work/Tower/Shafarevich`, whose `H1Fp`/`H2Fp` are also universe-`0`.
-/

open NumberField CategoryTheory
open scoped Classical

namespace Work.CFT.MainTheorem

noncomputable section

/-- The **idèle class group** `C_K = I_K / Kˣ` of the number field `K`. -/
abbrev CK (K : Type) [Field K] [NumberField K] : Type :=
  NumberField.IdeleClassGroup (𝓞 K) K

/-- The unit group `𝒪_K^×` of the number field `K`, as a module over `Gal(K/F)` for a Galois
extension `K/F`: the natural action of `σ ∈ Gal(K/F)` on units, Mathlib's
`Rep.ofAlgebraAutOnUnits`. -/
abbrev unitsRep (F K : Type) [Field F] [Field K] [Algebra F K] : Rep ℤ (Gal(K/F)) :=
  Rep.ofAlgebraAutOnUnits F K

section Rep

variable {G M : Type} [Group G] [CommGroup M]

/-- The `ℤ`-linear representation of `G` on `Additive M` associated to a multiplicative action
`ρ : G →* MulAut M`.  This is how a Galois action on the idèle class group `C_K` is turned into a
`Rep ℤ (Gal(K/F))`, so that Mathlib's group cohomology and Tate cohomology apply. -/
def repOfMulAut (ρ : G →* MulAut M) : Rep ℤ G :=
  letI := MulDistribMulAction.compHom M ρ
  Rep.ofMulDistribMulAction G M

end Rep

section Cohomology

variable {G : Type} [Group G] [Fintype G]

/-- `Ĥ⁰(G, A)`, the zeroth Tate cohomology of the `G`-module `A`. -/
abbrev H0 (A : Rep ℤ G) : Type := tateCohomology A 0

/-- `Ĥ⁻¹(G, A)`, the `(-1)`st Tate cohomology of the `G`-module `A`. -/
abbrev Hm1 (A : Rep ℤ G) : Type := tateCohomology A (-1)

/-- The **Herbrand quotient** `h(G, A) = |Ĥ⁰(G, A)| / |Ĥ⁻¹(G, A)|` of a `ℤ`-linear representation
`A` of a finite group `G`.  (`Nat.card` of an infinite type is `0`; the intended use is with `A`
finitely generated over `ℤ`, where both Tate cohomology groups are finite, so that `Nat.card` is
the honest order.) -/
def herbrandQuotient (A : Rep ℤ G) : ℚ :=
  (Nat.card (H0 A) : ℚ) / (Nat.card (Hm1 A) : ℚ)

@[simp] lemma herbrandQuotient_def (A : Rep ℤ G) :
    herbrandQuotient A = (Nat.card (H0 A) : ℚ) / (Nat.card (Hm1 A) : ℚ) := rfl

end Cohomology

end

end Work.CFT.MainTheorem
