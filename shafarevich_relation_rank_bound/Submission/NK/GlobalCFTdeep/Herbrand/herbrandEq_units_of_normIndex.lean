/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Submission.NK.GlobalCFTdeep.Basic

/-!
# The Herbrand quotient of the units, from the index of the norm group

For a finite Galois extension `E/F` of fields with group `G = Gal(E/F)`, this file computes the
Herbrand quotient of the units `Eˣ` (with its natural `G`-action, i.e. the `ℤ[G]`-module
`Rep.ofMulDistribMulAction (E ≃ₐ[F] E) Eˣ`):

  `|Ĥ⁰(G, Eˣ)| = [E : F] · |Ĥ¹(G, Eˣ)|`

— in the cross-multiplied `Nat.card` form used in `NK.GlobalCFTdeep`, `HerbrandEq M [E : F]`.

Two classical facts enter:

* **Hilbert 90** (Noether's generalisation): `Ĥ¹(G, Eˣ) = 0`, i.e. `|Ĥ¹(G, Eˣ)| = 1`.  This holds
  for *every* finite Galois extension and is proved here from Mathlib's
  `groupCohomology.H1ofAutOnUnitsUnique` together with the identification of positive Tate
  cohomology with group cohomology `TateCohomology.isoGroupCohomology`.
* **The `Ĥ⁰`-computation**: `Ĥ⁰(G, Eˣ) ≅ Fˣ ⧸ N_{E/F}(Eˣ)`, the quotient of the units of the base
  field by the norm group (the commons theorem
  `Commons.RepresentationTheory.TateCohomology.natCard_tateCohomology_zero_units`).  Hence
  `|Ĥ⁰(G, Eˣ)| = [Fˣ : N(Eˣ)]`, the *index* of the norm group — the hypothesis `hindex` of the main
  theorem.

Note that the hypothesis `[Fˣ : N(Eˣ)] = [E : F]` is *not* automatic: it holds for local fields
(Herbrand's theorem) and for the idèle class group of a number field, which is exactly where the
statement is applied, but fails for instance for `ℚ(i)/ℚ` (where the norm group has infinite
index).  The theorem below is therefore the honest conditional statement, and its proof genuinely
uses `hindex`.
-/

set_option autoImplicit false

open CategoryTheory

namespace NK.GlobalCFTdeep.Herbrand

/-- **Hilbert 90 for the units, in the `ℤ`-representation used in this chapter.**  For a finite
Galois extension `E/F`, the first *Tate* cohomology of the units vanishes.

Mathlib's `groupCohomology.H1ofAutOnUnitsUnique` gives the vanishing of the *group* cohomology
`H¹(Gal(E/F), Eˣ)` (for a finite, not necessarily Galois, extension); positive Tate cohomology
agrees with group cohomology by `TateCohomology.isoGroupCohomology`. -/
theorem natCard_tateCohomology_one_units {F E : Type} [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [IsGalois F E] :
    Nat.card (tateCohomology (Rep.ofMulDistribMulAction (E ≃ₐ[F] E) Eˣ) 1) = 1 := by
  -- Hilbert 90: `H¹(Gal(E/F), Eˣ) = 0`
  have hsubG : Subsingleton (groupCohomology (Rep.ofMulDistribMulAction (E ≃ₐ[F] E) Eˣ) 1) :=
    (inferInstance : Subsingleton (groupCohomology.H1 (Rep.ofAlgebraAutOnUnits F E)))
  have hOne1 : Nat.card (groupCohomology (Rep.ofMulDistribMulAction (E ≃ₐ[F] E) Eˣ) 1) = 1 :=
    Nat.card_eq_one_iff_unique.mpr ⟨hsubG, ⟨0⟩⟩
  -- `Ĥ¹` and `H¹` agree in positive degrees
  exact (Nat.card_congr ((TateCohomology.isoGroupCohomology (R := ℤ) (G := E ≃ₐ[F] E) 1).app
    (Rep.ofMulDistribMulAction (E ≃ₐ[F] E) Eˣ)).toLinearEquiv.toEquiv).trans hOne1

/-- **The `Ĥ⁰`-computation in the form of an index.**  For a finite Galois extension `E/F` the
zeroth Tate cohomology of the units has the cardinality of the quotient of `Fˣ` by the norm group
`N_{E/F}(Eˣ)`, which is by definition the index of `N_{E/F}(Eˣ)` in `Fˣ`. -/
theorem hZero_units_eq_index {F E : Type} [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [IsGalois F E] :
    hZero (Rep.ofMulDistribMulAction (E ≃ₐ[F] E) Eˣ) =
      (MonoidHom.range (Units.map (Algebra.norm F : E →* F))).index := by
  rw [hZero_def]
  rw [show (Rep.ofMulDistribMulAction (E ≃ₐ[F] E) Eˣ) = Rep.ofAlgebraAutOnUnits F E from rfl]
  rw [Commons.RepresentationTheory.TateCohomology.natCard_tateCohomology_zero_units F E]
  rfl

/-- **The Herbrand quotient of the units is the degree**, whenever the norm group has index
`[E : F]`:

  `|Ĥ⁰(Gal(E/F), Eˣ)| = [E : F] · |Ĥ¹(Gal(E/F), Eˣ)|`.

Indeed `|Ĥ⁰| = [Fˣ : N(Eˣ)] = [E : F]` is the hypothesis, while `|Ĥ¹| = 1` by Hilbert 90. -/
theorem herbrandEq_units_of_normIndex {F E : Type} [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [IsGalois F E]
    (hindex : (MonoidHom.range (Units.map (Algebra.norm F : E →* F))).index = Module.finrank F E) :
    HerbrandEq (Rep.ofMulDistribMulAction (E ≃ₐ[F] E) Eˣ) (Module.finrank F E) := by
  have hOne : hOne (Rep.ofMulDistribMulAction (E ≃ₐ[F] E) Eˣ) = 1 := by
    show Nat.card (tateCohomology (Rep.ofMulDistribMulAction (E ≃ₐ[F] E) Eˣ) 1) = 1
    exact natCard_tateCohomology_one_units
  rw [HerbrandEq, hZero_units_eq_index, hOne, mul_one, hindex]

end NK.GlobalCFTdeep.Herbrand
