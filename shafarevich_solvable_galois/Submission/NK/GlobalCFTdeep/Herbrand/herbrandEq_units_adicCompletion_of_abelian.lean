/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Submission.NK.GlobalCFTdeep.Herbrand.herbrandEq_units_of_normIndex
import Submission.NK.LocalReciprocity.index_normGroup_eq_finrank
import Submission.Commons.RepresentationTheory.TateCohomology.natCard_tateCohomology_zero_units
import Submission.Commons.RepresentationTheory.TateCohomology.tateCohomology_zero_iso
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The local Herbrand quotient of the units (abelian case)

Let `L / K` be a finite Galois extension of number fields, `q` a finite place of `L` above a finite
place `Q` of `K`, and `L_q = q.adicCompletion L`, `K_Q = Q.adicCompletion K` the corresponding
local fields.  This file proves the **local Herbrand index theorem** for the units of the local
field `L_q`:

  `|Ĥ⁰(Gal(L_q/K_Q), L_qˣ)| = [L_q : K_Q] · |Ĥ¹(Gal(L_q/K_Q), L_qˣ)|`,

i.e. `HerbrandEq (Rep.ofMulDistribMulAction Gal(L_q/K_Q) L_qˣ) [L_q : K_Q]` in the notation of
`NK.GlobalCFTdeep`.  This is the local input of the global Herbrand quotient computation.

Two classical facts are used, both available elsewhere:

* **Hilbert 90**: `|Ĥ¹(Gal(L_q/K_Q), L_qˣ)| = 1` (Mathlib's `H1ofAutOnUnitsUnique` together with
  `TateCohomology.isoGroupCohomology`);
* the `Ĥ⁰`-computation `|Ĥ⁰| = [K_Qˣ : N L_qˣ]` (the commons theorem
  `Commons.RepresentationTheory.TateCohomology.natCard_tateCohomology_zero_units`), combined with the
  **abelian local norm index theorem** `[K_Qˣ : N L_qˣ] = [L_q : K_Q]`
  (`NK.LocalReciprocity.index_normGroup_eq_finrank`).

## Why the statement carries a `Fintype` hypothesis

The statement is given with an *arbitrary* `Fintype Gal(L_q/K_Q)` instance rather than the canonical
one (`AlgEquiv.fintype`).  Since the `Fintype` instance is an argument of `tateCohomology`, the
resulting `HerbrandEq` proposition is *not* syntactically the one produced by the library lemmas
about Tate cohomology, and the two cannot be identified definitionally (unfolding the Tate complex
is out of the question).  We therefore prove the statement for an arbitrary instance `A`.  The extra
lemma `natCard_tateCohomology_zero_eq_of_fintype_eq` is the point where this is harmless: the zeroth
Tate cohomology group depends on the `Fintype` instance only through the norm map, and the norm map
`∑ g, ρ g` does not depend on the chosen `Finset.univ` (all `univ`s of a given type coincide by
`Finset.ext`).  This lets us transfer the `Ĥ⁰`-computation to the instance at hand.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

open CategoryTheory

namespace NK.GlobalCFTdeep.Herbrand

/-! ### Two `Fintype` instances give the same norm map -/

/-- All `Finset.univ` of a type coincide, whatever the `Fintype` instance. -/
theorem finset_univ_eq_of_fintype_eq {G : Type} (A B : Fintype G) :
    @Finset.univ G A = @Finset.univ G B :=
  Finset.ext fun a => by simp

/-- **The norm map of a representation does not depend on the `Fintype` instance.**  The norm
`∑ g, ρ g` is a sum over `Finset.univ`, and all these finite sets coincide. -/
theorem representation_norm_eq_of_fintype_eq {G : Type} [Group G] {V : Type} [AddCommGroup V]
    [Module ℤ V] (A B : Fintype G) (ρ : Representation ℤ G V) :
    @Representation.norm ℤ G V _ _ A _ _ ρ = @Representation.norm ℤ G V _ _ B _ _ ρ := by
  show (@Finset.univ G A).sum (fun g => ρ g) = (@Finset.univ G B).sum (fun g => ρ g)
  rw [finset_univ_eq_of_fintype_eq A B]

/-- **The zeroth Tate cohomology does not depend on the `Fintype` instance.**  Indeed, by
`Commons.RepresentationTheory.TateCohomology.tateCohomology_zero_iso` it is the quotient of the
invariants by the image of the norm, and the norm map is instance independent
(`representation_norm_eq_of_fintype_eq`). -/
theorem natCard_tateCohomology_zero_eq_of_fintype_eq {G : Type} [Group G] {V : Type}
    [AddCommGroup V] [Module ℤ V] (A B : Fintype G) (ρ : Representation ℤ G V) :
    Nat.card (@tateCohomology ℤ G _ _ A (Rep.of ρ) 0) =
      Nat.card (@tateCohomology ℤ G _ _ B (Rep.of ρ) 0) := by
  obtain ⟨eA⟩ := @Commons.RepresentationTheory.TateCohomology.tateCohomology_zero_iso G V _ A _ _ ρ
  obtain ⟨eB⟩ := @Commons.RepresentationTheory.TateCohomology.tateCohomology_zero_iso G V _ B _ _ ρ
  rw [Nat.card_congr eA.toEquiv, Nat.card_congr eB.toEquiv]
  rw [show @Representation.norm ℤ G V _ _ A _ _ ρ = @Representation.norm ℤ G V _ _ B _ _ ρ from
    representation_norm_eq_of_fintype_eq A B ρ]

/-! ### Hilbert 90, for an arbitrary `Fintype` instance -/

/-- **Hilbert 90** in the form used in this chapter: the first Tate cohomology of the units
vanishes, for an arbitrary `Fintype` instance on the Galois group.  Positive Tate cohomology agrees
with group cohomology (`TateCohomology.isoGroupCohomology`), where the statement is Mathlib's
`groupCohomology.H1ofAutOnUnitsUnique`. -/
theorem natCard_tateCohomology_one_of_fintype {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] (A : Fintype (L ≃ₐ[K] L)) :
    Nat.card (@tateCohomology ℤ (L ≃ₐ[K] L) _ _ A (Rep.ofAlgebraAutOnUnits K L) 1) = 1 := by
  have hsubG : Subsingleton (groupCohomology (Rep.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ) 1) :=
    (inferInstance : Subsingleton (groupCohomology.H1 (Rep.ofAlgebraAutOnUnits K L)))
  have hOne1 : Nat.card (groupCohomology (Rep.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ) 1) = 1 :=
    Nat.card_eq_one_iff_unique.mpr ⟨hsubG, ⟨0⟩⟩
  exact (Nat.card_congr ((TateCohomology.isoGroupCohomology (R := ℤ) (G := L ≃ₐ[K] L) 1).app
    (Rep.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ)).toLinearEquiv.toEquiv).trans hOne1

/-! ### The main statement, for an arbitrary `Fintype` instance -/

/-- **Local Herbrand theorem for the units (abelian case)**, in the form in which the `Fintype`
instance on the local Galois group is an explicit argument (see the discussion in the header of this
file).  The proof combines Hilbert 90 (`natCard_tateCohomology_one_of_fintype`) with the
`Ĥ⁰`-computation of the units and the abelian local norm index theorem. -/
theorem herbrandEq_units_adicCompletion_of_fintype {K L : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    [hq : q.asIdeal.LiesOver Q.asIdeal]
    (A : Fintype (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L))
    (hcomm : ∀ a b : q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L, a * b = b * a) :
    @NK.GlobalCFTdeep.HerbrandEq (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) _
      A
      (Rep.ofMulDistribMulAction (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L)
        (q.adicCompletion L)ˣ)
      (Module.finrank (Q.adicCompletion K) (q.adicCompletion L)) := by
  -- the local extension `L_q / K_Q` is finite and Galois
  haveI hfin : FiniteDimensional (Q.adicCompletion K) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion Q q hq
  haveI hgal : IsGalois (Q.adicCompletion K) (q.adicCompletion L) :=
    Submission.NeukirchUchida.Local.isGalois_adicCompletion Q q hq
  rw [NK.GlobalCFTdeep.HerbrandEq, NK.GlobalCFTdeep.hZero_def, NK.GlobalCFTdeep.hOne_def]
  -- Hilbert 90: `|Ĥ¹| = 1`
  have h1 : Nat.card (@tateCohomology ℤ (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L)
        _ _ A (Rep.ofMulDistribMulAction
          (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) (q.adicCompletion L)ˣ)
        1) = 1 := by
    change Nat.card (@tateCohomology ℤ (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L)
        _ _ A (Rep.ofAlgebraAutOnUnits (Q.adicCompletion K) (q.adicCompletion L)) 1) = 1
    exact natCard_tateCohomology_one_of_fintype A
  -- `|Ĥ⁰| = [K_Qˣ : N L_qˣ] = [L_q : K_Q]`
  have h0 : Nat.card (@tateCohomology ℤ (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L)
        _ _ A (Rep.ofMulDistribMulAction
          (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) (q.adicCompletion L)ˣ)
        0) =
      Module.finrank (Q.adicCompletion K) (q.adicCompletion L) := by
    change Nat.card (@tateCohomology ℤ (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L)
        _ _ A (Rep.ofAlgebraAutOnUnits (Q.adicCompletion K) (q.adicCompletion L)) 0) = _
    -- the `Ĥ⁰`-computation for the (canonical) `Fintype` instance of the library theorems; the
    -- instance is extracted existentially so that it can be named
    obtain ⟨B, hB⟩ : ∃ B : Fintype (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L),
        Nat.card (@tateCohomology ℤ
            (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) _ _
          B (Rep.ofAlgebraAutOnUnits (Q.adicCompletion K) (q.adicCompletion L)) 0) =
        (MonoidHom.range (Units.map
          (Algebra.norm (Q.adicCompletion K) : (q.adicCompletion L) →* (Q.adicCompletion K)))).index :=
      ⟨_, by
        rw [Commons.RepresentationTheory.TateCohomology.natCard_tateCohomology_zero_units
          (Q.adicCompletion K) (q.adicCompletion L), Subgroup.index_eq_card]⟩
    have hAB := natCard_tateCohomology_zero_eq_of_fintype_eq A B
      (Representation.ofMulDistribMulAction
        (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) (q.adicCompletion L)ˣ)
    rw [show Rep.of (Representation.ofMulDistribMulAction
          (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) (q.adicCompletion L)ˣ) =
        Rep.ofAlgebraAutOnUnits (Q.adicCompletion K) (q.adicCompletion L) from rfl] at hAB
    rw [hAB, hB]
    exact NK.LocalReciprocity.index_normGroup_eq_finrank Q q hcomm
  rw [h0, h1, mul_one]

/-- **Local Herbrand theorem for the units (abelian case).**  If the local Galois group of
`L_q / K_Q` is abelian, the Herbrand quotient of the local units is the local degree — the local
input of the global computation of the Herbrand quotient of the idèle class group. -/
theorem herbrandEq_units_adicCompletion_of_abelian {K L : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    [q.asIdeal.LiesOver Q.asIdeal]
    [Fintype (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L)]
    (hcomm : ∀ a b : q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L,
      a * b = b * a) :
    NK.GlobalCFTdeep.HerbrandEq (Rep.ofMulDistribMulAction
      (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) (q.adicCompletion L)ˣ)
      (Module.finrank (Q.adicCompletion K) (q.adicCompletion L)) :=
  herbrandEq_units_adicCompletion_of_fintype Q q _ hcomm

end NK.GlobalCFTdeep.Herbrand
