/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The coefficient-field reduction: from any char-0 field to a *real* one

`Work.ORFinal.theorem_1_1_of_hughesFree` needs the ring coherence of `K[G]` for an arbitrary field
`K` of characteristic zero, but the JL §5 machinery of this area (T2, T4, T5-real, T6, T7) is only
available for coefficient embeddings `φK : K →+* ℂ` that are **real-valued**: for a general `φK`
the involution of `U(G)` is only `ℂ`-conjugate-linear, so it does not give the `K`-linear antipode
that the mirror of JL Lemma 5.1′/Lemma 5.2 needs (obstruction §6(b) of `README.md`).

This file performs the reduction.  Three ingredients:

* `Work.ORFinal.FiniteFree.ringCoherent_of_finite_free` — coherence ascends along a finite free
  extension of rings (Chase's lemma argument);
* `Work.ORFinal.FiniteFree.module_finite_free_monoidAlgebra` — `K[X]` is a finite free
  `K₀[X]`-module when `K` is a finite extension of `K₀`;
* `Work.ORFinal.RealSubfield.exists_real_subfield_of_essFiniteType` — every field `F` of
  characteristic zero that is essentially of finite type over `ℚ` has a subfield `L` with `F/L`
  finite and an embedding `L →+* ℝ`.

The main results are

* `Work.ORFinal.ringCoherent_monoidAlgebra_of_finite` — coherence for a finite coefficient
  extension;
* `Work.ORFinal.ringCoherent_of_typeZero` — for `K₀ : Type 0`, coherence of `K₀[X]` follows from
  coherence at every *real-embeddable* coefficient field;
* `Work.ORFinal.ringCoherent_of_charZero` — the same for an arbitrary char-0 field `K`, with the
  group pushed into `K`'s universe by `ULift`, by composing with
  `Work.ORDivLoc.P2.ringCoherent_ulift_of_typeZero`.
-/
import Mathlib
import Submission.Work.ORFinal.FiniteFree.ringCoherent_of_finite_free
import Submission.Work.ORFinal.FiniteFree.module_finite_free_monoidAlgebra
import Submission.Work.ORFinal.RealSubfield.exists_real_subfield_of_essFiniteType
import Submission.Work.ORDivLoc.P2.ringCoherent_ulift_of_typeZero

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

universe u v

open Work.ORFinal.FiniteFree

namespace Work.ORFinal

/-- **Coherence ascends along a finite extension of the coefficient field.**  If `K₀[X]` is
coherent and `K` is finite over `K₀`, then `K[X]` is coherent. -/
theorem ringCoherent_monoidAlgebra_of_finite (K₀ : Type u) [Field K₀] (K : Type u) [Field K]
    [Algebra K₀ K] [Module.Finite K₀ K] (X : Type v) [Group X]
    [J : Module (MonoidAlgebra K₀ X) (MonoidAlgebra K X)]
    (hJ : ∀ (a : MonoidAlgebra K₀ X) (m : MonoidAlgebra K X),
      a • m = MonoidAlgebra.mapRingHom X (algebraMap K₀ K) a * m)
    (h : Ring.Coherent (MonoidAlgebra K₀ X)) : Ring.Coherent (MonoidAlgebra K X) := by
  haveI hfree : Module.Free K₀ K := inferInstance
  haveI hf : Module.Free (MonoidAlgebra K₀ X) (MonoidAlgebra K X) :=
    (module_finite_free_monoidAlgebra K₀ K X hJ).1
  haveI hfin : Module.Finite (MonoidAlgebra K₀ X) (MonoidAlgebra K X) :=
    (module_finite_free_monoidAlgebra K₀ K X hJ).2
  exact ringCoherent_of_finite_free (MonoidAlgebra K₀ X) (MonoidAlgebra K X)
    (MonoidAlgebra.mapRingHom X (algebraMap K₀ K)) hJ h

/-- **The `Type 0` coefficient-field reduction.**  For a char-0 field `K₀` in the small universe,
coherence of `K₀[X]` follows from coherence of `L[X]` for every field `L` (also small) of
characteristic zero that embeds into `ℝ`.

Proof: `Ring.Coherent.of_subfield` reduces to the finitely generated subfields `F ≤ K₀`;
`exists_real_subfield_of_essFiniteType` gives `L ⊆ F` real-embeddable with `F/L` finite; coherence
ascends from `L[X]` to `F[X]` by `ringCoherent_monoidAlgebra_of_finite`. -/
theorem ringCoherent_of_typeZero (K₀ : Type) [Field K₀] [CharZero K₀] (X : Type) [Group X]
    (h : ∀ (L : Type) [Field L] [CharZero L] (ψ : L →+* ℝ),
      Ring.Coherent (MonoidAlgebra L X)) :
    Ring.Coherent (MonoidAlgebra K₀ X) := by
  refine Ring.Coherent.of_subfield X K₀ ?_
  intro S
  let F := ↥(Subfield.closure (S : Set K₀))
  haveI : Algebra.EssFiniteType ℚ F :=
    Work.ORReductions.Field.essFiniteType_closure K₀ S
  obtain ⟨L, ψ, hψ, hfin⟩ :=
    Work.ORFinal.RealSubfield.exists_real_subfield_of_essFiniteType F
  letI : Module (MonoidAlgebra ↥L X) (MonoidAlgebra F X) :=
    Module.compHom _ (MonoidAlgebra.mapRingHom X (algebraMap ↥L F))
  haveI : Module.Finite ↥L F := hfin
  exact ringCoherent_monoidAlgebra_of_finite ↥L F X (fun _ _ => rfl) (h ↥L ψ)

/-- **The coefficient-field reduction for an arbitrary char-0 field.**  Coherence of `K[X]` for
`K` of characteristic zero, with the group lifted into `K`'s universe, follows from coherence of
`L[X]` at every small real-embeddable coefficient field `L`. -/
theorem ringCoherent_of_charZero (K : Type u) [Field K] [CharZero K] {X : Type} [Group X]
    (h : ∀ (L : Type) [Field L] [CharZero L] (ψ : L →+* ℝ),
      Ring.Coherent (MonoidAlgebra L X)) :
    Ring.Coherent (MonoidAlgebra K (ULift.{u} X)) :=
  Work.ORDivLoc.P2.ringCoherent_ulift_of_typeZero K
    (fun K₀ _ _ _ => ringCoherent_of_typeZero K₀ X h)

end Work.ORFinal
