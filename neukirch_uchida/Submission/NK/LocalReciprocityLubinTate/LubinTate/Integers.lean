import Submission.NK.LocalReciprocityLubinTate.LubinTate.nonempty_lubinTateModule
import Submission.NK.LocalReciprocityLubinTate.LubinTate.isLubinTateSeries_piXAddXq
import Submission.NK.LocalReciprocityLubinTate.LubinTate.isLubinTateCoeff_integers
import Submission.NK.LocalReciprocityLubinTate.LubinTate.isFrobeniusPower_integers

/-!
# The Lubin–Tate formal group of a uniformiser over the ring of integers

This file assembles the first half of the Lubin–Tate construction **unconditionally for the ring of
integers of a nonarchimedean local field**:

> for `F` a nonarchimedean local field, `π ∈ 𝒪[F]` an irreducible element (equivalently: a
> uniformiser, `𝒪[F]` being a discrete valuation ring) and `q = #𝓀[F]`, there is a **Lubin–Tate
> module over `𝒪[F]`** for `π` whose `π`-multiplication is the standard Lubin–Tate series
> `πX + X^q`; equivalently there is a commutative formal group law `F_π` over `𝒪[F]` of which
> `πX + X^q` is an endomorphism, together with the ring homomorphism `𝒪[F] → End(F_π)`, `a ↦ [a]`,
> exhibiting `𝔪[F]` as an `𝒪[F]`-module under the group law of `F_π`.

This is Milne, *Class Field Theory*, §I.1 (Lemma 2.11, Propositions 2.12, 2.14, Corollary 2.17) in
the form in which the local class field theory chapter consumes it — *proved*, with no hypotheses
beyond the local field and the uniformiser.  The remaining half of the construction (the division
points `F_π[π^n]`, the fields `K_{π,n} = F(F_π[π^n])`, their degrees and Galois groups, and the norm
groups) is Stage 4–5 of `Submission/Work/LocalReciprocityLubinTate/README.md`.

## Main result

* `NK.LocalReciprocityLubinTate.lubinTateModule_integers`.
-/

open scoped ValuativeRel

namespace NK.LocalReciprocityLubinTate

universe u

noncomputable section

/-- The residue field of a nonarchimedean local field has at least two elements, so
`2 ≤ residueCard F`. -/
theorem two_le_residueCard (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] : 2 ≤ residueCard F := by
  haveI : Finite 𝓀[F] := inferInstance
  haveI : Fintype 𝓀[F] := Fintype.ofFinite _
  haveI : Nontrivial 𝓀[F] := inferInstance
  rw [residueCard, Nat.card_eq_fintype_card]
  exact Fintype.one_lt_card

/-- **The Lubin–Tate formal group of a uniformiser over `𝒪[F]`.**

For a nonarchimedean local field `F`, an irreducible (equivalently: uniformising) element
`π ∈ 𝒪[F]` and `q = #𝓀[F]`, there is a Lubin–Tate `𝒪[F]`-module for `π` whose `π`-multiplication is
the standard Lubin–Tate series `πX + X^q`: a commutative formal group law `F_π` over `𝒪[F]`
admitting `πX + X^q` as an endomorphism, together with the `𝒪[F]`-module structure `a ↦ [a]` on
`𝔪[F]`.

This is Milne, *CFT*, §I.1 (Lemma 2.11 + Propositions 2.12, 2.14 + Corollary 2.17), proved here from
the degree induction `NK.LocalReciprocityLubinTate.existsUnique_lubinTate_solution`; all its
hypotheses are themselves theorems for `𝒪[F]`
(`isLubinTateCoeff_integers`, `isFrobeniusPower_integers`, `isLubinTateSeries_piXAddXq`). -/
theorem lubinTateModule_integers (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (π : (↥(ValuativeRel.valuation F).integer))
    (hπ : Irreducible π) :
    ∃ M : LubinTateModule (↥(ValuativeRel.valuation F).integer) π (residueCard F),
      M.toLaw.piEndo = piXAddXq π (residueCard F) :=
  LubinTate.nonempty_lubinTateModule (LubinTate.isLubinTateCoeff_integers F π hπ)
    (LubinTate.isFrobeniusPower_integers F π hπ)
    (LubinTate.isLubinTateSeries_piXAddXq π (residueCard F) (two_le_residueCard F))

/-- The existence of the Lubin–Tate formal group law of a uniformiser, in the chapter's
`LubinTateFormalGroupExists` formulation (the `𝒪[F]`-module structure is part of the datum). -/
theorem lubinTateFormalGroupExists_integers (F : Type u) [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (π : (↥(ValuativeRel.valuation F).integer)) (hπ : Irreducible π) :
    LubinTateFormalGroupExists (↥(ValuativeRel.valuation F).integer) π (residueCard F) :=
  (lubinTateModule_integers F π hπ).elim fun M _ => ⟨M⟩

end

end NK.LocalReciprocityLubinTate
