/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Submission.NK.GlobalCFTdeep.Herbrand.milneFourTwoExact_nonempty
import Submission.NK.GlobalCFTdeep.Herbrand.Reduction

/-!
# The complete assembly of Milne's Theorem 4.3

With Milne's Lemma 4.2 now inhabiting the equivariant short exact sequence
`0 → U(T) → 𝕀_{L,T} → C_L → 0` (`Herbrand/milneFourTwoExact_nonempty.lean`), the whole of Milne's
proof of the Herbrand-quotient computation `h(Gal(L/K), C_L) = [L : K]` reduces to the two
classical *numerical* inputs of Milne's Propositions 2.7 and 3.1 for the chosen `T`:

* `hJ : h(𝕀_{L,T}) = P` where `P = ∏_{v ∈ S}[L_w : K_v]` (Proposition 2.7, from the local
  computations and Shapiro's lemma — both already available here: `herbrandEq_coind_iff`,
  `herbrandEq_coind_trivial`, `herbrandEq_of_shortExact`, `herbrandEq_units_adicCompletion_of_abelian`);
* `hU : [L:K] · h(U(T)) = P · |Ĥ¹(U(T))|`, i.e. `[L:K] · h(U(T)) = P` (Proposition 3.1, from
  Dirichlet's unit theorem, the `T`-unit theorem and the comparison of `G`-stable lattices).

`herbrandQuotient_of_milneFourTwo` below is that assembly: it produces
`NK.GlobalCFT.HerbrandQuotient K L` (Milne's Theorem 4.3) for a cyclic extension from those two
inputs and the complement condition `𝕀_L = Lˣ · 𝕀_{L,T}` of Lemma 4.2, with no further
cohomological work.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped NumberField RestrictedProduct IsMulCommutative
open NumberField IsDedekindDomain
open CategoryTheory

noncomputable section

namespace NK.GlobalCFTdeep

open NK.GlobalCFT

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- **Milne, *Class Field Theory*, Theorem 4.3, from the two numerical inputs of Propositions 2.7
and 3.1.**  For a cyclic extension `L/K`, a finite `Gal(L/K)`-stable set `T` of places of `L`
satisfying the complement condition `𝕀_L = Lˣ · 𝕀_{L,T}` of Lemma 4.2, and a natural number `P`
with `h(𝕀_{L,T}) = P` (Proposition 2.7) and `[L:K]·h(U(T)) = P` (Proposition 3.1):

  `h(Gal(L/K), C_L) = [L : K]`,

i.e. `NK.GlobalCFT.HerbrandQuotient K L`. -/
theorem herbrandQuotient_of_milneFourTwo [IsCyclic (L ≃ₐ[K] L)] (T : Set (Place L))
    (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : Place L⦄, w ∈ T → σ • w ∈ T)
    (h : (⊤ : Subgroup (Idele L)) = Idele.principalSubgroup L ⊔ TIdeles T) (P : ℕ)
    (hJ : HerbrandEq (tIdelesRep T hT) P)
    (hU : Nat.card (L ≃ₐ[K] L) * hZero (tUnitsRep T hT) = P * hOne (tUnitsRep T hT))
    (hP : 0 < P) (hJ1 : 0 < hOne (tIdelesRep T hT)) (hU1 : 0 < hOne (tUnitsRep T hT))
    [Finite ↥(tateCohomology (tUnitsRep T hT) 0)]
    [Finite ↥(tateCohomology (tUnitsRep T hT) 1)]
    [Finite ↥(tateCohomology (tIdelesRep T hT) 0)]
    [Finite ↥(tateCohomology (tIdelesRep T hT) 1)]
    [Finite ↥(tateCohomology (IdeleClassGroup.rep K L) 0)]
    [Finite ↥(tateCohomology (IdeleClassGroup.rep K L) 1)] :
    HerbrandQuotient K L := by
  obtain ⟨E⟩ := Herbrand.milneFourTwoExact_nonempty T hT h
  exact herbrandQuotient_of_TIdeles T hT P E.i E.p E.w E.shortExact hJ hU hP hJ1 hU1

end NK.GlobalCFTdeep
