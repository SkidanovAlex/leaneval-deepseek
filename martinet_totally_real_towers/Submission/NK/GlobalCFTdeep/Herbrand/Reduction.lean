/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Submission.NK.GlobalCFTdeep.CoCore.Reciprocity
import Submission.NK.GlobalCFTdeep.Herbrand.SIdeles
import Submission.NK.GlobalCFTdeep.Herbrand.natCard_tateCohomology_mul_of_shortExact

/-!
# The Herbrand quotient of `C_L`: the route through the `S`-idèles and the `S`-units

The delivered chapter states the Herbrand-quotient computation (Milne, *Class Field Theory*,
Theorem 4.3)

  `h(Gal(L/K), C_L) = [L : K]`

as the structure `NK.GlobalCFT.HerbrandQuotient K L`.  This file contains the **reduction** of
that structure to the three classical ingredients of Milne's proof, with the cohomological
assembly (multiplicativity of the Herbrand quotient along a short exact sequence, Milne
Proposition 3.6 together with Lemma 3.7) carried out in full.

Milne's proof, for cyclic `L/K` with group `G` and `n = [L : K]`:

1. choose a finite set `S` of places of `K` containing the archimedean places, the primes ramified
   in `L`, and a generating set of the ideal class group of `L`; let `T` be the places of `L`
   above `S`;
2. **Lemma 4.2**: `𝕀_L = Lˣ · 𝕀_{L,T}`, `Lˣ ∩ 𝕀_{L,T} = U_T` (the `T`-units), hence
   `C_L = 𝕀_L ⧸ Lˣ ≅ 𝕀_{L,T} ⧸ U_T` as `ℤ[G]`-modules — this is the short exact sequence
   `0 → U_T → 𝕀_{L,T} → C_L → 0` recorded below as `MilneHerbrandData.shortExact`;
3. **Proposition 2.7** (with the local computations `h(G_w, L_wˣ) = [L_w : K_v]` of Proposition 2.5
   and Shapiro's lemma): `h(𝕀_{L,T}) = ∏_{v ∈ S} [L_w : K_v] =: P`;
4. **Proposition 3.1** (`S`-unit theorem, Dirichlet's unit theorem and the comparison of
   `G`-stable lattices): `n · h(U_T) = P`;
5. `h(C_L) = h(𝕀_{L,T}) / h(U_T) = P / (P/n) = n`.

The arithmetic of step 5 is carried out in `herbrandEq_of_sequence` below, in the cross-multiplied
form in which the chapter states all Herbrand quotients (`Nat.card`-equalities, no division).

## What is *proved* here, and what is input

* `herbrandEq_of_sequence`: step 5, **proved** (given the Herbrand multiplicativity identity along
  the short exact sequence — an abstract statement about `ℤ[G]`-modules, proved independently in
  `Submission/Work/GlobalCFTdeep/Herbrand/multiplicativity.lean` when that file is present).
* `MilneHerbrandData`: steps 1–4 as data — the `S`-idèles `J`, the `S`-units `U`, the exact
  sequence `0 → U → J → C_L → 0`, and the two classical Herbrand computations with `P` in place of
  `∏_{v∈S}[L_w:K_v]`.
* `herbrandEq_classGroup`: `h(G, C_L) = [L:K]` from that data, and `HerbrandQuotient K L`.
-/

set_option maxHeartbeats 1600000
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

variable {G : Type} [CommGroup G] [Fintype G] [IsCyclic G]

/-- **Herbrand multiplicativity along a short exact sequence** (Milne, *CFT*, Proposition 3.6 with
Lemma 3.7), in the cross-multiplied form used by the assembly below.  It is proved from the long
exact sequence in Tate cohomology and the two-periodicity for cyclic `G`
(`Submission/Work/GlobalCFTdeep/Herbrand/natCard_tateCohomology_mul_of_shortExact.lean`). -/
theorem hZero_mul_hOne_of_shortExact (S : ShortComplex (Rep ℤ G)) (hS : S.ShortExact)
    [Finite ↥(tateCohomology S.X₁ 0)] [Finite ↥(tateCohomology S.X₁ 1)]
    [Finite ↥(tateCohomology S.X₂ 0)] [Finite ↥(tateCohomology S.X₂ 1)]
    [Finite ↥(tateCohomology S.X₃ 0)] [Finite ↥(tateCohomology S.X₃ 1)] :
    hZero S.X₂ * hOne S.X₁ * hOne S.X₃ =
      hZero S.X₁ * hZero S.X₃ * hOne S.X₂ :=
  Herbrand.natCard_tateCohomology_mul_of_shortExact S hS

/-- **The arithmetic core of Milne's Theorem 4.3.**  If `|Ĥ⁰(J)| = P·|Ĥ¹(J)|`,
`n·|Ĥ⁰(U)| = P·|Ĥ¹(U)|` (i.e. the Herbrand quotient of `U` is `P/n`), and the Herbrand
multiplicativity identity holds along a short exact sequence `0 → U → J → C → 0`, then the
Herbrand quotient of `C` is `n`; in cross-multiplied form, `|Ĥ⁰(C)| = n·|Ĥ¹(C)|`. -/
theorem mul_eq_of_herbrand_data {n P A J₁ U₀ U₁ C₀ C₁ : ℕ}
    (hJ : A = P * J₁) (hU : n * U₀ = P * U₁)
    (hMult : A * U₁ * C₁ = U₀ * C₀ * J₁)
    (hP : 0 < P) (hJ1 : 0 < J₁) (hU1 : 0 < U₁) :
    C₀ = n * C₁ := by
  have hU' : U₀ * n = P * U₁ := by rw [mul_comm]; exact hU
  have h1 : P * J₁ * U₁ * C₁ * n = P * U₁ * C₀ * J₁ := by
    calc P * J₁ * U₁ * C₁ * n = A * U₁ * C₁ * n := by rw [hJ]
      _ = U₀ * C₀ * J₁ * n := by rw [hMult]
      _ = (U₀ * n) * (C₀ * J₁) := by ring
      _ = (P * U₁) * (C₀ * J₁) := by rw [hU']
      _ = P * U₁ * C₀ * J₁ := by ring
  have h2 : (P * J₁ * U₁) * (C₁ * n) = (P * J₁ * U₁) * C₀ := by
    have h3 : P * J₁ * U₁ * C₁ * n = P * J₁ * U₁ * (C₁ * n) := by ring
    rw [h3] at h1
    rw [h1]
    ring
  have h4 : C₁ * n = C₀ := Nat.mul_left_cancel (by positivity) h2
  rw [← h4, mul_comm]

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- **Milne, *Class Field Theory*, Theorem 4.3**: `h(Gal(L/K), C_L) = [L : K]`, from the data of
the `S`-idèles and `S`-units: `P = ∏_{v ∈ S}[L_w : K_v]` is the product of the local degrees, `J`
and `U` are the `S`-idèles and the `S`-units, and the two hypotheses are Milne's Propositions 2.7
and 3.1, `h(J) = P` and `[L:K]·h(U) = P`.  The third hypothesis is the Herbrand multiplicativity
identity along the exact sequence `0 → U → J → C_L → 0` of Lemma 4.2 (proved for cyclic `G` in
`Submission/Work/GlobalCFTdeep/Herbrand/natCard_tateCohomology_mul_of_shortExact.lean`). -/
theorem herbrandEq_of_milneData
    (J U : Rep ℤ (L ≃ₐ[K] L)) (P : ℕ)
    (hJ : HerbrandEq J P) (hU : Nat.card (L ≃ₐ[K] L) * hZero U = P * hOne U)
    (hP : 0 < P) (hJ1 : 0 < hOne J) (hU1 : 0 < hOne U)
    (hMult : hZero J * hOne U * hOne (IdeleClassGroup.rep K L) =
      hZero U * hZero (IdeleClassGroup.rep K L) * hOne J) :
    HerbrandEq (IdeleClassGroup.rep K L) (Module.finrank K L) := by
  have h : hZero (IdeleClassGroup.rep K L) =
      Nat.card (L ≃ₐ[K] L) * hOne (IdeleClassGroup.rep K L) :=
    mul_eq_of_herbrand_data hJ hU hMult hP hJ1 hU1
  show hZero (IdeleClassGroup.rep K L) = Module.finrank K L * hOne (IdeleClassGroup.rep K L)
  rw [← IsGalois.card_aut_eq_finrank K L]
  exact h

/-- **The Herbrand-quotient computation of Milne's Theorem 4.3** in the form of the delivered
structure `NK.GlobalCFT.HerbrandQuotient`, from the `S`-idèles/`S`-units data.

The finiteness of `Ĥ¹(Gal(L/K), C_L)` is a separate hypothesis: classically `Ĥ¹ = 0`
(Milne, *CFT*, Theorem 5.1(b)), so in particular it is finite.  It is not implied by the equation
`|Ĥ⁰| = [L:K]·|Ĥ¹|` alone, because `Nat.card` is `0` on infinite types. -/
theorem herbrandQuotient_of_milneData
    (J U : Rep ℤ (L ≃ₐ[K] L)) (P : ℕ)
    (hJ : HerbrandEq J P) (hU : Nat.card (L ≃ₐ[K] L) * hZero U = P * hOne U)
    (hP : 0 < P) (hJ1 : 0 < hOne J) (hU1 : 0 < hOne U)
    (hMult : hZero J * hOne U * hOne (IdeleClassGroup.rep K L) =
      hZero U * hZero (IdeleClassGroup.rep K L) * hOne J)
    [Finite ↥(tateCohomology (IdeleClassGroup.rep K L) 1)] :
    HerbrandQuotient K L where
  finite_h1 := Nat.card_pos
  herbrand := herbrandEq_of_milneData J U P hJ hU hP hJ1 hU1 hMult

/-- **Milne, *CFT*, Theorem 4.3** from the `S`-idèles/`S`-units data, with the Herbrand
multiplicativity identity *discharged* by the long exact sequence in Tate cohomology: the exact
sequence `0 → U → J → C_L → 0` of Lemma 4.2, together with Propositions 2.7 and 3.1, gives
`h(Gal(L/K), C_L) = [L : K]` for cyclic `L/K`. -/
theorem herbrandQuotient_of_milneShortExact [IsCyclic (L ≃ₐ[K] L)]
    (J U : Rep ℤ (L ≃ₐ[K] L)) (P : ℕ) (i : U ⟶ J) (p : J ⟶ IdeleClassGroup.rep K L)
    (w : i ≫ p = 0) (hS : (ShortComplex.mk i p w).ShortExact)
    (hJ : HerbrandEq J P) (hU : Nat.card (L ≃ₐ[K] L) * hZero U = P * hOne U)
    (hP : 0 < P) (hJ1 : 0 < hOne J) (hU1 : 0 < hOne U)
    [Finite ↥(tateCohomology U 0)] [Finite ↥(tateCohomology U 1)]
    [Finite ↥(tateCohomology J 0)] [Finite ↥(tateCohomology J 1)]
    [Finite ↥(tateCohomology (IdeleClassGroup.rep K L) 0)]
    [Finite ↥(tateCohomology (IdeleClassGroup.rep K L) 1)] :
    HerbrandQuotient K L :=
  herbrandQuotient_of_milneData J U P hJ hU hP hJ1 hU1
    (hZero_mul_hOne_of_shortExact (ShortComplex.mk i p w) hS)

/-! ### The `S`-idèles and `S`-units of `Herbrand/SIdeles.lean` -/

/-- **Milne, *CFT*, Theorem 4.3** for the concrete `T`-idèles and `T`-units of
`Submission/Work/GlobalCFTdeep/Herbrand/SIdeles.lean`: given the two classical Herbrand
computations (Propositions 2.7 and 3.1) and the multiplicativity identity along
`0 → U(T) → 𝕀_{L,T} → C_L → 0`, the Herbrand quotient of `C_L` is `[L : K]`. -/
theorem herbrandEq_of_TIdeles (T : Set (Place L))
    (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : Place L⦄, w ∈ T → σ • w ∈ T) (P : ℕ)
    (hJ : HerbrandEq (tIdelesRep T hT) P)
    (hU : Nat.card (L ≃ₐ[K] L) * hZero (tUnitsRep T hT) = P * hOne (tUnitsRep T hT))
    (hP : 0 < P) (hJ1 : 0 < hOne (tIdelesRep T hT)) (hU1 : 0 < hOne (tUnitsRep T hT))
    (hMult : hZero (tIdelesRep T hT) * hOne (tUnitsRep T hT) *
        hOne (IdeleClassGroup.rep K L) =
      hZero (tUnitsRep T hT) * hZero (IdeleClassGroup.rep K L) * hOne (tIdelesRep T hT)) :
    HerbrandEq (IdeleClassGroup.rep K L) (Module.finrank K L) :=
  herbrandEq_of_milneData (tIdelesRep T hT) (tUnitsRep T hT) P hJ hU hP hJ1 hU1 hMult


/-- **Milne, *CFT*, Theorem 4.3** for the concrete `T`-idèles and `T`-units of
`Herbrand/SIdeles.lean`, with the exact sequence of Milne's Lemma 4.2 supplied as data: the two
classical computations (Propositions 2.7 and 3.1) give `h(Gal(L/K), C_L) = [L : K]`. -/
theorem herbrandQuotient_of_TIdeles [IsCyclic (L ≃ₐ[K] L)] (T : Set (Place L))
    (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : Place L⦄, w ∈ T → σ • w ∈ T) (P : ℕ)
    (i : tUnitsRep T hT ⟶ tIdelesRep T hT) (p : tIdelesRep T hT ⟶ IdeleClassGroup.rep K L)
    (w : i ≫ p = 0) (hS : (ShortComplex.mk i p w).ShortExact)
    (hJ : HerbrandEq (tIdelesRep T hT) P)
    (hU : Nat.card (L ≃ₐ[K] L) * hZero (tUnitsRep T hT) = P * hOne (tUnitsRep T hT))
    (hP : 0 < P) (hJ1 : 0 < hOne (tIdelesRep T hT)) (hU1 : 0 < hOne (tUnitsRep T hT))
    [Finite ↥(tateCohomology (tUnitsRep T hT) 0)]
    [Finite ↥(tateCohomology (tUnitsRep T hT) 1)]
    [Finite ↥(tateCohomology (tIdelesRep T hT) 0)]
    [Finite ↥(tateCohomology (tIdelesRep T hT) 1)]
    [Finite ↥(tateCohomology (IdeleClassGroup.rep K L) 0)]
    [Finite ↥(tateCohomology (IdeleClassGroup.rep K L) 1)] :
    HerbrandQuotient K L :=
  herbrandQuotient_of_milneShortExact (tIdelesRep T hT) (tUnitsRep T hT) P i p w hS
    hJ hU hP hJ1 hU1

end NK.GlobalCFTdeep
