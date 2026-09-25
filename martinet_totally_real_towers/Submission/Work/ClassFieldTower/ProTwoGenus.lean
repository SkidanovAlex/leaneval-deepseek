import Mathlib
import Submission.Work.ClassFieldTower.Defs
import Submission.Work.ClassFieldTower.Objects
import Submission.Work.ClassFieldTower.Main
import Submission.Work.ClassFieldTower.ProTwoDefs
import Submission.Work.ClassFieldTower.ProTwo
import Submission.Work.ClassFieldTower.five_le_of_surjective_zmodTwo_five
import Submission.Commons.GroupTheory.SpecificGroups.ZModProd.exists_mulEquiv_multiplicative_fin_zmod_two_of_fintype_commutative_pow_two_eq_one_card

/-!
# `Work.ClassFieldTower.ProTwoGenus` -- the generator half, without class field theory

The sound Golod--Shafarevich input `ProTwoShafarevichKochInput F` below isolates the arithmetic
content as (i) the Shafarevich--Koch deficiency bound on the number of relators,
`#rel ≤ #α + 1`, and (ii) a description of `G_∅` by the finite `2`-quotients of an abstract group
`G` (`DescribesMaximalProTwo`).  The numerical bound `5 ≤ #α` is NOT assumed: it is DERIVED, with
no class field theory, from

* the existence of an unramified exponent-`2` Galois level of degree `2^5` over `F`
  (`HasGenusLevel F` -- the genus field of an imaginary quadratic field with six prime
  discriminant factors: for `F = ℚ(√D)`, `D = d₁⋯d₆`, the field `ℚ(√d₁,…,√d₆)`), and
* `DescribesMaximalProTwo F G`, whose second conjunct makes that level a quotient of `G`.

Indeed a finite group of order `32` all of whose elements are involutions is `(ℤ/2)^5`, which
needs five generators, so `#α ≥ 5` (`five_le_of_surjective_zmodTwo_five`).
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open scoped Classical
open scoped NumberField
open NumberField

noncomputable section

namespace Work.ClassFieldTower

/-- **The genus level.**  There is a finite unramified Galois extension `L/F` of degree `2^5`
whose Galois group has exponent `2`.  For `F = ℚ(√D)` with `D = d₁⋯d₆` a product of six prime
discriminants, `L = ℚ(√d₁,…,√d₆)` works. -/
def HasGenusLevel (F : Type*) [Field F] [NumberField F] : Prop :=
  ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra F L)
    (_ : FiniteDimensional F L) (_ : IsGalois F L),
    differentIdeal (𝓞 F) (𝓞 L) = ⊤ ∧ (∀ σ : L ≃ₐ[F] L, σ ^ 2 = 1) ∧
      Nat.card (L ≃ₐ[F] L) = 2 ^ 5

/-- **The exact description of `G_∅` by an abstract group `G`.**  The finite `2`-group quotients
of `G` are, up to isomorphism, exactly the Galois groups of the finite unramified pro-`2` Galois
extensions of `F`. -/
def DescribesMaximalProTwo (F : Type*) [Field F] [NumberField F] (G : Type*) [Group G] : Prop :=
  (∀ (N : Subgroup G) [N.Normal], Finite (G ⧸ N) → IsPGroup 2 (G ⧸ N) →
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra F L)
      (_ : FiniteDimensional F L) (_ : IsGalois F L),
      differentIdeal (𝓞 F) (𝓞 L) = ⊤ ∧ Nonempty ((L ≃ₐ[F] L) ≃* (G ⧸ N))) ∧
  (∀ (L : Type) [Field L] [NumberField L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L],
    differentIdeal (𝓞 F) (𝓞 L) = ⊤ → IsPGroup 2 (L ≃ₐ[F] L) →
    ∃ (N : Subgroup G) (_ : N.Normal), Finite (G ⧸ N) ∧ IsPGroup 2 (G ⧸ N) ∧
      Nonempty ((G ⧸ N) ≃* (L ≃ₐ[F] L)))

/-- **The Shafarevich--Koch input, sound form.**  An abstract group `G` describing `G_∅`
(`DescribesMaximalProTwo`), residually a finite `2`-group, with a presentation by `α` generators
(minimal) and `rel` relators satisfying the Shafarevich--Koch deficiency bound
`#rel ≤ #α + 1`.  The bound `5 ≤ #α` is derived, not assumed. -/
def ProTwoShafarevichKochInput (F : Type*) [Field F] [NumberField F] : Prop :=
  ∃ (α : Type) (_ : Fintype α) (_ : DecidableEq α) (rel : Finset (FreeGroup α)),
    let G := FreeGroup α ⧸ Subgroup.normalClosure (rel : Set (FreeGroup α))
    rel.card ≤ Fintype.card α + 1 ∧
    (∀ S : Finset G, Subgroup.closure (S : Set G) = ⊤ → Fintype.card α ≤ S.card) ∧
    ResiduallyFiniteTwoGroup G ∧
    DescribesMaximalProTwo F G

/-- A group of exponent dividing `2` is commutative. -/
theorem commute_of_sq_eq_one {G : Type*} [Group G] (h : ∀ x : G, x ^ 2 = 1)
    (a b : G) : a * b = b * a := by
  have ha : a⁻¹ = a := by
    have := h a
    rw [pow_two] at this
    exact mul_eq_one_iff_inv_eq.mp this
  have hb : b⁻¹ = b := by
    have := h b
    rw [pow_two] at this
    exact mul_eq_one_iff_inv_eq.mp this
  have hab : (a * b)⁻¹ = a * b := by
    have := h (a * b)
    rw [pow_two] at this
    exact mul_eq_one_iff_inv_eq.mp this
  rw [mul_inv_rev, ha, hb] at hab
  exact hab.symm

/-- **`5 ≤ #α`, with no class field theory.**  From a genus level of `F` and a description of
`G_∅` by `G`, the minimal generator number `#α` of `G` is at least `5`. -/
theorem five_le_card_of_genusLevel {F : Type} [Field F] [NumberField F] {G : Type} [Group G]
    {α : Type} [Fintype α] [DecidableEq α] {rel : Finset (FreeGroup α)}
    (hpres : Nonempty (G ≃* FreeGroup α ⧸ Subgroup.normalClosure (rel : Set (FreeGroup α))))
    (hmin : ∀ S : Finset G, Subgroup.closure (S : Set G) = ⊤ → Fintype.card α ≤ S.card)
    (hdesc : DescribesMaximalProTwo F G) (hgenus : HasGenusLevel F) :
    5 ≤ Fintype.card α := by
  classical
  obtain ⟨L, iL, iNL, iAL, hfd, hgal, hunr, hexp, hcard⟩ := hgenus
  letI : Field L := iL
  letI : NumberField L := iNL
  letI : Algebra F L := iAL
  letI : FiniteDimensional F L := hfd
  letI : IsGalois F L := hgal
  have hpg : IsPGroup 2 (L ≃ₐ[F] L) := by
    rw [isPGroup_iff_pow_pow_eq_one]
    intro σ
    exact ⟨1, by rw [pow_one]; exact hexp σ⟩
  obtain ⟨N, hN, hfinN, hpgN, ⟨eN⟩⟩ := hdesc.2 L hunr hpg
  haveI : N.Normal := hN
  haveI : Fintype (G ⧸ N) := Fintype.ofFinite _
  have h2N : ∀ z : G ⧸ N, z ^ 2 = 1 := by
    intro z
    refine eN.injective ?_
    rw [map_pow, hexp (eN z), map_one]
  haveI : IsMulCommutative (G ⧸ N) :=
    IsMulCommutative.of_comm (fun a b => commute_of_sq_eq_one h2N a b)
  have hcardN : Nat.card (G ⧸ N) = 2 ^ 5 := by
    rw [Nat.card_congr eN.toEquiv]
    exact hcard
  obtain ⟨e5⟩ :=
    Commons.GroupTheory.SpecificGroups.ZModProd.exists_mulEquiv_multiplicative_fin_zmod_two_of_fintype_commutative_pow_two_eq_one_card
      (G := G ⧸ N) h2N hcardN
  have hpres' : HasMinimalPresentation G (Fintype.card α) rel.card :=
    ⟨α, ‹Fintype α›, ‹DecidableEq α›, rel, rfl, rfl, hpres, hmin⟩
  exact five_le_of_surjective_zmodTwo_five hpres'
    (e5.toMonoidHom.comp (QuotientGroup.mk' N))
    (e5.surjective.comp (QuotientGroup.mk'_surjective N))

/-- **THE SOUND ARITHMETIC INPUT, with the generator half divorced from class field theory.**

`ProTwoShafarevichKochInput F` (the Shafarevich--Koch deficiency bound `#rel ≤ #α + 1` plus a
description of `G_∅` by the finite `2`-quotients of `G`) together with a genus level of `F`
(`HasGenusLevel F`, pure number theory) gives an infinite maximal unramified pro-`2` extension.

This is the exact content of the classical Golod--Shafarevich theorem for a quadratic field
ramified at many places: the numerical bound `d ≥ 5` is supplied by genus theory, and only the
relation bound is class field theory. -/
theorem infiniteProTwoExtension_of_shafarevichKoch_and_genusLevel {F : Type} [Field F]
    [NumberField F] (h : ProTwoShafarevichKochInput F) (hgenus : HasGenusLevel F) :
    InfiniteProTwoExtension F := by
  classical
  obtain ⟨α, iα, iD, rel, hrel, hmin, hres, hdesc⟩ := h
  let G := FreeGroup α ⧸ Subgroup.normalClosure (rel : Set (FreeGroup α))
  have h5 : 5 ≤ Fintype.card α :=
    five_le_card_of_genusLevel (F := F) (G := G) ⟨MulEquiv.refl G⟩ hmin hdesc hgenus
  have hpos : 0 < Fintype.card α := by omega
  have hineq : 4 * rel.card ≤ Fintype.card α * Fintype.card α :=
    four_mul_le_sq_of_le_add_one hrel h5
  obtain ⟨M⟩ := exists_maximalUnramifiedProP F 2
  refine ⟨M, ?_⟩
  rw [M.infinite_galoisGroup_iff_unbounded_subfields]
  intro N
  obtain ⟨L, iL, iNL, iAL, hfd, hgal, hdeg, hdiff, hpgL⟩ :=
    exists_unramifiedLevel_of_proTwoPresentation (F := F) (G := G) rel
      ⟨MulEquiv.refl G⟩ hmin hpos hineq hres hdesc.1 N
  letI : Field L := iL
  letI : NumberField L := iNL
  letI : Algebra F L := iAL
  letI : FiniteDimensional F L := hfd
  letI : IsGalois F L := hgal
  letI : IsPGroup 2 (L ≃ₐ[F] L) := hpgL
  obtain ⟨φ, -⟩ := M.universal L hpgL hdiff
  let e : L ≃ₐ[F] ↥(φ.fieldRange) := AlgEquiv.ofInjectiveField φ
  haveI : FiniteDimensional F ↥(φ.fieldRange) := e.toLinearEquiv.finiteDimensional
  haveI : IsGalois F ↥(φ.fieldRange) := IsGalois.of_algEquiv e
  refine ⟨φ.fieldRange, inferInstance, inferInstance, ?_⟩
  rw [← e.toLinearEquiv.finrank_eq]
  exact hdeg

end Work.ClassFieldTower
