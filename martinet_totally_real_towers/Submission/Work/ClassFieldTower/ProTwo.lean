import Mathlib
import Submission.Work.ClassFieldTower.Defs
import Submission.Work.ClassFieldTower.Objects
import Submission.Work.ClassFieldTower.Tower
import Submission.Work.ClassFieldTower.Main
import Submission.Work.ClassFieldTower.ProTwoDefs
import Submission.Work.ClassFieldTower.infinite_of_hasMinimalPresentation
import Submission.Work.ClassFieldTower.exists_maximalUnramifiedProP
import Submission.Helpers
import Submission.Work.ClassFieldTower.isPGroup_two_of_residuallyFiniteTwo_of_finite
import Submission.Work.ClassFieldTower.finite_of_bounded_twoQuotients
import Submission.Work.ClassFieldTower.exists_imaginaryQuadratic_classGroupTwoRank_ge_five

/-!
# `Work.ClassFieldTower.ProTwo` -- the SOUND Golod--Shafarevich reduction

This module performs the Golod--Shafarevich argument in the form that is actually correct for a
pro-`p` group, avoiding the trap described in `ProTwoDefs.lean` (an infinite profinite Galois
group is uncountable, so it has no finite ABSTRACT presentation).

## The argument

Let `G` be an abstract group with a finite presentation `⟨α | rel⟩` that is *minimal* in `α`,
with `0 < #α` and `4 · #rel ≤ #α²`, which is residually a finite `2`-group
(`ResiduallyFiniteTwoGroup G`) and all of whose finite `2`-quotients are realized by unramified
extensions of `F` (`RealizedByUnramifiedExtensions F G`).  Then:

1. `ResiduallyFiniteTwoGroup G → Finite G → IsPGroup 2 G`, so the finite `p`-group
   Golod--Shafarevich inequality applies and `infinite_of_hasMinimalPresentation` gives
   `Infinite G`;
2. `ResiduallyFiniteTwoGroup G` + `Infinite G` gives finite `2`-quotients of `G` of arbitrarily
   large order (`finite_of_bounded_twoQuotients` in contrapositive form);
3. each of these is a finite unramified Galois extension of `F`, so `F` has unramified Galois
   extensions of arbitrarily large degree;
4. by the universal property of `F_∅` each of those embeds into `F_∅`, so `G_∅ = Gal(F_∅/F)` is
   infinite, and every level has `rootDiscr L = rootDiscr F`.

The single arithmetic input is `ProTwoPresentationData F` -- the Shafarevich--Koch presentation
datum for `G_∅` -- which is the classical Golod--Shafarevich arithmetic and needs the Artin
correspondence together with the Shafarevich--Koch relation bound.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open scoped Classical
open scoped NumberField
open NumberField

noncomputable section

namespace Work.ClassFieldTower

/-- **THE SOUND REDUCTION.**  A finite presentation of an abstract group `G` with `0 < #α`,
`α` minimal, `4 · #rel ≤ #α²`, plus `ResiduallyFiniteTwoGroup G` and
`RealizedByUnramifiedExtensions F G`, produces finite unramified Galois extensions of `F` of
arbitrarily large degree -- each of them pro-`2` (i.e. with `IsPGroup 2` Galois group). -/
theorem exists_unramifiedLevel_of_proTwoPresentation {F : Type*} [Field F] [NumberField F]
    {G : Type*} [Group G] {α : Type} [Fintype α] [DecidableEq α] (rel : Finset (FreeGroup α))
    (hpres : Nonempty (G ≃* FreeGroup α ⧸ Subgroup.normalClosure (rel : Set (FreeGroup α))))
    (hmin : ∀ S : Finset G, Subgroup.closure (S : Set G) = ⊤ → Fintype.card α ≤ S.card)
    (hpos : 0 < Fintype.card α)
    (hineq : 4 * rel.card ≤ Fintype.card α * Fintype.card α)
    (hres : ResiduallyFiniteTwoGroup G)
    (hreal : RealizedByUnramifiedExtensions F G) (N : ℕ) :
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra F L)
      (_ : FiniteDimensional F L) (_ : IsGalois F L),
      N ≤ Module.finrank F L ∧ differentIdeal (𝓞 F) (𝓞 L) = ⊤ ∧ IsPGroup 2 (L ≃ₐ[F] L) := by
  classical
  have hpres' : HasMinimalPresentation G (Fintype.card α) rel.card :=
    ⟨α, ‹Fintype α›, ‹DecidableEq α›, rel, rfl, rfl, hpres, hmin⟩
  have hinf : Infinite G :=
    infinite_of_hasMinimalPresentation
      (fun hfin => isPGroup_two_of_residuallyFiniteTwo_of_finite hres hfin) hpos hpres' hineq
  have hunb : ∃ (N' : Subgroup G) (_ : N'.Normal), Finite (G ⧸ N') ∧ IsPGroup 2 (G ⧸ N') ∧
      N < Nat.card (G ⧸ N') := by
    by_contra hc
    have hb : ∀ (N' : Subgroup G) [N'.Normal], Finite (G ⧸ N') → IsPGroup 2 (G ⧸ N') →
        Nat.card (G ⧸ N') ≤ N := by
      intro N' hN' hf hp
      by_contra hle
      exact hc ⟨N', hN', hf, hp, not_le.mp hle⟩
    exact absurd (finite_of_bounded_twoQuotients hres N hb)
      (not_finite_iff_infinite.mpr hinf)
  obtain ⟨N', hN', hfin', hpg', hcard'⟩ := hunb
  obtain ⟨L, iL, iNL, iAL, hfd, hgal, hdiff, ⟨e⟩⟩ := hreal N' hfin' hpg'
  refine ⟨L, iL, iNL, iAL, hfd, hgal, ?_, hdiff, ?_⟩
  · rw [← IsGalois.card_aut_eq_finrank F L]
    exact le_of_lt (lt_of_lt_of_eq hcard' (Nat.card_congr e.toEquiv.symm))
  · exact hpg'.of_equiv e.symm

/-- **The level form of the sound crux**: `ProTwoTowerInput F` gives, for every `N`, a finite
unramified Galois extension of `F` of degree at least `N` with pro-`2` Galois group. -/
theorem exists_unramifiedLevel_of_proTwoTowerInput {F : Type} [Field F] [NumberField F]
    (h : ProTwoTowerInput F) (N : ℕ) :
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra F L)
      (_ : FiniteDimensional F L) (_ : IsGalois F L),
      N ≤ Module.finrank F L ∧ differentIdeal (𝓞 F) (𝓞 L) = ⊤ ∧ IsPGroup 2 (L ≃ₐ[F] L) := by
  classical
  obtain ⟨⟨α, iα, iD, rel, hgen, hdef, hmin, hres, hreal⟩, h5, hu⟩ := h
  let G := FreeGroup α ⧸ Subgroup.normalClosure (rel : Set (FreeGroup α))
  have hineq : 4 * rel.card ≤ Fintype.card α * Fintype.card α := by
    have h1 : rel.card ≤ Fintype.card α + 1 := by omega
    have h2 : 5 ≤ Fintype.card α := by omega
    exact four_mul_le_sq_of_le_add_one h1 h2
  have hpos : 0 < Fintype.card α := by omega
  exact exists_unramifiedLevel_of_proTwoPresentation (F := F) (G := G) rel
    ⟨MulEquiv.refl G⟩ hmin hpos hineq hres hreal N

/-- **THE SOUND CRUX.**  `ProTwoTowerInput F` (the Shafarevich--Koch presentation datum with the
numerical certificate) implies that the maximal unramified pro-`2` extension of `F` is
infinite. -/
theorem infiniteProTwoExtension_of_proTwoTowerInput {F : Type} [Field F] [NumberField F]
    (h : ProTwoTowerInput F) : InfiniteProTwoExtension F := by
  classical
  obtain ⟨M⟩ := exists_maximalUnramifiedProP F 2
  refine ⟨M, ?_⟩
  rw [M.infinite_galoisGroup_iff_unbounded_subfields]
  intro N
  obtain ⟨L, iL, iNL, iAL, hfd, hgal, hdeg, hdiff, hpg⟩ :=
    exists_unramifiedLevel_of_proTwoTowerInput h N
  letI : Field L := iL
  letI : NumberField L := iNL
  letI : Algebra F L := iAL
  letI : FiniteDimensional F L := hfd
  letI : IsGalois F L := hgal
  letI : IsPGroup 2 (L ≃ₐ[F] L) := hpg
  obtain ⟨φ, -⟩ := M.universal L hpg hdiff
  let e : L ≃ₐ[F] ↥(φ.fieldRange) := AlgEquiv.ofInjectiveField φ
  haveI : FiniteDimensional F ↥(φ.fieldRange) := e.toLinearEquiv.finiteDimensional
  haveI : IsGalois F ↥(φ.fieldRange) := IsGalois.of_algEquiv e
  refine ⟨φ.fieldRange, inferInstance, inferInstance, ?_⟩
  rw [← e.toLinearEquiv.finrank_eq]
  exact hdeg

/-- **The conclusion in number-field form**: unramified levels of unbounded degree and constant
root discriminant `rootDiscr F`. -/
theorem exists_unramifiedNumberField_of_proTwoTowerInput {F : Type} [Field F] [NumberField F]
    (h : ProTwoTowerInput F) (N : ℕ) :
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra F L)
      (_ : FiniteDimensional F L) (_ : IsGalois F L),
      N ≤ Module.finrank F L ∧ differentIdeal (𝓞 F) (𝓞 L) = ⊤ ∧
        NumberField.rootDiscr L = NumberField.rootDiscr F := by
  obtain ⟨L, iL, iNL, iAL, hfd, hgal, hdeg, hdiff, hpg⟩ :=
    exists_unramifiedLevel_of_proTwoTowerInput h N
  exact ⟨L, iL, iNL, iAL, hfd, hgal, hdeg, hdiff, rootDiscr_eq_of_differentIdeal_eq_top hdiff⟩

/-- **THE ASYMPTOTICALLY GOOD FAMILY** from the sound arithmetic input. -/
theorem exists_bounded_rootDiscr_family_of_proTwoTowerInput {F : Type} [Field F] [NumberField F]
    (h : ProTwoTowerInput F) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∃ (L : Type) (_ : Field L) (_ : NumberField L),
      N ≤ Module.finrank ℚ L ∧ NumberField.rootDiscr L ≤ C := by
  classical
  refine ⟨NumberField.rootDiscr F,
    lt_of_lt_of_le zero_lt_one (Submission.Helpers.one_le_rootDiscr F), ?_⟩
  intro N
  obtain ⟨L, iL, iNL, iAL, hfd, hgal, hdeg, hdiff, hrd⟩ :=
    exists_unramifiedNumberField_of_proTwoTowerInput h N
  letI : Field L := iL
  letI : NumberField L := iNL
  letI : Algebra F L := iAL
  letI : FiniteDimensional F L := hfd
  have hdegQ : Module.finrank F L ≤ Module.finrank ℚ L := by
    have hmul : Module.finrank ℚ F * Module.finrank F L = Module.finrank ℚ L :=
      Module.finrank_mul_finrank ℚ F L
    have hpos : 0 < Module.finrank ℚ F := Module.finrank_pos
    nlinarith [Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hpos)]
  exact ⟨L, iL, iNL, le_trans hdeg hdegQ, le_of_eq hrd⟩

end Work.ClassFieldTower
