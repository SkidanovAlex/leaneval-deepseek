import Mathlib
import Submission.Helpers
import Submission.GroupTheory.GolodShafarevichCriterion
import Submission.Commons.NumberTheory.NumberField.rootDiscr_eq_of_different_eq_top
import Submission.Commons.NumberTheory.NumberField.isTotallyReal_of_isUnramifiedAtInfinitePlaces
import Submission.Commons.GroupTheory.finite_of_bounded_finite_quotients

open scoped NumberField
open NumberField

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-!
# The arithmetic input of the Golod--Shafarevich route, and the reduction of the benchmark to it

**STATUS: sorry-free.**  CHAIN C (the Golod--Shafarevich route).  Off the `Submission.lean`
proof path.

The Golod--Shafarevich proof of Martinet's theorem has two halves:

* the GROUP THEORY: a correct packaging of the Golod--Shafarevich criterion
  (`Submission.GroupTheory.GolodShafarevichCriterion`); and
* the ARITHMETIC: a presentation of the maximal unramified pro-`2` extension group of a
  totally real number field by `d` generators and `r` relators with `4 * r ≤ d ^ 2`.

This module records the second half as a single `Prop`,
`GolodShafarevichArithmeticInput`, and reduces the benchmark statement to it (given the
finite `p`-group Golod--Shafarevich inequality and one elementary group-theory lemma about
bounded finite quotients).  The intermediate step is the observation that
`F` has unramified (at every finite prime and at the infinite places) totally real Galois
extensions of unbounded degree -- and each such level has root discriminant exactly
`rootDiscr F`, which is Martinet's conclusion.

`GolodShafarevichArithmeticInput` asks for:

* a totally real number field `F`;
* a finite presentation `⟨α | rel⟩` of a group `G` with `4 * |rel| ≤ |α| ^ 2`, `|α| > 0`,
  `α` minimal (`hmin`), all finite quotients of `G` of `2`-power order (`hquot`);
* `G` residually finite (`hres`); and
* EVERY finite quotient `G ⧸ N` of `G` is (isomorphic to) the Galois group of a finite
  Galois extension `L / F` unramified at every finite prime and at the infinite places
  (`hreal`) -- i.e. `G` is a presentation of the maximal unramified pro-`2` group of `F`.

Both directions of the identification "arithmetic ⟹ such a presentation" and the relation
rank bound (`4 r ≤ d ^ 2`) are the arithmetic content to be supplied later; the
finite `p`-group Golod--Shafarevich inequality is
`Submission.GroupTheory.FinitePGroupGolodShafarevich`.
-/

namespace Submission.NumberField

noncomputable section

/-- **The unbounded-level reduction.**  If a totally real number field `F` has Galois
extensions unramified at every finite prime and at the infinite places of unbounded degree,
then the benchmark statement holds: every such level `L` is totally real and has
`rootDiscr L = rootDiscr F`, so `C := rootDiscr F` is an admissible constant. -/
theorem exists_totallyReal_discr_le_of_unbounded_unramified_pro2
    (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F]
    (h : ∀ N : ℕ, ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra F L)
            (_ : FiniteDimensional F L),
            N ≤ Module.finrank F L ∧ differentIdeal (𝓞 F) (𝓞 L) = ⊤ ∧
              IsUnramifiedAtInfinitePlaces F L) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∃ d : ℕ, N ≤ d ∧
      ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : NumberField.IsTotallyReal K),
        Module.finrank ℚ K = d ∧ |(NumberField.discr K : ℝ)| ≤ C ^ d := by
  classical
  have hCpos : 0 < NumberField.rootDiscr F :=
    lt_of_lt_of_le zero_lt_one (Submission.Helpers.one_le_rootDiscr F)
  refine Submission.Helpers.exists_totallyReal_discr_le_of_rootDiscrFamily
    ⟨NumberField.rootDiscr F, hCpos, ?_⟩
  intro N
  obtain ⟨L, iL, iNL, iAL, hfdL, hdeg, hdiff, hunr⟩ := h N
  letI : Field L := iL
  letI : NumberField L := iNL
  letI : Algebra F L := iAL
  letI : FiniteDimensional F L := hfdL
  haveI : IsUnramifiedAtInfinitePlaces F L := hunr
  have htr : NumberField.IsTotallyReal L :=
    Commons.NumberTheory.NumberField.isTotallyReal_of_isUnramifiedAtInfinitePlaces F L
  have hdegQ : Module.finrank F L ≤ Module.finrank ℚ L := by
    have hmul : Module.finrank ℚ F * Module.finrank F L = Module.finrank ℚ L :=
      Module.finrank_mul_finrank ℚ F L
    have hpos : 0 < Module.finrank ℚ F := Module.finrank_pos
    nlinarith [Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hpos)]
  have hroot : NumberField.rootDiscr L = NumberField.rootDiscr F :=
    Commons.NumberTheory.NumberField.rootDiscr_eq_of_different_eq_top hdiff
  exact ⟨Module.finrank ℚ L, le_trans hdeg hdegQ, L, iL, iNL, htr, rfl, le_of_eq hroot⟩

/-- **The arithmetic input of the Golod--Shafarevich seam.** -/
def GolodShafarevichArithmeticInput : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : NumberField F) (_ : NumberField.IsTotallyReal F)
    (α : Type) (_ : Fintype α) (_ : DecidableEq α) (rel : Finset (FreeGroup α)),
    let G := FreeGroup α ⧸ Subgroup.normalClosure (rel : Set (FreeGroup α))
    0 < Fintype.card α ∧
    4 * rel.card ≤ Fintype.card α * Fintype.card α ∧
    (∀ S : Finset G, Subgroup.closure (S : Set G) = ⊤ → Fintype.card α ≤ S.card) ∧
    Group.ResiduallyFinite G ∧
    (∀ (N : Subgroup G) [N.Normal], Finite (G ⧸ N) → IsPGroup 2 (G ⧸ N)) ∧
    (∀ (N : Subgroup G) [N.Normal], Finite (G ⧸ N) →
      ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra F L)
        (_ : FiniteDimensional F L) (_ : IsGalois F L),
        differentIdeal (𝓞 F) (𝓞 L) = ⊤ ∧ IsUnramifiedAtInfinitePlaces F L ∧
        Nonempty ((L ≃ₐ[F] L) ≃* (G ⧸ N)))

/-- **THE REDUCTION.**  The arithmetic input above, together with the finite `p`-group
Golod--Shafarevich inequality and the elementary fact that a finitely generated residually
finite group with bounded finite quotients is finite, implies the benchmark statement.

The chain is: the corrected criterion
(`Submission.GroupTheory.infinite_of_presentation_of_golodShafarevich`) makes `G` infinite;
residual finiteness then forces `G` to have finite quotients of arbitrarily large order;
each of those is an unramified totally real Galois extension of `F`; and the
unbounded-level reduction above finishes. -/
theorem exists_totallyReal_discr_le_of_golodShafarevich
    (hbound : ∀ (M : ℕ) (G : Type) [Group G] [Group.FG G] [Group.ResiduallyFinite G],
      (∀ (N : Subgroup G) [N.Normal], Finite (G ⧸ N) → Nat.card (G ⧸ N) ≤ M) → Finite G)
    (hGS : Submission.GroupTheory.FinitePGroupGolodShafarevich 2)
    (h : GolodShafarevichArithmeticInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∃ d : ℕ, N ≤ d ∧
      ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : NumberField.IsTotallyReal K),
        Module.finrank ℚ K = d ∧ |(NumberField.discr K : ℝ)| ≤ C ^ d := by
  classical
  obtain ⟨F, iF, iNF, hTR, α, iα, iDα, rel, hpos, hineq, hmin, hres, hquot, hreal⟩ := h
  letI : Field F := iF
  letI : NumberField F := iNF
  letI : NumberField.IsTotallyReal F := hTR
  letI : Fintype α := iα
  letI : DecidableEq α := iDα
  let G := FreeGroup α ⧸ Subgroup.normalClosure (rel : Set (FreeGroup α))
  haveI hFG : Group.FG G := inferInstance
  haveI hRF : Group.ResiduallyFinite G := hres
  have hpres : Nonempty (G ≃* FreeGroup α ⧸ Subgroup.normalClosure (rel : Set (FreeGroup α))) :=
    ⟨MulEquiv.refl G⟩
  have hinf : Infinite G :=
    Submission.GroupTheory.infinite_of_presentation_of_golodShafarevich hGS rel hpos hpres
      hmin hquot hineq
  have hunb : ∀ M : ℕ, ∃ (N : Subgroup G) (_ : N.Normal), Finite (G ⧸ N) ∧ M < Nat.card (G ⧸ N) := by
    intro M
    by_contra hc
    refine absurd (hbound M G ?_) (not_finite_iff_infinite.mpr hinf)
    intro N hNnorm hfin
    by_contra hle
    exact hc ⟨N, hNnorm, hfin, not_le.mp hle⟩
  refine exists_totallyReal_discr_le_of_unbounded_unramified_pro2 F ?_
  intro N
  obtain ⟨N₀, hN₀n, hfin, hcard⟩ := hunb N
  obtain ⟨L, iL, iNL, iAL, hfdL, hgalL, hdiff, hunr, ⟨e⟩⟩ := hreal N₀ hfin
  refine ⟨L, iL, iNL, iAL, hfdL, ?_, hdiff, hunr⟩
  letI : Field L := iL
  letI : NumberField L := iNL
  letI : Algebra F L := iAL
  letI : FiniteDimensional F L := hfdL
  letI : IsGalois F L := hgalL
  rw [← IsGalois.card_aut_eq_finrank F L]
  exact le_of_lt (lt_of_lt_of_eq hcard (Nat.card_congr e.toEquiv).symm)

/-- **THE REDUCTION, unconditional in the group-theoretic input.**  The arithmetic input and
the finite `p`-group Golod--Shafarevich inequality imply the benchmark statement: the
bounded-quotient input of the previous theorem is supplied by the commons lemma
`Commons.GroupTheory.finite_of_bounded_finite_quotients`. -/
theorem exists_totallyReal_discr_le_of_golodShafarevichArithmetic
    (hGS : Submission.GroupTheory.FinitePGroupGolodShafarevich 2)
    (h : GolodShafarevichArithmeticInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∃ d : ℕ, N ≤ d ∧
      ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : NumberField.IsTotallyReal K),
        Module.finrank ℚ K = d ∧ |(NumberField.discr K : ℝ)| ≤ C ^ d :=
  exists_totallyReal_discr_le_of_golodShafarevich
    (fun M G _ _ _ hh => Commons.GroupTheory.finite_of_bounded_finite_quotients G M hh) hGS h

end

end Submission.NumberField
