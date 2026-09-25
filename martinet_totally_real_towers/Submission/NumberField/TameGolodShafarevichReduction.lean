import Mathlib
import Submission.GroupTheory.GolodShafarevichCriterion
import Submission.Commons.GroupTheory.finite_of_bounded_finite_quotients
import Submission.Commons.NumberTheory.NumberField.natAbs_discr_le_pow_of_tame_different
import Submission.Commons.NumberTheory.NumberField.ramificationIdx_dvd_two_pow_of_isPGroup
import Submission.Commons.NumberTheory.NumberField.ramificationIdx_dvd_finrank_of_isGalois
import Submission.Commons.NumberTheory.NumberField.isTotallyReal_of_isUnramifiedAtInfinitePlaces

open scoped NumberField
open NumberField

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-!
# The Golod--Shafarevich reduction for the TAME route (the source paper's route)

**STATUS: sorry-free.**  CHAIN C-2 (the tame / `MartinetTameWall` route).  Off the
`Submission.lean` proof path.

`Submission.lean` currently proves the benchmark statement from the named wall
`Submission.NumberField.MartinetTameWall` (the infinitude of the tame pro-`2` tower).  This module
provides the SAME reduction, but ending at a PRESENTATION-SHAPED arithmetic input, which is the
form the arithmetic will actually supply:

* `exists_totallyReal_discr_le_of_unbounded_tame_levels` -- a totally real base `F`, a finite set
  `S` of odd primes, and Galois levels `L/F` with `[L : F]` unbounded, pro-`2` Galois group,
  unramified at the infinite places, and `S`-supported different, produce the benchmark statement.
  This is the POINTWISE (no-tower, no maximal-extension) form of the SESSION 278 tame assembly:
  each level satisfies the tame discriminant bound
  `|disc L| ≤ (|disc F| · ∏_{q ∈ S} q) ^ [L : ℚ]`
  (`Commons.NumberTheory.NumberField.natAbs_discr_le_pow_of_tame_different`, whose tameness
  hypothesis is discharged from the pro-`2`-ness: a `2`-power ramification index is coprime to the
  odd prime `q`);
* `TameGolodShafarevichInput` -- THE ARITHMETIC INPUT OF THE TAME ROUTE in presentation form:
  a finite presentation `⟨α | rel⟩` of a group `G` with `4 * r ≤ d ^ 2` (`d = |α| > 0`, minimal
  generators), all finite quotients `2`-groups, `G` residually finite, and every finite quotient of
  `G` isomorphic to the Galois group of a finite Galois extension of `ℚ` with `S`-supported
  different and unramified at the infinite places (i.e. `⟨α | rel⟩` presents the maximal pro-`2`
  extension of `ℚ` unramified outside `S`).  The two sides of the arithmetic are
  (i) `d ≥ |S|` -- from the multiquadratic extension
  (`Commons.NumberTheory.NumberField.exists_multiquadratic_totallyReal_unramifiedOutside`) and
  (ii) the relation count `r ≤ d + 1` (indeed `r = d`) -- the `F_2` Euler characteristic of `G_S^T`
  (`Neukirch 10.7.12`);
* `exists_totallyReal_discr_le_of_tameGolodShafarevich` -- THE REDUCTION:
  `FinitePGroupGolodShafarevich 2` + `TameGolodShafarevichInput` ⟹ the benchmark statement.
-/

namespace Submission.NumberField

noncomputable section

/-- **The pointwise tame reduction.**  If a totally real number field `F` has, for arbitrarily
large `N`, a finite Galois extension `L/F` with `[L : F] ≥ N`, pro-`2` Galois group, unramified at
the infinite places, and `S`-supported different (`S` a finite set of odd primes), then the
benchmark statement holds, with the explicit constant `|disc F| · ∏_{q ∈ S} q`. -/
theorem exists_totallyReal_discr_le_of_unbounded_tame_levels
    (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F]
    (S : Finset ℕ) (hS : ∀ q ∈ S, Nat.Prime q) (hodd : ∀ q ∈ S, q ≠ 2)
    (h : ∀ N : ℕ, ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra F L)
            (_ : FiniteDimensional F L) (_ : IsGalois F L),
            N ≤ Module.finrank F L ∧ IsPGroup 2 (L ≃ₐ[F] L) ∧
            IsUnramifiedAtInfinitePlaces F L ∧
            (∀ (P : Ideal (𝓞 L)), P.IsPrime → P ≠ ⊥ →
              P ∣ differentIdeal (𝓞 F) (𝓞 L) → ∃ q ∈ S, P.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ)))) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∃ d : ℕ, N ≤ d ∧
      ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : NumberField.IsTotallyReal K),
        Module.finrank ℚ K = d ∧ |(NumberField.discr K : ℝ)| ≤ C ^ d := by
  classical
  set C : ℝ := (((NumberField.discr F).natAbs * ∏ q ∈ S, q : ℕ) : ℝ) with hCdef
  have hCpos : 0 < C := by
    rw [hCdef]
    have h1 : 1 ≤ (NumberField.discr F).natAbs :=
      Int.natAbs_pos.mpr (NumberField.discr_ne_zero F)
    have h2 : 0 < ∏ q ∈ S, q := by
      refine Finset.prod_pos fun q hq => (hS q hq).pos
    have : 0 < (NumberField.discr F).natAbs * ∏ q ∈ S, q := Nat.mul_pos (lt_of_lt_of_le zero_lt_one h1) h2
    exact_mod_cast this
  refine ⟨C, hCpos, fun N => ?_⟩
  obtain ⟨L, iL, iNL, iAL, hfdL, hgalL, hNL, hpgL, hunrInf, hsupp⟩ := h N
  letI : Field L := iL
  letI : NumberField L := iNL
  letI : Algebra F L := iAL
  letI : FiniteDimensional F L := hfdL
  letI : IsGalois F L := hgalL
  haveI : IsUnramifiedAtInfinitePlaces F L := hunrInf
  have htr : NumberField.IsTotallyReal L :=
    Commons.NumberTheory.NumberField.isTotallyReal_of_isUnramifiedAtInfinitePlaces F L
  -- the tame discriminant bound at the level `L`
  have htame : ∀ q ∈ S, ∀ (P : Ideal (𝓞 L)), P.IsMaximal →
      P.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ)) →
        ¬ q ∣ P.ramificationIdx (𝓞 F) := by
    intro q hq P hPmax hPlies hdvd
    obtain ⟨k, hk⟩ :=
      Commons.NumberTheory.NumberField.ramificationIdx_dvd_two_pow_of_isPGroup (F := F)
        (L := L) hpgL P
    rw [hk] at hdvd
    have hq2 : q ∣ 2 := (hS q hq).dvd_of_dvd_pow hdvd
    rcases (Nat.dvd_prime Nat.prime_two).mp hq2 with h1 | h2
    · exact (hS q hq).ne_one h1
    · exact hodd q hq h2
  have hbound :=
    Commons.NumberTheory.NumberField.natAbs_discr_le_pow_of_tame_different (F := F) (L := L)
      S hS hsupp htame
  -- relative-to-absolute degree
  have hdegQ : Module.finrank F L ≤ Module.finrank ℚ L := by
    have hmul : Module.finrank ℚ F * Module.finrank F L = Module.finrank ℚ L :=
      Module.finrank_mul_finrank ℚ F L
    have hpos : 0 < Module.finrank ℚ F := Module.finrank_pos
    nlinarith [Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hpos)]
  have hdisc : |(NumberField.discr L : ℝ)| = ((NumberField.discr L).natAbs : ℝ) := by
    calc |(NumberField.discr L : ℝ)| = ((|NumberField.discr L| : ℤ) : ℝ) := by rw [Int.cast_abs]
      _ = (((NumberField.discr L).natAbs : ℤ) : ℝ) := by rw [Int.abs_eq_natAbs]
      _ = ((NumberField.discr L).natAbs : ℝ) := by norm_num
  refine ⟨Module.finrank ℚ L, le_trans hNL hdegQ, L, iL, iNL, htr, rfl, ?_⟩
  rw [hdisc]
  calc ((NumberField.discr L).natAbs : ℝ)
      ≤ ((NumberField.discr F).natAbs * ∏ q ∈ S, q : ℕ) ^ Module.finrank ℚ L := by
        exact_mod_cast hbound
    _ = C ^ Module.finrank ℚ L := by rw [hCdef]

/-- **The arithmetic input of the tame Golod--Shafarevich route, in presentation form.** -/
def TameGolodShafarevichInput : Prop :=
  ∃ (S : Finset ℕ), (∀ q ∈ S, Nat.Prime q) ∧ (∀ q ∈ S, q ≠ 2) ∧
    ∃ (α : Type) (_ : Fintype α) (_ : DecidableEq α) (rel : Finset (FreeGroup α)),
    let G := FreeGroup α ⧸ Subgroup.normalClosure (rel : Set (FreeGroup α))
    0 < Fintype.card α ∧
    4 * rel.card ≤ Fintype.card α * Fintype.card α ∧
    (∀ S' : Finset G, Subgroup.closure (S' : Set G) = ⊤ → Fintype.card α ≤ S'.card) ∧
    Group.ResiduallyFinite G ∧
    (∀ (N : Subgroup G) [N.Normal], Finite (G ⧸ N) → IsPGroup 2 (G ⧸ N)) ∧
    (∀ (N : Subgroup G) [N.Normal], Finite (G ⧸ N) →
      ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra ℚ L)
        (_ : FiniteDimensional ℚ L) (_ : IsGalois ℚ L),
        IsUnramifiedAtInfinitePlaces ℚ L ∧
        (∀ (P : Ideal (𝓞 L)), P.IsPrime → P ≠ ⊥ → P ∣ differentIdeal (𝓞 ℚ) (𝓞 L) →
          ∃ q ∈ S, P.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ))) ∧
        Nonempty ((L ≃ₐ[ℚ] L) ≃* (G ⧸ N)))

/-- **THE REDUCTION (tame route).**  The finite `p`-group Golod--Shafarevich inequality together
with the arithmetic input above implies the benchmark statement.

The chain: the corrected criterion
(`Submission.GroupTheory.infinite_of_presentation_of_golodShafarevich`) makes `G` infinite;
residual finiteness plus
`Commons.GroupTheory.finite_of_bounded_finite_quotients` produces finite quotients of `G` of
arbitrarily large order; the arithmetic input turns each of them into a pro-`2`, infinite-place
unramified, `S`-supported Galois extension of `ℚ` of the same degree; and the pointwise tame
reduction above finishes. -/
theorem exists_totallyReal_discr_le_of_tameGolodShafarevich
    (hGS : Submission.GroupTheory.FinitePGroupGolodShafarevich 2)
    (h : TameGolodShafarevichInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∃ d : ℕ, N ≤ d ∧
      ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : NumberField.IsTotallyReal K),
        Module.finrank ℚ K = d ∧ |(NumberField.discr K : ℝ)| ≤ C ^ d := by
  classical
  obtain ⟨S, hS, hodd, α, iα, iDα, rel, hpos, hineq, hmin, hres, hquot, hreal⟩ := h
  letI : Fintype α := iα
  letI : DecidableEq α := iDα
  let G := FreeGroup α ⧸ Subgroup.normalClosure (rel : Set (FreeGroup α))
  haveI hRF : Group.ResiduallyFinite G := hres
  have hpres : Nonempty (G ≃* FreeGroup α ⧸ Subgroup.normalClosure (rel : Set (FreeGroup α))) :=
    ⟨MulEquiv.refl G⟩
  have hinf : Infinite G :=
    Submission.GroupTheory.infinite_of_presentation_of_golodShafarevich hGS rel hpos hpres
      hmin hquot hineq
  have hunb : ∀ M : ℕ, ∃ (N : Subgroup G) (_ : N.Normal), Finite (G ⧸ N) ∧ M < Nat.card (G ⧸ N) := by
    intro M
    by_contra hc
    refine absurd (Commons.GroupTheory.finite_of_bounded_finite_quotients G M ?_)
      (not_finite_iff_infinite.mpr hinf)
    intro N hNnorm hfin
    by_contra hle
    exact hc ⟨N, hNnorm, hfin, not_le.mp hle⟩
  refine exists_totallyReal_discr_le_of_unbounded_tame_levels ℚ S hS hodd ?_
  intro N
  obtain ⟨N₀, hN₀n, hfin, hcard⟩ := hunb N
  obtain ⟨L, iL, iNL, iAL, hfdL, hgalL, hunrInf, hsupp, ⟨e⟩⟩ := hreal N₀ hfin
  refine ⟨L, iL, iNL, iAL, hfdL, hgalL, ?_, ?_, hunrInf, hsupp⟩
  · rw [← IsGalois.card_aut_eq_finrank ℚ L]
    exact le_of_lt (lt_of_lt_of_eq hcard (Nat.card_congr e.toEquiv).symm)
  · exact (hquot N₀ hfin).of_equiv e.symm

end

end Submission.NumberField
