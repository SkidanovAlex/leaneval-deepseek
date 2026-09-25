import Mathlib
import Submission.Helpers
import Submission.Commons.FieldTheory.Galois.exists_finite_galois_finrank_ge_of_infinite_gal
import Submission.Commons.NumberTheory.NumberField.rootDiscr_eq_of_different_eq_top
import Submission.Commons.NumberTheory.NumberField.one_le_rootDiscr

open scoped NumberField
open NumberField

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-!
# The weak wall: an infinite unramified pro-`2` extension of an ARBITRARY number field

**STATUS: sorry-free.**  Off the `Submission.lean` proof path (additive infrastructure for the
Golod--Shafarevich routes).

The benchmark statement asks for TOTALLY REAL fields with bounded root discriminant.  This
module records that the total-reality requirement is not where the arithmetic content lies: if
a number field `F` (for instance an imaginary quadratic one -- the classical Golod--Shafarevich
situation) has an INFINITE unramified extension whose finite levels are unramified everywhere,
then its levels give number fields (not necessarily totally real) of unbounded degree with
CONSTANT root discriminant.  Together with the observation that the maximal real subfield `K⁺`
of a CM field satisfies `rootDiscr K⁺ ≤ rootDiscr K` (see `Work.CMRealSubfield`), this reduces
the benchmark to the *weaker* wall

  `BoundedRdTowerWall :  ∃ C > 0, ∀ N, ∃ a number field K of degree ≥ N with rootDiscr K ≤ C`

which needs no total reality, no tameness and no `S`-support condition.

The point of the reduction is that the classical Golod--Shafarevich theorem produces such an
infinite unramified tower over an imaginary quadratic field with a large `2`-class group
(`Submission/PLAN.md`, Route B), whereas the totally real tame-tower formulation makes the
relation count harder to state.
-/

namespace Submission.NumberField

noncomputable section

/-- **The weak wall (root discriminant form).**  There is `C > 0` such that for every `N` there
is a number field of degree at least `N` and root discriminant at most `C`.  No total reality,
no Galois-ness and no ramification restriction. -/
def BoundedRdTowerWall : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∃ d : ℕ, N ≤ d ∧
    ∃ (K : Type) (_ : Field K) (_ : NumberField K),
      Module.finrank ℚ K = d ∧ NumberField.rootDiscr K ≤ C

/-- **The weak wall (discriminant form).**  Same, with the absolute discriminant bound
`|disc K| ≤ C ^ [K : ℚ]`. -/
def BoundedDiscrTowerWall : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∃ d : ℕ, N ≤ d ∧
    ∃ (K : Type) (_ : Field K) (_ : NumberField K),
      Module.finrank ℚ K = d ∧ |(NumberField.discr K : ℝ)| ≤ C ^ d

/-- The root-discriminant form implies the discriminant form (for the same `C`). -/
theorem boundedDiscrTowerWall_of_boundedRdTowerWall (h : BoundedRdTowerWall) :
    BoundedDiscrTowerWall := by
  obtain ⟨C, hC, hfam⟩ := h
  refine ⟨C, hC, fun N => ?_⟩
  obtain ⟨d, hd, K, iK, iNK, hdeg, hrd⟩ := hfam N
  exact ⟨d, hd, K, iK, iNK, hdeg,
    Submission.Helpers.abs_discr_le_of_rootDiscr_le hdeg hrd⟩

/-- **An infinite unramified extension of an arbitrary number field gives the weak wall.**

If `K/F` is an infinite Galois extension whose finite dimensional Galois subextensions are
unramified at every finite prime (relative different `⊤`), then the levels realize
`BoundedRdTowerWall` with the constant `rootDiscr F`: every level has root discriminant
`rootDiscr F`, and the degrees over `ℚ` are unbounded.

This is the `p = 2` instance of the Golod--Shafarevich assembly WITHOUT the hypothesis that
`F` (or the levels) is totally real, which is what one has over an imaginary quadratic
base field. -/
theorem boundedRdTowerWall_of_infinite_unramified
    {F : Type} [Field F] [NumberField F]
    {K : Type} [Field K] [Algebra F K] [IsGalois F K]
    (hinf : Infinite (K ≃ₐ[F] K))
    (hunr : ∀ (L : IntermediateField F K) [NumberField ↥L], FiniteDimensional F L →
      IsGalois F L → differentIdeal (𝓞 F) (𝓞 ↥L) = ⊤) :
    BoundedRdTowerWall := by
  refine ⟨NumberField.rootDiscr F, lt_of_lt_of_le zero_lt_one
    (Submission.Helpers.one_le_rootDiscr F), fun N => ?_⟩
  obtain ⟨L, hfdL, hgalL, hdegL⟩ :=
    Commons.FieldTheory.Galois.exists_finite_galois_finrank_ge_of_infinite_gal
      (F := F) (K := K) hinf N
  letI : FiniteDimensional F L := hfdL
  letI : IsGalois F L := hgalL
  haveI : NumberField ↥L := NumberField.of_module_finite F ↥L
  have hroot : NumberField.rootDiscr ↥L = NumberField.rootDiscr F :=
    Commons.NumberTheory.NumberField.rootDiscr_eq_of_different_eq_top
      (E := F) (K := ↥L) (hunr L hfdL hgalL)
  have hmul : Module.finrank ℚ F * Module.finrank F ↥L = Module.finrank ℚ ↥L :=
    Module.finrank_mul_finrank ℚ F ↥L
  have hpos : 0 < Module.finrank ℚ F := Module.finrank_pos
  refine ⟨Module.finrank ℚ ↥L, ?_, ↥L, inferInstance, inferInstance, rfl, le_of_eq hroot⟩
  have hle : Module.finrank F ↥L ≤ Module.finrank ℚ F * Module.finrank F ↥L :=
    Nat.le_mul_of_pos_left _ hpos
  calc N ≤ Module.finrank F ↥L := hdegL
    _ ≤ Module.finrank ℚ F * Module.finrank F ↥L := hle
    _ = Module.finrank ℚ ↥L := hmul

end

end Submission.NumberField

namespace Submission.NumberField

noncomputable section

/-- **THE UNRAMIFIED PRO-`2` TOWER WALL (Route B).**  There is a number field `F` -- for
instance an imaginary quadratic one with a large `2`-class group, which is the classical
Golod--Shafarevich situation -- carrying an INFINITE Galois extension `K/F` all of whose
finite dimensional Galois subextensions are unramified at every finite prime.

This is the weakest form of the arithmetic input that still implies the benchmark statement:
it does NOT ask for `F` to be totally real, for the levels to be totally real, for tameness,
or for anything about `S`-supported ramification.  The passage to the benchmark statement goes
through `BoundedRdTowerWall` (this file) and the maximal real subfield of a CM field
(`Work.CMRealSubfield`). -/
def UnramifiedPro2TowerWall : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : NumberField F)
    (K : Type) (_ : Field K) (_ : Algebra F K) (_ : IsGalois F K),
    Infinite (K ≃ₐ[F] K) ∧
    (∀ (L : IntermediateField F K) [NumberField ↥L], FiniteDimensional F L → IsGalois F L →
      differentIdeal (𝓞 F) (𝓞 ↥L) = ⊤)

/-- **The weak wall follows from the unramified pro-`2` tower wall.** -/
theorem boundedRdTowerWall_of_unramifiedPro2TowerWall (h : UnramifiedPro2TowerWall) :
    BoundedRdTowerWall := by
  obtain ⟨F, iF, iNF, K, iK, iA, iG, hinf, hunr⟩ := h
  letI : Field F := iF
  letI : NumberField F := iNF
  letI : Field K := iK
  letI : Algebra F K := iA
  letI : IsGalois F K := iG
  exact boundedRdTowerWall_of_infinite_unramified hinf hunr

/-- **The discriminant-form weak wall follows from the unramified pro-`2` tower wall.** -/
theorem boundedDiscrTowerWall_of_unramifiedPro2TowerWall (h : UnramifiedPro2TowerWall) :
    BoundedDiscrTowerWall :=
  boundedDiscrTowerWall_of_boundedRdTowerWall
    (boundedRdTowerWall_of_unramifiedPro2TowerWall h)

end

end Submission.NumberField

namespace Submission.NumberField

noncomputable section

/-- **The pointwise form of the weak wall.**  If a single number field `F` has, for every `N`,
a finite extension of degree `≥ N` with relative different `⊤` (unramified at every finite
prime), then `BoundedRdTowerWall` holds with constant `rootDiscr F`.

This is the form the arithmetic side feeds: the arithmetic produces such levels (e.g. from
`GolodShafarevichArithmeticInput` WITHOUT the total-reality hypothesis), and every level has
root discriminant exactly `rootDiscr F`. -/
theorem boundedRdTowerWall_of_unbounded_unramified
    (F : Type) [Field F] [NumberField F]
    (h : ∀ N : ℕ, ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra F L)
            (_ : FiniteDimensional F L),
            N ≤ Module.finrank F L ∧ differentIdeal (𝓞 F) (𝓞 L) = ⊤) :
    BoundedRdTowerWall := by
  refine ⟨NumberField.rootDiscr F, lt_of_lt_of_le zero_lt_one
    (Submission.Helpers.one_le_rootDiscr F), fun N => ?_⟩
  obtain ⟨L, iL, iNL, iAL, hfdL, hdeg, hdiff⟩ := h N
  letI : Field L := iL
  letI : NumberField L := iNL
  letI : Algebra F L := iAL
  letI : FiniteDimensional F L := hfdL
  have hroot : NumberField.rootDiscr L = NumberField.rootDiscr F :=
    Commons.NumberTheory.NumberField.rootDiscr_eq_of_different_eq_top (E := F) (K := L) hdiff
  have hmul : Module.finrank ℚ F * Module.finrank F L = Module.finrank ℚ L :=
    Module.finrank_mul_finrank ℚ F L
  have hpos : 0 < Module.finrank ℚ F := Module.finrank_pos
  refine ⟨Module.finrank ℚ L, ?_, L, iL, iNL, rfl, le_of_eq hroot⟩
  calc N ≤ Module.finrank F L := hdeg
    _ ≤ Module.finrank ℚ F * Module.finrank F L := Nat.le_mul_of_pos_left _ hpos
    _ = Module.finrank ℚ L := hmul

/-- The same, in the discriminant form. -/
theorem boundedDiscrTowerWall_of_unbounded_unramified
    (F : Type) [Field F] [NumberField F]
    (h : ∀ N : ℕ, ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra F L)
            (_ : FiniteDimensional F L),
            N ≤ Module.finrank F L ∧ differentIdeal (𝓞 F) (𝓞 L) = ⊤) :
    BoundedDiscrTowerWall :=
  boundedDiscrTowerWall_of_boundedRdTowerWall
    (boundedRdTowerWall_of_unbounded_unramified F h)

end

end Submission.NumberField
