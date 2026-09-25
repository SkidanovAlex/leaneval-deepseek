import Mathlib
import Submission.Work.ClassFieldTower.All
import Submission.Work.CMRealSubfield.All

/-!
# `Work.HilbertTowerCM.Defs` -- unramified levels and the two walls of the CM endgame

This is the definition layer of the `Work/HilbertTowerCM` area, the subproject that
turns an *arithmetic* statement about the maximal unramified pro-`2` extension of the
imaginary quadratic field

  `Kc = ℚ(√-30030)`

into **CM witnesses** of bounded root discriminant, i.e. into an input for
`Submission.Work.CMRealSubfield` (`Work.CMRealSubfield.CMWall`).

## The objects

* `UnramifiedLevel F` -- a finite Galois extension `L/F` of number fields which is unramified
  at every finite prime (`differentIdeal (𝓞 F) (𝓞 L) = ⊤`).  These are the levels of the
  unramified tower over `F`.
* `RealPartLevel`/`realPart` -- the **maximal real subfield** `L⁺ = NumberField.maximalRealSubfield L`
  of a level: it is always totally real, and `rootDiscr L⁺ ≤ rootDiscr L = rootDiscr F`
  (`UnramifiedLevel.realPart_rootDiscr_le`).

## The walls (what the CM endgame needs, stated exactly)

For a fixed base `F` (in the application `F = Kc`):

* `RealPartWall F` -- levels whose maximal real subfield has unbounded degree.  Because `L⁺` is
  totally real and has no larger root discriminant than `F`, this *is* the benchmark with the
  constant `rootDiscr F` (see `Work.HilbertTowerCM.benchmark_of_realPartWall`).  This is the
  weakest sufficient input of the whole endgame, and it is what the CM machinery is used for.
* `CMLevelWall F` -- levels that are CM (`NumberField.IsCMField`).  Such levels give
  `Work.CMRealSubfield.CMWall` with constant `rootDiscr F` (`cmWall_of_cmLevelWall`), hence the
  benchmark (`Work.CMRealSubfield.benchmark_of_cmWall`).
* `HalfRealLevelWall F` -- the structurally weakest form: levels whose maximal real subfield has
  at least half the degree (true for CM levels, where `[L : L⁺] = 2`).  It feeds
  `Work.CMRealSubfield.benchmark_of_halfRealSubfieldWall`.

All three walls are *proved* to imply the benchmark in `Work.HilbertTowerCM.Reduction`; the
arithmetic obligation of the endgame is to produce levels satisfying one of them.
-/

open scoped NumberField
open NumberField

noncomputable section

namespace Work.HilbertTowerCM

/-- **A level of an unramified tower over `F`**: a finite Galois extension `L/F` of number
fields with trivial relative different (unramified at every finite prime).

The carrier is `UnramifiedLevel.L`; Field/NumberField/Algebra/FiniteDimensional/IsGalois are
registered as instances so that `Module.finrank F L.L`, `rootDiscr L.L`,
`NumberField.maximalRealSubfield L.L` etc. resolve. -/
structure UnramifiedLevel (F : Type*) [Field F] [NumberField F] where
  /-- the level. -/
  L : Type
  [fieldL : Field L]
  [numberFieldL : NumberField L]
  [algebraL : Algebra F L]
  [finiteDimensionalL : FiniteDimensional F L]
  [isGaloisL : IsGalois F L]
  /-- the level is unramified at every finite prime. -/
  isUnramified : differentIdeal (𝓞 F) (𝓞 L) = ⊤

attribute [instance] UnramifiedLevel.fieldL UnramifiedLevel.numberFieldL UnramifiedLevel.algebraL
  UnramifiedLevel.finiteDimensionalL UnramifiedLevel.isGaloisL

namespace UnramifiedLevel

variable {F : Type*} [Field F] [NumberField F]

/-- **The root discriminant of a level is that of the base**: the discriminant is raised to the
`F`-degree and the relative different is trivial. -/
theorem rootDiscr_eq (L : UnramifiedLevel F) : rootDiscr L.L = rootDiscr F :=
  ClassFieldTower.rootDiscr_eq_of_differentIdeal_eq_top L.isUnramified

/-- The absolute discriminant of a level: `|disc L| = |disc F| ^ [L : F]`. -/
theorem discr_natAbs_eq (L : UnramifiedLevel F) :
    (NumberField.discr L.L).natAbs = (NumberField.discr F).natAbs ^ Module.finrank F L.L :=
  ClassFieldTower.natAbs_discr_eq_pow_of_differentIdeal_eq_top L.isUnramified

/-- **Levels of an unramified tower over a totally complex base are totally complex**: a real
place of a level would restrict to a real place of the base. -/
theorem isTotallyComplex (L : UnramifiedLevel F) [IsTotallyComplex F] :
    IsTotallyComplex L.L :=
  CMRealSubfield.isTotallyComplex_of_isTotallyComplex_base F L.L

/-- The **maximal real subfield** of a level, as a number field.  Its instances are
`NumberField.maximalRealSubfield L.L` (a subfield of `L.L`) with the subtype field structure. -/
abbrev realPart (L : UnramifiedLevel F) : Type := ↥(maximalRealSubfield L.L)

instance (L : UnramifiedLevel F) : Field (realPart L) := inferInstance
instance (L : UnramifiedLevel F) : NumberField (realPart L) := inferInstance
instance (L : UnramifiedLevel F) : IsTotallyReal (realPart L) :=
  NumberField.isTotallyReal_maximalRealSubfield

/-- **The real part of a level is totally real.** -/
theorem isTotallyReal_realPart (L : UnramifiedLevel F) : IsTotallyReal (realPart L) :=
  inferInstance

/-- **The root discriminant bound for the real part of a level**: `rootDiscr L⁺ ≤ rootDiscr F`.
This uses only the tower formula `disc(L) = disc(L⁺)^[L : L⁺] · N(𝔡)` and is the source of the
constant in the whole endgame. -/
theorem realPart_rootDiscr_le (L : UnramifiedLevel F) :
    rootDiscr (realPart L) ≤ rootDiscr F :=
  le_trans (CMRealSubfield.RootDiscr.rootDiscr_maximalRealSubfield_le_rootDiscr L.L)
    (le_of_eq L.rootDiscr_eq)

/-- The degree of the real part of a level, `[L⁺ : ℚ]`. -/
abbrev realPart_finrank (L : UnramifiedLevel F) : ℕ := Module.finrank ℚ (realPart L)

end UnramifiedLevel

/-! ## The walls -/

/-- **The real-part wall.**  For every `N` there is an unramified level whose maximal real
subfield has degree at least `N`.  Since a level has root discriminant `rootDiscr F` and its real
part has no larger root discriminant, this wall gives the benchmark with the constant
`rootDiscr F` (`Work.HilbertTowerCM.benchmark_of_realPartWall`). -/
def RealPartWall (F : Type*) [Field F] [NumberField F] : Prop :=
  ∀ N : ℕ, ∃ L : UnramifiedLevel F, N ≤ UnramifiedLevel.realPart_finrank L

/-- **The CM-level wall.**  For every `N` there is an unramified level which is CM and has degree
at least `N`.  Such levels give `Work.CMRealSubfield.CMWall` (with constant `rootDiscr F`), hence
the benchmark. -/
def CMLevelWall (F : Type*) [Field F] [NumberField F] : Prop :=
  ∀ N : ℕ, ∃ L : UnramifiedLevel F, IsCMField L.L ∧ N ≤ Module.finrank ℚ L.L

/-- **The half-real wall.**  For every `N` there is an unramified level of degree at least `N`
whose maximal real subfield has at least half the degree.  A CM level satisfies this with
equality (`[L : L⁺] = 2`). -/
def HalfRealLevelWall (F : Type*) [Field F] [NumberField F] : Prop :=
  ∀ N : ℕ, ∃ L : UnramifiedLevel F,
    N ≤ Module.finrank ℚ L.L ∧ Module.finrank ℚ L.L ≤ 2 * UnramifiedLevel.realPart_finrank L

/-- The CM-level wall is in particular the half-real wall: for a CM level `[L : L⁺] = 2`. -/
theorem halfRealLevelWall_of_cmLevelWall {F : Type*} [Field F] [NumberField F]
    (h : CMLevelWall F) : HalfRealLevelWall F := by
  intro N
  obtain ⟨L, hCM, hdeg⟩ := h N
  refine ⟨L, hdeg, ?_⟩
  haveI := hCM
  have h2 : Module.finrank ℚ L.L = 2 * Module.finrank ℚ (UnramifiedLevel.realPart L) :=
    CMRealSubfield.RealSubfield.finrank_eq_two_mul_finrank_maximalRealSubfield L.L
  show Module.finrank ℚ L.L ≤ 2 * Module.finrank ℚ (UnramifiedLevel.realPart L)
  omega

/-- **A CM level has half-real real part, hence the half-real wall is the relevant structural
condition**: a level is CM iff it is totally complex with a real part of exactly half the
degree (`Work.CMRealSubfield.RealSubfield.isCMField_iff_isTotallyComplex_and_finrank`). -/
theorem isCMField_iff_realPart_half {F : Type*} [Field F] [NumberField F]
    (L : UnramifiedLevel F) :
    IsCMField L.L ↔ IsTotallyComplex L.L ∧
      Module.finrank ℚ L.L = 2 * Module.finrank ℚ (UnramifiedLevel.realPart L) := by
  have h := CMRealSubfield.RealSubfield.isCMField_iff_isTotallyComplex_and_finrank L.L
  constructor
  · intro hCM
    exact ⟨h.mp hCM |>.1, (h.mp hCM |>.2).symm⟩
  · rintro ⟨hTC, hfin⟩
    exact h.mpr ⟨hTC, hfin.symm⟩

end Work.HilbertTowerCM
