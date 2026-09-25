import Mathlib
import Submission.Work.Tower.Defs
import Submission.Work.Tower.Unramified.Basic
import Submission.Work.Tower.Unramified.Discriminant

set_option linter.style.haveILetI false

namespace Work.Tower.TowerCut

-- Imports: Mathlib, Submission.Work.Tower.Defs, Submission.Work.Tower.Unramified.Basic,
--          Submission.Work.Tower.Unramified.Discriminant
-- `AlgebraicClosure F` is a `ℚ`-algebra via `ℚ → F → ⋯`; it has `CharZero`.
-- Useful existing results (all proved, no sorry):
--   * `Work.Tower.natAbs_discr_eq_pow_of_isUnramifiedExtensionForallPrimes`
--       (h : IsUnramifiedExtensionForallPrimes F L) :
--       (discr L).natAbs = (discr F).natAbs ^ Module.finrank F L
--   * `Work.Tower.one_le_rootDiscr K : 1 ≤ rootDiscr K`
--   * `NumberField.finite_of_discr_bdd (A) (N)` : the set of intermediate fields of `A/ℚ` which
--     are finite-dimensional over `ℚ` and have `|discr| ≤ N` is finite
--     (`Mathlib/NumberTheory/NumberField/Discriminant/Basic.lean`).
-- Route: for `M` in the set, get `NumberField ↥M` from `NumberField.of_module_finite F`;
-- `Module.finrank F ↥M * Module.finrank ℚ F = Module.finrank ℚ ↥M` (tower law), so
-- `Module.finrank F ↥M ≤ n`; with `1 ≤ (discr F).natAbs` conclude
-- `|discr ↥M| ≤ (discr F).natAbs ^ n`; finally apply the finiteness of Hermite to the injective
-- map `M ↦ M.restrictScalars ℚ` (`IntermediateField.restrictScalars` keeps the same carrier, so
-- injection is `SetLike.ext`-level and `NumberField.discr` is unchanged).

open NumberField
open scoped Classical nonZeroDivisors

/-- **There are only finitely many intermediate fields `M` of `AlgebraicClosure F / F` which are
finite over `F`, unramified over `F` at every finite prime, and satisfy `[M : ℚ] ≤ n`.**

This is the `TowerCut` finiteness statement of the tower construction: it is the Hermite-style
input which guarantees that only finitely many fields compete at each level of the cut. -/
theorem finite_setOf_unramified (F : Type*) [Field F] [NumberField F] (n : ℕ) :
    {M : IntermediateField F (AlgebraicClosure F) |
      FiniteDimensional F M ∧ Work.Tower.IsUnramifiedExtensionForallPrimes F ↥M ∧
        Module.finrank ℚ ↥M ≤ n}.Finite := by
  classical
  -- The Hermite bound `N = |discr F| ^ n` on the absolute discriminant of the fields appearing.
  set N : ℕ := (discr F).natAbs ^ n with hN
  -- The set of `ℚ`-intermediate fields of `AlgebraicClosure F` which are number fields of
  -- discriminant bounded by `N` (phrased with the existential form of the Hermite theorem).
  set T : Set (IntermediateField ℚ (AlgebraicClosure F)) :=
    {K | ∃ h : FiniteDimensional ℚ ↥K,
      |@NumberField.discr ↥K _ (@NumberField.mk _ _ inferInstance h)| ≤ (N : ℤ)} with hTdef
  -- **Hermite's theorem** gives that `T` is finite.
  have hTfin : T.Finite := by
    have h := NumberField.finite_of_discr_bdd (AlgebraicClosure F) N
    refine (h.image Subtype.val).subset ?_
    rintro K ⟨hK, hdisc⟩
    exact ⟨⟨K, hK⟩, hdisc, rfl⟩
  -- It remains to inject our set into `T` along `M ↦ M.restrictScalars ℚ`.
  refine Set.Finite.of_finite_image (f := IntermediateField.restrictScalars ℚ) ?_
    (IntermediateField.restrictScalars_injective ℚ).injOn
  refine hTfin.subset ?_
  rintro K ⟨M, hM, rfl⟩
  obtain ⟨hfd, hunr, hdeg⟩ := hM
  -- `M` is a number field and finite dimensional over `ℚ` (via the tower `ℚ → F → M`).
  haveI : NumberField ↥M := NumberField.of_module_finite F ↥M
  haveI hMq : Module.Finite ℚ ↥M := Module.Finite.trans F ↥M
  -- `↥(M.restrictScalars ℚ)` is the same type as `↥M`, with the same `ℚ`-structure.
  haveI hMq' : Module.Finite ℚ ↥(M.restrictScalars ℚ) := inferInstanceAs (Module.Finite ℚ ↥M)
  haveI : NumberField ↥(M.restrictScalars ℚ) :=
    NumberField.of_module_finite ℚ ↥(M.restrictScalars ℚ)
  -- The discriminant is unchanged by `restrictScalars` (same carrier, same `ℚ`-algebra structure).
  have hdisc_eq : discr ↥(M.restrictScalars ℚ) = discr ↥M :=
    NumberField.discr_eq_discr_of_ringEquiv _ (RingEquiv.refl _)
  -- Unramifiedness makes the absolute discriminant the `[M : F]`-th power of `|discr F|`.
  have hpow := Work.Tower.natAbs_discr_eq_pow_of_isUnramifiedExtensionForallPrimes hunr
  -- Tower law: `[M : F] * [F : ℚ] = [M : ℚ] ≤ n`, hence `[M : F] ≤ n`.
  have htower : Module.finrank F ↥M * Module.finrank ℚ F = Module.finrank ℚ ↥M := by
    rw [← Module.finrank_mul_finrank ℚ F ↥M, mul_comm]
  have hfr : Module.finrank F ↥M ≤ n := by
    have h1 : 0 < Module.finrank ℚ F := Module.finrank_pos
    calc Module.finrank F ↥M ≤ Module.finrank F ↥M * Module.finrank ℚ F :=
          Nat.le_mul_of_pos_right _ h1
      _ = Module.finrank ℚ ↥M := htower
      _ ≤ n := hdeg
  -- Since `1 ≤ |discr F|`, the discriminant bound follows.
  have hbound : (discr ↥M).natAbs ≤ N := by
    rw [hpow, hN]
    exact Nat.pow_le_pow_right (Int.natAbs_pos.mpr (NumberField.discr_ne_zero F)) hfr
  have hmain : |discr ↥(M.restrictScalars ℚ)| ≤ (N : ℤ) := by
    rw [hdisc_eq, ← Int.natCast_natAbs]
    exact_mod_cast hbound
  exact ⟨hMq', hmain⟩

end Work.Tower.TowerCut
