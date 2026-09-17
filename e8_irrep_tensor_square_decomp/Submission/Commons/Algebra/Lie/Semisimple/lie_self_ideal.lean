import Mathlib.Algebra.Lie.Semisimple.Basic
import Mathlib.Order.CompletePartialOrder

/-!
# A Lie ideal of a semisimple Lie algebra equals its own derived ideal

We prove that if `I` is a Lie ideal of a semisimple Lie algebra `L` (over any field `K`),
then `⁅I, I⁆ = I`.  The proof rests on the two basic structural facts about semisimple Lie
algebras available in Mathlib:

* the atoms (with respect to inclusion) of the lattice of Lie ideals are precisely the simple
  ideals (`LieAlgebra.IsSemisimple.isSimple_of_isAtom`), and the atoms are independent and
  generated the whole algebra (`LieAlgebra.IsSemisimple.sSup_atoms_eq_top`), so that by
  `LieAlgebra.IsSemisimple.booleanGenerators` every ideal is the supremum of the atoms
  contained in it (`IsCompactlyGenerated.BooleanGenerators.atomistic`);
* a simple non-abelian Lie algebra `A` is perfect, i.e. `⁅A, A⁆ = A`.

The latter is `lie_self_of_isAtom` below: for an atom `A`, `A` is a simple Lie algebra, so the
derived ideal `derivedSeries K A 1` is either `⊥` (which would make `A` abelian, contradicting
`LieAlgebra.IsSimple.non_abelian`) or `⊤`; transporting back along `A.incl` via
`LieIdeal.derivedSeries_eq_derivedSeriesOfIdeal_map` gives `⁅A, A⁆ = A`.

The main theorem then follows by writing `I` as the supremum of the atoms `A ≤ I` and observing
`A = ⁅A, A⁆ ≤ ⁅I, I⁆` for each of them, while `⁅I, I⁆ ≤ I` is automatic.
-/

namespace Commons.Algebra.Lie.Semisimple

open LieAlgebra

/-- An atom of the lattice of Lie ideals of a semisimple Lie algebra - that is, a simple ideal -
is perfect: it equals its own derived ideal. -/
lemma lie_self_of_isAtom {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    [LieAlgebra.IsSemisimple K L] {A : LieIdeal K L} (hA : IsAtom A) : ⁅A, A⁆ = A := by
  -- A simple non-abelian Lie algebra is perfect.
  have hsimple : LieAlgebra.IsSimple K A := LieAlgebra.IsSemisimple.isSimple_of_isAtom A hA
  have htop : LieAlgebra.derivedSeries K A 1 = ⊤ := by
    rcases hsimple.eq_bot_or_eq_top (LieAlgebra.derivedSeries K A 1) with h | h
    · exfalso
      refine hsimple.non_abelian ?_
      rw [← lie_abelian_iff_equiv_lie_abelian (LieIdeal.topEquiv (R := K) (L := A))]
      exact (LieAlgebra.abelian_iff_derived_one_eq_bot (R := K) (L := A) ⊤).mpr h
    · exact h
  -- Transport the statement from the simple Lie algebra `A` back to the ambient `L`.
  have htopmap : (⊤ : LieIdeal K A).map A.incl = A := by
    apply le_antisymm
    · rw [LieIdeal.map_le]
      rintro y ⟨a, -, rfl⟩
      exact a.2
    · intro x hx
      simpa using LieIdeal.mem_map (f := A.incl) (I := (⊤ : LieIdeal K A))
        (x := (⟨x, hx⟩ : A)) (LieSubmodule.mem_top _)
  have hmap := LieIdeal.derivedSeries_eq_derivedSeriesOfIdeal_map (R := K) (L := L) (I := A) 1
  rw [htop, htopmap] at hmap
  have h2 : derivedSeriesOfIdeal K L 1 A = ⁅A, A⁆ := by
    rw [LieAlgebra.derivedSeriesOfIdeal_succ, LieAlgebra.derivedSeriesOfIdeal_zero]
  rw [h2] at hmap
  exact hmap.symm

/-- A Lie ideal of a semisimple Lie algebra is perfect: it is equal to its derived ideal
`⁅I, I⁆`. -/
theorem lie_self_ideal {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    [LieAlgebra.IsSemisimple K L] (I : LieIdeal K L) : ⁅I, I⁆ = I := by
  refine le_antisymm (LieSubmodule.lie_le_left I I) ?_
  -- Write `I` as the supremum of the atoms (simple ideals) contained in it.
  have hS := LieAlgebra.IsSemisimple.booleanGenerators K L
  obtain ⟨T, hTS, hT⟩ :=
    hS.atomistic I (by rw [LieAlgebra.IsSemisimple.sSup_atoms_eq_top]; exact le_top)
  have h : sSup T ≤ ⁅I, I⁆ := by
    refine sSup_le ?_
    intro A hA
    have hAle : A ≤ I := by rw [hT]; exact le_sSup hA
    calc A = ⁅A, A⁆ := (lie_self_of_isAtom (hTS hA)).symm
      _ ≤ ⁅I, I⁆ := LieSubmodule.mono_lie hAle hAle
  exact hT.symm ▸ h

end Commons.Algebra.Lie.Semisimple
