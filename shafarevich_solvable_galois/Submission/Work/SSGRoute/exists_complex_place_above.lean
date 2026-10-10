import Mathlib.RingTheory.Henselian
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
import Submission.Work.SSGRoute.eb_arch_aux

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Work.SSGRoute

/-- **Enlarging a number field so that a prescribed archimedean place becomes complex.**

For number fields `k ⊆ L₀` with `L₀/k` finite Galois and a *real* infinite place `u₀` of `L₀`, there
is a finite Galois extension `L/k` containing `L₀` and an infinite place `u` of `L` lying over `u₀`
which is *complex*. -/
theorem exists_complex_place_above (k L₀ : Type) [Field k] [NumberField k] [Field L₀]
    [NumberField L₀] [Algebra k L₀] [FiniteDimensional k L₀] [IsGalois k L₀]
    (u₀ : NumberField.InfinitePlace L₀) (hu₀ : u₀.IsReal) :
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra k L) (_ : Algebra L₀ L)
      (_ : IsScalarTower k L₀ L) (_ : FiniteDimensional k L) (_ : IsGalois k L)
      (u : NumberField.InfinitePlace L), u.LiesOver u₀ ∧ u.IsComplex := by
  classical
  -- Enlarge `k ⊆ L₀` to a cyclotomic tower `k ⊆ L₀ ⊆ E` containing `M = k(ζ₃)`, whose every
  -- infinite place is complex.
  obtain ⟨M, E, hMf, hMNF, hEf, hENF, hkM, hkE, hL₀E, hME, hstLE, hstME, hfdM, hfdE,
    hgalM, hgalE, hcyc, hcycE, hadjoin, hcomp⟩ :=
      eb_arch_aux k L₀ 3 (by norm_num) (by norm_num)
  letI : Algebra k E := hkE
  letI : Algebra L₀ E := hL₀E
  letI : IsScalarTower k L₀ E := hstLE
  letI : FiniteDimensional k E := hfdE
  letI : IsGalois k E := hgalE
  letI : Algebra k M := hkM
  letI : Algebra M E := hME
  letI : IsScalarTower k M E := hstME
  -- `E` is finite (hence algebraic) over `L₀`, since it is finite over `k`.
  haveI hfinLE : FiniteDimensional L₀ E :=
    Module.Finite.of_restrictScalars_finite k L₀ E
  haveI halgLE : Algebra.IsAlgebraic L₀ E := Algebra.IsAlgebraic.of_finite L₀ E
  -- A complex embedding of `E` extending the real embedding defining `u₀`.
  let φ : L₀ →+* ℂ := NumberField.InfinitePlace.embedding u₀
  let u : NumberField.InfinitePlace E :=
    NumberField.InfinitePlace.mk (NumberField.ComplexEmbedding.lift E φ)
  refine ⟨E, hEf, hENF, hkE, hL₀E, hstLE, hfdE, hgalE, u, ?_, ?_⟩
  · -- `u` restricts to `u₀` on `L₀`.
    have h : u.comap (algebraMap L₀ E) = u₀ := by
      rw [NumberField.InfinitePlace.comap_mk_lift (K := E) φ]
      exact NumberField.InfinitePlace.mk_embedding u₀
    exact ⟨congrArg Subtype.val h⟩
  · -- `u` restricts to a place of `M = k(ζ₃)`, and every such place is complex.
    refine NumberField.InfinitePlace.IsComplex.of_comap (algebraMap M E) ?_
    exact hcomp (u.comap (algebraMap M E))

end Work.SSGRoute
