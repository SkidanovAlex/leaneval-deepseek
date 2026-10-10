import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Algebra.IsSimpleRing
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Commons.NumberTheory.NumberField.numberField_of_intermediateField
import Submission.Work.SSGRoute.exists_level_pthRoot
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

namespace Work.SSGRoute

/-- **A level (Galois over `k`) on which a global unit becomes a `p`-th power.**

For a tower `k ⊆ K` of number fields with `K/k` finite Galois, a prime `p` and `β ∈ Kˣ`, there is a
number field `L` with `k ⊆ K ⊆ L` finite Galois over `k` in which the image of `β` is a `p`-th
power (already in `Lˣ`, not just locally).

Route: put `K` inside `Ω = AlgebraicClosure k`: `IsAlgClosed.lift` gives `ι : K →ₐ[k] Ω` (using
`Algebra.IsAlgebraic.of_finite`), take `K' := ι.fieldRange : IntermediateField k Ω`, with
`FiniteDimensional k ↥K'`, `IsGalois k ↥K'` via `IsGalois.of_algEquiv (AlgHom.equivFieldRange ι)`
and `NumberField ↥K'` via `Commons.NumberTheory.NumberField.numberField_of_intermediateField`.
Apply `Work.SSGRoute.exists_level_pthRoot` with base field `k`, `Ω`, and the level `K'` to the unit
`x := Units.mk0 (AlgHom.equivFieldRange ι β) _ : ↥K'ˣ`, obtaining `L' : IntermediateField k Ω`
with `NumberField ↥L'`, `FiniteDimensional k ↥L'`, `IsGalois k ↥L'`, `K' ≤ L'`, and
`y : ↥L'ˣ` with `Units.map (IntermediateField.inclusion h) x = y ^ p`.  Take `L := ↥L'` with
`Algebra K ↥L' := RingHom.toAlgebra ((IntermediateField.inclusion h).comp
(AlgHom.equivFieldRange ι)).toRingHom`, `IsScalarTower k K ↥L'` (`IsScalarTower.of_algebraMap_eq`
using `commutes`), and `FiniteDimensional K ↥L'` (`Module.Finite.right k K ↥L'`). -/
theorem exists_level_globalUnit_pthPower (p : ℕ) [Fact p.Prime] (k K : Type) [Field k]
    [NumberField k] [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K]
    [IsGalois k K] (β : Kˣ) :
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra k L) (_ : Algebra K L)
      (_ : IsScalarTower k K L) (_ : FiniteDimensional k L) (_ : IsGalois k L),
      ∃ c : Lˣ, Units.map (algebraMap K L).toMonoidHom β = c ^ p := by
  classical
  -- Put `K` inside `Ω = AlgebraicClosure k`.
  let Ω := AlgebraicClosure k
  haveI hΩ : IsAlgClosed Ω := inferInstance
  haveI hAlg : Algebra.IsAlgebraic k K := Algebra.IsAlgebraic.of_finite k K
  let ι : K →ₐ[k] Ω := IsAlgClosed.lift
  let K' : IntermediateField k Ω := ι.fieldRange
  let e : K ≃ₐ[k] ↥K' := AlgHom.equivFieldRange ι
  haveI hK'fd : FiniteDimensional k ↥K' := e.toLinearEquiv.finiteDimensional
  haveI hK'gal : IsGalois k ↥K' := IsGalois.of_algEquiv e
  haveI hK'nf : NumberField ↥K' :=
    Commons.NumberTheory.NumberField.numberField_of_intermediateField (K := k) (K' := Ω) K'
  -- the trivial scalar tower needed to apply `exists_level_pthRoot` with base field `k`
  haveI hSTΩ : IsScalarTower k k Ω := IsScalarTower.of_algebraMap_eq (fun a => by simp)
  -- the unit of `K'` corresponding to `β`
  let x : K'ˣ := Units.map (e : K →* ↥K') β
  -- enlarge the level so that `x` becomes a `p`-th power
  obtain ⟨L', hL'nf, hL'fd, hL'gal, hle, y, hy⟩ := exists_level_pthRoot p k k Ω K' x
  -- `β` is sent by `e` into `K'` and then by the inclusion into `L'`
  let f : K →ₐ[k] ↥L' := (IntermediateField.inclusion hle).comp e.toAlgHom
  letI : Algebra K ↥L' := f.toRingHom.toAlgebra
  have hcomp : ∀ b : K, (algebraMap K ↥L') b = (IntermediateField.inclusion hle) (e b) :=
    fun _ => rfl
  haveI hST : IsScalarTower k K ↥L' := by
    refine IsScalarTower.of_algebraMap_eq (fun a => ?_)
    rw [hcomp (algebraMap k K a), e.commutes a,
      (IntermediateField.inclusion hle).commutes a]
  refine ⟨↥L', inferInstance, hL'nf, inferInstance, f.toRingHom.toAlgebra, hST, hL'fd, hL'gal,
    y, ?_⟩
  rw [← hy]
  dsimp only [x]
  refine Units.ext ?_
  simp only [Units.coe_map]
  exact hcomp β

end Work.SSGRoute
