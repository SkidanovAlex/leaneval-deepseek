import Mathlib
import Submission.Work.SSGRoute.ZDataMup.CycleDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Existence of the base change of a cycle

Given a cycle `c` for a number field `K` and a finite Galois extension `L/K`, we construct a
cycle `cL` for `L` whose support is exactly the set of primes of `L` lying above the primes of
`c`.  Concretely the support is the finite union, over the primes `𝔭 ∈ c.supp`, of the (finite)
set of primes `𝔮` of `L` with `𝔮 ∣ 𝔭`; finiteness of the individual fibres is
`Ideal.finite_factors` applied to the ideal `𝔭 · 𝓞 L`, since every `𝔮` above `𝔭` divides
`𝔭 · 𝓞 L`.

The exponents are irrelevant for `Cycle.IsBaseChange`, so they are all taken to be `1`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped NumberField nonZeroDivisors
open NumberField IsDedekindDomain

noncomputable section

namespace Work.SSGRoute.ZDataMup

/-- If a prime `𝔮` of `𝓞 L` lies over a prime `𝔭` of `𝓞 K`, then `𝔮` divides the extension
ideal `𝔭 · 𝓞 L`: indeed `𝔭 = 𝔮 ∩ 𝓞 K`, so `𝔭 · 𝓞 L ⊆ 𝔮`. -/
theorem liesOver_map_le {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] (𝔭 : HeightOneSpectrum (𝓞 K))
    (𝔮 : HeightOneSpectrum (𝓞 L)) (h : 𝔮.asIdeal.LiesOver 𝔭.asIdeal) :
    Ideal.map (algebraMap (𝓞 K) (𝓞 L)) 𝔭.asIdeal ≤ 𝔮.asIdeal := by
  have := h
  rw [Ideal.map_le_iff_le_comap]
  exact le_of_eq (Ideal.over_def 𝔮.asIdeal 𝔭.asIdeal)

/-- The primes of `𝓞 L` lying above a fixed prime `𝔭` of `𝓞 K` form a finite set. -/
theorem finite_setOf_liesOver {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] (𝔭 : HeightOneSpectrum (𝓞 K)) :
    {𝔮 : HeightOneSpectrum (𝓞 L) | 𝔮.asIdeal.LiesOver 𝔭.asIdeal}.Finite := by
  have hI : 𝔭.asIdeal.map (algebraMap (𝓞 K) (𝓞 L)) ≠ 0 :=
    Ideal.map_ne_bot_of_ne_bot 𝔭.ne_bot
  refine (Ideal.finite_factors hI).subset ?_
  intro 𝔮 h𝔮
  exact Ideal.dvd_iff_le.mpr (liesOver_map_le 𝔭 𝔮 h𝔮)

/-- The set of primes of `𝓞 L` lying above some prime of the support of a cycle `c` is finite. -/
theorem finite_liesOver_union {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] (c : Cycle K) :
    (⋃ 𝔭 ∈ (c.supp : Set (HeightOneSpectrum (𝓞 K))),
      {𝔮 : HeightOneSpectrum (𝓞 L) | 𝔮.asIdeal.LiesOver 𝔭.asIdeal}).Finite :=
  c.supp.finite_toSet.biUnion (fun 𝔭 _ => finite_setOf_liesOver 𝔭)

/-- **Base change of a cycle along a finite extension `L/K`**: the support of `cL` is the set of
primes of `L` above the primes of `c.lev`.  The levels are set to `1`, since
`Cycle.IsBaseChange` only constrains the support. -/
theorem CycleBaseChangeExists
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] (c : Work.SSGRoute.ZDataMup.Cycle K) :
    ∃ cL : Work.SSGRoute.ZDataMup.Cycle L, Work.SSGRoute.ZDataMup.Cycle.IsBaseChange K L c cL := by
  let S : Set (HeightOneSpectrum (𝓞 L)) :=
    ⋃ 𝔭 ∈ (c.supp : Set (HeightOneSpectrum (𝓞 K))),
      {𝔮 : HeightOneSpectrum (𝓞 L) | 𝔮.asIdeal.LiesOver 𝔭.asIdeal}
  have hS : S.Finite := finite_liesOver_union c
  refine ⟨⟨hS.toFinset, fun _ => 1⟩, ?_⟩
  intro 𝔮
  change 𝔮 ∈ hS.toFinset ↔ ∃ 𝔭 ∈ c.supp, 𝔮.asIdeal.LiesOver 𝔭.asIdeal
  rw [Set.Finite.mem_toFinset]
  simp only [S, Set.mem_iUnion, Finset.mem_coe]
  exact ⟨fun ⟨i, hi, h⟩ => ⟨i, hi, h⟩, fun ⟨i, hi, h⟩ => ⟨i, hi, h⟩⟩

end Work.SSGRoute.ZDataMup
