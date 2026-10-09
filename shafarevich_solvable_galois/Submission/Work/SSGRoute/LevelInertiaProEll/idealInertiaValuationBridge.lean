/-
# The inertia condition: ideals versus valuations

For a Galois extension `L/K` of number fields, a prime `P` of `𝓞 L` and `σ : L ≃ₐ[K] L` fixing
`P`, the following two conditions are equivalent:

* `σ x - x ∈ P` for all `x : 𝓞 L` (i.e. `σ` lies in the inertia subgroup, expressed on the
  ring of integers), and
* `v_P (σ y - y) < 1` for all `y` in the valuation ring at `P` (i.e. `σ` acts trivially on the
  maximal ideal of the valuation ring, hence trivially on its residue field).

The mathematical content is that the valuation ring at `P` is the localization of `𝓞 L` at `P`,
so an element of it can be written as `n / d` with `d ∉ P`; reducing `σ(n/d) - n/d` to a common
denominator then shows that the "mod `P`" condition propagates from `𝓞 L` to the localization.
That propagation is proved once and for all in `valuationSubringFixing` (a statement about an
arbitrary Dedekind domain `R` with fraction field `K`); here we only have to translate between
the ideal-theoretic and valuation-theoretic formulations.
-/
import Mathlib
import Submission.Work.SSGRoute.LevelInertiaProEll.Defs
import Submission.Work.SSGRoute.LevelInertiaProEll.valuationSubringFixing
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.LevelInertiaProEll

open scoped Pointwise NumberField algebraMap

theorem idealInertiaValuationBridge {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)) (σ : L ≃ₐ[K] L)
    (hσ : σ • P.asIdeal = P.asIdeal) :
    (∀ x : NumberField.RingOfIntegers L, σ • x - x ∈ P.asIdeal) ↔
      (∀ y : IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime L P,
        (IsDedekindDomain.HeightOneSpectrum.valuation L P) (σ (y : L) - (y : L)) < 1) := by
  -- `hσ` is part of the mathematical context (`σ` lies in the decomposition group of `P`) but
  -- is not needed for the equivalence itself.
  have _hσ := hσ
  -- The elementwise translation of the left-hand condition into a valuation condition.
  have key : ∀ x : NumberField.RingOfIntegers L,
      ((IsDedekindDomain.HeightOneSpectrum.valuation L P) (σ (x : L) - (x : L)) < 1 ↔
        σ • x - x ∈ P.asIdeal) := by
    intro x
    have hmem := IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem (K := L) P (σ • x - x)
    have hcoe : ((σ • x - x : NumberField.RingOfIntegers L) : L) = σ (x : L) - (x : L) := rfl
    rwa [hcoe] at hmem
  constructor
  · -- `σ` fixes `𝓞 L` modulo `P`, hence the valuation ring at `P` modulo its maximal ideal.
    intro h y
    have hy : (y : L) ∈
        (IsDedekindDomain.HeightOneSpectrum.valuation L P).valuationSubring :=
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_le_valuation (K := L) P y.2
    have h0 := valuationSubringFixing (R := NumberField.RingOfIntegers L) (K := L) P
      σ.toRingEquiv (fun x => (key x).mpr (h x)) hy
    simpa using h0
  · -- Conversely, `𝓞 L` sits inside the valuation ring at `P`.
    intro h x
    refine (key x).mp ?_
    have hy : ((algebraMap (NumberField.RingOfIntegers L)
        (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime L P) x : _) : L) =
        (x : L) := rfl
    have h1 := h (algebraMap (NumberField.RingOfIntegers L)
      (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime L P) x)
    rwa [hy] at h1

end Work.SSGRoute.LevelInertiaProEll
