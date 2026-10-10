import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.RamificationInertia.Ramification
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Submission.Work.SSGRoute.PTdualControl.C6_rankOneBrick
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `LevelCocycleDatum` constructor, with its components named

`PTdualControl.LevelCocycleDatum` carries its level existentially.  This file unpacks it into a
constructor, so that the two remaining tasks of C6's non-invariant case can be stated — and handed
out — *separately*:

* **unramifiedness** (`p ∤ e(q'|q)`, spelled `Nat.Coprime (q.asIdeal.ramificationIdx' q'.asIdeal) p`):
  produce `hcop`, from the concentrated Kummer radical (`Sha2Lib.equivariantKummerRadical`, frozen;
  its clauses 2–3 are the concentration off the N-orbit of `q` and the prescribed nontrivial class of
  a unit), and
* **conjugation-separation**: produce the cocycle `z` together with `hz` (inertia-vanishing) and `hd`
  (a detecting `d ∈ D_{q'}` with `μ ∘ z ≠ 0`) for non-invariant `μ` — the exact complement of the
  *proved* invariant case (`PTdualControl.C6_rankOneBrick_invariantCase`,
  `Sha2Lib.detectorInvariantCaseExtZ`).

The theorem below has no mathematical content (it is the definition's anonymous-constructor
elimination, one line); its value is interface: the callers that *produce* `hcop` and `z, hz, hd` are
now separately statable.  The real work stays in `Sha2Lib.rankOneLevelDatumExists` /
`rankOne_functionalDetection`.
-/

namespace Work.SSGRoute.Sha2Lib

open CategoryTheory SSGRoute.PTExt

/-- **Constructor for `LevelCocycleDatum`** (`μ_p ⊆ K` setting), with the level and the four
components named. -/
theorem levelCocycleDatum_of_components (p : ℕ) [Fact p.Prime] (k K : Type) [Field k]
    [NumberField k] [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (w : NK.GlobalCFT.Place K)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hwq : w = NK.GlobalCFT.Place.ofFinite q)
    (M : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K))
    (μ : Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype M ⟶
      Work.SSGRoute.E7cOmega.divRep (SSGRoute.PTExt.decompK (k := k) (K := K) w))
    (L : IntermediateField K Ω) [NumberField ↥L] [FiniteDimensional k ↥L] [IsGalois k ↥L]
    (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L))
    (hq' : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q') w)
    (hcop : Nat.Coprime (q.asIdeal.ramificationIdx' q'.asIdeal) p)
    (z : ↥(groupCohomology.cocycles₁ (Rep.res (SSGRoute.PTExt.galRes k K ↥L) M)))
    (hz : ∀ γ : ↥L ≃ₐ[k] ↥L, SSGRoute.PTExt.IsInertiaAt q' γ →
      (z : (↥L ≃ₐ[k] ↥L) → M.V) γ = 0)
    (hd : ∃ d : ↥L ≃ₐ[k] ↥L, d ∈ SSGRoute.PTExt.decompK (k := k) (K := ↥L)
        (NK.GlobalCFT.Place.ofFinite q') ∧ μ.hom ((z : (↥L ≃ₐ[k] ↥L) → M.V) d) ≠ 0) :
    Work.SSGRoute.PTdualControl.LevelCocycleDatum p k K Ω w q hwq M μ :=
  ⟨L, inferInstance, inferInstance, inferInstance, q', hq', hcop, z, hz, hd⟩

end Work.SSGRoute.Sha2Lib
