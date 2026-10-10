import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.RingTheory.RamificationInertia.Ramification
import Submission.Work.SSGRoute.E7cOmega.ratDivDefs
import Submission.Work.SSGRoute.SSGStage.exists_regularModule_inert_level
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

/-!
# The level input of the unramified detector (`ℚ/ℤ`-coefficient form)

This file isolates the **arithmetic core** of node `C6`
(`Work.SSGRoute.E7cOmega.exists_level_unramified_detecting_class`): the construction of a finite
Galois level `L ⊇ K` together with a `Gal(K/k)`-equivariant additive functional `φ` on
`N = ker (galRes k K L : Gal(L/k) →* Gal(K/k))` which

* `(2a)` vanishes on the inertia subgroup of the chosen place `q'` (so that the resulting class is
  unramified), and
* `(2b)` takes, at the `N`-coordinate of some `d` in the decomposition group of `q'`, a value which
  the given functional `μ : res_{D_w} M ⟶ ℚ/ℤ` does not kill.

Given such a level, the cohomological bookkeeping
(`Work.SSGRoute.E7cOmega.exists_detecting_class_of_coord_functional`) turns `φ` into a class
`h ∈ H¹(Gal(L/k), res M)` which is unramified at `q'` and whose level pairing with `δμ ≠ 0` is
non-zero, whence the node.  Formally the statement below is *not* the node: it mentions no `Ext`
class, no level pairing and no `φ ≠ 0`; it is the arithmetic statement that the level exists.
-/

namespace Work.SSGRoute.E7cOmega

open SSGRoute.PTExt

/-- **The level input of the unramified detector.**  For every non-zero `D_w`-equivariant
`μ : res_{D_w} M ⟶ ℚ/ℤ` there are a finite Galois level `L ⊇ K` over `k`, a place `q' | w` with
`e(q'|q)` prime to `p` and a `Gal(K/k)`-equivariant additive `φ` on `ker (galRes k K L)` with the
properties `(2a)` and `(2b)` above. -/
theorem exists_level_detecting_functional
    (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (M : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Finite M] (hM : ∀ m : M, p • m = 0)
    (w : NK.GlobalCFT.Place K)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hwq : w = NK.GlobalCFT.Place.ofFinite q)
    (hpq : ((p : NumberField.RingOfIntegers K) ∉ q.asIdeal))
    (hI : ∀ σ : K ≃ₐ[k] K, SSGRoute.PTExt.IsInertiaAt q σ → ∀ m : M, M.ρ σ m = m)
    (μ : Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype M ⟶
      Work.SSGRoute.E7cOmega.divRep (SSGRoute.PTExt.decompK (k := k) (K := K) w))
    (hμ : μ ≠ 0) :
    ∃ (L : IntermediateField K Ω) (_ : NumberField ↥L) (_ : FiniteDimensional k ↥L)
      (_ : IsGalois k ↥L)
      (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L))
      (hq' : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q') w),
      Nat.Coprime (q'.asIdeal.ramificationIdx (NumberField.RingOfIntegers K)) p ∧
      ∃ (s : (K ≃ₐ[k] K) →* (↥L ≃ₐ[k] ↥L))
        (hs : ∀ σ : K ≃ₐ[k] K, SSGRoute.PTExt.galRes k K ↥L (s σ) = σ)
        (φ : Additive ((SSGRoute.PTExt.galRes k K ↥L).ker) →+ M.V),
        (∀ (σ : ↥L ≃ₐ[k] ↥L) (g : (SSGRoute.PTExt.galRes k K ↥L).ker),
          φ (Additive.ofMul ⟨σ * (g : ↥L ≃ₐ[k] ↥L) * σ⁻¹,
              Work.SSGRoute.SSGStage.ker_galRes_conj_mem p k K Ω L σ g⟩)
            = M.ρ (SSGRoute.PTExt.galRes k K ↥L σ) (φ (Additive.ofMul g))) ∧
        (∀ γ : ↥L ≃ₐ[k] ↥L, SSGRoute.PTExt.IsInertiaAt q' γ →
          φ (Additive.ofMul (Work.SSGRoute.SSGStage.coordKer k K Ω L s hs γ)) = 0) ∧
        (∃ d : ↥L ≃ₐ[k] ↥L, d ∈ SSGRoute.PTExt.decompK (k := k) (K := ↥L)
            (NK.GlobalCFT.Place.ofFinite q') ∧
          μ.hom (φ (Additive.ofMul (Work.SSGRoute.SSGStage.coordKer k K Ω L s hs d))) ≠ 0) := by
  sorry

end Work.SSGRoute.E7cOmega
