import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.PT.vf_aux
import Submission.Work.SSGRoute.PT.vf_local_compare
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PT.G1plusOwn

/-- **Two elements of `S'` with conjugate `finQW`-places are equal.**

`S'` is a finite set of finite places of `Ω` no two of which are `Gal(Ω/k)`-conjugate
(`hS'disj`).  If the places of `L` obtained by restricting two of its elements differ by an element
`σ` of `Gal(L/k)`, then the two elements of `Ω` are equal.

This gives (a) the *injectivity* of `A ↦ ofFinite (finQW L A hA)` on `S'` (take `σ = 1`), which is
what allows the sum `∑ A ∈ S', …` of clause (7) to be reindexed as a sum over the Finset of
`L`-places, and (b) the *pairwise non-conjugacy* of that Finset, which is the `hW` hypothesis of
`Work.SSGRoute.PT.G1plusOwn.sum_iota_eq_zero_of_extToClasses_zero`.

Proof.  Lift `σ` to `τ : Ω ≃ₐ[k] Ω` (`AlgEquiv.restrictNormalHom_surjective`; cf.
`Work.SSGRoute.PT.exists_restrictNormal_eq_of_isAlgClosure`), so that
`τ.restrictNormal L = σ`.  Then `Work.SSGRoute.PT.ofFinite_finQW_smul` gives
`ofFinite (finQW L (τ • A) hA') = σ • ofFinite (finQW L A hA) = ofFinite (finQW L B hB)`; comparing
primes (`NK.GlobalCFT.Place.ofFinite_inj`) and passing to the traces
(`Work.SSGRoute.PT.finQW_comap`) gives equal `comap`s of `τ • A` and `B` on `↥L`, whence
`Work.SSGRoute.PT.exists_smul_eq_of_comap_eq_of_isAlgClosure` produces `ρ : Ω ≃ₐ[↥L] Ω` with
`ρ • (τ • A) = B`, i.e. `IsConjPlace k A B` by
`Work.SSGRoute.PT.isConjPlace_of_smul_smul`; then `hS'disj` gives `A = B`.  The extra obligation
`IsFinPlace k (τ • A)` is `Work.SSGRoute.isFinPlace_smul_iff`.-/
theorem isConjPlace_of_finQW_conj {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (L : IntermediateField k Ω) [FiniteDimensional k L] [IsGalois k L]
    [NumberField ↥L]
    (S' : Finset (ValuationSubring Ω)) (hS'fin : ∀ A ∈ S', SSGRoute.IsFinPlace k A)
    (hS'disj : ∀ A ∈ S', ∀ B ∈ S', SSGRoute.IsConjPlace k A B → A = B)
    (σ : ↥L ≃ₐ[k] ↥L) {A B : ValuationSubring Ω} (hA : A ∈ S') (hB : B ∈ S')
    (h : σ • NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW L A (hS'fin A hA)) =
      NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW L B (hS'fin B hB))) :
    A = B := by
  obtain ⟨τ, hτ⟩ := Work.SSGRoute.PT.exists_restrictNormal_eq_of_isAlgClosure L σ
  have hA' : SSGRoute.IsFinPlace k (τ • A) :=
    (Work.SSGRoute.isFinPlace_smul_iff A τ).mpr (hS'fin A hA)
  have h1 : NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW L (τ • A) hA') =
      NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW L B (hS'fin B hB)) := by
    rw [Work.SSGRoute.PT.ofFinite_finQW_smul L A (hS'fin A hA) τ hA', hτ]
    exact h
  have hq : Work.SSGRoute.PT.finQW L (τ • A) hA' = Work.SSGRoute.PT.finQW L B (hS'fin B hB) :=
    NK.GlobalCFT.Place.ofFinite_inj.mp h1
  have hcomap : (τ • A).comap (algebraMap ↥L Ω) = B.comap (algebraMap ↥L Ω) := by
    rw [Work.SSGRoute.PT.finQW_comap L (τ • A) hA',
      Work.SSGRoute.PT.finQW_comap L B (hS'fin B hB), hq]
  obtain ⟨ρ, hρ⟩ :=
    Work.SSGRoute.PT.exists_smul_eq_of_comap_eq_of_isAlgClosure L (τ • A) B hcomap
  exact hS'disj A hA B hB
    (Work.SSGRoute.PT.isConjPlace_of_smul_smul L (A := A) (B := B) τ ρ hρ)

end Work.SSGRoute.PT.G1plusOwn
