import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Submission.NK.RankTheoryDeep.PlacesOverEll
import Submission.NK.RankTheoryDeep.dual_pi_surjective_finite_coordinates
import Submission.NK.RankTheoryDeep.rank_dual_integralIdeles_le_pi
import Submission.NK.RankTheoryDeep.rank_pi_le_sum
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The assembly over the idèle class group: `rank Hom_cts(∏_v 𝒪_vˣ, ℤ_ℓ) ≤ [K : ℚ]`

The chain of inequalities proved here is

```
Dual (∏_v 𝒪_vˣ)              ↪  Dual (∏_{v : Place K} 𝒪_vˣ)                 [integral idèles = full product]
Dual (∏_{v : Place K} 𝒪_vˣ)  =  ⨁_{v | ℓ} Dual (𝒪_vˣ)                      [finite support; v ∤ ℓ and v | ∞
                                                                             contribute nothing]
rank ⨁_{v | ℓ} Dual (𝒪_vˣ)   ≤  ∑_{v | ℓ} e_v f_v = [K : ℚ]                  [local unit structure,
                                                                             fundamental identity]
```

The only input is the classical **local unit structure** at the places above `ℓ`
(`NK.RankTheoryDeep.LocalUnitDualRankInput`).  Everything else is proved here.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped NumberField

namespace NK.RankTheoryDeep

universe u

/-- **The assembly: the character module of the integral idèles has rank at most `[K : ℚ]`.**
Given the local unit structure at the places above `ℓ`, the `ℤ_ℓ`-rank of
`Hom_cts(∏_v 𝒪_vˣ, ℤ_ℓ)` is at most the number of `ℓ`-adic places weighted by their local degrees,
i.e. at most `[K : ℚ]`. -/
theorem rank_dual_integralIdeles_le (K : Type u) [Field K] [NumberField K] {ℓ : ℕ}
    [Fact ℓ.Prime] (hloc : LocalUnitDualRankInput.{u} ℓ) :
    Module.rank (PadicInt ℓ)
        (NK.Reconstruct.Dual (↥(NK.GlobalCFT.Idele.integralIdeles K)) ℓ)
      ≤ (Module.finrank ℚ K : Cardinal) := by
  classical
  -- the surjectivity which turns the product into a finite sum
  have hS : ∀ v : NK.GlobalCFT.Place K, v ∉ placesOverEll K ℓ →
      Subsingleton (NK.Reconstruct.Dual
        (↥(NK.GlobalCFT.Place.localUnits K v)) ℓ) :=
    fun v hv => subsingleton_dual_localUnits_of_not_mem_placesOverEll K v hv
  have hsurj := dual_pi_surjective_finite_coordinates (S := placesOverEll K ℓ)
    (A := fun v => ↥(NK.GlobalCFT.Place.localUnits K v)) hS
  -- the transpose (restriction) map, as a linear map
  let Φ : ((v : {v // v ∈ placesOverEll K ℓ}) →
        NK.Reconstruct.Dual (↥(NK.GlobalCFT.Place.localUnits K v)) ℓ) →ₗ[PadicInt ℓ]
      NK.Reconstruct.Dual
        (∀ v : NK.GlobalCFT.Place K, ↥(NK.GlobalCFT.Place.localUnits K v)) ℓ :=
    { toFun := fun ψ => ∑ v : {v // v ∈ placesOverEll K ℓ},
        (NK.Reconstruct.dualMap ℓ (Pi.evalMonoidHom _ (v : NK.GlobalCFT.Place K))
          (continuous_apply (v : NK.GlobalCFT.Place K)) (ψ v) :
            NK.Reconstruct.Dual
              (∀ v : NK.GlobalCFT.Place K, ↥(NK.GlobalCFT.Place.localUnits K v)) ℓ)
      map_add' := by
        intro x y
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun v _ => ?_
        simp only [Pi.add_apply]
        exact NK.Reconstruct.dualMap_add ℓ _ _ (x v) (y v)
      map_smul' := by
        intro a x
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun v _ => ?_
        exact dualMap_smul _ _ a (x v) }
  have hΦ : Function.Surjective Φ := hsurj
  -- the reindexing of the sum over the places above `ℓ`
  have hreindex : (∑ v ∈ placesOverEll K ℓ,
        Module.rank (PadicInt ℓ)
          (NK.Reconstruct.Dual (↥(NK.GlobalCFT.Place.localUnits K v)) ℓ))
      = ∑ q : ↥((Ideal.span {(ℓ : ℤ)}).primesOver (NumberField.RingOfIntegers K)),
          Module.rank (PadicInt ℓ) (NK.Reconstruct.Dual
            (↥(NK.GlobalCFT.Place.localUnits K
              (NK.GlobalCFT.Place.ofFinite (primeOfOver K q)))) ℓ) := by
    rw [placesOverEll, Finset.sum_image]
    intro a _ b _ hab
    refine Subtype.ext ?_
    exact congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal
      (NK.GlobalCFT.Place.ofFinite_inj.mp hab)
  -- the local bound, summed
  have hlocal : (∑ q : ↥((Ideal.span {(ℓ : ℤ)}).primesOver (NumberField.RingOfIntegers K)),
        Module.rank (PadicInt ℓ) (NK.Reconstruct.Dual
          (↥(NK.GlobalCFT.Place.localUnits K
            (NK.GlobalCFT.Place.ofFinite (primeOfOver K q)))) ℓ))
      ≤ (Module.finrank ℚ K : Cardinal) := by
    have hstep : ∀ q : ↥((Ideal.span {(ℓ : ℤ)}).primesOver (NumberField.RingOfIntegers K)),
        Module.rank (PadicInt ℓ) (NK.Reconstruct.Dual
          (↥(NK.GlobalCFT.Place.localUnits K
            (NK.GlobalCFT.Place.ofFinite (primeOfOver K q)))) ℓ)
          ≤ (((primeOfOver K q).asIdeal.ramificationIdx ℤ
              * (primeOfOver K q).asIdeal.inertiaDeg ℤ : ℕ) : Cardinal) :=
      fun q => by
        simpa only [dualRank, Nat.cast_mul] using hloc K (primeOfOver K q) q.2.2
    calc (∑ q : ↥((Ideal.span {(ℓ : ℤ)}).primesOver (NumberField.RingOfIntegers K)),
            Module.rank (PadicInt ℓ) (NK.Reconstruct.Dual
              (↥(NK.GlobalCFT.Place.localUnits K
                (NK.GlobalCFT.Place.ofFinite (primeOfOver K q)))) ℓ))
        ≤ ∑ q : ↥((Ideal.span {(ℓ : ℤ)}).primesOver (NumberField.RingOfIntegers K)),
            (((primeOfOver K q).asIdeal.ramificationIdx ℤ
              * (primeOfOver K q).asIdeal.inertiaDeg ℤ : ℕ) : Cardinal) :=
          Finset.sum_le_sum fun q _ => hstep q
      _ = ((∑ q : ↥((Ideal.span {(ℓ : ℤ)}).primesOver (NumberField.RingOfIntegers K)),
              (primeOfOver K q).asIdeal.ramificationIdx ℤ
              * (primeOfOver K q).asIdeal.inertiaDeg ℤ : ℕ) : Cardinal) := by
          rw [Nat.cast_sum]
      _ = ((Module.finrank ℚ K : ℕ) : Cardinal) := by
          rw [show (∑ q : ↥((Ideal.span {(ℓ : ℤ)}).primesOver (NumberField.RingOfIntegers K)),
                  (primeOfOver K q).asIdeal.ramificationIdx ℤ
                * (primeOfOver K q).asIdeal.inertiaDeg ℤ)
              = ∑ q : ↥((Ideal.span {(ℓ : ℤ)}).primesOver (NumberField.RingOfIntegers K)),
                  (q : Ideal (NumberField.RingOfIntegers K)).ramificationIdx ℤ
                    * (q : Ideal (NumberField.RingOfIntegers K)).inertiaDeg ℤ from rfl,
            sum_localDeg_eq_finrank K]
  calc Module.rank (PadicInt ℓ)
        (NK.Reconstruct.Dual (↥(NK.GlobalCFT.Idele.integralIdeles K)) ℓ)
      ≤ Module.rank (PadicInt ℓ) (NK.Reconstruct.Dual
          (∀ v : NK.GlobalCFT.Place K, ↥(NK.GlobalCFT.Place.localUnits K v)) ℓ) :=
        rank_dual_integralIdeles_le_pi K
    _ ≤ Module.rank (PadicInt ℓ) ((v : {v // v ∈ placesOverEll K ℓ}) →
          NK.Reconstruct.Dual (↥(NK.GlobalCFT.Place.localUnits K v)) ℓ) :=
        LinearMap.rank_le_of_surjective Φ hΦ
    _ ≤ ∑ v ∈ placesOverEll K ℓ, Module.rank (PadicInt ℓ)
          (NK.Reconstruct.Dual (↥(NK.GlobalCFT.Place.localUnits K v)) ℓ) :=
        rank_pi_le_sum (placesOverEll K ℓ)
          (fun v => NK.Reconstruct.Dual (↥(NK.GlobalCFT.Place.localUnits K v)) ℓ)
    _ = _ := hreindex
    _ ≤ (Module.finrank ℚ K : Cardinal) := hlocal

end NK.RankTheoryDeep
