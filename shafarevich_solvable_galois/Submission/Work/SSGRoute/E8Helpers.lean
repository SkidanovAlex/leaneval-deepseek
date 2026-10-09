/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Helper lemmas for `Work.SSGRoute.brauer_single_place` (E8')

The stabiliser/decomposition-group bridges that the E8' development (and its delegated pieces)
share.  Everything here is sorry-free.
-/
import Mathlib
import Submission.Work.SSGRoute.E8Defs
import Submission.NK.HassePrinciple.LocalUnits
import Submission.NK.GlobalCFT.GaloisAction
import Submission.NK.GlobalCFT.Inclusion.globalCFT_localAction
import Submission.Commons.NumberTheory.NumberField.Completion.decompositionSubgroupMulEquivLocalGalois_coe
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Work.SSGRoute

open CategoryTheory NumberField

/-! ## The relative decomposition group at a finite place -/

/-- **The stabiliser of a finite place is its decomposition group** (in the sense of
`Commons.NumberTheory.NumberField.Completion.decompositionSubgroup`), for `k ⊆ K ⊆ E`. -/
theorem eb_stab_eq_decomp (k K E : Type) [Field k] [NumberField k] [Field K] [NumberField K]
    [Field E] [NumberField E] [Algebra k K] [Algebra k E] [Algebra K E] [IsScalarTower k K E]
    [FiniteDimensional k K] [FiniteDimensional K E] [FiniteDimensional k E]
    [IsGalois k K] [IsGalois k E] [IsGalois K E]
    (ŵ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)) :
    EB_StabEqDecomp k K E ŵ := by
  unfold EB_StabEqDecomp
  ext σ
  rw [MulAction.mem_stabilizer_iff,
    NK.GlobalCFT.Inclusion.globalCFT_mem_decompositionSubgroup_iff,
    NK.GlobalCFT.Place.smul_ofFinite, NK.GlobalCFT.Place.ofFinite_inj]

/-- **The relative decomposition group has the local degree as its cardinality.**

For `k ⊆ K ⊆ E` finite Galois extensions of number fields and places `ŵ | W` of `E | K`, the
stabiliser of `ŵ` in `Gal(E/K)` has cardinality the local degree `[E_ŵ : K_W]`. -/
theorem eb_stab_card (k K E : Type) [Field k] [NumberField k] [Field K] [NumberField K]
    [Field E] [NumberField E] [Algebra k K] [Algebra k E] [Algebra K E] [IsScalarTower k K E]
    [FiniteDimensional k K] [FiniteDimensional K E] [FiniteDimensional k E]
    [IsGalois k K] [IsGalois k E] [IsGalois K E]
    (W : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (ŵ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E))
    (hW : ŵ.asIdeal.LiesOver W.asIdeal) :
    letI : Algebra (W.adicCompletion K) (ŵ.adicCompletion E) :=
      Commons.NumberTheory.NumberField.Completion.adicCompletionAlgebra W ŵ hW
    Nat.card (MulAction.stabilizer (E ≃ₐ[K] E) (NK.GlobalCFT.Place.ofFinite ŵ)) =
      Module.finrank (W.adicCompletion K) (ŵ.adicCompletion E) := by
  letI : Algebra (W.adicCompletion K) (ŵ.adicCompletion E) :=
    Commons.NumberTheory.NumberField.Completion.adicCompletionAlgebra W ŵ hW
  haveI hfd : FiniteDimensional (W.adicCompletion K) (ŵ.adicCompletion E) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion W ŵ hW
  haveI hgal : IsGalois (W.adicCompletion K) (ŵ.adicCompletion E) :=
    Commons.NumberTheory.NumberField.Completion.isGalois_adicCompletion W ŵ hW
  rw [show (MulAction.stabilizer (E ≃ₐ[K] E) (NK.GlobalCFT.Place.ofFinite ŵ))
      = Commons.NumberTheory.NumberField.Completion.decompositionSubgroup (K := K) ŵ
      from eb_stab_eq_decomp k K E ŵ]
  rw [Nat.card_congr (Commons.NumberTheory.NumberField.Completion.decompositionSubgroupMulEquivLocalGalois
      (K := K) (L := E) W ŵ hW).toEquiv]
  exact IsGalois.card_aut_eq_finrank (W.adicCompletion K) (ŵ.adicCompletion E)

/-! ## The stabiliser inclusion and the localisation functoriality -/

/-- **The inclusion of stabilisers `Stab_{Gal(E/M)}(ŵ) →* Stab_{Gal(E/k)}(ŵ)`** for `k ⊆ M`,
induced by the restriction of scalars `E ≃ₐ[M] E → E ≃ₐ[k] E`. -/
noncomputable def stabIncl {k M E : Type} [Field k] [NumberField k] [Field M] [NumberField M]
    [Field E] [NumberField E] [Algebra k M] [Algebra k E] [Algebra M E] [IsScalarTower k M E]
    (ŵ : NK.GlobalCFT.Place E) :
    MulAction.stabilizer (E ≃ₐ[M] E) ŵ →* MulAction.stabilizer (E ≃ₐ[k] E) ŵ where
  toFun σ := ⟨AlgEquiv.restrictScalars k σ.1, by
    rw [MulAction.mem_stabilizer_iff]
    show (AlgEquiv.restrictScalars k σ.1) • ŵ = ŵ
    rw [show (AlgEquiv.restrictScalars k σ.1) • ŵ = σ.1 • ŵ from rfl]
    exact σ.2⟩
  map_one' := Subtype.ext rfl
  map_mul' σ τ := Subtype.ext rfl

/-- **The local automorphism attached to a stabilised place depends only on the underlying global
automorphism**: the two `localAutHom`s at the levels `k` and `M` agree on a stabiliser element and
its image under `stabIncl`. -/
theorem localAutHom_stabIncl {k M E : Type} [Field k] [NumberField k] [Field M] [NumberField M]
    [Field E] [NumberField E] [Algebra k M] [Algebra k E] [Algebra M E] [IsScalarTower k M E]
    (ŵ : NK.GlobalCFT.Place E) (σ : MulAction.stabilizer (E ≃ₐ[M] E) ŵ) :
    NK.HassePrinciple.localAutHom (K := k) ŵ (stabIncl (k := k) (M := M) ŵ σ) =
      NK.HassePrinciple.localAutHom (K := M) ŵ σ := by
  refine NK.HassePrinciple.localRingEquiv_ext_of_algebraMap
    (NK.HassePrinciple.localAut_continuous ŵ (stabIncl (k := k) (M := M) ŵ σ))
    (NK.HassePrinciple.localAut_continuous ŵ σ) (fun x => ?_)
  change NK.HassePrinciple.localAut ŵ (stabIncl (k := k) (M := M) ŵ σ)
      (algebraMap E (NK.GlobalCFT.Place.localField E ŵ) x) =
    NK.HassePrinciple.localAut ŵ σ (algebraMap E (NK.GlobalCFT.Place.localField E ŵ) x)
  rw [NK.HassePrinciple.localAut_algebraMap, NK.HassePrinciple.localAut_algebraMap]
  rfl

/-- **The local units representation of the lower level is the restriction of scalars of the
representation of the upper level along `stabIncl`** (definitionally). -/
theorem res_stabIncl_localUnitsRep_eq {k M E : Type} [Field k] [NumberField k] [Field M]
    [NumberField M] [Field E] [NumberField E] [Algebra k M] [Algebra k E] [Algebra M E]
    [IsScalarTower k M E] [FiniteDimensional k E] [FiniteDimensional M E] [IsGalois k E]
    [IsGalois M E] (ŵ : NK.GlobalCFT.Place E) :
    Rep.res (stabIncl (k := k) (M := M) ŵ) (NK.HassePrinciple.localUnitsRep k E ŵ) =
      NK.HassePrinciple.localUnitsRep M E ŵ :=
  rfl

/-! ## The Galois orbit of a place -/

/-- The places of `L` outside the `Gal(L/k)`-orbit of `w₀` are exactly the places of `L` not lying
over the place of `k` below `w₀`. -/
theorem not_liesOver_iff_not_mem_orbit (k L : Type) [Field k] [NumberField k] [Field L]
    [NumberField L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (w₀ : NK.GlobalCFT.Place L) (v₀ : NK.GlobalCFT.Place k)
    (hv₀ : NK.GlobalCFT.Place.LiesOver w₀ v₀) (w : NK.GlobalCFT.Place L) :
    (∀ σ : L ≃ₐ[k] L, σ • w₀ ≠ w) ↔ ¬ NK.GlobalCFT.Place.LiesOver w v₀ := by
  constructor
  · intro h hlies
    obtain ⟨σ, hσ⟩ :=
      NK.GlobalCFT.Inclusion.globalCFT_exists_smul_eq_of_liesOver hv₀ hlies
    exact h σ hσ
  · intro h σ hσ
    exact h (hσ ▸ ((NK.GlobalCFT.Place.liesOver_smul_iff (σ := σ)).mpr hv₀))

end Work.SSGRoute
