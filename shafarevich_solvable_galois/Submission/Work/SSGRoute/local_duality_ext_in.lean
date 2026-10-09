import Mathlib
import Submission.Work.SSGRoute.local_duality_ext
import Submission.Work.SSGRoute.local_duality_ext_detect_levels
import Submission.Work.SSGRoute.local_duality_ext_detect_h
import Submission.Work.SSGRoute.local_duality_ext_realization_of_detection
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory

/-! ## Finite duality for `ZMod p`-bilinear pairings

The realisation clause (ii) of E7b is the "detection implies realisation" direction of the finite
duality of `𝔽_p`-vector spaces: if a `ZMod p`-bilinear form `B : V →ₗ W →ₗ ZMod p` detects every
nonzero `w ∈ W`, then `B` is onto the dual of `W`.  This is
`LinearMap.flip_injective_iff₂` (`Injective B.flip ↔ Surjective B`, requiring only that `W` be
finite-dimensional). -/

/-- **Detection implies realisation.** -/
theorem surjective_of_flip_injective {p : ℕ} [Fact p.Prime] {V W : Type*}
    [AddCommGroup V] [Module (ZMod p) V]
    [AddCommGroup W] [Module (ZMod p) W] [FiniteDimensional (ZMod p) W]
    (B : V →ₗ[ZMod p] W →ₗ[ZMod p] ZMod p)
    (h : Function.Injective B.flip) : Function.Surjective B :=
  LinearMap.flip_injective_iff₂.mp h

/-- The `forall`-form of the hypothesis of `surjective_of_flip_injective`. -/
theorem flip_injective_of_detection {p : ℕ} [Fact p.Prime] {V W : Type*}
    [AddCommGroup V] [Module (ZMod p) V]
    [AddCommGroup W] [Module (ZMod p) W]
    (B : V →ₗ[ZMod p] W →ₗ[ZMod p] ZMod p)
    (h : ∀ w : W, w ≠ 0 → ∃ v : V, B v w ≠ 0) : Function.Injective B.flip := by
  intro w w' hww'
  by_contra hne
  obtain ⟨v, hv⟩ := h (w - w') (sub_ne_zero.mpr hne)
  have hww'v : B v w = B v w' := by
    have h := congrArg (fun (φ : V →ₗ[ZMod p] ZMod p) => φ v) hww'
    simpa only [LinearMap.flip_apply] using h
  exact hv (by rw [map_sub, hww'v, sub_self])

/-! ## E7b

The theorem is the conjunction of the two clauses: clause (i) is the detection over *all* levels
(`Work.SSGRoute.local_duality_ext_detect_levels`), clause (ii) is the detection at the *given*
level (`Work.SSGRoute.local_duality_ext_detect_h`) turned into the realisation of every functional
by the finite duality `Work.SSGRoute.local_duality_ext_realization_of_detection`. -/

/-- **E7b (fresh attempt): canonical local duality at a place `w` of `K`, in `Ext` form.**

`μ_p ⊆ K`, `M` finite `p`-torsion. The Yoneda pairing of `Ext¹_{D_w}(M, K_wˣ)` with
`H¹(D_{w'}, M)` into `H²(D_{w'}, L_{w'}ˣ)` (`D_{w'} =` decomposition group of `w'`, `w' | w`):
(i) has no left kernel over all levels `L ⊇ K` and places `w' | w`; (ii) at a level with
`p ∣ |D_{w'}|`, realises every `p`-torsion functional.  All the `Ext`-algebra used below
(`levelPair_pushClass`, `levelPair_pushClass_bridge`, `pushClass_surjective`,
`levelPair_trivial_eq_zero_iff_norm`, `levelPair_trivial_eq_zero_iff_normB`) is already proved
in `Submission/Work/SSGRoute/local_duality_ext.lean`; the remaining content is the
arithmetic input (the perfectness of the local Kummer pairing, i.e. clause (i) detection and
clause (ii) realisation) plus the local-global existence of levels. -/
theorem local_duality_ext_in (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
    [FiniteDimensional k K] [IsGalois k K]
    (ζ : K) (hζ : IsPrimitiveRoot ζ p)
    (M : Rep Coeff (K ≃ₐ[k] K)) [Finite M] (hM : ∀ m : M, p • m = 0)
    (w : NK.GlobalCFT.Place K) :
    (∀ y : Abelian.Ext (Rep.res (decompK (k := k) w).subtype M) (localUnitsK (k := k) w) 1,
      (∀ (L : Type) [Field L] [NumberField L] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
        [FiniteDimensional k L] [IsGalois k L]
        (w' : NK.GlobalCFT.Place L) (hw' : NK.GlobalCFT.Place.LiesOver w' w)
        (f : MulAction.stabilizer (L ≃ₐ[k] L) w' →* decompK (k := k) w)
        (hf : ∀ σ, ((f σ : decompK (k := k) w) : K ≃ₐ[k] K) = galRes k K L (σ : L ≃ₐ[k] L))
        (ι : Rep.res f (localUnitsK (k := k) w) ⟶ NK.HassePrinciple.localUnitsRep k L w')
        (hι : ∀ u : (NK.GlobalCFT.Place.localField K w)ˣ,
          ι.hom (Additive.ofMul u) =
            Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits w' w hw' u))
        (h : extH (Rep.res f (Rep.res (decompK (k := k) w).subtype M)) 1),
        levelPair f ι y h = 0) → y = 0) ∧
    ∀ (L : Type) [Field L] [NumberField L] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
      [FiniteDimensional k L] [IsGalois k L]
      (w' : NK.GlobalCFT.Place L) (hw' : NK.GlobalCFT.Place.LiesOver w' w)
      (f : MulAction.stabilizer (L ≃ₐ[k] L) w' →* decompK (k := k) w)
      (hf : ∀ σ, ((f σ : decompK (k := k) w) : K ≃ₐ[k] K) = galRes k K L (σ : L ≃ₐ[k] L))
      (ι : Rep.res f (localUnitsK (k := k) w) ⟶ NK.HassePrinciple.localUnitsRep k L w')
      (hι : ∀ u : (NK.GlobalCFT.Place.localField K w)ˣ,
        ι.hom (Additive.ofMul u) =
          Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits w' w hw' u)),
      p ∣ Nat.card (MulAction.stabilizer (L ≃ₐ[k] L) w') →
      ∀ lam : extH (Rep.res f (Rep.res (decompK (k := k) w).subtype M)) 1 →+
          extH (NK.HassePrinciple.localUnitsRep k L w') 2,
        (∀ h, p • lam h = 0) →
        ∃ y : Abelian.Ext (Rep.res (decompK (k := k) w).subtype M) (localUnitsK (k := k) w) 1,
          ∀ h, levelPair f ι y h = lam h := by
  refine ⟨local_duality_ext_detect_levels p k K ζ hζ M hM w, ?_⟩
  intro L _ _ _ _ _ _ _ w' hw' f hf ι hι hp lam hlam
  exact local_duality_ext_realization_of_detection p k K M hM w L w' hw' f hf ι hι hp
    (fun h hne => local_duality_ext_detect_h p k K ζ hζ M hM w L w' hw' f hf ι hι hp h hne)
    lam hlam

end Work.SSGRoute
