import Mathlib
import Submission.Work.SSGRoute.PTDefsOmega
import Submission.Work.SSGRoute.phi1_lambda_defs
import Submission.Work.SSGRoute.phi1_level_index
import Submission.Work.SSGRoute.phi1_level_system
import Submission.Work.SSGRoute.phi1_level_limit
import Submission.Work.SSGRoute.phi1_class_level
import Submission.Work.SSGRoute.phi1_lambda_compat
import Submission.Work.SSGRoute.phi1_level_trivial_two
import Submission.Work.SSGRoute.addHom_extend_of_exponent
import Submission.Work.SSGRoute.pt_char_pTorsion
import Submission.Work.SSGRoute.E4R3.inflC_injective
import Submission.Work.SSGRoute.phi1_wcolim
import Submission.Work.SSGRoute.phi1_glue
import Submission.Work.SSGRoute.phi0_realization_in
import Submission.Work.SSGRoute.LF.Conj
import Submission.Work.SSGRoute.LF.Descent
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 800000
set_option linter.unusedSectionVars false


open SSGRoute.PTExt CategoryTheory

open Work.SSGRoute.LF

/-- **E5s, the realisation step: the compatible level family attached to `y`.**

`S : 0 → S.X₁ --S.f--> S.X₂ --S.g--> S.X₃ → 0` is a short exact sequence of `Gal(K/k)`-modules,
`e : S.X₁ ≅ 𝔽_p` with `𝔽_p` the trivial module, `μ_p ⊆ k` (witnessed by `ζ`), and
`y ∈ Ext¹_G(S.X₃, C_K)` is such that the level functionals `h ↦ φ¹(y)(h)` kill the kernel of the
connecting map `δ_L : H¹(Gal(L/k),S.X₃) → H²(Gal(L/k),S.X₁)` at every level `K ≤ L ≤ Ω`
(hypothesis `hy`).

Conclusion: a **compatible, `p`-torsion family** of functionals
`lam_L : H²(Gal(L/k),𝔽_p) →+ H²(Gal(L/k),C_L)` over the levels of `Ω` which extends those partial
functionals, transported along `e`:
`lam_L (δ_L h ∘ e.hom) = φ¹(y)(h)` for all levels `L` and all `h`
(the composite is Yoneda composition in the *second* variable of `δ_L h ∈ Ext²(ℤ, S.X₁)` with the
degree-`0` coefficient map `e.hom : S.X₁ ⟶ 𝔽_p`, transported to the level `L`).

Normalised case. Taking `S := ShortComplex.mk i π hh` with `S.X₁ = 𝔽_p` and `e := Iso.refl`
recovers the plain statement "`λ_L(δ_L h) := φ¹(y)(h)` extends to a compatible `p`-torsion family
`lam`"; the general `e` is pure transport, and the transformation formula is the naturality of
`ShortExact.extClass` under the change of sub-object:
`S'.extClass = S.extClass ∘ mk₀ e.hom` for the conjugated sequence `S'` with `S'.f = e.inv ≫ S.f`.

Consumer: `Work.SSGRoute.exists_realization_of_delta_lam`, which then applies the Brauer
realisation input `Work.SSGRoute.phi0_realization_in` to `lam`.

Route. This step needs only linear algebra and class field theory, NOT the Brauer realisation:
* the partial functionals are compatible (`Work.SSGRoute.lambdaOnRange_inflCIn`,
  `Work.SSGRoute.lambdaOnRange_inflCIn_colim`), so in the normalised case they glue to an additive
  map on `W = colim_L im(δ_L)`; extending it to `V = colim_L H²(Gal(L/k),𝔽_p)` is linear algebra
  (`Work.SSGRoute.addHom_extend_of_exponent`, since `V` has exponent `p`; the normalised `W`-system
  and its comparison `iota : Wcolim →+ V` are in `Submission/Work/SSGRoute/phi1_wcolim.lean`);
* reading the values back off levelwise uses `A_L[p] = H²(Gal(L/k),C_L)[p] ≅ ℤ/p` for `p ∣ [L:k]`
  and the fact that inflation between such levels is an isomorphism on `p`-torsion
  (`|H²(Gal(L/k),C_L)| = [L:k]`, cyclic: `NK.GlobalCFTdeep.CohomologicalFieldAxiom` from
  `FundamentalClassElement`, transferred to the `Ext` core by the E0b bridge
  `Work.SSGRoute.bridgeE`), and that `H²(Gal(L/k),𝔽_p) = 0` when `p ∤ [L:k]`
  (`Commons.RepresentationTheory.GroupCohomology.natCard_nsmul_groupCohomology_succ_eq_zero`
  together with `p • z = 0`, as the coefficients are `𝔽_p`);
* compatibility of the resulting `lam_L` is then the colimit relation of `V` together with
  injectivity of inflation on `H²(·,C_·)` (`Work.SSGRoute.classIncl_inflation_injective`, PROVED).
  Concretely: pick an additive `Λ : V →+ A[p]` extending the glued functional; for `p ∣ [L:k]` set
  `lam L x :=` the preimage of `Λ (of x)` in `A_L[p]` under the inflation isomorphism
  `A_L[p] ≅ A[p]`, and for `p ∤ [L:k]` set `lam L x := 0` (forced, as its source is `0`). -/
theorem level_family_of_delta (p : ℕ) [Fact p.Prime] (k K Ω : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K] [Field Ω]
    [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (ζ : k) (hζ : IsPrimitiveRoot ζ p)
    (S : ShortComplex (Rep Coeff (K ≃ₐ[k] K))) (hS : S.ShortExact)
    (e : S.X₁ ≅ Rep.trivial Coeff (K ≃ₐ[k] K) (ZMod p))
    (y : Abelian.Ext S.X₃ (classesK k K) 1)
    (hy : ∀ (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
        (h : extH (Rep.res (galRes k K L) S.X₃) 1),
        deltaHom (k := k) (K := K) (L := L) S hS h = 0 →
          phiAt (k := k) (K := K) (L := L) y h = 0) :
    ∃ lam : ∀ (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L],
        extH (Rep.trivial Coeff (L ≃ₐ[k] L) (ZMod p)) 2 →+ extH (classesK k L) 2,
      (∀ (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
        (h : extH (Rep.trivial Coeff (L ≃ₐ[k] L) (ZMod p)) 2), p • lam L h = 0) ∧
      (∀ (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
        (L' : IntermediateField K Ω) [NumberField L'] [FiniteDimensional k L'] [IsGalois k L']
        (hLL : L ≤ L') (h : extH (Rep.trivial Coeff (L ≃ₐ[k] L) (ZMod p)) 2),
        inflCIn (k := k) hLL (lam L h) = lam L' (inflTrivIn (k := k) hLL (ZMod p) h)) ∧
      (∀ (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
        (h : extH (Rep.res (galRes k K L) S.X₃) 1),
        lam L ((deltaHom (k := k) (K := K) (L := L) S hS h).comp
            (Abelian.Ext.mk₀ ((Rep.resFunctor (galRes k K L)).map e.hom)) (add_zero 2))
          = phiAt (k := k) (K := K) (L := L) y h) := by
  -- **The conjugated short exact sequence** `S' : 0 → 𝔽_p → S.X₂ → S.X₃ → 0`, whose connecting
  -- map is the composite of `δ` with the coefficient map `e.hom` (`LF.conjS_deltaHom`).
  -- The hypothesis `hy` transfers to `S'` (`LF.hy_conj`).
  have hy' : ∀ (L : Lvl k K Ω) (h : extH (Rep.res (galRes k K L.1) S.X₃) 1),
      deltaHom (k := k) (K := K) (L := L.1) (conjS p S e) (conjS_shortExact p S hS e) h = 0 →
        phiAt (k := k) (K := K) (L := L.1) y h = 0 :=
    fun L h hh => hy_conj p S hS e y hy L.1 h hh
  -- **The glued functional and its extension `Λ : V →+ A`** (the unconditional gluing layer):
  -- `Λ (δ_L j) = ofA_L (φ¹(y)(j))` on the `δ`-images, with `p`-torsion values.
  obtain ⟨Λ, hΛ, hpΛ⟩ := lambdaBar_ext (k := k) (K := K) (Ω := Ω) p S.X₂ S.X₃ (e.inv ≫ S.f) S.g
    (conjZero p S e) (conjS_shortExact p S hS e) y hy'
  -- **The descended family**: `lam L x` is the unique `p`-torsion `w ∈ H²(Gal(L/k),C_L)` with
  -- `ofA_L w = Λ (of_L x)`.
  refine ⟨fun (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L]
      [IsGalois k L] =>
      descentLam (k := k) (K := K) (Ω := Ω) p Λ hpΛ
        ⟨L, inferInstance, inferInstance, inferInstance⟩, ?_, ?_, ?_⟩
  · -- `p`-torsion
    intro L _ _ _ h
    exact (descentLam_mem (k := k) (K := K) (Ω := Ω) p Λ hpΛ
      ⟨L, inferInstance, inferInstance, inferInstance⟩ h).1
  · -- compatibility with inflation
    intro L _ _ _ L' _ _ _ hLL h
    set Lv : Lvl k K Ω := ⟨L, inferInstance, inferInstance, inferInstance⟩ with hLv
    set Lv' : Lvl k K Ω := ⟨L', inferInstance, inferInstance, inferInstance⟩ with hLv'
    have hlev : Lv ≤ Lv' := hLL
    refine ClassLevelLimit.of_injective (k := k) (K := K) (Ω := Ω) Lv' ?_
    show ClassLevelLimit.of (k := k) (K := K) (Ω := Ω) Lv'
          (classLevelMap (k := k) Lv Lv' hlev
            (descentLam (k := k) (K := K) (Ω := Ω) p Λ hpΛ Lv h))
        = ClassLevelLimit.of (k := k) (K := K) (Ω := Ω) Lv'
            (descentLam (k := k) (K := K) (Ω := Ω) p Λ hpΛ Lv'
              (levelMap (k := k) (K := K) (Ω := Ω) p Lv Lv' hlev h))
    rw [ClassLevelLimit.of_levelMap (k := k) (K := K) (Ω := Ω) hlev
      (descentLam (k := k) (K := K) (Ω := Ω) p Λ hpΛ Lv h)]
    rw [(descentLam_mem (k := k) (K := K) (Ω := Ω) p Λ hpΛ Lv h).2,
      (descentLam_mem (k := k) (K := K) (Ω := Ω) p Λ hpΛ Lv'
        (levelMap (k := k) (K := K) (Ω := Ω) p Lv Lv' hlev h)).2]
    rw [← LevelCohLimit.of_levelMap (k := k) (K := K) (Ω := Ω) p hlev h]
  · -- the values on the `δ`-images
    intro L _ _ _ h
    set Lv : Lvl k K Ω := ⟨L, inferInstance, inferInstance, inferInstance⟩ with hLv
    rw [conjS_deltaHom p S hS e L h]
    show descentLam (k := k) (K := K) (Ω := Ω) p Λ hpΛ Lv
        (deltaHom (k := k) (K := K) (L := Lv.1) (conjS p S e) (conjS_shortExact p S hS e) h)
      = phiAt (k := k) (K := K) (L := Lv.1) y h
    exact (descentLam_unique (k := k) (K := K) (Ω := Ω) p Λ hpΛ Lv
      (deltaHom (k := k) (K := K) (L := Lv.1) (conjS p S e) (conjS_shortExact p S hS e) h)
      (phiAt (k := k) (K := K) (L := Lv.1) y h)
      (by
        have h1 := smul_lambdaOnRange_eq_zero (k := k) (K := K) (Ω := Ω) p S.X₂ S.X₃
          (e.inv ≫ S.f) S.g (conjZero p S e) (conjS_shortExact p S hS e) y hy' Lv
          ((deltaHom (k := k) (K := K) (L := Lv.1) (conjS p S e)
            (conjS_shortExact p S hS e)).rangeRestrict h)
        rwa [lambdaOnRange_apply (k := k) (K := K) (L := Lv.1) (conjS p S e)
          (conjS_shortExact p S hS e) y (hy' Lv) h] at h1)
      (by
        rw [← Lambda_apply_delta (k := k) (K := K) (Ω := Ω) p S.X₂ S.X₃ (e.inv ≫ S.f) S.g
          (conjZero p S e) (conjS_shortExact p S hS e) y hy' Λ hΛ Lv h])).symm

end Work.SSGRoute
