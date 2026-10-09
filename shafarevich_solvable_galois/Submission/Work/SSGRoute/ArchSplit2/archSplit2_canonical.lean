import Mathlib
import Submission.Work.SSGRoute.ArchSplit2.ell_bot_family
import Submission.Work.SSGRoute.ArchSplit2.archSplit2_square_sign
import Submission.Work.SSGRoute.E1aClean.globalDictionaryCanonDefs
import Submission.Work.SSGRoute.ExtChain.ChainGamma
import Submission.Work.SSGRoute.ArchDictionary.Defs
import Submission.Work.SSGRoute.ArchSplit2.archSplit2Phi
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ArchSplit2

set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

/-- **(A3) The canonical split-place family `ψ_w`** (lead's ruling in `flags_1730/flags_0605.md`:
canonical, NOT an arbitrary linear extension).  `p = 2`, `w` a split infinite place of `K`
(`decompK w = ⊥`) with a seam witness; the conclusion is an `E`-indexed family
`ψ E : E →+ Ext¹_{D_w}(E'|, K_wˣ)` (`E' = DualMod p (E ⊗ T)`) such that

* `ψ E` is bijective, for every finite `𝔽₂[Gal(K/k)]`-module `E`;
* `ψ` is **natural** in the coefficient: `ψ E₂ (f e) = mk₀ (resMap (decompK w).subtype F').comp (ψ E e)`
  for the transpose `F'` of `f ⊗ id_T` (this is the `push`/`hψnat` input of
  `PT.archSplitPlace_dictionary_natural_of_h2E₂`);
* `ψ E` agrees with the canonical global dictionary on global cocycles:
  `ψ E (b c) = extLoc w (extToIdeles (globalDictionaryCanon … b))` (the square, i.e. the `hF` input).

This is precisely the `(ψ, hψ, hψnat, hF)` input that the *proved*
`Work.SSGRoute.PT.archSplitPlace_dictionary_natural_of_h2E₂` consumes to produce the split-place
archimedean dictionary with its four clauses AND its naturality clause; it is also A3 of
`_lead_design/ssg_arch2_2320.md`, the split half of the archimedean conjunct.

Route: define `ψ E := (ell E).symm`-composed with the coefficient identification
`DualMod p (DualMod p (E ⊗ T)) ≅ E` (`e1aCoeffNat`); bijectivity is A1's, the square is A2, and
naturality is A1's naturality clause together with the naturality of `e1aCoeffNat`
(`PT.e1a_coeff_iso_natural`).  A1 is `ArchSplit2.ell_bot_family` (proved), A2 is
`ArchSplit2.archSplit2_square_sign` (proved).

File: `Submission/Work/SSGRoute/ArchSplit2/archSplit2_canonical.lean`; namespace
`Work.SSGRoute.ArchSplit2`. -/
theorem archSplit2_canonical (p : ℕ) [Fact p.Prime] (hp : p = 2) (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (w : NK.GlobalCFT.Place ↥K) (hbot : SSGRoute.PTExt.decompK (k := k) w = ⊥)
    (hwit : ∃ (c₀ : Ω ≃ₐ[k] Ω) (φ₀ : Ω →+* ℂ), c₀ ^ 2 = 1 ∧ c₀ ≠ 1 ∧
      (∀ x : Ω, φ₀ (c₀ x) = starRingEnd ℂ (φ₀ x)) ∧
      w = NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk (φ₀.comp (algebraMap ↥K Ω)))) :
    ∃ ψ : ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
        [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E],
        E →+ CategoryTheory.Abelian.Ext
          (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype
            (SSGRoute.PTExt.modRep (K ≃ₐ[k] K) (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))))
          (SSGRoute.PTExt.localUnitsK (k := k) w) 1,
      (∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
          [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E], Function.Bijective (ψ E)) ∧
      (∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
          [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
          (E2 : Type) [AddCommGroup E2] [Module (ZMod p) E2] [DistribMulAction (K ≃ₐ[k] K) E2]
          [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E2] [Finite E2]
          (f : E →ₗ[ZMod p] E2) (_ : ∀ (g : K ≃ₐ[k] K) (e : E), f (g • e) = g • f e)
          (F' : SSGRoute.PTExt.modRep (K ≃ₐ[k] K) (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E2 T)) ⟶
            SSGRoute.PTExt.modRep (K ≃ₐ[k] K) (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T)))
          (_ : ∀ (θ : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E2 T)) (e : E) (t : T),
            (show Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T) from F'.hom θ)
              (TensorProduct.tmul (ZMod p) e t) = θ (TensorProduct.tmul (ZMod p) (f e) t))
          (e : E),
          ψ E2 (f e) =
            (CategoryTheory.Abelian.Ext.mk₀
              (Rep.resMap (SSGRoute.PTExt.decompK (k := k) w).subtype F')).comp (ψ E e) (zero_add 1)) ∧
      (∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
          [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
          (c : Ω ≃ₐ[k] Ω), c ^ 2 = 1 → c ≠ 1 → ∀ φ : Ω →+* ℂ,
          (∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x)) →
          w = NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk (φ.comp (algebraMap ↥K Ω))) →
          ∀ b : (Ω ≃ₐ[k] Ω) → E,
            SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b → SSGRoute.IsLocConstOn ⊤ b →
            ψ E (b c) = SSGRoute.PTExt.extLoc (k := k) w (SSGRoute.PTExt.extToIdeles (k := k)
              (Work.SSGRoute.E1aClean.globalDictionaryCanon p k Ω K ζ hζ hζK T hT E b))) := by
  classical
  obtain ⟨ell, hbij, hreal, hnat⟩ := ell_bot_family p hp k Ω K T w hbot hwit
  let ψfun : ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
      [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E],
      E →+ CategoryTheory.Abelian.Ext
        (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype
          (SSGRoute.PTExt.modRep (K ≃ₐ[k] K) (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))))
        (SSGRoute.PTExt.localUnitsK (k := k) w) 1 :=
    fun E _ _ _ _ _ =>
      (AddEquiv.ofBijective (ell E) (hbij E)).symm.toAddMonoidHom.comp
        (archSplit2Phi p k Ω K ζ hζ hζK T hT E).toAddMonoidHom
  have hElle : ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
      [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E] (x : E),
      ell E (ψfun E x) = archSplit2Phi p k Ω K ζ hζ hζK T hT E x := by
    intro E _ _ _ _ _ x
    show ell E ((AddEquiv.ofBijective (ell E) (hbij E)).symm
        (archSplit2Phi p k Ω K ζ hζ hζK T hT E x)) = archSplit2Phi p k Ω K ζ hζ hζK T hT E x
    rw [← AddEquiv.ofBijective_apply (ell E) (hbij E)]
    exact AddEquiv.apply_symm_apply _ _
  refine ⟨ψfun, ?_, ?_, ?_⟩
  · intro E _ _ _ _ _
    refine ⟨?_, ?_⟩
    · intro a b hab
      have h2 : archSplit2Phi p k Ω K ζ hζ hζK T hT E a
          = archSplit2Phi p k Ω K ζ hζ hζK T hT E b := by
        rw [← hElle E a, ← hElle E b, hab]
      exact (archSplit2Phi p k Ω K ζ hζ hζK T hT E).injective h2
    · intro y
      refine ⟨(archSplit2Phi p k Ω K ζ hζ hζK T hT E).symm
        ((AddEquiv.ofBijective (ell E) (hbij E)) y), ?_⟩
      show (AddEquiv.ofBijective (ell E) (hbij E)).symm
          (archSplit2Phi p k Ω K ζ hζ hζK T hT E
            ((archSplit2Phi p k Ω K ζ hζ hζK T hT E).symm
              ((AddEquiv.ofBijective (ell E) (hbij E)) y))) = y
      rw [AddEquiv.apply_symm_apply (archSplit2Phi p k Ω K ζ hζ hζK T hT E),
        AddEquiv.symm_apply_apply]
  · intro E _ _ _ _ _ E2 _ _ _ _ _ f hf F' hF e
    have hkey : archSplit2Phi p k Ω K ζ hζ hζK T hT E2 (f e)
        = ell E2 ((CategoryTheory.Abelian.Ext.mk₀
            (Rep.resMap (SSGRoute.PTExt.decompK (k := k) w).subtype F')).comp
              (ψfun E e) (zero_add 1)) := by
      ext m2
      rw [hnat E E2 F' (ψfun E e) m2,
        archSplit2Phi_natural_apply p k Ω K ζ hζ hζK T hT E E2 f hf F' hF e m2]
      rw [hElle E e]
    show (AddEquiv.ofBijective (ell E2) (hbij E2)).symm
        (archSplit2Phi p k Ω K ζ hζ hζK T hT E2 (f e))
      = (CategoryTheory.Abelian.Ext.mk₀
          (Rep.resMap (SSGRoute.PTExt.decompK (k := k) w).subtype F')).comp (ψfun E e) (zero_add 1)
    rw [hkey, ← AddEquiv.ofBijective_apply (ell E2) (hbij E2),
      AddEquiv.symm_apply_apply]
  · intro E _ _ _ _ _ c hc2 hc1 φ hlink hw b hb hl
    set X := SSGRoute.PTExt.extLoc (k := k) w (SSGRoute.PTExt.extToIdeles (k := k)
      (Work.SSGRoute.E1aClean.globalDictionaryCanon p k Ω K ζ hζ hζK T hT E b)) with hX
    have hA2 := archSplit2_square_sign p hp k Ω K ζ hζ hζK T hT E c hc2 hc1 φ hlink
      w hw hbot (ell E) (hreal E) b hb hl
    have hkey : archSplit2Phi p k Ω K ζ hζ hζK T hT E (b c) = ell E X := by
      ext m
      exact zmod_two_dichotomy_aux hp _ _
        ((archSplit2Phi_eq_zero_iff p k Ω K ζ hζ hζK T hT E (b c) m).trans (hA2 m).symm)
    show (AddEquiv.ofBijective (ell E) (hbij E)).symm
        (archSplit2Phi p k Ω K ζ hζ hζK T hT E (b c)) = X
    rw [hkey, ← AddEquiv.ofBijective_apply (ell E) (hbij E), AddEquiv.symm_apply_apply]


end Work.SSGRoute.ArchSplit2
