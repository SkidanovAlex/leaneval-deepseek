import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.DualMod.Main
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.E1aClean.h1locCoeffNatural
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The local dictionary `βl` built from a *natural* family of local `Ext`-isomorphisms

This file isolates the last step of `Work.SSGRoute.E1aClean.localDictionary_natural_family` that
does **not** involve the comparison square: given *any* family

  `Φ E : H1loc(D_A,E) ≃+ Ext¹_{D_q}(res E′, K_qˣ)`  (`E′ = DualMod p (E⊗T)`)

which is natural in the coefficient module (the clause of
`Work.SSGRoute.E1aClean.localDictFamilyNatural`), the map

  `βl E A q b := Φ E (toClass b)`

satisfies the three dictionary clauses of the target — additive on locally constant cocycles,
kernel the coboundaries, onto — **and** the target's naturality clause, the latter because the map
on `H1loc` induced by an equivariant `f : E₁ →+ E₂` is the one supplied by
`Work.SSGRoute.E1aClean.h1locCoeffNatural`, whose `hF1`-clause is exactly the hypothesis `Φ`'s
naturality needs.

Everything here is bookkeeping over `toClass` (`toClass_add`, `toClass_eq_zero_iff`,
`toClass_surjective`).
-/

namespace Work.SSGRoute.E1aClean

open CategoryTheory SSGRoute.PTExt
open scoped TensorProduct

noncomputable section

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
  [NumberField K]
variable (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]

/-- The local `Ext`-group in which the local dictionary takes its values. -/
abbrev localExt (A : ValuationSubring Ω)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] : Type :=
  CategoryTheory.Abelian.Ext
    (Rep.res (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype
      (SSGRoute.PTExt.modRep (K ≃ₐ[k] K) (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))))
    (SSGRoute.PTExt.localUnitsK (k := k) (NK.GlobalCFT.Place.ofFinite q)) 1

/-- **The three dictionary clauses of `βl` from an additive equivalence `Φ` on `H1loc`.**

`βl E A q b := Φ E (toClass b)`. -/
theorem beta_l_spec (A : ValuationSubring Ω)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (Φ : ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
        [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E],
        Work.SSGRoute.H1loc p k Ω K E (SSGRoute.decomp k A) ≃+ localExt p k Ω K T A q E) :
    let βl : ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
        [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E],
        ((Ω ≃ₐ[k] Ω) → E) → localExt p k Ω K T A q E :=
      fun E _ _ _ _ _ b => Φ E (Work.SSGRoute.toClass p k Ω K E (SSGRoute.decomp k A) b)
    ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
      [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E],
      (∀ b b' : (Ω ≃ₐ[k] Ω) → E,
          SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b →
          SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b →
          SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b' →
          SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b' →
          βl E (b + b') = βl E b + βl E b') ∧
      (∀ b : (Ω ≃ₐ[k] Ω) → E,
          SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b →
          SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b →
          (βl E b = 0 ↔ SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k A) b)) ∧
      (∀ y, ∃ b : (Ω ≃ₐ[k] Ω) → E,
          SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b ∧
          SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b ∧ βl E b = y) := by
  intro βl E
  refine ⟨?_, ?_, ?_⟩
  · intro b b' hb hl hb' hl'
    have hbC : b ∈ Work.SSGRoute.lcCocycles p k Ω K E (SSGRoute.decomp k A) := ⟨hb, hl⟩
    have hbC' : b' ∈ Work.SSGRoute.lcCocycles p k Ω K E (SSGRoute.decomp k A) := ⟨hb', hl'⟩
    show Φ E (Work.SSGRoute.toClass p k Ω K E (SSGRoute.decomp k A) (b + b'))
        = Φ E (Work.SSGRoute.toClass p k Ω K E (SSGRoute.decomp k A) b)
          + Φ E (Work.SSGRoute.toClass p k Ω K E (SSGRoute.decomp k A) b')
    rw [Work.SSGRoute.toClass_add p k Ω K E (SSGRoute.decomp k A) hbC hbC', map_add]
  · intro b hb hl
    have hbC : b ∈ Work.SSGRoute.lcCocycles p k Ω K E (SSGRoute.decomp k A) := ⟨hb, hl⟩
    show Φ E (Work.SSGRoute.toClass p k Ω K E (SSGRoute.decomp k A) b) = 0
      ↔ SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k A) b
    rw [(Φ E).map_eq_zero_iff, Work.SSGRoute.toClass_eq_zero_iff p k Ω K E (SSGRoute.decomp k A) hbC]
    rfl
  · intro y
    obtain ⟨g, hg, hgt⟩ := Work.SSGRoute.toClass_surjective p k Ω K E (SSGRoute.decomp k A)
      ((Φ E).symm y)
    exact ⟨g, hg.1, hg.2, by
      show Φ E (Work.SSGRoute.toClass p k Ω K E (SSGRoute.decomp k A) g) = y
      rw [hgt, AddEquiv.apply_symm_apply]⟩

/-- **The naturality clause of `βl` from the naturality of the family `Φ`.**

The `F` produced by `h1locCoeffNatural` has, by construction, the `hF1`-property that `Φ`'s
naturality needs; the rest is `βl E = Φ E ∘ toClass`. -/
theorem beta_l_natural (A : ValuationSubring Ω)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (Φ : ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
        [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E],
        Work.SSGRoute.H1loc p k Ω K E (SSGRoute.decomp k A) ≃+ localExt p k Ω K T A q E)
    (hnat : ∀ (E₁ : Type) [AddCommGroup E₁] [Module (ZMod p) E₁] [DistribMulAction (K ≃ₐ[k] K) E₁]
        [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E₁] [Finite E₁]
        (E₂ : Type) [AddCommGroup E₂] [Module (ZMod p) E₂] [DistribMulAction (K ≃ₐ[k] K) E₂]
        [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E₂] [Finite E₂]
        (f : E₁ →ₗ[ZMod p] E₂) (hf : ∀ (g : K ≃ₐ[k] K) (e : E₁), f (g • e) = g • f e)
        (F : Work.SSGRoute.H1loc p k Ω K E₁ (SSGRoute.decomp k A) →+
              Work.SSGRoute.H1loc p k Ω K E₂ (SSGRoute.decomp k A))
        (hF1 : ∀ (b : (Ω ≃ₐ[k] Ω) → E₁)
          (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b)
          (hl : SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b),
          F (Work.SSGRoute.toClass p k Ω K E₁ (SSGRoute.decomp k A) b) =
            Work.SSGRoute.toClass p k Ω K E₂ (SSGRoute.decomp k A) (fun g => f (b g)))
        (F' : SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
              (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E₂ T)) ⟶
            SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
              (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E₁ T)))
        (hF' : ∀ (φ : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E₂ T)) (e : E₁) (t : T),
          (show Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E₁ T) from F'.hom φ)
            (TensorProduct.tmul (ZMod p) e t) = φ (TensorProduct.tmul (ZMod p) (f e) t))
        (x : Work.SSGRoute.H1loc p k Ω K E₁ (SSGRoute.decomp k A)),
        (Φ E₂) (F x) =
          (CategoryTheory.Abelian.Ext.mk₀
            (Rep.resMap (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype F')).comp
            ((Φ E₁) x) (zero_add 1)) :
    ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
      [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
      (E2 : Type) [AddCommGroup E2] [Module (ZMod p) E2] [DistribMulAction (K ≃ₐ[k] K) E2]
      [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E2] [Finite E2]
      (f : E →ₗ[ZMod p] E2) (hf : ∀ (g : K ≃ₐ[k] K) (e : E), f (g • e) = g • f e)
      (F' : SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
            (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E2 T)) ⟶
          SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
            (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T)))
      (hF' : ∀ (φ : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E2 T)) (e : E) (t : T),
        (show Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T) from F'.hom φ)
          (TensorProduct.tmul (ZMod p) e t) = φ (TensorProduct.tmul (ZMod p) (f e) t))
      (b : (Ω ≃ₐ[k] Ω) → E),
      SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b →
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b →
      Φ E2 (Work.SSGRoute.toClass p k Ω K E2 (SSGRoute.decomp k A) (fun σ => f (b σ))) =
        (CategoryTheory.Abelian.Ext.mk₀
          (Rep.resMap (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype F')).comp
          (Φ E (Work.SSGRoute.toClass p k Ω K E (SSGRoute.decomp k A) b)) (zero_add 1) := by
  intro E _ _ _ _ _ E2 _ _ _ _ _ f hf F' hF' b hb hl
  obtain ⟨F, hF1, -⟩ := h1locCoeffNatural p k Ω K A E E2 (f : E →+ E2) hf
  have h1 : Work.SSGRoute.toClass p k Ω K E2 (SSGRoute.decomp k A) (fun σ => f (b σ))
      = F (Work.SSGRoute.toClass p k Ω K E (SSGRoute.decomp k A) b) :=
    (hF1 b hb hl).symm
  rw [h1]
  exact hnat E E2 f hf F hF1 F' hF' _

end

end Work.SSGRoute.E1aClean
