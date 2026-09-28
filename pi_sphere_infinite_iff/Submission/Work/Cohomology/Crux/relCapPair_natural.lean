import Mathlib
import Submission.Work.Cohomology.RelCapHTransfer
import Submission.Work.Cohomology.exists_relComplexMap
import Submission.Work.Cohomology.localHomology
import Submission.Work.Cohomology.relCapH
import Submission.Work.Cohomology.cap_natural
import Submission.Work.Cohomology.kronH_natural

set_option backward.isDefEq.respectTransparency false

namespace Work.Cohomology.Crux

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

noncomputable section

/-- The composite `cokernel.π ≫ relChainsMapOf` is the chain map followed by `cokernel.π`. -/
lemma cruxCokernel_π_relChainsMapOf {X Y : TopCat} (A : Set X) (B : Set Y) (f : X ⟶ Y)
    (g : TopCat.of A ⟶ TopCat.of B) (w : subtypeIncl X A ≫ f = g ≫ subtypeIncl Y B) :
    cokernel.π (inclChains X A) ≫ relChainsMapOf X Y A B f g w
      = chainMap ℤ X Y f ≫ cokernel.π (inclChains Y B) := by
  rw [relChainsMapOf]
  exact cokernel_π_map (inclChains X A) (inclChains Y B)
    (chainMap ℤ (TopCat.of A) (TopCat.of B) g) (chainMap ℤ X Y f) _

/-- The elementwise form: a lift of a relative chain is carried to a lift of its image. -/
lemma cruxRelChainsMapOf_apply {X Y : TopCat} (A : Set X) (B : Set Y) (f : X ⟶ Y)
    (g : TopCat.of A ⟶ TopCat.of B) (w : subtypeIncl X A ≫ f = g ≫ subtypeIncl Y B)
    (k : ℕ) (x : (singularChains ℤ X).X k) :
    ((relChainsMapOf X Y A B f g w).f k).hom (((cokernel.π (inclChains X A)).f k).hom x)
      = ((cokernel.π (inclChains Y B)).f k).hom (((chainMap ℤ X Y f).f k).hom x) := by
  have h := congrArg (fun (m : singularChains ℤ X ⟶ relChains Y B) => (ModuleCat.Hom.hom (m.f k)) x)
    (cruxCokernel_π_relChainsMapOf A B f g w)
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply] at h
  exact h

/-- The elementwise form of `HomologicalComplex.cyclesMap_i` for chain complexes. -/
lemma cruxCyclesMap_i_apply {K L : ChainComplex (ModuleCat ℤ) ℕ} (φ : K ⟶ L) (i : ℕ)
    (z : K.cycles i) :
    (L.iCycles i).hom ((HomologicalComplex.cyclesMap φ i).hom z)
      = (φ.f i).hom ((K.iCycles i).hom z) := by
  have h := congrArg (fun (m : K.cycles i ⟶ L.X i) => (ModuleCat.Hom.hom m) z)
    (HomologicalComplex.cyclesMap_i φ i)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h

/-- The elementwise form of `HomologicalComplex.cyclesMap_i` for cochain complexes. -/
lemma cruxCyclesMap_i_apply' {K L : CochainComplex (ModuleCat ℤ) ℕ} (φ : K ⟶ L) (i : ℕ)
    (z : K.cycles i) :
    (L.iCycles i).hom ((HomologicalComplex.cyclesMap φ i).hom z)
      = (φ.f i).hom ((K.iCycles i).hom z) := by
  have h := congrArg (fun (m : K.cycles i ⟶ L.X i) => (ModuleCat.Hom.hom m) z)
    (HomologicalComplex.cyclesMap_i φ i)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h

/-- **Naturality of the relative cap product under a map of pairs.**

For `f : X₁ ⟶ X₂` with `f '' A₁ ⊆ A₂`, a relative cohomology class `a ∈ Hⁿ(X₂,A₂;ℤ)` and a
relative homology class `c ∈ H_{n+m}(X₁,A₁;ℤ)` one has

  `f_*((f^* a) ⌢ c) = a ⌢ (f_* c)`,

where `f^*` is the pullback on relative cohomology induced by `relComplexMap`,
`f_* : H_{n+m}(X₁,A₁) → H_{n+m}(X₂,A₂)` is the pushforward on *relative* homology induced by
`relChainsMapOf`, and `f_* : H_m(X₁) → H_m(X₂)` on the left is the pushforward on *absolute*
homology induced by `chainMap ℤ X₁ X₂ f`.

The proof reduces to cycle representatives (using the surjectivity of `homologyπ`), lifts the
relative cycle to an absolute chain along `cokernel.π (inclChains X₁ A₁)`, and applies the
chain-level naturality `cap_natural` of the cap product; the identification of the pulled-back
relative cocycle with the transpose of the chain map applied to the cocycle is `relMapLM_coe`,
and the pushed-forward lift is computed with `cokernel_π_relChainsMapOf`. -/
theorem relCapPair_natural {X₁ X₂ : TopCat} (A₁ : Set X₁) (A₂ : Set X₂) (f : X₁ ⟶ X₂)
    (h : ∀ x ∈ A₁, f x ∈ A₂) (n m : ℕ)
    (a : relCohomology ℤ X₂ A₂ n) (c : (relChains X₁ A₁).homology (n + m)) :
    (HomologicalComplex.homologyMap (chainMap ℤ X₁ X₂ f) m).hom
        (relCapPair X₁ A₁ n m
          ((HomologicalComplex.homologyMap (relComplexMap ℤ A₁ A₂ f h) n).hom a) c)
      = relCapPair X₂ A₂ n m a
          ((HomologicalComplex.homologyMap
            (relChainsMapOf X₁ X₂ A₁ A₂ f (relMapSub A₁ A₂ f h) (relMapSub_spec A₁ A₂ f h))
            (n + m)).hom c) := by
  classical
  obtain ⟨w, rfl⟩ := (ModuleCat.epi_iff_surjective
    ((relComplex ℤ X₂ A₂).homologyπ n)).mp inferInstance a
  obtain ⟨v, rfl⟩ := (ModuleCat.epi_iff_surjective
    ((relChains X₁ A₁).homologyπ (n + m))).mp inferInstance c
  set φ : relComplex ℤ X₂ A₂ ⟶ relComplex ℤ X₁ A₁ := relComplexMap ℤ A₁ A₂ f h with hφ
  set gg : relChains X₁ A₁ ⟶ relChains X₂ A₂ :=
    relChainsMapOf X₁ X₂ A₁ A₂ f (relMapSub A₁ A₂ f h) (relMapSub_spec A₁ A₂ f h) with hgg
  set cf : singularChains ℤ X₁ ⟶ singularChains ℤ X₂ := chainMap ℤ X₁ X₂ f with hcf
  set w₁ : (relComplex ℤ X₁ A₁).cycles n := (HomologicalComplex.cyclesMap φ n).hom w with hw₁
  set v₂ : (relChains X₂ A₂).cycles (n + m) := (HomologicalComplex.cyclesMap gg (n + m)).hom v
    with hv₂def
  -- the cycle-level naturality
  have hcycle : (HomologicalComplex.cyclesMap cf m).hom (relCapPairZ X₁ A₁ n m w₁ v)
      = relCapPairZ X₂ A₂ n m w v₂ := by
    apply iCycles_injective_C ℤ (singularChains ℤ X₂) m
    have hcyc : (singularChains ℤ X₂).iCycles m
          ((HomologicalComplex.cyclesMap cf m).hom (relCapPairZ X₁ A₁ n m w₁ v))
        = cf.f m ((singularChains ℤ X₁).iCycles m (relCapPairZ X₁ A₁ n m w₁ v)) :=
      cruxCyclesMap_i_apply cf m (relCapPairZ X₁ A₁ n m w₁ v)
    rw [hcyc, relCapPairZ_iCycles X₁ A₁ n m w₁ v, relCapPairZ_iCycles X₂ A₂ n m w v₂]
    obtain ⟨x₀, hx₀⟩ : ∃ x₀ : (singularChains ℤ X₁).X (n + m),
        (cokernel.π ((inclChains X₁ A₁).f (n + m))).hom x₀
          = (relChains_cokernelIso X₁ A₁ (n + m)).hom
              ((relChains X₁ A₁).iCycles (n + m) v) :=
      (ModuleCat.epi_iff_surjective _).mp inferInstance _
    have hx : ((cokernel.π (inclChains X₁ A₁)).f (n + m)).hom x₀
        = (relChains X₁ A₁).iCycles (n + m) v := by
      refine (ModuleCat.mono_iff_injective
        ((relChains_cokernelIso X₁ A₁ (n + m)).hom)).mp inferInstance ?_
      rw [relChains_cokernelIso_canon_apply]
      exact hx₀
    rw [← hx₀, relCapHalf_apply_incl X₁ A₁ (((relComplex ℤ X₁ A₁).iCycles n).hom w₁) x₀]
    -- the pushforward of the lift represents the pushed-forward relative cycle
    have hv₂ : (relChains X₂ A₂).iCycles (n + m) v₂
        = ((cokernel.π (inclChains X₂ A₂)).f (n + m)).hom (cf.f (n + m) x₀) := by
      have h1 : (relChains X₂ A₂).iCycles (n + m) v₂
          = (gg.f (n + m)).hom ((relChains X₁ A₁).iCycles (n + m) v) :=
        cruxCyclesMap_i_apply gg (n + m) v
      rw [h1, ← hx]
      exact cruxRelChainsMapOf_apply A₁ A₂ f (relMapSub A₁ A₂ f h) (relMapSub_spec A₁ A₂ f h)
        (n + m) x₀
    rw [hv₂, relChains_cokernelIso_canon_apply,
      relCapHalf_apply_incl X₂ A₂ (((relComplex ℤ X₂ A₂).iCycles n).hom w) (cf.f (n + m) x₀)]
    -- the pulled-back cochain is the transpose of the chain map applied to the cochain
    have hα : ((relComplex ℤ X₁ A₁).iCycles n).hom w₁
        = (relMapLM ℤ A₁ A₂ f h n) (((relComplex ℤ X₂ A₂).iCycles n).hom w) := by
      rw [cruxCyclesMap_i_apply' φ n w]
      rw [hφ, relComplexMap_f]
      rfl
    rw [hα, relMapLM_coe, dualChainMap_f_hom]
    -- chain-level naturality of the cap product
    have hnat := cap_natural ℤ (TopCat.toSSet.map f)
      (Subtype.val (((relComplex ℤ X₂ A₂).iCycles n).hom w) : Cochain ℤ (TopCat.toSSet.obj X₂) n) x₀
    rw [← chainMap_f_eq ℤ X₁ X₂ f m, ← chainMap_f_eq ℤ X₁ X₂ f n,
      ← chainMap_f_eq ℤ X₁ X₂ f (n + m)] at hnat
    exact hnat
  -- assemble
  have hA : (HomologicalComplex.homologyMap φ n).hom
        (((relComplex ℤ X₂ A₂).homologyπ n).hom w)
      = ((relComplex ℤ X₁ A₁).homologyπ n).hom w₁ :=
    homologyMap_homologyπ_apply φ n w
  have hB : (HomologicalComplex.homologyMap gg (n + m)).hom
        (((relChains X₁ A₁).homologyπ (n + m)).hom v)
      = ((relChains X₂ A₂).homologyπ (n + m)).hom v₂ :=
    homologyMap_homologyπ_apply gg (n + m) v
  rw [hA, hB]
  rw [relCapPair_apply X₁ A₁ n m w₁ v]
  rw [homologyMap_homologyπ_apply cf m (relCapPairZ X₁ A₁ n m w₁ v)]
  rw [relCapPair_apply X₂ A₂ n m w v₂]
  exact congrArg (ModuleCat.Hom.hom ((singularChains ℤ X₂).homologyπ m)) hcycle


end

end Work.Cohomology.Crux
