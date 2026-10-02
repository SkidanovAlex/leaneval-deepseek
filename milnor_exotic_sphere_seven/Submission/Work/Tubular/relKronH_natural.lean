import Mathlib
import Submission.Work.Tubular.relKronecker_chain
import Submission.Work.Cohomology.localHomology
import Submission.Work.Cohomology.exists_relComplexMap
import Submission.Work.Tubular.RelAPI
import Submission.Work.Tubular.exists_relKronH_eval_iso
import Submission.Work.Cohomology.relCupHNatural
import Submission.Work.Cohomology.relCochainDual

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open CategoryTheory

namespace Work.Tubular

/-!
# Naturality of the relative Kronecker pairing

`Work.Tubular.relKronH X A n : H^n(X,A;ℤ) →ₗ[ℤ] (H_n(X,A;ℤ) →ₗ[ℤ] ℤ)` is the relative Kronecker
pairing of the tubular chapter, defined (`Submission/Work/Tubular/relKronecker_chain.lean`) as a
`Classical.choose`, with the only usable characterisation being its computation rule
`Work.Tubular.relKronH_apply_of_relDualProj` on the class of a relative cocycle and the class of a
relative cycle.

The present file proves its **naturality** in the pair, for an *arbitrary* map of pairs, i.e. an
arbitrary pair of continuous maps `f : X ⟶ Y`, `g : TopCat.of A ⟶ TopCat.of B` compatible in the
sense that `subtypeIncl X A ≫ f = g ≫ subtypeIncl Y B`: for a relative class `β ∈ H^n(Y,B;ℤ)` and a
relative homology class `c ∈ H_n(X,A;ℤ)`,

  `⟨f^* β, c⟩_{(X,A)} = ⟨β, f_* c⟩_{(Y,B)}`.

Both sides are computed on the classes of a relative cocycle `ζ` of `(Y,B)` and a relative cycle
`cc` of `(X,A)` (`homologyπ` is surjective).  Choosing an absolute chain `z0` lifting `cc`
(`relDualProj_surjective`), the left hand side is `relKronH_apply_of_relDualProj`, i.e. the
evaluation of the pulled-back cocycle `relMapLM ζ` on `z0`; by `relMapLM_coe` and
`dualChainMap_f_hom` this evaluation is that of `ζ` on the image of `z0` under `chainMap f`, and
`chainMap f z0` lifts the image cycle by the chain-level naturality `relChainsMapOf` of the
quotient map `C_*(X) → C_*(X,A)`, proved here from the compatibility hypothesis `w` alone.  This is
exactly the right hand side.  Note that the whole argument uses only the compatibility `w`; no
relation between `g` and the *formula* of `f` is needed.

The one technical subtlety (as in the companion file `Work.ThomBordism.FrameSigns.relKronH_natural`
for the canonical `g = relMapSub A B f hf`) is that `relKronH_apply_of_relDualProj` concludes with
the evaluation of a `Work.Cohomology.Cochain`, a type that is only *definitionally* the type of the
underlying cochain of a relative cocycle; rewriting inside the resulting goal with `rw` breaks at
the transparency level used by the rewriter, so the two evaluations are compared through explicit
`Eq.trans` chains and `LinearMap.dualMap_apply` instead.
-/

/-- **The chain-level naturality of the quotient map `C_*(X) → C_*(X,A)`**: for a map of pairs
`f : X ⟶ Y`, `g : A ⟶ B`, `w : subtypeIncl X A ≫ f = g ≫ subtypeIncl Y B`, the projection
`relDualProj` commutes with the induced map of relative chain complexes and the induced map of
absolute chain complexes. -/
private lemma relDualProj_relChainsMapOf_general {X Y : TopCat} (A : Set X) (B : Set Y)
    (f : X ⟶ Y) (g : TopCat.of A ⟶ TopCat.of B)
    (w : Work.Cohomology.subtypeIncl X A ≫ f = g ≫ Work.Cohomology.subtypeIncl Y B) (n : ℕ) :
    Work.Cohomology.relDualProj X A n ≫ (Work.Cohomology.relChainsMapOf X Y A B f g w).f n
      = (Work.Cohomology.chainMap ℤ X Y f).f n ≫ Work.Cohomology.relDualProj Y B n := by
  have hw : Work.Cohomology.inclChains X A ≫ Work.Cohomology.chainMap ℤ X Y f
      = Work.Cohomology.chainMap ℤ (TopCat.of A) (TopCat.of B) g
        ≫ Work.Cohomology.inclChains Y B := by
    simp only [Work.Cohomology.inclChains, Work.Cohomology.chainMap, ← Functor.map_comp, w]
  have h := Work.Cohomology.cokernel_π_map (Work.Cohomology.inclChains X A)
    (Work.Cohomology.inclChains Y B) (Work.Cohomology.chainMap ℤ (TopCat.of A) (TopCat.of B) g)
    (Work.Cohomology.chainMap ℤ X Y f) hw
  have h2 := congrArg (fun k => k.f n) h
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f] at h2
  rw [Work.Cohomology.relChainsMapOf]
  exact h2

/-- A morphism of complexes sends the class of a cycle to the class of the image cycle. -/
private lemma homologyMap_homologyπ_apply_general {R : Type} [CommRing R] {ι : Type}
    {cs : ComplexShape ι} {K L : HomologicalComplex (ModuleCat R) cs} (φ : K ⟶ L) (i : ι)
    [K.HasHomology i] [L.HasHomology i] (z : K.cycles i) :
    (HomologicalComplex.homologyMap φ i).hom ((K.homologyπ i).hom z) =
      (L.homologyπ i).hom ((HomologicalComplex.cyclesMap φ i).hom z) := by
  have h := HomologicalComplex.homologyπ_naturality φ i
  have h2 := congrArg (fun g => g.hom z) h
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h2

/-- Naturality of the relative Kronecker pairing, in the general `TopCat`-morphism form. -/
private lemma relKronH_natural_aux {X Y : TopCat} (A : Set X) (B : Set Y)
    (f : X ⟶ Y) (g : TopCat.of A ⟶ TopCat.of B) (hf : ∀ x ∈ A, f x ∈ B)
    (w : Work.Cohomology.subtypeIncl X A ≫ f = g ≫ Work.Cohomology.subtypeIncl Y B) (n : ℕ)
    (b : Work.Cohomology.relCohomology ℤ Y B n)
    (z : (Work.Cohomology.relChains X A).homology n) :
    Work.Tubular.relKronH X A n
        ((HomologicalComplex.homologyMap
          (Work.Cohomology.relComplexMap ℤ A B f hf) n).hom b) z
      = Work.Tubular.relKronH Y B n b
          ((HomologicalComplex.homologyMap
            (Work.Cohomology.relChainsMapOf X Y A B f g w) n).hom z) := by
  -- reduce to the classes of a relative cocycle of `(Y,B)` and a relative cycle of `(X,A)`
  obtain ⟨ζ, rfl⟩ := (ModuleCat.epi_iff_surjective
    ((Work.Cohomology.relComplex ℤ Y B).homologyπ n)).mp inferInstance b
  obtain ⟨cc, rfl⟩ := (ModuleCat.epi_iff_surjective
    ((Work.Cohomology.relChains X A).homologyπ n)).mp inferInstance z
  have hcl : Work.Cohomology.relClassOf ℤ Y B
      (Work.Tubular.relOfCycle Y B n ζ) (Work.Tubular.relDiffLM_relOfCycle Y B n ζ)
      = (HomologicalComplex.homologyπ (Work.Cohomology.relComplex ℤ Y B) n).hom ζ :=
    Work.Tubular.relClassOf_relOfCycle Y B n ζ
  rw [← hcl]
  -- a lift of the relative cycle `cc` to an absolute chain
  obtain ⟨z0, hz0⟩ := Work.Cohomology.relDualProj_surjective X A n
      ((HomologicalComplex.iCycles (Work.Cohomology.relChains X A) n).hom cc)
  set ψ := Work.Cohomology.relChainsMapOf X Y A B f g w with hψ
  -- the pullback of the class of `ζ`
  rw [Work.Cohomology.homologyMap_relComplexMap_relClassOf ℤ A B f hf
      (Work.Tubular.relOfCycle Y B n ζ) (Work.Tubular.relDiffLM_relOfCycle Y B n ζ)]
  -- the two evaluations, with the `Cochain` types made explicit
  let αL : Work.Cohomology.Cochain ℤ (TopCat.toSSet.obj X) n :=
    ((Work.Cohomology.relMapLM ℤ A B f hf n) (Work.Tubular.relOfCycle Y B n ζ)).1
  let αR : Work.Cohomology.Cochain ℤ (TopCat.toSSet.obj Y) n :=
    (Work.Tubular.relOfCycle Y B n ζ).1
  have hLk : Work.Tubular.relKronH X A n
        (Work.Cohomology.relClassOf ℤ X A
          (Work.Cohomology.relMapLM ℤ A B f hf n (Work.Tubular.relOfCycle Y B n ζ))
          (Work.Cohomology.relDiffLM_relMapLM ℤ A B f hf (Work.Tubular.relOfCycle Y B n ζ)
            (Work.Tubular.relDiffLM_relOfCycle Y B n ζ)))
        ((HomologicalComplex.homologyπ (Work.Cohomology.relChains X A) n).hom cc)
      = Work.Cohomology.kronecker ℤ (TopCat.toSSet.obj X) αL z0 :=
    Work.Tubular.relKronH_apply_of_relDualProj n _ _ cc z0 hz0
  -- the image of the lift is a lift of the image cycle
  have hz1 : (Work.Cohomology.relDualProj Y B n)
      (((Work.Cohomology.chainMap ℤ X Y f).f n).hom z0)
      = ((Work.Cohomology.relChains Y B).iCycles n).hom
          ((HomologicalComplex.cyclesMap ψ n).hom cc) := by
    have h1 := congrArg (fun (k : (Work.Cohomology.singularChains ℤ X).X n ⟶
        (Work.Cohomology.relChains Y B).X n) => (ConcreteCategory.hom k) z0)
      (relDualProj_relChainsMapOf_general A B f g w n)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h1
    have h2 := congrArg (fun (k : (Work.Cohomology.relChains X A).cycles n ⟶
        (Work.Cohomology.relChains Y B).X n) => (ConcreteCategory.hom k) cc)
      (HomologicalComplex.cyclesMap_i ψ n)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
    rw [← h1, hz0, ← h2]
  have hR1 : (HomologicalComplex.homologyMap ψ n).hom
        ((HomologicalComplex.homologyπ (Work.Cohomology.relChains X A) n).hom cc)
      = (HomologicalComplex.homologyπ (Work.Cohomology.relChains Y B) n).hom
          ((HomologicalComplex.cyclesMap ψ n).hom cc) :=
    homologyMap_homologyπ_apply_general ψ n cc
  have hRk : Work.Tubular.relKronH Y B n
        (Work.Cohomology.relClassOf ℤ Y B (Work.Tubular.relOfCycle Y B n ζ)
          (Work.Tubular.relDiffLM_relOfCycle Y B n ζ))
        ((HomologicalComplex.homologyπ (Work.Cohomology.relChains Y B) n).hom
          ((HomologicalComplex.cyclesMap ψ n).hom cc))
      = Work.Cohomology.kronecker ℤ (TopCat.toSSet.obj Y) αR
          (((Work.Cohomology.chainMap ℤ X Y f).f n).hom z0) :=
    Work.Tubular.relKronH_apply_of_relDualProj (X := Y) (A := B) n _ _ _ _ hz1
  -- the two evaluations agree: the second is the transpose of the chain map applied to the first
  have hfin : Work.Cohomology.kronecker ℤ (TopCat.toSSet.obj X) αL z0
      = Work.Cohomology.kronecker ℤ (TopCat.toSSet.obj Y) αR
          (((Work.Cohomology.chainMap ℤ X Y f).f n).hom z0) := by
    have h1 := Work.Cohomology.relMapLM_coe ℤ A B f hf n (Work.Tubular.relOfCycle Y B n ζ)
    have h2 := Work.Cohomology.dualChainMap_f_hom ℤ X Y f n
    have h12 : αL = ((Work.Cohomology.chainMap ℤ X Y f).f n).hom.dualMap αR :=
      h1.trans (congrArg (fun ψ => ψ (Work.Tubular.relOfCycle Y B n ζ).1) h2)
    change αL z0 = αR (((Work.Cohomology.chainMap ℤ X Y f).f n).hom z0)
    rw [h12]
    exact LinearMap.dualMap_apply _ _ _
  refine hLk.trans ?_
  rw [hR1, hRk]
  exact hfin

theorem relKronH_natural {X Y : TopCat} {A : Set X} {B : Set Y} (f : X ⟶ Y)
    (g : TopCat.of A ⟶ TopCat.of B)
    (hf : ∀ x ∈ A, f x ∈ B)
    (w : CategoryTheory.CategoryStruct.comp (Work.Cohomology.subtypeIncl X A) f
      = CategoryTheory.CategoryStruct.comp g (Work.Cohomology.subtypeIncl Y B))
    (n : ℕ) (β : (Work.Cohomology.relComplex ℤ Y B).homology n)
    (c : (Work.Cohomology.relChains X A).homology n) :
    Work.Tubular.relKronH X A n
        ((HomologicalComplex.homologyMap
          (Work.Cohomology.relComplexMap ℤ A B f hf) n).hom β) c
      = Work.Tubular.relKronH Y B n β
          ((HomologicalComplex.homologyMap
            (Work.Cohomology.relChainsMapOf X Y A B f g w) n).hom c) :=
  relKronH_natural_aux A B f g hf w n β c

end Work.Tubular
