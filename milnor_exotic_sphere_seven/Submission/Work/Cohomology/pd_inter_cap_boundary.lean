import Mathlib
import Submission.Work.Cohomology.cap_natural
import Submission.Work.Cohomology.pd_union_aux
import Submission.Work.Cohomology.pd_hatcher_W
import Submission.Work.Cohomology.pd_us_frame

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology Simplicial CategoryTheory.Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

/-!
# The boundary/naturality plumbing for the intersection

The main result of this file, `pd_inter_cap_boundary`, records a small compatibility between the
cap product and the inclusion `U ∩ V ↪ U ∪ V`: if a chain `γ` supported in the trace of `U ∩ V`
inside `U ∪ V` has boundary the cap product `s • (ψX ⌢ α₂X)` of a cochain of `U ∪ V` with a chain
`α₂X` of `U ∪ V` which comes from a chain `b` of `U ∩ V`, then the same cap product computed
in `U ∩ V` is a boundary there.

The mathematical content is the naturality of the cap product (`cap_natural`) together with the
fact that the inclusions `U ∩ V ↪ U ∪ V` and the traces of `U ∩ V` inside `U ∪ V` are injective
on singular chains (`inclChains_f_injective`).
-/

/-- The inclusion of the chains of `S` in `M` factors through the inclusion `S ⊆ W`. -/
theorem pdIncl_inclChains_comp {M : TopCat} {S W : Set M} (h : S ⊆ W) :
    inclChains M S
      = chainMap ℤ (TopCat.of S) (TopCat.of W) (pdIncl W S h) ≫ inclChains M W := by
  rw [pdIncl_eq_inclChainsSub h]
  exact (inclChainsSub_comp M S W h).symm

/-- The composite of `pdIncl` with the inclusion of the chains of `W` in `M` is the inclusion
of the chains of `S` in `M`. -/
theorem pdIncl_inclChains_apply {M : TopCat} {S W : Set M} (h : S ⊆ W) (n : ℕ)
    (x : (singularChains ℤ (TopCat.of S)).X n) :
    (inclChains M W).f n
        (((SSet.chainComplexMap (TopCat.toSSet.map (pdIncl W S h)) (ModuleCat.of ℤ ℤ)).f n).hom x)
      = (inclChains M S).f n x := by
  have h2 := congrArg (fun (g : singularChains ℤ (TopCat.of S) ⟶ singularChains ℤ M) =>
      (g.f n).hom x) (pdIncl_inclChains_comp (M := M) h)
  exact h2.symm

/-- `pdTrMap` is injective on chains, because `pdTrInv` is a left inverse of it. -/
theorem chainMap_pdTrMap_injective {M : TopCat} {W S : Set M} (h : S ⊆ W) (n : ℕ) :
    Function.Injective (fun x : (singularChains ℤ (TopCat.of S)).X n =>
      ((chainMap ℤ (TopCat.of S) (TopCat.of (pdTr W S)) (pdTrMap h)).f n).hom x) := by
  have hsect : pdTrMap h ≫ pdTrInv h = 𝟙 (TopCat.of S) := by ext x; rfl
  have hcomp : chainMap ℤ (TopCat.of S) (TopCat.of (pdTr W S)) (pdTrMap h)
      ≫ chainMap ℤ (TopCat.of (pdTr W S)) (TopCat.of S) (pdTrInv h)
      = 𝟙 (singularChains ℤ (TopCat.of S)) := by
    rw [chainMap_compPD, hsect, chainMap_id']
  have hleft : Function.LeftInverse
      (fun z => ((chainMap ℤ (TopCat.of (pdTr W S)) (TopCat.of S) (pdTrInv h)).f n).hom z)
      (fun x => ((chainMap ℤ (TopCat.of S) (TopCat.of (pdTr W S)) (pdTrMap h)).f n).hom x) := by
    intro x
    have h2 := congrArg (fun (g : singularChains ℤ (TopCat.of S) ⟶ singularChains ℤ (TopCat.of S)) =>
        (g.f n).hom x) hcomp
    exact h2
  exact hleft.injective

/-- `pdIncl` is injective on chains: it is the composite of `pdTrMap` (a homeomorphism) and the
inclusion of the chains of the trace. -/
theorem chainComplexMap_pdIncl_injective {M : TopCat} {W S : Set M} (h : S ⊆ W) (n : ℕ) :
    Function.Injective (ModuleCat.Hom.hom ((SSet.chainComplexMap
      (TopCat.toSSet.map (pdIncl W S h)) (ModuleCat.of ℤ ℤ)).f n)) := by
  have hfac : ∀ x : (singularChains ℤ (TopCat.of S)).X n,
      (ModuleCat.Hom.hom ((SSet.chainComplexMap (TopCat.toSSet.map (pdIncl W S h))
          (ModuleCat.of ℤ ℤ)).f n)) x
        = (ModuleCat.Hom.hom ((inclChains (TopCat.of W) (pdTr W S)).f n))
            ((ModuleCat.Hom.hom ((chainMap ℤ (TopCat.of S) (TopCat.of (pdTr W S))
              (pdTrMap h)).f n)) x) := by
    intro x
    have hfac_eq : chainMap ℤ (TopCat.of S) (TopCat.of W) (pdIncl W S h)
        = chainMap ℤ (TopCat.of S) (TopCat.of (pdTr W S)) (pdTrMap h)
          ≫ inclChains (TopCat.of W) (pdTr W S) := by
      rw [pdIncl_eq_inclChainsSub h, inclChainsSub_eq_pdTrMap h]
    have h2 := congrArg (fun (g : singularChains ℤ (TopCat.of S) ⟶
        singularChains ℤ (TopCat.of W)) => (g.f n).hom x) hfac_eq
    exact h2
  intro x y hxy
  have hxy' : (ModuleCat.Hom.hom ((inclChains (TopCat.of W) (pdTr W S)).f n))
        ((ModuleCat.Hom.hom ((chainMap ℤ (TopCat.of S) (TopCat.of (pdTr W S))
          (pdTrMap h)).f n)) x)
      = (ModuleCat.Hom.hom ((inclChains (TopCat.of W) (pdTr W S)).f n))
        ((ModuleCat.Hom.hom ((chainMap ℤ (TopCat.of S) (TopCat.of (pdTr W S))
          (pdTrMap h)).f n)) y) := by
    rw [← hfac x, ← hfac y]
    exact hxy
  exact chainMap_pdTrMap_injective h n (inclChains_f_injective (TopCat.of W) (pdTr W S) n hxy')

theorem pd_inter_cap_boundary {M : TopCat} [T2Space M] {U V : Set M}
    (hUV : U ∩ V ⊆ (U ∪ V : Set M))
    {k mj : ℕ} (s : ℤ)
    (ψX : Work.Cohomology.Cochain ℤ (TopCat.toSSet.obj (TopCat.of (U ∪ V : Set M))) (k+1))
    (b : (Work.Cohomology.singularChains ℤ (TopCat.of (U ∩ V : Set M))).X (k+1+mj))
    (α₂X : (Work.Cohomology.singularChains ℤ (TopCat.of (U ∪ V : Set M))).X (k+1+mj))
    (hb : (Work.Cohomology.inclChains M (U ∪ V : Set M)).f (k+1+mj) α₂X
      = (Work.Cohomology.inclChains M (U ∩ V : Set M)).f (k+1+mj) b)
    (hB : ∃ γ ∈ LinearMap.range (((Work.Cohomology.inclChains (TopCat.of (U ∪ V : Set M))
        (Work.Cohomology.pdTr (U ∪ V) (U ∩ V))).f (mj+1)).hom),
        (Work.Cohomology.singularChains ℤ (TopCat.of (U ∪ V : Set M))).d (mj+1) mj γ
          = s • Work.Cohomology.cap ℤ (TopCat.toSSet.obj (TopCat.of (U ∪ V : Set M))) ψX mj α₂X) :
    ∃ δ : (Work.Cohomology.singularChains ℤ (TopCat.of (U ∩ V : Set M))).X (mj+1),
      (Work.Cohomology.singularChains ℤ (TopCat.of (U ∩ V : Set M))).d (mj+1) mj δ
        = s • Work.Cohomology.cap ℤ (TopCat.toSSet.obj (TopCat.of (U ∩ V : Set M)))
            (ψX.comp ((SSet.chainComplexMap (TopCat.toSSet.map
              (Work.Cohomology.pdIncl (U ∪ V : Set M) (U ∩ V : Set M) hUV))
                (ModuleCat.of ℤ ℤ)).f (k+1)).hom) mj b := by
  obtain ⟨γ, hγmem, hγd⟩ := hB
  -- the local spelling of the hypotheses
  have hb' : (ModuleCat.Hom.hom ((inclChains M (U ∪ V : Set M)).f (k+1+mj))) α₂X
      = (ModuleCat.Hom.hom ((inclChains M (U ∩ V : Set M)).f (k+1+mj))) b := hb
  have hγd' : (ModuleCat.Hom.hom ((singularChains ℤ (TopCat.of (U ∪ V : Set M))).d (mj+1) mj)) γ
      = s • cap ℤ (TopCat.toSSet.obj (TopCat.of (U ∪ V : Set M))) ψX mj α₂X := hγd
  -- the two chains have the same image in `U ∪ V`
  have hα₂ : α₂X = (ModuleCat.Hom.hom ((SSet.chainComplexMap (TopCat.toSSet.map
      (pdIncl (U ∪ V : Set M) (U ∩ V : Set M) hUV)) (ModuleCat.of ℤ ℤ)).f (k+1+mj))) b := by
    apply inclChains_f_injective M (U ∪ V : Set M) (k+1+mj)
    exact hb'.trans (pdIncl_inclChains_apply (M := M) hUV (k+1+mj) b).symm
  -- the cap product in `U ∪ V` of `α₂X` is the image of the cap product in `U ∩ V` of `b`
  have hcap : (ModuleCat.Hom.hom ((SSet.chainComplexMap (TopCat.toSSet.map
        (pdIncl (U ∪ V : Set M) (U ∩ V : Set M) hUV)) (ModuleCat.of ℤ ℤ)).f mj))
        (cap ℤ (TopCat.toSSet.obj (TopCat.of (U ∩ V : Set M)))
          (ψX.comp ((SSet.chainComplexMap (TopCat.toSSet.map
            (pdIncl (U ∪ V : Set M) (U ∩ V : Set M) hUV))
              (ModuleCat.of ℤ ℤ)).f (k+1)).hom) mj b)
      = cap ℤ (TopCat.toSSet.obj (TopCat.of (U ∪ V : Set M))) ψX mj α₂X := by
    rw [hα₂]
    exact cap_natural ℤ (TopCat.toSSet.map (pdIncl (U ∪ V : Set M) (U ∩ V : Set M) hUV)) ψX b
  -- lift `γ` to a chain of `U ∩ V`
  obtain ⟨δ, hδ⟩ := pd_us_mem_range_pdIncl_of_mem_range_pdTr (M := M) hUV hγmem
  have hδ' : (ModuleCat.Hom.hom ((SSet.chainComplexMap (TopCat.toSSet.map
      (pdIncl (U ∪ V : Set M) (U ∩ V : Set M) hUV)) (ModuleCat.of ℤ ℤ)).f (mj+1))) δ = γ := hδ
  refine ⟨δ, ?_⟩
  -- it suffices to compare the images in `U ∪ V`
  apply chainComplexMap_pdIncl_injective hUV mj
  have hdnat : (ModuleCat.Hom.hom ((SSet.chainComplexMap (TopCat.toSSet.map
        (pdIncl (U ∪ V : Set M) (U ∩ V : Set M) hUV)) (ModuleCat.of ℤ ℤ)).f mj))
        ((ModuleCat.Hom.hom ((singularChains ℤ (TopCat.of (U ∩ V : Set M))).d (mj+1) mj)) δ)
      = (ModuleCat.Hom.hom ((singularChains ℤ (TopCat.of (U ∪ V : Set M))).d (mj+1) mj))
        ((ModuleCat.Hom.hom ((SSet.chainComplexMap (TopCat.toSSet.map
          (pdIncl (U ∪ V : Set M) (U ∩ V : Set M) hUV)) (ModuleCat.of ℤ ℤ)).f (mj+1))) δ) := by
    have h := congrArg (fun (g : (singularChains ℤ (TopCat.of (U ∩ V : Set M))).X (mj+1) ⟶
        (singularChains ℤ (TopCat.of (U ∪ V : Set M))).X mj) => g δ)
      (HomologicalComplex.Hom.comm (SSet.chainComplexMap (TopCat.toSSet.map
        (pdIncl (U ∪ V : Set M) (U ∩ V : Set M) hUV)) (ModuleCat.of ℤ ℤ)) (mj+1) mj)
    exact h.symm
  have hstep : (ModuleCat.Hom.hom ((SSet.chainComplexMap (TopCat.toSSet.map
        (pdIncl (U ∪ V : Set M) (U ∩ V : Set M) hUV)) (ModuleCat.of ℤ ℤ)).f mj))
        ((ModuleCat.Hom.hom ((singularChains ℤ (TopCat.of (U ∩ V : Set M))).d (mj+1) mj)) δ)
      = s • (ModuleCat.Hom.hom ((SSet.chainComplexMap (TopCat.toSSet.map
        (pdIncl (U ∪ V : Set M) (U ∩ V : Set M) hUV)) (ModuleCat.of ℤ ℤ)).f mj))
        (cap ℤ (TopCat.toSSet.obj (TopCat.of (U ∩ V : Set M)))
          (ψX.comp ((SSet.chainComplexMap (TopCat.toSSet.map
            (pdIncl (U ∪ V : Set M) (U ∩ V : Set M) hUV))
              (ModuleCat.of ℤ ℤ)).f (k+1)).hom) mj b) := by
    rw [hdnat, hδ', hγd', ← hcap]
  exact hstep.trans (map_zsmul _ s _).symm

end

end Work.Cohomology
