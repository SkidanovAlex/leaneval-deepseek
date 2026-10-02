import Mathlib
import Submission.Work.ThomBordism.FrameSigns.chartCoh_compare
import Submission.Work.ThomBordism.FrameSigns.chartCoh_pair_ne_zero
import Submission.Work.Tubular.exists_relKronH_eval_iso
import Submission.Work.ThomBordism.FrameSigns.relKronH_unimodular

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.ThomBordism.KeyLocal

open CategoryTheory

noncomputable section

/-!
# The chart class is the frame sign times any class pairing to `1` with the local class

Let `V` be a closed oriented smooth `8`-manifold, `i` a chart of the finite cover, `x ∈ src V i` a
point of its source, and let `c := locClass (TopCat.of V.pt) 8 V.c x` be the local fundamental class
of `V` at `x` in `H₈(V, V∖{x};ℤ)`.

* `Work.Tubular.relKronH (TopCat.of V.pt) (punct V x) 8` is the relative Kronecker pairing
  `H⁸(V, V∖{x};ℤ) →ₗ (H₈(V, V∖{x};ℤ) →ₗ ℤ)`, an isomorphism because the relative homology is
  degreewise free (`localHomology_charted`: it is `ℤ` in degree `8` and `0` otherwise).
* `c` is a cyclic generator of `H₈(V, V∖{x};ℤ)` (the field `Man8.c_fund`), so the evaluation
  functional `a ↦ ⟨a, c⟩` is *injective*: a class of `H⁸` is determined by its pairing with `c`.
* `pairVal V i x := ⟨chartCoh V i x, c⟩` is a *unit* of `ℤ`: it is the image of the generator `c`
  under the composite of the isomorphisms
  `H₈(V,V∖x) ≅ H₈(↥srcᵢ, srcᵢ∖x) ≅ H₈(ℝ⁸,ℝ⁸∖0) ≅ ℤ`
  (the first two are the homology isomorphisms of the inclusion of the chart source and of the
  translated chart, `isIso_chartSrcChain` / `isIso_chartTransChain`, and the last is `dual0`), so
  `pairVal = ±1`.

Consequently any class `o` of `H⁸(V, V∖{x};ℤ)` with `⟨o, c⟩ = 1` must be `± chartCoh`, with the
sign prescribed by `pairVal`: `chartCoh = (if 0 < pairVal then 1 else -1) • o`.
-/

/-- **A surjective `ℤ`-linear functional sends a cyclic generator to a unit.**  If `f : M →ₗ[ℤ] ℤ` is
surjective and `m` spans `M`, then `f m = ±1`. -/
lemma isUnit_apply_of_surjective_of_span_singleton_eq_top {M : Type*} [AddCommGroup M] [Module ℤ M]
    (f : M →ₗ[ℤ] ℤ) (hf : Function.Surjective f) {m : M}
    (hm : Submodule.span ℤ ({m} : Set M) = ⊤) : IsUnit (f m) := by
  have hspan : Submodule.span ℤ ({f m} : Set ℤ) = ⊤ := by
    rw [show ({f m} : Set ℤ) = f '' ({m} : Set M) by ext y; simp]
    rw [← Submodule.map_span, hm, ← LinearMap.range_eq_map]
    exact LinearMap.range_eq_top.mpr hf
  obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp
    (show (1 : ℤ) ∈ Submodule.span ℤ ({f m} : Set ℤ) by rw [hspan]; exact Submodule.mem_top)
  refine isUnit_iff_exists_inv.mpr ⟨k, ?_⟩
  rw [mul_comm]
  rw [zsmul_eq_mul] at hk
  simpa using hk

theorem chartCoh_eq_frameSign_smul (V : Work.ThomBordism.Man8) (i : Work.ThomBordism.FrameSigns.ChartIdx V)
    {x : V.pt} (hx : x ∈ Work.ThomBordism.FrameSigns.src V i)
    (o : Work.Thom.RelCoh ℤ 8 V.pt (Work.ThomBordism.FrameSigns.punct V x))
    (ho : Work.Tubular.relKronH (TopCat.of V.pt) (Work.ThomBordism.FrameSigns.punct V x) 8 o
        (Work.Orient.locClass (TopCat.of V.pt) 8 V.c x) = 1) :
    Work.ThomBordism.FrameSigns.chartCoh V i x hx
      = (if 0 < Work.ThomBordism.FrameSigns.pairVal V i x hx then (1 : ℤ) else -1) • o := by
  -- freeness of the relative homology of the pair `(V, V∖{x})`
  have hfree : ∀ j, Module.Free ℤ
      ↥((Work.Cohomology.relChains (TopCat.of V.pt)
        (Work.ThomBordism.FrameSigns.punct V x)).homology j) := by
    intro j
    rcases eq_or_ne j 8 with hj | hj
    · subst hj
      obtain ⟨e⟩ := (Work.Cohomology.localHomology_charted 8 (by norm_num) V.pt x 8).1 rfl
      exact Module.Free.of_equiv' (inferInstance : Module.Free ℤ ℤ) e.toLinearEquiv.symm
    · haveI : Subsingleton ↥((Work.Cohomology.relChains (TopCat.of V.pt)
          (Work.ThomBordism.FrameSigns.punct V x)).homology j) :=
        ModuleCat.subsingleton_of_isZero
          ((Work.Cohomology.localHomology_charted 8 (by norm_num) V.pt x j).2 hj)
      exact Module.Free.of_subsingleton ℤ _
  -- the local fundamental class, and the fact that it spans
  set cc : ↥((Work.Cohomology.relChains (TopCat.of V.pt)
      (Work.ThomBordism.FrameSigns.punct V x)).homology 8) :=
    Work.Orient.locClass (TopCat.of V.pt) 8 V.c x with hcc
  have hspan_cc : Submodule.span ℤ ({cc} : Set _) = ⊤ := by
    rw [hcc]
    exact V.c_fund x
  -- the homology isomorphisms of the inclusion of the chart source and of the translated chart
  haveI hExc : IsIso (HomologicalComplex.homologyMap
      (Work.ThomBordism.FrameSigns.chartSrcChain V i x hx) 8) :=
    Work.ThomBordism.FrameSigns.isIso_chartSrcChain V i hx
  haveI hTrans : IsIso (HomologicalComplex.homologyMap
      (Work.ThomBordism.FrameSigns.chartTransChain V i x hx) 8) :=
    Work.ThomBordism.FrameSigns.isIso_chartTransChain V i hx
  let gV : ↥((Work.Cohomology.relChains (TopCat.of V.pt)
      (Work.ThomBordism.FrameSigns.punct V x)).homology 8) →ₗ[ℤ]
      ↥((Work.Cohomology.relChains (TopCat.of ↥(Work.ThomBordism.FrameSigns.src V i))
        (Work.ThomBordism.FrameSigns.punctSrc V i x)).homology 8) :=
    ((CategoryTheory.inv (HomologicalComplex.homologyMap
      (Work.ThomBordism.FrameSigns.chartSrcChain V i x hx) 8)).hom)
  let gS : ↥((Work.Cohomology.relChains (TopCat.of ↥(Work.ThomBordism.FrameSigns.src V i))
      (Work.ThomBordism.FrameSigns.punctSrc V i x)).homology 8) →ₗ[ℤ]
      ↥(Work.ThomBordism.FrameSigns.modelC.homology 8) :=
    (HomologicalComplex.homologyMap
      (Work.ThomBordism.FrameSigns.chartTransChain V i x hx) 8).hom
  let g : ↥((Work.Cohomology.relChains (TopCat.of V.pt)
      (Work.ThomBordism.FrameSigns.punct V x)).homology 8) →ₗ[ℤ] ℤ :=
    (Work.ThomBordism.FrameSigns.dual0).comp (gS.comp gV)
  let zX : ↥((Work.Cohomology.relChains (TopCat.of ↥(Work.ThomBordism.FrameSigns.src V i))
      (Work.ThomBordism.FrameSigns.punctSrc V i x)).homology 8) := gV cc
  have hzXc : (HomologicalComplex.homologyMap
      (Work.ThomBordism.FrameSigns.chartSrcChain V i x hx) 8).hom zX = cc := by
    have h := congrArg (fun (k : (Work.Cohomology.relChains (TopCat.of V.pt)
        (Work.ThomBordism.FrameSigns.punct V x)).homology 8 ⟶
        (Work.Cohomology.relChains (TopCat.of V.pt)
          (Work.ThomBordism.FrameSigns.punct V x)).homology 8) => k.hom cc)
      (CategoryTheory.IsIso.inv_hom_id (HomologicalComplex.homologyMap
        (Work.ThomBordism.FrameSigns.chartSrcChain V i x hx) 8))
    simpa only [gV, ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id,
      LinearMap.id_apply] using h
  -- naturality of the pairing along the two pair maps, and the defining property of `chartCoh`
  have hG := Work.ThomBordism.FrameSigns.chartCoh_spec V i hx
  have hpair1 : (Work.Tubular.relKronH (TopCat.of V.pt)
        (Work.ThomBordism.FrameSigns.punct V x) 8)
        (Work.ThomBordism.FrameSigns.chartCoh V i x hx) cc
      = (Work.Tubular.relKronH (TopCat.of ↥(Work.ThomBordism.FrameSigns.src V i))
          (Work.ThomBordism.FrameSigns.punctSrc V i x) 8)
        ((Work.Thom.relCohMap (Work.ThomBordism.FrameSigns.srcIncl V i)
            (Work.ThomBordism.FrameSigns.punctSrc V i x)
            (Work.ThomBordism.FrameSigns.punct V x)
            (Work.ThomBordism.FrameSigns.punctSrc_mem V i x) ℤ 8).hom
          (Work.ThomBordism.FrameSigns.chartCoh V i x hx)) zX := by
    have hnat := Work.ThomBordism.FrameSigns.relKronH_natural_srcIncl V i hx
      (Work.ThomBordism.FrameSigns.chartCoh V i x hx) zX
    rw [hzXc] at hnat
    exact hnat.symm
  have hpair2 : (Work.Tubular.relKronH (TopCat.of ↥(Work.ThomBordism.FrameSigns.src V i))
        (Work.ThomBordism.FrameSigns.punctSrc V i x) 8)
        ((Work.Thom.relCohMap (Work.ThomBordism.FrameSigns.chartTrans V i x hx)
            (Work.ThomBordism.FrameSigns.punctSrc V i x) Work.ThomBordism.FrameSigns.E8p
            (Work.ThomBordism.FrameSigns.chartTrans_mem V i x hx) ℤ 8).hom
          Work.ThomBordism.FrameSigns.tau) zX
      = (Work.Tubular.relKronH (TopCat.of (EuclideanSpace ℝ (Fin 8)))
          Work.ThomBordism.FrameSigns.E8p 8) Work.ThomBordism.FrameSigns.tau
          ((HomologicalComplex.homologyMap
            (Work.ThomBordism.FrameSigns.chartTransChain V i x hx) 8).hom zX) :=
    Work.ThomBordism.FrameSigns.relKronH_natural_chartTrans V i hx
      Work.ThomBordism.FrameSigns.tau zX
  have hpv : Work.ThomBordism.FrameSigns.pairVal V i x hx = g cc := by
    show (Work.Tubular.relKronH (TopCat.of V.pt)
      (Work.ThomBordism.FrameSigns.punct V x) 8)
      (Work.ThomBordism.FrameSigns.chartCoh V i x hx)
      (Work.Orient.locClass (TopCat.of V.pt) 8 V.c x) = _
    rw [← hcc, hpair1, hG, hpair2, Work.ThomBordism.FrameSigns.tau_pair]
    rfl
  -- `pairVal` is the image of the generator `cc` under an isomorphism, hence a unit
  have hsurjG : Function.Surjective g := by
    intro z
    obtain ⟨w1, hw1⟩ := (CategoryTheory.ConcreteCategory.bijective_of_isIso
      (Work.ThomBordism.FrameSigns.e8.hom)).2 z
    obtain ⟨w2, hw2⟩ := (CategoryTheory.ConcreteCategory.bijective_of_isIso
      (HomologicalComplex.homologyMap
        (Work.ThomBordism.FrameSigns.chartTransChain V i x hx) 8)).2 w1
    obtain ⟨w3, hw3⟩ := (CategoryTheory.ConcreteCategory.bijective_of_isIso
      (CategoryTheory.inv (HomologicalComplex.homologyMap
        (Work.ThomBordism.FrameSigns.chartSrcChain V i x hx) 8))).2 w2
    refine ⟨w3, ?_⟩
    have h1 : gV w3 = w2 := hw3
    have h2 : gS w2 = w1 := hw2
    have h3 : Work.ThomBordism.FrameSigns.dual0 w1 = z := hw1
    show Work.ThomBordism.FrameSigns.dual0 (gS (gV w3)) = z
    rw [h1, h2]
    exact h3
  have hunit : IsUnit (Work.ThomBordism.FrameSigns.pairVal V i x hx) := by
    rw [hpv]
    exact isUnit_apply_of_surjective_of_span_singleton_eq_top g hsurjG hspan_cc
  have hval : Work.ThomBordism.FrameSigns.pairVal V i x hx = 1
      ∨ Work.ThomBordism.FrameSigns.pairVal V i x hx = -1 :=
    Int.isUnit_iff.mp hunit
  -- `⟨·, c⟩` is injective
  have hinj : Function.Injective (fun a : Work.Thom.RelCoh ℤ 8 V.pt
      (Work.ThomBordism.FrameSigns.punct V x) =>
      (Work.Tubular.relKronH (TopCat.of V.pt)
        (Work.ThomBordism.FrameSigns.punct V x) 8) a
        (Work.Orient.locClass (TopCat.of V.pt) 8 V.c x)) := by
    intro a b hab
    obtain ⟨e, he⟩ := Work.Tubular.exists_relKronH_eval_iso (TopCat.of V.pt)
      (Work.ThomBordism.FrameSigns.punct V x) 8 hfree
    have hab' : e a cc = e b cc := by
      rw [he a cc, he b cc, hcc]
      exact hab
    have hker : cc ∈ LinearMap.ker (e a - e b) := by
      rw [LinearMap.mem_ker, LinearMap.sub_apply, hab', sub_self]
    have hle : Submodule.span ℤ ({cc} : Set _) ≤ LinearMap.ker (e a - e b) :=
      Submodule.span_le.mpr (by rintro z rfl; exact hker)
    have h0 : e a - e b = 0 := by
      ext z
      exact LinearMap.mem_ker.mp (hle (by rw [hspan_cc]; exact Submodule.mem_top))
    exact e.injective (sub_eq_zero.mp h0)
  -- conclude
  have hchart : Work.ThomBordism.FrameSigns.chartCoh V i x hx
      = Work.ThomBordism.FrameSigns.pairVal V i x hx • o := by
    apply hinj
    show (Work.Tubular.relKronH (TopCat.of V.pt)
        (Work.ThomBordism.FrameSigns.punct V x) 8)
        (Work.ThomBordism.FrameSigns.chartCoh V i x hx)
        (Work.Orient.locClass (TopCat.of V.pt) 8 V.c x)
      = (Work.Tubular.relKronH (TopCat.of V.pt)
          (Work.ThomBordism.FrameSigns.punct V x) 8)
        (Work.ThomBordism.FrameSigns.pairVal V i x hx • o)
        (Work.Orient.locClass (TopCat.of V.pt) 8 V.c x)
    have h1 : (Work.Tubular.relKronH (TopCat.of V.pt)
        (Work.ThomBordism.FrameSigns.punct V x) 8)
        (Work.ThomBordism.FrameSigns.pairVal V i x hx • o)
        (Work.Orient.locClass (TopCat.of V.pt) 8 V.c x)
      = Work.ThomBordism.FrameSigns.pairVal V i x hx
        * (Work.Tubular.relKronH (TopCat.of V.pt)
            (Work.ThomBordism.FrameSigns.punct V x) 8) o
          (Work.Orient.locClass (TopCat.of V.pt) 8 V.c x) := by
      simp [map_zsmul, zsmul_eq_mul]
    rw [h1, ho, mul_one]
    rfl
  rw [hchart]
  rcases hval with h | h
  · have hs : (if 0 < Work.ThomBordism.FrameSigns.pairVal V i x hx then (1 : ℤ) else -1) = 1 := by
      rw [h]; norm_num
    rw [hs, h]
  · have hs : (if 0 < Work.ThomBordism.FrameSigns.pairVal V i x hx then (1 : ℤ) else -1) = -1 := by
      rw [h]; norm_num
    rw [hs, h]

end

end Work.ThomBordism.KeyLocal
