import Mathlib
import Submission.Work.ThomBordism.FrameSigns.Charts
import Submission.Work.ThomBordism.FrameSigns.relKronH_natural
import Submission.Work.Orient.Closed
import Submission.Work.Thom.ATools
import Submission.Work.Cohomology.capRelAux
import Submission.Work.Thom.relCohMap_homotopic

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.ThomBordism.FrameSigns

open Classical CategoryTheory

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

section FSaux

set_option backward.isDefEq.respectTransparency false



/-! ## The translated chart and the excision of a coordinate ball -/

/-- The relative chain map induced by the identity of pairs is the reduction map `relCokerMap`. -/
lemma relChainsMapOf_id_eq_relCokerMap (X : TopCat) (A B : Set X) (h : A ⊆ B) :
    Work.Cohomology.relChainsMapOf X X A B (TopCat.ofHom (ContinuousMap.id X))
      (Work.Cohomology.relMapSub A B (TopCat.ofHom (ContinuousMap.id X)) h)
      (Work.Cohomology.relMapSub_spec A B (TopCat.ofHom (ContinuousMap.id X)) h)
    = Work.Cohomology.relCokerMap X A B h := by
  apply (cancel_epi (Limits.cokernel.π (Work.Cohomology.inclChains X A))).mp
  rw [Work.Cohomology.capRel_cokernel_π_relChainsMapOf]
  rw [Work.Cohomology.relCokerMap_comp_π]
  rw [TopCat.ofHom_id, Work.Cohomology.chainMap_id', Category.id_comp]

/-- The relative pullback only depends on the pair map, not on the proof that it is a pair map. -/
lemma relCohMap_hcongr {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (A : Set X) (B : Set Y)
    (h h' : ∀ x ∈ A, f x ∈ B) (R : Type) [CommRing R] (n : ℕ) :
    Work.Thom.relCohMap f A B h R n = Work.Thom.relCohMap f A B h' R n := by
  show HomologicalComplex.homologyMap
      (Work.Cohomology.relComplexMap (X₁ := TopCat.of X) (X₂ := TopCat.of Y) R A B
        (TopCat.ofHom f) h) n
    = HomologicalComplex.homologyMap
      (Work.Cohomology.relComplexMap (X₁ := TopCat.of X) (X₂ := TopCat.of Y) R A B
        (TopCat.ofHom f) h') n
  rw [Work.Thom.relComplexMap_hcongrA A B (TopCat.ofHom f) h h' R]

/-- **The pairing with the local class of a fundamental class, localised at a set containing the
point.**  For `x ∈ K` and a class `b ∈ H⁸(M, M∖{x};ℤ)`, the pairing of `b` with the local class of a
global class `c` at `x` equals the pairing of the image of `b` in `H⁸(M, M∖K;ℤ)` with the class of
`c` at `K`.  This is `Work.ThomBordism.FrameSigns.relKronH_natural` for the map of pairs
`(M, M∖K) → (M, M∖{x})` together with `Work.Cohomology.relLocClass_restrict`. -/
lemma relKronH_pairing_restrict (M : TopCat) {K : Set M} {x : M} (hx : x ∈ K)
    (c : (Work.Cohomology.singularChains ℤ M).homology 8)
    (b : Work.Thom.RelCoh ℤ 8 M {y : M | y ≠ x})
    (hf : ∀ z ∈ (Kᶜ : Set M), (ContinuousMap.id M) z ∈ ({y : M | y ≠ x})) :
    (Work.Tubular.relKronH M {y : M | y ≠ x} 8) b (Work.Orient.locClass M 8 c x)
      = (Work.Tubular.relKronH M (Kᶜ) 8)
          ((Work.Thom.relCohMap (ContinuousMap.id M) (Kᶜ) {y : M | y ≠ x} hf ℤ 8).hom b)
          (Work.Orient.relClass M 8 c K) := by
  have himg : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (Work.Cohomology.relChainsMapOf M M (Kᶜ) ({y : M | y ≠ x})
        (TopCat.ofHom (ContinuousMap.id M))
        (TopCat.ofHom ⟨fun a => ⟨(ContinuousMap.id M) a, hf a a.2⟩,
          Continuous.subtype_mk ((ContinuousMap.id M).continuous.comp continuous_subtype_val)
            (fun a => hf a a.2)⟩)
        (Work.Cohomology.relMapSub_spec (Kᶜ) ({y : M | y ≠ x})
          (TopCat.ofHom (ContinuousMap.id M)) hf)) 8))
      (Work.Orient.relClass M 8 c K) = Work.Orient.locClass M 8 c x := by
    rw [show Work.Cohomology.relChainsMapOf M M (Kᶜ) {y : M | y ≠ x}
        (TopCat.ofHom (ContinuousMap.id M))
        (TopCat.ofHom ⟨fun a => ⟨(ContinuousMap.id M) a, hf a a.2⟩,
          Continuous.subtype_mk ((ContinuousMap.id M).continuous.comp continuous_subtype_val)
            (fun a => hf a a.2)⟩) _ =
        Work.Cohomology.relCokerMap M (Kᶜ) {y : M | y ≠ x} hf from ?_]
    · exact Work.Cohomology.relLocClass_restrict M 8 c (K := ({x} : Set M)) (K' := K)
        (Set.singleton_subset_iff.mpr hx)
    · apply (cancel_epi (Limits.cokernel.π (Work.Cohomology.inclChains M (Kᶜ)))).mp
      rw [Work.Cohomology.capRel_cokernel_π_relChainsMapOf]
      rw [Work.Cohomology.relCokerMap_comp_π]
      rw [TopCat.ofHom_id, Work.Cohomology.chainMap_id', Category.id_comp]
  have hnat := relKronH_natural (f := ContinuousMap.id M)
    (A := (Kᶜ : Set M)) (B := ({y : M | y ≠ x})) hf 8 b (Work.Orient.relClass M 8 c K)
  rw [himg] at hnat
  exact hnat.symm
/-- **Excision for a closed coordinate ball inside a chart source**: the inclusion of pairs
`(↥(src V i), src V i ∖ K) → (V, V∖K)` induces an isomorphism on relative cohomology (both
`src V i` and `Kᶜ` are open and they cover `V.pt` because `K ⊆ src V i`). -/
lemma isIso_exc_ball (V : Man8) (i : ChartIdx V) {K : Set V.pt} (hKc : IsClosed K)
    (hKs : K ⊆ src V i) :
    CategoryTheory.IsIso (Work.Thom.relCohMap (srcIncl V i)
      {z : ↥(src V i) | (z : V.pt) ∉ K} (Kᶜ) (fun z hz => hz) ℤ 8) := by
  have hcov : src V i ∪ Kᶜ = Set.univ := by
    ext y
    simp only [Set.mem_union, Set.mem_univ, iff_true]
    by_cases hy : y ∈ src V i
    · exact Or.inl hy
    · exact Or.inr (fun hyK => hy (hKs hyK))
  have hsub : ∀ y ∈ {z : ↥(src V i) | (z : V.pt) ∈ (Kᶜ : Set V.pt)},
      (Work.Cohomology.subtypeIncl (TopCat.of V.pt) (src V i)) y ∈ (Kᶜ : Set V.pt) :=
    fun y hy => hy
  have heq : (Work.Cohomology.subtypeIncl (TopCat.of V.pt) (src V i))
      = TopCat.ofHom (srcIncl V i) := rfl
  have key := Work.Cohomology.capRel_excision_isIso (TopCat.of V.pt) (src V i) (Kᶜ)
    (chartOf V i).1.open_source hKc.isOpen_compl hcov 8 hsub
  have hcongr := Work.Cohomology.capRel_relComplexMap_congr ℤ
    {z : ↥(src V i) | (z : V.pt) ∉ K} (Kᶜ) heq hsub (fun z hz => hz)
  have key' : CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.relComplexMap ℤ {z : ↥(src V i) | (z : V.pt) ∉ K} (Kᶜ)
        (TopCat.ofHom (srcIncl V i)) (fun z hz => hz)) 8) := by
    rw [← hcongr]
    exact key
  exact key'

/-- The translated chart restricted to the complement of a set containing its centre lands in the
punctured model space. -/
theorem chartTrans_mem_compl (V : Man8) (i : ChartIdx V) {K : Set V.pt} (hKs : K ⊆ src V i)
    {x : V.pt} (hx : x ∈ K) :
    ∀ z ∈ {z : ↥(src V i) | (z : V.pt) ∉ K}, chartTrans V i x (hKs hx) z ∈ E8p :=
  fun z hz => chartTrans_mem V i x (hKs hx) z (fun hzx => hz (hzx ▸ hx))

/-- **A coordinate ball is path connected**: two of its points are joined by a continuous path that
stays inside the ball.  (`K` is the preimage under a chart of a closed ball around the chart image
of its centre, intersected with the chart source; take the straight segment in that closed ball.) -/
theorem isCoordBall_path {n : ℕ} {M : TopCat} [ChartedSpace (EuclideanSpace ℝ (Fin n)) ↑M]
    {K : Set ↑M} (hK : IsCoordBall n M K) {x y : ↑M} (hx : x ∈ K) (hy : y ∈ K) :
    ∃ γ : C(unitInterval, ↑M), γ 0 = x ∧ γ 1 = y ∧ ∀ t, γ t ∈ K := by
  obtain ⟨z, r, hr, hball, rfl⟩ := hK
  set e := chartAt (EuclideanSpace ℝ (Fin n)) z with he
  have hxe : x ∈ e.source := hx.2
  have hye : y ∈ e.source := hy.2
  have hxr : e x ∈ Metric.closedBall (e z) (r / 2) := hx.1
  have hyr : e y ∈ Metric.closedBall (e z) (r / 2) := hy.1
  set a : unitInterval → EuclideanSpace ℝ (Fin n) :=
    fun t => (1 - (t : ℝ)) • e x + (t : ℝ) • e y with ha
  have ha_cont : Continuous a := by rw [ha]; fun_prop
  have ha_mem : ∀ t : unitInterval, a t ∈ Metric.closedBall (e z) (r / 2) := by
    intro t
    have h1 : a t ∈ segment ℝ (e x) (e y) := by
      rw [ha, segment_eq_image]
      exact ⟨(t : ℝ), ⟨t.2.1, t.2.2⟩, rfl⟩
    exact (convex_closedBall (e z) (r / 2)).segment_subset hxr hyr h1
  have ha_tgt : ∀ t : unitInterval, a t ∈ e.target := fun t =>
    hball (Metric.closedBall_subset_ball (by linarith) (ha_mem t))
  refine ⟨⟨fun t => e.symm (a t), ?_⟩, ?_, ?_, ?_⟩
  · exact e.continuousOn_symm.comp_continuous ha_cont ha_tgt
  · show e.symm (a 0) = x
    have h0 : a 0 = e x := by simp [ha]
    rw [h0, e.left_inv hxe]
  · show e.symm (a 1) = y
    have h1 : a 1 = e y := by simp [ha]
    rw [h1, e.left_inv hye]
  · intro t
    refine ⟨?_, e.mapsTo_symm (ha_tgt t)⟩
    simp only [ContinuousMap.coe_mk, Set.mem_preimage]
    rw [e.right_inv (ha_tgt t)]
    exact ha_mem t

/-- **The pullback along the translated chart does not depend on the centre** as long as the centre
moves along a path inside `K ⊆ src V i`.  The homotopy `H (t,z) = eᵢ z − eᵢ (γ t)` is a homotopy of
maps of pairs `(↥(src V i), src V i ∖ K) → (ℝ⁸, ℝ⁸∖0)`. -/
lemma chartTrans_pullback_eq_of_path (V : Man8) (i : ChartIdx V) {K : Set V.pt}
    (hKs : K ⊆ src V i) {x y : V.pt} (hx : x ∈ K) (hy : y ∈ K)
    (χx : ∀ z ∈ {z : ↥(src V i) | (z : V.pt) ∉ K}, chartTrans V i x (hKs hx) z ∈ E8p)
    (χy : ∀ z ∈ {z : ↥(src V i) | (z : V.pt) ∉ K}, chartTrans V i y (hKs hy) z ∈ E8p)
    (γ : C(unitInterval, V.pt)) (hγ0 : γ 0 = x) (hγ1 : γ 1 = y) (hγK : ∀ t, γ t ∈ K)
    (ξ : Work.Thom.RelCoh ℤ 8 (EuclideanSpace ℝ (Fin 8)) E8p) :
    (Work.Thom.relCohMap (chartTrans V i x (hKs hx)) {z : ↥(src V i) | (z : V.pt) ∉ K} E8p
        χx ℤ 8).hom ξ
      = (Work.Thom.relCohMap (chartTrans V i y (hKs hy)) {z : ↥(src V i) | (z : V.pt) ∉ K} E8p
        χy ℤ 8).hom ξ := by
  have hγs : ∀ t, γ t ∈ src V i := fun t => hKs (hγK t)
  let δ : C(unitInterval, ↥(src V i)) :=
    ⟨fun t => ⟨γ t, hγs t⟩, Continuous.subtype_mk γ.continuous hγs⟩
  have hcont1 : Continuous fun p : unitInterval × ↥(src V i) => chartMap V i (p.2 : V.pt) := by
    have h : Continuous fun p : unitInterval × ↥(src V i) =>
        chartTrans V i x (hKs hx) p.2 + chartMap V i x :=
      ((chartTrans V i x (hKs hx)).continuous.comp continuous_snd).add continuous_const
    have h2 : (fun p : unitInterval × ↥(src V i) =>
          chartTrans V i x (hKs hx) p.2 + chartMap V i x)
        = fun p : unitInterval × ↥(src V i) => chartMap V i (p.2 : V.pt) := by
      funext p
      rw [chartTrans_apply, sub_add_cancel]
    rw [h2] at h
    exact h
  have hcont2 : Continuous fun p : unitInterval × ↥(src V i) => chartMap V i (γ p.1) := by
    have h : Continuous fun p : unitInterval × ↥(src V i) =>
        chartTrans V i x (hKs hx) (δ p.1) + chartMap V i x :=
      (((chartTrans V i x (hKs hx)).continuous.comp δ.continuous).comp continuous_fst).add
        continuous_const
    have h2 : (fun p : unitInterval × ↥(src V i) =>
          chartTrans V i x (hKs hx) (δ p.1) + chartMap V i x)
        = fun p : unitInterval × ↥(src V i) => chartMap V i (γ p.1) := by
      funext p
      rw [chartTrans_apply, sub_add_cancel]
      rfl
    rw [h2] at h
    exact h
  have hHfun : Continuous fun p : unitInterval × ↥(src V i) =>
      chartMap V i (p.2 : V.pt) - chartMap V i (γ p.1) := hcont1.sub hcont2
  let hH : ContinuousMap.Homotopy (chartTrans V i x (hKs hx)) (chartTrans V i y (hKs hy)) :=
    ContinuousMap.Homotopy.mk
      ⟨fun p : unitInterval × ↥(src V i) =>
          chartMap V i (p.2 : V.pt) - chartMap V i (γ p.1), hHfun⟩
      (fun z => by
        show chartMap V i (z : V.pt) - chartMap V i (γ 0) = chartTrans V i x (hKs hx) z
        rw [hγ0, chartTrans_apply])
      (fun z => by
        show chartMap V i (z : V.pt) - chartMap V i (γ 1) = chartTrans V i y (hKs hy) z
        rw [hγ1, chartTrans_apply])
  have hHmem : ∀ t z, z ∈ {z : ↥(src V i) | (z : V.pt) ∉ K} → hH (t, z) ∈ E8p := by
    intro t z hz
    show chartMap V i (z : V.pt) - chartMap V i (γ t) ∈ E8p
    intro hzero
    have h1 : chartMap V i (z : V.pt) = chartMap V i (γ t) := sub_eq_zero.mp hzero
    have h2 : (chartOf V i).1.symm (chartMap V i (z : V.pt)) = (z : V.pt) :=
      (chartOf V i).1.left_inv z.2
    have h3 : (chartOf V i).1.symm (chartMap V i (γ t)) = γ t :=
      (chartOf V i).1.left_inv (hγs t)
    exact hz (by rw [← h2, h1, h3]; exact hγK t)
  have hkey := Work.Thom.relCohMap_homotopic {z : ↥(src V i) | (z : V.pt) ∉ K} E8p
    χx χy hH hHmem ℤ 8
  exact congrArg (fun (g : Work.Thom.RelCoh ℤ 8 (EuclideanSpace ℝ (Fin 8)) E8p ⟶
      Work.Thom.RelCoh ℤ 8 ↥(src V i) {z : ↥(src V i) | (z : V.pt) ∉ K}) => g.hom ξ) hkey

/-- **The image of the chart class at `x ∈ K` under the restriction `H⁸(V,V∖{x}) → H⁸(V,V∖K)`.**
It is the inverse image under the excision isomorphism `H⁸(V,V∖K) ≅ H⁸(↥(src V i), src V i ∖ K)` of the
pullback of `ξ` along the translated chart, viewed as a map of pairs
`(↥(src V i), src V i ∖ K) → (ℝ⁸, ℝ⁸∖0)`. -/
theorem excision_compute (V : Man8) (i : ChartIdx V) {K : Set V.pt}
    (hKs : K ⊆ src V i) {x : V.pt} (hx : x ∈ K)
    (hf_x : ∀ z ∈ (Kᶜ : Set V.pt), (ContinuousMap.id V.pt) z ∈ punct V x)
    (χxK : ∀ z ∈ {z : ↥(src V i) | (z : V.pt) ∉ K}, chartTrans V i x (hKs hx) z ∈ E8p) :
    (Work.Thom.relCohMap (srcIncl V i) {z : ↥(src V i) | (z : V.pt) ∉ K} (Kᶜ)
        (fun z hz => hz) ℤ 8).hom
      ((Work.Thom.relCohMap (ContinuousMap.id V.pt) (Kᶜ) (punct V x) hf_x ℤ 8).hom
        (chartCoh V i x (hKs hx)))
    = (Work.Thom.relCohMap (chartTrans V i x (hKs hx)) {z : ↥(src V i) | (z : V.pt) ∉ K} E8p
        χxK ℤ 8).hom tau := by
  haveI : CategoryTheory.IsIso (Work.Thom.relCohMap (srcIncl V i) (punctSrc V i x) (punct V x)
      (punctSrc_mem V i x) ℤ 8) := isIso_exc V i x (hKs hx)
  have hβf : ∀ z ∈ {z : ↥(src V i) | (z : V.pt) ∉ K},
      (ContinuousMap.id (↥(src V i))) z ∈ punctSrc V i x :=
    fun z hz => fun hzx => hz (hzx ▸ hx)
  have hgf1 : ∀ z ∈ {z : ↥(src V i) | (z : V.pt) ∉ K},
      (ContinuousMap.id V.pt) ((srcIncl V i) z) ∈ punct V x :=
    fun z hz => hf_x ((srcIncl V i) z) hz
  have hgf2 : ∀ z ∈ {z : ↥(src V i) | (z : V.pt) ∉ K},
      (srcIncl V i) ((ContinuousMap.id (↥(src V i))) z) ∈ punct V x :=
    fun z hz => hf_x ((srcIncl V i) z) hz
  have hgf3 : ∀ z ∈ {z : ↥(src V i) | (z : V.pt) ∉ K},
      (chartTrans V i x (hKs hx)) ((ContinuousMap.id (↥(src V i))) z) ∈ E8p :=
    fun z hz => χxK z hz
  -- (i) the excision square
  have hsq : (Work.Thom.relCohMap (ContinuousMap.id V.pt) (Kᶜ) (punct V x) hf_x ℤ 8)
      ≫ (Work.Thom.relCohMap (srcIncl V i) {z : ↥(src V i) | (z : V.pt) ∉ K} (Kᶜ)
          (fun z hz => hz) ℤ 8)
      = (Work.Thom.relCohMap (srcIncl V i) (punctSrc V i x) (punct V x)
          (punctSrc_mem V i x) ℤ 8)
        ≫ (Work.Thom.relCohMap (ContinuousMap.id (↥(src V i)))
            {z : ↥(src V i) | (z : V.pt) ∉ K} (punctSrc V i x) hβf ℤ 8) := by
    have hL : (Work.Thom.relCohMap (ContinuousMap.id V.pt) (Kᶜ) (punct V x) hf_x ℤ 8)
        ≫ (Work.Thom.relCohMap (srcIncl V i) {z : ↥(src V i) | (z : V.pt) ∉ K} (Kᶜ)
            (fun z hz => hz) ℤ 8)
        = (Work.Thom.relCohMap ((ContinuousMap.id V.pt).comp (srcIncl V i))
            {z : ↥(src V i) | (z : V.pt) ∉ K} (punct V x) hgf1 ℤ 8) :=
      Work.Thom.relCohMap_compA (A := {z : ↥(src V i) | (z : V.pt) ∉ K})
        (B := (Kᶜ : Set V.pt)) (C := punct V x) (srcIncl V i) (ContinuousMap.id V.pt)
        (fun z hz => hz) hf_x hgf1 ℤ 8
    have hR : (Work.Thom.relCohMap (srcIncl V i) (punctSrc V i x) (punct V x)
          (punctSrc_mem V i x) ℤ 8)
        ≫ (Work.Thom.relCohMap (ContinuousMap.id (↥(src V i)))
            {z : ↥(src V i) | (z : V.pt) ∉ K} (punctSrc V i x) hβf ℤ 8)
        = (Work.Thom.relCohMap ((srcIncl V i).comp (ContinuousMap.id (↥(src V i))))
            {z : ↥(src V i) | (z : V.pt) ∉ K} (punct V x) hgf2 ℤ 8) :=
      Work.Thom.relCohMap_compA (A := {z : ↥(src V i) | (z : V.pt) ∉ K})
        (B := punctSrc V i x) (C := punct V x) (ContinuousMap.id (↥(src V i))) (srcIncl V i)
        hβf (punctSrc_mem V i x) hgf2 ℤ 8
    rw [hL, hR,
      Work.Thom.relCohMap_congrA {z : ↥(src V i) | (z : V.pt) ∉ K} (punct V x)
        (ContinuousMap.id_comp (f := srcIncl V i)) hgf1 hgf1 ℤ 8,
      Work.Thom.relCohMap_congrA {z : ↥(src V i) | (z : V.pt) ∉ K} (punct V x)
        (ContinuousMap.comp_id (f := srcIncl V i)) hgf2 hgf2 ℤ 8]
  -- (ii) the unfolding of `chartCoh`
  have hcx : (Work.Thom.relCohMap (srcIncl V i) (punctSrc V i x) (punct V x)
        (punctSrc_mem V i x) ℤ 8).hom (chartCoh V i x (hKs hx))
      = (Work.Thom.relCohMap (chartTrans V i x (hKs hx)) (punctSrc V i x) E8p
          (chartTrans_mem V i x (hKs hx)) ℤ 8).hom tau := by
    have h := congrArg (fun (g : Work.Thom.RelCoh ℤ 8 ↥(src V i) (punctSrc V i x) ⟶
        Work.Thom.RelCoh ℤ 8 ↥(src V i) (punctSrc V i x)) =>
        g.hom ((Work.Thom.relCohMap (chartTrans V i x (hKs hx)) (punctSrc V i x) E8p
          (chartTrans_mem V i x (hKs hx)) ℤ 8).hom tau))
      (IsIso.inv_hom_id (Work.Thom.relCohMap (srcIncl V i) (punctSrc V i x) (punct V x)
        (punctSrc_mem V i x) ℤ 8))
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply,
      chartCoh] using h
  -- (iii) the composite of the two pullbacks
  have hcomp : (Work.Thom.relCohMap (ContinuousMap.id (↥(src V i)))
        {z : ↥(src V i) | (z : V.pt) ∉ K} (punctSrc V i x) hβf ℤ 8).hom
      ((Work.Thom.relCohMap (chartTrans V i x (hKs hx)) (punctSrc V i x) E8p
        (chartTrans_mem V i x (hKs hx)) ℤ 8).hom tau)
      = (Work.Thom.relCohMap (chartTrans V i x (hKs hx))
          {z : ↥(src V i) | (z : V.pt) ∉ K} E8p χxK ℤ 8).hom tau := by
    have h1 : (Work.Thom.relCohMap (chartTrans V i x (hKs hx)) (punctSrc V i x) E8p
          (chartTrans_mem V i x (hKs hx)) ℤ 8)
        ≫ (Work.Thom.relCohMap (ContinuousMap.id (↥(src V i)))
            {z : ↥(src V i) | (z : V.pt) ∉ K} (punctSrc V i x) hβf ℤ 8)
        = (Work.Thom.relCohMap (chartTrans V i x (hKs hx))
            {z : ↥(src V i) | (z : V.pt) ∉ K} E8p χxK ℤ 8) := by
      have hL : (Work.Thom.relCohMap (chartTrans V i x (hKs hx)) (punctSrc V i x) E8p
            (chartTrans_mem V i x (hKs hx)) ℤ 8)
          ≫ (Work.Thom.relCohMap (ContinuousMap.id (↥(src V i)))
              {z : ↥(src V i) | (z : V.pt) ∉ K} (punctSrc V i x) hβf ℤ 8)
          = (Work.Thom.relCohMap ((chartTrans V i x (hKs hx)).comp
              (ContinuousMap.id (↥(src V i))))
              {z : ↥(src V i) | (z : V.pt) ∉ K} E8p hgf3 ℤ 8) :=
        Work.Thom.relCohMap_compA (A := {z : ↥(src V i) | (z : V.pt) ∉ K})
          (B := punctSrc V i x) (C := E8p) (ContinuousMap.id (↥(src V i)))
          (chartTrans V i x (hKs hx)) hβf (chartTrans_mem V i x (hKs hx)) hgf3 ℤ 8
      rw [hL,
        Work.Thom.relCohMap_congrA {z : ↥(src V i) | (z : V.pt) ∉ K} E8p
          (ContinuousMap.comp_id (f := chartTrans V i x (hKs hx))) hgf3 hgf3 ℤ 8]
    have h2 := congrArg (fun (g : Work.Thom.RelCoh ℤ 8 (EuclideanSpace ℝ (Fin 8)) E8p ⟶
        Work.Thom.RelCoh ℤ 8 ↥(src V i) {z : ↥(src V i) | (z : V.pt) ∉ K}) => g.hom tau) h1
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h2
  -- assembly
  have hkey : (Work.Thom.relCohMap (srcIncl V i) {z : ↥(src V i) | (z : V.pt) ∉ K} (Kᶜ)
        (fun z hz => hz) ℤ 8).hom
      ((Work.Thom.relCohMap (ContinuousMap.id V.pt) (Kᶜ) (punct V x) hf_x ℤ 8).hom
        (chartCoh V i x (hKs hx)))
      = (Work.Thom.relCohMap (ContinuousMap.id (↥(src V i)))
          {z : ↥(src V i) | (z : V.pt) ∉ K} (punctSrc V i x) hβf ℤ 8).hom
        ((Work.Thom.relCohMap (chartTrans V i x (hKs hx)) (punctSrc V i x) E8p
          (chartTrans_mem V i x (hKs hx)) ℤ 8).hom tau) := by
    have h := congrArg (fun (g : Work.Thom.RelCoh ℤ 8 V.pt (punct V x) ⟶
        Work.Thom.RelCoh ℤ 8 ↥(src V i) {z : ↥(src V i) | (z : V.pt) ∉ K}) =>
        g.hom (chartCoh V i x (hKs hx))) hsq
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, hcx] using h
  rw [hkey, hcomp]

/-- The chart frame sign is constant on a coordinate ball contained in the chart source.

This is the local constancy of `frameSign V i` on `src V i`, hence (with
`Work.Orient.exists_isCoordBall_mem_nhds`) the continuity of `frameSign V i` on `src V i`.

Route.  Let `K` be the coordinate ball, `M := TopCat.of V.pt`.  For `x ∈ K ⊆ src V i`, by naturality
of the Kronecker pairing (`Work.ThomBordism.FrameSigns.relKronH_natural`) applied to the map of
pairs `id : (M, Kᶜ) → (M, {x}ᶜ)` and `Work.Orient.relClass_restrict`,

  `⟨chartCoh V i x hx, locClass M 8 V.c x⟩ = ⟨ρ_x^K (chartCoh V i x hx), relClass M 8 V.c K⟩`,

where `ρ_x^K : H⁸(M,{x}ᶜ) → H⁸(M,Kᶜ)` is `relCohMap (id M) Kᶜ ({x}ᶜ)`.  Next, by naturality of the
inverse of the excision isomorphism `isIso_exc` (its forward square commutes by
`Work.Thom.relCohMap_compA`, and the inverse of a natural isomorphism is natural),

  `ρ_x^K (chartCoh V i x hx) = (exc_K)⁻¹ ((chartTrans V i x hx restricted to K)^* τ)`,

where `exc_K` is the excision isomorphism `H⁸(M,Kᶜ) ≅ H⁸(↥(src V i), (src V i)∖K)`.  Finally the maps
of pairs `chartTrans V i x hx` and `chartTrans V i y hy` restricted to `(src V i, src V i ∖ K)` are
homotopic through maps of pairs (move the centre `x` to `y` along a path in the path-connected `K`;
`eᵢ` is injective on `src V i`, so `eᵢ z ≠ eᵢ (γ t)` for `z ∉ K`), so
`Work.Thom.relCohMap_homotopic` gives `(chartTrans V i x)^* τ = (chartTrans V i y)^* τ`; hence the two
pairing values, and therefore the two `frameSign` values, agree. -/
theorem frameSign_eq_of_isCoordBall (V : Man8) (i : ChartIdx V)
    {K : Set V.pt} (hK : IsCoordBall 8 (TopCat.of V.pt) K) (hKs : K ⊆ src V i)
    {x y : V.pt} (hx : x ∈ K) (hy : y ∈ K) :
    frameSign V i x = frameSign V i y := by
  have hKc : IsClosed K := hK.isCompact.isClosed
  have hf_x0 : ∀ z, z ∈ (Kᶜ : Set V.pt) → z ∈ punct V x := fun z hz hzx => hz (hzx ▸ hx)
  have hf_y0 : ∀ z, z ∈ (Kᶜ : Set V.pt) → z ∈ punct V y := fun z hz hzy => hz (hzy ▸ hy)
  have hf_x : ∀ z ∈ (Kᶜ : Set V.pt), (ContinuousMap.id V.pt) z ∈ punct V x :=
    fun z hz => hf_x0 z hz
  have hf_y : ∀ z ∈ (Kᶜ : Set V.pt), (ContinuousMap.id V.pt) z ∈ punct V y :=
    fun z hz => hf_y0 z hz
  obtain ⟨γ, hγ0, hγ1, hγK⟩ := isCoordBall_path hK hx hy
  haveI : CategoryTheory.IsIso (Work.Thom.relCohMap (srcIncl V i)
      {z : ↥(src V i) | (z : V.pt) ∉ K} (Kᶜ) (fun z hz => hz) ℤ 8) :=
    isIso_exc_ball V i hKc hKs
  have hinj : Function.Injective (ConcreteCategory.hom (Work.Thom.relCohMap (srcIncl V i)
      {z : ↥(src V i) | (z : V.pt) ∉ K} (Kᶜ) (fun z hz => hz) ℤ 8)) :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  have hEq : (Work.Thom.relCohMap (ContinuousMap.id V.pt) (Kᶜ) (punct V x) hf_x ℤ 8).hom
        (chartCoh V i x (hKs hx))
      = (Work.Thom.relCohMap (ContinuousMap.id V.pt) (Kᶜ) (punct V y) hf_y ℤ 8).hom
        (chartCoh V i y (hKs hy)) := by
    refine hinj ?_
    rw [excision_compute V i hKs hx hf_x (chartTrans_mem_compl V i hKs hx),
        excision_compute V i hKs hy hf_y (chartTrans_mem_compl V i hKs hy),
        chartTrans_pullback_eq_of_path V i hKs hx hy (chartTrans_mem_compl V i hKs hx)
          (chartTrans_mem_compl V i hKs hy) γ hγ0 hγ1 hγK tau]
  have hp_x := relKronH_pairing_restrict (TopCat.of V.pt) (K := K) (x := x) hx V.c
    (chartCoh V i x (hKs hx)) hf_x
  have hp_y := relKronH_pairing_restrict (TopCat.of V.pt) (K := K) (x := y) hy V.c
    (chartCoh V i y (hKs hy)) hf_y
  have hp_x' : (Work.Tubular.relKronH (TopCat.of V.pt) (punct V x) 8) (chartCoh V i x (hKs hx))
        (Work.Orient.locClass (TopCat.of V.pt) 8 V.c x)
      = (Work.Tubular.relKronH (TopCat.of V.pt) (Kᶜ) 8)
        ((Work.Thom.relCohMap (ContinuousMap.id V.pt) (Kᶜ) (punct V x) hf_x ℤ 8).hom
          (chartCoh V i x (hKs hx)))
        (Work.Orient.relClass (TopCat.of V.pt) 8 V.c K) := hp_x
  have hp_y' : (Work.Tubular.relKronH (TopCat.of V.pt) (punct V y) 8) (chartCoh V i y (hKs hy))
        (Work.Orient.locClass (TopCat.of V.pt) 8 V.c y)
      = (Work.Tubular.relKronH (TopCat.of V.pt) (Kᶜ) 8)
        ((Work.Thom.relCohMap (ContinuousMap.id V.pt) (Kᶜ) (punct V y) hf_y ℤ 8).hom
          (chartCoh V i y (hKs hy)))
        (Work.Orient.relClass (TopCat.of V.pt) 8 V.c K) := hp_y
  have hpair : pairVal V i x (hKs hx) = pairVal V i y (hKs hy) := by
    show (Work.Tubular.relKronH (TopCat.of V.pt) (punct V x) 8) (chartCoh V i x (hKs hx))
        (Work.Orient.locClass (TopCat.of V.pt) 8 V.c x)
      = (Work.Tubular.relKronH (TopCat.of V.pt) (punct V y) 8) (chartCoh V i y (hKs hy))
        (Work.Orient.locClass (TopCat.of V.pt) 8 V.c y)
    rw [hp_x', hp_y', hEq]
  rw [frameSign_of_mem V i x (hKs hx), frameSign_of_mem V i y (hKs hy), hpair]

end FSaux

end

end Work.ThomBordism.FrameSigns
