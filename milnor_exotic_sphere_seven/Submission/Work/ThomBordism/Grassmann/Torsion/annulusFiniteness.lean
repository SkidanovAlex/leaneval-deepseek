import Mathlib
import Submission.Work.ThomBordism.Grassmann.Torsion.annulusGeom
import Submission.Work.ThomBordism.Grassmann.Torsion.finiteTransfer
import Submission.Work.ThomBordism.Grassmann.Torsion.finiteCoverHomologyFinite
import Submission.Work.ThomBordism.Grassmann.Torsion.goodCoverSubordinate
import Submission.Work.ThomBordism.compactHomologyFinite
import Submission.Work.ThomBordism.Grassmann.Smooth.Chart.Model

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open scoped Manifold ContDiff
open Module

/-!
# Finite generation of the homology of the annulus

`annSet k m = {p : TM k m | 1 < fibN p ∧ fibN p < 2}` is covered by the finitely many chart pieces
of a finite good cover of `OG k m` subordinate to the chart base sets; over each piece the bundle is
trivial, so the piece is homeomorphic to `U × S^{k-1} × (1,2)` (`annOverHomeomorph`), whose homology
is finitely generated.  `finiteCoverHomologyFinite` then gives finite generation for `annSet`.
-/

namespace Work.ThomBordism.Grassmann.Torsion

open Work.ThomBordism.Grassmann

noncomputable section

variable {k m : ℕ}

/-! ## The chart at a point of the Grassmannian, recording its index -/

/-- The chart index of the chart chosen at a point of the Grassmannian by the `ChartedSpace`
instance. -/
noncomputable def chartIdxAt (y : OG k m) : ChartIdx k m :=
  (Classical.choose (Smooth.exists_mem_chartSrc y)).1

/-- The orientation sign of the chart chosen at a point of the Grassmannian. -/
noncomputable def chartSignAt (y : OG k m) : ℝ :=
  (Classical.choose (Smooth.exists_mem_chartSrc y)).2

theorem chartAt_eq_euclidChart (y : OG k m) :
    (chartAt (EuclideanSpace ℝ (Fin (k * m))) y)
      = Smooth.euclidChart (chartIdxAt y) (chartSignAt y) := rfl

/-- The source of a Grassmann chart is contained in the base set of its index. -/
theorem chart_source_subset (S : ChartIdx k m) (ε : ℝ) :
    (Smooth.euclidChart (k := k) (m := m) S ε).source ⊆ baseSet S := by
  intro x hx
  rw [Smooth.euclidChart, OpenPartialHomeomorph.trans_source] at hx
  exact (Smooth.mem_chartSrc.mp hx.1).1

/-! ## The homology of the sphere and of the interval -/

theorem sphereHomologyFiniteAmb {k : ℕ} (hk : 1 ≤ k) (n : ℕ) :
    Module.Finite ℤ
      ((Work.Cohomology.singularChains ℤ (TopCat.of ↥(Metric.sphere (0 : Amb k) 1))).homology n) := by
  haveI : Fact (Module.finrank ℝ (Amb k) = (k - 1) + 1) :=
    Fact.mk (by rw [finrank_euclideanSpace_fin, Nat.sub_add_cancel hk])
  haveI : CompactSpace ↥(Metric.sphere (0 : Amb k) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere (0 : Amb k) 1)
  exact Work.ThomBordism.compactHomologyFinite (n := k - 1) (k := n)
    (X := ↥(Metric.sphere (0 : Amb k) 1))

theorem intervalContractible : ContractibleSpace ↥(Set.Ioo (1 : ℝ) 2) :=
  (convex_Ioo 1 2).contractibleSpace ⟨3 / 2, by rw [Set.mem_Ioo]; norm_num⟩

/-! ## The annulus piece over a subset of a chart

The points of `↥(annSet k m)` projecting into `W` are the points of the annulus over `W`. -/

/-- The points of `↥(annSet k m)` projecting into `W` are the points of the annulus over `W`. -/
noncomputable def annPieceHomeo (W : Set (OG k m)) :
    ↥(annOver k m W) ≃ₜ
      ↥{p : ↥(annSet k m) | (tautologicalBundle k m).proj p.1 ∈ W} where
  toFun p := ⟨⟨p.1, ⟨p.2.1, p.2.2.1⟩⟩, p.2.2.2⟩
  invFun q := ⟨q.1.1, q.1.2.1, q.1.2.2, q.2⟩
  left_inv p := rfl
  right_inv q := rfl
  continuous_toFun :=
    Continuous.subtype_mk
      (Continuous.subtype_mk continuous_subtype_val fun p => ⟨p.2.1, p.2.2.1⟩)
      fun p => p.2.2.2
  continuous_invFun :=
    Continuous.subtype_mk
      (continuous_subtype_val.comp continuous_subtype_val)
      fun q => ⟨q.1.2.1, q.1.2.2, q.2⟩

/-- **Finite generation of the homology of the annulus piece over `W`**, given that nonempty `W`
is contractible. -/
theorem annOverHomologyFinite (S : ChartIdx k m) {W : Set (OG k m)} (hW : W ⊆ baseSet S)
    (hWc : W.Nonempty → ContractibleSpace ↥W) (n : ℕ) :
    Module.Finite ℤ
      ((Work.Cohomology.singularChains ℤ (TopCat.of ↥(annOver k m W))).homology n) := by
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0
    have hemp : annOver 0 m W = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro p hp
      haveI : Subsingleton ((tautologicalBundle 0 m).Fiber p.1) :=
        (inferInstance : Subsingleton (EuclideanSpace ℝ (Fin 0)))
      have hp1 : 1 < fibN 0 m p := hp.1
      have h2 : fibN 0 m p = 0 := (fibN_eq_zero_iff 0 m p).mpr (Subsingleton.elim _ _)
      rw [h2] at hp1
      exact absurd hp1 (by norm_num)
    rw [hemp]
    exact Work.ThomBordism.fgch_moduleFinite_homology_of_contractibleOrEmpty
      ↥(∅ : Set (TM 0 m)) (fun hc => by obtain ⟨x, hx⟩ := hc; exact absurd hx (by simp)) n
  · rcases W.eq_empty_or_nonempty with h | hne
    · subst h
      have hemp : annOver k m (∅ : Set (OG k m)) = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        intro p hp
        exact hp.2.2
      rw [hemp]
      exact Work.ThomBordism.fgch_moduleFinite_homology_of_contractibleOrEmpty
        ↥(∅ : Set (TM k m)) (fun hc => by obtain ⟨x, hx⟩ := hc; exact absurd hx (by simp)) n
    · haveI : ContractibleSpace ↥W := hWc hne
      haveI : ContractibleSpace ↥(Set.Ioo (1 : ℝ) 2) := intervalContractible
      have hIS : Module.Finite ℤ ((Work.Cohomology.singularChains ℤ
          (TopCat.of (↥(Set.Ioo (1 : ℝ) 2) × ↥(Metric.sphere (0 : Amb k) 1)))).homology n) :=
        homologyFinite_prod_contractible (X := ↥(Set.Ioo (1 : ℝ) 2))
          (Y := ↥(Metric.sphere (0 : Amb k) 1)) n (sphereHomologyFiniteAmb hkpos n)
      have hSI : Module.Finite ℤ ((Work.Cohomology.singularChains ℤ
          (TopCat.of (↥(Metric.sphere (0 : Amb k) 1) × ↥(Set.Ioo (1 : ℝ) 2)))).homology n) :=
        moduleFinite_homology_of_homeomorphCM (Homeomorph.prodComm _ _) n hIS
      have hWSI : Module.Finite ℤ ((Work.Cohomology.singularChains ℤ
          (TopCat.of (↥W × (↥(Metric.sphere (0 : Amb k) 1)
            × ↥(Set.Ioo (1 : ℝ) 2))))).homology n) :=
        homologyFinite_prod_contractible (X := ↥W)
          (Y := ↥(Metric.sphere (0 : Amb k) 1) × ↥(Set.Ioo (1 : ℝ) 2)) n hSI
      exact moduleFinite_homology_of_homeomorphCM (annOverHomeomorph S hW).symm n hWSI

/-! ## The finite good cover of the Grassmannian, and the annulus -/

/-- **The homology of the annulus of the tautological bundle is finitely generated.** -/
theorem annSetHomologyFinite (k m n : ℕ) :
    Module.Finite ℤ
      ((Work.Cohomology.singularChains ℤ (TopCat.of ↥(annSet k m))).homology n) := by
  classical
  -- ## 1. A finite chart cover of `OG k m`
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun y : OG k m => (chartAt (EuclideanSpace ℝ (Fin (k * m))) y).source)
    (fun y => (chartAt (EuclideanSpace ℝ (Fin (k * m))) y).open_source)
    (by
      intro x _
      exact Set.mem_iUnion.mpr ⟨x, mem_chart_source _ x⟩)
  let y : Fin s.card → OG k m := fun j => (s.equivFin.symm j : OG k m)
  let c : Fin s.card → EuclideanSpace ℝ (Fin (k * m)) :=
    fun j => chartAt (EuclideanSpace ℝ (Fin (k * m))) (y j) (y j)
  let ψ : Fin s.card → OpenPartialHomeomorph (OG k m) (EuclideanSpace ℝ (Fin (k * m))) :=
    fun j => (chartAt (EuclideanSpace ℝ (Fin (k * m))) (y j)).trans
      (Work.EmbeddedSpheres.TubeProject.subRightOpenPartialHomeomorph (c j))
  let W : Fin s.card → Set (OG k m) := fun j => baseSet (chartIdxAt (y j))
  have hψmem : ∀ j : Fin s.card, ψ j ∈ IsManifold.maximalAtlas
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k * m)))) (∞ : ℕ∞ω) (OG k m) := by
    intro j
    exact Work.EmbeddedSpheres.TubeProject.trans_mem_maximalAtlas_of_mem_groupoid
      (e := chartAt (EuclideanSpace ℝ (Fin (k * m))) (y j))
      (f := Work.EmbeddedSpheres.TubeProject.subRightOpenPartialHomeomorph (c j))
      (IsManifold.chart_mem_maximalAtlas (I := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k * m))))
        (n := (∞ : ℕ∞ω)) (y j))
      (Work.EmbeddedSpheres.TubeProject.subRight_mem_contDiffGroupoid (∞ : ℕ∞ω) (c j))
  have hψcov : (⋃ j : Fin s.card, (ψ j).source) = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro x
    have hx : x ∈ (⋃ i ∈ s, (chartAt (EuclideanSpace ℝ (Fin (k * m))) i).source) :=
      hs (Set.mem_univ x)
    rw [Set.mem_iUnion₂] at hx
    obtain ⟨i, hi, hxi⟩ := hx
    refine Set.mem_iUnion.mpr ⟨s.equivFin ⟨i, hi⟩, ?_⟩
    have hyi : y (s.equivFin ⟨i, hi⟩) = i := by
      simp only [y]; rw [Equiv.symm_apply_apply]
    have hz' : x ∈ ((chartAt (EuclideanSpace ℝ (Fin (k * m))) (y (s.equivFin ⟨i, hi⟩))).trans
        (Work.EmbeddedSpheres.TubeProject.subRightOpenPartialHomeomorph
          (c (s.equivFin ⟨i, hi⟩)))).source := by
      rw [OpenPartialHomeomorph.trans_source, hyi]
      exact ⟨hxi, Set.mem_univ _⟩
    exact hz'
  have hy0 : ∀ j : Fin s.card, y j ∈ (ψ j).source ∧ ψ j (y j) = 0 := by
    intro j
    constructor
    · have hz : y j ∈ ((chartAt (EuclideanSpace ℝ (Fin (k * m))) (y j)).trans
          (Work.EmbeddedSpheres.TubeProject.subRightOpenPartialHomeomorph (c j))).source := by
        rw [OpenPartialHomeomorph.trans_source]
        exact ⟨mem_chart_source _ _, Set.mem_univ _⟩
      exact hz
    · have hz : ((chartAt (EuclideanSpace ℝ (Fin (k * m))) (y j)).trans
          (Work.EmbeddedSpheres.TubeProject.subRightOpenPartialHomeomorph (c j))) (y j) = 0 := by
        rw [OpenPartialHomeomorph.trans_apply,
          Work.EmbeddedSpheres.TubeProject.subRightOpenPartialHomeomorph_apply]
        exact sub_self _
      exact hz
  have hWsub : ∀ j : Fin s.card, (ψ j).source ⊆ W j := by
    intro j z hz
    have h1 : z ∈ (chartAt (EuclideanSpace ℝ (Fin (k * m))) (y j)).source := by
      have hz' : z ∈ ((chartAt (EuclideanSpace ℝ (Fin (k * m))) (y j)).trans
          (Work.EmbeddedSpheres.TubeProject.subRightOpenPartialHomeomorph (c j))).source := hz
      rw [OpenPartialHomeomorph.trans_source] at hz'
      exact hz'.1
    exact chart_source_subset (chartIdxAt (y j)) (chartSignAt (y j)) h1
  have hC2 : ∀ i j : Fin s.card,
      ContDiffOn ℝ 2 (fun u : EuclideanSpace ℝ (Fin (k * m)) => ψ j ((ψ i).symm u))
        (ψ i '' ((ψ i).source ∩ (ψ j).source)) := by
    intro i j
    exact (Work.ThomBordism.contDiffOn_transition_of_mem_maximalAtlas (n := (∞ : ℕ∞ω))
      (hψmem i) (hψmem j)).of_le ENat.LEInfty.out
  have hinj : ∀ i j : Fin s.card, ∀ u ∈ ψ i '' ((ψ i).source ∩ (ψ j).source),
      Function.Injective
        (fderiv ℝ (fun v : EuclideanSpace ℝ (Fin (k * m)) => ψ j ((ψ i).symm v)) u) := by
    intro i j u hu
    exact Work.ThomBordism.injective_fderiv_transition_of_mem_maximalAtlas (n := (∞ : ℕ∞ω))
      (by decide) (hψmem i) (hψmem j) hu
  obtain ⟨m', U, r, hUopen, hUcov, hUgood, hUsub⟩ :=
    goodCoverSubordinate (OG k m) ψ hψcov y hy0 hC2 hinj W hWsub
  -- ## 2. The pieces of the annulus over the cover
  let Wp : Fin m' → Set ↥(annSet k m) :=
    fun i => {z | (tautologicalBundle k m).proj z.1 ∈ U i}
  have hWpopen : ∀ i, IsOpen (Wp i) := fun i =>
    (hUopen i).preimage ((tautologicalBundle k m).continuous_proj.comp continuous_subtype_val)
  have hWpcov : (⋃ i, Wp i) = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro z
    have hz : ∃ i, (tautologicalBundle k m).proj z.1 ∈ U i := by
      have h : (tautologicalBundle k m).proj z.1 ∈ (⋃ i, U i) := by rw [hUcov]; trivial
      rwa [Set.mem_iUnion] at h
    obtain ⟨i, hi⟩ := hz
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  have hfin : ∀ (S : Finset (Fin m')), S.Nonempty → ∀ n, Module.Finite ℤ
      ((Work.Cohomology.singularChains ℤ (TopCat.of ↥(⋂ i ∈ S, Wp i))).homology n) := by
    intro S hS n
    obtain ⟨i₀, hi₀⟩ := hS
    have hWchart : (⋂ i ∈ S, U i) ⊆ baseSet (chartIdxAt (y (r i₀))) := by
      intro x hx
      rw [Set.mem_iInter₂] at hx
      exact hUsub i₀ (hx i₀ hi₀)
    have hann : Module.Finite ℤ ((Work.Cohomology.singularChains ℤ
        (TopCat.of ↥(annOver k m (⋂ i ∈ S, U i)))).homology n) :=
      annOverHomologyFinite (chartIdxAt (y (r i₀))) hWchart (fun hne => hUgood S ⟨i₀, hi₀⟩ hne) n
    have hpiece : Module.Finite ℤ ((Work.Cohomology.singularChains ℤ
        (TopCat.of ↥{p : ↥(annSet k m) |
          (tautologicalBundle k m).proj p.1 ∈ ⋂ i ∈ S, U i})).homology n) :=
      moduleFinite_homology_of_homeomorphCM (annPieceHomeo (⋂ i ∈ S, U i)) n hann
    have hset : (⋂ i ∈ S, Wp i)
        = {p : ↥(annSet k m) | (tautologicalBundle k m).proj p.1 ∈ ⋂ i ∈ S, U i} := by
      ext z
      simp only [Set.mem_iInter, Set.mem_ofPred_eq, Wp]
    exact moduleFinite_homology_of_homeomorphCM (Homeomorph.setCongr hset.symm) n hpiece
  -- ## 3. Assemble
  exact finiteCoverHomologyFinite (X := TopCat.of ↥(annSet k m)) Wp hWpopen hWpcov hfin n

end

end Work.ThomBordism.Grassmann.Torsion
