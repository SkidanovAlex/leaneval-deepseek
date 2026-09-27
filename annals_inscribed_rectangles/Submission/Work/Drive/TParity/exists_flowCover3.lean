import Mathlib
import Submission.Work.Drive.TParity.Basic
import Submission.Work.Drive.TParity.ChartDeriv
import Submission.Work.Drive.TParity.FlowSetupK3
import Submission.Work.Drive.TParity.exists_flowChart_at3
import Submission.Work.Drive.ManifoldParity.FlowSetupDefs
import Submission.Work.Drive.ManifoldParity.InterSetFlowDefs

namespace Work.Drive.TParity

open scoped Manifold ContDiff Topology
open Manifold Set

set_option backward.isDefEq.respectTransparency false

noncomputable section

/-- The triple intersection set is compact (it is a closed subset of the compact nine-box). -/
theorem isCompact_K3 {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M) (hD : ∀ k, Continuous (D k)) :
    IsCompact (K3 D) := by
  have h1 : IsClosed {x : Amb 8 | D 0 (bPartC 0 x) = D 1 (bPartC 1 x)} :=
    isClosed_eq ((hD 0).comp (bPartC 0).continuous) ((hD 1).comp (bPartC 1).continuous)
  have h2 : IsClosed {x : Amb 8 | D 0 (bPartC 0 x) = D 2 (bPartC 2 x)} :=
    isClosed_eq ((hD 0).comp (bPartC 0).continuous) ((hD 2).comp (bPartC 2).continuous)
  have hclosed : IsClosed (K3 D) := by
    have hset : K3 D = Submission.Drive.unitBox 8 ∩
        ({x : Amb 8 | D 0 (bPartC 0 x) = D 1 (bPartC 1 x)} ∩
          {x : Amb 8 | D 0 (bPartC 0 x) = D 2 (bPartC 2 x)}) := by
      ext x
      simp only [mem_K3, meet3, Set.mem_inter_iff, Set.mem_ofPred_eq]
    rw [hset]
    exact (isClosed_unitBox 8).inter (h1.inter h2)
  exact (isCompact_unitBox 8).of_isClosed_subset hclosed (fun x hx => hx.1)

theorem exists_flowCover3 {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M)
    (hD : ∀ k, ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) (D k))
    (htrans : Work.Drive.TParity.transHyp D) (V : Work.Drive.Amb 8 → Work.Drive.Amb 8)
    (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V) (hVs : HasCompactSupport V)
    (hVtan : Work.Drive.TParity.Vtan D V) (hVne : Work.Drive.TParity.Vne D V)
    (hmapsTo : ∀ x ∈ Work.Drive.TParity.K3 D, ∀ t : ℝ,
      (∀ u ∈ Set.uIcc (0 : ℝ) t,
        Work.Drive.TParity.flowV8 V hV hVs u x ∈ Submission.Drive.unitBox 8) →
      Work.Drive.TParity.flowV8 V hV hVs t x ∈ Work.Drive.TParity.K3 D) :
    Nonempty (Work.Drive.FlowCover (Work.Drive.TParity.K3_setup D V hV hVs hmapsTo)) := by
  classical
  have hpoint (x : Amb 8) (hx : x ∈ K3 D) :
      ∃ C : Work.Drive.FlowChart V (K3 D) x, x ∈ C.region := by
    have hbox : x ∈ Submission.Drive.unitBox 8 := hx.1
    have hmeet : meet3 D x := hx.2
    have hxreg : x ∈ region3 (D 0 (bPartC 0 x)) D := mem_region3_self D hmeet
    have hsurj : Function.Surjective
        (fderiv ℝ (chartDiff3 (D 0 (bPartC 0 x)) D) x) :=
      chartDiff3_surj D hD hxreg hmeet (htrans x hbox hmeet)
    obtain ⟨i, hi⟩ := Work.Drive.exists_domRestrict_surjective hsurj
    obtain ⟨C, -, hCx⟩ := exists_flowChart_at3 D hD hV.continuous hx hsurj
      (hVtan x hx (D 0 (bPartC 0 x)) hxreg) (hVne x hx) i hi
    exact ⟨C, hCx⟩
  have hcompact : IsCompact (K3 D) := isCompact_K3 D (fun k => (hD k).continuous)
  let Cof : ∀ x : Amb 8, x ∈ K3 D → Work.Drive.FlowChart V (K3 D) x :=
    fun x hx => Classical.choose (hpoint x hx)
  by_cases hne : (K3 D).Nonempty
  · haveI : Nonempty {x : Amb 8 // x ∈ K3 D} :=
      ⟨⟨hne.choose, hne.choose_spec⟩⟩
    obtain ⟨t, ht⟩ := hcompact.elim_finite_subcover
      (fun x : {x : Amb 8 // x ∈ K3 D} => (Cof x.1 x.2).region)
      (fun x => (Cof x.1 x.2).isOpen_region)
      (fun x hx => Set.mem_iUnion.mpr
        ⟨⟨x, hx⟩, Classical.choose_spec (hpoint x hx)⟩)
    have hcover : K3 D ∩ Submission.Drive.unitBox 8 ⊆
        ⋃ j : {j : {x : Amb 8 // x ∈ K3 D} // j ∈ t}, (Cof j.1.1 j.1.2).region := by
      intro y hy
      have h := ht hy.1
      simp only [Set.mem_iUnion] at h
      obtain ⟨i, hi, hyi⟩ := h
      exact Set.mem_iUnion.mpr ⟨⟨i, hi⟩, hyi⟩
    let Cov : Work.Drive.FlowCover (K3_setup D V hV hVs hmapsTo) :=
      { ι := {j : {x : Amb 8 // x ∈ K3 D} // j ∈ t}, str := inferInstance,
        p := fun j => j.1.1, C := fun j => Cof j.1.1 j.1.2, cover := hcover }
    exact ⟨Cov⟩
  · let p0 : Fin 0 → Amb 8 := fun j => j.elim0
    have hcover : K3 D ∩ Submission.Drive.unitBox 8 ⊆
        ⋃ j : Fin 0, (j.elim0 : Work.Drive.FlowChart V (K3 D) (p0 j)).region := by
      intro y hy
      exact absurd ⟨y, hy.1⟩ hne
    let Cov : Work.Drive.FlowCover (K3_setup D V hV hVs hmapsTo) :=
      { ι := Fin 0, str := inferInstance, p := p0, C := fun j => j.elim0, cover := hcover }
    exact ⟨Cov⟩

end

end Work.Drive.TParity
