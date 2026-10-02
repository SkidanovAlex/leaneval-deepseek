import Mathlib
import Submission.Work.ThomBordism.modelBdrySign
import Submission.Work.PTGeometric.HOFChart

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Topology Manifold

namespace Work.ThomBordism

noncomputable section

variable {m k : ℕ} [NeZero (m + 1 + k)] {v : Euc (m + 1 + k) →L[ℝ] Euc k}

/-- **A chart transfer of the Euclidean model generator generates the local group.** -/
theorem span_chartTr_eucFam {W : TopCat} [T1Space W] {N : ℕ} (hN : 1 ≤ N)
    (e : OpenPartialHomeomorph W (Euc N)) (x : W) (hw : x ∈ e.source) :
    Submodule.span ℤ
      ({Work.PTGeometric.HOF.chartTr e x hw (Work.PTGeometric.HOF.eucFam N hN (e x))} :
        Set (Work.Orient.LocH W N x)) = ⊤ :=
  Work.Tubular.span_singleton_eq_top_of_surjective _
    (Work.PTGeometric.HOF.chartTr_surjective e x hw) _
    (Work.PTGeometric.HOF.eucFam_gen N hN (e x))

/-- **The class over a compact piece inside the source of a chart.** -/
theorem pieceClassChartTr {W : TopCat} [T2Space W] {N : ℕ} (hN : 1 ≤ N)
    (e : OpenPartialHomeomorph W (Euc N)) (K : Set W) (hK : IsCompact K)
    (hKsrc : ∀ x ∈ K, x ∈ e.source) :
    ∃ a : Work.Orient.RelH W N K,
      ∀ (x : W) (hx : x ∈ K),
        Work.Orient.resRelH W N (Set.singleton_subset_iff.mpr hx) a
          = Work.PTGeometric.HOF.chartTr e x (hKsrc x hx)
              (Work.PTGeometric.HOF.eucFam N hN (e x)) := by
  classical
  set S : Set (Euc N) := e '' K with hS
  have hScomp : IsCompact S := hK.image_of_continuousOn (e.continuousOn.mono hKsrc)
  have hSclosed : IsClosed S := hScomp.isClosed
  have hSsub : S ⊆ e.target := by
    rintro y ⟨x, hx, rfl⟩
    exact e.map_source (hKsrc x hx)
  have hpc : ∀ z' ∉ Work.PTGeometric.HOF.trace (X := TopCat.of (Euc N)) e.target S,
      Work.PTGeometric.HOF.eSymmA e z' ∉ K := by
    intro z' hz' hzK
    refine hz' ?_
    show (z' : Euc N) ∈ S
    rw [← e.right_inv z'.2]
    exact ⟨e.symm (z' : Euc N), hzK, rfl⟩
  refine ⟨Work.PTGeometric.HOF.RelHmapOf N (Work.PTGeometric.HOF.eSymmA e)
      (Work.PTGeometric.HOF.trace (X := TopCat.of (Euc N)) e.target S) K hpc
      ((Work.PTGeometric.HOF.excE (TopCat.of (Euc N)) N e.target e.open_target S hSsub
        hSclosed).symm (Work.PTGeometric.HOF.eucCanon N hN S hScomp)), ?_⟩
  intro x hxK
  have hxsrc : x ∈ e.source := hKsrc x hxK
  have hxex : e x ∈ e.target := e.map_source hxsrc
  have hexS : e x ∈ S := ⟨x, hxK, rfl⟩
  have hexsub : Work.PTGeometric.HOF.punctSet (TopCat.of (Euc N)) e.target (e x)
      ⊆ Work.PTGeometric.HOF.trace (X := TopCat.of (Euc N)) e.target S := by
    intro z' hz'
    show (z' : Euc N) ∈ S
    rw [show (z' : Euc N) = e x from hz']
    exact hexS
  have h1 : Work.Orient.resRelH W N (Set.singleton_subset_iff.mpr hxK)
      (Work.PTGeometric.HOF.RelHmapOf N (Work.PTGeometric.HOF.eSymmA e)
        (Work.PTGeometric.HOF.trace (X := TopCat.of (Euc N)) e.target S) K hpc
        ((Work.PTGeometric.HOF.excE (TopCat.of (Euc N)) N e.target e.open_target S hSsub
          hSclosed).symm (Work.PTGeometric.HOF.eucCanon N hN S hScomp)))
      = Work.PTGeometric.HOF.RelHmapOf N (Work.PTGeometric.HOF.eSymmA e)
          (Work.PTGeometric.HOF.punctSet (TopCat.of (Euc N)) e.target (e x)) ({x} : Set W)
          (fun z' hz' => Work.PTGeometric.HOF.eSymmA_pair e x hxsrc hz')
          (Work.Orient.resRelH (TopCat.of ↥e.target) N
            (A := Work.PTGeometric.HOF.punctSet (TopCat.of (Euc N)) e.target (e x))
            (B := Work.PTGeometric.HOF.trace (X := TopCat.of (Euc N)) e.target S) hexsub
            ((Work.PTGeometric.HOF.excE (TopCat.of (Euc N)) N e.target e.open_target S hSsub
              hSclosed).symm (Work.PTGeometric.HOF.eucCanon N hN S hScomp))) := by
    have h := LinearMap.congr_fun
      (Work.PTGeometric.HOF.RelHmapOf_resRelH (X := TopCat.of ↥e.target) (Y := W) (n := N)
        (Work.PTGeometric.HOF.eSymmA e)
        (K₁ := Work.PTGeometric.HOF.punctSet (TopCat.of (Euc N)) e.target (e x))
        (K₂ := Work.PTGeometric.HOF.trace (X := TopCat.of (Euc N)) e.target S)
        (K'₁ := ({x} : Set W)) (K'₂ := K) hexsub (Set.singleton_subset_iff.mpr hxK) hpc
        (fun z' hz' => Work.PTGeometric.HOF.eSymmA_pair e x hxsrc hz'))
      ((Work.PTGeometric.HOF.excE (TopCat.of (Euc N)) N e.target e.open_target S hSsub
        hSclosed).symm (Work.PTGeometric.HOF.eucCanon N hN S hScomp))
    exact h.symm
  have h2 : Work.Orient.resRelH (TopCat.of ↥e.target) N
      (A := Work.PTGeometric.HOF.punctSet (TopCat.of (Euc N)) e.target (e x))
      (B := Work.PTGeometric.HOF.trace (X := TopCat.of (Euc N)) e.target S) hexsub
      ((Work.PTGeometric.HOF.excE (TopCat.of (Euc N)) N e.target e.open_target S hSsub
        hSclosed).symm (Work.PTGeometric.HOF.eucCanon N hN S hScomp))
      = ((Work.PTGeometric.HOF.punctIso (TopCat.of (Euc N)) N e.target e.open_target (e x)
          hxex isClosed_singleton).symm.toLinearMap)
        (Work.PTGeometric.HOF.eucFam N hN (e x)) := by
    have h := Work.PTGeometric.HOF.resRelH_excE_symm (X := TopCat.of (Euc N)) N e.target
      e.open_target (K₁ := ({e x} : Set (Euc N))) (K₂ := S) (Set.singleton_subset_iff.mpr hexS)
      hSsub (Set.singleton_subset_iff.mpr hxex) isClosed_singleton hSclosed
      (Work.PTGeometric.HOF.eucCanon N hN S hScomp)
    rw [Work.PTGeometric.HOF.eucCanon_spec N hN S hScomp (e x) hexS] at h
    exact h
  rw [h1, h2]
  show Work.PTGeometric.HOF.chartTr e x hxsrc (Work.PTGeometric.HOF.eucFam N hN (e x))
      = Work.PTGeometric.HOF.chartTr e x (hKsrc x hxK)
          (Work.PTGeometric.HOF.eucFam N hN (e x))
  exact congrArg (fun (h : x ∈ e.source) =>
      Work.PTGeometric.HOF.chartTr e x h (Work.PTGeometric.HOF.eucFam N hN (e x)))
    (Subsingleton.elim hxsrc (hKsrc x hxK))

theorem modelHalfOrientation {m k : ℕ} [NeZero (m + 1 + k)] {v : Euc (m + 1 + k) →L[ℝ] Euc k} (hm : 1 ≤ m) (s : ModelSplit (a := m + 1) (k := k) v) (hpos : splitPos s) : @Work.Orient.IsHalfOrientationFamily m (TopCat.of ↥(ModelLevelSet (a := m + 1) (k := k) v)) (modelChartedSpace (k := k) s) (fun x hx => modelOrientation s hm x (by rw [modelChartSource_eq_compl]; exact fun h => hx (by rw [modelBdry_eq_boundary]; exact h))) := by
  classical
  letI : ChartedSpace (EuclideanHalfSpace (m + 1)) ↥(ModelLevelSet (a := m + 1) (k := k) v) :=
    modelChartedSpace (k := k) s
  have hN : 1 ≤ m + 1 := by omega
  refine ⟨?_, ?_⟩
  · intro x hx
    have hw : x ∈ modelChartSource (a := m + 1) (k := k) s := by
      rw [modelChartSource_eq_compl]
      exact fun h => hx (by rw [modelBdry_eq_boundary]; exact h)
    show Submodule.span ℤ
      ({(Work.PTGeometric.HOF.chartTr (modelChart (a := m + 1) (k := k) s) x hw
        (Work.PTGeometric.HOF.eucFam (m + 1) hN
          (modelChart (a := m + 1) (k := k) s x)))} :
        Set (Work.Orient.LocH (TopCat.of ↥(ModelLevelSet (a := m + 1) (k := k) v))
          (m + 1) x)) = ⊤
    exact span_chartTr_eucFam hN _ x hw
  · intro K hK hKint
    have hKsrc : ∀ x ∈ K, x ∈ modelChartSource (a := m + 1) (k := k) s := by
      intro x hx
      rw [modelChartSource_eq_compl]
      exact fun h => hKint x hx (by rw [modelBdry_eq_boundary]; exact h)
    obtain ⟨a, ha⟩ := pieceClassChartTr hN (modelChart (a := m + 1) (k := k) s) K
      hK.isCompact hKsrc
    refine ⟨a, ?_⟩
    intro x hx hxK
    rw [ha x hxK]
    have hw : x ∈ modelChartSource (a := m + 1) (k := k) s := by
      rw [modelChartSource_eq_compl]
      exact fun h => hx (by rw [modelBdry_eq_boundary]; exact h)
    show Work.PTGeometric.HOF.chartTr (modelChart (a := m + 1) (k := k) s) x (hKsrc x hxK)
        (Work.PTGeometric.HOF.eucFam (m + 1) hN
          (modelChart (a := m + 1) (k := k) s x))
      = Work.PTGeometric.HOF.chartTr (modelChart (a := m + 1) (k := k) s) x hw
          (Work.PTGeometric.HOF.eucFam (m + 1) hN
            (modelChart (a := m + 1) (k := k) s x))
    exact congrArg (fun (h : x ∈ modelChartSource (a := m + 1) (k := k) s) =>
        Work.PTGeometric.HOF.chartTr (modelChart (a := m + 1) (k := k) s) x h
          (Work.PTGeometric.HOF.eucFam (m + 1) hN
            (modelChart (a := m + 1) (k := k) s x)))
      (Subsingleton.elim (hKsrc x hxK) hw)

end

end Work.ThomBordism
