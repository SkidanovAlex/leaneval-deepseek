import Mathlib
import Submission.Work.PTGeometric.HOFXfer
import Submission.Work.PTGeometric.eucFam_germ_ball

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Topology

namespace Work.PTGeometric.HOF

noncomputable section

variable {W : TopCat} {N : ℕ}

/-- `excE_symm_incl` in the `punctIso` spelling. -/
theorem punctIso_symm_incl {E : TopCat} (N : ℕ) {B U : Set E} (hBU : B ⊆ U) (hB : IsOpen B)
    (hU : IsOpen U) (x : E) (hxB : x ∈ B) (hxU : x ∈ U) (hxc : IsClosed ({x} : Set E))
    (v : Work.Orient.RelH E N ({x} : Set E)) :
    RelHmapOf N (inclSub B U hBU) (trace B ({x} : Set E)) (trace U ({x} : Set E))
        (fun z hz => hz)
        (((punctIso E N B hB x hxB hxc).symm.toLinearMap) v)
      = ((punctIso E N U hU x hxU hxc).symm.toLinearMap) v :=
  excE_symm_incl hBU hB hU (Set.singleton_subset_iff.mpr hxB) (Set.singleton_subset_iff.mpr hxU)
    hxc v

/-- **The chart transfer does not depend on the chart** (at a point where the transition has positive
determinant). -/
theorem chartTr_change (N : ℕ) (hN : 1 ≤ N) {W : TopCat} [T1Space W]
    (e f : OpenPartialHomeomorph W (Euc N)) (w : W) (he : w ∈ e.source) (hf : w ∈ f.source)
    (A : Euc N →L[ℝ] Euc N)
    (hd : HasFDerivAt (fun z : Euc N => f (e.symm z)) A (e w))
    (hdet : 0 < LinearMap.det A.toLinearMap) :
    chartTr e w he (eucFam N hN (e w)) = chartTr f w hf (eucFam N hN (f w)) := by
  classical
  have hsymm : e.symm (e w) = w := e.left_inv he
  have hsrc : IsOpen ((e.symm.trans f).source) := (e.symm.trans f).open_source
  have hmem : e w ∈ (e.symm.trans f).source := by
    refine ⟨e.map_source he, ?_⟩
    show e.symm (e w) ∈ f.source
    rw [hsymm]; exact hf
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp hsrc (e w) hmem
  have hmemB : ∀ z ∈ Metric.ball (α := Euc N) (e w) ρ, z ∈ e.target ∧ e.symm z ∈ f.source :=
    fun z hz => hball hz
  have hFa : f (e.symm (e w)) = f w := by rw [hsymm]
  have hnz : ∀ z ∈ Metric.ball (α := Euc N) (e w) ρ, z ≠ e w → f (e.symm z) ≠ f w := by
    intro z hz hzne h
    have h2 : e.symm z = w := f.injOn (hmemB z hz).2 hf h
    exact hzne ((e.right_inv (hmemB z hz).1).symm.trans (by rw [h2]))
  have hsymmc : Continuous fun z : ↥(Metric.ball (α := Euc N) (e w) ρ) => e.symm (z : Euc N) :=
    e.continuousOn_symm.domRestrict.comp
      (Continuous.subtype_mk continuous_subtype_val (fun z => (hmemB z z.2).1))
  have hfsrc : Continuous fun z : ↥(Metric.ball (α := Euc N) (e w) ρ) =>
      (⟨e.symm (z : Euc N), (hmemB z z.2).2⟩ : ↥f.source) :=
    Continuous.subtype_mk hsymmc (fun z => (hmemB z z.2).2)
  have hFc : Continuous fun z : ↥(Metric.ball (α := Euc N) (e w) ρ) => f (e.symm z) :=
    f.continuousOn.domRestrict.comp hfsrc
  -- the germ
  have hgerm := eucFam_germ_ball N hN (e w) (f w) ρ hρ (fun z => f (e.symm z)) hFc hFa hnz A hd hdet
  -- the corestricted transition
  let Ψ : TopCat.of ↥(Metric.ball (α := Euc N) (e w) ρ) ⟶ TopCat.of ↥f.target :=
    TopCat.ofHom ⟨fun z => ⟨f (e.symm (z : Euc N)), f.map_source (hmemB z z.2).2⟩, by
      exact Continuous.subtype_mk hFc (fun z => f.map_source (hmemB z z.2).2)⟩
  have hΨpair : ∀ z ∉ punctSet (TopCat.of (Euc N)) (Metric.ball (α := Euc N) (e w) ρ) (e w),
      Ψ z ∉ punctSet (TopCat.of (Euc N)) f.target (f w) := by
    intro z hz
    exact hnz (z : Euc N) z.2 (fun h => hz h)
  have hfact : (TopCat.ofHom ⟨fun z : ↥(Metric.ball (α := Euc N) (e w) ρ) => f (e.symm z), hFc⟩)
      = Ψ ≫ Work.Cohomology.subtypeIncl (TopCat.of (Euc N)) f.target := by
    apply TopCat.ext
    intro z
    show f (e.symm (z : Euc N)) = ((Ψ z : ↥f.target) : Euc N)
    rfl
  have hBTe : Metric.ball (α := Euc N) (e w) ρ ⊆ e.target := fun z hz => (hball hz).1
  -- (1) the germ, inverted and pushed into the target of `f`
  have hgerm' : eucFam N hN (f w)
      = RelHmapOf N (TopCat.ofHom ⟨fun z : ↥(Metric.ball (α := Euc N) (e w) ρ) => f (e.symm z), hFc⟩)
          (punctSet (TopCat.of (Euc N)) (Metric.ball (α := Euc N) (e w) ρ) (e w))
          ({f w} : Set (Euc N))
          (fun z hz => hnz (z : Euc N) z.2 (fun h => hz h))
          (((punctIso (TopCat.of (Euc N)) N (Metric.ball (α := Euc N) (e w) ρ) Metric.isOpen_ball
            (e w) (Metric.mem_ball_self hρ) isClosed_singleton).symm.toLinearMap)
            (eucFam N hN (e w))) := hgerm.symm
  have hkeyA :
      RelHmapOf N (TopCat.ofHom ⟨fun z : ↥(Metric.ball (α := Euc N) (e w) ρ) => f (e.symm z), hFc⟩)
          (punctSet (TopCat.of (Euc N)) (Metric.ball (α := Euc N) (e w) ρ) (e w))
          ({f w} : Set (Euc N)) (fun z hz => hnz (z : Euc N) z.2 (fun h => hz h))
          (((punctIso (TopCat.of (Euc N)) N (Metric.ball (α := Euc N) (e w) ρ) Metric.isOpen_ball
            (e w) (Metric.mem_ball_self hρ) isClosed_singleton).symm.toLinearMap)
            (eucFam N hN (e w)))
        = (excM (TopCat.of (Euc N)) N f.target ({f w} : Set (Euc N)))
            (RelHmapOf N Ψ (punctSet (TopCat.of (Euc N)) (Metric.ball (α := Euc N) (e w) ρ) (e w))
              (punctSet (TopCat.of (Euc N)) f.target (f w)) hΨpair
              (((punctIso (TopCat.of (Euc N)) N (Metric.ball (α := Euc N) (e w) ρ) Metric.isOpen_ball
                (e w) (Metric.mem_ball_self hρ) isClosed_singleton).symm.toLinearMap)
                (eucFam N hN (e w)))) := by
    rw [RelHmapOf_congr
      (f := (TopCat.ofHom ⟨fun z : ↥(Metric.ball (α := Euc N) (e w) ρ) => f (e.symm z), hFc⟩))
      (f' := Ψ ≫ Work.Cohomology.subtypeIncl (TopCat.of (Euc N)) f.target)
      (K := punctSet (TopCat.of (Euc N)) (Metric.ball (α := Euc N) (e w) ρ) (e w))
      (K' := ({f w} : Set (Euc N))) hfact
      (fun z hz => hnz (z : Euc N) z.2 (fun h => hz h))
      (fun z hz => by
        show f (e.symm (z : Euc N)) ≠ f w
        exact hnz (z : Euc N) z.2 (fun h => hz h))]
    rw [← RelHmapOf_comp (f := Ψ)
      (g := Work.Cohomology.subtypeIncl (TopCat.of (Euc N)) f.target)
      (K := punctSet (TopCat.of (Euc N)) (Metric.ball (α := Euc N) (e w) ρ) (e w))
      (K' := punctSet (TopCat.of (Euc N)) f.target (f w)) (K'' := ({f w} : Set (Euc N)))
      hΨpair (fun z hz => hz) (fun z hz => hnz (z : Euc N) z.2 (fun h => hz h))]
    rw [LinearMap.comp_apply]
    rfl
  have hkey : ((punctIso (TopCat.of (Euc N)) N f.target f.open_target (f w) (f.map_source hf)
        isClosed_singleton).symm.toLinearMap) (eucFam N hN (f w))
      = RelHmapOf N Ψ (punctSet (TopCat.of (Euc N)) (Metric.ball (α := Euc N) (e w) ρ) (e w))
          (punctSet (TopCat.of (Euc N)) f.target (f w)) hΨpair
          (((punctIso (TopCat.of (Euc N)) N (Metric.ball (α := Euc N) (e w) ρ) Metric.isOpen_ball
            (e w) (Metric.mem_ball_self hρ) isClosed_singleton).symm.toLinearMap)
            (eucFam N hN (e w))) := by
    have h := congrArg (((punctIso (TopCat.of (Euc N)) N f.target f.open_target (f w)
      (f.map_source hf) isClosed_singleton).symm.toLinearMap)) hgerm'
    rw [hkeyA] at h
    rw [punctIso_symm_toLinearMap_excM] at h
    exact h
  -- (2) push the transition through the two ambient chart maps
  have hmap : Ψ ≫ eSymmA f = inclSub (Metric.ball (α := Euc N) (e w) ρ) e.target hBTe ≫ eSymmA e := by
    apply TopCat.ext
    intro z
    show f.symm (f (e.symm (z : Euc N))) = e.symm (z : Euc N)
    rw [f.left_inv (hmemB (z : Euc N) z.2).2]
  have hstep2 :
      (RelHmapOf N (eSymmA f) (punctSet (TopCat.of (Euc N)) f.target (f w)) ({w} : Set W)
          (fun z hz => eSymmA_pair f w hf hz))
          (RelHmapOf N Ψ (punctSet (TopCat.of (Euc N)) (Metric.ball (α := Euc N) (e w) ρ) (e w))
            (punctSet (TopCat.of (Euc N)) f.target (f w)) hΨpair
            (((punctIso (TopCat.of (Euc N)) N (Metric.ball (α := Euc N) (e w) ρ) Metric.isOpen_ball
              (e w) (Metric.mem_ball_self hρ) isClosed_singleton).symm.toLinearMap)
              (eucFam N hN (e w))))
        = RelHmapOf N (eSymmA e) (punctSet (TopCat.of (Euc N)) e.target (e w)) ({w} : Set W)
            (fun z hz => eSymmA_pair e w he hz)
            (RelHmapOf N (inclSub (Metric.ball (α := Euc N) (e w) ρ) e.target hBTe)
              (punctSet (TopCat.of (Euc N)) (Metric.ball (α := Euc N) (e w) ρ) (e w))
              (punctSet (TopCat.of (Euc N)) e.target (e w)) (fun z hz => hz)
              (((punctIso (TopCat.of (Euc N)) N (Metric.ball (α := Euc N) (e w) ρ) Metric.isOpen_ball
                (e w) (Metric.mem_ball_self hρ) isClosed_singleton).symm.toLinearMap)
                (eucFam N hN (e w)))) := by
    rw [← LinearMap.comp_apply, RelHmapOf_comp (f := Ψ) (g := eSymmA f)
      (K := punctSet (TopCat.of (Euc N)) (Metric.ball (α := Euc N) (e w) ρ) (e w))
      (K' := punctSet (TopCat.of (Euc N)) f.target (f w)) (K'' := ({w} : Set W))
      hΨpair (fun z hz => eSymmA_pair f w hf hz)
      (fun z hz => by
        show f.symm (f (e.symm (z : Euc N))) ≠ w
        rw [f.left_inv (hmemB (z : Euc N) z.2).2]
        exact eSymmA_pair e w he
          (z := (inclSub (Metric.ball (α := Euc N) (e w) ρ) e.target hBTe z)) hz)]
    rw [RelHmapOf_congr (f := Ψ ≫ eSymmA f)
      (f' := inclSub (Metric.ball (α := Euc N) (e w) ρ) e.target hBTe ≫ eSymmA e)
      (K := punctSet (TopCat.of (Euc N)) (Metric.ball (α := Euc N) (e w) ρ) (e w))
      (K' := ({w} : Set W)) hmap
      (fun z hz => by
        show f.symm (f (e.symm (z : Euc N))) ≠ w
        rw [f.left_inv (hmemB (z : Euc N) z.2).2]
        exact eSymmA_pair e w he
          (z := (inclSub (Metric.ball (α := Euc N) (e w) ρ) e.target hBTe z)) hz)
      (fun z hz => eSymmA_pair e w he
        (z := (inclSub (Metric.ball (α := Euc N) (e w) ρ) e.target hBTe z)) hz)]
    rw [← RelHmapOf_comp (f := inclSub (Metric.ball (α := Euc N) (e w) ρ) e.target hBTe)
      (g := eSymmA e)
      (K := punctSet (TopCat.of (Euc N)) (Metric.ball (α := Euc N) (e w) ρ) (e w))
      (K' := punctSet (TopCat.of (Euc N)) e.target (e w)) (K'' := ({w} : Set W))
      (fun z hz => hz) (fun y hy => eSymmA_pair e w he hy)
      (fun z hz => eSymmA_pair e w he
        (z := (inclSub (Metric.ball (α := Euc N) (e w) ρ) e.target hBTe z)) hz)]
    rw [LinearMap.comp_apply]
  -- (3) restrict from the ball to the point
  have hstep3 :
      RelHmapOf N (inclSub (Metric.ball (α := Euc N) (e w) ρ) e.target hBTe)
          (punctSet (TopCat.of (Euc N)) (Metric.ball (α := Euc N) (e w) ρ) (e w))
          (punctSet (TopCat.of (Euc N)) e.target (e w)) (fun z hz => hz)
          (((punctIso (TopCat.of (Euc N)) N (Metric.ball (α := Euc N) (e w) ρ) Metric.isOpen_ball
            (e w) (Metric.mem_ball_self hρ) isClosed_singleton).symm.toLinearMap)
            (eucFam N hN (e w)))
        = ((punctIso (TopCat.of (Euc N)) N e.target e.open_target (e w) (e.map_source he)
            isClosed_singleton).symm.toLinearMap) (eucFam N hN (e w)) :=
    punctIso_symm_incl (E := TopCat.of (Euc N)) N hBTe Metric.isOpen_ball e.open_target (e w)
      (Metric.mem_ball_self hρ) (e.map_source he) isClosed_singleton (eucFam N hN (e w))
  rw [chartTr_apply f w hf, chartTr_apply e w he, hkey, hstep2, hstep3]

end

end Work.PTGeometric.HOF
