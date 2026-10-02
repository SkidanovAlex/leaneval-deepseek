import Mathlib
import Submission.Work.PTGeometric.HOFXfer
import Submission.Work.PTGeometric.HOFExc
import Submission.Work.PTGeometric.HOFDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Topology

namespace Work.ThomBordism.PosAtlas

open Work.PTGeometric.HOF

noncomputable section

variable {N : ℕ} {W : TopCat} [T1Space W]

/-! ## Notation -/

/-- The model space `ℝ^N` as a `TopCat`. -/
abbrev Modl (N : ℕ) : TopCat := TopCat.of (Euc N)

/-- The punctured target of the composite chart, in the unfolded spelling. -/
abbrev tK (e : OpenPartialHomeomorph W (Euc N)) (h : Euc N ≃ₜ Euc N) (w : W) :
    Set ↥(h.symm ⁻¹' e.target) :=
  punctSet (Modl N) (h.symm ⁻¹' e.target) (h (e w))

/-- The punctured target of the chart `e`. -/
abbrev eK (e : OpenPartialHomeomorph W (Euc N)) (w : W) : Set ↥e.target :=
  punctSet (Modl N) e.target (e w)

/-! ## The auxiliary maps -/

/-- The map `h.symm`, restricted to `h.symm ⁻¹' e.target`. -/
def hSub (e : OpenPartialHomeomorph W (Euc N)) (h : Euc N ≃ₜ Euc N) :
    TopCat.of ↥(h.symm ⁻¹' e.target) ⟶ TopCat.of ↥e.target :=
  TopCat.ofHom ⟨fun z => ⟨h.symm (z : Euc N), z.2⟩,
    Continuous.subtype_mk (h.continuous_invFun.comp continuous_subtype_val) _⟩

theorem hSub_apply (e : OpenPartialHomeomorph W (Euc N)) (h : Euc N ≃ₜ Euc N)
    (z : ↥(h.symm ⁻¹' e.target)) : ((hSub e h) z : Euc N) = h.symm (z : Euc N) := rfl

/-- The map `h.symm` as a self-map of the model space. -/
def hAmb (h : Euc N ≃ₜ Euc N) : Modl N ⟶ Modl N :=
  TopCat.ofHom ⟨fun z => h.symm z, h.continuous_invFun⟩

/-- `h (e w)` lies in `h.symm ⁻¹' e.target`. -/
theorem hSub_mem (e : OpenPartialHomeomorph W (Euc N)) (h : Euc N ≃ₜ Euc N) (w : W)
    (hw : w ∈ e.source) : h (e w) ∈ h.symm ⁻¹' e.target := by
  rw [Set.mem_preimage, h.symm_apply_apply]
  exact e.map_source hw

/-- The pair condition for `hSub`. -/
theorem hSub_pair (e : OpenPartialHomeomorph W (Euc N)) (h : Euc N ≃ₜ Euc N) (w : W)
    (hw : w ∈ e.source) :
    ∀ z ∉ tK e h w, (hSub e h) z ∉ eK e w := by
  intro z hz hh
  have h1 : (z : Euc N) ≠ h (e w) := hz
  have h2 : h.symm (z : Euc N) = e w := hh
  exact h1 (by rw [← h2, h.apply_symm_apply])

/-- The pair condition for `hAmb`. -/
theorem hAmb_pair (e : OpenPartialHomeomorph W (Euc N)) (h : Euc N ≃ₜ Euc N) (w : W) :
    ∀ z ∉ ({h (e w)} : Set (Euc N)), hAmb h z ∉ ({e w} : Set (Euc N)) := fun z hz => by
  simp only [Set.mem_singleton_iff] at hz ⊢
  intro hh
  exact hz (by rw [← hh]; exact (h.apply_symm_apply z).symm)

/-- `eSymmA` of the composite chart is the composite of `hSub` with `eSymmA e`. -/
theorem eSymmA_transHomeomorph (e : OpenPartialHomeomorph W (Euc N)) (h : Euc N ≃ₜ Euc N) :
    eSymmA (e.transHomeomorph h) = hSub e h ≫ eSymmA e := by
  apply TopCat.ext
  intro z
  rfl

/-- The square linking `hSub` with the ambient self-homeomorphism `h.symm`. -/
theorem hSub_comp_subtypeIncl (e : OpenPartialHomeomorph W (Euc N)) (h : Euc N ≃ₜ Euc N) :
    hSub e h ≫ Work.Cohomology.subtypeIncl (Modl N) e.target
      = Work.Cohomology.subtypeIncl (Modl N) (h.symm ⁻¹' e.target) ≫ hAmb h := by
  apply TopCat.ext
  intro z
  rfl

/-! ## The two structural identities -/

/-- **Compatibility of excision with the passage from the chart `e` to `e.transHomeomorph h`.** -/
theorem punctIso_symm_Hsub (e : OpenPartialHomeomorph W (Euc N)) (h : Euc N ≃ₜ Euc N) (w : W)
    (hw : w ∈ e.source)
    (Y : Work.Orient.RelH (Modl N) N ({h (e w)} : Set (Euc N))) :
    RelHmapOf N (hSub e h) (tK e h w) (eK e w) (hSub_pair e h w hw)
        ((punctIso (Modl N) N (h.symm ⁻¹' e.target) (e.open_target.preimage h.symm.continuous)
          (h (e w)) (hSub_mem e h w hw) isClosed_singleton).symm.toLinearMap Y)
      = (punctIso (Modl N) N e.target e.open_target (e w) (e.map_source hw)
          isClosed_singleton).symm.toLinearMap
          (RelHmapOf N (hAmb h) ({h (e w)} : Set (Euc N)) ({e w} : Set (Euc N))
            (hAmb_pair e h w) Y) := by
  apply excM_injective (Modl N) N e.target e.open_target ({e w} : Set (Euc N))
    (Set.singleton_subset_iff.mpr (e.map_source hw)) isClosed_singleton
  rw [punctIso_excM_symm' (Modl N) N e.target e.open_target (e w) (e.map_source hw)
    isClosed_singleton (RelHmapOf N (hAmb h) ({h (e w)} : Set (Euc N)) ({e w} : Set (Euc N))
      (hAmb_pair e h w) Y)]
  have hC1 : ∀ z ∉ tK e h w,
      (hSub e h ≫ Work.Cohomology.subtypeIncl (Modl N) e.target) z ∉ ({e w} : Set (Euc N)) :=
    fun z hz => hSub_pair e h w hw z hz
  have hC2 : ∀ z ∉ tK e h w,
      (Work.Cohomology.subtypeIncl (Modl N) (h.symm ⁻¹' e.target) ≫ hAmb h) z
        ∉ ({e w} : Set (Euc N)) := fun z hz hh => by
    have hh' : h.symm (z : Euc N) = e w := hh
    refine hz ?_
    show (z : Euc N) = h (e w)
    rw [← hh', h.apply_symm_apply]
  have hC3 : ∀ z ∉ tK e h w,
      (Work.Cohomology.subtypeIncl (Modl N) (h.symm ⁻¹' e.target)) z
        ∉ ({h (e w)} : Set (Euc N)) := fun z hz => hz
  have hC4 : ∀ z ∉ ({h (e w)} : Set (Euc N)), hAmb h z ∉ ({e w} : Set (Euc N)) :=
    hAmb_pair e h w
  have h1 : excM (Modl N) N e.target ({e w} : Set (Euc N))
      = RelHmapOf N (Work.Cohomology.subtypeIncl (Modl N) e.target) (eK e w)
          ({e w} : Set (Euc N)) (fun z hz => hz) := rfl
  rw [h1]
  have h2 : (RelHmapOf N (Work.Cohomology.subtypeIncl (Modl N) e.target) (eK e w)
        ({e w} : Set (Euc N)) (fun z hz => hz)).comp
      (RelHmapOf N (hSub e h) (tK e h w) (eK e w) (hSub_pair e h w hw))
      = RelHmapOf N (hSub e h ≫ Work.Cohomology.subtypeIncl (Modl N) e.target)
          (tK e h w) ({e w} : Set (Euc N)) hC1 :=
    RelHmapOf_comp (f := hSub e h)
      (g := Work.Cohomology.subtypeIncl (Modl N) e.target)
      (K := tK e h w) (K' := eK e w) (K'' := ({e w} : Set (Euc N)))
      (hSub_pair e h w hw) (fun z hz => hz) hC1
  rw [← LinearMap.comp_apply, h2]
  have h3 : RelHmapOf N (hSub e h ≫ Work.Cohomology.subtypeIncl (Modl N) e.target)
        (tK e h w) ({e w} : Set (Euc N)) hC1
      = RelHmapOf N (Work.Cohomology.subtypeIncl (Modl N) (h.symm ⁻¹' e.target) ≫ hAmb h)
          (tK e h w) ({e w} : Set (Euc N)) hC2 :=
    RelHmapOf_congr (hSub_comp_subtypeIncl e h) hC1 hC2
  rw [h3]
  have h4 : RelHmapOf N
        (Work.Cohomology.subtypeIncl (Modl N) (h.symm ⁻¹' e.target) ≫ hAmb h)
        (tK e h w) ({e w} : Set (Euc N)) hC2
      = (RelHmapOf N (hAmb h) ({h (e w)} : Set (Euc N)) ({e w} : Set (Euc N))
            (hAmb_pair e h w)).comp
        (RelHmapOf N (Work.Cohomology.subtypeIncl (Modl N) (h.symm ⁻¹' e.target))
          (tK e h w) ({h (e w)} : Set (Euc N)) hC3) :=
    (RelHmapOf_comp (f := Work.Cohomology.subtypeIncl (Modl N) (h.symm ⁻¹' e.target))
      (g := hAmb h) (K := tK e h w) (K' := ({h (e w)} : Set (Euc N)))
      (K'' := ({e w} : Set (Euc N))) hC3 hC4 hC2).symm
  rw [h4, LinearMap.comp_apply]
  have h5 : RelHmapOf N (Work.Cohomology.subtypeIncl (Modl N) (h.symm ⁻¹' e.target))
        (tK e h w) ({h (e w)} : Set (Euc N)) hC3
        ((punctIso (Modl N) N (h.symm ⁻¹' e.target) (e.open_target.preimage h.symm.continuous)
          (h (e w)) (hSub_mem e h w hw) isClosed_singleton).symm.toLinearMap Y) = Y :=
    punctIso_excM_symm' (Modl N) N (h.symm ⁻¹' e.target)
      (e.open_target.preimage h.symm.continuous) (h (e w)) (hSub_mem e h w hw)
      isClosed_singleton Y
  exact congrArg (RelHmapOf N (hAmb h) ({h (e w)} : Set (Euc N)) ({e w} : Set (Euc N))
    (hAmb_pair e h w)) h5

/-- **Functoriality of `RelHmapOf` along `hSub ≫ eSymmA e`.** -/
theorem relHmapOf_eSymmA_comp (e : OpenPartialHomeomorph W (Euc N)) (h : Euc N ≃ₜ Euc N)
    (w : W) (hw : w ∈ e.source)
    (v : Work.Orient.RelH (TopCat.of ↥(h.symm ⁻¹' e.target)) N (tK e h w)) :
    RelHmapOf N (hSub e h ≫ eSymmA e) (tK e h w) ({w} : Set W)
        (fun z hz => eSymmA_pair e w hw (hSub_pair e h w hw z hz)) v
      = RelHmapOf N (eSymmA e) (eK e w) ({w} : Set W)
          (fun z hz => eSymmA_pair e w hw hz)
          (RelHmapOf N (hSub e h) (tK e h w) (eK e w) (hSub_pair e h w hw) v) := by
  have h2 : RelHmapOf N (hSub e h ≫ eSymmA e) (tK e h w) ({w} : Set W)
        (fun z hz => eSymmA_pair e w hw (hSub_pair e h w hw z hz))
      = (RelHmapOf N (eSymmA e) (eK e w) ({w} : Set W)
            (fun z hz => eSymmA_pair e w hw hz)).comp
        (RelHmapOf N (hSub e h) (tK e h w) (eK e w) (hSub_pair e h w hw)) :=
    (RelHmapOf_comp (f := hSub e h) (g := eSymmA e) (K := tK e h w) (K' := eK e w)
      (K'' := ({w} : Set W)) (hSub_pair e h w hw) (fun z hz => eSymmA_pair e w hw hz)
      (fun z hz => eSymmA_pair e w hw (hSub_pair e h w hw z hz))).symm
  rw [h2, LinearMap.comp_apply]

/-- The unfolding of `chartTr` for the composite chart. -/
theorem chartTr_transHomeomorph_apply (e : OpenPartialHomeomorph W (Euc N)) (h : Euc N ≃ₜ Euc N)
    (w : W) (hw : w ∈ e.source)
    (Y : Work.Orient.RelH (Modl N) N ({h (e w)} : Set (Euc N))) :
    chartTr (e.transHomeomorph h) w hw Y
      = RelHmapOf N (eSymmA (e.transHomeomorph h))
          (punctSet (Modl N) (e.transHomeomorph h).target ((e.transHomeomorph h) w))
          ({w} : Set W) (fun z hz => eSymmA_pair (e.transHomeomorph h) w hw hz)
          ((punctIso (Modl N) N (e.transHomeomorph h).target (e.transHomeomorph h).open_target
            ((e.transHomeomorph h) w) ((e.transHomeomorph h).map_source hw)
            isClosed_singleton).symm.toLinearMap Y) := rfl

/-- **The bridge** between the unfolded spelling of the composite and the spelling produced by
`chartTr_apply` for `e.transHomeomorph h`. -/
theorem chartTr_transHomeomorph_bridge (e : OpenPartialHomeomorph W (Euc N)) (h : Euc N ≃ₜ Euc N)
    (w : W) (hw : w ∈ e.source)
    (Y : Work.Orient.RelH (Modl N) N ({h (e w)} : Set (Euc N))) :
    RelHmapOf N (eSymmA (e.transHomeomorph h))
        (punctSet (Modl N) (e.transHomeomorph h).target ((e.transHomeomorph h) w))
        ({w} : Set W) (fun z hz => eSymmA_pair (e.transHomeomorph h) w hw hz)
        ((punctIso (Modl N) N (e.transHomeomorph h).target (e.transHomeomorph h).open_target
          ((e.transHomeomorph h) w) ((e.transHomeomorph h).map_source hw)
          isClosed_singleton).symm.toLinearMap Y)
      = RelHmapOf N (hSub e h ≫ eSymmA e) (tK e h w) ({w} : Set W)
          (fun z hz => eSymmA_pair e w hw (hSub_pair e h w hw z hz))
          ((punctIso (Modl N) N (h.symm ⁻¹' e.target) (e.open_target.preimage h.symm.continuous)
            (h (e w)) (hSub_mem e h w hw) isClosed_singleton).symm.toLinearMap Y) := rfl

theorem chartTr_transHomeomorph {N : ℕ} {W : TopCat} [T1Space W]
    (e : OpenPartialHomeomorph W (EuclideanSpace ℝ (Fin N)))
    (h : EuclideanSpace ℝ (Fin N) ≃ₜ EuclideanSpace ℝ (Fin N))
    (w : W) (hw : w ∈ e.source)
    (Y : Work.Orient.RelH (TopCat.of (EuclideanSpace ℝ (Fin N))) N
          ({h (e w)} : Set (EuclideanSpace ℝ (Fin N)))) :
    Work.PTGeometric.HOF.chartTr (e.transHomeomorph h) w hw Y
      = Work.PTGeometric.HOF.chartTr e w hw
          (Work.PTGeometric.HOF.RelHmapOf N (TopCat.ofHom ⟨fun z => h.symm z, h.continuous_invFun⟩)
            ({h (e w)} : Set (EuclideanSpace ℝ (Fin N)))
            ({e w} : Set (EuclideanSpace ℝ (Fin N)))
            (fun z hz => by
              simp only [Set.mem_singleton_iff] at hz ⊢
              intro hh
              exact hz (by rw [← hh]; exact (h.apply_symm_apply z).symm)) Y) := by
  calc chartTr (e.transHomeomorph h) w hw Y
      = RelHmapOf N (eSymmA (e.transHomeomorph h))
          (punctSet (Modl N) (e.transHomeomorph h).target ((e.transHomeomorph h) w))
          ({w} : Set W) (fun z hz => eSymmA_pair (e.transHomeomorph h) w hw hz)
          ((punctIso (Modl N) N (e.transHomeomorph h).target (e.transHomeomorph h).open_target
            ((e.transHomeomorph h) w) ((e.transHomeomorph h).map_source hw)
            isClosed_singleton).symm.toLinearMap Y) := chartTr_transHomeomorph_apply e h w hw Y
    _ = RelHmapOf N (hSub e h ≫ eSymmA e) (tK e h w) ({w} : Set W)
          (fun z hz => eSymmA_pair e w hw (hSub_pair e h w hw z hz))
          ((punctIso (Modl N) N (h.symm ⁻¹' e.target) (e.open_target.preimage h.symm.continuous)
            (h (e w)) (hSub_mem e h w hw) isClosed_singleton).symm.toLinearMap Y) :=
        chartTr_transHomeomorph_bridge e h w hw Y
    _ = RelHmapOf N (eSymmA e) (eK e w) ({w} : Set W)
          (fun z hz => eSymmA_pair e w hw hz)
          (RelHmapOf N (hSub e h) (tK e h w) (eK e w) (hSub_pair e h w hw)
            ((punctIso (Modl N) N (h.symm ⁻¹' e.target)
              (e.open_target.preimage h.symm.continuous) (h (e w)) (hSub_mem e h w hw)
              isClosed_singleton).symm.toLinearMap Y)) :=
        relHmapOf_eSymmA_comp e h w hw
          ((punctIso (Modl N) N (h.symm ⁻¹' e.target)
            (e.open_target.preimage h.symm.continuous) (h (e w)) (hSub_mem e h w hw)
            isClosed_singleton).symm.toLinearMap Y)
    _ = RelHmapOf N (eSymmA e) (eK e w) ({w} : Set W)
          (fun z hz => eSymmA_pair e w hw hz)
          ((punctIso (Modl N) N e.target e.open_target (e w) (e.map_source hw)
            isClosed_singleton).symm.toLinearMap
            (RelHmapOf N (hAmb h) ({h (e w)} : Set (Euc N)) ({e w} : Set (Euc N))
              (hAmb_pair e h w) Y)) :=
        congrArg (fun t => RelHmapOf N (eSymmA e) (eK e w) ({w} : Set W)
          (fun z hz => eSymmA_pair e w hw hz) t) (punctIso_symm_Hsub e h w hw Y)
    _ = chartTr e w hw
          (RelHmapOf N (hAmb h) ({h (e w)} : Set (Euc N)) ({e w} : Set (Euc N))
            (hAmb_pair e h w) Y) :=
        (Work.PTGeometric.HOF.chartTr_apply e w hw
          (RelHmapOf N (hAmb h) ({h (e w)} : Set (Euc N)) ({e w} : Set (Euc N))
            (hAmb_pair e h w) Y)).symm

end

end Work.ThomBordism.PosAtlas
