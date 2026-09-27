import Mathlib
import Submission.Work.Engulf.Tools
import Submission.Work.Engulf.Basic
import Submission.Work.Geo.Radial.ChartImage
import Submission.Work.Geo.Radial.continuousOn_chartInv
import Submission.Work.Geo.Radial.ext_homeo_open
import Submission.Work.Cells.Connell.connell_aux

/-!
# Conjugating a supported self-homeomorphism of `ℝⁿ` through a cube chart

`Work.Engulf.E4alt.conjChart`: a self-homeomorphism `h` of `ℝⁿ` which is the identity outside the
open cube of radius `β < 1` conjugates, through any cube chart `ψ : PL.CubeChart n M`, to a
self-homeomorphism `H` of `M` supported in the compact image `ψ '' PL.closedCube β`, agreeing with
`ψ ∘ h ∘ ψ⁻¹` on the chart image `ψ '' PL.openCube 1` and fixing everything outside it.

The proof is the elementary one.  Because `h` is the identity outside `openCube β`, it preserves the
open unit cube, so it restricts to a self-homeomorphism of `↥(openCube 1)`; transporting along the
chart gives a self-homeomorphism `hO` of `O := ψ '' openCube 1` which is the identity off the
compact set `C := O ∩ ψ '' closedCube β`.  The blueprint's `C0`
(`Work.Geo.Radial.ext_homeo_open`) then extends `hO` to `M` by the identity off `O`.
-/

open Set Metric

namespace Work.Engulf.E4alt

variable {n : ℕ} {M : Type*}

/-! ## Elementary stability properties of `h` -/

/-- A self-homeomorphism of `E n` which fixes everything outside `PL.openCube β` maps
`PL.openCube β` into itself. -/
lemma mapsTo_openCube {β : ℝ} (h : PL.E n ≃ₜ PL.E n)
    (hfix : ∀ x, x ∉ PL.openCube (n := n) β → h x = x) :
    ∀ y, y ∈ PL.openCube (n := n) β → h y ∈ PL.openCube (n := n) β := by
  intro y hy
  by_contra hc
  have hy' : h y = y := h.injective (hfix (h y) hc)
  exact hc (by rw [hy']; exact hy)

/-- A self-homeomorphism of `E n` which fixes everything outside `PL.openCube β`, `β < 1`, maps
the open unit cube into itself. -/
lemma mapsTo_openCube_one {β : ℝ} (hβ1 : β < 1) (h : PL.E n ≃ₜ PL.E n)
    (hfix : ∀ x, x ∉ PL.openCube (n := n) β → h x = x) :
    ∀ y, y ∈ PL.openCube (n := n) 1 → h y ∈ PL.openCube (n := n) 1 := by
  intro y hy
  by_contra hc
  by_cases hyb : y ∈ PL.openCube (n := n) β
  · exact hc (Work.Engulf.openCube_mono (le_of_lt hβ1)
      (mapsTo_openCube (n := n) h hfix y hyb))
  · rw [hfix y hyb] at hc
    exact hc hy

/-- The inverse of a self-homeomorphism of `E n` which fixes everything outside `PL.openCube β`,
`β < 1`, maps the open unit cube into itself. -/
lemma symm_mapsTo_openCube_one {β : ℝ} (hβ1 : β < 1) (h : PL.E n ≃ₜ PL.E n)
    (hfix : ∀ x, x ∉ PL.openCube (n := n) β → h x = x) :
    ∀ y, y ∈ PL.openCube (n := n) 1 → h.symm y ∈ PL.openCube (n := n) 1 := by
  intro y hy
  by_cases hwb : h.symm y ∈ PL.openCube (n := n) β
  · exact Work.Engulf.openCube_mono (le_of_lt hβ1) hwb
  · have h3 : h (h.symm y) = h.symm y := hfix (h.symm y) hwb
    rw [h.apply_symm_apply y] at h3
    rw [h3.symm]
    exact hy

/-! ## The induced homeomorphism of the chart image -/

/-- The conjugation of `h` through the chart `ψ`, as a self-homeomorphism of the chart image
`ψ '' PL.openCube 1`.  It is the identity off `ψ '' PL.closedCube β`. -/
theorem exists_conj_homeo {n : ℕ} {M : Type*} [TopologicalSpace M]
    (ψ : PL.CubeChart n M) {β : ℝ} (hβ1 : β < 1) (h : PL.E n ≃ₜ PL.E n)
    (hfix : ∀ x, x ∉ PL.openCube (n := n) β → h x = x) :
    ∃ hO : ↥(ψ.toFun '' PL.openCube (n := n) 1) ≃ₜ ↥(ψ.toFun '' PL.openCube (n := n) 1),
      (∀ x (hx : x ∈ PL.openCube (n := n) 1),
        (hO ⟨ψ.toFun x, ⟨x, hx, rfl⟩⟩ : M) = ψ.toFun (h x)) ∧
      (∀ x : ↥(ψ.toFun '' PL.openCube (n := n) 1),
        (x : M) ∉ ψ.toFun '' PL.closedCube (n := n) β → hO x = x) := by
  have hmem1 := mapsTo_openCube_one hβ1 h hfix
  have hmem1s := symm_mapsTo_openCube_one hβ1 h hfix
  -- the two branches land in the chart image
  have key : ∀ z : M, z ∈ ψ.toFun '' PL.openCube (n := n) 1 →
      ψ.toFun (h (Work.Geo.Radial.chartInv ψ z)) ∈ ψ.toFun '' PL.openCube (n := n) 1 :=
    fun z hz => ⟨h (Work.Geo.Radial.chartInv ψ z),
      hmem1 _ (Work.Geo.Radial.chartInv_mem ψ hz), rfl⟩
  have keyinv : ∀ z : M, z ∈ ψ.toFun '' PL.openCube (n := n) 1 →
      ψ.toFun (h.symm (Work.Geo.Radial.chartInv ψ z)) ∈ ψ.toFun '' PL.openCube (n := n) 1 :=
    fun z hz => ⟨h.symm (Work.Geo.Radial.chartInv ψ z),
      hmem1s _ (Work.Geo.Radial.chartInv_mem ψ hz), rfl⟩
  -- the two branches are continuous on the chart image
  have hcF : ContinuousOn (fun z : M => ψ.toFun (h (Work.Geo.Radial.chartInv ψ z)))
      (ψ.toFun '' PL.openCube (n := n) 1) :=
    ψ.cont.comp (h.continuous.comp_continuousOn (Work.Geo.Radial.continuousOn_chartInv ψ))
      (fun z hz => hmem1 _ (Work.Geo.Radial.chartInv_mem ψ hz))
  have hcG : ContinuousOn (fun z : M => ψ.toFun (h.symm (Work.Geo.Radial.chartInv ψ z)))
      (ψ.toFun '' PL.openCube (n := n) 1) :=
    ψ.cont.comp (h.symm.continuous.comp_continuousOn (Work.Geo.Radial.continuousOn_chartInv ψ))
      (fun z hz => hmem1s _ (Work.Geo.Radial.chartInv_mem ψ hz))
  -- the two branches, as maps of the chart image
  let FF : ↥(ψ.toFun '' PL.openCube (n := n) 1) → ↥(ψ.toFun '' PL.openCube (n := n) 1) :=
    fun x => ⟨ψ.toFun (h (Work.Geo.Radial.chartInv ψ (x : M))), key (x : M) x.2⟩
  let GG : ↥(ψ.toFun '' PL.openCube (n := n) 1) → ↥(ψ.toFun '' PL.openCube (n := n) 1) :=
    fun x => ⟨ψ.toFun (h.symm (Work.Geo.Radial.chartInv ψ (x : M))), keyinv (x : M) x.2⟩
  have hcontFF : Continuous FF := by
    refine Continuous.subtype_mk ?_ _
    exact continuousOn_iff_continuous_domRestrict.mp hcF
  have hcontGG : Continuous GG := by
    refine Continuous.subtype_mk ?_ _
    exact continuousOn_iff_continuous_domRestrict.mp hcG
  have hleft : Function.LeftInverse GG FF := by
    intro x
    apply Subtype.ext
    have h1 : h (Work.Geo.Radial.chartInv ψ (x : M)) ∈ PL.openCube (n := n) 1 :=
      hmem1 _ (Work.Geo.Radial.chartInv_mem ψ x.2)
    have h2 : Work.Geo.Radial.chartInv ψ
        (ψ.toFun (h (Work.Geo.Radial.chartInv ψ (x : M)))) =
        h (Work.Geo.Radial.chartInv ψ (x : M)) :=
      Work.Geo.Radial.chartInv_apply ψ h1
    show ψ.toFun (h.symm (Work.Geo.Radial.chartInv ψ
      (ψ.toFun (h (Work.Geo.Radial.chartInv ψ (x : M)))))) = (x : M)
    rw [h2, h.symm_apply_apply, Work.Geo.Radial.chartInv_toFun ψ x.2]
  have hright : Function.RightInverse GG FF := by
    intro x
    apply Subtype.ext
    have h1 : h.symm (Work.Geo.Radial.chartInv ψ (x : M)) ∈ PL.openCube (n := n) 1 :=
      hmem1s _ (Work.Geo.Radial.chartInv_mem ψ x.2)
    have h2 : Work.Geo.Radial.chartInv ψ
        (ψ.toFun (h.symm (Work.Geo.Radial.chartInv ψ (x : M)))) =
        h.symm (Work.Geo.Radial.chartInv ψ (x : M)) :=
      Work.Geo.Radial.chartInv_apply ψ h1
    show ψ.toFun (h (Work.Geo.Radial.chartInv ψ
      (ψ.toFun (h.symm (Work.Geo.Radial.chartInv ψ (x : M)))))) = (x : M)
    rw [h2, h.apply_symm_apply, Work.Geo.Radial.chartInv_toFun ψ x.2]
  let hO : ↥(ψ.toFun '' PL.openCube (n := n) 1) ≃ₜ ↥(ψ.toFun '' PL.openCube (n := n) 1) :=
    Homeomorph.mk (Equiv.mk FF GG hleft hright) hcontFF hcontGG
  have hO_apply : ∀ x (hx : x ∈ PL.openCube (n := n) 1),
      (hO ⟨ψ.toFun x, ⟨x, hx, rfl⟩⟩ : M) = ψ.toFun (h x) := by
    intro x hx
    show ψ.toFun (h (Work.Geo.Radial.chartInv ψ (ψ.toFun x))) = ψ.toFun (h x)
    rw [Work.Geo.Radial.chartInv_apply ψ hx]
  have hO_id : ∀ x : ↥(ψ.toFun '' PL.openCube (n := n) 1),
      (x : M) ∉ ψ.toFun '' PL.closedCube (n := n) β → hO x = x := by
    intro x hx
    apply Subtype.ext
    have hy2 : ψ.toFun (Work.Geo.Radial.chartInv ψ (x : M)) = (x : M) :=
      Work.Geo.Radial.chartInv_toFun ψ x.2
    have hyc : Work.Geo.Radial.chartInv ψ (x : M) ∉ PL.closedCube (n := n) β := by
      intro hm
      exact hx ⟨Work.Geo.Radial.chartInv ψ (x : M), hm, hy2⟩
    have hyb : Work.Geo.Radial.chartInv ψ (x : M) ∉ PL.openCube (n := n) β :=
      fun hh => hyc (fun i => le_of_lt (hh i))
    show ψ.toFun (h (Work.Geo.Radial.chartInv ψ (x : M))) = (x : M)
    rw [hfix _ hyb, hy2]
  exact ⟨hO, hO_apply, hO_id⟩

/-! ## The main statement -/

set_option linter.style.haveILetI false in
set_option linter.unusedVariables false in
theorem conjChart {n : ℕ} {M : Type*} [MetricSpace M] (T : Work.Engulf.ToolsAll n)
    (ψ : PL.CubeChart n M) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (h : PL.E n ≃ₜ PL.E n) (hfix : ∀ x, x ∉ PL.openCube (n := n) β → h x = x) :
    ∃ H : M ≃ₜ M, PL.CSupp H (ψ.toFun '' PL.closedCube β) ∧
      (∀ x ∈ PL.openCube (n := n) 1, H (ψ.toFun x) = ψ.toFun (h x)) ∧
      (∀ z : M, z ∉ ψ.toFun '' PL.openCube (n := n) 1 → H z = z) := by
  obtain ⟨hO, hO_apply, hO_id⟩ := exists_conj_homeo ψ hβ1 h hfix
  have hOopen : IsOpen (ψ.toFun '' PL.openCube (n := n) 1) :=
    Work.Geo.Radial.isOpen_chartImage ψ
  have hScomp : IsCompact (ψ.toFun '' PL.closedCube (n := n) β) :=
    Work.Geo.Radial.isCompact_image_closedCube ψ β hβ1
  have hSO : ψ.toFun '' PL.closedCube (n := n) β ⊆ ψ.toFun '' PL.openCube (n := n) 1 :=
    Set.image_mono (Work.Engulf.closedCube_subset_openCube hβ1)
  -- `C` is the image of the compact `ψ '' closedCube β` inside the chart image
  have hCcomp : IsCompact {x : ↥(ψ.toFun '' PL.openCube (n := n) 1) |
      (x : M) ∈ ψ.toFun '' PL.closedCube (n := n) β} := by
    haveI : CompactSpace ↥(ψ.toFun '' PL.closedCube (n := n) β) :=
      isCompact_iff_compactSpace.mp hScomp
    have hcont : Continuous fun y : ↥(ψ.toFun '' PL.closedCube (n := n) β) =>
        (⟨(y : M), hSO y.2⟩ : ↥(ψ.toFun '' PL.openCube (n := n) 1)) :=
      Continuous.subtype_mk continuous_subtype_val (fun y => hSO y.2)
    have heq : {x : ↥(ψ.toFun '' PL.openCube (n := n) 1) |
          (x : M) ∈ ψ.toFun '' PL.closedCube (n := n) β}
        = (fun y : ↥(ψ.toFun '' PL.closedCube (n := n) β) =>
            (⟨(y : M), hSO y.2⟩ : ↥(ψ.toFun '' PL.openCube (n := n) 1))) '' univ := by
      ext x
      constructor
      · intro hx
        have hx' : (x : M) ∈ ψ.toFun '' PL.closedCube (n := n) β := hx
        obtain ⟨y, hy, hyx⟩ := hx'
        exact ⟨⟨ψ.toFun y, ⟨y, hy, rfl⟩⟩, trivial, Subtype.ext hyx⟩
      · rintro ⟨y, -, hyx⟩
        rw [← hyx]
        exact y.2
    rw [heq]
    exact isCompact_univ.image hcont
  obtain ⟨H, hH_on, hH_off⟩ := Work.Geo.Radial.ext_homeo_open
    (ψ.toFun '' PL.openCube (n := n) 1) hOopen hO
    {x : ↥(ψ.toFun '' PL.openCube (n := n) 1) |
      (x : M) ∈ ψ.toFun '' PL.closedCube (n := n) β} hCcomp hO_id
  refine ⟨H, ?_, ?_, ?_⟩
  · refine ⟨ψ.toFun '' PL.closedCube (n := n) β, hScomp, subset_rfl, ?_⟩
    intro z hz
    by_cases hzO : z ∈ ψ.toFun '' PL.openCube (n := n) 1
    · rw [hH_on ⟨z, hzO⟩]
      exact congrArg Subtype.val (hO_id ⟨z, hzO⟩ hz)
    · exact hH_off z hzO
  · intro x hx
    rw [hH_on ⟨ψ.toFun x, ⟨x, hx, rfl⟩⟩]
    exact hO_apply x hx
  · intro z hz
    exact hH_off z hz

end Work.Engulf.E4alt
