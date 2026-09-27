import Mathlib
import Submission.Work.PL.Defs
import Submission.Work.Cells.Connell.Defs
import Submission.Work.Cells.Connell.cubeChart_injOn
import Submission.Work.Cells.Connell.cubeChart_isOpen_image_openCube
import Submission.Work.Cells.Connell.cubeChart_isCompact_image_closedCube
import Submission.Work.Cells.Connell.cubeChart_homeoOn_apply
import Submission.Work.Cells.Connell.exists_closedCube_subset_of_isCompact_subset_openCube
import Submission.Work.Cells.Connell.exists_thinFamily_of_domDim

/-!
# Auxiliary lemmas for Connell's cell-count reduction (`Work.Cells.Connell`)

Small topological lemmas used by `connell_step` and its two main ingredients
(`engulf_skel`, `stretch_homeo`).  Nothing here is special to the argument.
-/

open Set Metric

set_option linter.unusedVariables false

namespace Work.Cells.Connell

/-! ## Monotonicity and elementary facts about sup-norm cubes -/

theorem closedCube_mono {n : ℕ} {r r' : ℝ} (h : r ≤ r') :
    PL.closedCube (n := n) r ⊆ PL.closedCube (n := n) r' :=
  fun _ hx i => le_trans (hx i) h

/-- The open cube of radius `β` sits inside the closed cube of radius `β` (for `β ≥ 0`). -/
theorem openCube_subset_closedCube {n : ℕ} {β : ℝ} :
    PL.openCube (n := n) β ⊆ PL.closedCube (n := n) β :=
  fun _ hx i => le_of_lt (hx i)

/-- A point of the open unit cube outside the closed `β`-cube, for `0 < β < 1` and `n ≥ 1`. -/
theorem exists_mem_openCube_notMem_closedCube {n : ℕ} (hn : 1 ≤ n) {β : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ z : PL.E n, z ∈ PL.openCube (n := n) 1 ∧ z ∉ PL.closedCube (n := n) β := by
  let c : ℝ := (β + 1) / 2
  have hc0 : 0 < c := by simp only [c]; linarith
  have hcβ : β < c := by simp only [c]; linarith
  have hc1 : c < 1 := by simp only [c]; linarith
  refine ⟨(PiLp.homeomorph 2 (fun _ : Fin n => ℝ)).symm (fun _ => c), ?_, ?_⟩
  · intro i
    have hcoord : (PiLp.homeomorph 2 (fun _ : Fin n => ℝ)).symm (fun _ => c) i = c := by
      simp [PiLp.homeomorph]
    rw [hcoord, abs_of_pos hc0]; exact hc1
  · intro hc
    have hcoord : (PiLp.homeomorph 2 (fun _ : Fin n => ℝ)).symm (fun _ => c) ⟨0, hn⟩ = c := by
      simp [PiLp.homeomorph]
    have := hc ⟨0, hn⟩
    rw [hcoord, abs_of_pos hc0] at this
    linarith

/-! ## Compactness in a subtype

The preimage of a compact set under the inclusion of a subtype is compact, provided the compact
set is already contained in the subtype. -/

theorem isCompact_subtype_preimage_of_subset {X : Type*} [TopologicalSpace X]
    {s K : Set X} (hK : IsCompact K) (hKs : K ⊆ s) :
    IsCompact {x : ↥s | (x : X) ∈ K} := by
  set A : Set ↥s := {x | (x : X) ∈ K} with hA
  have hhomeo : Nonempty (↥K ≃ₜ ↥A) := ⟨{
    toFun := fun w => ⟨⟨(w : X), hKs w.2⟩, w.2⟩
    invFun := fun a => ⟨(a.1 : X), a.2⟩
    left_inv := fun w => Subtype.ext rfl
    right_inv := fun a => Subtype.ext (Subtype.ext rfl)
    continuous_toFun := Continuous.subtype_mk
      (Continuous.subtype_mk continuous_subtype_val (fun w => hKs w.2)) (fun w => w.2)
    continuous_invFun := Continuous.subtype_mk
      (continuous_subtype_val.comp continuous_subtype_val) (fun a => a.2) }⟩
  obtain ⟨e⟩ := hhomeo
  rw [isCompact_iff_compactSpace]
  haveI : CompactSpace ↥K := isCompact_iff_compactSpace.mp hK
  exact e.compactSpace

/-! ## Openness of a chart cube intersected with the preimage of an open set -/

/-- For a cube chart `c` and an open set `U ⊆ M`, the set of points of the open unit cube that
`c` maps into `U` is open in `ℝⁿ`. -/
theorem isOpen_setOf_openCube_and_chart_mem {n : ℕ} {M : Type*} [TopologicalSpace M]
    (c : PL.CubeChart n M) {U : Set M} (hU : IsOpen U) :
    IsOpen {z : PL.E n | z ∈ PL.openCube (n := n) 1 ∧ c.toFun z ∈ U} := by
  set s := PL.openCube (n := n) 1 with hs
  have hso : IsOpen s := isOpen_openCube n 1
  have hcont : Continuous (s.domRestrict c.toFun) :=
    continuousOn_iff_continuous_domRestrict.mp c.cont
  have hpre : IsOpen (((s).domRestrict c.toFun) ⁻¹' U) := hcont.isOpen_preimage U hU
  have himg : IsOpen (Subtype.val '' (((s).domRestrict c.toFun) ⁻¹' U)) :=
    hso.isOpenMap_subtype_val _ hpre
  have hset : Subtype.val '' (((s).domRestrict c.toFun) ⁻¹' U)
      = {z : PL.E n | z ∈ PL.openCube (n := n) 1 ∧ c.toFun z ∈ U} := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩; exact ⟨w.2, hw⟩
    · rintro ⟨hz1, hz2⟩; exact ⟨⟨z, hz1⟩, hz2, rfl⟩
  rw [hset] at himg
  exact himg

/-! ## A nowhere-dense image misses a nonempty open set

This is `exists_notMem_image_of_thinFamily` without its (unused) chart hypothesis. -/

theorem exists_notMem_image_of_thinFamily' {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
    (A : Set M) (hA : IsClosed A) (hAne : (Aᶜ).Nonempty)
    (c : PL.CubeChart n M) {ι : Type} [Finite ι] (F : ι → Set (PL.E n)) (hF : ThinFamily F)
    {L : Set (PL.E n)} (hL : L ⊆ ⋃ i, F i) :
    ∃ p, p ∈ Aᶜ ∧ p ∉ c.toFun '' L := by
  have hFnd : ∀ i, IsNowhereDense (F i) :=
    fun i => ((hF i).1.isClosed).isNowhereDense_iff.mpr (hF i).2.2
  have hndL : IsNowhereDense L := (IsNowhereDense.iUnion hFnd).mono hL
  have hIntClL : interior (closure L) = ∅ := hndL
  have hIntL : interior L = ∅ :=
    eq_empty_of_subset_empty (hIntClL ▸ interior_mono subset_closure)
  have himg : interior (c.toFun '' L) = ∅ := by
    let U : Set (PL.E n) := PL.openCube (n := n) 1
    have hUopen : IsOpen U := isOpen_openCube n 1
    have hLU : L ⊆ U := by
      intro x hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp (hL hx)
      exact (hF i).2.1 hi
    let L' : Set ↥U := Subtype.val ⁻¹' L
    have hL'val : Subtype.val '' L' = L := by
      ext x; constructor
      · rintro ⟨y, hy, rfl⟩; exact hy
      · intro hx; exact ⟨⟨x, hLU hx⟩, hx, rfl⟩
    have hL'nd : IsNowhereDense L' := by
      rw [IsNowhereDense]
      have hcl : closure L' = Subtype.val ⁻¹' closure L := by
        rw [hUopen.isOpenEmbedding_subtypeVal.isEmbedding.closure_eq_preimage_closure_image L',
          hL'val]
      rw [hcl, ← hUopen.isOpenMap_subtype_val.preimage_interior_eq_interior_preimage
            continuous_subtype_val (closure L), hIntClL, preimage_empty]
    have hndImg : IsNowhereDense ((U.domRestrict c.toFun) '' L') :=
      c.emb.isInducing.isNowhereDense_image hL'nd
    have heq : (U.domRestrict c.toFun) '' L' = c.toFun '' L := by
      ext y; constructor
      · rintro ⟨x, hx, rfl⟩; exact ⟨x.1, hx, rfl⟩
      · rintro ⟨x, hx, rfl⟩; exact ⟨⟨x, hLU hx⟩, hx, rfl⟩
    rw [heq] at hndImg
    exact eq_empty_of_subset_empty (hndImg ▸ interior_mono subset_closure)
  by_contra hcon
  push Not at hcon
  have hsub : Aᶜ ⊆ c.toFun '' L := fun x hx => hcon x hx
  have hle : Aᶜ ⊆ interior (c.toFun '' L) := interior_maximal hsub hA.isOpen_compl
  rw [himg] at hle
  obtain ⟨p, hp⟩ := hAne
  exact (notMem_empty p) (hle hp)

/-! ## Conjugating a self-homeomorphism of the open cube by a chart -/

/-- A self-homeomorphism `h` of `ℝⁿ` that fixes every point outside the open cube of radius
`β < 1` maps the open unit cube into itself, hence restricts to a self-homeomorphism of it. -/
theorem mapsTo_openCube_of_fix_outside {n : ℕ} {β : ℝ} (hβ1 : β < 1)
    (h : PL.E n ≃ₜ PL.E n) (hh : ∀ x, x ∉ PL.openCube (n := n) β → h x = x) :
    ∀ x ∈ PL.openCube (n := n) 1, h x ∈ PL.openCube (n := n) 1 := by
  intro x hx
  have hh' : ∀ x, x ∉ PL.closedCube (n := n) β → h x = x :=
    fun x hx => hh x (fun hxo => hx (openCube_subset_closedCube hxo))
  have himg : h '' PL.closedCube (n := n) β = PL.closedCube (n := n) β := by
    apply Set.Subset.antisymm
    · rintro y ⟨w, hw, rfl⟩
      by_contra hy
      have h1 : h (h w) = h w := hh' (h w) hy
      have h2 : h w = w := h.injective h1
      exact hy (h2.symm ▸ hw)
    · intro y hy
      refine ⟨h.symm y, ?_, h.apply_symm_apply y⟩
      by_contra hc
      have h1 : h (h.symm y) = h.symm y := hh' (h.symm y) hc
      rw [h.apply_symm_apply] at h1
      exact hc (h1 ▸ hy)
  by_cases hxc : x ∈ PL.closedCube (n := n) β
  · have : h x ∈ PL.closedCube (n := n) β := by
      rw [← himg]; exact ⟨x, hxc, rfl⟩
    exact fun i => lt_of_le_of_lt (this i) hβ1
  · rw [hh' x hxc]; exact hx

/-- Conjugate a self-homeomorphism `h` of `ℝⁿ` supported off the complement of `openCube β`
(`β < 1`) by a cube chart `c`: the result is a self-homeomorphism of the cell `c '' openCube 1`
that acts as `z ↦ c (h z)` and is the identity outside `c '' closedCube β`. -/
theorem chart_conj {n : ℕ} {M : Type*} [TopologicalSpace M]
    (c : PL.CubeChart n M) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (h : PL.E n ≃ₜ PL.E n) (hh : ∀ x, x ∉ PL.openCube (n := n) β → h x = x) :
    ∃ g : ↥(c.toFun '' PL.openCube (n := n) 1) ≃ₜ ↥(c.toFun '' PL.openCube (n := n) 1),
      (∀ z (hz : z ∈ PL.openCube (n := n) 1),
        (g ⟨c.toFun z, ⟨z, hz, rfl⟩⟩ : M) = c.toFun (h z)) ∧
      (∀ x : ↥(c.toFun '' PL.openCube (n := n) 1),
        (x : M) ∉ c.toFun '' PL.closedCube (n := n) β → g x = x) := by
  have hsub : PL.openCube (n := n) β ⊆ PL.closedCube (n := n) β := openCube_subset_closedCube
  have hh' : ∀ x, x ∉ PL.closedCube (n := n) β → h x = x :=
    fun x hx => hh x (fun hxo => hx (hsub hxo))
  have hhs : ∀ x, x ∉ PL.openCube (n := n) β → h.symm x = x :=
    fun x hx => (congrArg h.symm (hh x hx)).symm.trans (h.symm_apply_apply x)
  have hmap := mapsTo_openCube_of_fix_outside hβ1 h hh
  have hmap' := mapsTo_openCube_of_fix_outside hβ1 h.symm hhs
  let h' : ↥(PL.openCube (n := n) 1) ≃ₜ ↥(PL.openCube (n := n) 1) :=
    { toFun := fun x => ⟨h x, hmap x x.2⟩
      invFun := fun x => ⟨h.symm x, hmap' x x.2⟩
      left_inv := fun x => Subtype.ext (h.symm_apply_apply (x : PL.E n))
      right_inv := fun x => Subtype.ext (h.apply_symm_apply (x : PL.E n))
      continuous_toFun := Continuous.subtype_mk
        (h.continuous.comp continuous_subtype_val) (fun x => hmap x x.2)
      continuous_invFun := Continuous.subtype_mk
        (h.symm.continuous.comp continuous_subtype_val) (fun x => hmap' x x.2) }
  obtain ⟨e, he⟩ := cubeChart_homeoOn_apply c (isOpen_openCube n 1) (fun _ hx => hx)
  have hev : ∀ z (hz : z ∈ PL.openCube (n := n) 1),
      e ⟨z, hz⟩ = (⟨c.toFun z, ⟨z, hz, rfl⟩⟩ : ↥(c.toFun '' PL.openCube (n := n) 1)) :=
    fun z hz => Subtype.ext (he ⟨z, hz⟩)
  refine ⟨(e.symm.trans h').trans e, ?_, ?_⟩
  · intro z hz
    have h1 : ((e.symm.trans h').trans e) ⟨c.toFun z, ⟨z, hz, rfl⟩⟩ = e (h' ⟨z, hz⟩) := by
      rw [← hev z hz, Homeomorph.trans_apply, Homeomorph.trans_apply,
        Homeomorph.symm_apply_apply]
    rw [h1]
    show (e (h' ⟨z, hz⟩) : M) = c.toFun (h z)
    rw [he]
    rfl
  · intro x hx
    obtain ⟨z, hz, hzx⟩ := x.2
    have hx1 : x = e ⟨z, hz⟩ := by
      apply Subtype.ext
      rw [he]
      exact hzx.symm
    rw [hx1, Homeomorph.trans_apply, Homeomorph.trans_apply, Homeomorph.symm_apply_apply]
    have hzc : z ∉ PL.closedCube (n := n) β := by
      intro hzc
      exact hx ⟨z, hzc, hzx⟩
    have hzo : z ∉ PL.openCube (n := n) β := fun ho => hzc (hsub ho)
    have hhz : h z = z := hh z hzo
    have hh'z : h' ⟨z, hz⟩ = ⟨z, hz⟩ := by
      apply Subtype.ext
      show h z = z
      exact hhz
    rw [hh'z]

end Work.Cells.Connell
