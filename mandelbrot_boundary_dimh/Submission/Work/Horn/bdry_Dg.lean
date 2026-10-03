import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Interfaces.HornParts
import Submission.Work.Horn.basic
import Submission.Work.HornCov.sheet_Phi
import Submission.Work.Horn.pushdown_covering

/-!
# `Work.Horn.bdry_Dg` — the boundary of the horn domain `D_g` and the properness clause

This module isolates the **exact** obstruction to the properness clause
`∀ L ⊆ B', IsCompact L → IsCompact (B' ∩ g ⁻¹' L)` of `MandelDim.IsImmediateBasin` for the
pushed-down horn map `g = pushdown d.E` (the last clause needed by `Work.Horn.horn_germ_F0`).

## 1. Characterization of properness

For a connected component `B'` of the parabolic basin of `g` on an open `D`, and a compact
`L ⊆ B'`:

    IsCompact (B' ∩ g ⁻¹' L)   ⟺   closure (B' ∩ g ⁻¹' L) ⊆ D .

`S := B' ∩ g ⁻¹' L` is relatively closed in the basin and bounded; it is closed in `ℂ` exactly when
its closure does not leave `D`, because any limit point staying in `D` maps into the closed `L` by
continuity, hence lies in the basin by backward invariance, hence in the component `B'`.
**So the entire properness content is: the preimages of a compact `L ⊆ B'` do not accumulate on
`∂D`.**

## 2. The boundary of the horn domain

The horn domain is `D_g = insert 0 (π '' (Bu ∪ Bl))`.  The structural fact that makes the boundary
escape *wild*: `MandelDim.Btil d B = Dφ ∩ φ⁻¹ B` is **closed in** `d.DE = Dφ ∩ φ⁻¹ P`, and using
the `T`-invariance of `DE` (interface field `ParabData.DE_T`)

    π '' frontier (Btil d B)  ∩  π '' d.DE  =  ∅ .

Since `g` is holomorphic on the open set `π '' d.DE` (`Work.Repel.pushdown_holo` with `DE_T`), the
points where the properness obstruction can occur (namely `∂D_g`) are exactly points at which `g`
is **not** holomorphic.
-/

namespace Work.Horn

open MandelDim Set Filter Topology Metric
open scoped Topology

noncomputable section

/-- `Btil d B = Dφ ∩ φ⁻¹ B` is open when `B` is. -/
theorem isOpen_Btil {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀) {B : Set ℂ}
    (hB : IsOpen B) : IsOpen (MandelDim.Btil d B) := by
  have h : MandelDim.Btil d B = d.Dφ ∩ d.φ ⁻¹' B := rfl
  rw [h]
  exact d.φ_holo.continuousOn.isOpen_inter_preimage d.Dφ_open hB

/-- The `φ`-image of `Btil d B` lies in `B`. -/
theorem image_phi_Btil_subset {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    {B : Set ℂ} : d.φ '' MandelDim.Btil d B ⊆ B := by
  rintro y ⟨w, hw, rfl⟩
  exact hw.2

/-- **`Btil d B` is closed in `d.DE`.**  If `B` is closed in the parabolic basin (e.g. `B` a
component of it), then a point of `d.DE` in the closure of `Btil d B` already lies in it. -/
theorem Btil_closed_in_DE {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀) {B : Set ℂ}
    (hBcl : ∀ y ∈ MandelDim.ParabolicBasin f₀ D₀, y ∈ closure B → y ∈ B) :
    ∀ w ∈ d.DE, w ∈ closure (MandelDim.Btil d B) → w ∈ MandelDim.Btil d B := by
  intro w hwDE hwcl
  by_contra hw
  have hφbasin : d.φ w ∈ MandelDim.ParabolicBasin f₀ D₀ := hwDE.2
  have hφnotcl : d.φ w ∉ closure B := fun h => hw ⟨hwDE.1, hBcl _ hφbasin h⟩
  have hnot : ¬ (∀ ε : ℝ, 0 < ε → ∃ y ∈ B, dist (d.φ w) y < ε) :=
    fun h => hφnotcl (Metric.mem_closure_iff.mpr h)
  push_neg at hnot
  obtain ⟨ε, hε, hεb⟩ := hnot
  have hcont : ContinuousAt d.φ w :=
    d.φ_holo.continuousOn.continuousAt (d.Dφ_open.mem_nhds hwDE.1)
  obtain ⟨δ, hδ, hδb⟩ := Metric.continuousAt_iff.mp hcont ε hε
  obtain ⟨x, hx, hxd⟩ := Metric.mem_closure_iff.mp hwcl δ hδ
  have h2 : dist (d.φ w) (d.φ x) < ε := by
    rw [dist_comm]
    exact hδb (x := x) (by rwa [dist_comm] at hxd)
  exact absurd (hεb (d.φ x) hx.2) (not_le.mpr h2)

/-- **The frontier of `Btil d B` misses `d.DE`.** -/
theorem frontier_Btil_disjoint_DE {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    {B : Set ℂ} (hB : IsOpen B)
    (hBcl : ∀ y ∈ MandelDim.ParabolicBasin f₀ D₀, y ∈ closure B → y ∈ B) :
    ∀ w ∈ frontier (MandelDim.Btil d B), w ∉ d.DE := by
  intro w hw hwDE
  rw [(isOpen_Btil d hB).frontier_eq] at hw
  exact hw.2 (Btil_closed_in_DE d hBcl w hwDE hw.1)

/-- **The `π`-images of the frontier of `Btil d B` and of `d.DE` are disjoint** (uses the
`T`-invariance of `d.DE`, i.e. the interface field `ParabData.DE_T`). -/
theorem piExp_frontier_disjoint_piExp_DE {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    {B : Set ℂ} (hT : MandelDim.IsTInvariant d.DE) (hB : IsOpen B)
    (hBcl : ∀ y ∈ MandelDim.ParabolicBasin f₀ D₀, y ∈ closure B → y ∈ B) :
    MandelDim.piExp '' frontier (MandelDim.Btil d B) ∩ MandelDim.piExp '' d.DE = ∅ := by
  rw [← Set.not_nonempty_iff_eq_empty]
  rintro ⟨x, ⟨⟨u, hu, hxu⟩, ⟨w, hw, hxw⟩⟩⟩
  have hpu : MandelDim.piExp u = MandelDim.piExp w := by rw [hxu, hxw]
  obtain ⟨k, hk⟩ := Work.Horn.MandelDim.piExp_eq_iff.mp hpu
  exact frontier_Btil_disjoint_DE d hB hBcl u hu
    (hk ▸ MandelDim.IsTInvariant.add_int hT hw k)

/-- **The properness clause of `MandelDim.IsImmediateBasin` for a component of the basin is
equivalent to "no accumulation at the boundary of the domain".** -/
theorem isCompact_inter_preimage_iff_closure_subset {g : ℂ → ℂ} {D B L : Set ℂ}
    (hDopen : IsOpen D) (hg : DifferentiableOn ℂ g D) (hBsub : B ⊆ D)
    (hBbasin : B ⊆ MandelDim.ParabolicBasin g D)
    (hBcl : ∀ y ∈ MandelDim.ParabolicBasin g D, y ∈ closure B → y ∈ B)
    (hback : ∀ z ∈ D, g z ∈ MandelDim.ParabolicBasin g D →
      z ∈ MandelDim.ParabolicBasin g D)
    (hL : L ⊆ B) (hLc : IsCompact L) (hbdd : Bornology.IsBounded (B ∩ g ⁻¹' L)) :
    IsCompact (B ∩ g ⁻¹' L) ↔ closure (B ∩ g ⁻¹' L) ⊆ D := by
  constructor
  · intro hc
    have hS : closure (B ∩ g ⁻¹' L) = B ∩ g ⁻¹' L := hc.isClosed.closure_eq
    intro z hz
    have hz' : z ∈ B ∩ g ⁻¹' L := hS ▸ hz
    exact hBsub hz'.1
  · intro hcl
    have hclosed : IsClosed (B ∩ g ⁻¹' L) := by
      rw [← closure_subset_iff_isClosed]
      intro p hp
      have hpD : p ∈ D := hcl hp
      have hcont : ContinuousAt g p := hg.continuousOn.continuousAt (hDopen.mem_nhds hpD)
      have hgp : g p ∈ closure (g '' (B ∩ g ⁻¹' L)) := by
        rw [Metric.mem_closure_iff]
        intro ε hε
        obtain ⟨δ, hδ, hδb⟩ := Metric.continuousAt_iff.mp hcont ε hε
        obtain ⟨x, hx, hxd⟩ := Metric.mem_closure_iff.mp hp δ hδ
        refine ⟨g x, ⟨x, hx, rfl⟩, ?_⟩
        rw [dist_comm]
        exact hδb (x := x) (by rwa [dist_comm] at hxd)
      have hgL : g p ∈ L := by
        have h1 : closure (g '' (B ∩ g ⁻¹' L)) ⊆ closure L :=
          closure_mono (fun y ⟨z, hz, hyz⟩ => hyz ▸ (Set.mem_preimage.mp hz.2))
        rw [hLc.isClosed.closure_eq] at h1
        exact h1 hgp
      have hpbasin : p ∈ MandelDim.ParabolicBasin g D := hback p hpD (hBbasin (hL hgL))
      exact ⟨hBcl p hpbasin (closure_mono inter_subset_left hp), hgL⟩
    exact hbdd.isCompact_closure.of_isClosed_subset hclosed subset_closure

/-- `π ⁻¹' frontier A = frontier (π ⁻¹' A)` for the open continuous map `π = piExp`. -/
theorem preimage_frontier_piExp (A : Set ℂ) :
    MandelDim.piExp ⁻¹' frontier A = frontier (MandelDim.piExp ⁻¹' A) := by
  have hcl : ∀ B : Set ℂ, MandelDim.piExp ⁻¹' closure B = closure (MandelDim.piExp ⁻¹' B) := by
    intro B
    refine Set.Subset.antisymm ?_ ?_
    · intro x hx
      rw [Set.mem_preimage] at hx
      rw [Metric.mem_closure_iff] at hx ⊢
      intro ε hε
      have hball : MandelDim.piExp '' Metric.ball x ε ∈ 𝓝 (MandelDim.piExp x) :=
        (Work.Horn.piExp_isOpenMap _ Metric.isOpen_ball).mem_nhds
          ⟨x, Metric.mem_ball_self hε, rfl⟩
      obtain ⟨ε', hε', hε'sub⟩ := Metric.mem_nhds_iff.mp hball
      obtain ⟨y, hyA, hyε⟩ := hx ε' hε'
      obtain ⟨u, hu, huy⟩ := hε'sub (Metric.mem_ball.mpr (by rw [dist_comm]; exact hyε))
      refine ⟨u, ?_, ?_⟩
      · rw [Set.mem_preimage, huy]
        exact hyA
      · rw [dist_comm]
        exact Metric.mem_ball.mp hu
    · intro x hx
      rw [Set.mem_preimage]
      rw [Metric.mem_closure_iff] at hx ⊢
      intro ε hε
      obtain ⟨δ, hδ, hδb⟩ := Metric.continuous_iff.mp Work.Horn.piExp_continuous x ε hε
      obtain ⟨y, hy, hyd⟩ := hx δ hδ
      exact ⟨MandelDim.piExp y, hy, by rw [dist_comm]; exact hδb y (by rwa [dist_comm] at hyd)⟩
  have key : MandelDim.piExp ⁻¹' (closure A ∩ closure Aᶜ)
      = closure (MandelDim.piExp ⁻¹' A) ∩ closure ((MandelDim.piExp ⁻¹' A)ᶜ) := by
    rw [Set.preimage_inter, hcl A, hcl Aᶜ, Set.preimage_compl]
  rw [show frontier A = closure A ∩ closure Aᶜ from frontier_eq_closure_inter_closure,
    show frontier (MandelDim.piExp ⁻¹' A)
      = closure (MandelDim.piExp ⁻¹' A) ∩ closure ((MandelDim.piExp ⁻¹' A)ᶜ) from
        frontier_eq_closure_inter_closure,
    key]

/-- **The frontier of `π '' Bu` misses `π '' DE`** for a `T`-invariant open `Bu` that is closed in
`Btil d B`.  Consequently `g = pushdown d.E` is not holomorphic at any point of the frontier of the
horn domain except possibly `0`. -/
theorem frontier_piExp_component_disjoint_piExp_DE {f₀ : ℂ → ℂ} {D₀ : Set ℂ}
    (d : MandelDim.ParabData f₀ D₀) {B Bu : Set ℂ}
    (hB : IsOpen B)
    (hBcl : ∀ y ∈ MandelDim.ParabolicBasin f₀ D₀, y ∈ closure B → y ∈ B)
    (hBu_sub : Bu ⊆ MandelDim.Btil d B) (hBu_open : IsOpen Bu)
    (hBu_cl : ∀ y ∈ MandelDim.Btil d B, y ∈ closure Bu → y ∈ Bu)
    (hBuT : MandelDim.IsTInvariant Bu) :
    frontier (MandelDim.piExp '' Bu) ∩ MandelDim.piExp '' d.DE = ∅ := by
  -- `π ⁻¹' (π '' Bu) = Bu`
  have hpre : MandelDim.piExp ⁻¹' (MandelDim.piExp '' Bu) = Bu := by
    ext u
    constructor
    · rintro ⟨v, hv, huv⟩
      obtain ⟨k, hk⟩ := Work.Horn.MandelDim.piExp_eq_iff.mp huv
      have huk : u = v + ((-k : ℤ) : ℂ) := by rw [hk]; push_cast; ring
      rw [huk]
      exact MandelDim.IsTInvariant.add_int hBuT hv (-k)
    · intro hu
      exact ⟨u, hu, rfl⟩
  rw [← Set.not_nonempty_iff_eq_empty]
  rintro ⟨x, hxfront, w, hwDE, hxw⟩
  have hwfront : w ∈ frontier Bu := by
    have h : MandelDim.piExp w ∈ frontier (MandelDim.piExp '' Bu) := by rw [hxw]; exact hxfront
    have h' : w ∈ MandelDim.piExp ⁻¹' frontier (MandelDim.piExp '' Bu) := h
    rwa [preimage_frontier_piExp, hpre] at h'
  have hwcl : w ∈ closure Bu := hwfront.1
  have hwBtil : w ∈ MandelDim.Btil d B := Btil_closed_in_DE d hBcl w hwDE
    (closure_mono hBu_sub hwcl)
  have hwmem : w ∈ Bu := hBu_cl w hwBtil hwcl
  have hwint : w ∈ interior Bu := by
    rw [hBu_open.interior_eq]
    exact hwmem
  exact hwfront.2 hwint

/-- **A point of the holomorphy domain `π '' d.DE` lying in the closure of the horn domain is
already in the horn domain.**  Combined with the characterization
`Work.Horn.isCompact_inter_preimage_iff_closure_subset`, this means that the confinement

    closure (B' ∩ g ⁻¹' L) ⊆ π '' d.DE

is *sufficient* for the properness of `g : B' → B'`. -/
theorem piExp_DE_inter_closure_subset {f₀ : ℂ → ℂ} {D₀ : Set ℂ}
    (d : MandelDim.ParabData f₀ D₀) {B Bu Bl : Set ℂ}
    (hB : IsOpen B)
    (hBcl : ∀ y ∈ MandelDim.ParabolicBasin f₀ D₀, y ∈ closure B → y ∈ B)
    (hBu_sub : Bu ⊆ MandelDim.Btil d B) (hBu_open : IsOpen Bu)
    (hBu_cl : ∀ y ∈ MandelDim.Btil d B, y ∈ closure Bu → y ∈ Bu)
    (hBuT : MandelDim.IsTInvariant Bu)
    (hBl_sub : Bl ⊆ MandelDim.Btil d B) (hBl_open : IsOpen Bl)
    (hBl_cl : ∀ y ∈ MandelDim.Btil d B, y ∈ closure Bl → y ∈ Bl)
    (hBlT : MandelDim.IsTInvariant Bl) :
    MandelDim.piExp '' d.DE ∩ closure (insert 0 (MandelDim.piExp '' (Bu ∪ Bl)))
      ⊆ insert 0 (MandelDim.piExp '' (Bu ∪ Bl)) := by
  have hdisjU := frontier_piExp_component_disjoint_piExp_DE d hB hBcl hBu_sub hBu_open hBu_cl hBuT
  have hdisjL := frontier_piExp_component_disjoint_piExp_DE d hB hBcl hBl_sub hBl_open hBl_cl hBlT
  intro x hx
  obtain ⟨hxDE, hxcl⟩ := hx
  have hcl : closure (insert 0 (MandelDim.piExp '' (Bu ∪ Bl)))
      = insert 0 (closure (MandelDim.piExp '' Bu) ∪ closure (MandelDim.piExp '' Bl)) := by
    simp only [Set.image_union, Set.insert_eq, closure_union, closure_singleton]
  rw [hcl, Set.mem_insert_iff, Set.mem_union] at hxcl
  rw [Set.mem_insert_iff, Set.image_union]
  rcases hxcl with h0 | hU | hL
  · exact Or.inl h0
  · have hxint : x ∈ interior (MandelDim.piExp '' Bu) := by
      by_contra h
      have hmem : x ∈ frontier (MandelDim.piExp '' Bu) ∩ MandelDim.piExp '' d.DE :=
        ⟨⟨hU, h⟩, hxDE⟩
      rw [hdisjU] at hmem
      exact hmem
    rw [((Work.Horn.piExp_isOpenMap _ hBu_open).interior_eq)] at hxint
    exact Or.inr (Or.inl hxint)
  · have hxint : x ∈ interior (MandelDim.piExp '' Bl) := by
      by_contra h
      have hmem : x ∈ frontier (MandelDim.piExp '' Bl) ∩ MandelDim.piExp '' d.DE :=
        ⟨⟨hL, h⟩, hxDE⟩
      rw [hdisjL] at hmem
      exact hmem
    rw [((Work.Horn.piExp_isOpenMap _ hBl_open).interior_eq)] at hxint
    exact Or.inr (Or.inr hxint)

end

end Work.Horn
