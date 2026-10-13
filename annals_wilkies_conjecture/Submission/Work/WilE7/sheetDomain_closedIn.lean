import Mathlib
import Submission.Work.Wilkies.E.Spec

set_option autoImplicit false

namespace Work.WilE7

open WilkiesDesign.E

/-! ## A tool about preconnected sets

If `s` is preconnected and `a` lies in its closure, then `insert a s` is still preconnected.
Mathlib has no such lemma (`IsPreconnected.insert` / `isPreconnected_insert` are absent), so we
prove it here; it is the step that lets us recognise points of `closure Z` as elements of `Z`
once we know that they lie in the same set `A` as `Z`. -/
theorem preconnected_insert_of_mem_closure {α : Type*} [TopologicalSpace α] {s : Set α} {a : α}
    (hs : IsPreconnected s) (ha : a ∈ closure s) : IsPreconnected (insert a s) := by
  rw [isPreconnected_iff_subset_of_disjoint] at hs ⊢
  intro u v hu hv huv hdisj
  have hsu : s ⊆ u ∪ v := fun x hx => huv (Set.mem_insert_of_mem a hx)
  have hsd : s ∩ (u ∩ v) = ∅ := by
    rw [← Set.subset_empty_iff]
    rintro x ⟨hxs, hxu, hxv⟩
    rw [← hdisj]
    exact ⟨Set.mem_insert_of_mem a hxs, hxu, hxv⟩
  rcases hs u v hu hv hsu hsd with h1 | h1
  · -- `s ⊆ u`: then `insert a s ⊆ u` unless `a ∈ v`, which the disjointness forbids
    rcases (huv (Set.mem_insert a s) : a ∈ u ∨ a ∈ v) with hau | hav
    · exact Or.inl (Set.insert_subset_iff.mpr ⟨hau, h1⟩)
    · exfalso
      obtain ⟨w, hwv, hws⟩ := mem_closure_iff.mp ha v hv hav
      have hmem : w ∈ insert a s ∩ (u ∩ v) := ⟨Set.mem_insert_of_mem a hws, h1 hws, hwv⟩
      rw [hdisj] at hmem
      exact hmem
  · -- `s ⊆ v`, the symmetric case
    rcases (huv (Set.mem_insert a s) : a ∈ u ∨ a ∈ v) with hau | hav
    · exfalso
      obtain ⟨w, hwu, hws⟩ := mem_closure_iff.mp ha u hu hau
      have hmem : w ∈ insert a s ∩ (u ∩ v) := ⟨Set.mem_insert_of_mem a hws, hwu, h1 hws⟩
      rw [hdisj] at hmem
      exact hmem
    · exact Or.inr (Set.insert_subset_iff.mpr ⟨hav, h1⟩)

/-- The projection of a connected component of the sheet domain (cut by the chamber `C`) is
closed inside `C`, provided the frontier of `S.X.set` projects into `Forbidden`.

Proof. Let `A = S.X.set ∩ π⁻¹'C`, let `Z` be the component of `z₀` in `A` and `Y = π '' Z`. Every
EA semi-Pfaffian set sits in the cube `cubeC (p+q)`, which is compact; hence `closure Z` is
compact, `π '' closure Z` is closed, and `closure Y ⊆ π '' closure Z`. Take `x ∈ closure Y ∩ C`
and `z ∈ closure Z` with `π z = x`. If `z ∉ S.X.set`, then `z` lies in the frontier of `S.X.set`,
so `z ∈ Forbidden` and `π z = x ∉ C`, a contradiction; hence `z ∈ A`. Since `z` lies in the
closure of the preconnected set `Z`, the set `insert z Z` is preconnected, it is contained in `A`
and it contains `z₀`, so it lies in the connected component `Z` of `z₀`; thus `z ∈ Z` and
`x = π z ∈ Y`. -/
theorem sheetDomain_closedIn
    {p q : ℕ} (S : WilkiesDesign.E.Stratum p q)
    (C : Set (Fin p → ℝ)) (Forbidden : Set (Fin (p + q) → ℝ))
    (hForb : ∀ w ∈ Forbidden, WilkiesDesign.E.projFirst p q w ∉ C)
    (hFr : closure S.X.set \ S.X.set ⊆ Forbidden)
    (z₀ : Fin (p + q) → ℝ)
    (hz₀ : z₀ ∈ S.X.set) (hz₀C : WilkiesDesign.E.projFirst p q z₀ ∈ C) :
    closure (Set.image (WilkiesDesign.E.projFirst p q)
        (connectedComponentIn (S.X.set ∩ {w : Fin (p + q) → ℝ |
          WilkiesDesign.E.projFirst p q w ∈ C}) z₀)) ∩ C ⊆
      Set.image (WilkiesDesign.E.projFirst p q)
        (connectedComponentIn (S.X.set ∩ {w : Fin (p + q) → ℝ |
          WilkiesDesign.E.projFirst p q w ∈ C}) z₀) := by
  -- abbreviations: the sheet domain `A` and the component `Z` of `z₀` in it
  set A : Set (Fin (p + q) → ℝ) :=
    S.X.set ∩ {w : Fin (p + q) → ℝ | WilkiesDesign.E.projFirst p q w ∈ C} with hA
  set Z : Set (Fin (p + q) → ℝ) := connectedComponentIn A z₀ with hZ
  intro x hx
  rw [Set.mem_inter_iff] at hx
  obtain ⟨hxcl, hxC⟩ := hx
  have hπ : Continuous (WilkiesDesign.E.projFirst p q) :=
    continuous_pi (fun i => continuous_apply (Fin.castAdd q i))
  -- `Z ⊆ A`
  have hZsubA : Z ⊆ A := by
    intro w hw
    rw [hZ] at hw
    exact connectedComponentIn_subset A z₀ hw
  -- `Z ⊆ S.X.set`
  have hZsubS : Z ⊆ S.X.set := by
    intro w hw
    have h := hZsubA hw
    rw [hA] at h
    exact h.1
  -- every EA set lies in the cube
  have hZsubCube : Z ⊆ WilkiesDesign.E.cubeC (p + q) := by
    intro w hw
    exact (show w ∈ WilkiesDesign.E.cubeC (p + q) ∧ _ from hZsubS hw).1
  -- the cube is compact
  have hcube : IsCompact (WilkiesDesign.E.cubeC (p + q)) := by
    have hEq : Set.univ.pi (fun _ : Fin (p + q) => Set.Icc (-1 : ℝ) 1)
        = WilkiesDesign.E.cubeC (p + q) := by
      ext x
      simp only [WilkiesDesign.E.cubeC, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]
      exact ⟨fun h i => abs_le.mpr (h i), fun h i => abs_le.mp (h i)⟩
    rw [← hEq]
    exact isCompact_univ_pi (fun _ => isCompact_Icc)
  have hclZ : IsCompact (closure Z) :=
    hcube.of_isClosed_subset isClosed_closure (closure_minimal hZsubCube hcube.isClosed)
  have himgcl : IsClosed (Set.image (WilkiesDesign.E.projFirst p q) (closure Z)) :=
    (hclZ.image hπ).isClosed
  -- continuity of `π` plus compactness of `closure Z`: `closure Y ⊆ π '' closure Z`
  have hmain : closure (Set.image (WilkiesDesign.E.projFirst p q) Z)
      ⊆ Set.image (WilkiesDesign.E.projFirst p q) (closure Z) :=
    closure_minimal (Set.image_mono subset_closure) himgcl
  have hxz : x ∈ Set.image (WilkiesDesign.E.projFirst p q) (closure Z) := hmain hxcl
  rw [Set.mem_image] at hxz
  obtain ⟨z, hzcl, hzπ⟩ := hxz
  have hzC : WilkiesDesign.E.projFirst p q z ∈ C := by rw [hzπ]; exact hxC
  -- `z` cannot be a frontier point of `S.X.set`
  have hzS : z ∈ S.X.set := by
    by_contra hnot
    have hzfr : z ∈ closure S.X.set \ S.X.set := ⟨closure_mono hZsubS hzcl, hnot⟩
    exact hForb z (hFr hzfr) hzC
  have hzA : z ∈ A := by
    rw [hA]
    exact ⟨hzS, hzC⟩
  -- `z` lies in the same component as `z₀`
  have hz0A : z₀ ∈ A := by
    rw [hA]
    exact ⟨hz₀, hz₀C⟩
  have hz0Z : z₀ ∈ Z := by
    rw [hZ]; exact mem_connectedComponentIn hz0A
  have hpre : IsPreconnected Z := by rw [hZ]; exact isPreconnected_connectedComponentIn
  have hins : IsPreconnected (insert z Z) := preconnected_insert_of_mem_closure hpre hzcl
  have hsub : insert z Z ⊆ A := Set.insert_subset_iff.mpr ⟨hzA, hZsubA⟩
  have hcomp : insert z Z ⊆ connectedComponentIn A z₀ :=
    hins.subset_connectedComponentIn (Set.mem_insert_of_mem z hz0Z) hsub
  rw [← hZ] at hcomp
  exact ⟨z, hcomp (Set.mem_insert z Z), hzπ⟩

end Work.WilE7
