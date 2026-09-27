import Mathlib
import Submission.Work.Brown.Basic

/-!
# Collapsing the complement of an open Euclidean cell

This file constructs, for an open subset `U` of a locally compact Hausdorff space `X` that is
homeomorphic to `ℝⁿ`, a continuous surjection

`q : OnePoint X → 𝕊ⁿ`

which is injective on `U` and collapses the complement of `U` (inside the one-point
compactification `OnePoint X`) to a single point.  Concretely `q` is the composite of the
"collapse" map

`collapseMap e : OnePoint X → OnePoint (PL.E n)`

(where `e : ↥U ≃ₜ PL.E n` is the given homeomorphism) with the standard homeomorphism
`OnePoint (PL.E n) ≃ₜ 𝕊ⁿ` of `onePointEquivSphereOfFinrankEq`.

This is the combinatorial heart of the statement
`Work.Brown.Compactify.exists_collapseMap`.
-/

open Set Filter Metric
open scoped Topology

namespace Work.Brown.Compactify

/-- The collapse map: send `x ∈ U` to `e x ∈ PL.E n`, and everything else (including `∞`) to `∞`,
inside the one-point compactification.  Formally a map `OnePoint X → OnePoint (PL.E n)`. -/
noncomputable def collapseMap {X : Type*} [TopologicalSpace X] {n : ℕ} {U : Set X}
    (e : ↥U ≃ₜ PL.E n) : OnePoint X → OnePoint (PL.E n) := by
  classical
  exact fun z => OnePoint.elim z OnePoint.infty
    (fun x => if hx : x ∈ U then (e ⟨x, hx⟩ : OnePoint (PL.E n)) else OnePoint.infty)

@[simp] lemma collapseMap_infty {X : Type*} [TopologicalSpace X] {n : ℕ} {U : Set X}
    (e : ↥U ≃ₜ PL.E n) : collapseMap e OnePoint.infty = OnePoint.infty := rfl

lemma collapseMap_coe_of_mem {X : Type*} [TopologicalSpace X] {n : ℕ} {U : Set X}
    (e : ↥U ≃ₜ PL.E n) {x : X} (hx : x ∈ U) :
    collapseMap e (x : OnePoint X) = (e ⟨x, hx⟩ : OnePoint (PL.E n)) := by
  simp [collapseMap, hx]

lemma collapseMap_coe_of_notMem {X : Type*} [TopologicalSpace X] {n : ℕ} {U : Set X}
    (e : ↥U ≃ₜ PL.E n) {x : X} (hx : x ∉ U) :
    collapseMap e (x : OnePoint X) = OnePoint.infty := by
  simp [collapseMap, hx]

/-- Auxiliary: for `s ⊆ PL.E n` closed and compact, the set of points of `X` whose collapse lies in
the image of `s` is the image of a compact (hence closed) subset of `X`. -/
private lemma compact_preimage_aux {X : Type*} [TopologicalSpace X] {n : ℕ} {U : Set X}
    (e : ↥U ≃ₜ PL.E n) {s : Set (PL.E n)} (hs : IsCompact s) :
    IsCompact (Subtype.val '' (e ⁻¹' s)) :=
  ((e.isCompact_preimage).2 hs).image continuous_subtype_val

/-- The collapse map is continuous as a map on `X` (i.e. before passing to the compactification). -/
lemma continuous_collapseMap_restrict {X : Type*} [TopologicalSpace X] [T2Space X] {n : ℕ}
    {U : Set X} (e : ↥U ≃ₜ PL.E n) (hU : IsOpen U) :
    Continuous (fun x : X => collapseMap e (x : OnePoint X)) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x ∈ U
  · have h1 : ContinuousAt (fun y : ↥U => collapseMap e ((y : X) : OnePoint X)) ⟨x, hx⟩ := by
      rw [show (fun y : ↥U => collapseMap e ((y : X) : OnePoint X))
            = fun y : ↥U => (e y : OnePoint (PL.E n)) from by
          funext y; exact collapseMap_coe_of_mem e y.2]
      fun_prop
    exact ((hU.isOpenEmbedding_subtypeVal).continuousAt_iff
      (g := fun x : X => collapseMap e (x : OnePoint X)) (x := (⟨x, hx⟩ : ↥U))).1 h1
  · rw [ContinuousAt]
    have hval : collapseMap e (x : OnePoint X) = OnePoint.infty := collapseMap_coe_of_notMem e hx
    rw [hval]
    rw [OnePoint.hasBasis_nhds_infty.tendsto_right_iff]
    intro s hs
    obtain ⟨hs_closed, hs_compact⟩ := hs
    have hC : IsCompact (Subtype.val '' (e ⁻¹' s)) := compact_preimage_aux e hs_compact
    have hCcl : IsClosed (Subtype.val '' (e ⁻¹' s)) := hC.isClosed
    have hxmem : x ∉ Subtype.val '' (e ⁻¹' s) := by
      rintro ⟨y, hy, hyx⟩
      exact hx (hyx ▸ y.2)
    have hmem : (Subtype.val '' (e ⁻¹' s))ᶜ ∈ 𝓝 x := hCcl.compl_mem_nhds hxmem
    refine mem_of_superset hmem ?_
    intro y hy
    change collapseMap e (y : OnePoint X) ∈ OnePoint.some '' sᶜ ∪ {OnePoint.infty}
    rw [Set.mem_compl_iff, Set.mem_image] at hy
    by_cases hyU : y ∈ U
    · rw [collapseMap_coe_of_mem e hyU]
      rw [Set.mem_union]; left; rw [Set.mem_image]
      refine ⟨e ⟨y, hyU⟩, ?_, rfl⟩
      rw [Set.mem_compl_iff]
      intro hmem2
      exact hy ⟨⟨y, hyU⟩, hmem2, rfl⟩
    · rw [collapseMap_coe_of_notMem e hyU]
      exact Set.mem_union_right _ (Set.mem_singleton _)

/-- The collapse map tends to `∞` along the cocompact-(closed) filter; this is the "continuity at
infinity" statement needed to extend it to `OnePoint X`. -/
lemma tendsto_collapseMap_coclosedCompact {X : Type*} [TopologicalSpace X] [T2Space X] {n : ℕ}
    {U : Set X} (e : ↥U ≃ₜ PL.E n) :
    Tendsto (fun x : X => collapseMap e (x : OnePoint X)) (Filter.coclosedCompact X)
      (𝓝 (OnePoint.infty : OnePoint (PL.E n))) := by
  rw [OnePoint.hasBasis_nhds_infty.tendsto_right_iff]
  intro s hs
  obtain ⟨hs_closed, hs_compact⟩ := hs
  have hC : IsCompact (Subtype.val '' (e ⁻¹' s)) := compact_preimage_aux e hs_compact
  have hCcl : IsClosed (Subtype.val '' (e ⁻¹' s)) := hC.isClosed
  refine mem_of_superset (hC.compl_mem_coclosedCompact_of_isClosed hCcl) ?_
  intro y hy
  change collapseMap e (y : OnePoint X) ∈ OnePoint.some '' sᶜ ∪ {OnePoint.infty}
  rw [Set.mem_compl_iff, Set.mem_image] at hy
  by_cases hyU : y ∈ U
  · rw [collapseMap_coe_of_mem e hyU]
    rw [Set.mem_union]; left; rw [Set.mem_image]
    refine ⟨e ⟨y, hyU⟩, ?_, rfl⟩
    rw [Set.mem_compl_iff]
    intro hmem2
    exact hy ⟨⟨y, hyU⟩, hmem2, rfl⟩
  · rw [collapseMap_coe_of_notMem e hyU]
    exact Set.mem_union_right _ (Set.mem_singleton _)

/-- The collapse map `OnePoint X → OnePoint (PL.E n)` is continuous. -/
lemma continuous_collapseMap {X : Type*} [TopologicalSpace X] [T2Space X] {n : ℕ} {U : Set X}
    (e : ↥U ≃ₜ PL.E n) (hU : IsOpen U) : Continuous (collapseMap e) := by
  rw [OnePoint.continuous_iff]
  exact ⟨tendsto_collapseMap_coclosedCompact e, continuous_collapseMap_restrict e hU⟩

/-- The fibres of the collapse map: it is injective off the complement of `U`, and collapses that
complement to the single point `∞`. -/
lemma collapseMap_eq_iff {X : Type*} [TopologicalSpace X] {n : ℕ} {U : Set X}
    (e : ↥U ≃ₜ PL.E n) (x y : OnePoint X) :
    collapseMap e x = collapseMap e y ↔
      x = y ∨ (x ∈ (OnePoint.some '' U : Set (OnePoint X))ᶜ ∧
               y ∈ (OnePoint.some '' U : Set (OnePoint X))ᶜ) := by
  induction x using OnePoint.rec with
  | infty =>
    induction y using OnePoint.rec with
    | infty => simp
    | coe b =>
      by_cases hb : b ∈ U
      · rw [collapseMap_coe_of_mem e hb]
        simp [hb]
      · rw [collapseMap_coe_of_notMem e hb]
        simp [Set.mem_compl_iff, Set.mem_image, hb]
  | coe a =>
    induction y using OnePoint.rec with
    | infty =>
      by_cases ha : a ∈ U
      · rw [collapseMap_coe_of_mem e ha]
        simp [ha]
      · rw [collapseMap_coe_of_notMem e ha]
        simp [Set.mem_compl_iff, Set.mem_image, ha]
    | coe b =>
      by_cases ha : a ∈ U <;> by_cases hb : b ∈ U
      · rw [collapseMap_coe_of_mem e ha, collapseMap_coe_of_mem e hb]
        simp [Set.mem_compl_iff, Set.mem_image, ha, hb]
      · rw [collapseMap_coe_of_mem e ha, collapseMap_coe_of_notMem e hb]
        have hab : ¬ a = b := fun h => hb (h ▸ ha)
        simp [Set.mem_compl_iff, Set.mem_image, ha, hb, hab]
      · rw [collapseMap_coe_of_notMem e ha, collapseMap_coe_of_mem e hb]
        have hab : ¬ a = b := fun h => ha (h ▸ hb)
        simp [Set.mem_compl_iff, Set.mem_image, ha, hb, hab]
      · rw [collapseMap_coe_of_notMem e ha, collapseMap_coe_of_notMem e hb]
        simp [Set.mem_compl_iff, Set.mem_image, ha, hb]

/-- The collapse map is surjective. -/
lemma collapseMap_surjective {X : Type*} [TopologicalSpace X] {n : ℕ} {U : Set X}
    (e : ↥U ≃ₜ PL.E n) : Function.Surjective (collapseMap e) := by
  intro v
  induction v using OnePoint.rec with
  | infty => exact ⟨OnePoint.infty, collapseMap_infty e⟩
  | coe w => exact ⟨(e.symm w : ↥U), by rw [collapseMap_coe_of_mem e (e.symm w).2]; simp⟩

/-- For an open subset `U` of a locally compact Hausdorff space that is homeomorphic to `ℝⁿ`,
there is a continuous surjection from the one-point compactification of `X` onto the sphere `𝕊ⁿ`
which is injective on `U` and identifies exactly the points outside `U`. -/
theorem exists_collapseMap {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
    {n : ℕ} {U : Set X} (hU : IsOpen U) (hc : Nonempty (↥U ≃ₜ PL.E n)) :
    ∃ q : OnePoint X → ↥(Metric.sphere (0 : PL.E (n + 1)) 1), Continuous q ∧ Function.Surjective q ∧
      ∀ x y, q x = q y ↔ x = y ∨
        (x ∈ ((↑) '' U : Set (OnePoint X))ᶜ ∧ y ∈ ((↑) '' U : Set (OnePoint X))ᶜ) := by
  obtain ⟨e⟩ := hc
  have hφ : OnePoint (PL.E n) ≃ₜ ↥(Metric.sphere (0 : PL.E (n + 1)) 1) :=
    onePointEquivSphereOfFinrankEq (V := PL.E n) (ι := Fin (n + 1)) (by simp)
  refine ⟨fun z => hφ (collapseMap e z), hφ.continuous.comp (continuous_collapseMap e hU), ?_, ?_⟩
  · intro w
    obtain ⟨v, hv⟩ := hφ.surjective w
    obtain ⟨z, hz⟩ := collapseMap_surjective e v
    exact ⟨z, by show hφ (collapseMap e z) = w; rw [hz, hv]⟩
  · intro x y
    rw [hφ.injective.eq_iff]
    exact collapseMap_eq_iff e x y

end Work.Brown.Compactify
