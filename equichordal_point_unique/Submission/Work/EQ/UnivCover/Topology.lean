import Submission.Work.EQ.UnivCover.Defs
import Submission.Work.EQ.UnivCover.Sheet

/-!
# The topology of the universal cover

Over a space whose disc-like sets form a neighbourhood basis, the sheets are a topological basis of
the universal cover; the projection is continuous and the cover is Hausdorff.
-/

set_option autoImplicit false
open _root_.Topology
open scoped Topology
open Work.EQ.UnivCover

namespace Work.EQ.UnivCover

variable {X : Type*} [TopologicalSpace X] {x₀ : X}

/-- Absorbing a smaller sheet into a bigger one: if `e` lies in the sheet of `e₁` over `V` and `e'`
lies in the sheet of `e` over `W ⊆ V`, then `e'` lies in the sheet of `e₁` over `V`. -/
theorem UC_sheet_trans {V W : Set X} {e e₁ e' : UC x₀} (he : e ∈ UC.sheet e₁ V)
    (he' : e' ∈ UC.sheet e W) (hWV : W ⊆ V) : e' ∈ UC.sheet e₁ V := by
  obtain ⟨heV, δ₁, hδ₁, hc₁⟩ := he
  obtain ⟨he'W, δ, hδ, hc⟩ := he'
  refine ⟨hWV he'W, δ₁.trans δ, ?_, ?_⟩
  · intro t
    have ht : (δ₁.trans δ) t ∈ Set.range (δ₁.trans δ) := ⟨t, rfl⟩
    rw [Path.trans_range, Set.mem_union] at ht
    rcases ht with ⟨s, hs⟩ | ⟨s, hs⟩
    · rw [← hs]; exact hδ₁ s
    · rw [← hs]; exact hWV (hδ s)
  · rw [hc, hc₁]
    simp only [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.trans_assoc]

/-- The sheets form a topological basis of the universal cover. -/
theorem UC_isTopologicalBasis_basis (hB : HasDiscBasis X) :
    TopologicalSpace.IsTopologicalBasis (UC.basis x₀) := by
  refine ⟨?_, ?_, rfl⟩
  · rintro S₁ ⟨e₁, V₁, hV₁, heV₁, rfl⟩ S₂ ⟨e₂, V₂, hV₂, heV₂, rfl⟩ e ⟨h₁, h₂⟩
    obtain ⟨W, hW, heW, hWV⟩ := hB e.pt (V₁ ∩ V₂) (hV₁.isOpen.inter hV₂.isOpen)
      (Set.mem_inter h₁.1 h₂.1)
    exact ⟨UC.sheet e W, ⟨e, W, hW, heW, rfl⟩, UC.self_mem_sheet heW,
      fun _ he' => ⟨UC_sheet_trans h₁ he' fun x hx => (hWV hx).1,
        UC_sheet_trans h₂ he' fun x hx => (hWV hx).2⟩⟩
  · rw [Set.sUnion_eq_univ_iff]
    intro e
    obtain ⟨V, hV, heV, -⟩ := hB e.pt Set.univ isOpen_univ (Set.mem_univ e.pt)
    exact ⟨UC.sheet e V, ⟨e, V, hV, heV, rfl⟩, UC.self_mem_sheet heV⟩

/-- A sheet is open in the universal cover. -/
theorem UC_isOpen_sheet (hB : HasDiscBasis X) {e : UC x₀} {V : Set X} (hV : IsDiscLike V)
    (heV : e.pt ∈ V) : IsOpen (UC.sheet e V) :=
  (UC_isTopologicalBasis_basis hB).isOpen ⟨e, V, hV, heV, rfl⟩

/-- The projection of the universal cover is continuous. -/
theorem UC_continuous_proj (hB : HasDiscBasis X) : Continuous (UC.proj (x₀ := x₀)) := by
  have hb := UC_isTopologicalBasis_basis (x₀ := x₀) hB
  rw [continuous_def]
  intro U hU
  have hcover : UC.proj ⁻¹' U = ⋃₀ {S ∈ UC.basis x₀ | S ⊆ UC.proj ⁻¹' U} := by
    refine Set.Subset.antisymm (fun e he => ?_) (Set.sUnion_subset fun S hS => hS.2)
    obtain ⟨V, hV, heV, hVU⟩ := hB e.pt U hU he
    exact ⟨UC.sheet e V, ⟨⟨e, V, hV, heV, rfl⟩,
      fun e' he' => hVU he'.1⟩, UC.self_mem_sheet heV⟩
  rw [hcover]
  exact isOpen_sUnion fun S hS => hb.isOpen hS.1

/-- The universal cover of a Hausdorff space is Hausdorff. -/
theorem UC_t2Space [T2Space X] (hB : HasDiscBasis X) : T2Space (UC x₀) := by
  have hb := UC_isTopologicalBasis_basis (x₀ := x₀) hB
  refine ⟨fun e₁ e₂ hne => ?_⟩
  by_cases hpt : e₁.pt = e₂.pt
  · obtain ⟨V, hV, heV, -⟩ := hB e₁.pt Set.univ isOpen_univ (Set.mem_univ e₁.pt)
    have he₂V : e₂.pt ∈ V := hpt ▸ heV
    refine ⟨UC.sheet e₁ V, UC.sheet e₂ V, hb.isOpen ⟨e₁, V, hV, heV, rfl⟩,
      hb.isOpen ⟨e₂, V, hV, he₂V, rfl⟩, UC.self_mem_sheet heV, UC.self_mem_sheet he₂V, ?_⟩
    refine Set.disjoint_left.mpr fun e' he'₁ he'₂ => hne ?_
    exact (UC_sheet_unique hV).2 he'₁ he'₂ hpt
  · obtain ⟨U₁, U₂, hU₁, hU₂, he₁, he₂, hdisj⟩ := t2_separation hpt
    obtain ⟨V₁, hV₁, heV₁, hV₁U₁⟩ := hB e₁.pt U₁ hU₁ he₁
    obtain ⟨V₂, hV₂, heV₂, hV₂U₂⟩ := hB e₂.pt U₂ hU₂ he₂
    refine ⟨UC.sheet e₁ V₁, UC.sheet e₂ V₂, hb.isOpen ⟨e₁, V₁, hV₁, heV₁, rfl⟩,
      hb.isOpen ⟨e₂, V₂, hV₂, heV₂, rfl⟩, UC.self_mem_sheet heV₁, UC.self_mem_sheet heV₂, ?_⟩
    exact Set.disjoint_left.mpr fun e' he'₁ he'₂ =>
      Set.disjoint_left.mp hdisj (hV₁U₁ he'₁.1) (hV₂U₂ he'₂.1)

/-- The family of sheets is a basis and the cover is Hausdorff. -/
theorem UC_basis_and_t2Space [T2Space X] (hB : HasDiscBasis X) :
    TopologicalSpace.IsTopologicalBasis (UC.basis x₀) ∧ T2Space (UC x₀) :=
  ⟨UC_isTopologicalBasis_basis hB, UC_t2Space hB⟩

end Work.EQ.UnivCover
