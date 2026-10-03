import Mathlib

namespace Work.Topology.Covering

/-- For `u ⊆ s`, the subtype `{x : ↥s // (x : X) ∈ u}` is homeomorphic to `↥u`, via the
identity on the underlying points. -/
def subtypePreimageHomeomorph {X : Type*} [TopologicalSpace X] {s : Set X} (u : Set X)
    (h : u ⊆ s) : ↥(Subtype.val ⁻¹' u : Set ↥s) ≃ₜ ↥u where
  toFun y := ⟨(y.1.1 : X), y.2⟩
  invFun x := ⟨⟨x.1, h x.2⟩, x.2⟩
  left_inv _ := Subtype.ext (Subtype.ext rfl)
  right_inv _ := Subtype.ext rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- For `u ⊆ s`, the fiber `(Subtype.val ⁻¹' u) ×ˢ univ` of `↥s × β` over `u` is homeomorphic
to `↥u × β`, preserving both coordinates. -/
def prodSetFiberHomeomorph {α : Type*} [TopologicalSpace α] {β : Type*} [TopologicalSpace β]
    {s : Set α} (u : Set α) (h : u ⊆ s) :
    ↥((Subtype.val ⁻¹' u : Set ↥s) ×ˢ (Set.univ : Set β)) ≃ₜ ↥u × β where
  toFun z := (⟨(z.1.1.1 : α), z.2.1⟩, (z.1.2 : β))
  invFun p := ⟨((⟨p.1.1, h p.1.2⟩ : ↥s), p.2), ⟨p.1.2, trivial⟩⟩
  left_inv _ := Subtype.ext (Prod.ext (Subtype.ext rfl) rfl)
  right_inv _ := Prod.ext (Subtype.ext rfl) rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- `prodSetFiberHomeomorph` preserves the base point. -/
lemma prodSetFiberHomeomorph_fst {α : Type*} [TopologicalSpace α] {β : Type*}
    [TopologicalSpace β] {s : Set α} (u : Set α) (h : u ⊆ s)
    (z : ↥((Subtype.val ⁻¹' u : Set ↥s) ×ˢ (Set.univ : Set β))) :
    ((prodSetFiberHomeomorph u h z).1 : α) = (z.1.1 : α) := rfl

/-- **Restricting a trivialization to a smaller base.** Let `f : X → Y`, let `U ⊆ Y` carry a
trivialization `H : f ⁻¹' U ≃ₜ ↥U × I` of `f` over `U` (compatibly with the projection,
`(H x).1 = f x`), and let `U' ⊆ U` be open.  Then `f ⁻¹' U'` is open in `X` (given `f ⁻¹' U`
open) and the trivialization restricts to `H' : f ⁻¹' U' ≃ₜ ↥U' × I` with `(H' x).1 = f x`. -/
theorem restrict_base_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} {I : Type*} [TopologicalSpace I] {U U' : Set Y} (hU'U : U' ⊆ U)
    (hU'open : IsOpen U') (hfUopen : IsOpen (f ⁻¹' U))
    (H : f ⁻¹' U ≃ₜ U × I) (hH : ∀ x : f ⁻¹' U, ((H x).1 : Y) = f x) :
    IsOpen (f ⁻¹' U') ∧ ∃ H' : f ⁻¹' U' ≃ₜ U' × I, ∀ x : f ⁻¹' U', ((H' x).1 : Y) = f x := by
  have hW'W : f ⁻¹' U' ⊆ f ⁻¹' U := fun _ hx => hU'U hx
  -- The part of the trivial product lying over `U'`.
  let s' : Set ↥U := Subtype.val ⁻¹' U'
  let t : Set (↥U × I) := s' ×ˢ (Set.univ : Set I)
  have ht_mem : ∀ y : ↥U × I, (y ∈ t) ↔ ((y.1 : ↥U) : Y) ∈ U' := by
    intro y; simp [t, s']
  have ht : IsOpen t := by
    have hcont : Continuous fun y : ↥U × I => ((y.1 : ↥U) : Y) :=
      continuous_subtype_val.comp continuous_fst
    have : t = (fun y : ↥U × I => ((y.1 : ↥U) : Y)) ⁻¹' U' := by ext y; exact ht_mem y
    rw [this]; exact hU'open.preimage hcont
  -- **Part 1**: `f ⁻¹' U'` is open, as `H ⁻¹' t` transported back along the open embedding
  -- `↥(f ⁻¹' U) → X`.
  have hOpen : IsOpen (f ⁻¹' U') := by
    have hpre : IsOpen (H ⁻¹' t) := H.isOpen_preimage.mpr ht
    rw [isOpen_induced_iff] at hpre
    obtain ⟨V, hV, hVeq⟩ := hpre
    have hkey : ∀ w : ↥(f ⁻¹' U), (w : X) ∈ V ↔ (w : X) ∈ f ⁻¹' U' := by
      intro w
      have h1 : ((w : X) ∈ V) ↔ (H w ∈ t) := Set.ext_iff.mp hVeq w
      rw [ht_mem] at h1
      refine h1.trans ?_
      change ((H w).1 : Y) ∈ U' ↔ f (w : X) ∈ U'
      rw [hH w]
    have hEq : f ⁻¹' U' = V ∩ f ⁻¹' U := by
      ext x
      constructor
      · intro hx
        exact ⟨(hkey ⟨x, hW'W hx⟩).mpr hx, hW'W hx⟩
      · rintro ⟨hxV, hxU⟩
        exact (hkey ⟨x, hxU⟩).mp hxV
    rw [hEq]
    exact hV.inter hfUopen
  refine ⟨hOpen, ?_⟩
  -- **Part 2**: restrict the homeomorphism `H` to the fiber over `U'`.
  have hsets : (Subtype.val ⁻¹' (f ⁻¹' U') : Set ↥(f ⁻¹' U)) = H ⁻¹' t := by
    ext w
    show f (w : X) ∈ U' ↔ H w ∈ t
    rw [ht_mem, hH w]
  -- Reshape the total space `↥(f ⁻¹' U')` into the fiber of `H` over `U'`.
  let ε : ↥(f ⁻¹' U') ≃ₜ ↥(Subtype.val ⁻¹' (f ⁻¹' U') : Set ↥(f ⁻¹' U)) :=
    (subtypePreimageHomeomorph (s := f ⁻¹' U) (f ⁻¹' U') hW'W).symm
  -- Restrict `H` to the fiber over `U'`.
  let e2 : ↥(Subtype.val ⁻¹' (f ⁻¹' U') : Set ↥(f ⁻¹' U)) ≃ₜ ↥t := Homeomorph.sets H hsets
  -- Reshape the fiber of the trivial product over `U'` into `↥U' × I`.
  let e3 : ↥t ≃ₜ ↥U' × I := prodSetFiberHomeomorph (s := U) U' hU'U
  refine ⟨ε.trans (e2.trans e3), ?_⟩
  intro x
  show ((e3 (e2 (ε x))).1 : Y) = f (x : X)
  -- Each stage preserves the base point, and `e2` is compatible with the projection by `hH`.
  have hA : ((e3 (e2 (ε x))).1 : Y) = (((e2 (ε x) : ↥t) : ↥U × I).1.1 : Y) :=
    prodSetFiberHomeomorph_fst U' hU'U (e2 (ε x))
  have hB : (((e2 (ε x) : ↥t) : ↥U × I).1.1 : Y) = f ((ε x).1.1) := by
    have h2 : (↑(e2 (ε x)) : ↥U × I) = H (ε x).1 := rfl
    rw [h2]
    exact hH ((ε x).1)
  have hC : ((ε x).1.1 : X) = (x : X) := rfl
  rw [hA, hB, hC]

end Work.Topology.Covering
