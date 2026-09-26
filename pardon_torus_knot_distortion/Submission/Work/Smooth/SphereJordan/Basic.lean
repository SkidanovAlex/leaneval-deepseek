import Submission.Work.Smooth.SphereJordan.Defs

/-!
# The elementary API of `TwoDiscs` and `FamilyData`, and their transport along homeomorphisms

This file proves the elementary consequences of the two-disc decomposition of a simple closed curve
of the Riemann sphere (`TwoDiscs`) which the nesting argument consumes, and shows that the whole
datum — for one curve (`TwoDiscs`) and for a finite family (`FamilyData`) — is transported along any
homeomorphism of `ℂ ∪ {∞}`.

The transport is what lets the planar theorem, which is only available for curves that avoid `∞`, be
applied to an arbitrary curve: move the curve by a Möbius transformation so that it misses `∞`, apply
`Work.Smooth.SphereJordan.planeTwoDiscs`, and move back
(`Work.Smooth.SphereJordan.twoDiscs_of_pointOff`).
-/

open Set
open LeanEval.KnotTheory.PardonDistortion

namespace Work.Smooth.SphereJordan

noncomputable section

namespace TwoDiscs

variable {c : ℝ → RiemannSphere}

/-- The open side bounded by the first disc. -/
def openSide (h : TwoDiscs c) : Set RiemannSphere :=
  {x : RiemannSphere | ∃ z : Disc, ‖(z : ℂ)‖ < 1 ∧ h.e z = x}

/-- The open side bounded by the second disc. -/
def openSide' (h : TwoDiscs c) : Set RiemannSphere :=
  {x : RiemannSphere | ∃ z : Disc, ‖(z : ℂ)‖ < 1 ∧ h.e' z = x}

@[simp] theorem mem_openSide (h : TwoDiscs c) {x : RiemannSphere} :
    x ∈ h.openSide ↔ ∃ z : Disc, ‖(z : ℂ)‖ < 1 ∧ h.e z = x := Iff.rfl

@[simp] theorem mem_openSide' (h : TwoDiscs c) {x : RiemannSphere} :
    x ∈ h.openSide' ↔ ∃ z : Disc, ‖(z : ℂ)‖ < 1 ∧ h.e' z = x := Iff.rfl

theorem isOpen_openSide (h : TwoDiscs c) : IsOpen h.openSide := h.open_interior

theorem isOpen_openSide' (h : TwoDiscs c) : IsOpen h.openSide' := h.open_interior'

/-- A point of the closed disc of the curve which lies on the curve is the image of a boundary
point of the model disc. -/
theorem norm_eq_one_of_mem_range_left (h : TwoDiscs c) {z : Disc} {θ : ℝ}
    (hθ : h.e z = c θ) : ‖(z : ℂ)‖ = 1 := by
  have h1 : z = circlePoint θ := h.inj (by rw [hθ, h.boundary θ])
  rw [h1, Work.Smooth.Jordan.circlePoint_coe, Complex.norm_exp_ofReal_mul_I]

theorem norm_eq_one_of_mem_range_right (h : TwoDiscs c) {z : Disc} {θ : ℝ}
    (hθ : h.e' z = c θ) : ‖(z : ℂ)‖ = 1 := by
  have h1 : z = circlePoint θ := h.inj' (by rw [hθ, h.boundary' θ])
  rw [h1, Work.Smooth.Jordan.circlePoint_coe, Complex.norm_exp_ofReal_mul_I]

/-- A point of the open side of a disc is not on the curve. -/
theorem not_mem_range_of_mem_openSide (h : TwoDiscs c) {x : RiemannSphere}
    (hx : x ∈ h.openSide) : x ∉ Set.range c := by
  obtain ⟨z, hz, rfl⟩ := hx
  rintro ⟨θ, hθ⟩
  have h1 := h.norm_eq_one_of_mem_range_left hθ.symm
  rw [h1] at hz
  exact absurd hz (lt_irrefl 1)

theorem not_mem_range_of_mem_openSide' (h : TwoDiscs c) {x : RiemannSphere}
    (hx : x ∈ h.openSide') : x ∉ Set.range c := by
  obtain ⟨z, hz, rfl⟩ := hx
  rintro ⟨θ, hθ⟩
  have h1 := h.norm_eq_one_of_mem_range_right hθ.symm
  rw [h1] at hz
  exact absurd hz (lt_irrefl 1)

/-- The image of the closed model disc is the open side together with the curve. -/
theorem range_eq_openSide_union (h : TwoDiscs c) :
    Set.range h.e = h.openSide ∪ Set.range c := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    by_cases hz : ‖(z : ℂ)‖ < 1
    · exact Or.inl ⟨z, hz, rfl⟩
    · refine Or.inr ?_
      have hz1 : ‖(z : ℂ)‖ = 1 := le_antisymm (by
        have h : dist (z : ℂ) 0 ≤ 1 := z.2
        rwa [dist_eq_norm, sub_zero] at h) (not_lt.mp hz)
      obtain ⟨θ, hθ⟩ := Work.Smooth.Jordan.exists_circlePoint_eq z hz1
      exact ⟨θ, by rw [← hθ, h.boundary θ]⟩
  · rintro (⟨z, hz, rfl⟩ | ⟨θ, hθ⟩)
    · exact ⟨z, rfl⟩
    · exact ⟨circlePoint θ, by rw [h.boundary θ, hθ]⟩

theorem range_eq_openSide'_union (h : TwoDiscs c) :
    Set.range h.e' = h.openSide' ∪ Set.range c := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    by_cases hz : ‖(z : ℂ)‖ < 1
    · exact Or.inl ⟨z, hz, rfl⟩
    · refine Or.inr ?_
      have hz1 : ‖(z : ℂ)‖ = 1 := le_antisymm (by
        have h : dist (z : ℂ) 0 ≤ 1 := z.2
        rwa [dist_eq_norm, sub_zero] at h) (not_lt.mp hz)
      obtain ⟨θ, hθ⟩ := Work.Smooth.Jordan.exists_circlePoint_eq z hz1
      exact ⟨θ, by rw [← hθ, h.boundary' θ]⟩
  · rintro (⟨z, hz, rfl⟩ | ⟨θ, hθ⟩)
    · exact ⟨z, rfl⟩
    · exact ⟨circlePoint θ, by rw [h.boundary' θ, hθ]⟩

/-- The closed disc, minus its boundary, is the open side. -/
theorem range_sdiff_range_eq_openSide (h : TwoDiscs c) :
    Set.range h.e \ Set.range c = h.openSide := by
  rw [h.range_eq_openSide_union]
  ext x
  constructor
  · rintro ⟨hx | hx, hx'⟩
    · exact hx
    · exact absurd hx hx'
  · intro hx
    exact ⟨Or.inl hx, h.not_mem_range_of_mem_openSide hx⟩

theorem range_sdiff_range_eq_openSide' (h : TwoDiscs c) :
    Set.range h.e' \ Set.range c = h.openSide' := by
  rw [h.range_eq_openSide'_union]
  ext x
  constructor
  · rintro ⟨hx | hx, hx'⟩
    · exact hx
    · exact absurd hx hx'
  · intro hx
    exact ⟨Or.inl hx, h.not_mem_range_of_mem_openSide' hx⟩

/-- The sphere is the disjoint union of the two open sides and the curve. -/
theorem openSide_union_range_union_openSide' (h : TwoDiscs c) :
    h.openSide ∪ Set.range c ∪ h.openSide' = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  have hcover : x ∈ Set.range h.e ∨ x ∈ Set.range h.e' := by
    have h1 : x ∈ Set.range h.e ∪ Set.range h.e' := by rw [h.cover]; exact Set.mem_univ x
    exact h1
  rcases hcover with hx | hx
  · rw [h.range_eq_openSide_union] at hx
    rcases hx with hx | hx
    · exact Or.inl (Or.inl hx)
    · exact Or.inl (Or.inr hx)
  · rw [h.range_eq_openSide'_union] at hx
    rcases hx with hx | hx
    · exact Or.inr hx
    · exact Or.inl (Or.inr hx)

/-- The two open sides are disjoint. -/
theorem disjoint_openSide_openSide' (h : TwoDiscs c) :
    Disjoint h.openSide h.openSide' := by
  rw [Set.disjoint_left]
  intro x hx hx'
  have h1 : x ∈ Set.range c := by
    have h2 : x ∈ Set.range h.e ∩ Set.range h.e' :=
      ⟨⟨hx.choose, hx.choose_spec.2⟩, ⟨hx'.choose, hx'.choose_spec.2⟩⟩
    rwa [h.meet] at h2
  exact h.not_mem_range_of_mem_openSide hx h1

/-- The trace of the curve lies in the first disc. -/
theorem range_subset_left (h : TwoDiscs c) : Set.range c ⊆ Set.range h.e := by
  rintro _ ⟨θ, rfl⟩
  exact ⟨circlePoint θ, h.boundary θ⟩

/-- The trace of the curve lies in the second disc. -/
theorem range_subset_right (h : TwoDiscs c) : Set.range c ⊆ Set.range h.e' := by
  rintro _ ⟨θ, rfl⟩
  exact ⟨circlePoint θ, h.boundary' θ⟩

/-- **A two-disc datum is transported along a homeomorphism** of the Riemann sphere. -/
def mapHomeomorph (Φ : RiemannSphere ≃ₜ RiemannSphere) (h : TwoDiscs c) :
    TwoDiscs (fun t => Φ (c t)) where
  simple := ⟨Φ.continuous.comp h.simple.1,
    fun t => by show Φ (c (t + 2 * Real.pi)) = Φ (c t); rw [h.simple.2.1 t],
    fun a ha b hb hab => h.simple.2.2 ha hb (Φ.injective hab)⟩
  e := ⟨fun z => Φ (h.e z), Φ.continuous.comp h.e.continuous⟩
  e' := ⟨fun z => Φ (h.e' z), Φ.continuous.comp h.e'.continuous⟩
  inj := fun a b hab => h.inj (Φ.injective hab)
  inj' := fun a b hab => h.inj' (Φ.injective hab)
  boundary := fun θ => by simp [h.boundary θ]
  boundary' := fun θ => by simp [h.boundary' θ]
  open_interior := by
    have h1 : {x : RiemannSphere |
        ∃ z : Disc, ‖(z : ℂ)‖ < 1 ∧ (⟨fun z => Φ (h.e z),
          Φ.continuous.comp h.e.continuous⟩ : C(Disc, RiemannSphere)) z = x} =
        Φ '' h.openSide := by
      ext x
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨h.e z, ⟨z, hz, rfl⟩, rfl⟩
      · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
        exact ⟨z, hz, rfl⟩
    rw [h1]
    exact Φ.isOpenMap h.openSide h.isOpen_openSide
  open_interior' := by
    have h1 : {x : RiemannSphere |
        ∃ z : Disc, ‖(z : ℂ)‖ < 1 ∧ (⟨fun z => Φ (h.e' z),
          Φ.continuous.comp h.e'.continuous⟩ : C(Disc, RiemannSphere)) z = x} =
        Φ '' h.openSide' := by
      ext x
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨h.e' z, ⟨z, hz, rfl⟩, rfl⟩
      · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
        exact ⟨z, hz, rfl⟩
    rw [h1]
    exact Φ.isOpenMap h.openSide' h.isOpen_openSide'
  cover := by
    show Set.range (fun z : Disc => Φ (h.e z)) ∪ Set.range (fun z : Disc => Φ (h.e' z)) = Set.univ
    have h1 : Set.range (fun z : Disc => Φ (h.e z)) = Φ '' Set.range h.e := by
      ext x; constructor
      · rintro ⟨z, rfl⟩; exact ⟨h.e z, ⟨z, rfl⟩, rfl⟩
      · rintro ⟨y, ⟨z, rfl⟩, rfl⟩; exact ⟨z, rfl⟩
    have h2 : Set.range (fun z : Disc => Φ (h.e' z)) = Φ '' Set.range h.e' := by
      ext x; constructor
      · rintro ⟨z, rfl⟩; exact ⟨h.e' z, ⟨z, rfl⟩, rfl⟩
      · rintro ⟨y, ⟨z, rfl⟩, rfl⟩; exact ⟨z, rfl⟩
    rw [h1, h2, ← Set.image_union, h.cover, Set.image_univ]
    exact Φ.surjective.range_eq
  meet := by
    show Set.range (fun z : Disc => Φ (h.e z)) ∩ Set.range (fun z : Disc => Φ (h.e' z)) =
      Set.range (fun t : ℝ => Φ (c t))
    have h1 : Set.range (fun z : Disc => Φ (h.e z)) = Φ '' Set.range h.e := by
      ext x; constructor
      · rintro ⟨z, rfl⟩; exact ⟨h.e z, ⟨z, rfl⟩, rfl⟩
      · rintro ⟨y, ⟨z, rfl⟩, rfl⟩; exact ⟨z, rfl⟩
    have h2 : Set.range (fun z : Disc => Φ (h.e' z)) = Φ '' Set.range h.e' := by
      ext x; constructor
      · rintro ⟨z, rfl⟩; exact ⟨h.e' z, ⟨z, rfl⟩, rfl⟩
      · rintro ⟨y, ⟨z, rfl⟩, rfl⟩; exact ⟨z, rfl⟩
    have h3 : Set.range (fun t : ℝ => Φ (c t)) = Φ '' Set.range c := by
      ext x; constructor
      · rintro ⟨t, rfl⟩; exact ⟨c t, ⟨t, rfl⟩, rfl⟩
      · rintro ⟨y, ⟨t, rfl⟩, rfl⟩; exact ⟨t, rfl⟩
    rw [h1, h2, h3, ← Set.image_inter Φ.injective, h.meet]


end TwoDiscs

end

end Work.Smooth.SphereJordan
