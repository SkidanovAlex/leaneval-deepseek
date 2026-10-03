import Mathlib

namespace Work.ORHughesFree.DivisionRank

/-- The block map `(x₁, x₂) ↦ (f x₁, φ x₁ + h x₂)` has image of dimension at least
`finrank (range f) + finrank (range h)`: its image projects onto `range f` and contains a
copy of `range h` inside the kernel of that projection. -/
theorem finrank_range_prod_le {D : Type*} [DivisionRing D]
    {M₁ M₂ N₁ N₂ : Type*} [AddCommGroup M₁] [Module D M₁] [AddCommGroup M₂] [Module D M₂]
    [AddCommGroup N₁] [Module D N₁] [AddCommGroup N₂] [Module D N₂]
    [Module.Finite D N₁] [Module.Finite D N₂]
    (f : M₁ →ₗ[D] N₁) (h : M₂ →ₗ[D] N₂) (φ : M₁ →ₗ[D] N₂) :
    Module.finrank D (LinearMap.range f) + Module.finrank D (LinearMap.range h) ≤
      Module.finrank D (LinearMap.range (LinearMap.prod (f.comp (LinearMap.fst D M₁ M₂))
        ((φ.comp (LinearMap.fst D M₁ M₂)) + (h.comp (LinearMap.snd D M₁ M₂))))) := by
  -- `g` is the block map `(x₁, x₂) ↦ (f x₁, φ x₁ + h x₂)`.
  set g : M₁ × M₂ →ₗ[D] N₁ × N₂ :=
    LinearMap.prod (f.comp (LinearMap.fst D M₁ M₂))
      ((φ.comp (LinearMap.fst D M₁ M₂)) + (h.comp (LinearMap.snd D M₁ M₂))) with hg
  have hg_apply : ∀ (x : M₁ × M₂), g x = (f x.1, φ x.1 + h x.2) := by
    intro x; simp [hg, LinearMap.prod_apply]
  -- `p` is the projection of `range g` onto the first factor.
  let p : (LinearMap.range g) →ₗ[D] N₁ := (LinearMap.fst D N₁ N₂).comp (LinearMap.range g).subtype
  have hp_apply : ∀ w : LinearMap.range g, p w = (w : N₁ × N₂).1 := by
    intro w; simp [p]
  -- the projection is onto `range f`
  have hrange_p : LinearMap.range p = LinearMap.range f := by
    ext z
    constructor
    · intro hz
      rw [LinearMap.mem_range] at hz
      obtain ⟨w, hw⟩ := hz
      rw [← hw, LinearMap.mem_range]
      obtain ⟨x, hx⟩ := LinearMap.mem_range.mp w.2
      refine ⟨x.1, ?_⟩
      rw [hp_apply, ← hx, hg_apply]
    · intro hz
      rw [LinearMap.mem_range] at hz
      obtain ⟨x₁, hx₁⟩ := hz
      rw [← hx₁, LinearMap.mem_range]
      refine ⟨⟨g (x₁, 0), LinearMap.mem_range_self g _⟩, ?_⟩
      simp [hp_apply, hg_apply]
  -- rank-nullity for the projection
  have hrank : Module.finrank D (LinearMap.range f) + Module.finrank D (p.ker) =
      Module.finrank D (LinearMap.range g) := by
    have hh := LinearMap.finrank_range_add_finrank_ker p
    rw [hrange_p] at hh
    exact hh
  -- the copy of `range h` sitting in `ker p`
  let s : (LinearMap.range h) →ₗ[D] (N₁ × N₂) := (LinearMap.inr D N₁ N₂).comp (LinearMap.range h).subtype
  have hs_apply : ∀ y : LinearMap.range h, s y = (0, (y : N₂)) := by
    intro y; simp [s]
  let s1 : (LinearMap.range h) →ₗ[D] (LinearMap.range g) :=
    LinearMap.codRestrict (LinearMap.range g) s (fun y => by
      obtain ⟨x₂, hx₂⟩ := LinearMap.mem_range.mp y.2
      rw [hs_apply, LinearMap.mem_range]
      refine ⟨(0, x₂), ?_⟩
      rw [hg_apply]
      simp [hx₂])
  have hs1_apply : ∀ y : LinearMap.range h, ((s1 y : LinearMap.range g) : N₁ × N₂) = (0, (y : N₂)) := by
    intro y; rw [LinearMap.codRestrict_apply, hs_apply]
  let s2 : (LinearMap.range h) →ₗ[D] (LinearMap.ker p) :=
    LinearMap.codRestrict (LinearMap.ker p) s1 (fun y => by
      rw [LinearMap.mem_ker, hp_apply, hs1_apply])
  have hs2_apply : ∀ y : LinearMap.range h, (((s2 y : LinearMap.ker p) : LinearMap.range g) : N₁ × N₂) = (0, (y : N₂)) := by
    intro y; rw [LinearMap.codRestrict_apply, hs1_apply]
  have hinj : Function.Injective s2 := by
    intro y y' hyy'
    have h1 := congrArg (fun z : LinearMap.ker p => (((z : LinearMap.range g) : N₁ × N₂))) hyy'
    rw [hs2_apply, hs2_apply] at h1
    have h2 : (y : N₂) = (y' : N₂) := by
      simpa using congrArg Prod.snd h1
    exact Subtype.ext h2
  have hle : Module.finrank D (LinearMap.range h) ≤ Module.finrank D (LinearMap.ker p) :=
    LinearMap.finrank_le_finrank_of_injective hinj
  calc Module.finrank D (LinearMap.range f) + Module.finrank D (LinearMap.range h)
      ≤ Module.finrank D (LinearMap.range f) + Module.finrank D (LinearMap.ker p) :=
        Nat.add_le_add_left hle _
    _ = Module.finrank D (LinearMap.range g) := hrank

end Work.ORHughesFree.DivisionRank
