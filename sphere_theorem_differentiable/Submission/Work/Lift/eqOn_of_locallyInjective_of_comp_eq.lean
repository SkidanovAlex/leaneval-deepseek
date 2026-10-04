import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.style.haveILetI false

namespace Work.Lift

/-- Two continuous maps `u₁ u₂ : ℝ → X` into a Hausdorff space that lift the same path
`γ : ℝ → Y` through a map `f : X → Y` which is injective on a neighbourhood of every point
`u₁ s` (`s ∈ [0,S]`), and which agree at `0`, agree on all of `[0,S]`.

The argument is the classical one: the equal locus of `u₁` and `u₂` is closed in `↥(Icc 0 S)`
(because `X` is Hausdorff) and open in `↥(Icc 0 S)` (because `f` is injective on a neighbourhood
of `u₁ s`, whence `u₁ = u₂` on a neighbourhood of any point where they already agree), so it is a
nonempty clopen subset of a preconnected space. -/
theorem eqOn_of_locallyInjective_of_comp_eq
    {X Y : Type*} [TopologicalSpace X] [T2Space X] [TopologicalSpace Y]
    {f : X → Y} {u₁ u₂ : ℝ → X} {γ : ℝ → Y} {S : ℝ} (hS : 0 ≤ S)
    (hu₁ : ContinuousOn u₁ (Set.Icc 0 S)) (hu₂ : ContinuousOn u₂ (Set.Icc 0 S))
    (h₁ : ∀ s ∈ Set.Icc 0 S, f (u₁ s) = γ s) (h₂ : ∀ s ∈ Set.Icc 0 S, f (u₂ s) = γ s)
    (h0 : u₁ 0 = u₂ 0)
    (hloc : ∀ s ∈ Set.Icc 0 S, ∃ U ∈ nhds (u₁ s), ∀ a ∈ U, ∀ b ∈ U, f a = f b → a = b) :
    ∀ s ∈ Set.Icc 0 S, u₁ s = u₂ s := by
  haveI hpre : PreconnectedSpace ↥(Set.Icc 0 S) :=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  have hg₁ : Continuous ((Set.Icc 0 S).domRestrict u₁) := hu₁.domRestrict
  have hg₂ : Continuous ((Set.Icc 0 S).domRestrict u₂) := hu₂.domRestrict
  let E : Set ↥(Set.Icc 0 S) :=
    {x | (Set.Icc 0 S).domRestrict u₁ x = (Set.Icc 0 S).domRestrict u₂ x}
  have hEcl : IsClosed E := isClosed_eq hg₁ hg₂
  have hEop : IsOpen E := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    have hx' : u₁ ↑x = u₂ ↑x := hx
    obtain ⟨U, hU, hinj⟩ := hloc ↑x x.2
    have hU₂ : U ∈ nhds (u₂ ↑x) := hx' ▸ hU
    have h1 : (Set.Icc 0 S).domRestrict u₁ ⁻¹' U ∈ nhds x :=
      hg₁.continuousAt.preimage_mem_nhds hU
    have h2 : (Set.Icc 0 S).domRestrict u₂ ⁻¹' U ∈ nhds x :=
      hg₂.continuousAt.preimage_mem_nhds hU₂
    filter_upwards [h1, h2] with y hy1 hy2
    simp only [Set.domRestrict, Set.mem_preimage] at hy1 hy2 ⊢
    exact hinj (u₁ ↑y) hy1 (u₂ ↑y) hy2 (by rw [h₁ ↑y y.2, h₂ ↑y y.2])
  have hEnon : E.Nonempty := ⟨⟨0, ⟨le_refl 0, hS⟩⟩, h0⟩
  have hAll : E = Set.univ := IsClopen.eq_univ ⟨hEcl, hEop⟩ hEnon
  have hpoint : ∀ x : ↥(Set.Icc 0 S), u₁ ↑x = u₂ ↑x := by
    intro x
    have hx : x ∈ E := by rw [hAll]; trivial
    simpa [E, Set.domRestrict] using hx
  intro s hs
  exact hpoint ⟨s, hs⟩

end Work.Lift
