import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Topology.Defs.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Submission.Work.SSGRoute.PT.AlphaPairing
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Naturality of the `α²`-pairing in the coefficient `N`

For an equivariant `φ : N₁ →+ N₂` of `G`-modules, precomposition `f ↦ f ∘ φ` is an equivariant
map `Hom_ℤ(N₂,C) →+ Hom_ℤ(N₁,C)`, hence acts on `H²`.  The cupping pairing
`α² : H²(G, Hom_ℤ(N,C)) × H⁰(G,N) → H²(G,C)`, `(c, n) ↦ c ⌣ n`, is natural:

`α² (mapH2 (precomp φ) x) n = α² x (φ n)`.

Both sides are represented by the same `2`-cocycle `(g,h) ↦ c(g,h)(φ n)`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open Classical

namespace Work.SSGRoute.PT

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- The cocycle underlying `α²` commutes with the coefficient map: cupping a pushed-forward cocycle
with an invariant `n : N₁` gives the same `2`-cocycle as cupping the original cocycle with
`φ n`. -/
theorem cupCochainZ2_comp_precomp
    {N₁ : Type*} [AddCommGroup N₁] [DistribMulAction G N₁]
    {N₂ : Type*} [AddCommGroup N₂] [DistribMulAction G N₂]
    {C : Type*} [AddCommGroup C] [DistribMulAction G C]
    (φ : N₁ →+ N₂) (hφ : Work.GroupCohomology.IsEquivariant G φ)
    (hpre : Work.GroupCohomology.IsEquivariant G (ConjHom.precomp φ))
    (c : ↥(Work.AbsoluteKummer.Z2 G (ConjHom N₂ C)))
    (n : ↥(Work.GroupCohomology.invariants G N₁)) :
    cupCochainZ2 (Work.AbsoluteKummer.mapZ2 (ConjHom.precomp φ) hpre c) n
      = cupCochainZ2 c (invariantsHom φ hφ n) := by
  refine Subtype.ext (funext fun p => rfl)

theorem alphaTwo_naturality {G : Type*} [Group G] [TopologicalSpace G]
    {N₁ : Type*} [AddCommGroup N₁] [DistribMulAction G N₁]
    {N₂ : Type*} [AddCommGroup N₂] [DistribMulAction G N₂]
    {C : Type*} [AddCommGroup C] [DistribMulAction G C]
    (φ : N₁ →+ N₂) (hφ : Work.GroupCohomology.IsEquivariant G φ)
    (hpre : Work.GroupCohomology.IsEquivariant G (Work.SSGRoute.PT.ConjHom.precomp φ))
    (x : Work.AbsoluteKummer.H2 G (Work.SSGRoute.PT.ConjHom N₂ C))
    (n : ↥(Work.GroupCohomology.invariants G N₁)) :
    Work.SSGRoute.PT.alphaTwo
        (Work.AbsoluteKummer.mapH2 (Work.SSGRoute.PT.ConjHom.precomp φ) hpre x) n
      = Work.SSGRoute.PT.alphaTwo x (Work.SSGRoute.PT.invariantsHom φ hφ n) := by
  suffices key : ∀ c : ↥(Work.AbsoluteKummer.Z2 G (Work.SSGRoute.PT.ConjHom N₂ C)),
      Work.SSGRoute.PT.alphaTwo
        (Work.AbsoluteKummer.mapH2 (Work.SSGRoute.PT.ConjHom.precomp φ) hpre
          (Work.AbsoluteKummer.H2π G (Work.SSGRoute.PT.ConjHom N₂ C) c)) n
      = Work.SSGRoute.PT.alphaTwo
          (Work.AbsoluteKummer.H2π G (Work.SSGRoute.PT.ConjHom N₂ C) c)
          (Work.SSGRoute.PT.invariantsHom φ hφ n) by
    obtain ⟨c, hc⟩ := QuotientAddGroup.mk'_surjective
      ((Work.AbsoluteKummer.B2 G (Work.SSGRoute.PT.ConjHom N₂ C)).comap
        (Work.AbsoluteKummer.Z2 G (Work.SSGRoute.PT.ConjHom N₂ C)).subtype) x
    rw [← hc]
    exact key c
  intro c
  rw [Work.AbsoluteKummer.mapH2_H2π, Work.SSGRoute.PT.alphaTwo_H2π, Work.SSGRoute.PT.alphaTwo_H2π]
  exact congrArg (Work.AbsoluteKummer.H2π G C) (cupCochainZ2_comp_precomp φ hφ hpre c n)

end Work.SSGRoute.PT
