import Mathlib.GroupTheory.Nilpotent
import Mathlib.Algebra.Field.ZMod
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Submission.Work.SSGRoute.phi1_defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Ext²_G(𝔽_p, U) = 0` when `H¹(G,U) = H²(G,U) = 0`

The trivial `G`-module `𝔽_p = ZMod p` sits in the coefficient short exact sequence
`0 → ℤ --p--> ℤ → 𝔽_p → 0` of trivial representations (`SSGRoute.Phi1.coeffSES`, with
`SSGRoute.Phi1.coeffSES_shortExact` by primality of `p`).  Its contravariant long exact sequence
in the second variable reads, in degrees `1 → 2`,

`Ext¹(ℤ,U) → Ext¹(ℤ,U) --δ--> Ext²(𝔽_p,U) → Ext²(ℤ,U) → Ext²(ℤ,U)`.

Since `Ext¹(ℤ,U) = H¹(G,U)` and `Ext²(ℤ,U) = H²(G,U)` both vanish by hypothesis, the connecting
map `δ` is surjective onto `Ext²(𝔽_p,U)` and its source is a subsingleton, so `Ext²(𝔽_p,U)`
vanishes.  Concretely, for `x : Ext²(𝔽_p,U)`: exactness at `Ext²(𝔽_p,U)` produces a preimage
`x₁ : Ext¹(ℤ,U)` of `x` under the connecting map, and `x₁ = 0` by `H¹(G,U) = 0`.
-/

namespace Work.SSGRoute.ExtChain

open CategoryTheory

set_option linter.style.haveILetI false

noncomputable section

/-- **`Ext²` of the trivial `𝔽_p`-module vanishes** as soon as the first two `Ext`-groups of the
unit representation do: the long exact sequence of the coefficient sequence
`0 → ℤ --p--> ℤ → 𝔽_p → 0` exhibits `Ext²_G(𝔽_p,U)` as a quotient of `Ext¹_G(ℤ,U)`
(it is the image of the connecting map), and `Ext¹_G(ℤ,U) = 0` by hypothesis. -/
theorem ext2_zmod_trivial {p : ℕ} [Fact p.Prime] {G : Type} [Group G]
    (U : Rep.{0} SSGRoute.PTExt.Coeff G)
    (hU1 : Subsingleton (CategoryTheory.Abelian.Ext.{0} (SSGRoute.PTExt.unitRep G) U 1))
    (hU2 : Subsingleton (CategoryTheory.Abelian.Ext.{0} (SSGRoute.PTExt.unitRep G) U 2)) :
    Subsingleton (CategoryTheory.Abelian.Ext.{0}
      (Rep.trivial SSGRoute.PTExt.Coeff G (ZMod p)) U 2) := by
  -- The coefficient sequence `S : 0 → ℤ --p--> ℤ → 𝔽_p → 0` has `S.X₁ = S.X₂ = unitRep G`
  -- and `S.X₃ = 𝔽_p`, so the two hypotheses are exactly the vanishing of `Ext¹(S.X₁,U)` and
  -- `Ext²(S.X₂,U)`.
  haveI h2 : Subsingleton (CategoryTheory.Abelian.Ext.{0}
      (Work.SSGRoute.Phi1.coeffSES G p).X₂ U 2) := hU2
  haveI h1 : Subsingleton (CategoryTheory.Abelian.Ext.{0}
      (Work.SSGRoute.Phi1.coeffSES G p).X₁ U 1) := hU1
  have hS := Work.SSGRoute.Phi1.coeffSES_shortExact G p
  have hzero : ∀ z : CategoryTheory.Abelian.Ext.{0}
      (Rep.trivial SSGRoute.PTExt.Coeff G (ZMod p)) U 2, z = 0 := by
    intro z
    -- exactness of the long exact sequence at `Ext²(S.X₃,U)`: `z` comes from `Ext¹(S.X₁,U)`.
    have hz : (CategoryTheory.Abelian.Ext.mk₀ (Work.SSGRoute.Phi1.coeffSES G p).g).comp z
        (zero_add 2) = 0 := Subsingleton.elim _ _
    obtain ⟨x₁, hx₁⟩ := CategoryTheory.Abelian.Ext.contravariant_sequence_exact₃ hS U z hz
      (show 1 + 1 = 2 by norm_num)
    have hx₁0 : x₁ = 0 := Subsingleton.elim _ _
    rw [hx₁0] at hx₁
    rw [CategoryTheory.Abelian.Ext.comp_zero] at hx₁
    exact hx₁.symm
  exact ⟨fun x y => by rw [hzero x, hzero y]⟩

end

end Work.SSGRoute.ExtChain
