import Mathlib
import Submission.Work.SSGRoute.ShapiroInduced
import Submission.Work.Shrinking.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Shapiro permutation module of a family of subgroups

For a finite family of subgroups `H : ι → Subgroup G` of a group `G` we fix once and for all the
`𝔽_p[G]`-module

`shapiroT p G ι H = ∏_{a : ι} 𝔽_p[G ⧸ H a]`

(the product of the permutation modules on the individual coset spaces).  `G` acts on each coset
space by left translation and coordinatewise on the product.

Defining it (rather than existentially quantifying it, as `exists_shapiro_packaging` does) is what
lets the coinvariant shrinking argument of Schmidt–Wingberg be applied at the *local* places of a
Scholz solution: the coefficient module `T` must be fixed *before* the level `m` is chosen, while
the `2`-cocycles it carries depend on the level and on the Scholz solution.
-/

namespace Work.SSGRoute

open scoped TensorProduct

/-- The permutation module `∏_{a : ι} 𝔽_p[G ⧸ H a]` of a finite family of subgroups. -/
abbrev shapiroT (p : ℕ) (G : Type*) [Group G] (ι : Type*) (H : ι → Subgroup G) : Type _ :=
  ∀ a : ι, Shapiro.PermModX p (G ⧸ H a)

section Instances

variable {p : ℕ} {G : Type*} [Group G] {ι : Type*} {H : ι → Subgroup G}

noncomputable instance (priority := 100) instFintypeQuot_subgroup [Finite G] (Hc : Subgroup G) : Fintype (G ⧸ Hc) :=
  Fintype.ofFinite _

end Instances

/-- The coordinate projection `∏_a 𝔽_p[G ⧸ H a] → 𝔽_p[G ⧸ H a]`. -/
noncomputable def shapiroProj (p : ℕ) (G : Type*) [Group G] (ι : Type*) (H : ι → Subgroup G)
    (a : ι) : shapiroT p G ι H →ₗ[ZMod p] Shapiro.PermModX p (G ⧸ H a) :=
  LinearMap.proj a

/-- The coordinate insertion `𝔽_p[G ⧸ H a] → ∏_a 𝔽_p[G ⧸ H a]`. -/
noncomputable def shapiroSingle (p : ℕ) (G : Type*) [Group G] (ι : Type*) (H : ι → Subgroup G)
    [DecidableEq ι] (a : ι) : Shapiro.PermModX p (G ⧸ H a) →ₗ[ZMod p] shapiroT p G ι H :=
  LinearMap.single (ZMod p) (fun a => Shapiro.PermModX p (G ⧸ H a)) a

end Work.SSGRoute
