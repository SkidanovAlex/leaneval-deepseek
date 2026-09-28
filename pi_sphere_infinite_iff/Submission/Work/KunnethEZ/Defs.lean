import Mathlib
import Submission.Work.Cohomology.Crux33.EzGen
import Submission.Work.Cohomology.Crux33.ezBridge

/-!
# The chain-level Eilenberg–Zilber shuffle chain (general bidegree)

`Work.KunnethEZ.ezChain p q X Y u v` is the Eilenberg–Zilber shuffle chain of a `p`-chain `u` of
`X` and a `q`-chain `v` of `Y`, defined by linear extension of the simplex-level shuffle chain
`Work.Cohomology.Crux33.ezGen p q` over the canonical coordinate representation of chains
(`Work.Cohomology.Crux33.coords`).
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicTopology Simplicial Limits MonoidalCategory
open scoped Simplicial

namespace Work.KunnethEZ

noncomputable section

/-- `ℤ` as a module, spelled once. -/
abbrev ezR : ModuleCat ℤ := ModuleCat.of ℤ ℤ

/-- **The chain-level Eilenberg–Zilber shuffle chain**: the bilinear extension of the
simplex-level shuffle chain `Work.Cohomology.Crux33.ezGen p q` to `p`- and `q`-chains. -/
noncomputable def ezChain (p q : ℕ) (X Y : SSet)
    (u : (X.chainComplex ezR).X p) (v : (Y.chainComplex ezR).X q) :
    ((X ⊗ Y).chainComplex ezR).X (p+q) :=
  ∑ σ ∈ (Work.Cohomology.Crux33.coords X p u).support,
    ∑ τ ∈ (Work.Cohomology.Crux33.coords Y q v).support,
      ((Work.Cohomology.Crux33.coords X p u σ) * (Work.Cohomology.Crux33.coords Y q v τ)) •
        Work.Cohomology.Crux33.ezGen p q X Y σ τ

/-- The chain-level shuffle chain on a pair of generators is the simplex-level shuffle chain. -/
lemma ezChain_gen (p q : ℕ) (X Y : SSet)
    (σ : X.obj (Opposite.op (SimplexCategory.mk p)))
    (τ : Y.obj (Opposite.op (SimplexCategory.mk q))) :
    ezChain p q X Y ((X.ιChainComplex (R := ezR) σ).hom 1)
      ((Y.ιChainComplex (R := ezR) τ).hom 1)
      = Work.Cohomology.Crux33.ezGen p q X Y σ τ := by
  unfold ezChain
  rw [Work.Cohomology.Crux33.coords_ι, Work.Cohomology.Crux33.coords_ι]
  simp

end

end Work.KunnethEZ
