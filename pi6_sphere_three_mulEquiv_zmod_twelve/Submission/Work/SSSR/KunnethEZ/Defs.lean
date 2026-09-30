import Mathlib
import Submission.Work.SSSR.Cohomology.Crux33.EzGen
import Submission.Work.SSSR.Cohomology.Crux33.ezBridge
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicTopology Simplicial Limits MonoidalCategory
open scoped Simplicial
namespace Work.SSSR.KunnethEZ

noncomputable section

/-- `ℤ` as a module, spelled once. -/
abbrev ezR (R : Type) [CommRing R] [Nontrivial R] : ModuleCat R := ModuleCat.of R R

/-- **The chain-level Eilenberg–Zilber shuffle chain**: the bilinear extension of the
simplex-level shuffle chain `Work.Cohomology.Crux33.ezGen p q` to `p`- and `q`-chains. -/
noncomputable def ezChain (R : Type) [CommRing R] [Nontrivial R] (p q : ℕ) (X Y : SSet)
    (u : (X.chainComplex (ezR R)).X p) (v : (Y.chainComplex (ezR R)).X q) :
    ((X ⊗ Y).chainComplex (ezR R)).X (p+q) :=
  ∑ σ ∈ (Work.SSSR.Cohomology.Crux33.coords X p u).support,
    ∑ τ ∈ (Work.SSSR.Cohomology.Crux33.coords Y q v).support,
      ((Work.SSSR.Cohomology.Crux33.coords X p u σ) * (Work.SSSR.Cohomology.Crux33.coords Y q v τ)) •
        Work.SSSR.Cohomology.Crux33.ezGen p q X Y σ τ

/-- The chain-level shuffle chain on a pair of generators is the simplex-level shuffle chain. -/
lemma ezChain_gen (p q : ℕ) (X Y : SSet)
    (σ : X.obj (Opposite.op (SimplexCategory.mk p)))
    (τ : Y.obj (Opposite.op (SimplexCategory.mk q))) :
    ezChain R p q X Y ((X.ιChainComplex (R := (ezR R)) σ).hom 1)
      ((Y.ιChainComplex (R := (ezR R)) τ).hom 1)
      = Work.SSSR.Cohomology.Crux33.ezGen p q X Y σ τ := by
  unfold ezChain
  rw [Work.SSSR.Cohomology.Crux33.coords_ι, Work.SSSR.Cohomology.Crux33.coords_ι]
  simp

end

end Work.SSSR.KunnethEZ
