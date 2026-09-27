import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.Fund.Basic
import Submission.Work.KT.Fund.Geom
import Submission.Work.KT.Fund.Disc

/-!
# `Work.KT.Fund.AssemblyDefs` — the maps in the statement of `fund_product`

The target `Work.KT.fund_product` asserts the bijectivity of
`Φ(a,b) = s(a) + μ (s b) γ` where
* `s` is the pull-back along the projection `X × S² → X`,
* `γ = snd*(cls hopfIdem)` is the Hopf class on `X × S²`,
* `μ` is any `IsK0Mul` product.

The proof reduces (`NOTES_kappa.md` §0) to the statement that
`bottMap b = μ (s b) (γ - 1)` is an isomorphism `K0 C(X,ℂ) → ker r`, where `r` is the restriction
to the base point `pt = up 0` (where `hopfIdem` is literally `diag(1,0)`).

This file only fixes the notation.
-/

namespace Work.KT.Fund

open Matrix

noncomputable section

variable (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]

/-- The base point of `S²`, taken in the upper hemisphere chart (there `hopfIdem` is `diag(1,0)`). -/
def pt : S2 := up 0

/-- The inclusion of the base point `X → X × S²`. -/
def bp : C(X, X × S2) :=
  { toFun := fun x => (x, pt)
    continuous_toFun := by fun_prop }

/-- Restriction of `K₀`-classes on `X × S²` to the base point `X × {pt}`. -/
def r : K0 C(X × S2, ℂ) →+ K0 C(X, ℂ) := K0.mapA (pullAlg (bp X))

/-- Pull-back along the projection `X × S² → X`. -/
def s : K0 C(X, ℂ) →+ K0 C(X × S2, ℂ) :=
  K0.mapA (pullAlg (ContinuousMap.fst : C(X × S2, X)))

/-- The Hopf class on `X × S²`. -/
def gamma : K0 C(X × S2, ℂ) :=
  K0.mapA (pullAlg (ContinuousMap.snd : C(X × S2, S2))) (cls hopfIdem)

/-- The reduced Bott class `γ - 1` on `X × S²`. -/
def beta : K0 C(X × S2, ℂ) := gamma X - cls (Mat.one C(X × S2, ℂ) 1)

/-- The map `a ↦ s(a) · β` whose bijectivity is Bott periodicity. -/
def bottMap (μ : K0 C(X × S2, ℂ) →+ K0 C(X × S2, ℂ) →+ K0 C(X × S2, ℂ))
    (a : K0 C(X, ℂ)) : K0 C(X × S2, ℂ) := μ (s X a) (beta X)

/-- The map of the node: `(a,b) ↦ s(a) + μ (s b) γ`. -/
def phi (μ : K0 C(X × S2, ℂ) →+ K0 C(X × S2, ℂ) →+ K0 C(X × S2, ℂ))
    (ab : K0 C(X, ℂ) × K0 C(X, ℂ)) : K0 C(X × S2, ℂ) :=
  s X ab.1 + μ (s X ab.2) (gamma X)

end

end Work.KT.Fund
