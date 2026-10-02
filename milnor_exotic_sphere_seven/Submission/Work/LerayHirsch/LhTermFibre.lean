import Mathlib
import Submission.Work.LerayHirsch.FibreZetaPow
import Submission.Work.LerayHirsch.bijective_lhMap_fibre_of_trivCore

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# The summands of the Leray–Hirsch decomposition, restricted to a fibre

`Work.LerayHirsch.lhTerm (trivCore m) k i x` is the summand `π^*(x) ⌣ ζ_{ε^m}^i` of the Leray–Hirsch
decomposition of `H^{2k}(P(ε^m);ℤ)` (with `π : P(ε^m) → PUnit`).  This module computes its pullback
along the identification `ψ = projUniv m ∘ projClassFibre Z b : ProjFibre Z b → P(ε^m)` of a fibre
with `P(ε^m)`:

`ψ^*(π^*x ⌣ ζ_{ε^m}^i) = (const)^*x ⌣ (fibreIncl)^*(ζ_Z^i)`,

where

* `const : ProjFibre Z b → PUnit` is the constant map (the coefficient map: `π ∘ ψ` is constant
  because its target `PUnit` is a singleton), and
* `(fibreIncl Z b)^*(ζ_Z^i)` is the restriction of `ζ_Z^i` to the fibre, identified with the
  `i`-th power of the fibre's hyperplane class by `Work.LerayHirsch.CohMap_fibreIncl_zetaPow`.

Together with `Work.LerayHirsch.bijective_lhMap_fibre_of_trivCore` this is exactly the classical
form of the second half of the Leray–Hirsch statement (`Submission/Work/LerayHirsch/README.md`
§0.5): the restrictions of `1, ζ, …, ζ^{m-1}` to a fibre form a basis of `H^*(ℂP^{m-1};ℤ)`, the
coefficients being the cohomology of the point `PUnit`.

The proof is `Work.Whitney.cupChern_CohMap` for the two factors, `Work.Thom.CohMap_comp_apply` to
identify `π ∘ ψ` with the constant map, and `Work.LerayHirsch.CohMap_fibreIncl_zetaPow` for the
second factor.
-/

namespace Work.LerayHirsch

open Work.TangentClasses Work.Thom

open scoped LinearAlgebra.Projectivization

noncomputable section

variable {B : Type} [TopologicalSpace B] {ι : Type} {m : ℕ}

/-- `π ∘ ψ` is the constant map to the unique point of `PUnit`. -/
theorem projMap_comp_projUniv_projClassFibre
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (b : B) :
    (projMap (trivCore m)).comp ((projUniv m).comp (projClassFibre Z b))
      = ContinuousMap.const (ProjFibre Z b) PUnit.unit :=
  ContinuousMap.ext (fun z => Subsingleton.elim _ _)

/-- **The pullback of a summand of the Leray–Hirsch decomposition of `P(ε^m)` to a fibre**: it is the
product of the coefficient and the restriction of `ζ_Z^i` to the fibre. -/
theorem lhTerm_fibre_pullback (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι]
    (b : B) (k : ℕ) (i : {i : Fin m // (i : ℕ) ≤ k})
    (x : Coh ℤ (2 * (k - (i : ℕ))) PUnit) :
    (CohMap ((projUniv m).comp (projClassFibre Z b))
        ℤ (2 * ((k - (i : ℕ)) + (i : ℕ)))).hom
      (Work.Whitney.cupChern (k - (i : ℕ)) (i : ℕ)
        ((CohMap (projMap (trivCore m)) ℤ (2 * (k - (i : ℕ)))).hom x)
        (zetaPow (trivCore m) (i : ℕ)))
      = Work.Whitney.cupChern (k - (i : ℕ)) (i : ℕ)
          ((CohMap (ContinuousMap.const (ProjFibre Z b) PUnit.unit)
              ℤ (2 * (k - (i : ℕ)))).hom x)
          ((CohMap (fibreIncl Z b) ℤ (2 * (i : ℕ))).hom (zetaPow Z (i : ℕ))) := by
  rw [Work.Whitney.cupChern_CohMap]
  have h1 : (CohMap ((projUniv m).comp (projClassFibre Z b))
        ℤ (2 * (k - (i : ℕ)))).hom
      ((CohMap (projMap (trivCore m)) ℤ (2 * (k - (i : ℕ)))).hom x)
      = (CohMap (ContinuousMap.const (ProjFibre Z b) PUnit.unit)
          ℤ (2 * (k - (i : ℕ)))).hom x := by
    rw [Work.Thom.CohMap_comp_apply ((projUniv m).comp (projClassFibre Z b))
      (projMap (trivCore m)) ℤ (2 * (k - (i : ℕ))) x,
      projMap_comp_projUniv_projClassFibre Z b]
  have h2 := (CohMap_fibreIncl_zetaPow Z b (i : ℕ)).symm
  rw [h1, h2]

end

end Work.LerayHirsch
