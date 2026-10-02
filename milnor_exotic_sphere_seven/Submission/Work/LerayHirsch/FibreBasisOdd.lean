import Mathlib
import Submission.Work.LerayHirsch.FibreBasis
import Submission.Work.LerayHirsch.bijective_lhMap_fibre_of_trivCore
import Submission.Work.Cohomology.cupNaturalH

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
# The odd-degree decomposition of the cohomology of a fibre

This is the odd-degree companion of `Submission/Work/LerayHirsch/FibreBasis.lean`: the pullback of
the odd-degree Leray–Hirsch decomposition of `P(ε^m)` along the identification
`ψ = projUniv m ∘ projClassFibre Z b : ProjFibre Z b → P(ε^m)` of a fibre with `P(ε^m)` is the
decomposition

`(x_i) ↦ Σ_i (const)^*x_i ⌣ ζ^i`

of the odd cohomology `H^{2k+1}(ProjFibre Z b;ℤ)`, with `x_i ∈ H^{2k+1-2i}(PUnit;ℤ)`.

The main results are

* `Work.LerayHirsch.bijective_CohMap_projUniv_comp_projClassFibre` — the pullback along `ψ` is
  bijective in every degree (it is a homeomorphism, being the composite of
  `Work.LerayHirsch.fibreHomeo` and `Work.LerayHirsch.projUnivHomeo`);
* `Work.LerayHirsch.lhTermFibreOdd` / `lhMapFibreOdd` — the summands and the decomposition map;
* `Work.LerayHirsch.lhMapFibreOdd_eq` — the identification with the pullback of `lhMapOdd`;
* `Work.LerayHirsch.bijective_lhMapFibreOdd_of_kunnethCP` — bijectivity, from the chapter's standing
  input `KunnethCP` alone.

Together with the even part (`Work.LerayHirsch.bijective_lhMapFibre_of_kunnethCP`) this is the full
statement that the restrictions of `1, ζ, …, ζ^{m-1}` to a fibre form a basis of
`H^*(ℂP^{m-1};ℤ)`.
-/

namespace Work.LerayHirsch

open Work.TangentClasses Work.Thom

open scoped LinearAlgebra.Projectivization

noncomputable section

variable {B : Type} [TopologicalSpace B] {ι : Type} {m : ℕ}

/-- **The pullback along `projUniv m ∘ projClassFibre Z b` is bijective** in every degree `n`, being
the pullback along a homeomorphism. -/
theorem bijective_CohMap_projUniv_comp_projClassFibre
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (b : B) (n : ℕ) :
    Function.Bijective
      (CohMap ((projUniv m).comp (projClassFibre Z b)) ℤ n).hom := by
  have hcoe : (↑((fibreHomeo Z b).trans (projUnivHomeo m)) :
      C(ProjFibre Z b, ProjSpace (trivCore m)))
      = (projUniv m).comp (projClassFibre Z b) :=
    ContinuousMap.ext (fun x => rfl)
  rw [← hcoe]
  exact bijective_CohMap_of_homeomorph ((fibreHomeo Z b).trans (projUnivHomeo m)) n

/-- **The `i`-th summand of the odd-degree decomposition of the cohomology of a fibre**:
`(const)^*x ⌣ (fibreIncl Z b)^*(ζ^i)` with `x` in odd degree. -/
noncomputable def lhTermFibreOdd (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι]
    (b : B) (k : ℕ) (i : {i : Fin m // (i : ℕ) ≤ k})
    (x : Coh ℤ (2 * k + 1 - 2 * (i : ℕ)) PUnit) : Coh ℤ (2 * k + 1) (ProjFibre Z b) :=
  cohTransport (by omega)
    (Work.Cohomology.cupH' ℤ (Work.Whitney.ssB (ProjFibre Z b))
      (2 * k + 1 - 2 * (i : ℕ)) (2 * (i : ℕ))
      ((CohMap (ContinuousMap.const (ProjFibre Z b) PUnit.unit)
        ℤ (2 * k + 1 - 2 * (i : ℕ))).hom x)
      ((CohMap (fibreIncl Z b) ℤ (2 * (i : ℕ))).hom (zetaPow Z (i : ℕ))))

/-- **The odd-degree decomposition map of the cohomology of a fibre.** -/
noncomputable def lhMapFibreOdd (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι]
    (b : B) (k : ℕ) :
    ((i : {i : Fin m // (i : ℕ) ≤ k}) → Coh ℤ (2 * k + 1 - 2 * (i : ℕ)) PUnit) →
      Coh ℤ (2 * k + 1) (ProjFibre Z b) :=
  fun xf => ∑ i, lhTermFibreOdd Z b k i (xf i)

/-- **A summand of the odd fibre decomposition is the pullback of a summand of the odd decomposition
of `P(ε^m)`**: the two factors are `Work.Cohomology.cupNaturalH` (naturality of the cup product) and
`Work.LerayHirsch.CohMap_fibreIncl_zetaPow`, and the coefficient factor is the composite
`projMap (trivCore m) ∘ ψ`, which is the constant map. -/
theorem lhTermFibreOdd_pullback (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι]
    (b : B) (k : ℕ) (i : {i : Fin m // (i : ℕ) ≤ k})
    (x : Coh ℤ (2 * k + 1 - 2 * (i : ℕ)) PUnit) :
    (CohMap ((projUniv m).comp (projClassFibre Z b))
        ℤ ((2 * k + 1 - 2 * (i : ℕ)) + 2 * (i : ℕ))).hom
      (Work.Cohomology.cupH' ℤ (Work.Whitney.ssB (ProjSpace (trivCore m)))
        (2 * k + 1 - 2 * (i : ℕ)) (2 * (i : ℕ))
        ((CohMap (projMap (trivCore m)) ℤ (2 * k + 1 - 2 * (i : ℕ))).hom x)
        (zetaPow (trivCore m) (i : ℕ)))
      = Work.Cohomology.cupH' ℤ (Work.Whitney.ssB (ProjFibre Z b))
          (2 * k + 1 - 2 * (i : ℕ)) (2 * (i : ℕ))
          ((CohMap (ContinuousMap.const (ProjFibre Z b) PUnit.unit)
              ℤ (2 * k + 1 - 2 * (i : ℕ))).hom x)
          ((CohMap (fibreIncl Z b) ℤ (2 * (i : ℕ))).hom (zetaPow Z (i : ℕ))) := by
  rw [Work.Cohomology.cupNaturalH ℤ
    (TopCat.ofHom ((projUniv m).comp (projClassFibre Z b)))
    (2 * k + 1 - 2 * (i : ℕ)) (2 * (i : ℕ))
    ((CohMap (projMap (trivCore m)) ℤ (2 * k + 1 - 2 * (i : ℕ))).hom x)
    (zetaPow (trivCore m) (i : ℕ))]
  have h1 : (CohMap ((projUniv m).comp (projClassFibre Z b))
        ℤ (2 * k + 1 - 2 * (i : ℕ))).hom
      ((CohMap (projMap (trivCore m)) ℤ (2 * k + 1 - 2 * (i : ℕ))).hom x)
      = (CohMap (ContinuousMap.const (ProjFibre Z b) PUnit.unit)
          ℤ (2 * k + 1 - 2 * (i : ℕ))).hom x := by
    rw [Work.Thom.CohMap_comp_apply ((projUniv m).comp (projClassFibre Z b))
      (projMap (trivCore m)) ℤ (2 * k + 1 - 2 * (i : ℕ)) x,
      projMap_comp_projUniv_projClassFibre Z b]
  have h2 := (CohMap_fibreIncl_zetaPow Z b (i : ℕ)).symm
  rw [h1, h2]

/-- A summand of the odd fibre decomposition is the pullback of the corresponding summand of the odd
decomposition of `P(ε^m)`. -/
theorem lhTermFibreOdd_eq (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι]
    (b : B) (k : ℕ) (i : {i : Fin m // (i : ℕ) ≤ k})
    (x : Coh ℤ (2 * k + 1 - 2 * (i : ℕ)) PUnit) :
    lhTermFibreOdd Z b k i x
      = (CohMap ((projUniv m).comp (projClassFibre Z b)) ℤ (2 * k + 1)).hom
          (lhTermOdd (trivCore m) k i x) := by
  rw [lhTermFibreOdd, lhTermOdd, Work.Whitney.cohTransport_CohMap, lhTermFibreOdd_pullback]

/-- **The odd fibre decomposition is the pullback of the odd decomposition of `P(ε^m)`.** -/
theorem lhMapFibreOdd_eq (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι]
    (b : B) (k : ℕ) :
    lhMapFibreOdd Z b k
      = fun xf : (i : {i : Fin m // (i : ℕ) ≤ k}) → Coh ℤ (2 * k + 1 - 2 * (i : ℕ)) PUnit =>
          (CohMap ((projUniv m).comp (projClassFibre Z b)) ℤ (2 * k + 1)).hom
            (lhMapOdd (trivCore m) k xf) := by
  funext xf
  rw [lhMapFibreOdd, lhMapOdd, map_sum]
  exact Finset.sum_congr rfl (fun i _ => lhTermFibreOdd_eq Z b k i (xf i))

/-- **The odd-degree part of the basis statement**: the odd decomposition map of a fibre is a
bijection as soon as the trivial-bundle case `LerayHirschFull (trivCore m)` holds. -/
theorem bijective_lhMapFibreOdd_of_trivCore
    (h : LerayHirschFull (trivCore m))
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι] (b : B) (k : ℕ) :
    Function.Bijective (lhMapFibreOdd Z b k) := by
  rw [lhMapFibreOdd_eq]
  exact (bijective_CohMap_projUniv_comp_projClassFibre Z b (2 * k + 1)).comp (h.2 k)

/-- **The odd-degree part of the basis statement, from the chapter's standing input** `KunnethCP`. -/
theorem bijective_lhMapFibreOdd_of_kunnethCP (hK : KunnethCP)
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι] (b : B) (k : ℕ) :
    Function.Bijective (lhMapFibreOdd Z b k) :=
  bijective_lhMapFibreOdd_of_trivCore (lerayHirschFull_of_kunnethCP hK (trivCore m)) Z b k

end

end Work.LerayHirsch
