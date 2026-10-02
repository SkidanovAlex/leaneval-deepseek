import Mathlib
import Submission.Work.LerayHirsch.LhTermFibre
import Submission.Work.LerayHirsch.bijective_lhMap_fibre_of_trivCore
import Submission.Work.LerayHirsch.lerayHirsch_of_kunnethCP

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
# The Leray–Hirsch decomposition of the cohomology of a fibre

This module spells out the second half of the Leray–Hirsch statement of
`Submission/Work/LerayHirsch/README.md` §0.2 in the form in which it is used: the classes
`1, ζ, …, ζ^{m-1}` **restrict to a basis of the cohomology of each fibre** `ProjFibre Z b ≅ ℂP^{m-1}`.

The decomposition map of a fibre is

```lean
Work.LerayHirsch.lhTermFibre Z b k i x :
  Coh ℤ (2 * k) (ProjFibre Z b)      -- `(const)^*x ⌣ (fibreIncl)^*(ζ^i)`
Work.LerayHirsch.lhMapFibre Z b k    -- the sum over `i`
```

* `Work.LerayHirsch.lhTermFibre` — the `i`-th summand: the coefficient `x ∈ H^{2(k-i)}(PUnit;ℤ)`
  pulled back along the constant map to the fibre, multiplied by the restriction
  `(fibreIncl Z b)^*(ζ_Z^i)` of the `i`-th power of the hyperplane class.  By
  `Work.LerayHirsch.CohMap_fibreIncl_zetaPow` the latter is the `i`-th power of the fibre's
  hyperplane class, so this is literally `x ⌣ ζ^i` on the fibre.
* `Work.LerayHirsch.lhMapFibre` — the sum, i.e. the candidate basis expansion
  `(x_i) ↦ Σ_i (const)^*x_i ⌣ ζ^i`.
* `Work.LerayHirsch.lhTermFibre_eq` / `lhMapFibre_eq` — the identification with the pullback of the
  trivial-bundle decomposition `lhMap (trivCore m) k` along the canonical identification
  `projUniv m ∘ projClassFibre Z b : ProjFibre Z b → P(ε^m)` (the summand statement is
  `Work.LerayHirsch.lhTerm_fibre_pullback`).
* `Work.LerayHirsch.bijective_lhMapFibre_of_trivCore` — **`lhMapFibre Z b k` is a bijection** as
  soon as the trivial-bundle case `LerayHirschFull (trivCore m)` holds, i.e. as soon as
  `Work.LerayHirsch.KunnethCP` does (`bijective_lhMapFibre_of_kunnethCP`); the proof is
  `Work.LerayHirsch.bijective_lhMap_fibre_of_trivCore`, whose content is that the pullback along the
  homeomorphism `projUniv m ∘ projClassFibre Z b` is a bijection.

So the whole content of "`H^*(fibre)` is free on `1, ζ, …, ζ^{m-1}`" is the trivial-bundle case of
Künneth, which is the standing input `KunnethCP` of the chapter (subproject KUNNETH).
-/

namespace Work.LerayHirsch

open Work.TangentClasses Work.Thom

open scoped LinearAlgebra.Projectivization

noncomputable section

variable {B : Type} [TopologicalSpace B] {ι : Type} {m : ℕ}

/-- **The `i`-th summand of the decomposition of the cohomology of a fibre**:
`(const)^*x ⌣ (fibreIncl Z b)^*(ζ^i)`, where `const : ProjFibre Z b → PUnit` is the constant map. -/
noncomputable def lhTermFibre (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι]
    (b : B) (k : ℕ) (i : {i : Fin m // (i : ℕ) ≤ k}) (x : Coh ℤ (2 * (k - (i : ℕ))) PUnit) :
    Coh ℤ (2 * k) (ProjFibre Z b) :=
  cohTransport (by omega)
    (Work.Whitney.cupChern (k - (i : ℕ)) (i : ℕ)
      ((CohMap (ContinuousMap.const (ProjFibre Z b) PUnit.unit)
        ℤ (2 * (k - (i : ℕ)))).hom x)
      ((CohMap (fibreIncl Z b) ℤ (2 * (i : ℕ))).hom (zetaPow Z (i : ℕ))))

/-- **The decomposition map of the cohomology of a fibre**: `(x_i) ↦ Σ_i (const)^*x_i ⌣ ζ^i`. -/
noncomputable def lhMapFibre (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι]
    (b : B) (k : ℕ) :
    ((i : {i : Fin m // (i : ℕ) ≤ k}) → Coh ℤ (2 * (k - (i : ℕ))) PUnit) →
      Coh ℤ (2 * k) (ProjFibre Z b) :=
  fun xf => ∑ i, lhTermFibre Z b k i (xf i)

/-- A summand of the fibre decomposition is the pullback of the corresponding summand of the
decomposition of `P(ε^m)`. -/
theorem lhTermFibre_eq (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι]
    (b : B) (k : ℕ) (i : {i : Fin m // (i : ℕ) ≤ k})
    (x : Coh ℤ (2 * (k - (i : ℕ))) PUnit) :
    lhTermFibre Z b k i x
      = (CohMap ((projUniv m).comp (projClassFibre Z b)) ℤ (2 * k)).hom
          (lhTerm (trivCore m) k i x) := by
  rw [lhTermFibre, lhTerm_def, Work.Whitney.cohTransport_CohMap, lhTerm_fibre_pullback]

/-- **The fibre decomposition is the pullback of the trivial-bundle decomposition.** -/
theorem lhMapFibre_eq (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι]
    (b : B) (k : ℕ) :
    lhMapFibre Z b k
      = fun xf : (i : {i : Fin m // (i : ℕ) ≤ k}) → Coh ℤ (2 * (k - (i : ℕ))) PUnit =>
          (CohMap ((projUniv m).comp (projClassFibre Z b)) ℤ (2 * k)).hom
            (lhMap (trivCore m) k xf) := by
  funext xf
  rw [lhMapFibre, lhMap_apply, map_sum]
  exact Finset.sum_congr rfl (fun i _ => lhTermFibre_eq Z b k i (xf i))

/-- **The classes `1, ζ, …, ζ^{m-1}` restrict to a basis of the cohomology of each fibre**, modulo
the trivial-bundle case of Leray–Hirsch: if `LerayHirschFull (trivCore m)` holds, then the
decomposition map `(x_i) ↦ Σ_i (const)^*x_i ⌣ ζ^i` of `H^*(ProjFibre Z b;ℤ)` is a bijection in
every even degree. -/
theorem bijective_lhMapFibre_of_trivCore
    (h : LerayHirschFull (trivCore m))
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι] (b : B) (k : ℕ) :
    Function.Bijective (lhMapFibre Z b k) := by
  rw [lhMapFibre_eq]
  exact bijective_lhMap_fibre_of_trivCore h Z b k

/-- **The same, from the chapter's standing input**: `KunnethCP` (Künneth for `B × ℂP^{m-1}`,
subproject KUNNETH) gives the decomposition of the cohomology of each fibre on `1, ζ, …, ζ^{m-1}`. -/
theorem bijective_lhMapFibre_of_kunnethCP (hK : KunnethCP)
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι] (b : B) (k : ℕ) :
    Function.Bijective (lhMapFibre Z b k) :=
  bijective_lhMapFibre_of_trivCore (lerayHirschFull_of_kunnethCP hK (trivCore m)) Z b k

end

end Work.LerayHirsch
