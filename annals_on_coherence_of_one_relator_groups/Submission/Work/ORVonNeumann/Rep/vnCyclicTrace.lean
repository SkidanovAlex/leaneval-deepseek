/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ORVonNeumann area (N5 of the one-relator coherence project)

# The cyclic trace `∑ i ⟪δᵢ, (X ∘ Y) δᵢ⟫ = ∑ j ⟪δⱼ, (Y ∘ X) δⱼ⟫` for equivariant operators

An operator `Z : ⊕_{j : Fin m} ℓ²(G) → ⊕_{i : Fin n} ℓ²(G)` that commutes with the block
diagonal right regular action `diagOp` is exactly a matrix over the group von Neumann algebra
`N(G) = ρ(G)'`.  This module records that correspondence:

* `Work.ORVonNeumann.Rep.matOfEquiv` — the matrix of an equivariant operator, with entries
  `(matOfEquiv X hX) i j = hcoord i ∘ X ∘ hinclude j`, an element of `N(G)` because `X` is
  equivariant;
* `Work.ORVonNeumann.Rep.matOp_matOfEquiv` — the round trip, `matOp (matOfEquiv X hX) = X`:
  every equivariant operator *is* a matrix operator.

The target `Work.ORVonNeumann.Rep.vnCyclicTrace` is then immediate: writing an equivariant
operator as `matOp` of its matrix reduces the identity to the traciality of the amplified trace
`vnMTraceTracial`, combined with `vnMatOpMul` (multiplicativity of `matOp`) and `vnInnerHdelta`
(the diagonal matrix coefficient of `matOp` against `δ`).

This is the amplification of the traciality of `τ a = ⟪δ₁, a δ₁⟫`, and the algebraic input to
the identification of the von Neumann dimension of the range of a matrix operator with that of
its adjoint.
-/
import Mathlib
import Submission.Work.ORVonNeumann.Rep.vnDiag
import Submission.Work.ORVonNeumann.Rep.vnMTraceTracial
import Submission.Work.ORVonNeumann.Rep.vnInnerHdelta
import Submission.Work.ORVonNeumann.Rep.vnMatOpMul

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped InnerProductSpace InnerProduct

namespace Work.ORVonNeumann.Rep

universe u

variable {G : Type u} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [MeasurableMul G]

/-- The composition `hcoord i ∘ X ∘ hinclude j` commutes with the right regular
representation when `X` is equivariant, i.e. it lies in the group von Neumann algebra `N(G)`.

The computation is `hcoord i ∘ X ∘ hinclude j ∘ ρ g = hcoord i ∘ X ∘ diagOp g ∘ hinclude j`
(by `diagOp_hinclude`) `= hcoord i ∘ diagOp g ∘ X ∘ hinclude j` (by equivariance)
`= ρ g ∘ hcoord i ∘ X ∘ hinclude j` (by `hcoord_diagOp`). -/
theorem equivariant_entry_mem {m n : ℕ}
    (X : HSum (G := G) m →L[ℂ] HSum (G := G) n) (hX : Equivariant (G := G) X)
    (i : Fin n) (j : Fin m) :
    ((hcoord (G := G) n i).comp (X.comp (hinclude (G := G) m j)))
      ∈ Work.ORVonNeumann.groupVonNeumann G := by
  rw [Work.ORVonNeumann.mem_groupVonNeumann_iff]
  intro g
  rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.mul_def]
  change ((hcoord (G := G) n i).comp (X.comp (hinclude (G := G) m j))).comp (rightRegOp g)
      = (rightRegOp g).comp ((hcoord (G := G) n i).comp (X.comp (hinclude (G := G) m j)))
  calc ((hcoord (G := G) n i).comp (X.comp (hinclude (G := G) m j))).comp (rightRegOp g)
      = (hcoord (G := G) n i).comp ((X.comp (hinclude (G := G) m j)).comp (rightRegOp g)) :=
        ContinuousLinearMap.comp_assoc _ _ _
    _ = (hcoord (G := G) n i).comp
          (X.comp ((hinclude (G := G) m j).comp (rightRegOp g))) := by
        rw [ContinuousLinearMap.comp_assoc]
    _ = (hcoord (G := G) n i).comp
          (X.comp ((diagOp (G := G) m g).comp (hinclude (G := G) m j))) := by
        rw [← diagOp_hinclude (G := G) m g j]
    _ = (hcoord (G := G) n i).comp
          ((X.comp (diagOp (G := G) m g)).comp (hinclude (G := G) m j)) := by
        rw [ContinuousLinearMap.comp_assoc]
    _ = (hcoord (G := G) n i).comp
          (((diagOp (G := G) n g).comp X).comp (hinclude (G := G) m j)) := by
        rw [hX g]
    _ = (hcoord (G := G) n i).comp
          ((diagOp (G := G) n g).comp (X.comp (hinclude (G := G) m j))) := by
        rw [ContinuousLinearMap.comp_assoc]
    _ = ((hcoord (G := G) n i).comp (diagOp (G := G) n g)).comp
          (X.comp (hinclude (G := G) m j)) :=
        (ContinuousLinearMap.comp_assoc _ _ _).symm
    _ = ((rightRegOp g).comp (hcoord (G := G) n i)).comp
          (X.comp (hinclude (G := G) m j)) := by
        rw [hcoord_diagOp (G := G) n g i]
    _ = (rightRegOp g).comp
          ((hcoord (G := G) n i).comp (X.comp (hinclude (G := G) m j))) :=
        ContinuousLinearMap.comp_assoc _ _ _

/-- **The matrix of an equivariant operator.**  For an equivariant
`X : ⊕_{j : Fin m} ℓ²(G) → ⊕_{i : Fin n} ℓ²(G)`, the entry `(i, j)` is the composition
`hcoord i ∘ X ∘ hinclude j`, an element of the group von Neumann algebra `N(G)`
(`equivariant_entry_mem`). -/
noncomputable def matOfEquiv {m n : ℕ} (X : HSum (G := G) m →L[ℂ] HSum (G := G) n)
    (hX : Equivariant (G := G) X) :
    Matrix (Fin n) (Fin m) (↥(Work.ORVonNeumann.groupVonNeumann G)) :=
  fun i j =>
    ⟨(hcoord (G := G) n i).comp (X.comp (hinclude (G := G) m j)),
      equivariant_entry_mem X hX i j⟩

@[simp]
theorem matOfEquiv_apply {m n : ℕ} (X : HSum (G := G) m →L[ℂ] HSum (G := G) n)
    (hX : Equivariant (G := G) X) (i : Fin n) (j : Fin m) :
    (((matOfEquiv X hX) i j : ↥(Work.ORVonNeumann.groupVonNeumann G)) : boundedEnd G)
      = (hcoord (G := G) n i).comp (X.comp (hinclude (G := G) m j)) := rfl

/-- The coordinate projections and inclusions of `HSum n` form a resolution of the identity:
`∑ i, hinclude i ∘ hcoord i = 1`. -/
theorem sum_hinclude_hcoord (n : ℕ) :
    (∑ i : Fin n, (hinclude (G := G) n i).comp (hcoord (G := G) n i)) = 1 := by
  apply ContinuousLinearMap.ext
  intro x
  apply hsum_ext
  intro k
  rw [ContinuousLinearMap.sum_apply, map_sum]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply]
  rw [Finset.sum_eq_single k
    (fun j _ hj => by rw [hcoord_hinclude, if_neg (Ne.symm hj)])
    (fun h => absurd (Finset.mem_univ k) h)]
  simp [hcoord_hinclude]

/-- Pointwise form of `sum_hinclude_hcoord`: `∑ i, hinclude i (hcoord i x) = x`. -/
theorem sum_hinclude_hcoord_apply (n : ℕ) (x : HSum (G := G) n) :
    ∑ i : Fin n, hinclude (G := G) n i (hcoord (G := G) n i x) = x := by
  have h := congrArg (fun f : HSum (G := G) n →L[ℂ] HSum (G := G) n => f x)
    (sum_hinclude_hcoord (G := G) n)
  simpa using h

/-- **Every equivariant operator is the matrix operator of its matrix**:
`matOp (matOfEquiv X hX) = X`. -/
theorem matOp_matOfEquiv {m n : ℕ} (X : HSum (G := G) m →L[ℂ] HSum (G := G) n)
    (hX : Equivariant (G := G) X) :
    matOp (G := G) (matOfEquiv X hX) = X := by
  apply ContinuousLinearMap.ext
  intro x
  apply hsum_ext
  intro i
  rw [hcoord_matOp_apply]
  simp only [matOfEquiv, ContinuousLinearMap.comp_apply]
  rw [← map_sum, ← map_sum, sum_hinclude_hcoord_apply]

theorem vnCyclicTrace {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableMul G] {m n : ℕ} (X : Work.ORVonNeumann.Rep.HSum (G := G) m →L[ℂ] Work.ORVonNeumann.Rep.HSum (G := G) n) (Y : Work.ORVonNeumann.Rep.HSum (G := G) n →L[ℂ] Work.ORVonNeumann.Rep.HSum (G := G) m) (hX : Work.ORVonNeumann.Rep.Equivariant (G := G) X) (hY : Work.ORVonNeumann.Rep.Equivariant (G := G) Y) : (∑ i : Fin n, inner ℂ (Work.ORVonNeumann.Rep.hdelta (G := G) n i) (X (Y (Work.ORVonNeumann.Rep.hdelta (G := G) n i)))) = ∑ j : Fin m, inner ℂ (Work.ORVonNeumann.Rep.hdelta (G := G) m j) (Y (X (Work.ORVonNeumann.Rep.hdelta (G := G) m j))) := by
  -- Rewrite both sides as the amplified trace of the corresponding matrix product.
  have hL : (∑ i : Fin n, inner ℂ (hdelta (G := G) n i) (X (Y (hdelta (G := G) n i))))
      = mTrace (G := G) n (matOfEquiv X hX * matOfEquiv Y hY) := by
    rw [mTrace_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hcoe : matOp (G := G) (matOfEquiv X hX * matOfEquiv Y hY) (hdelta (G := G) n i)
        = X (Y (hdelta (G := G) n i)) := by
      rw [vnMatOpMul, ContinuousLinearMap.comp_apply, matOp_matOfEquiv, matOp_matOfEquiv]
    rw [← hcoe]
    exact vnInnerHdelta (G := G) (matOfEquiv X hX * matOfEquiv Y hY) i
  have hR : (∑ j : Fin m, inner ℂ (hdelta (G := G) m j) (Y (X (hdelta (G := G) m j))))
      = mTrace (G := G) m (matOfEquiv Y hY * matOfEquiv X hX) := by
    rw [mTrace_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hcoe : matOp (G := G) (matOfEquiv Y hY * matOfEquiv X hX) (hdelta (G := G) m j)
        = Y (X (hdelta (G := G) m j)) := by
      rw [vnMatOpMul, ContinuousLinearMap.comp_apply, matOp_matOfEquiv, matOp_matOfEquiv]
    rw [← hcoe]
    exact vnInnerHdelta (G := G) (matOfEquiv Y hY * matOfEquiv X hX) j
  rw [hL, hR]
  exact (vnMTraceTracial (G := G) (matOfEquiv Y hY) (matOfEquiv X hX)).symm

end Work.ORVonNeumann.Rep
