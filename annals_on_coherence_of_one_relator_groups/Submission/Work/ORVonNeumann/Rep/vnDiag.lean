/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ORVonNeumann area (N5 of the one-relator coherence project)

# The block diagonal right regular action and equivariant operators

The von Neumann algebra `N(G) = ρ(G)'` consists of the bounded operators on `ℓ²(G)` commuting
with the right regular representation `ρ`.  On the finite direct sum
`HSum n = ⊕_{i : Fin n} ℓ²(G)` the corresponding structure is the block diagonal action
`diagOp n g = ⊕_{i : Fin n} ρ g`, and an operator `Z : HSum m → HSum n` is *equivariant* if it
commutes with `diagOp`; these are exactly the "matrices over `N(G)`".  The operators `matOp X`
are equivariant, and equivariance is preserved by sums, composition, adjoints and inversion.

This is the setting in which the "cyclic trace"
`∑ i, ⟪δ i, (X ∘ Y) (δ i)⟫ = ∑ j, ⟪δ j, (Y ∘ X) (δ j)⟫`
holds for equivariant `X, Y` (it is the amplification of the traciality of `τ`), which is the
key algebraic input to the identification of the dimension of the range of a matrix operator
with that of its adjoint.
-/
import Mathlib
import Submission.Work.ORVonNeumann.Rep.vnCore

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped InnerProductSpace InnerProduct

namespace Work.ORVonNeumann.Rep

universe u

variable {G : Type u} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [MeasurableMul G]

/-- **The block diagonal action of the right regular representation on `HSum n`**:
`diagOp n g = ⊕_{i : Fin n} ρ g`.  It is a unitary of `HSum n`. -/
noncomputable def diagOp (n : ℕ) (g : G) : HSum (G := G) n →L[ℂ] HSum (G := G) n :=
  ∑ i : Fin n, (hinclude (G := G) n i).comp
    ((rightRegOp g).comp (hcoord (G := G) n i))

@[simp]
theorem diagOp_apply (n : ℕ) (g : G) (x : HSum (G := G) n) :
    diagOp (G := G) n g x
      = ∑ i : Fin n, hinclude (G := G) n i (rightRegOp g (hcoord (G := G) n i x)) := by
  simp [diagOp]

/-- `diagOp n g` acts coordinatewise by `ρ g`. -/
theorem hcoord_diagOp (n : ℕ) (g : G) (i : Fin n) :
    (hcoord (G := G) n i).comp (diagOp (G := G) n g)
      = (rightRegOp g).comp (hcoord (G := G) n i) := by
  apply ContinuousLinearMap.ext
  intro x
  rw [ContinuousLinearMap.comp_apply, diagOp_apply, map_sum]
  rw [Finset.sum_eq_single i]
  · simp [hcoord_hinclude]
  · intro j _ hj
    simp [hcoord_hinclude, Ne.symm hj]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- Pointwise form of `hcoord_diagOp`. -/
theorem hcoord_diagOp_apply (n : ℕ) (g : G) (i : Fin n) (x : HSum (G := G) n) :
    hcoord (G := G) n i (diagOp (G := G) n g x)
      = rightRegOp g (hcoord (G := G) n i x) :=
  congrArg (fun f : HSum (G := G) n →L[ℂ] l2 G => f x) (hcoord_diagOp (G := G) n g i)

/-- `diagOp n g` sends the `i`-th summand to the `i`-th summand. -/
theorem diagOp_hinclude (n : ℕ) (g : G) (i : Fin n) :
    (diagOp (G := G) n g).comp (hinclude (G := G) n i)
      = (hinclude (G := G) n i).comp (rightRegOp g) := by
  apply ContinuousLinearMap.ext
  intro x
  rw [ContinuousLinearMap.comp_apply, diagOp_apply]
  rw [Finset.sum_eq_single i]
  · simp [hcoord_hinclude]
  · intro j _ hj
    simp [hcoord_hinclude, hj]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- **Equivariance**: an operator `Z : HSum m → HSum n` is equivariant if it commutes with the
block diagonal right regular action.  These operators are exactly the "matrices over `N(G)`". -/
def Equivariant {m n : ℕ} (Z : HSum (G := G) m →L[ℂ] HSum (G := G) n) : Prop :=
  ∀ g : G, Z.comp (diagOp (G := G) m g) = (diagOp (G := G) n g).comp Z

theorem Equivariant.comp {l m n : ℕ} {Y : HSum (G := G) l →L[ℂ] HSum (G := G) m}
    {Z : HSum (G := G) m →L[ℂ] HSum (G := G) n} (hY : Equivariant Y) (hZ : Equivariant Z) :
    Equivariant (Z.comp Y) := by
  intro g
  rw [ContinuousLinearMap.comp_assoc, hY g, ← ContinuousLinearMap.comp_assoc, hZ g,
    ContinuousLinearMap.comp_assoc]

theorem Equivariant.add {m n : ℕ} {Y Z : HSum (G := G) m →L[ℂ] HSum (G := G) n}
    (hY : Equivariant Y) (hZ : Equivariant Z) : Equivariant (Y + Z) := by
  intro g
  rw [ContinuousLinearMap.add_comp, hY g, hZ g, ContinuousLinearMap.comp_add]

theorem Equivariant.sub {m n : ℕ} {Y Z : HSum (G := G) m →L[ℂ] HSum (G := G) n}
    (hY : Equivariant Y) (hZ : Equivariant Z) : Equivariant (Y - Z) := by
  intro g
  rw [ContinuousLinearMap.sub_comp, hY g, hZ g, ContinuousLinearMap.comp_sub]

theorem Equivariant.smul {m n : ℕ} (c : ℂ) {Z : HSum (G := G) m →L[ℂ] HSum (G := G) n}
    (hZ : Equivariant Z) : Equivariant (c • Z) := by
  intro g
  rw [ContinuousLinearMap.smul_comp, hZ g, ContinuousLinearMap.comp_smul]

theorem Equivariant.one (n : ℕ) :
    Equivariant (G := G) (1 : HSum (G := G) n →L[ℂ] HSum (G := G) n) := by
  intro g
  rw [ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id]

end Work.ORVonNeumann.Rep
