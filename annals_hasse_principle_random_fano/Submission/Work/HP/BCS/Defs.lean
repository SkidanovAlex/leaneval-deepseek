import Mathlib
import Submission.Work.HP.MMDefs

/-!
# Support definitions for `Work.HP.ballConeCount`

This file collects the objects used in the proof of `Work.HP.ballConeCount`
(lattice point counting in a ball intersected with two "cones" `𝒞_v^{(γ)}`).

The cone `𝒞_v^{(γ)} = {t : |⟨v,t⟩| ≤ ‖v‖‖t‖/(2γ)}` is a union of two convex cones; its
boundary is the union of two "cone surfaces" `{|⟨v,t⟩| = c‖t‖}` with `c = ‖v‖/(2γ)`
(unless `c ≥ ‖v‖`, in which case the cone is the whole space).
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory

namespace Work.HP.BCS

variable {k : ℕ}

/-- The cone surface `{|⟪a,x⟫| = c‖x‖}` in `ℝ^k` (a closed homogeneous set). -/
def coneSurf (a : EuclideanSpace ℝ (Fin k)) (c : ℝ) : Set (EuclideanSpace ℝ (Fin k)) :=
  {x | |inner ℝ a x| = c * ‖x‖}

/-- The closed cone `{|⟪a,x⟫| ≤ c‖x‖}` in `ℝ^k`. -/
def coneSet (a : EuclideanSpace ℝ (Fin k)) (c : ℝ) : Set (EuclideanSpace ℝ (Fin k)) :=
  {x | |inner ℝ a x| ≤ c * ‖x‖}

/-- The `r`-neighbourhood of the cone surface `{|⟪a,x⟫| = c‖x‖}`, intersected with the ball of
radius `s`: the boundary layer relevant for lattice point counting in the cone slice. -/
def coneTube (a : EuclideanSpace ℝ (Fin k)) (c s r : ℝ) :
    Set (EuclideanSpace ℝ (Fin k)) :=
  {x | ‖x‖ ≤ s ∧ ∃ y, |inner ℝ a y| = c * ‖y‖ ∧ ‖x - y‖ ≤ r}

/-- The union of the `r`-neighbourhoods of two cone surfaces inside the ball of radius `s`. -/
def coneTube2 (a b : EuclideanSpace ℝ (Fin k)) (c d s r : ℝ) :
    Set (EuclideanSpace ℝ (Fin k)) :=
  {x | ‖x‖ ≤ s ∧ ∃ y, (|inner ℝ a y| = c * ‖y‖ ∨ |inner ℝ b y| = d * ‖y‖) ∧ ‖x - y‖ ≤ r}

/-! ## Lattice counting vocabulary in `ℝ^k` -/

section counting
open scoped Pointwise

/-- The standard `L²`-embedding `ℤ^k → ℝ^k`. -/
def toEk {k : ℕ} (t : Fin k → ℤ) : EuclideanSpace ℝ (Fin k) := WithLp.toLp 2 fun i => (t i : ℝ)

/-- The half-open unit cube `[0,1)^k ⊆ ℝ^k`. -/
def unitCube (k : ℕ) : Set (EuclideanSpace ℝ (Fin k)) :=
  {x | ∀ i, x.ofLp i ∈ Set.Ico (0 : ℝ) 1}

/-- The lattice `Ψ '' ℤ^k`, for `Ψ` a linear map on `ℝ^k`. -/
def latImage {k : ℕ} (Ψ : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k)) :
    Set (EuclideanSpace ℝ (Fin k)) :=
  Ψ '' Set.range (toEk (k := k))

/-- The "cell radius": the radius of the fundamental parallelepiped `Ψ '' [0,1)^k`. -/
def cellRad {k : ℕ} (Ψ : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k)) : ℝ :=
  ∑ i, ‖Ψ (toEk (Pi.single i 1))‖

/-- Erosion of a set by another: `{x | x + B ⊆ K}` (in additive notation). -/
def erode {E : Type*} [Add E] (K B : Set E) : Set E := {x | ∀ b ∈ B, x + b ∈ K}

/-- The `R`-boundary layer of `K`: points that are in `K + B_R` but whose `B_R`-ball is not
contained in `K`. -/
def layer {E : Type*} [NormedAddCommGroup E] (K : Set E) (R : ℝ) : Set E :=
  (K + Metric.ball 0 R) \ erode K (Metric.ball 0 R)

end counting

end Work.HP.BCS
