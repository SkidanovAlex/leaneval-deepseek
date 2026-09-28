import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.GonLib

/-!
# The half-open unit cube in coefficient space

For `Φ : LatMap (ι := ι) R`, i.e. an injective `ℝ`-linear map `(Fin R → ℝ) →ₗ[ℝ] EuclideanSpace ℝ ι`,
the coefficient space `Fin R → ℝ` carries the standard lattice `ℤ^R`, whose fundamental domain is
the half-open cube `[-1/2, 1/2)^R` (rounding to the nearest lattice point).  These definitions are
used to compare the lattice point count `latCount Φ T` with the Lebesgue volume of the
"`Φ`-ball" `{x | ‖Φ x‖ ≤ T ± μ}`.
-/

set_option autoImplicit false

noncomputable section

namespace Work.HP.MDEstimates

open MeasureTheory

/-- The half-open unit cube `[-1/2, 1/2)^R` in coefficient space, the fundamental domain of the
standard lattice `ℤ^R` acting on `Fin R → ℝ`. -/
def halfCube (R : ℕ) : Set (Fin R → ℝ) := Set.univ.pi fun _ : Fin R => Set.Ico (-(1/2) : ℝ) (1/2)

/-- An integer vector, viewed as a real vector. -/
def toRealVec {R : ℕ} (z : Fin R → ℤ) : Fin R → ℝ := fun i => (z i : ℝ)

/-- The half-open cube `[-1/2, 1/2)^R` translated to the lattice point `z`. -/
def cubeAtZ {R : ℕ} (z : Fin R → ℤ) : Set (Fin R → ℝ) :=
  (fun x => x - toRealVec z) ⁻¹' halfCube R

variable {R : ℕ}

lemma mem_halfCube_iff {y : Fin R → ℝ} :
    y ∈ halfCube R ↔ ∀ i, -(1/2) ≤ y i ∧ y i < 1/2 := by
  simp [halfCube]

lemma mem_cubeAtZ_iff {z : Fin R → ℤ} {x : Fin R → ℝ} :
    x ∈ cubeAtZ z ↔ x - toRealVec z ∈ halfCube R := Iff.rfl

end Work.HP.MDEstimates
