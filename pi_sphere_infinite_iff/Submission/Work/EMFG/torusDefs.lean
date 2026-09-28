import Mathlib
import Submission.Work.PiS.Interfaces
import Submission.Work.ThomBordism.finiteGoodCoverHomology

set_option synthInstance.maxHeartbeats 400000

/-!
# EMFG — the torus `(S¹)^r` as a `K(ℤ^r, 1)`: definitions

`Work.EMFG.torusFGandEM` proves that `Fin r → Sph 1` (the `r`-torus, `S¹ = Work.Serre.Sph 1`) has
finitely generated integral homology and is a range model of `K(ℤ^r, 1)`.

This file collects the purely definitional ingredients:

* `Plane` — the ambient plane `ℝ²` in which `Sph 1` lives;
* `circleVec` — four vectors of `ℝ²` (namely `±e₀`, `±e₁`) whose positivity half-planes cover the
  circle;
* `circlePatch j` — the open piece `{x ∈ S¹ | ⟪x, circleVec j⟫ > 0}` of the circle; the four of them
  form a *good* cover of `S¹` (every nonempty finite intersection is an open convex cone intersected
  with `S¹`, hence contractible);
* `torusPatch r η` — the product piece `{f : Fin r → S¹ | ∀ i, f i ∈ circlePatch (η i)}`; as `η`
  ranges over `Fin r → Fin 4` these form a good cover of the `r`-torus.
-/

set_option autoImplicit false

namespace Work.EMFG

noncomputable section

/-- The plane `ℝ²` in which `S¹ = Work.Serre.Sph 1` lives. -/
abbrev Plane : Type := EuclideanSpace ℝ (Fin 2)

/-- Four vectors of the plane: `e₀`, `-e₀`, `e₁`, `-e₁`.  Their positivity half-planes cover the
circle, since a unit vector cannot be orthogonal to both `e₀` and `e₁`. -/
def circleVec : Fin 4 → Plane :=
  ![EuclideanSpace.single 0 (1 : ℝ), -EuclideanSpace.single 0 (1 : ℝ),
    EuclideanSpace.single 1 (1 : ℝ), -EuclideanSpace.single 1 (1 : ℝ)]

@[simp] theorem circleVec_zero : circleVec 0 = EuclideanSpace.single 0 (1 : ℝ) := rfl
@[simp] theorem circleVec_one : circleVec 1 = -EuclideanSpace.single 0 (1 : ℝ) := rfl
@[simp] theorem circleVec_two : circleVec 2 = EuclideanSpace.single 1 (1 : ℝ) := rfl
@[simp] theorem circleVec_three : circleVec 3 = -EuclideanSpace.single 1 (1 : ℝ) := rfl

/-- The open piece `{x ∈ S¹ | ⟪x, circleVec j⟫ > 0}` of the circle. -/
def circlePatch (j : Fin 4) : Set (Work.Serre.Sph 1) :=
  {x | 0 < inner ℝ (x : Plane) (circleVec j)}

@[simp] theorem mem_circlePatch {j : Fin 4} {x : Work.Serre.Sph 1} :
    x ∈ circlePatch j ↔ 0 < inner ℝ (x : Plane) (circleVec j) := Iff.rfl

/-- The product piece of the `r`-torus attached to `η : Fin r → Fin 4`: the functions whose `i`-th
value lies in `circlePatch (η i)`. -/
def torusPatch (r : ℕ) (η : Fin r → Fin 4) : Set (Fin r → Work.Serre.Sph 1) :=
  Set.pi Set.univ (fun i => circlePatch (η i))

theorem mem_torusPatch {r : ℕ} {η : Fin r → Fin 4} {f : Fin r → Work.Serre.Sph 1} :
    f ∈ torusPatch r η ↔ ∀ i, f i ∈ circlePatch (η i) := by
  simp [torusPatch]

end

end Work.EMFG
