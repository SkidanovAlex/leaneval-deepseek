import Mathlib
import Submission.Work.HP.Defs

/-!
# Coefficient-space lattices (support for `Work.HP.gon`)

A rank-`R` lattice in `ℝ^ι` is presented by an injective `ℝ`-linear map
`Φ : (Fin R → ℝ) →ₗ[ℝ] EuclideanSpace ℝ ι`.  The lattice itself is `Φ '' ℤ^R`, and all
counting / successive-minima / covolume data is expressed through the coefficient space
`Fin R → ℤ`.  This file contains the definitions and the elementary theory.
-/

set_option autoImplicit false

noncomputable section

open Finset
open scoped BigOperators

namespace Work.HP

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Coefficient-space presentation of a rank-`R` lattice: an injective linear map. -/
abbrev LatMap (R : ℕ) := (Fin R → ℝ) →ₗ[ℝ] EuclideanSpace ℝ ι

/-- The norm of a coefficient vector inside the lattice. -/
def latNorm {R : ℕ} (Φ : LatMap (ι := ι) R) (x : Fin R → ℝ) : ℝ := ‖Φ x‖

/-- The coefficient vectors of lattice points of norm `≤ T`. -/
def latSet {R : ℕ} (Φ : LatMap (ι := ι) R) (T : ℝ) : Set (Fin R → ℤ) :=
  {t | ‖Φ (fun i => (t i : ℝ))‖ ≤ T}

/-- The number of lattice points of norm `≤ T`. -/
def latCount {R : ℕ} (Φ : LatMap (ι := ι) R) (T : ℝ) : ℕ := (latSet Φ T).ncard

/-- The `i`-th successive minimum of the lattice (with respect to the unit ball of
`EuclideanSpace ℝ ι`). -/
def latMin {R : ℕ} (Φ : LatMap (ι := ι) R) (i : ℕ) : ℝ :=
  sInf {r : ℝ | 0 ≤ r ∧ ∃ f : Fin i → (Fin R → ℤ), LinearIndependent ℤ f ∧
    ∀ j, ‖Φ (fun k => (f j k : ℝ))‖ ≤ r}

/-- The covolume of the lattice, i.e. `√det` of the Gram matrix of the coefficient basis. -/
def latCovol {R : ℕ} (Φ : LatMap (ι := ι) R) : ℝ :=
  Real.sqrt (Matrix.det (Matrix.of (fun i j : Fin R =>
    inner ℝ (Φ (Pi.basisFun ℝ (Fin R) i)) (Φ (Pi.basisFun ℝ (Fin R) j)))))

end Work.HP


namespace Work.HP

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem symm_ofLp (z : ι → ℝ) :
    ((WithLp.linearEquiv 2 ℝ (ι → ℝ)).symm z).ofLp = z := by
  rw [WithLp.linearEquiv_symm_apply]; rfl

/-- The coefficient map attached to a family of integer vectors: `x ↦ Σ i, x i • v i`
(in `EuclideanSpace ℝ ι`). -/
noncomputable def phiOf {R : ℕ} (v : Fin R → (ι → ℤ)) : LatMap (ι := ι) R :=
  (WithLp.linearEquiv 2 ℝ (ι → ℝ)).symm.toLinearMap.comp
    (LinearMap.pi (fun k => ∑ i, ((v i) k : ℝ) • (LinearMap.proj i : (Fin R → ℝ) →ₗ[ℝ] ℝ)))

theorem phiOf_apply {R : ℕ} (v : Fin R → (ι → ℤ)) (x : Fin R → ℝ) (k : ι) :
    (phiOf v x).ofLp k = ∑ i, ((v i) k : ℝ) * x i := by
  simp only [phiOf, LinearEquiv.coe_toLinearMap, LinearMap.comp_apply, symm_ofLp,
    LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul]

theorem sum_smul_apply {R : ℕ} (v : Fin R → (ι → ℤ)) (t : Fin R → ℤ) (k : ι) :
    ((∑ i, t i • v i) k : ℝ) = ∑ i, ((v i) k : ℝ) * (t i : ℝ) := by
  have h : (∑ i, t i • v i : ι → ℤ) k = ∑ i, (t i • v i) k :=
    Finset.sum_apply k Finset.univ (fun i => t i • v i)
  rw [h]
  push_cast
  exact Finset.sum_congr rfl (fun i _ => by simp only [Pi.smul_apply, smul_eq_mul, Int.cast_mul]; ring)

theorem phiOf_cast {R : ℕ} (v : Fin R → (ι → ℤ)) (t : Fin R → ℤ) (k : ι) :
    (phiOf v (fun i => (t i : ℝ))).ofLp k = ((∑ i, t i • v i) k : ℝ) := by
  rw [phiOf_apply, sum_smul_apply]

theorem norm_toLp (w : ι → ℤ) :
    ‖WithLp.toLp 2 (fun k => (w k : ℝ))‖ = eNorm w := by
  rw [eNorm, PiLp.norm_eq_of_L2]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [WithLp.ofLp_toLp, Real.norm_eq_abs, sq_abs]

theorem phiOf_norm {R : ℕ} (v : Fin R → (ι → ℤ)) (t : Fin R → ℤ) :
    ‖phiOf v (fun i => (t i : ℝ))‖ = eNorm (∑ i, t i • v i) := by
  have h : phiOf v (fun i => (t i : ℝ)) = WithLp.toLp 2 (fun k => ((∑ i, t i • v i) k : ℝ)) := by
    rw [← WithLp.toLp_ofLp (p := 2) (phiOf v (fun i => (t i : ℝ)))]
    congr 1
    funext k
    rw [WithLp.ofLp_toLp, phiOf_cast]
  rw [h, norm_toLp]

end Work.HP
