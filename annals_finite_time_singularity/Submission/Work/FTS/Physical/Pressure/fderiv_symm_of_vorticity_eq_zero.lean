/-
# `Work.FTS.Physical.Pressure.fderiv_symm_of_vorticity_eq_zero`

A vanishing vorticity at a point forces the Fréchet derivative there to be **self-adjoint**: the
antisymmetric part of `DF(x)` is exactly the curl of `F` at `x`, so `(∇×F)(x) = 0` says precisely
that `DF(x)` is symmetric.

The argument is purely finite-dimensional linear algebra on `ℝ³ = EuclideanSpace ℝ (Fin 3)`:

* in the standard basis `e i = WithLp.toLp 2 (Pi.single i 1)`, the matrix of `L := DF(x)` is
  `M i j = (L (e i)) j`, and the three coordinates of `∇×F(x)` are
  `M 1 2 - M 2 1`, `M 2 0 - M 0 2`, `M 0 1 - M 1 0`;
* `∇×F(x) = 0` therefore gives `M i j = M j i` on every off-diagonal pair;
* a linear map whose matrix is symmetric is self-adjoint, i.e.
  `⟪L u, v⟫ = ⟪L v, u⟫` for all `u v`.
-/
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.BinaryProducts
import Mathlib.LinearAlgebra.CrossProduct
import Submission.Work.FTS.Physical.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false

namespace Work.FTS.Physical.Pressure

open FiniteTimeSingularity
open scoped Matrix

local notation "𝔼" => EuclideanSpace ℝ (Fin 3)

/-! ## Auxiliary basis and linear-algebra facts -/

/-- The inner product on `ℝ³` in coordinates: `⟪x, y⟫ = ∑ k, y k * x k`. -/
private lemma inner_eq_sum (x y : 𝔼) : inner ℝ x y = ∑ k : Fin 3, y k * x k := by
  simp [PiLp.inner_apply]

/-- Coordinates of `L u`, expanded in the standard basis: `(L u) k = ∑ i, u i * (L (e i)) k`. -/
private lemma coe_apply_sum (L : 𝔼 →L[ℝ] 𝔼) (u : 𝔼) (k : Fin 3) :
    (L u) k = ∑ i : Fin 3, u i * (L (e i)) k := by
  have hu : u = ∑ i : Fin 3, u i • e i := by
    conv_lhs => rw [← Module.Basis.sum_repr (PiLp.basisFun 2 ℝ (Fin 3)) u]
    simp [PiLp.basisFun_apply, e, PiLp.toLp_single]
  conv_lhs => rw [hu]
  rw [map_sum]
  simp only [map_smul]
  simp [Finset.sum_apply, Pi.smul_apply]

/-- **A linear map with symmetric matrix is self-adjoint.**  If the matrix
`M i j = (L (e i)) j` of `L` in the standard basis is symmetric, then `⟪L u, v⟫ = ⟪L v, u⟫`. -/
private theorem inner_eq_inner_of_symm (L : 𝔼 →L[ℝ] 𝔼)
    (hsym : ∀ i j : Fin 3, (L (e i)) j = (L (e j)) i) (u v : 𝔼) :
    inner ℝ (L u) v = inner ℝ (L v) u := by
  rw [inner_eq_sum, inner_eq_sum]
  simp only [coe_apply_sum L u, coe_apply_sum L v, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [hsym a b]
  ring

/-! ## The coordinates of the curl

The definition of `vorticity` is `∑ i, e i × (L (e i))`; in the standard basis its three
coordinates are the classical curl components. -/

/-- First coordinate: `(∇×F)₀ = ∂₁F₂ - ∂₂F₁`. -/
private lemma vorticity_zero (F : 𝔼 → 𝔼) (x : 𝔼) :
    (vorticity F x) 0 = (fderiv ℝ F x (e 1)) 2 - (fderiv ℝ F x (e 2)) 1 := by
  show (vorticity F x).ofLp 0 = _
  rw [show (vorticity F x).ofLp
        = ∑ i : Fin 3, ((e i : Fin 3 → ℝ) ⨯₃ (fderiv ℝ F x (e i) : Fin 3 → ℝ)) from rfl,
      Fin.sum_univ_three]
  simp only [cross_apply, e, WithLp.ofLp_toLp]
  norm_num [PiLp.single_apply]
  ring

/-- Second coordinate: `(∇×F)₁ = ∂₂F₀ - ∂₀F₂`. -/
private lemma vorticity_one (F : 𝔼 → 𝔼) (x : 𝔼) :
    (vorticity F x) 1 = (fderiv ℝ F x (e 2)) 0 - (fderiv ℝ F x (e 0)) 2 := by
  show (vorticity F x).ofLp 1 = _
  rw [show (vorticity F x).ofLp
        = ∑ i : Fin 3, ((e i : Fin 3 → ℝ) ⨯₃ (fderiv ℝ F x (e i) : Fin 3 → ℝ)) from rfl,
      Fin.sum_univ_three]
  simp only [cross_apply, e, WithLp.ofLp_toLp]
  norm_num [PiLp.single_apply]
  ring

/-- Third coordinate: `(∇×F)₂ = ∂₀F₁ - ∂₁F₀`. -/
private lemma vorticity_two (F : 𝔼 → 𝔼) (x : 𝔼) :
    (vorticity F x) 2 = (fderiv ℝ F x (e 0)) 1 - (fderiv ℝ F x (e 1)) 0 := by
  show (vorticity F x).ofLp 2 = _
  rw [show (vorticity F x).ofLp
        = ∑ i : Fin 3, ((e i : Fin 3 → ℝ) ⨯₃ (fderiv ℝ F x (e i) : Fin 3 → ℝ)) from rfl,
      Fin.sum_univ_three]
  simp only [cross_apply, e, WithLp.ofLp_toLp]
  norm_num [PiLp.single_apply]
  ring

/-- **The vanishing of the curl makes the matrix of `DF(x)` symmetric.** -/
private lemma symm_of_vorticity_eq_zero {F : 𝔼 → 𝔼} {x : 𝔼} (h : vorticity F x = 0) :
    ∀ i j : Fin 3, (fderiv ℝ F x (e i)) j = (fderiv ℝ F x (e j)) i := by
  have hz0 : (fderiv ℝ F x (e 1)) 2 - (fderiv ℝ F x (e 2)) 1 = 0 := by
    have := congrArg (fun w : 𝔼 => w.ofLp 0) h
    simpa [vorticity_zero F x, Pi.zero_apply] using this
  have hz1 : (fderiv ℝ F x (e 2)) 0 - (fderiv ℝ F x (e 0)) 2 = 0 := by
    have := congrArg (fun w : 𝔼 => w.ofLp 1) h
    simpa [vorticity_one F x, Pi.zero_apply] using this
  have hz2 : (fderiv ℝ F x (e 0)) 1 - (fderiv ℝ F x (e 1)) 0 = 0 := by
    have := congrArg (fun w : 𝔼 => w.ofLp 2) h
    simpa [vorticity_two F x, Pi.zero_apply] using this
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all <;> linarith

/-! ## The target lemma -/

theorem fderiv_symm_of_vorticity_eq_zero {F : Work.FTS.Physical.R3 → Work.FTS.Physical.R3}
    {x : Work.FTS.Physical.R3} (h : FiniteTimeSingularity.vorticity F x = 0) :
    ∀ u v : Work.FTS.Physical.R3,
      inner ℝ (fderiv ℝ F x u) v = inner ℝ (fderiv ℝ F x v) u := by
  intro u v
  exact inner_eq_inner_of_symm (fderiv ℝ F x) (symm_of_vorticity_eq_zero h) u v

end Work.FTS.Physical.Pressure
