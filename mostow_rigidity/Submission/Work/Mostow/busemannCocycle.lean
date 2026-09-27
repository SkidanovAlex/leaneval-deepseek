import Mathlib
import Submission.Work.Mostow.poAux
import Submission.Work.Mostow.Hyper
import Submission.Work.Mostow.BaryBase

/-!
# The Busemann cocycle identity

For `ξ` on the boundary sphere `Sph n` and `g : PO n 1`, the Busemann function normalised at the
base point `0` satisfies the cocycle identity

`busemann (bd g ξ) (g • u) = busemann ξ u + busemann (bd g ξ) (g • 0)`.

The proof is the explicit hyperboloid computation: with `θ η = (η,1)` the null lift of a boundary
point and `hlift u` the lift of a chart point, one has
`busemann η u = log (-⟨hlift u, θ η⟩)`, and `mat (rep g) *ᵥ θ ξ` is a positive multiple of
`θ (bd g ξ)` while `hlift (g • u)` is the Minkowski isometry `tsign (rep g) • mat (rep g)` applied
to `hlift u`.  Hence the argument of the logarithm is scaled by a constant depending only on
`(g, ξ)`, which is exactly the cocycle identity.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

variable {n : ℕ}

/-! ### Minkowski calculus -/

/-- The Minkowski pairing of a chart point with the null lift of a boundary point. -/
private lemma mform_hlift_theta (ξ u : E n) : mform (hlift u) (theta ξ) = inner ℝ u ξ - tpart u := by
  rw [mform_apply, inner_eq_sum]
  simp only [hlift_inl, theta_inl, hlift_inr, theta_inr, mul_one]

/-- `mform` is linear in its first variable. -/
private lemma mform_smul_left (c : ℝ) (x z : Fin n ⊕ Fin 1 → ℝ) : mform (c • x) z = c * mform x z := by
  simp only [mform, smul_dotProduct, smul_eq_mul]

/-- `mform` is linear in its second variable. -/
private lemma mform_smul_right (x : Fin n ⊕ Fin 1 → ℝ) (c : ℝ) (z : Fin n ⊕ Fin 1 → ℝ) :
    mform x (c • z) = c * mform x z := by
  simp only [mform, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

/-- `tpart u - ⟪u,η⟫` is minus the Minkowski pairing of `hlift u` with `θ η = (η,1)`. -/
private lemma tpart_sub_inner_eq_neg_mform (η u : E n) :
    tpart u - inner ℝ u η = - mform (hlift u) (theta η) := by
  rw [mform_hlift_theta]; ring

/-! ### The boundary action in homogeneous coordinates -/

/-- The time coordinate of the null vector `mat (rep g) *ᵥ θ ξ`. -/
noncomputable def bdt (g : PO n 1) (ξ : E n) : ℝ := ((mat (rep g)).mulVec (theta ξ)) (Sum.inr 0)

/-- The time coordinate of `mat (rep g) *ᵥ θ ξ` does not vanish on the boundary sphere. -/
lemma bdt_ne_zero (g : PO n 1) (ξ : E n) (hξ : ξ ∈ Sph n) : bdt g ξ ≠ 0 :=
  mat_mulVec_theta_ne_zero (rep g) hξ

/-- The null lift `θ (bd g ξ) = (bd g ξ, 1)` is the renormalisation of `mat (rep g) *ᵥ θ ξ`. -/
lemma theta_bd_smul (g : PO n 1) (ξ : E n) (hξ : ξ ∈ Sph n) :
    theta (bd g ξ) = (bdt g ξ)⁻¹ • ((mat (rep g)).mulVec (theta ξ)) := by
  have hm0 : bdt g ξ ≠ 0 := bdt_ne_zero g ξ hξ
  have hsm : (mat (rep g)).mulVec (theta ξ) = bdt g ξ • theta (bd g ξ) := by
    have h := smul_theta_of_time_ne_zero ((mat (rep g)).mulVec (theta ξ)) hm0
    rwa [show WithLp.toLp 2 (fun i : Fin n =>
        ((mat (rep g)).mulVec (theta ξ)) (Sum.inl i) /
        ((mat (rep g)).mulVec (theta ξ)) (Sum.inr 0)) = bd g ξ from rfl] at h
  calc theta (bd g ξ) = (bdt g ξ)⁻¹ • (bdt g ξ • theta (bd g ξ)) :=
        (inv_smul_smul₀ hm0 (theta (bd g ξ))).symm
    _ = (bdt g ξ)⁻¹ • ((mat (rep g)).mulVec (theta ξ)) := by rw [← hsm]

/-- The argument of the logarithm defining `busemann (bd g ξ) (g • v)` is the one defining
`busemann ξ v`, scaled by the constant `tsign (rep g) * (bdt g ξ)⁻¹`. -/
lemma arg_bd_smul (g : PO n 1) (ξ v : E n) (hξ : ξ ∈ Sph n) :
    tpart (g • v) - inner ℝ (g • v) (bd g ξ)
      = (tpart v - inner ℝ v ξ) * (tsign (rep g) * (bdt g ξ)⁻¹) := by
  rw [tpart_sub_inner_eq_neg_mform (bd g ξ) (g • v), theta_bd_smul g ξ hξ, mform_smul_right,
    show hlift (g • v) = tsign (rep g) • ((mat (rep g)).mulVec (hlift v)) from
      Hyper.hlift_actO (rep g) v,
    mform_smul_left, mform_mat_mulVec, mform_hlift_theta]
  ring

/-! ### The cocycle identity -/

theorem busemannCocycle (n : ℕ) (hA : POActionProp n) (g : PO n 1) (ξ u : E n) (hξ : ξ ∈ Sph n) :
    busemann (bd g ξ) (g • u) = busemann ξ u + busemann (bd g ξ) (g • 0) := by
  have hbd : bd g ξ ∈ Sph n := hA.2.2.2.2.2.2.2.1 g ξ hξ
  have hB : 0 < tpart u - inner ℝ u ξ := busemann_arg_pos ξ hξ u
  have hL : Real.exp (busemann (bd g ξ) (g • u))
      = (tpart u - inner ℝ u ξ) * (tsign (rep g) * (bdt g ξ)⁻¹) := by
    rw [busemann_eq_log, Real.exp_log (busemann_arg_pos (bd g ξ) hbd (g • u)),
      arg_bd_smul g ξ u hξ]
  have hR : Real.exp (busemann (bd g ξ) (g • 0)) = tsign (rep g) * (bdt g ξ)⁻¹ := by
    rw [busemann_eq_log, Real.exp_log (busemann_arg_pos (bd g ξ) hbd (g • 0)),
      arg_bd_smul g ξ 0 hξ, tpart_zero, inner_zero_left, sub_zero, one_mul]
  have hE : Real.exp (busemann ξ u) = tpart u - inner ℝ u ξ := Real.exp_log hB
  refine Real.exp_injective ?_
  rw [Real.exp_add, hL, hR, ← hE]

end Work.Mostow
