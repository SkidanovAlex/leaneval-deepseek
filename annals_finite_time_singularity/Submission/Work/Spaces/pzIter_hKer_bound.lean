/-
# The weighted sup-bound `|(z+1)^k ∂_z^k h(z)| ≤ k! (k+1)` for `h(z) = z/(1+z)²`

T. M. Elgindi, *Finite-time singularity formation for `C^{1,α}` solutions to the
incompressible Euler equations on `ℝ³`*, Annals of Math. **194** (2021).

The radial factor `h(z) = z/(1+z)²` is the profile of the fundamental model
(see `Submission/Work/Spaces/GammaW_Prelim.lean`, `hKer`).  This file proves the
elementary weighted bound

  `|(z+1)^k · h^{(k)}(z)| ≤ k! · (k+1)`   for `z ≥ 0`,

needed to control the `W^{l,∞}`-norm of `Γ(θ)·h(z)` (see
`Submission/Work/Spaces/Gamma_WlInf.lean`).

The proof computes the `k`-th derivative in closed form.  Writing

  `h(z) = (1+z)⁻¹ - (1+z)⁻²`,

a direct induction gives

  `h^{(k)}(z) = (-1)^k k! (z-k) (1+z)^{-(k+2)}`,

whence

  `(z+1)^k h^{(k)}(z) = (-1)^k k! (z-k)/(1+z)²`,

and the bound reduces to `|z-k| ≤ (k+1)(1+z)²` for `z ≥ 0`, which follows from
`|z-k| ≤ z+k` and `z+k ≤ (k+1)(1+z)²`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Topology

namespace Work.Spaces

set_option autoImplicit false

/-! ## The closed form of the `k`-th derivative -/

/-- The closed form of the `k`-th derivative of `z ↦ z/(1+z)²`:
`(-1)^k k! (z-k) (1+z)^{-(k+2)}`, written with `(1+z)⁻¹`. -/
noncomputable def hKerClosed (k : ℕ) (z : ℝ) : ℝ :=
  ((-1) ^ k * (k.factorial : ℝ)) * ((z - k) * ((1 + z)⁻¹) ^ (k + 2))

/-- `(1+z)^{-(k+2)} = (1+z)·(1+z)^{-(k+3)}` for `1+z ≠ 0`. -/
lemma hKerClosed_shift (k : ℕ) (z : ℝ) (hz : (1 + z) ≠ 0) :
    ((1 + z)⁻¹) ^ (k + 2) = (1 + z) * ((1 + z)⁻¹) ^ (k + 3) := by
  have hu : (1 + z) * ((1 + z)⁻¹) = 1 := mul_inv_cancel₀ hz
  have h1 : ((1 + z)⁻¹) ^ (k + 3) = ((1 + z)⁻¹) ^ (k + 2) * ((1 + z)⁻¹) := by
    rw [show k + 3 = (k + 2) + 1 by omega, pow_succ]
  rw [h1, mul_comm (((1 + z)⁻¹) ^ (k + 2)) ((1 + z)⁻¹), ← mul_assoc, hu, one_mul]

/-- `(1+z)^{-(k+1)}·(-(1+z)^{-2}) = -(1+z)^{-(k+3)}`. -/
lemma hKerClosed_neg_pow (k : ℕ) (z : ℝ) :
    ((1 + z)⁻¹) ^ (k + 1) * (-(((1 + z)⁻¹) ^ 2)) = -((1 + z)⁻¹) ^ (k + 3) := by
  rw [mul_neg, ← pow_add, show (k + 1) + 2 = k + 3 by omega]

/-- The value of the derivative of the closed form: if
`D_k(z) = (-1)^k k! (z-k)(1+z)^{-(k+2)}` then
`D_k'(z) = D_{k+1}(z) = (-1)^{k+1}(k+1)! (z-(k+1))(1+z)^{-(k+3)}`. -/
lemma hKerClosed_step (k : ℕ) (z : ℝ) (hz : (1 + z) ≠ 0) :
    (-1) ^ k * (k.factorial : ℝ) *
        (1 * ((1 + z)⁻¹) ^ (k + 2)
          + (z - (k : ℝ)) * ((↑(k + 2)) * ((1 + z)⁻¹) ^ (k + 1) * (-(((1 + z)⁻¹) ^ 2))))
      = hKerClosed (k + 1) z := by
  have hsign : (-1 : ℝ) ^ (k + 1) = -(-1) ^ k := by rw [pow_succ]; ring
  have hfact : (((k + 1).factorial : ℝ)) = (↑(k + 1) * ↑k.factorial) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hp2 : (↑(k + 2) : ℝ) * ((1 + z)⁻¹) ^ (k + 1) * (-(((1 + z)⁻¹) ^ 2)) =
      -((↑(k + 2)) * ((1 + z)⁻¹) ^ (k + 3)) := by
    rw [mul_assoc, hKerClosed_neg_pow k z, mul_neg]
  unfold hKerClosed
  rw [hsign, hfact, one_mul, hKerClosed_shift k z hz, hp2]
  push_cast
  ring

/-- The closed form has the expected derivative. -/
lemma hasDerivAt_hKerClosed (k : ℕ) {z : ℝ} (hz : z ≠ -1) :
    HasDerivAt (hKerClosed k) (hKerClosed (k + 1) z) z := by
  have hz' : (1 + z) ≠ 0 := by intro h; apply hz; linarith
  have h1 : HasDerivAt (fun t : ℝ => t - (k : ℝ)) 1 z := by
    simpa using (hasDerivAt_id z).sub_const (k : ℝ)
  have h2 : HasDerivAt (fun t : ℝ => (1 + t)⁻¹) (-((1 + z)⁻¹) ^ 2) z := by
    have hh : HasDerivAt (fun t : ℝ => 1 + t) 1 z := by
      simpa using (hasDerivAt_id z).const_add (1 : ℝ)
    have hv := hh.inv hz'
    have hval : -(1 : ℝ) / (1 + z) ^ 2 = -((1 + z)⁻¹) ^ 2 := by
      rw [div_eq_mul_inv, ← inv_pow]; ring
    rw [hval] at hv
    exact hv
  have hp := h2.pow (k + 2)
  have hmul := h1.mul hp
  have hc := hmul.const_mul ((-1) ^ k * (k.factorial : ℝ))
  have hfun :
      (fun y : ℝ => (-1) ^ k * (k.factorial : ℝ) *
        ((fun t : ℝ => t - (k : ℝ)) * (fun t : ℝ => (1 + t)⁻¹) ^ (k + 2)) y)
        = hKerClosed k := by
    funext y; simp only [hKerClosed, Pi.mul_apply, Pi.pow_apply]
  have hv2 : (-1) ^ k * (k.factorial : ℝ) *
      (1 * ((fun t : ℝ => (1 + t)⁻¹) ^ (k + 2)) z
        + (z - (k : ℝ)) * (↑(k + 2) * (1 + z)⁻¹ ^ (k + 2 - 1) * (-((1 + z)⁻¹) ^ 2)))
      = hKerClosed (k + 1) z := by
    simp only [Pi.pow_apply]
    rw [show k + 2 - 1 = k + 1 by omega]
    exact hKerClosed_step k z hz'
  rw [hfun, hv2] at hc
  exact hc

/-- The `k`-th derivative of `z ↦ z/(1+z)²` for `z > -1`. -/
theorem iter_deriv_hKerClosed : ∀ (k : ℕ) (z : ℝ),
    -1 < z → deriv^[k] (fun z : ℝ => z / (1 + z) ^ 2) z = hKerClosed k z := by
  intro k
  induction k with
  | zero =>
    intro z _
    simp only [Function.iterate_zero, id_eq, hKerClosed, Nat.factorial_zero, Nat.cast_one,
      pow_zero, Nat.cast_zero, sub_zero, inv_pow, div_eq_mul_inv]
    ring
  | succ k ih =>
    intro z hz
    rw [Function.iterate_succ_apply']
    have hev : (deriv^[k] (fun z : ℝ => z / (1 + z) ^ 2)) =ᶠ[𝓝 z] (hKerClosed k) := by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with y hy
      exact ih y hy
    rw [hev.deriv_eq]
    exact (hasDerivAt_hKerClosed k (by linarith)).deriv

/-! ## The weighted bound -/

theorem pzIter_hKer_bound (k : ℕ) (z : ℝ) (hz : 0 ≤ z) :
    |(z + 1) ^ k * deriv^[k] (fun z : ℝ => z / (1 + z) ^ 2) z| ≤ (k.factorial : ℝ) * (k + 1) := by
  have hz1 : -1 < z := by linarith
  rw [iter_deriv_hKerClosed k z hz1]
  have hz' : (1 + z) ≠ 0 := by positivity
  have hUnn : 0 ≤ ((1 + z)⁻¹) ^ 2 := sq_nonneg _
  have hknn : 0 ≤ (k.factorial : ℝ) := by positivity
  have hpow2 : (z + 1) ^ k * ((1 + z)⁻¹) ^ (k + 2) = ((1 + z)⁻¹) ^ 2 := by
    rw [pow_add, ← mul_assoc, ← mul_pow, show (z + 1) = (1 + z) by ring,
      mul_inv_cancel₀ hz', one_pow, one_mul]
  have hval : (z + 1) ^ k * hKerClosed k z
      = ((-1) ^ k * (k.factorial : ℝ)) * ((z - (k : ℝ)) * ((1 + z)⁻¹) ^ 2) := by
    rw [hKerClosed]
    rw [show (z + 1) ^ k * (((-1) ^ k * (k.factorial : ℝ)) *
          ((z - (k : ℝ)) * ((1 + z)⁻¹) ^ (k + 2)))
        = ((-1) ^ k * (k.factorial : ℝ)) *
            ((z - (k : ℝ)) * ((z + 1) ^ k * ((1 + z)⁻¹) ^ (k + 2))) by ring]
    rw [hpow2]
  rw [hval]
  have hmul1 : (1 + z) ^ 2 * ((1 + z)⁻¹) ^ 2 = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hz', one_pow]
  have hkey : |z - (k : ℝ)| ≤ ((k : ℝ) + 1) * (1 + z) ^ 2 := by
    have h1 : |z - (k : ℝ)| ≤ z + (k : ℝ) := by
      rw [abs_sub_le_iff]
      constructor <;> linarith [Nat.cast_nonneg (α := ℝ) k, hz]
    have h2 : z + (k : ℝ) ≤ ((k : ℝ) + 1) * (1 + z) ^ 2 := by
      nlinarith [sq_nonneg z, Nat.cast_nonneg (α := ℝ) k, hz]
    linarith
  have hb : |z - (k : ℝ)| * ((1 + z)⁻¹) ^ 2 ≤ (k : ℝ) + 1 := by
    calc |z - (k : ℝ)| * ((1 + z)⁻¹) ^ 2
        ≤ (((k : ℝ) + 1) * (1 + z) ^ 2) * ((1 + z)⁻¹) ^ 2 :=
          mul_le_mul_of_nonneg_right hkey hUnn
      _ = ((k : ℝ) + 1) * ((1 + z) ^ 2 * ((1 + z)⁻¹) ^ 2) := by ring
      _ = (k : ℝ) + 1 := by rw [hmul1]; ring
  have habs : |((-1) ^ k * (k.factorial : ℝ)) * ((z - (k : ℝ)) * ((1 + z)⁻¹) ^ 2)| =
      (k.factorial : ℝ) * (|z - (k : ℝ)| * ((1 + z)⁻¹) ^ 2) := by
    rw [abs_mul, abs_mul, abs_mul]
    have h1 : |((-1 : ℝ) ^ k)| = 1 := by rw [abs_pow]; norm_num
    rw [h1, abs_of_nonneg hknn, abs_of_nonneg hUnn]
    ring
  rw [habs]
  have := mul_le_mul_of_nonneg_left hb hknn
  simpa [Nat.cast_add, Nat.cast_one] using this

end Work.Spaces
