import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Spaces.Gamma_WlInf
import Submission.Work.Construction.L12_Fstar_eq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The weighted `z`-derivative bound for `(z,θ) ↦ c2m θ · 2α/(1+z)`

T. M. Elgindi, *Finite-time singularity formation for `C^{1,α}` solutions to the
incompressible Euler equations on `ℝ³`*, Annals of Math. **194** (2021).

The multiplier `c2m θ = cos(2θ) - sin² θ` (`Work.Construction.c2m`) of the transport term
is applied to the rational function `2α/(1+z)`.  This file proves the elementary weighted
estimate

`|(z+1)^k ∂_z^k (c2m θ · 2α/(1+z))(z)| ≤ 4 α k!`   for `z ≥ 0`, `0 < α ≤ 1`, `k ≤ 4`,

i.e. `Work.FTS.Nonlinear.FstarPkg.c2mInv_points`.  It is the `𝒲^{k,∞}`-input (the constant
of `Spaces.Jk`/`WlInf`) for the `c2m θ · 2α/(1+z)` factor appearing in the linearized
equations of §Modulation.

The proof is the same shape as `Work.Spaces.pzIter_hKer_bound` (which treats
`z/(1+z)²`): compute the `k`-th derivative in closed form.  Here the function is even
simpler; writing `B(z) = 2α/(1+z) = 2α·(1+z)⁻¹`, a direct induction gives

`deriv^[k] B z = (-1)^k k! · 2α · (1+z)^{-(k+1)}`  for `z > -1`,

whence

`(z+1)^k deriv^[k] B z = (-1)^k k! · 2α · (1+z)⁻¹`,

and `|c2m θ| ≤ 2`, `(1+z)⁻¹ ≤ 1` for `z ≥ 0` give the stated `4 α k!`.
-/

noncomputable section

open scoped Real Topology
open Filter

namespace Work.FTS.Nonlinear.FstarPkg

set_option autoImplicit false

-- The fixed statement carries the hypotheses `α ≤ 1` and `k ≤ 4`, which the estimate
-- below does not need (it holds for all `α > 0` and all `k`).
set_option linter.unusedVariables false

/-! ## The closed form of the `k`-th derivative of `(1+z)⁻¹` -/

/-- The closed form of the `k`-th derivative of `z ↦ (1+z)⁻¹`:
`(-1)^k k! (1+z)^{-(k+1)}`, written with the powers of `(1+z)⁻¹`. -/
noncomputable def nInvClosed (k : ℕ) (z : ℝ) : ℝ :=
  ((-1) ^ k * (k.factorial : ℝ)) * (((1 + z)⁻¹) ^ (k + 1))

/-- The value of the derivative of the closed form: the derivative of `nInvClosed k` is
`nInvClosed (k+1)` (at every point where `1+z ≠ 0`). -/
lemma nInvClosed_step (k : ℕ) (z : ℝ) :
    ((-1) ^ k * (k.factorial : ℝ)) *
        ((↑(k + 1) : ℝ) * ((1 + z)⁻¹) ^ k * (-(((1 + z)⁻¹) ^ 2)))
      = nInvClosed (k + 1) z := by
  have hsign : (-1 : ℝ) ^ (k + 1) = -(-1) ^ k := by rw [pow_succ]; ring
  have hfact : (((k + 1).factorial : ℝ)) = (↑(k + 1) * ↑k.factorial) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hpow : (↑(k + 1) : ℝ) * ((1 + z)⁻¹) ^ k * (-(((1 + z)⁻¹) ^ 2))
      = -(↑(k + 1) * ((1 + z)⁻¹) ^ (k + 2)) := by
    rw [mul_neg, mul_assoc, ← pow_add]
  unfold nInvClosed
  rw [hsign, hfact, hpow]
  ring

/-- The closed form has the expected derivative. -/
lemma hasDerivAt_nInvClosed (k : ℕ) {z : ℝ} (hz : z ≠ -1) :
    HasDerivAt (nInvClosed k) (nInvClosed (k + 1) z) z := by
  have hz' : (1 + z) ≠ 0 := by intro h; exact hz (by linarith)
  have hv : HasDerivAt (fun t : ℝ => (1 + t)⁻¹) (-((1 + z)⁻¹) ^ 2) z := by
    have hh : HasDerivAt (fun t : ℝ => 1 + t) 1 z := by
      simpa using (hasDerivAt_id z).const_add (1 : ℝ)
    have hv2 := hh.inv hz'
    have hval : -(1 : ℝ) / (1 + z) ^ 2 = -((1 + z)⁻¹) ^ 2 := by
      rw [div_eq_mul_inv, ← inv_pow]; ring
    rwa [hval] at hv2
  have hp := hv.pow (k + 1)
  have hc := hp.const_mul ((-1) ^ k * (k.factorial : ℝ))
  have hfun : (fun y : ℝ => ((-1) ^ k * (k.factorial : ℝ)) *
      ((fun t : ℝ => (1 + t)⁻¹) ^ (k + 1)) y) = nInvClosed k := by
    funext y; simp only [Pi.pow_apply, nInvClosed]
  have hv3 : ((-1) ^ k * (k.factorial : ℝ)) *
      ((↑(k + 1) : ℝ) * (1 + z)⁻¹ ^ (k + 1 - 1) * (-((1 + z)⁻¹) ^ 2))
      = nInvClosed (k + 1) z := by
    rw [show k + 1 - 1 = k by omega]
    exact nInvClosed_step k z
  rw [hfun, hv3] at hc
  exact hc

/-- The `k`-th derivative of `z ↦ (1+z)⁻¹` for `z > -1`. -/
theorem iter_deriv_nInvClosed : ∀ (k : ℕ) (z : ℝ),
    -1 < z → deriv^[k] (fun z : ℝ => (1 + z)⁻¹) z = nInvClosed k z := by
  intro k
  induction k with
  | zero =>
    intro z _
    simp [nInvClosed]
  | succ k ih =>
    intro z hz
    rw [Function.iterate_succ_apply']
    have hev : (deriv^[k] (fun z : ℝ => (1 + z)⁻¹)) =ᶠ[𝓝 z] nInvClosed k := by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with y hy
      exact ih y hy
    rw [hev.deriv_eq]
    exact (hasDerivAt_nInvClosed k (by linarith)).deriv

/-! ## Constants pass through iterated derivatives -/

/-- A constant factor passes through `deriv^[k]` (no differentiability needed). -/
lemma deriv_iter_const_mul (c : ℝ) (f : ℝ → ℝ) (k : ℕ) :
    deriv^[k] (fun z => c * f z) = fun z => c * deriv^[k] f z := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    funext x
    rw [Work.Spaces.deriv_const_mul', Function.iterate_succ_apply']

/-! ## The weighted bound -/

/-- `|(z+1)^k nInvClosed k z| ≤ k!` for `z ≥ 0`: the weight `(z+1)^k` cancels all but
one factor of `(1+z)⁻¹`. -/
lemma nInvClosed_weighted (k : ℕ) (z : ℝ) (hz : 0 ≤ z) :
    |(z + 1) ^ k * nInvClosed k z| ≤ (k.factorial : ℝ) := by
  have hz' : (1 + z) ≠ 0 := by positivity
  have hknn : (0 : ℝ) ≤ (k.factorial : ℝ) := by positivity
  have hpos : (0 : ℝ) < (1 + z)⁻¹ := by positivity
  have hpow : (z + 1) ^ k * ((1 + z)⁻¹) ^ (k + 1) = (1 + z)⁻¹ := by
    rw [pow_add, ← mul_assoc, ← mul_pow, show (z + 1) = (1 + z) by ring,
      mul_inv_cancel₀ hz', one_pow, one_mul, pow_one]
  have hsplit : (z + 1) ^ k * nInvClosed k z
      = ((-1 : ℝ) ^ k * (k.factorial : ℝ)) * ((z + 1) ^ k * ((1 + z)⁻¹) ^ (k + 1)) := by
    unfold nInvClosed; ring
  rw [hsplit, abs_mul, hpow]
  have h1 : |((-1 : ℝ) ^ k * (k.factorial : ℝ))| = (k.factorial : ℝ) := by
    rw [abs_mul, abs_of_nonneg hknn]; simp
  rw [h1, abs_of_nonneg (le_of_lt hpos)]
  exact mul_le_of_le_one_right hknn (inv_le_one_of_one_le₀ (by linarith))

/-! ## The iterated `z`-derivative of `c2m θ · 2α/(1+z)` -/

/-- `∂_z^k` of `(z,θ) ↦ c2m θ · 2α/(1+z)` in closed form (for `z > -1`). -/
lemma pzIter_c2m_inv (α : ℝ) (k : ℕ) (z θ : ℝ) (hz : -1 < z) :
    Work.Spaces.pzIter k (fun z θ => Work.Construction.c2m θ * (2 * α / (1 + z))) z θ
      = Work.Construction.c2m θ * (2 * α * nInvClosed k z) := by
  rw [Work.Spaces.pzIter_decomp k Work.Construction.c2m (fun z => 2 * α / (1 + z)) z θ]
  have hB : deriv^[k] (fun z : ℝ => 2 * α / (1 + z)) z = 2 * α * nInvClosed k z := by
    have h1 : (fun z : ℝ => 2 * α / (1 + z)) = fun z : ℝ => (2 * α) * ((1 + z)⁻¹) := by
      funext z; rw [div_eq_mul_inv]
    rw [h1, congrFun (deriv_iter_const_mul (2 * α) (fun z : ℝ => (1 + z)⁻¹) k) z,
      iter_deriv_nInvClosed k z hz]
  rw [hB]

/-- `|c2m θ| ≤ 2`. -/
lemma abs_c2m_le_two (θ : ℝ) : |Work.Construction.c2m θ| ≤ 2 := by
  rw [Work.Construction.c2m_eq]
  have hstep : |Real.cos (2 * θ) - Real.sin θ ^ 2|
      ≤ |Real.cos (2 * θ)| + |Real.sin θ ^ 2| := by
    have h := abs_sub_le (Real.cos (2 * θ)) (0 : ℝ) (Real.sin θ ^ 2)
    rwa [sub_zero, zero_sub, abs_neg] at h
  have hsin : |Real.sin θ ^ 2| = Real.sin θ ^ 2 := abs_of_nonneg (sq_nonneg _)
  calc |Real.cos (2 * θ) - Real.sin θ ^ 2|
      ≤ |Real.cos (2 * θ)| + |Real.sin θ ^ 2| := hstep
    _ = |Real.cos (2 * θ)| + Real.sin θ ^ 2 := by rw [hsin]
    _ ≤ 1 + 1 := add_le_add (Real.abs_cos_le_one _) (Real.sin_sq_le_one θ)
    _ = 2 := by norm_num

/-- The weighted bound `|(z+1)^k ∂_z^k (c2m θ · 2α/(1+z))(z)| ≤ 4 α k!`.  (The hypotheses
`hα1 : α ≤ 1` and `hk : k ≤ 4` are part of the fixed statement; the estimate is proved
here for all `α > 0` and all `k`.) -/
theorem c2mInv_points (α z θ : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hz : 0 ≤ z)
    (k : ℕ) (hk : k ≤ 4) :
    |(z + 1) ^ k * Work.Spaces.pzIter k
        (fun z θ => Work.Construction.c2m θ * (2 * α / (1 + z))) z θ|
      ≤ 4 * α * (k.factorial : ℝ) := by
  have hz1 : -1 < z := by linarith
  have hα2 : (0 : ℝ) ≤ 2 * α := by linarith
  have hc2m : |Work.Construction.c2m θ| ≤ 2 := abs_c2m_le_two θ
  rw [pzIter_c2m_inv α k z θ hz1]
  rw [show (z + 1) ^ k * (Work.Construction.c2m θ * (2 * α * nInvClosed k z))
        = Work.Construction.c2m θ * (2 * α * ((z + 1) ^ k * nInvClosed k z)) by ring]
  rw [abs_mul, abs_mul, abs_of_nonneg hα2]
  calc |Work.Construction.c2m θ| * (2 * α * |(z + 1) ^ k * nInvClosed k z|)
      ≤ 2 * (2 * α * (k.factorial : ℝ)) := by
        apply mul_le_mul hc2m (mul_le_mul_of_nonneg_left (nInvClosed_weighted k z hz) hα2)
          (mul_nonneg hα2 (abs_nonneg _)) (by norm_num)
    _ = 4 * α * (k.factorial : ℝ) := by ring

end Work.FTS.Nonlinear.FstarPkg
