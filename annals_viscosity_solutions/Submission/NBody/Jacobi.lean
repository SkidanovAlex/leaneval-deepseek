import ChallengeDeps
import Submission.NBody.Virial
import Mathlib

/-!
# The Lagrange–Jacobi identity `I'' = 4E + 2U`

Tenth stone of the analytic layer.  Writing `I(t) = ∑ᵢ mᵢ‖yᵢ(t)‖²` (twice the "inertia" in the
mass metric), the second derivative along a collision-free solution `y` of Newton's equations is

    `I''(t) = 2‖ẏ(t)‖²ₘ + 2∑ᵢ mᵢ⟨yᵢ(t), ÿᵢ(t)⟩ = 2‖ẏ‖²ₘ - 2U(y) = 4E + 2U(y)`,

the last step using `‖ẏ‖²ₘ = 2E + 2U` (definition of the energy) and Euler homogeneity
(`euler_homogeneity_U`) together with `ÿ = ∇ₘ(U m)(y)`.

Everything here is fully proved.
-/

open ViscositySolutions
open Filter Gradient Real Set
open scoped BigOperators
open scoped Topology
open InnerProductSpace

set_option autoImplicit false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {N : ℕ}

namespace Submission.NBody

/-- Twice the inertia of the configuration: `I(t) = ∑ᵢ mᵢ‖yᵢ(t)‖²`. -/
noncomputable def inertia (m : Fin N → ℝ) (y : ℝ → EN E N) (t : ℝ) : ℝ :=
  ∑ i, m i * ‖y t i‖ ^ 2

/-- First derivative of the inertia along a differentiable motion. -/
lemma hasDerivAt_inertia (m : Fin N → ℝ) {y : ℝ → EN E N} {t : ℝ}
    (hdy : HasDerivAt y (deriv y t) t) :
    HasDerivAt (inertia m y) (∑ i, m i * (2 * inner ℝ (y t i) (deriv y t i))) t := by
  have hfeq : inertia m y = (fun s : ℝ => ∑ i, m i * ‖y s i‖ ^ 2) := rfl
  rw [hfeq]
  exact hasDerivAt_kinetic_sum m hdy

/-- Derivative of the "velocity" part `∑ᵢ mᵢ·2⟨yᵢ, ẏᵢ⟩` of `I'`, for a `C²` motion. -/
lemma hasDerivAt_inertia_deriv_fun (m : Fin N → ℝ) {y : ℝ → EN E N} {t : ℝ}
    (hdy : HasDerivAt y (deriv y t) t) (hd2 : HasDerivAt (deriv y) (iteratedDeriv 2 y t) t) :
    HasDerivAt (fun s : ℝ => ∑ i, m i * (2 * inner ℝ (y s i) (deriv y s i)))
      (∑ i, m i * (2 * (inner ℝ (y t i) ((iteratedDeriv 2 y t) i) +
        inner ℝ ((deriv y t) i) ((deriv y t) i)))) t := by
  have hfeq : (fun s : ℝ => ∑ i, m i * (2 * inner ℝ (y s i) (deriv y s i)))
      = (∑ i : Fin N, (fun s : ℝ => m i * (2 * inner ℝ (y s i) (deriv y s i)))) := by
    funext s
    simp only [Finset.sum_apply]
  rw [hfeq]
  refine HasDerivAt.sum (ι := Fin N) (u := Finset.univ)
    (A := fun i : Fin N => fun s : ℝ => m i * (2 * inner ℝ (y s i) (deriv y s i)))
    (A' := fun i : Fin N => m i * (2 * (inner ℝ (y t i) ((iteratedDeriv 2 y t) i) +
      inner ℝ ((deriv y t) i) ((deriv y t) i)))) ?_
  intro i hi
  have h1 : HasDerivAt (fun s : ℝ => inner ℝ (y s i) (deriv y s i))
      (inner ℝ (y t i) ((iteratedDeriv 2 y t) i) +
        inner ℝ ((deriv y t) i) ((deriv y t) i)) t :=
    HasDerivAt.inner ℝ (hasDerivAt_apply hdy i) (hasDerivAt_apply hd2 i)
  exact HasDerivAt.const_mul (𝔸 := ℝ) (m i) (HasDerivAt.const_mul (𝔸 := ℝ) 2 h1)

/-- **The Lagrange–Jacobi identity.**  Along a collision-free solution,
`I''(t) = 4E + 2U(y(t))`. -/
theorem iteratedDeriv_two_inertia (m : Fin N → ℝ) (hm : ∀ i, m i ≠ 0) {y : ℝ → EN E N}
    (hy : IsNBodySolution m y) (hnc : ∀ t > 0, WithoutCollisions (y t)) {t : ℝ} (ht : 0 < t) :
    iteratedDeriv 2 (inertia m y) t = 4 * energy m y t + 2 * U m (y t) := by
  have ht' : Ioi (0 : ℝ) ∈ 𝓝 t := isOpen_Ioi.mem_nhds ht
  have hcAt : ContDiffAt ℝ 2 y t := hy.contDiff.contDiffAt ht'
  have hdy : HasDerivAt y (deriv y t) t := (hcAt.differentiableAt (by norm_num)).hasDerivAt
  have hd2 : HasDerivAt (deriv y) (iteratedDeriv 2 y t) t := hasDerivAt_deriv_of_contDiffAt hcAt
  -- derivative of `I`, rewritten as an eventual equality to the explicit function
  have hderiv_eq : deriv (inertia m y) =ᶠ[𝓝 t]
      (fun s : ℝ => ∑ i, m i * (2 * inner ℝ (y s i) (deriv y s i))) := by
    filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
    have hcAt_s : ContDiffAt ℝ 2 y s := hy.contDiff.contDiffAt (isOpen_Ioi.mem_nhds hs)
    have hdy_s : HasDerivAt y (deriv y s) s := (hcAt_s.differentiableAt (by norm_num)).hasDerivAt
    exact (hasDerivAt_inertia m hdy_s).deriv
  have hderiv : HasDerivAt (deriv (inertia m y))
      (∑ i, m i * (2 * (inner ℝ (y t i) ((iteratedDeriv 2 y t) i) +
        inner ℝ ((deriv y t) i) ((deriv y t) i)))) t :=
    (hderiv_eq.hasDerivAt_iff).mpr (hasDerivAt_inertia_deriv_fun m hdy hd2)
  -- rewrite the derivative value
  have hX : (∑ i, m i * (2 * (inner ℝ (y t i) ((iteratedDeriv 2 y t) i) +
        inner ℝ ((deriv y t) i) ((deriv y t) i)))) = 4 * energy m y t + 2 * U m (y t) := by
    -- split the sum and use the equation of motion
    have hsplit : (∑ i, m i * (2 * (inner ℝ (y t i) ((iteratedDeriv 2 y t) i) +
        inner ℝ ((deriv y t) i) ((deriv y t) i))))
        = (∑ i, m i * (2 * inner ℝ (y t i) ((iteratedDeriv 2 y t) i)))
          + (∑ i, m i * (2 * inner ℝ ((deriv y t) i) ((deriv y t) i))) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hsplit, hy.eq t ht]
    -- first sum: Euler homogeneity
    have hA : (∑ i, m i * (2 * inner ℝ (y t i) ((weightedGrad m (U m) (y t)) i)))
        = 2 * (∑ i, inner ℝ (y t i) ((gradient (U m) (y t)) i)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [gradient_eq_smul_weightedGrad m hm (y t) i, inner_smul_right]
      ring
    rw [hA, euler_homogeneity_U m (y t) (hnc t ht)]
    -- second sum: the kinetic part
    have hB : (∑ i, m i * (2 * inner ℝ ((deriv y t) i) ((deriv y t) i)))
        = 2 * (∑ i, m i * ‖deriv y t i‖ ^ 2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [real_inner_self_eq_norm_sq]
      ring
    rw [hB]
    have hS : (∑ i, m i * ‖deriv y t i‖ ^ 2) = 2 * energy m y t + 2 * U m (y t) := by
      simp only [energy]
      ring
    rw [hS]
    ring
  -- assemble: `I'' = deriv (deriv I)`
  rw [hX] at hderiv
  have h2 : iteratedDeriv 2 (inertia m y) t = deriv (deriv (inertia m y)) t := by
    rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one]
  rw [h2]
  exact hderiv.deriv

end Submission.NBody
