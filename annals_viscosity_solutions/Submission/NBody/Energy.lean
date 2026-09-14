import ChallengeDeps
import Submission.NBody.Shift
import Mathlib

/-!
# Conservation of energy for the `N`-body problem

Sixth stone of the analytic layer.  For a solution `y` of Newton's equations
(`y'' = ∇ₘ (U m) ∘ y`) the total energy

    `E(t) = ½ ‖ẏ(t)‖²ₘ - U(y(t))   ( = ½ ∑ᵢ mᵢ ‖ẏᵢ(t)‖² - U(y(t)) )`

is a first integral: `E` has derivative `0` wherever the motion is collision-free.  The proof
is the standard `d/dt ½‖ẏ‖² = ⟨ÿ, ẏ⟩ₘ` versus `d/dt U(y) = ⟨∇U(y), ẏ⟩` comparison, using the
force identity (`gradient_U_coord`/`inner_gradient_eq_fderiv`) from `Force.lean`.

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

/-- Kinetic energy `½ ∑ᵢ mᵢ ‖vᵢ‖²` (half the squared mass-weighted norm of the velocity). -/
noncomputable def kinetic (m : Fin N → ℝ) (v : EN E N) : ℝ := (1 / 2) * ∑ i, m i * ‖v i‖ ^ 2

/-- Total energy of the motion `y` at time `t`: `½∑ᵢ mᵢ‖ẏᵢ(t)‖² - U(y(t))`. -/
noncomputable def energy (m : Fin N → ℝ) (y : ℝ → EN E N) (t : ℝ) : ℝ :=
  (1 / 2) * (∑ i, m i * ‖deriv y t i‖ ^ 2) - U m (y t)

/-! ## Calculus preliminaries -/

/-- Componentwise derivative of a curve in configuration space. -/
lemma hasDerivAt_apply {y : ℝ → EN E N} {y' : EN E N} {t : ℝ} (h : HasDerivAt y y' t)
    (i : Fin N) : HasDerivAt (fun s : ℝ => y s i) (y' i) t := by
  have := (PiLp.proj (p := 2) (𝕜 := ℝ) (β := fun _ : Fin N => E) i).hasFDerivAt.comp_hasDerivAt t h
  simpa [Function.comp_def, PiLp.proj_apply] using this

/-- The velocity `deriv y` of a `C²` curve is differentiable, with derivative the second
derivative `iteratedDeriv 2 y`. -/
lemma hasDerivAt_deriv_of_contDiffAt {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ → F} {t : ℝ} (hcAt : ContDiffAt ℝ 2 f t) :
    HasDerivAt (deriv f) (iteratedDeriv 2 f t) t := by
  have hd : DifferentiableAt ℝ (deriv f) t := by
    rw [← iteratedDeriv_one]
    rw [iteratedDeriv_eq_equiv_comp]
    exact (ContinuousMultilinearMap.piFieldEquiv ℝ (Fin 1) F).symm.differentiableAt.comp t
      (hcAt.differentiableAt_iteratedFDeriv (m := 1) (by norm_num))
  have hh := hd.hasDerivAt
  rw [show iteratedDeriv 2 f t = deriv (deriv f) t by
    rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one]]
  exact hh

/-- Derivative of the squared mass-weighted velocity: `d/dt ∑ᵢ mᵢ‖vᵢ(t)‖²
= ∑ᵢ mᵢ · 2⟨vᵢ(t), vᵢ'(t)⟩`. -/
lemma hasDerivAt_kinetic_sum (m : Fin N → ℝ) {v : ℝ → EN E N} {v' : EN E N} {t : ℝ}
    (hv : HasDerivAt v v' t) :
    HasDerivAt (fun s : ℝ => ∑ i, m i * ‖v s i‖ ^ 2)
      (∑ i, m i * (2 * inner ℝ (v t i) (v' i))) t := by
  have hfeq : (fun s : ℝ => ∑ i, m i * ‖v s i‖ ^ 2) =
      (∑ i : Fin N, (fun s : ℝ => m i * ‖v s i‖ ^ 2)) := by
    funext s
    simp only [Finset.sum_apply]
  rw [hfeq]
  exact HasDerivAt.sum (ι := Fin N) (u := Finset.univ)
    (A := fun i : Fin N => fun s : ℝ => m i * ‖v s i‖ ^ 2)
    (A' := fun i : Fin N => m i * (2 * inner ℝ (v t i) (v' i)))
    (by
      intro i hi
      have h1 : HasDerivAt (fun s : ℝ => ‖v s i‖ ^ 2) (2 * inner ℝ (v t i) (v' i)) t :=
        (hasDerivAt_apply hv i).norm_sq
      exact HasDerivAt.const_mul (𝔸 := ℝ) (m i) h1)

/-! ## Conservation of energy -/

/-- The mass-weighted decomposition of the gradient: `(∇(U m) x)ᵢ = mᵢ • (∇ₘ (U m) x)ᵢ`. -/
lemma gradient_eq_smul_weightedGrad (m : Fin N → ℝ) (hm : ∀ i, m i ≠ 0) (x : EN E N)
    (i : Fin N) :
    (gradient (U m) x) i = m i • (weightedGrad m (U m) x) i := by
  rw [show (weightedGrad m (U m) x) i = (m i)⁻¹ • (gradient (U m) x) i by simp [weightedGrad]]
  rw [smul_smul, mul_inv_cancel₀ (hm i), one_smul]

/-- **Conservation of energy.**  Along a collision-free solution of Newton's equations the
total energy has derivative zero. -/
theorem energy_hasDerivAt_zero (m : Fin N → ℝ) (hm : ∀ i, m i ≠ 0) {y : ℝ → EN E N}
    (hy : IsNBodySolution m y) (hnc : ∀ t > 0, WithoutCollisions (y t)) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (energy m y) 0 t := by
  have ht' : Ioi (0 : ℝ) ∈ 𝓝 t := isOpen_Ioi.mem_nhds ht
  have hcAt : ContDiffAt ℝ 2 y t := hy.contDiff.contDiffAt ht'
  have hdy : HasDerivAt y (deriv y t) t := (hcAt.differentiableAt (by norm_num)).hasDerivAt
  have hd2 : HasDerivAt (deriv y) (iteratedDeriv 2 y t) t := hasDerivAt_deriv_of_contDiffAt hcAt
  -- derivative of the kinetic part
  have hkin : HasDerivAt (fun s : ℝ => (1 / 2) * ∑ i, m i * ‖deriv y s i‖ ^ 2)
      ((1 / 2) * (∑ i, m i * (2 * inner ℝ (deriv y t i) (iteratedDeriv 2 y t i)))) t :=
    HasDerivAt.const_mul (𝔸 := ℝ) (1 / 2) (hasDerivAt_kinetic_sum m hd2)
  -- derivative of the potential part
  have hpot : HasDerivAt (fun s : ℝ => U m (y s)) ((fderiv ℝ (U m) (y t)) (deriv y t)) t := by
    have hU_at : HasFDerivAt (U m) (fderiv ℝ (U m) (y t)) (y t) :=
      (hasFDerivAt_U m (y t) (hnc t ht)).differentiableAt.hasFDerivAt
    simpa [Function.comp_def] using hU_at.comp_hasDerivAt t hdy
  have hE : HasDerivAt (energy m y)
      ((1 / 2) * (∑ i, m i * (2 * inner ℝ (deriv y t i) (iteratedDeriv 2 y t i))) -
        (fderiv ℝ (U m) (y t)) (deriv y t)) t := by
    have hE' := hkin.sub hpot
    rw [show (fun s : ℝ => (1 / 2) * ∑ i, m i * ‖deriv y s i‖ ^ 2) - (fun s : ℝ => U m (y s))
        = energy m y by
      funext s
      simp [energy, Pi.sub_apply]] at hE'
    exact hE'
  -- the two contributions cancel
  have hkey : (fderiv ℝ (U m) (y t)) (deriv y t) =
      ∑ i, m i * inner ℝ (iteratedDeriv 2 y t i) (deriv y t i) := by
    rw [← inner_gradient_eq_fderiv (y t) (deriv y t)]
    rw [PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro i hi
    rw [gradient_eq_smul_weightedGrad m hm (y t) i, ← hy.eq t ht]
    rw [inner_smul_left]
    simp
  rw [hkey] at hE
  have hzero : (1 / 2) * (∑ i, m i * (2 * inner ℝ (deriv y t i) (iteratedDeriv 2 y t i))) -
      (∑ i, m i * inner ℝ (iteratedDeriv 2 y t i) (deriv y t i)) = 0 := by
    rw [Finset.mul_sum, sub_eq_zero]
    apply Finset.sum_congr rfl
    intro i hi
    rw [real_inner_comm]
    ring
  rwa [hzero] at hE


/-- **Energy is a first integral.**  Along a collision-free solution of Newton's equations the
total energy is constant on `(0, ∞)`: `E(s) = E(t)` for all `s, t > 0`. -/
theorem energy_eq_of_pos (m : Fin N → ℝ) (hm : ∀ i, m i ≠ 0) {y : ℝ → EN E N}
    (hy : IsNBodySolution m y) (hnc : ∀ t > 0, WithoutCollisions (y t))
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) : energy m y s = energy m y t := by
  have hdiff : DifferentiableOn ℝ (energy m y) (Ioi (0 : ℝ)) := fun x hx =>
    (energy_hasDerivAt_zero m hm hy hnc hx).differentiableAt.differentiableWithinAt
  have hfderiv : ∀ x ∈ Ioi (0 : ℝ), fderivWithin ℝ (energy m y) (Ioi (0 : ℝ)) x = 0 := by
    intro x hx
    have hd := energy_hasDerivAt_zero m hm hy hnc hx
    have hf : fderiv ℝ (energy m y) x = 0 := by
      simpa using hd.hasFDerivAt.fderiv
    rw [fderivWithin_of_isOpen isOpen_Ioi hx, hf]
  exact Convex.is_const_of_fderivWithin_eq_zero (convex_Ioi (0 : ℝ)) hdiff hfderiv hs ht

end Submission.NBody
