/-
Copyright: work module for the Elgindi finite-time singularity project.

# Auxiliary lemmas for `pz_mixed_mul_le`

Small, reusable facts about the operators `pzIter`, `DthIter` of
`Submission.Work.Spaces.Defs` and about one-dimensional iterated derivatives:
that `pzIter` is `iteratedDeriv`, that iterated derivatives of sums and of the
zero function behave as expected, that a partial derivative of a `C^∞` function
of two variables is again `C^∞`, and the elementary consequences of `SmoothInt`
used to feed those lemmas.
-/
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open Set Filter

namespace Work.Spaces

set_option autoImplicit false

/-! ## `pzIter` is the iterated derivative of the `z`-slice -/

/-- `pzIter k h z θ` is the `k`-th iterated derivative of the function
`z' ↦ h z' θ` evaluated at `z`. -/
theorem pzIter_eq_iteratedDeriv (k : ℕ) (h : ℝ → ℝ → ℝ) (z θ : ℝ) :
    pzIter k h z θ = iteratedDeriv k (fun z' => h z' θ) z := by
  rw [iteratedDeriv_eq_iterate]
  induction k generalizing z with
  | zero => rfl
  | succ n ih =>
      simp only [pzIter_succ, pz]
      have : (fun z' => pzIter n h z' θ) = deriv^[n] (fun z' => h z' θ) := by
        funext z'; exact ih z'
      rw [this, Function.iterate_succ_apply']

/-- The iterated derivatives of the zero function vanish. -/
theorem iteratedDeriv_zero_fun (n : ℕ) (x : ℝ) :
    iteratedDeriv n (fun _ : ℝ => (0 : ℝ)) x = 0 := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      rw [iteratedDeriv_succ,
        show iteratedDeriv n (fun _ : ℝ => (0 : ℝ)) = fun _ => 0 from funext ih]
      simp

/-- Iterated derivatives of a finite sum with constant coefficients. -/
theorem iteratedDeriv_sum_const_mul {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (F : ι → ℝ → ℝ) (n : ℕ) (x : ℝ)
    (h : ∀ i ∈ s, ContDiffAt ℝ (n : ℕ∞) (F i) x) :
    iteratedDeriv n (fun y => ∑ i ∈ s, c i * F i y) x
      = ∑ i ∈ s, c i * iteratedDeriv n (F i) x := by
  have hfun : (fun y => ∑ i ∈ s, c i * F i y) = ∑ i ∈ s, fun y => c i * F i y := by
    funext y
    rw [Finset.sum_apply]
  rw [hfun, iteratedDeriv_sum (f := fun i y => c i * F i y) (I := s) (x := x)
    (fun i hi => contDiffAt_const.mul (h i hi))]
  exact Finset.sum_congr rfl fun i hi => by
    rw [iteratedDeriv_const_mul _ (h i hi)]

/-! ## Smoothness of partial derivatives of a `C^∞` function of two variables -/

/-- The partial `θ`-derivative `(z,θ) ↦ ∂_θ f(z,θ)` of a `C^∞` function of two
variables is again `C^∞`.  (The `deriv` of the `θ`-slice is by definition the
value of `fderiv` on the second basis vector.) -/
theorem contDiffAt_deriv_slice {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : ContDiffAt ℝ ⊤ (Function.uncurry f) (z, θ)) :
    ContDiffAt ℝ ⊤ (fun p : ℝ × ℝ => deriv (fun y => f p.1 y) p.2) (z, θ) := by
  have hinner : ContDiffAt ℝ ⊤ (fun q : (ℝ × ℝ) × ℝ => (q.1.1, q.2)) ((z, θ), θ) :=
    by fun_prop
  have hfun : ContDiffAt ℝ ⊤ (fun q : (ℝ × ℝ) × ℝ => f q.1.1 q.2) ((z, θ), θ) :=
    ContDiffAt.comp (f := fun q : (ℝ × ℝ) × ℝ => (q.1.1, q.2)) ((z, θ), θ) h hinner
  have h1 : ContDiffWithinAt ℝ ⊤ (Function.uncurry (fun p : ℝ × ℝ => fun y : ℝ => f p.1 y))
      (Set.univ ×ˢ Set.univ) ((z, θ), θ) := by
    rw [Set.univ_prod_univ]
    exact hfun.contDiffWithinAt
  have hmain := ContDiffWithinAt.fderivWithin_apply (m := ⊤) (n := ⊤) (s := Set.univ)
    (t := Set.univ) (f := fun p : ℝ × ℝ => fun y : ℝ => f p.1 y)
    (g := fun p : ℝ × ℝ => p.2) (k := fun _ => (1 : ℝ)) (x₀ := (z, θ)) h1
    (by fun_prop) (by fun_prop) uniqueDiffOn_univ (by simp) (by simp) (by simp)
  have h2 : ContDiffWithinAt ℝ ⊤
      (fun p : ℝ × ℝ => deriv (fun y => f p.1 y) p.2) Set.univ (z, θ) := by
    change ContDiffWithinAt ℝ ⊤
      (fun x : ℝ × ℝ => (fderiv ℝ (fun y => f x.1 y) x.2) 1) Set.univ (z, θ)
    simpa only [fderivWithin_univ] using hmain
  exact contDiffWithinAt_univ.mp h2

/-- Restriction of a `C^∞` function of two variables to a horizontal slice is `C^∞`. -/
theorem contDiffAt_slice_left {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : ContDiffAt ℝ ⊤ (Function.uncurry f) (z, θ)) :
    ContDiffAt ℝ ⊤ (fun z' => f z' θ) z := by
  have hlin : ContDiffAt ℝ ⊤ (fun z' : ℝ => (z', θ)) z := by fun_prop
  exact h.comp z hlin

/-- Restriction of a `C^∞` function of two variables to a vertical slice is `C^∞`. -/
theorem contDiffAt_slice_right {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : ContDiffAt ℝ ⊤ (Function.uncurry f) (z, θ)) :
    ContDiffAt ℝ ⊤ (fun θ' => f z θ') θ := by
  have hlin : ContDiffAt ℝ ⊤ (fun θ' : ℝ => (z, θ')) θ := by fun_prop
  exact h.comp θ hlin

/-! ## Vanishing of `DthIter` at the angular boundary -/

/-- At a point where `sin (2θ) = 0`, every positive iterate of `D_θ` vanishes. -/
theorem DthIter_succ_eq_zero_of_sin_eq_zero (j : ℕ) (h : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hθ : Real.sin (2 * θ) = 0) : DthIter (j + 1) h z θ = 0 := by
  simp [DthIter_succ, Dth, hθ]

/-- At the two angular endpoints `θ = 0` and `θ = π/2` of `Iθ` the factor `sin (2θ)`
of `D_θ` vanishes. -/
theorem sin_two_mul_eq_zero_of_mem_Iθ_of_not_mem_Ioo {θ : ℝ} (hθ : θ ∈ Iθ)
    (h : θ ∉ Ioo 0 (π / 2)) : Real.sin (2 * θ) = 0 := by
  have hcases : θ = 0 ∨ θ = π / 2 := by
    rcases hθ with ⟨h0, h1⟩
    by_cases hle : θ ≤ 0
    · exact Or.inl (le_antisymm hle h0)
    · have hle' : 0 < θ := not_le.mp hle
      refine Or.inr (le_antisymm h1 ?_)
      by_contra hc
      exact absurd ⟨hle', lt_of_not_ge hc⟩ h
  rcases hcases with rfl | rfl
  · simp
  · rw [show 2 * (π / 2) = π by ring, Real.sin_pi]

/-! ## Elementary consequences of `SmoothInt` -/

/-- `SmoothInt` functions are `C^∞` (jointly in both variables) at every point
lying over the open quadrant. -/
theorem SmoothInt.contDiffAt_uncurry {f : ℝ → ℝ → ℝ} (hf : SmoothInt f) {z θ : ℝ}
    (hz : z ∈ Set.Ioi (-1)) (hθ : θ ∈ Ioo 0 (π / 2)) :
    ContDiffAt ℝ ⊤ (Function.uncurry f) (z, θ) := by
  refine hf.1.contDiffAt ?_
  exact (isOpen_Ioi.prod isOpen_Ioo).mem_nhds (by rw [Set.mem_prod]; exact ⟨hz, hθ⟩)

/-- For fixed `z` over the open quadrant, the `θ`-slice of a `SmoothInt` function is
`C^∞` on `(0, π/2)`. -/
theorem SmoothInt.contDiffOn_theta_slice {f : ℝ → ℝ → ℝ} (hf : SmoothInt f) {z : ℝ}
    (hz : z ∈ Set.Ioi (-1)) :
    ContDiffOn ℝ ⊤ (fun θ => f z θ) (Ioo 0 (π / 2)) := by
  rw [isOpen_Ioo.contDiffOn_iff]
  intro θ hθ
  have h1 : ContDiffAt ℝ ⊤ (Function.uncurry f) (z, θ) := hf.contDiffAt_uncurry hz hθ
  have h2 : ContDiffAt ℝ ⊤ (fun θ' : ℝ => (z, θ')) θ := by fun_prop
  exact h1.comp θ h2

/-- For fixed `θ` in the closed quadrant, the `z`-slice of a `SmoothInt` function is
`C^∞` on `(-1, ∞)`. -/
theorem SmoothInt.contDiffAt_z_slice {f : ℝ → ℝ → ℝ} (hf : SmoothInt f) {z θ : ℝ}
    (hz : z ∈ Iz) (hθ : θ ∈ Iθ) :
    ContDiffAt ℝ ⊤ (fun z' => f z' θ) z := by
  have h := hf.2 θ hθ
  have hz' : z ∈ Set.Ioi (-1) := by
    simp only [Iz, Set.mem_Ici] at hz; simp only [Set.mem_Ioi]; linarith
  exact h.contDiffAt (isOpen_Ioi.mem_nhds hz')

end Work.Spaces
