/-
Copyright: work module for the Elgindi finite-time singularity project.

# Elementary auxiliary facts for Lemma `WtoW`

Small, self-contained ingredients used in the proof of
`Work.Elliptic.WtoW` (Elgindi, *Finite-time singularity formation for `C^{1,α}`
solutions to the incompressible Euler equations on `ℝ³`*, Annals of Math. **194**
(2021), Lemma `WtoW`, tex 1255):

* `WtoW_sin2_nonneg`, `WtoW_sin2_le_one`: elementary bounds for `sin 2θ` on `Iθ`;
* `WtoW_sin2_min_bound`: `min θ (π/2 - θ) ≤ (π/4) sin(2θ)` on `Iθ`, the inequality
  that converts the fundamental-theorem-of-calculus bounds in `θ` into the angular
  weight `sin(2θ)` of the `𝒲^{4,∞}`-norm;
* `WtoW_Addrpow_le_one`: the "`A · Z`" cancellation `(α+s)s^{α/5}·s^{-α/5}/(α+s) ≤ 1`
  uniform in `α ∈ (0,1]`, `s ∈ [0,1]`;
* `WtoW_SupFinite_of_bound`: a uniform pointwise bound makes the `L^∞`-supremum
  honest;
* `WtoW_pzIter_mul_theta`: `∂_z^m` of a product with a factor depending only on `θ`;
* `WtoW_pzIter_z_indep`: `∂_z^m` of a function of `θ` alone;
* `WtoW_DthIter_sin_two_z_indep`: `D_θ^e (sin 2θ)` does not depend on `z`.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Elliptic

set_option autoImplicit false
set_option linter.unusedVariables false

/-- `sin (2θ) ≥ 0` on `Iθ`. -/
theorem WtoW_sin2_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- `sin (2θ) ≤ 1` on `Iθ`. -/
theorem WtoW_sin2_le_one (θ : ℝ) : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _

/-- On `Iθ`, `min θ (π/2 - θ) ≤ (π/4) sin (2θ)`. -/
theorem WtoW_sin2_min_bound {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    min θ (π / 2 - θ) ≤ (π / 4) * Real.sin (2 * θ) := by
  have hpi := Real.pi_pos
  rcases le_total θ (π / 4) with h | h
  · rw [min_eq_left (by linarith)]
    have hx0 : 0 ≤ 2 * θ := by linarith [hθ.1]
    have hx1 : 2 * θ ≤ π / 2 := by linarith
    have hm : 2 / Real.pi * (2 * θ) ≤ Real.sin (2 * θ) := Real.mul_le_sin hx0 hx1
    have h2 : (π / 4) * (2 / Real.pi * (2 * θ)) = θ := by
      field_simp; ring
    calc θ = (π / 4) * (2 / Real.pi * (2 * θ)) := h2.symm
      _ ≤ (π / 4) * Real.sin (2 * θ) := mul_le_mul_of_nonneg_left hm (by positivity)
  · rw [min_eq_right (by linarith)]
    have hx0 : 0 ≤ Real.pi - 2 * θ := by linarith [hθ.2]
    have hx1 : Real.pi - 2 * θ ≤ Real.pi / 2 := by linarith
    have hm : 2 / Real.pi * (Real.pi - 2 * θ) ≤ Real.sin (Real.pi - 2 * θ) :=
      Real.mul_le_sin hx0 hx1
    rw [Real.sin_pi_sub] at hm
    have h2 : (π / 4) * (2 / Real.pi * (Real.pi - 2 * θ)) = π / 2 - θ := by
      field_simp; ring
    calc π / 2 - θ = (π / 4) * (2 / Real.pi * (Real.pi - 2 * θ)) := h2.symm
      _ ≤ (π / 4) * Real.sin (2 * θ) := mul_le_mul_of_nonneg_left hm (by positivity)

/-- The `A · Z` cancellation: `(α+s)·s^{α/5}·(s^{-α/5}/(α+s)) ≤ 1` for `s ≥ 0`,
`α > 0`. -/
theorem WtoW_Addrpow_le_one {α s : ℝ} (hα : 0 < α) (hs : 0 ≤ s) :
    (α + s) * s ^ (α / 5) * (s ^ (-(α / 5)) / (α + s)) ≤ 1 := by
  have h5 : (0 : ℝ) < α / 5 := by linarith
  have hne : α + s ≠ 0 := by positivity
  have hEq : (α + s) * s ^ (α / 5) * (s ^ (-(α / 5)) / (α + s))
      = s ^ (α / 5) * s ^ (-(α / 5)) := by
    field_simp
  rw [hEq]
  rcases eq_or_lt_of_le hs with h | h
  · rw [← h, Real.zero_rpow (ne_of_gt h5), Real.zero_rpow (by linarith : -(α / 5) ≠ 0)]
    norm_num
  · rw [← Real.rpow_add h, add_neg_cancel, Real.rpow_zero]

/-- `SmoothNbhd` implies `SmoothInt` (a local copy, so that no unstable module has to
be imported). -/
theorem WtoW_SmoothInt {f : ℝ → ℝ → ℝ} (h : Work.Spaces.SmoothNbhd f) :
    Work.Spaces.SmoothInt f := by
  refine ⟨h.mono ?_, ?_⟩
  · rintro ⟨z, θ⟩ ⟨hz, hθ⟩
    exact ⟨hz, by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  · intro θ hθ
    have hθ' : θ ∈ Set.Ioo (-1) (π / 2 + 1) :=
      ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
    have hmap : Set.MapsTo (fun z : ℝ => (z, θ)) (Set.Ioi (-1))
        (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (π / 2 + 1)) := fun z hz => ⟨hz, hθ'⟩
    exact h.comp (contDiffOn_id.prodMk contDiffOn_const) hmap

/-- A uniform pointwise bound makes `SupFinite` hold. -/
theorem WtoW_SupFinite_of_bound {g : ℝ → ℝ → ℝ} {C : ℝ}
    (h : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ, |g z θ| ≤ C) :
    Work.Spaces.SupFinite g :=
  ⟨C, fun y hy => by rcases hy with ⟨z, hz, θ, hθ, rfl⟩; exact h z hz θ hθ⟩

/-- `∂_z^m` of a product with a factor depending only on `θ`. -/
theorem WtoW_pzIter_mul_theta (m : ℕ) (a : ℝ → ℝ) (u : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pzIter m (fun z θ => a θ * u z θ) z θ
      = a θ * Work.Spaces.pzIter m u z θ := by
  induction m generalizing z with
  | zero => rfl
  | succ n ih =>
      show deriv (fun z' => Work.Spaces.pzIter n (fun z θ => a θ * u z θ) z' θ) z
        = a θ * deriv (fun z' => Work.Spaces.pzIter n u z' θ) z
      rw [show (fun z' => Work.Spaces.pzIter n (fun z θ => a θ * u z θ) z' θ)
            = fun z' => a θ * Work.Spaces.pzIter n u z' θ from funext fun z' => ih z']
      rw [deriv_const_mul_field]

/-- `∂_z^m` of a function depending only on `θ`, for `m ≥ 1`. -/
theorem WtoW_pzIter_succ_z_indep (m : ℕ) (F : ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pzIter (m + 1) (fun z θ => F θ) z θ = 0 := by
  induction m generalizing z with
  | zero =>
      show deriv (fun z' => (fun z θ => F θ) z' θ) z = 0
      simp
  | succ n ih =>
      show deriv (fun z' => Work.Spaces.pzIter (n + 1) (fun z θ => F θ) z' θ) z = 0
      rw [show (fun z' => Work.Spaces.pzIter (n + 1) (fun z θ => F θ) z' θ) = fun _ => (0 : ℝ)
            from funext fun z' => ih z']
      simp

/-- `D_θ^e (sin 2θ)` is independent of `z`. -/
theorem WtoW_DthIter_sin_two_z_indep : ∀ (e : ℕ) (z θ : ℝ),
    Work.Spaces.DthIter e (fun z θ => Real.sin (2 * θ)) z θ
      = Work.Spaces.DthIter e (fun z θ => Real.sin (2 * θ)) 0 θ := by
  intro e
  induction e with
  | zero => intro z θ; rfl
  | succ n ih =>
      intro z θ
      show Real.sin (2 * θ)
            * deriv (fun θ' => Work.Spaces.DthIter n (fun z θ => Real.sin (2 * θ)) z θ') θ
        = Real.sin (2 * θ)
            * deriv (fun θ' => Work.Spaces.DthIter n (fun z θ => Real.sin (2 * θ)) 0 θ') θ
      rw [show (fun θ' => Work.Spaces.DthIter n (fun z θ => Real.sin (2 * θ)) z θ')
            = (fun θ' => Work.Spaces.DthIter n (fun z θ => Real.sin (2 * θ)) 0 θ') from
        funext fun θ' => ih z θ']

end Work.Elliptic
