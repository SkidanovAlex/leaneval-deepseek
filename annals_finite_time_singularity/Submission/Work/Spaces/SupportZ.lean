/-
Copyright: work module for the Elgindi finite-time singularity project.

# Compactly supported functions vanish for large `z`, together with all their derivatives

If `Function.uncurry f` has compact support then there is `R ≥ 0` such that `f z θ = 0`
for every `z > R` and every `θ`, and the same holds for all the iterated operators
`pzIter k`, `DthIter k` and `mixed j i` applied to `f`.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Order.Lattice
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Spaces

set_option autoImplicit false

theorem SupportZ (f : ℝ → ℝ → ℝ) (h : HasCompactSupport (Function.uncurry f)) :
    ∃ R : ℝ, 0 ≤ R ∧ (∀ z θ : ℝ, R < z → f z θ = 0) ∧
      (∀ k : ℕ, ∀ z θ : ℝ, R < z → pzIter k f z θ = 0) ∧
      (∀ k : ℕ, ∀ z θ : ℝ, R < z → DthIter k f z θ = 0) ∧
      (∀ j i : ℕ, ∀ z θ : ℝ, R < z → mixed j i f z θ = 0) := by
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp h.isBounded
  have h0 : ∀ z θ : ℝ, max C 0 < z → f z θ = 0 := by
    intro z θ hz
    by_contra hne
    have hmem : (z, θ) ∈ tsupport (Function.uncurry f) :=
      subset_closure (show (z, θ) ∈ Function.support (Function.uncurry f) from hne)
    have h1 : ‖(z, θ)‖ ≤ C := hC _ hmem
    have h2 : z ≤ ‖(z, θ)‖ := by
      have hznn : 0 < z := lt_of_le_of_lt (le_max_right C 0) hz
      have h := norm_fst_le (z, θ)
      rwa [Real.norm_eq_abs, abs_of_pos hznn] at h
    linarith [h1, h2, le_max_left C (0 : ℝ)]
  have hPz : ∀ k : ℕ, ∀ z θ : ℝ, max C 0 < z → pzIter k f z θ = 0 := by
    intro k
    induction k with
    | zero => exact h0
    | succ k ih =>
      intro z θ hz
      rw [pzIter_succ, pz]
      have hev : (fun z' => pzIter k f z' θ) =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
        exact ih z' θ hz'
      rw [hev.deriv_eq, deriv_const]
  have hDth : ∀ k : ℕ, ∀ z θ : ℝ, max C 0 < z → DthIter k f z θ = 0 := by
    intro k
    induction k with
    | zero => exact h0
    | succ k ih =>
      intro z θ hz
      rw [DthIter_succ, Dth]
      have hp : pth (DthIter k f) z θ = 0 := by
        rw [pth]
        have hev : (fun θ' => DthIter k f z θ') =ᶠ[𝓝 θ] (fun _ => (0 : ℝ)) := by
          filter_upwards with θ'
          exact ih z θ' hz
        rw [hev.deriv_eq, deriv_const]
      rw [hp, mul_zero]
  have hDz : ∀ j : ℕ, ∀ H : ℝ → ℝ → ℝ, (∀ z θ : ℝ, max C 0 < z → H z θ = 0) →
      ∀ z θ : ℝ, max C 0 < z → DzIter j H z θ = 0 := by
    intro j
    induction j with
    | zero => intro H hH z θ hz; exact hH z θ hz
    | succ j ih =>
      intro H hH z θ hz
      rw [DzIter_succ, Dz]
      have hp : pz (DzIter j H) z θ = 0 := by
        rw [pz]
        have hev : (fun z' => DzIter j H z' θ) =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
          filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
          exact ih H hH z' θ hz'
        rw [hev.deriv_eq, deriv_const]
      rw [hp, mul_zero]
  exact ⟨max C 0, le_max_right _ _, h0, hPz, hDth,
    fun j i z θ hz => hDz j (DthIter i f) (hDth i) z θ hz⟩

end Work.Spaces
