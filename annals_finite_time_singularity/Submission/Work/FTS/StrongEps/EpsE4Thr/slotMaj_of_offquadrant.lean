import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.EpsE4Thr.DecayMaj

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-! ## Vanishing of the slots off the open quadrant

`D_θ = sin(2θ)∂_θ` and `D_z = z∂_z` are derivative operators, so if a profile `g` vanishes at
*every* angle outside `(0, π/2)` then every slot `D_z^jD_θ^i g` vanishes there too: the vanishing
is preserved by `D_z` (the slice in `z` at a fixed angle is identically zero), and `D_θ` either
sees a whole neighbourhood on which the function is zero (angles strictly below `0` or strictly
above `π/2`) or multiplies by `sin(2θ) = 0` (the angles `0` and `π/2`). -/

private theorem DthIter_eq_zero_of_offquadrant {g : Fn}
    (hoff : ∀ z θ : ℝ, θ ∉ Set.Ioo 0 (π / 2) → g z θ = 0) :
    ∀ (i : ℕ) (z θ : ℝ), θ ∉ Set.Ioo 0 (π / 2) → Work.Spaces.DthIter i g z θ = 0 := by
  intro i
  induction i with
  | zero => intro z θ hθ; exact hoff z θ hθ
  | succ i ih =>
    intro z θ hθ
    show Real.sin (2 * θ) * deriv (fun θ' => Work.Spaces.DthIter i g z θ') θ = 0
    rcases eq_or_ne (Real.sin (2 * θ)) 0 with hs | hs
    · rw [hs, zero_mul]
    · -- `sin(2θ) ≠ 0` forces `θ ∉ [0, π/2]`, so a whole neighbourhood of `θ` is off the quadrant
      have hnotcl : θ ∉ closure (Set.Ioo (0 : ℝ) (π / 2)) := by
        intro hcl
        have hmem : θ ∈ Set.Icc (0 : ℝ) (π / 2) := by
          rwa [closure_Ioo (ne_of_lt (by linarith [Real.pi_pos] : (0 : ℝ) < π / 2))] at hcl
        exact hs (by
          rcases eq_or_lt_of_le hmem.1 with h | h
          · rw [← h]; simp
          · rcases eq_or_lt_of_le hmem.2 with h2 | h2
            · rw [h2, show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
            · exact absurd ⟨h, h2⟩ hθ)
      have hderiv : deriv (fun θ' => Work.Spaces.DthIter i g z θ') θ = 0 := by
        have hev : (fun θ' => Work.Spaces.DthIter i g z θ') =ᶠ[𝓝 θ] fun _ => (0 : ℝ) := by
          filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hnotcl] with θ' hθ'
          exact ih z θ' (fun hmem => hθ' (subset_closure hmem))
        rw [hev.deriv_eq, deriv_const]
      rw [hderiv, mul_zero]

private theorem mixed_eq_zero_of_offquadrant {g : Fn}
    (hoff : ∀ z θ : ℝ, θ ∉ Set.Ioo 0 (π / 2) → g z θ = 0) (j i : ℕ) (z θ : ℝ)
    (hθ : θ ∉ Set.Ioo 0 (π / 2)) : Work.Spaces.mixed j i g z θ = 0 := by
  have hD : ∀ z' : ℝ, Work.Spaces.DthIter i g z' θ = 0 :=
    fun z' => DthIter_eq_zero_of_offquadrant hoff i z' θ hθ
  have hdz : ∀ j : ℕ, ∀ z : ℝ, Work.Spaces.DzIter j (Work.Spaces.DthIter i g) z θ = 0 := by
    intro j
    induction j with
    | zero => intro z; exact hD z
    | succ j ih =>
      intro z
      simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
      rw [show (fun z' => Work.Spaces.DzIter j (Work.Spaces.DthIter i g) z' θ) = fun _ => (0 : ℝ)
            from funext ih, deriv_const, mul_zero]
  show Work.Spaces.DzIter j (Work.Spaces.DthIter i g) z θ = 0
  exact hdz j z

/-- **The `SlotMaj` clause from a quadrant bound plus off-quadrant vanishing.**  `SlotMaj k Maj g`
quantifies over *all* real angles, while every pointwise estimate on the route is a statement
about the open quadrant; for a profile which vanishes off the open quadrant the two agree, because
`D_θ` and `D_z` are derivative operators and both carry the vanishing (`D_θ = sin(2θ)∂_θ` kills
the boundary angles, and on the complementary open regions the slice is locally zero). -/
theorem slotMaj_of_offquadrant {k : ℕ} {Maj : ℝ → ℝ} {g : Fn}
    (h0 : ∀ z, 0 ≤ Maj z)
    (hoff : ∀ z θ : ℝ, θ ∉ Set.Ioo 0 (π / 2) → g z θ = 0)
    (hbd : ∀ z : ℝ, 0 < z → ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 → ∀ j i : ℕ, j + i ≤ k →
      |Work.Spaces.mixed j i g z θ| ≤ Maj z) :
    SlotMaj k Maj g := by
  intro z hz θ j i hji
  by_cases hθ : θ ∈ Set.Ioo 0 (π / 2)
  · exact hbd z hz θ hθ.1 hθ.2 j i hji
  · rw [mixed_eq_zero_of_offquadrant hoff j i z θ hθ, abs_zero]
    exact h0 z

end Work.FTS.StrongEps.EpsE4Thr
