/-
Copyright: work module for the Elgindi finite-time singularity project.

# Auxiliary lemmas for the angular slice integrability of the "hard" terms

The file `T2Defs` collects the five "hard" terms of the `D_z`-transport pairing into
`Hhard α f g`.  This module supplies the elementary ingredients used to prove that the
angular slice `θ ↦ Hhard α f g z θ` is integrable on `Iθ` (lemma `T2SliceHard`):

* `continuousOn_slice` and `exists_nonneg_bound_abs`: the angular slice of a `SmoothNbhd`
  function is continuous on the compact interval `Iθ`, hence admits a nonnegative bound;
* `DzIter_const_mul`, `mixed_sin_factor`, `pz_mixed_sin_factor`: the factor `sin(2θ)`
  produced by each application of `D_θ = sin(2θ) ∂_θ` survives the `D_z`-iterations, so
  every `mixed j i g` with `i ≥ 1` — and also its `z`-derivative `∂_z mixed j i g` — is
  divisible by `sin(2θ)`;
* `sq_mul_rpow_neg`, `sq_mul_rpow_neg_le_one`: the resulting weight algebra
  `sin(2θ)² · sin(2θ)^{-γ} = sin(2θ)^{2-γ} ≤ 1` for `γ < 2`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.mixed_comm
import Submission.Work.Spaces.SmoothCompact_Aux
import Submission.Work.FTS.H2.T2Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2

set_option autoImplicit false

/-! ## The angular slice of a smooth function -/

/-- For a function which is smooth on an open neighbourhood of the closed quadrant
(`Work.Spaces.SmoothNbhd`), the angular slice `θ ↦ h z θ` is continuous on `Iθ` for
every `z ∈ Iz`. -/
theorem continuousOn_slice {h : ℝ → ℝ → ℝ} (hsm : Work.Spaces.SmoothNbhd h) {z : ℝ}
    (hz : z ∈ Work.Spaces.Iz) :
    ContinuousOn (fun θ => h z θ) Work.Spaces.Iθ := by
  intro θ hθ
  have hcd : ContDiffAt ℝ ⊤ (Function.uncurry h) (z, θ) :=
    hsm.contDiffAt (Work.Spaces.isOpen_nbhU.mem_nhds (Work.Spaces.mem_nbhU hz hθ))
  exact (hcd.continuousAt.comp (Continuous.prodMk_right z).continuousAt).continuousWithinAt

/-- A function continuous on the compact interval `Iθ` admits a nonnegative bound for its
absolute value. -/
theorem exists_nonneg_bound_abs {u : ℝ → ℝ} (hu : ContinuousOn u Work.Spaces.Iθ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ ∈ Work.Spaces.Iθ, |u θ| ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image hu.abs
  exact ⟨max C 0, le_max_right _ _, fun θ hθ => le_trans (hC ⟨θ, hθ, rfl⟩) (le_max_left _ _)⟩

/-! ## The factor `sin(2θ)` survives the `D_z`-iterates -/

/-- A function of `θ` alone may be pulled out of the iterates of `D_z = z ∂_z`. -/
theorem DzIter_const_mul (j : ℕ) (c : ℝ → ℝ) (K : ℝ → ℝ → ℝ) :
    Work.Spaces.DzIter j (fun z θ => c θ * K z θ)
      = fun z θ => c θ * Work.Spaces.DzIter j K z θ := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [Work.Spaces.DzIter_succ, ih, Work.Spaces.DzIter_succ]
      funext z θ
      show z * deriv (fun z' => c θ * Work.Spaces.DzIter j K z' θ) z
        = c θ * (z * deriv (fun z' => Work.Spaces.DzIter j K z' θ) z)
      rw [deriv_const_mul_field]
      ring

/-- The `sin(2θ)` produced by the outermost `D_θ` of `D_θ^{i+1}` survives the
`D_z`-iterates. -/
theorem mixed_sin_factor (j i : ℕ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.mixed j (i + 1) g
      = fun z θ => Real.sin (2 * θ)
          * Work.Spaces.DzIter j (Work.Spaces.pth (Work.Spaces.DthIter i g)) z θ := by
  have h : Work.Spaces.DthIter (i + 1) g
      = fun z θ => Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.DthIter i g) z θ := rfl
  show Work.Spaces.DzIter j (Work.Spaces.DthIter (i + 1) g) = _
  rw [h]
  exact DzIter_const_mul j (fun θ => Real.sin (2 * θ))
    (Work.Spaces.pth (Work.Spaces.DthIter i g))

/-- The `z`-derivative of the same factorisation: `∂_z (mixed j (i+1) g)` also carries the
factor `sin(2θ)`, since the factor is independent of `z`. -/
theorem pz_mixed_sin_factor (j i : ℕ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pz (Work.Spaces.mixed j (i + 1) g) z θ
      = Real.sin (2 * θ)
          * Work.Spaces.pz (Work.Spaces.DzIter j (Work.Spaces.pth (Work.Spaces.DthIter i g)))
              z θ := by
  rw [mixed_sin_factor j i g]
  show deriv (fun z' => Real.sin (2 * θ)
        * Work.Spaces.DzIter j (Work.Spaces.pth (Work.Spaces.DthIter i g)) z' θ) z
      = Real.sin (2 * θ)
        * deriv (fun z' => Work.Spaces.DzIter j (Work.Spaces.pth (Work.Spaces.DthIter i g))
            z' θ) z
  rw [deriv_const_mul_field]

/-! ## Weight algebra at the angular endpoints -/

/-- `s² · s^{-γ} = s^{2-γ}` for `s ≥ 0` and `γ < 2`. -/
theorem sq_mul_rpow_neg (s γ : ℝ) (hs : 0 ≤ s) (hγ : γ < 2) :
    s ^ 2 * s ^ (-γ) = s ^ (2 - γ) := by
  have hne : (2 : ℝ) + (-γ) ≠ 0 := by linarith
  have h2 : s ^ (2 : ℝ) = s ^ 2 := Real.rpow_natCast s 2
  calc s ^ 2 * s ^ (-γ) = s ^ (2 : ℝ) * s ^ (-γ) := by rw [h2]
    _ = s ^ ((2 : ℝ) + -γ) :=
        (Real.rpow_add' (x := s) (y := (2 : ℝ)) (z := -γ) hs hne).symm
    _ = s ^ (2 - γ) := by rw [show (2 : ℝ) + -γ = 2 - γ by ring]

/-- `s² · s^{-γ} ≤ 1` for `0 ≤ s ≤ 1` and `0 ≤ 2 - γ`.  This is the pointwise bound which
makes `sin(2θ)^{2-γ}` (the effective weight of a "hard" mixed summand) bounded on `Iθ`. -/
theorem sq_mul_rpow_neg_le_one (s γ : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hγ : γ < 2)
    (hγ2 : 0 ≤ 2 - γ) : s ^ 2 * s ^ (-γ) ≤ 1 := by
  rw [sq_mul_rpow_neg s γ hs0 hγ]
  exact Real.rpow_le_one hs0 hs1 hγ2

end Work.FTS.H2
