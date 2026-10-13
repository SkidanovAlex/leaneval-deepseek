import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.AeI1Fts.Defs
import Submission.Work.FTS.EllipticEst.Honest.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `HkSq_pth_grad`

The level-`0` square of the `ℋ`-norm of the angular derivative of the radial gradient
`U u = z ∂_z u` equals the iterated integral of `(V u)²σ`, where `V u = z ∂_z∂_θu` and
`σ = sigE = sin(2θ)^{-η}`:

  `HkSq α 0 (∂_θ(z∂_zu)) = ∫_z w(z)² ∫_θ (V u z θ)² σ(θ)`.

This is a pure rewriting statement: on the *open* quadrant `(0,∞) × (0,π/2)` the two
functions `∂_θ U u` and `V u` agree by Clairaut (`Work.Spaces.pz_pth_comm`), the two
integration domains `Iz = [0,∞)`, `Iθ = [0,π/2]` differ from `Ioi 0`, `Ioo 0 (π/2)` by
null sets (`{0}` and `{0, π/2}`), and the level-`0` `ℋ`-integrand is the weighted square
`w²·g²·σ` (`Honest.HkIntegrand_zero_eq`, `Honest.sq_profile_eq`).  No integrability
hypothesis is needed: all integrals are totalised, and the manipulations used are valid
for arbitrary (junk-valued) integrals.

The only hypothesis on `u` is joint `C^n`-smoothness on the open quadrant, for every `n`
(in particular `C²`, which is all Clairaut needs).
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AeI1Fts

set_option autoImplicit false

local notation "Iθo" => Set.Ioo (0 : ℝ) (Real.pi / 2)

/-- **Clairaut for the mixed slot.**  On the open quadrant, `∂_θ(z∂_z u) = z∂_z∂_θu`,
i.e. `pth (grad u) = V u`.

`pth (grad u) z θ = z·∂_θ(∂_zu)`, and the order of the two partial derivatives may be
swapped because `u` is `C²` at `(z,θ)`. -/
theorem pth_grad_eq_V (u : ℝ → ℝ → ℝ)
    (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Iθo,
      Work.Spaces.pth (Work.FTS.EllipticEst.H2W.Ae.grad u) z θ = V u z θ := by
  intro z hz θ hθ
  have hqd : IsOpen (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    isOpen_Ioi.prod isOpen_Ioo
  have hcd : ContDiffAt ℝ 2 (Function.uncurry u) (z, θ) :=
    (hu 2).contDiffAt (hqd.mem_nhds ⟨hz, hθ⟩)
  have hcl := Work.Spaces.pz_pth_comm (f := u) hcd
  have h1 : Work.Spaces.pth (Work.FTS.EllipticEst.H2W.Ae.grad u) z θ
      = z * deriv (fun θ' => Work.Spaces.pz u z θ') θ := by
    show deriv (fun θ' => Work.FTS.EllipticEst.H2W.Ae.grad u z θ') θ
      = z * deriv (fun θ' => Work.Spaces.pz u z θ') θ
    simp only [Work.FTS.EllipticEst.H2W.Ae.grad]
    rw [deriv_const_mul_field]
  rw [h1]
  show z * deriv (fun θ' => Work.Spaces.pz u z θ') θ
      = z * Work.Spaces.pz (Work.Spaces.pth u) z θ
  rw [hcl]
  rfl

/-- The level-`0` `ℋ`-integrand of `g` is `w²·g²·σ` on `Iθ = [0,π/2]`. -/
theorem hkIntegrand_zero_eq_sigE (α : ℝ) (g : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α 0 g z θ
      = (g z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * sigE θ := by
  rw [Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq,
    Work.FTS.EllipticEst.Honest.sq_profile_eq g z θ
      (Work.FTS.EllipticEst.Honest.sin_two_nonneg_of_mem_Iθ hθ)]
  rfl

/-- **`HkSq α 0 (∂_θ U u)` as the `V u`-energy.** -/
theorem HkSq_zero_pth_grad (α : ℝ) (u : ℝ → ℝ → ℝ)
    (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    Work.Spaces.HkSq α 0 (Work.Spaces.pth (Work.FTS.EllipticEst.H2W.Ae.grad u))
      = ∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2
          * ∫ θ in Iθo, (V u z θ) ^ 2 * sigE θ := by
  have hgrad := pth_grad_eq_V u hu
  calc Work.Spaces.HkSq α 0 (Work.Spaces.pth (Work.FTS.EllipticEst.H2W.Ae.grad u))
      = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.pth (Work.FTS.EllipticEst.H2W.Ae.grad u) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 :=
        Work.FTS.EllipticEst.Honest.HkSq_zero_eq α _
    _ = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.pth (Work.FTS.EllipticEst.H2W.Ae.grad u) z θ) ^ 2
            * (Work.Spaces.w z) ^ 2 * sigE θ := by
        refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
        exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc
          (fun θ hθ =>
            Work.FTS.EllipticEst.Honest.sq_profile_eq _ z θ
              (Work.FTS.EllipticEst.Honest.sin_two_nonneg_of_mem_Iθ hθ))
    _ = ∫ z in Work.Spaces.Iz, ∫ θ in Iθo,
          (Work.Spaces.pth (Work.FTS.EllipticEst.H2W.Ae.grad u) z θ) ^ 2
            * (Work.Spaces.w z) ^ 2 * sigE θ := by
        refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
        exact MeasureTheory.setIntegral_congr_set
          (MeasureTheory.Ioo_ae_eq_Icc (μ := volume)).symm
    _ = ∫ z in Set.Ioi (0 : ℝ), ∫ θ in Iθo,
          (Work.Spaces.pth (Work.FTS.EllipticEst.H2W.Ae.grad u) z θ) ^ 2
            * (Work.Spaces.w z) ^ 2 * sigE θ :=
        MeasureTheory.setIntegral_congr_set (MeasureTheory.Ioi_ae_eq_Ici (μ := volume)).symm
    _ = ∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2
          * ∫ θ in Iθo, (V u z θ) ^ 2 * sigE θ := by
        refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun z hz => ?_)
        rw [show (∫ θ in Iθo,
              (Work.Spaces.pth (Work.FTS.EllipticEst.H2W.Ae.grad u) z θ) ^ 2
                * (Work.Spaces.w z) ^ 2 * sigE θ)
            = ∫ θ in Iθo,
              ((V u z θ) ^ 2 * sigE θ) * (Work.Spaces.w z) ^ 2 from by
          refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun θ hθ => ?_)
          rw [hgrad z hz θ hθ]
          ring]
        rw [MeasureTheory.integral_mul_const]
        ring

theorem HkSq_pth_grad (α : ℝ) (u : ℝ → ℝ → ℝ)
    (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    Work.Spaces.HkSq α 0 (Work.Spaces.pth (Work.FTS.EllipticEst.H2W.Ae.grad u))
      = ∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2
          * ∫ θ in Set.Ioo 0 (Real.pi / 2),
              (Work.FTS.EllipticEst.AeI1Fts.V u z θ) ^ 2
                * Work.FTS.EllipticEst.AeI1Fts.sigE θ :=
  HkSq_zero_pth_grad α u hu

end Work.FTS.EllipticEst.AeI1Fts
