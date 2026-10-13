import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.FTS.StrongEps.H5.Data
import Submission.Work.FTS.StrongPersist.dthU_c2m_bound6
import Submission.Work.FTS.Nonlinear.FstarPkg.dthU_c2m_bound
import Submission.Work.FTS.LocData.DthIter_Gam_abs_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.H5.Atoms

open scoped Real Topology

/-! ## Data for the angular profile `θ ↦ D_θ c2m θ`

The angular coefficient of the transport term is `c2m θ = cos(2θ) - sin²θ`, and the profile
that enters the level-five atoms is `θ ↦ dthU c2m θ = sin(2θ)·(c2m)'θ`.  This file records the
two facts the surrounding H5 machinery needs about it:

* it is `C^∞` on the open quadrant (as a function of `(z,θ)` independent of `z`);
* it and its first four angular jets are bounded by a constant times `sin(2θ)` on `[0,π/2]`.

The smoothness is inherited from `θ ↦ c2m θ` through the operator `D_θ = sin(2θ)∂_θ`, and the
bounds are the ones already established for the iterates of `dthU` on `c2m`
(`Work.FTS.StrongPersist.dthU_c2m_bound6`, which gives `|D_θ^j c2m| ≤ C sin(2θ)²` for
`1 ≤ j ≤ 6`); since `dthU^[i] (dthU c2m) = dthU^[i+1] c2m` and `sin(2θ)² ≤ sin(2θ)` on
`Iθ = [0,π/2]`, the required `sin(2θ)`-bounds follow. -/

/-- `(z,θ) ↦ dthU c2m θ` is `C^∞` on the open quadrant. -/
theorem smoothOpen_dthU_c2m :
    Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => Work.Spaces.dthU Work.Construction.c2m θ) := by
  have hc2m : Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => Work.Construction.c2m θ) := by
    have hsnd : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => p.2) := contDiff_snd
    have hcos : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => Real.cos (2 * p.2)) :=
      Real.contDiff_cos.comp (contDiff_const.mul hsnd)
    have hsin2 : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => Real.sin p.2 ^ 2) :=
      (Real.contDiff_sin.comp hsnd).pow 2
    have h1 : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => Real.cos (2 * p.2) - Real.sin p.2 ^ 2) :=
      hcos.sub hsin2
    have h2 : ContDiff ℝ Work.Stability.smoothOrder
        (fun p : ℝ × ℝ => Real.cos (2 * p.2) - Real.sin p.2 ^ 2) := h1.of_le le_top
    exact h2.contDiffOn.mono (Set.subset_univ _)
  -- `D_θ` of the `z`-independent function `c2m` is exactly `dthU c2m`
  exact hc2m.Dth

theorem DthUC2mProfileData : ∃ C : ℝ, 0 < C ∧
    Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => Work.Spaces.dthU Work.Construction.c2m θ) ∧
    (∀ θ ∈ Work.Spaces.Iθ, |Work.Spaces.dthU Work.Construction.c2m θ| ≤ C) ∧
    (∀ i : ℕ, 1 ≤ i → i ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => Work.Spaces.dthU Work.Construction.c2m θ') 0 θ|
        ≤ C * Real.sin (2 * θ)) := by
  obtain ⟨C, hCpos, hC⟩ := Work.FTS.StrongPersist.dthU_c2m_bound6
  refine ⟨C, hCpos, smoothOpen_dthU_c2m, ?_, ?_⟩
  · intro θ hθ
    have h := hC 1 le_rfl (by norm_num) θ
    rw [Function.iterate_one] at h
    have hs1 : Real.sin (2 * θ) ^ 2 ≤ 1 := by
      nlinarith [Real.sin_sq_le_one (2 * θ)]
    calc |Work.Spaces.dthU Work.Construction.c2m θ| ≤ C * Real.sin (2 * θ) ^ 2 := h
      _ ≤ C * 1 := mul_le_mul_of_nonneg_left hs1 (le_of_lt hCpos)
      _ = C := by ring
  · intro i hi1 hi4 θ hθ
    have hs0 : 0 ≤ Real.sin (2 * θ) :=
      Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1],
        by linarith [hθ.2, Real.pi_pos]⟩
    have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
    have hsq : Real.sin (2 * θ) ^ 2 ≤ Real.sin (2 * θ) := by nlinarith
    have hstep : Work.Spaces.dthU^[i + 1] Work.Construction.c2m θ
        = Work.Spaces.dthU^[i] (Work.Spaces.dthU Work.Construction.c2m) θ := by
      rw [Function.iterate_succ_apply]
    have h := hC (i + 1) (by omega) (by omega) θ
    rw [hstep] at h
    rw [Work.FTS.LocData.DthIter_rad_eq i (Work.Spaces.dthU Work.Construction.c2m) 0 θ]
    calc |Work.Spaces.dthU^[i] (Work.Spaces.dthU Work.Construction.c2m) θ|
        ≤ C * Real.sin (2 * θ) ^ 2 := h
      _ ≤ C * Real.sin (2 * θ) := mul_le_mul_of_nonneg_left hsq (le_of_lt hCpos)

end Work.FTS.StrongEps.H5.Atoms
