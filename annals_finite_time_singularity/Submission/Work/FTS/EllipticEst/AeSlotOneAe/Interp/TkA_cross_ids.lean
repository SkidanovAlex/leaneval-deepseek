import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.AeSlotOneAe.Interp.TkA_cross_defs
import Submission.Work.FTS.EllipticEst.H2W.AeDataAof
import Submission.Work.FTS.EllipticEst.H2W.slot11_src_int
import Submission.Work.EllipticEst.H2W.pthIter2_DzIter_comm

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AeSlotOneAe.Interp

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## The angular unfolding of the `Tk`-slot -/

/-- **The pointwise unfolding of the top slot of `Tk` at level `1`.**  On `Iθ` the `γ`-weighted
square of `D_θ f` equals the `σ`-weighted square of `∂_θ f`:
`(D_θ f · Wt α)² = (∂_θ f)² · w² · σ`. -/
theorem Tk_slot_eq {α : ℝ} (hα0 : 0 < α) (hα : α ≤ 1 / 4) (f : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.mixed 0 1 f z θ * Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.pth f z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * sigA α θ := by
  have hs : 0 ≤ Real.sin (2 * θ) := Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1],
    by linarith [hθ.2, Real.pi_pos]⟩
  have hunfold : Work.Spaces.mixed 0 1 f z θ * Work.Spaces.Wt α z θ
      = (Real.sin (2 * θ) * Work.Spaces.pth f z θ)
        * (Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) := by
    simp only [Work.Spaces.mixed, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_succ,
      Work.Spaces.DthIter_zero, Work.Spaces.Dth, Work.Spaces.Wt, Work.Spaces.wTheta]
  rw [hunfold, sigA]
  rcases eq_or_lt_of_le hs with h | h
  · have hg : 0 < Work.Spaces.gam α / 2 := by
      have h := Work.Spaces.gam_pos hα0
      linarith
    have h1 : (-(Work.Spaces.gam α / 2)) ≠ 0 := neg_ne_zero.mpr (ne_of_gt hg)
    have h2 : 2 - Work.Spaces.gam α ≠ 0 := by
      have h := Work.Spaces.gam_sub_one α
      intro hc
      linarith
    rw [← h, Real.zero_rpow h1, Real.zero_rpow h2]
    ring
  · have hsq : (Real.sin (2 * θ) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2
        = (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) := by
      have h2 : Real.sin (2 * θ) * Real.sin (2 * θ)
          = (Real.sin (2 * θ)) ^ ((2 : ℕ) : ℝ) := by
        rw [Real.rpow_natCast, pow_two]
      have h3 : (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))
          = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
        rw [← Real.rpow_add h,
          show -(Work.Spaces.gam α / 2) + -(Work.Spaces.gam α / 2)
            = -(Work.Spaces.gam α) by ring]
      calc (Real.sin (2 * θ) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2
          = (Real.sin (2 * θ) * Real.sin (2 * θ))
              * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))
                * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) := by ring
        _ = (Real.sin (2 * θ)) ^ ((2 : ℕ) : ℝ)
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by rw [h2, h3]
        _ = (Real.sin (2 * θ)) ^ (((2 : ℕ) : ℝ) + -(Work.Spaces.gam α)) := by
              rw [Real.rpow_add h]
        _ = (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) := rfl
    rw [show (Real.sin (2 * θ) * Work.Spaces.pth f z θ
          * (Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2)))) ^ 2
        = (Work.Spaces.pth f z θ * Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2
        from by ring, hsq, mul_pow]

/-- **The integral form of the unfolding**: `Tk α 1 f` is the `σ`-weighted square of `∂_θ f`. -/
theorem Tk_eq {α : ℝ} (hα0 : 0 < α) (hα : α ≤ 1 / 4) (f : ℝ → ℝ → ℝ) :
    Work.FTS.EllipticEst.remov.Step.Tk α 1 f
      = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.pth f z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * sigA α θ := by
  rw [Work.FTS.EllipticEst.remov.Step.Tk]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
  exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => Tk_slot_eq hα0 hα f hθ)

/-! ## The three operator identities on the open quadrant -/

/-- `A' = D_z A` on the open quadrant. -/
theorem A1z_eqOn_Dz {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    Set.EqOn (Function.uncurry (A1z Ψ)) (Function.uncurry (Work.Spaces.DzIter 1 (Az Ψ)))
      Work.FTS.EllipticEst.Q0 := by
  rintro ⟨z, θ⟩ hp
  obtain ⟨hz, hθ, hlt⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
  change A1z Ψ z θ = z * Work.Spaces.pz (Az Ψ) z θ
  rw [show (Az Ψ) = fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ from rfl,
      show A1z Ψ = fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ
        from rfl]
  exact (Work.FTS.EllipticEst.H2W.dz_zsq_pzIter2_eq hΨ hz ⟨hθ, hlt⟩).symm

/-- `H = D_z B - B` on the open quadrant. -/
theorem Hz_eqOn {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    Set.EqOn (Function.uncurry (Hz Ψ))
      (Function.uncurry (fun z θ => Work.Spaces.Dz (Bz Ψ) z θ - Bz Ψ z θ))
      Work.FTS.EllipticEst.Q0 := by
  rintro ⟨z, θ⟩ hp
  obtain ⟨hz, hθ, hlt⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
  change Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ) z θ - Work.Spaces.pthIter 2 Ψ z θ
      = Work.Spaces.Dz (Bz Ψ) z θ - Bz Ψ z θ
  have h := Work.EllipticEst.H2W.pthIter2_DzIter_comm hΨ 1
    (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ, hlt⟩)
  simp only [Function.uncurry] at h
  rw [h]
  rfl

/-- **The cross identity** `∂_θ²A = z ∂_z H` on the open quadrant. -/
theorem pth2_Az_eqOn {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    Set.EqOn (Function.uncurry (fun z θ => Work.Spaces.pthIter 2 (Az Ψ) z θ))
      (Function.uncurry (fun z θ => z * Work.Spaces.pz (Hz Ψ) z θ))
      Work.FTS.EllipticEst.Q0 := by
  rintro ⟨z, θ⟩ hp
  obtain ⟨hz, hθ, hlt⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
  have hθ' : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ, hlt⟩
  have hpth2 : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 Ψ) :=
    Work.FTS.EllipticEst.SmoothOpen.pth (Work.FTS.EllipticEst.SmoothOpen.pth hΨ)
  change Work.Spaces.pthIter 2 (Az Ψ) z θ = z * Work.Spaces.pz (Hz Ψ) z θ
  -- the left-hand side is `z² ∂_z²(∂_θ²Ψ)`
  have hL : Work.Spaces.pthIter 2 (Az Ψ) z θ
      = z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.pthIter 2 Ψ) z θ :=
    Work.FTS.EllipticEst.H2W.AeDataAofAux.pthIter_two_zsq_pzIter2_eq hΨ hz hθ'
  -- the `z`-slice of `H` agrees with `z ↦ z ∂_z(∂_θ²Ψ) - ∂_θ²Ψ` near `z`
  have hev : (fun z' : ℝ => Hz Ψ z' θ)
      =ᶠ[𝓝 z] (fun z' : ℝ => z' * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z' θ
        - Work.Spaces.pthIter 2 Ψ z' θ) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
    have h := Work.EllipticEst.H2W.pthIter2_DzIter_comm hΨ 1
      (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz', hθ, hlt⟩)
    simp only [Function.uncurry] at h
    change Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ) z' θ - Work.Spaces.pthIter 2 Ψ z' θ
        = z' * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z' θ - Work.Spaces.pthIter 2 Ψ z' θ
    rw [h]
    rfl
  have hderiv : HasDerivAt (fun z' : ℝ => z' * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z' θ
      - Work.Spaces.pthIter 2 Ψ z' θ)
      (z * Work.Spaces.pzIter 2 (Work.Spaces.pthIter 2 Ψ) z θ) z := by
    have h1 : HasDerivAt (fun z' : ℝ => z') (1 : ℝ) z := hasDerivAt_id z
    have h2 : HasDerivAt (fun z' : ℝ => Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z' θ)
        (Work.Spaces.pzIter 2 (Work.Spaces.pthIter 2 Ψ) z θ) z :=
      Work.FTS.EllipticEst.SmoothOpen.hasDerivAt_slice_pzIter hpth2 1 hθ' hz
    have h3 : HasDerivAt (fun z' : ℝ => Work.Spaces.pthIter 2 Ψ z' θ)
        (Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ) z :=
      Work.FTS.EllipticEst.SmoothOpen.hasDerivAt_slice hpth2 hθ' hz
    convert (h1.mul h2).sub h3 using 1
    ring
  rw [hL, show Work.Spaces.pz (Hz Ψ) z θ = deriv (fun z' : ℝ => Hz Ψ z' θ) z from rfl,
    Filter.EventuallyEq.deriv_eq hev, hderiv.deriv]
  ring

end Work.FTS.EllipticEst.AeSlotOneAe.Interp
