/-
# `Work.FTS.RegPkgGal.R4c.van_zsq`

The analytic core of `van_global`: the same angular FTC bound as
`Work.FTS.RegPkgGal.R4b.van_of_dthvan`, but with the `z ^ 2` factor kept, so that it is valid
for **every** `z ≥ 0` (not only `z ≤ 2`):

  `|g z θ τ| ≤ K · z² · Γ(θ)`,  `K = Cθ · max (M/(α·c₁)) (N/(2α·c₂))`.

This is exactly the argument of `R4b.van_of_dthvan`, whose only use of `z ≤ 2` is the numerical
step `z² ≤ 4` (producing the constant `4` there).  Here that step is simply dropped: the factor
`z²` is carried along, which is legitimate because the majorants of the two halves are *linear*
in `z²` (`pth_le_majorant`, `pth_le_majorant_right` both give `Cθ·z²·(…)`), so no information
about `z` is lost when integrating in `θ`.

The slice calculus (`hasDerivAt_sliceTh`, `slice_ftc_abs_le`), the two majorants and the two
lower bounds of `Γ` are imported from `R4b` (`Submission.Work.FTS.RegPkgGal.R4b.van_of_dthvan`),
as are the two endpoint rates `primBoundLeft`, `primBoundRight` of the density `Γ/sin(2θ)`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Submission.Work.FTS.RegPkgGal.R4b.van_of_dthvan
import Submission.Work.FTS.RegPkgGal.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open Set Filter Topology MeasureTheory
open scoped Topology Real

namespace Work.FTS.RegPkgGal.R4c

open Work.FTS.RegPkgGal.R4b

set_option autoImplicit false

/-- The analytic core of `van_global`: the angular FTC bound with the `z ^ 2` factor kept, valid
for **every** `z ≥ 0` (not only `z ≤ 2`).  This is `Work.FTS.RegPkgGal.R4b.van_of_dthvan` with the
`z ≤ 2` restriction removed: the proof there in fact produces
`|g z θ τ| ≤ Cθ * z^2 * max (M / (α * c₁)) (N / (2 * α * c₂)) * Γ(θ)` for all `z ≥ 0` (the `4` in
its final constant is only `z^2 ≤ 4`), so the same argument with `z ^ 2` in place of `4` at the one
step which uses `z ≤ 2` gives this. -/
theorem van_zsq {α S Cθ : ℝ} (hα : 0 < α) (hS : 0 < S) (hCθ : 0 ≤ Cθ)
    {g : ℝ → ℝ → ℝ → ℝ}
    (hsm : ∀ τ ∈ Set.Icc 0 S,
      ContDiffOn ℝ 1 (Function.uncurry (fun z θ => g z θ τ))
        (Set.prod (Set.Ioi (-1 : ℝ)) (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1))))
    (hd : ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |Work.Spaces.Dth (Work.FTS.Regularity.gSlice g τ) z θ| ≤ Cθ * z ^ 2 * Work.FTS.Regularity.Gamma α θ)
    (hvt : ∀ τ ∈ Set.Icc 0 S, Work.Spaces.VanishTheta (Work.FTS.Regularity.gSlice g τ)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |g z θ τ| ≤ K * z ^ 2 * Work.FTS.Regularity.Gamma α θ := by
  obtain ⟨M, hM0, hM⟩ := primBoundLeft hα
  obtain ⟨N, hN0, hN⟩ := primBoundRight hα
  set c1 : ℝ := (1 / Real.pi) ^ α with hc1
  set c2 : ℝ := ((Real.sqrt 2 / 2) * (2 / Real.pi) ^ 2) ^ α with hc2
  have hc1pos : 0 < c1 := by rw [hc1]; exact Real.rpow_pos_of_pos (by positivity) _
  have hc2pos : 0 < c2 := by rw [hc2]; exact Real.rpow_pos_of_pos (by positivity) _
  have hzsq : ∀ z : ℝ, 0 ≤ z ^ 2 := fun z => sq_nonneg z
  refine ⟨Cθ * max (M / (α * c1)) (N / (2 * α * c2)), ?_, ?_⟩
  · exact mul_nonneg hCθ (le_trans (div_nonneg hM0 (by positivity)) (le_max_left _ _))
  · intro τ hτ z θ hz hθ
    have hzmem : z ∈ Set.Ioi (-1 : ℝ) := by rw [Set.mem_Ioi]; linarith
    rcases le_or_gt θ (Real.pi / 4) with hθle | hθgt
    · -- ## the left half: integrate from `0` up to `θ ≤ π/4`
      have hθ0 : 0 ≤ θ := hθ.1
      have hsub : Set.Icc (0:ℝ) θ ⊆ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1) := by
        intro x hx
        exact ⟨by linarith [hx.1], by linarith [hx.2, hθ.2, Real.pi_pos]⟩
      have hmaj_int : IntervalIntegrable (fun x : ℝ => Cθ * z ^ 2 * M * x ^ (α - 1)) volume 0 θ :=
        (intervalIntegral.intervalIntegrable_rpow' (show (-1:ℝ) < α - 1 by linarith)).const_mul _
      have hmaj : ∀ᵐ x ∂(volume.restrict (Set.Ioc (0:ℝ) θ)),
          ‖deriv (fun θ' => g z θ' τ) x‖ ≤ Cθ * z ^ 2 * M * x ^ (α - 1) := by
        filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioc] with x hx
        have hxle : x ≤ Real.pi / 4 := le_trans hx.2 hθle
        have h := pth_le_majorant hCθ (hd τ hτ) hM hz hx.1 hxle
        simpa [Work.Spaces.pth, Work.FTS.Regularity.gSlice, Real.norm_eq_abs] using h
      have hftc := slice_ftc_abs_le isOpen_Ioi isOpen_Ioo (hsm τ hτ) hzmem hθ0 hsub hmaj_int hmaj
      have hval : ∫ x in (0:ℝ)..θ, Cθ * z ^ 2 * M * x ^ (α - 1)
          = Cθ * z ^ 2 * M * (θ ^ α / α) := by
        rw [intervalIntegral.integral_const_mul,
            integral_rpow (Or.inl (show (-1:ℝ) < α - 1 by linarith)),
            show α - 1 + 1 = α by ring, Real.zero_rpow (ne_of_gt hα), sub_zero]
      have hGam : c1 * θ ^ α ≤ Work.FTS.Regularity.Gamma α θ := by
        rw [hc1]; exact Gamma_left_lb hα hθ0 hθle
      have hAc1 : θ ^ α * c1 ≤ Work.FTS.Regularity.Gamma α θ := by
        linarith [hGam, mul_comm c1 (θ ^ α)]
      have hΓ0 : 0 ≤ Work.FTS.Regularity.Gamma α θ := Work.ConstructionInstance.Gamma_nonneg hθ
      have hquot : θ ^ α / α ≤ Work.FTS.Regularity.Gamma α θ / (α * c1) := by
        rw [div_le_iff₀ (by linarith : (0:ℝ) < α),
            show Work.FTS.Regularity.Gamma α θ / (α * c1) * α
              = Work.FTS.Regularity.Gamma α θ * α / (α * c1) by ring,
            le_div_iff₀ (by positivity : (0:ℝ) < α * c1)]
        nlinarith [hAc1, hα, hc1pos]
      have hstep2 : M * (θ ^ α / α) ≤ (M / (α * c1)) * Work.FTS.Regularity.Gamma α θ := by
        have h1 := mul_le_mul_of_nonneg_left hquot hM0
        rwa [show M * (Work.FTS.Regularity.Gamma α θ / (α * c1))
              = (M / (α * c1)) * Work.FTS.Regularity.Gamma α θ by ring] at h1
      have hstep3 : (M / (α * c1)) * Work.FTS.Regularity.Gamma α θ
          ≤ max (M / (α * c1)) (N / (2 * α * c2)) * Work.FTS.Regularity.Gamma α θ :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hΓ0
      calc |g z θ τ| = |g z θ τ - g z 0 τ| := by
              rw [show g z 0 τ = 0 from (hvt τ hτ).1 z, sub_zero]
        _ ≤ ∫ x in (0:ℝ)..θ, Cθ * z ^ 2 * M * x ^ (α - 1) := hftc
        _ = Cθ * z ^ 2 * M * (θ ^ α / α) := hval
        _ = Cθ * z ^ 2 * (M * (θ ^ α / α)) := by ring
        _ ≤ Cθ * z ^ 2 * ((M / (α * c1)) * Work.FTS.Regularity.Gamma α θ) :=
              mul_le_mul_of_nonneg_left hstep2 (mul_nonneg hCθ (hzsq z))
        _ ≤ Cθ * z ^ 2 * (max (M / (α * c1)) (N / (2 * α * c2))
              * Work.FTS.Regularity.Gamma α θ) :=
              mul_le_mul_of_nonneg_left hstep3 (mul_nonneg hCθ (hzsq z))
        _ = (Cθ * max (M / (α * c1)) (N / (2 * α * c2))) * z ^ 2
              * Work.FTS.Regularity.Gamma α θ := by ring
    · -- ## the right half: integrate from `θ > π/4` up to `π/2`
      have hθpi2 : θ ≤ Real.pi / 2 := hθ.2
      have hsub : Set.Icc θ (Real.pi / 2) ⊆ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1) := by
        intro x hx
        exact ⟨by linarith [hx.1, Real.pi_pos], by linarith [hx.2, Real.pi_pos]⟩
      have hbase : IntervalIntegrable (fun x : ℝ => x ^ (2 * α - 1)) volume 0 (Real.pi / 2 - θ) :=
        intervalIntegral.intervalIntegrable_rpow' (show (-1:ℝ) < 2 * α - 1 by linarith)
      have hcomp : IntervalIntegrable (fun x : ℝ => (Real.pi / 2 - x) ^ (2 * α - 1))
          volume (Real.pi / 2) θ := by
        have h' := hbase.comp_sub_left (Real.pi / 2)
        rw [sub_zero, show Real.pi / 2 - (Real.pi / 2 - θ) = θ by ring] at h'
        exact h'
      have hmaj_int : IntervalIntegrable
          (fun x : ℝ => Cθ * z ^ 2 * N * (Real.pi / 2 - x) ^ (2 * α - 1)) volume θ (Real.pi / 2) :=
        (hcomp.symm).const_mul _
      have hmaj : ∀ᵐ x ∂(volume.restrict (Set.Ioc θ (Real.pi / 2))),
          ‖deriv (fun θ' => g z θ' τ) x‖ ≤ Cθ * z ^ 2 * N * (Real.pi / 2 - x) ^ (2 * α - 1) := by
        rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
        have hae : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ Real.pi / 2 := by
          rw [MeasureTheory.ae_iff]
          simp only [ne_eq, not_not, Set.ofPred_eq_eq_singleton]
          exact MeasureTheory.measure_singleton _
        filter_upwards [hae] with x hx hxmem
        have hx1 : Real.pi / 4 ≤ x := le_trans (le_of_lt hθgt) hxmem.1.le
        have hx2 : x < Real.pi / 2 := lt_of_le_of_ne hxmem.2 hx
        have h := pth_le_majorant_right hCθ (hd τ hτ) hN hz hx1 hx2
        simpa [Work.Spaces.pth, Work.FTS.Regularity.gSlice, Real.norm_eq_abs] using h
      have hftc := slice_ftc_abs_le isOpen_Ioi isOpen_Ioo (hsm τ hτ) hzmem hθpi2 hsub hmaj_int hmaj
      have hval : ∫ x in θ..(Real.pi / 2), Cθ * z ^ 2 * N * (Real.pi / 2 - x) ^ (2 * α - 1)
          = Cθ * z ^ 2 * N * ((Real.pi / 2 - θ) ^ (2 * α) / (2 * α)) := by
        rw [intervalIntegral.integral_const_mul]
        congr 1
        rw [intervalIntegral.integral_comp_sub_left (fun s : ℝ => s ^ (2 * α - 1)) (Real.pi / 2),
            show Real.pi / 2 - Real.pi / 2 = 0 by ring,
            integral_rpow (Or.inl (show (-1:ℝ) < 2 * α - 1 by linarith)),
            show 2 * α - 1 + 1 = 2 * α by ring,
            Real.zero_rpow (by linarith : 2 * α ≠ 0), sub_zero]
      have hσ0 : 0 ≤ Real.pi / 2 - θ := by linarith [hθpi2]
      have hσle : Real.pi / 2 - θ ≤ Real.pi / 4 := by linarith [hθgt]
      have hGam : c2 * (Real.pi / 2 - θ) ^ (2 * α) ≤ Work.FTS.Regularity.Gamma α θ := by
        have h := Gamma_right_lb hα hσ0 hσle
        rwa [show Real.pi / 2 - (Real.pi / 2 - θ) = θ by ring] at h
      have hAc2 : (Real.pi / 2 - θ) ^ (2 * α) * c2 ≤ Work.FTS.Regularity.Gamma α θ := by
        linarith [hGam, mul_comm c2 ((Real.pi / 2 - θ) ^ (2 * α))]
      have hΓ0 : 0 ≤ Work.FTS.Regularity.Gamma α θ := Work.ConstructionInstance.Gamma_nonneg hθ
      have hquot : (Real.pi / 2 - θ) ^ (2 * α) / (2 * α)
          ≤ Work.FTS.Regularity.Gamma α θ / (2 * α * c2) := by
        rw [div_le_iff₀ (by linarith : (0:ℝ) < 2 * α),
            show Work.FTS.Regularity.Gamma α θ / (2 * α * c2) * (2 * α)
              = Work.FTS.Regularity.Gamma α θ * (2 * α) / (2 * α * c2) by ring,
            le_div_iff₀ (by positivity : (0:ℝ) < 2 * α * c2)]
        nlinarith [hAc2, hα, hc2pos]
      have hstep2 : N * ((Real.pi / 2 - θ) ^ (2 * α) / (2 * α))
          ≤ (N / (2 * α * c2)) * Work.FTS.Regularity.Gamma α θ := by
        have h1 := mul_le_mul_of_nonneg_left hquot hN0
        rwa [show N * (Work.FTS.Regularity.Gamma α θ / (2 * α * c2))
              = (N / (2 * α * c2)) * Work.FTS.Regularity.Gamma α θ by ring] at h1
      have hstep3 : (N / (2 * α * c2)) * Work.FTS.Regularity.Gamma α θ
          ≤ max (M / (α * c1)) (N / (2 * α * c2)) * Work.FTS.Regularity.Gamma α θ :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) hΓ0
      calc |g z θ τ| = |g z (Real.pi / 2) τ - g z θ τ| := by
              rw [show g z (Real.pi / 2) τ = 0 from (hvt τ hτ).2 z, zero_sub, abs_neg]
        _ ≤ ∫ x in θ..(Real.pi / 2), Cθ * z ^ 2 * N * (Real.pi / 2 - x) ^ (2 * α - 1) := hftc
        _ = Cθ * z ^ 2 * N * ((Real.pi / 2 - θ) ^ (2 * α) / (2 * α)) := hval
        _ = Cθ * z ^ 2 * (N * ((Real.pi / 2 - θ) ^ (2 * α) / (2 * α))) := by ring
        _ ≤ Cθ * z ^ 2 * ((N / (2 * α * c2)) * Work.FTS.Regularity.Gamma α θ) :=
              mul_le_mul_of_nonneg_left hstep2 (mul_nonneg hCθ (hzsq z))
        _ ≤ Cθ * z ^ 2 * (max (M / (α * c1)) (N / (2 * α * c2))
              * Work.FTS.Regularity.Gamma α θ) :=
              mul_le_mul_of_nonneg_left hstep3 (mul_nonneg hCθ (hzsq z))
        _ = (Cθ * max (M / (α * c1)) (N / (2 * α * c2))) * z ^ 2
              * Work.FTS.Regularity.Gamma α θ := by ring

end Work.FTS.RegPkgGal.R4c
