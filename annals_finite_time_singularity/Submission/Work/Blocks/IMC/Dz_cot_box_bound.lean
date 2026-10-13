/-
Copyright: work module for the Elgindi finite-time singularity project.

# The box bound `|D_z G · cot(2θ)| ≤ M` on `[δ,R] × [0,π/2]`

For `G` smooth on the open strip `(0,∞) × (-1, π/2+1)` which vanishes on the two angular
boundary segments `θ = 0` and `θ = π/2`, the product `D_z G · cot(2θ)` is bounded on the
closed box `[δ,R] × [0,π/2]` (`0 < δ < R`).

The two singularities are of different nature:

* the factor `cot(2θ)` blows up like `1/(2θ)` at the two endpoints, while `θ ↦ D_z G(z,θ)`
  is `C¹` there and vanishes at `θ = 0, π/2`: indeed `G(z,0) = G(z,π/2) = 0` for *every* `z`,
  so `∂_z G(z,0) = ∂_z G(z,π/2) = 0` as well.  The mean value estimate
  `Dz_le_mul_min` therefore gives `|D_z G(z,θ)| ≤ M · min θ (π/2 - θ)` on the box;
* the angular factor is compensated by `SinMinBounds`: `|cot 2θ| · min θ (π/2-θ) ≤ K`.

The constant `M` is the sup of `|D_z ∂_θ G|` on the compact box, finite by compactness (the
box lies in the open strip, where `D_z ∂_θ G` is continuous); `abs_Dz_mul_cot_le` assembles
the two estimates.

This file is deliberately self-contained: the lemmas `abs_Dz_le_mul_min`,
`abs_cot_mul_min_le`, `abs_Dz_mul_cot_le` below duplicate (with the plain `∀ n, ContDiffOn ℝ n`
smoothness hypothesis in place of the `RPFresh.SmoothStrip` abbreviation) the statements of
`Work.FTS.EllipticEst.RPFresh.InterpCompact`, in order to keep the trust surface small.
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.H2.STBasic
import Submission.Work.FTS.EllipticEst.ThetaU.K1Aux
import Submission.Work.Spaces.SinMinBounds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Blocks.IMC

set_option autoImplicit false

/-- The box `[δ,R] × [0,π/2]` is contained in the open strip `(0,∞) × (-1, π/2+1)` of
smoothness. -/
theorem icc_prod_Iθ_subset_OStrip {δ R : ℝ} (hδ : 0 < δ) :
    Set.Icc δ R ×ˢ Work.Spaces.Iθ ⊆ Work.FTS.EllipticEst.ThetaU.OStrip := by
  intro p hp
  obtain ⟨hp1, hp2⟩ := hp
  exact ⟨lt_of_lt_of_le hδ hp1.1,
    ⟨by linarith [hp2.1], by linarith [hp2.2, Real.pi_pos]⟩⟩

/-- The `θ`-slice `θ ↦ D_zG z θ` is smooth near the closed interval, for `z > 0`. -/
theorem contDiffOn_slice_Dz {G : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry G)
      (Work.FTS.EllipticEst.ThetaU.OStrip))
    {z : ℝ} (hz : 0 < z) (n : ℕ) :
    ContDiffOn ℝ n (fun θ : ℝ => Work.Spaces.Dz G z θ)
      (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) := by
  have hmap : Set.MapsTo (fun θ : ℝ => (z, θ))
      (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) Work.FTS.EllipticEst.ThetaU.OStrip :=
    fun θ hθ => ⟨hz, hθ⟩
  have h := (Work.FTS.EllipticEst.ThetaU.contDiffOn_uncurry_Dz_fin (n := n)
      (hsm (n + 1))).comp (contDiffOn_const.prodMk contDiffOn_id) hmap
  simpa only [Function.comp_def, id_eq, Function.uncurry] using h

/-- On the box, `|D_zG z θ| ≤ M · min θ (π/2 - θ)` whenever `M` bounds
`∂_θ(D_zG) = D_z(∂_θG)` there: `D_zG(z,·)` vanishes at `θ = 0, π/2` (because
`G(·,0) = G(·,π/2) = 0` identically in `z`), so the mean value bound on each half of
`Iθ` gives `|D_zG z θ| ≤ M·θ` and `|D_zG z θ| ≤ M·(π/2 - θ)`. -/
theorem Dz_le_mul_min {G : ℝ → ℝ → ℝ} {δ R M : ℝ} (hδ : 0 < δ)
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry G)
      (Work.FTS.EllipticEst.ThetaU.OStrip))
    (h0 : ∀ z : ℝ, G z 0 = 0) (h1 : ∀ z : ℝ, G z (Real.pi / 2) = 0)
    (hM : ∀ z ∈ Set.Icc δ R, ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.Dz (Work.Spaces.pth G) z θ| ≤ M) :
    ∀ z ∈ Set.Icc δ R, ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.Dz G z θ| ≤ M * min θ (Real.pi / 2 - θ) := by
  have hIθ_sub : ∀ θ ∈ Work.Spaces.Iθ, θ ∈ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1) := fun θ hθ =>
    ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  have hDz0 : ∀ z : ℝ, Work.Spaces.Dz G z 0 = 0 := by
    intro z
    show z * Work.Spaces.pz G z 0 = 0
    have hfun : (fun z' : ℝ => G z' 0) = fun _ => (0 : ℝ) := funext fun z' => h0 z'
    rw [show Work.Spaces.pz G z 0 = deriv (fun z' : ℝ => G z' 0) z from rfl, hfun, deriv_const,
      mul_zero]
  have hDzπ : ∀ z : ℝ, Work.Spaces.Dz G z (Real.pi / 2) = 0 := by
    intro z
    show z * Work.Spaces.pz G z (Real.pi / 2) = 0
    have hfun : (fun z' : ℝ => G z' (Real.pi / 2)) = fun _ => (0 : ℝ) := funext fun z' => h1 z'
    rw [show Work.Spaces.pz G z (Real.pi / 2)
        = deriv (fun z' : ℝ => G z' (Real.pi / 2)) z from rfl, hfun, deriv_const, mul_zero]
  intro z hz θ hθ
  have hz0 : 0 < z := lt_of_lt_of_le hδ hz.1
  have hleft : |Work.Spaces.Dz G z θ| ≤ M * θ := by
    have hcd : ContDiffOn ℝ 1 (fun s : ℝ => Work.Spaces.Dz G z s) (Set.uIcc (0 : ℝ) θ) := by
      rw [Set.uIcc_of_le hθ.1]
      exact (contDiffOn_slice_Dz hsm hz0 1).mono (fun s hs =>
        ⟨by linarith [hs.1], by linarith [hs.2, hθ.2, Real.pi_pos]⟩)
    have hFTC : (∫ s in (0 : ℝ)..θ, deriv (fun s : ℝ => Work.Spaces.Dz G z s) s)
        = Work.Spaces.Dz G z θ := by
      rw [intervalIntegral.integral_deriv_of_contDiffOn_uIcc hcd, hDz0 z, sub_zero]
    have hbound : ∀ s ∈ Set.uIoc (0 : ℝ) θ,
        ‖deriv (fun s : ℝ => Work.Spaces.Dz G z s) s‖ ≤ M := by
      intro s hs
      rw [Set.uIoc_of_le hθ.1, Set.mem_Ioc] at hs
      have hsI : s ∈ Work.Spaces.Iθ := ⟨le_of_lt hs.1, le_trans hs.2 hθ.2⟩
      rw [Real.norm_eq_abs, show deriv (fun s : ℝ => Work.Spaces.Dz G z s) s
          = Work.Spaces.pth (Work.Spaces.Dz G) z s from rfl,
        Work.FTS.EllipticEst.ThetaU.pth_Dz_eq ((hsm 2).contDiffAt
          ((isOpen_Ioi.prod isOpen_Ioo).mem_nhds ⟨hz0, hIθ_sub s hsI⟩))]
      exact hM z hz s hsI
    have h3 := intervalIntegral.norm_integral_le_of_norm_le_const hbound
    rw [sub_zero] at h3
    have h2 : |(∫ s in (0 : ℝ)..θ, deriv (fun s : ℝ => Work.Spaces.Dz G z s) s)| ≤ M * θ := by
      simpa only [Real.norm_eq_abs, abs_of_nonneg hθ.1] using h3
    rwa [hFTC] at h2
  have hright : |Work.Spaces.Dz G z θ| ≤ M * (Real.pi / 2 - θ) := by
    have hcd : ContDiffOn ℝ 1 (fun s : ℝ => Work.Spaces.Dz G z s)
        (Set.uIcc θ (Real.pi / 2)) := by
      rw [Set.uIcc_of_le hθ.2]
      exact (contDiffOn_slice_Dz hsm hz0 1).mono (fun s hs =>
        ⟨by linarith [hs.1, hθ.1], by linarith [hs.2, Real.pi_pos]⟩)
    have hFTC : (∫ s in θ..(Real.pi / 2), deriv (fun s : ℝ => Work.Spaces.Dz G z s) s)
        = -Work.Spaces.Dz G z θ := by
      rw [intervalIntegral.integral_deriv_of_contDiffOn_uIcc hcd, hDzπ z]
      ring
    have hbound : ∀ s ∈ Set.uIoc θ (Real.pi / 2),
        ‖deriv (fun s : ℝ => Work.Spaces.Dz G z s) s‖ ≤ M := by
      intro s hs
      rw [Set.uIoc_of_le hθ.2, Set.mem_Ioc] at hs
      have hsI : s ∈ Work.Spaces.Iθ := ⟨le_trans hθ.1 hs.1.le, hs.2⟩
      rw [Real.norm_eq_abs, show deriv (fun s : ℝ => Work.Spaces.Dz G z s) s
          = Work.Spaces.pth (Work.Spaces.Dz G) z s from rfl,
        Work.FTS.EllipticEst.ThetaU.pth_Dz_eq ((hsm 2).contDiffAt
          ((isOpen_Ioi.prod isOpen_Ioo).mem_nhds ⟨hz0, hIθ_sub s hsI⟩))]
      exact hM z hz s hsI
    have h3 := intervalIntegral.norm_integral_le_of_norm_le_const hbound
    have h2 : |(∫ s in θ..(Real.pi / 2),
        deriv (fun s : ℝ => Work.Spaces.Dz G z s) s)| ≤ M * (Real.pi / 2 - θ) := by
      simpa only [Real.norm_eq_abs,
        abs_of_nonneg (by linarith [hθ.2] : (0 : ℝ) ≤ Real.pi / 2 - θ)] using h3
    rw [hFTC, abs_neg] at h2
    exact h2
  rcases le_total θ (Real.pi / 2 - θ) with h | h
  · rw [min_eq_left h]; exact hleft
  · rw [min_eq_right h]; exact hright

/-- `|cot(2θ)| · min θ (π/2 - θ)` is bounded on `Iθ`: this is `Work.Spaces.SinMinBounds`
for the exponent `1` combined with `|cos| ≤ 1`. -/
theorem abs_cot_mul_min_le {K : ℝ}
    (hK : ∀ θ ∈ Work.Spaces.Iθ,
      min θ (Real.pi / 2 - θ) * (Real.sin (2 * θ)) ^ (-(1 : ℝ)) ≤ K) :
    ∀ θ ∈ Work.Spaces.Iθ, |Real.cot (2 * θ)| * min θ (Real.pi / 2 - θ) ≤ K := by
  have hK0 : 0 ≤ K := by
    have h := hK 0 ⟨le_rfl, by linarith [Real.pi_pos]⟩
    have hz : min 0 (Real.pi / 2 - 0) * (Real.sin (2 * 0)) ^ (-(1 : ℝ)) = 0 := by
      have h1 : min 0 (Real.pi / 2 - 0) = 0 :=
        min_eq_left (by linarith [Real.pi_pos] : (0 : ℝ) ≤ Real.pi / 2 - 0)
      rw [h1, zero_mul]
    rw [hz] at h
    exact h
  intro θ hθ
  rcases eq_or_lt_of_le hθ.1 with h0 | h0
  · subst h0
    have hzero : |Real.cot (2 * 0)| * min 0 (Real.pi / 2 - 0) = 0 := by
      rw [mul_zero, Real.cot_eq_cos_div_sin, Real.sin_zero, div_zero, abs_zero, zero_mul]
    rw [hzero]; exact hK0
  rcases eq_or_lt_of_le hθ.2 with hpi | hpi
  · subst hpi
    have harg : 2 * (Real.pi / 2) = Real.pi := by ring
    have hzero : |Real.cot (2 * (Real.pi / 2))| * min (Real.pi / 2) (Real.pi / 2 - Real.pi / 2)
        = 0 := by
      rw [harg, Real.cot_eq_cos_div_sin, Real.sin_pi, div_zero, abs_zero, zero_mul]
    rw [hzero]; exact hK0
  have hsin : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [h0]) (by linarith [hpi, Real.pi_pos])
  have h1 : |Real.cot (2 * θ)| ≤ 1 / Real.sin (2 * θ) := by
    rw [Real.cot_eq_cos_div_sin, abs_div, abs_of_pos hsin]
    exact div_le_div_of_nonneg_right (Real.abs_cos_le_one _) hsin.le
  have hmin : 0 ≤ min θ (Real.pi / 2 - θ) := le_min hθ.1 (by linarith [hθ.2])
  calc |Real.cot (2 * θ)| * min θ (Real.pi / 2 - θ)
      ≤ (1 / Real.sin (2 * θ)) * min θ (Real.pi / 2 - θ) :=
        mul_le_mul_of_nonneg_right h1 hmin
    _ = min θ (Real.pi / 2 - θ) * (Real.sin (2 * θ)) ^ (-(1 : ℝ)) := by
        rw [Real.rpow_neg hsin.le, Real.rpow_one]; ring
    _ ≤ K := hK θ hθ

/-- On the box, `|D_zG · cot(2θ)|` is bounded by `M · K`. -/
theorem abs_Dz_mul_cot_le {G : ℝ → ℝ → ℝ} {δ R M K : ℝ} (hδ : 0 < δ)
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry G)
      (Work.FTS.EllipticEst.ThetaU.OStrip))
    (h0 : ∀ z : ℝ, G z 0 = 0) (h1 : ∀ z : ℝ, G z (Real.pi / 2) = 0)
    (hM : ∀ z ∈ Set.Icc δ R, ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.Dz (Work.Spaces.pth G) z θ| ≤ M)
    (hK : ∀ θ ∈ Work.Spaces.Iθ,
      min θ (Real.pi / 2 - θ) * (Real.sin (2 * θ)) ^ (-(1 : ℝ)) ≤ K)
    (hM0 : 0 ≤ M) :
    ∀ z ∈ Set.Icc δ R, ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.Dz G z θ * Real.cot (2 * θ)| ≤ M * K := by
  intro z hz θ hθ
  have h1 := Dz_le_mul_min hδ hsm h0 h1 hM z hz θ hθ
  have h2 := abs_cot_mul_min_le hK θ hθ
  rw [abs_mul]
  calc |Work.Spaces.Dz G z θ| * |Real.cot (2 * θ)|
      ≤ (M * min θ (Real.pi / 2 - θ)) * |Real.cot (2 * θ)| :=
        mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
    _ = M * (|Real.cot (2 * θ)| * min θ (Real.pi / 2 - θ)) := by ring
    _ ≤ M * K := mul_le_mul_of_nonneg_left h2 hM0

/-- The compact quantity `D_z ∂_θ G` is bounded on the box, by compactness of the box and
continuity on the ambient open strip. -/
theorem exists_box_bound_Dz_pth {δ R : ℝ} (hδ : 0 < δ) (hδR : δ < R) {G : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry G)
      (Work.FTS.EllipticEst.ThetaU.OStrip)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z ∈ Set.Icc δ R, ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.Dz (Work.Spaces.pth G) z θ| ≤ M := by
  have hpth : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pth G))
      Work.FTS.EllipticEst.ThetaU.OStrip :=
    Work.FTS.EllipticEst.ThetaU.contDiffOn_uncurry_pth_fin (n := 1) (hsm 2)
  have hDz : ContDiffOn ℝ 0 (Function.uncurry (Work.Spaces.Dz (Work.Spaces.pth G)))
      Work.FTS.EllipticEst.ThetaU.OStrip :=
    Work.FTS.EllipticEst.ThetaU.contDiffOn_uncurry_Dz_fin (n := 0) hpth
  have hcont : ContinuousOn (Function.uncurry (Work.Spaces.Dz (Work.Spaces.pth G)))
      (Set.Icc δ R ×ˢ Work.Spaces.Iθ) :=
    hDz.continuousOn.mono (icc_prod_Iθ_subset_OStrip hδ)
  have hcomp : IsCompact (Set.Icc δ R ×ˢ Work.Spaces.Iθ) :=
    isCompact_Icc.prod isCompact_Icc
  obtain ⟨M, hM⟩ := hcomp.exists_bound_of_continuousOn hcont
  refine ⟨M, ?_, ?_⟩
  · have hx : (δ, (0 : ℝ)) ∈ Set.Icc δ R ×ˢ Work.Spaces.Iθ :=
      ⟨⟨le_rfl, le_of_lt hδR⟩, ⟨le_rfl, by linarith [Real.pi_pos]⟩⟩
    exact le_trans (norm_nonneg _) (hM (δ, 0) hx)
  · intro z hz θ hθ
    simpa only [Function.uncurry, Real.norm_eq_abs] using hM (z, θ) ⟨hz, hθ⟩

theorem Dz_cot_box_bound {δ R : ℝ} (hδ : 0 < δ) (hδR : δ < R) {G : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry G) (Work.FTS.EllipticEst.ThetaU.OStrip))
    (h0 : ∀ z, G z 0 = 0) (hπ : ∀ z, G z (Real.pi / 2) = 0) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z ∈ Set.Icc δ R, ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.Dz G z θ * Real.cot (2 * θ)| ≤ M := by
  obtain ⟨M, hM0, hM⟩ := exists_box_bound_Dz_pth hδ hδR hsm
  obtain ⟨K, hKpos, hK⟩ := Work.Spaces.SinMinBounds 1 (by norm_num) (by norm_num)
  exact ⟨M * K, mul_nonneg hM0 hKpos.le, fun z hz θ hθ =>
    abs_Dz_mul_cot_le (M := M) (K := K) hδ hsm h0 hπ hM hK hM0 z hz θ hθ⟩

end Work.Blocks.IMC
