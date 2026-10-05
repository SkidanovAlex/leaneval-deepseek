import Mathlib
import Submission.Work.RPB.B5.chartLev_inverse
import Submission.Work.RPB.B5.chart_C12
import Submission.Work.RPB.B5.slabDerivBounds
import Submission.Work.RPB.B5.C12.slabGlobalExtendPeriodic_C12
import Submission.Work.RPB.B5.slabExtendPeriodic
import Submission.Work.RPB.B5.halfChordSmooth
import Submission.Work.RPB.B5.chordSurf_rhoChart_full

/-!
# B5: a uniform positive lower bound for `∂_ρ chartLev` on a strip

Given the `ρ = r²`-chart `W` of the chord annulus (`W τ t (r²) = chordSurf CI.c a τ t r` for
`0 < r < π/2`), `C¹²` on the box `[0,1] × ℝ × (-ρ₀, ρ₀)` and quasi-periodic in `t`, the level
function `chartLev W τ t ρ = K₀ (W τ t ρ) + 1` has a strictly positive `ρ`-derivative at
`ρ = 0`, uniformly in `(τ, t)`:

* for `ρ > 0` the chord identity gives `chartLev W τ t ρ = ρ · ‖halfChord CI.c τ t √ρ‖²`, so the
  one-sided slope at `0⁺` tends to `‖deriv (CI.c τ) t‖² > 0` (`Work.RPB.B5.chartLev_deriv_zero`);
  the two-sided derivative at `0` exists because the slice is `C¹²` there;

* extending the level function in `τ` (`Work.RPB.B5.slabExtendPeriodic`), globalising
  (`Work.RPB.B5.C12.slabGlobalExtendPeriodic_C12`) and applying the compactness argument
  `Work.RPB.B5.slabDerivBounds`, we obtain `δ > 0` with `δ ≤ ∂_ρ chartLev` on a strip
  `Ioo (-κ) κ`, uniformly over `τ ∈ [0,1]` and all `t`.
-/

open scoped ContDiff Topology

set_option autoImplicit false

namespace Work.RPB.B5

theorem chartLev_strip_deriv_bound (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (ρ₀ : ℝ) (W : ℝ → ℝ → ℝ → Work.RPV.PS) (hρ₀ : 0 < ρ₀)
    (hW : ContDiffOn ℝ 12 (fun z : ℝ × (ℝ × ℝ) => W z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-ρ₀) ρ₀))
    (hWchord : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ r ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      W τ t (r ^ 2) = Work.RPB.chordSurf CI.c a τ t r)
    (hWper : ∀ τ t ρ, W τ (t + 2 * Real.pi) ρ = Work.RPV.Tk 1 (W τ t ρ)) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ ρ₀ ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ ρ ∈ Set.Ioo (-κ) κ,
        δ ≤ deriv (fun ρ : ℝ => Work.RPB.B5.chartLev W τ t ρ) ρ := by
  -- the even extension of the half-chord, used to evaluate the level function at `ρ = 0`
  obtain ⟨hc, hc_sm, _hc_even, _hc_per, hc_zero, hc_half⟩ :=
    halfChordSmooth CI.c CI.smooth CI.per
  -- ## (1) extend the level function from the closed box to the slab `(-1,2) × ℝ × (-ρ₀,ρ₀)`
  obtain ⟨F, hF_slab, hF_eq, hF_per⟩ :=
    slabExtendPeriodic (fun τ t ρ => chartLev W τ t ρ) 12 ρ₀ hρ₀ 1 one_pos
      (chartLev_contDiffOn_C12 hW) (fun τ t ρ => chartLev_per hWper τ t ρ)
  have htwo : (1 : ℝ) + 1 = 2 := by norm_num
  rw [htwo] at hF_slab
  -- the level function vanishes at `ρ = 0`
  have hF0 : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t, F τ t 0 = 0 := by
    intro τ hτ t
    rw [hF_eq τ hτ t 0 ⟨by linarith, hρ₀⟩]
    exact chartLev_zero hρ₀ hc hc_sm hc_half hWchord τ t
      ((chartLev_slice_contDiffOn_C12 hW τ t hτ).of_le (by norm_num)) hτ
  -- ## (2) globalise to a `C¹²` function of `(τ, t, ρ)`, still `2π`-periodic in `t`
  obtain ⟨S, hS_sm, hS_per, _hS_zero, hS_eq⟩ :=
    C12.slabGlobalExtendPeriodic_C12 (fun τ t ρ => F τ t ρ) ρ₀ hρ₀ hF_slab hF_per hF0
  -- ## (3) the `ρ`-derivative of the globalisation at `ρ = 0` is positive, uniformly in `(τ, t)`
  have hδ : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t, 0 < deriv (fun ρ => S τ t ρ) 0 := by
    intro τ hτ t
    have hagree : (fun ρ : ℝ => S τ t ρ) =ᶠ[𝓝 (0 : ℝ)]
        (fun ρ : ℝ => chartLev W τ t ρ) := by
      have hmem : Set.Ioo (-(ρ₀ / 2)) (ρ₀ / 2) ∈ 𝓝 (0 : ℝ) :=
        isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩
      filter_upwards [hmem] with ρ hρ
      rw [Set.mem_Ioo] at hρ
      rw [hS_eq τ hτ t ρ (by rw [abs_lt]; exact hρ)]
      exact hF_eq τ hτ t ρ ⟨by linarith [hρ.1], by linarith [hρ.2]⟩
    rw [Filter.EventuallyEq.deriv_eq hagree,
      chartLev_deriv_zero hρ₀ hc hc_sm hc_zero hc_half hWchord τ t
        ((chartLev_slice_contDiffOn_C12 hW τ t hτ).of_le (by norm_num)) hτ]
    exact pow_pos (norm_pos_iff.mpr (CI.imm τ hτ t)) 2
  -- ## (4) the uniform strip bound for the globalisation
  obtain ⟨ε₀, hε₀pos, δ, hδpos, _M, _hMpos, hbnd⟩ :=
    slabDerivBounds S (hS_sm.of_le (by norm_num)) hS_per hδ
  -- ## (5) transfer the bound back to the level function itself
  refine ⟨min ε₀ (ρ₀ / 2), lt_min hε₀pos (by linarith),
    le_trans (min_le_right _ _) (by linarith), δ, hδpos, ?_⟩
  intro τ hτ t ρ hρ
  rw [Set.mem_Ioo] at hρ
  have hρabs : |ρ| < min ε₀ (ρ₀ / 2) := abs_lt.mpr hρ
  have hρle : |ρ| ≤ ε₀ := le_of_lt (lt_of_lt_of_le hρabs (min_le_left _ _))
  have hρlt : |ρ| < ρ₀ / 2 := lt_of_lt_of_le hρabs (min_le_right _ _)
  -- the globalisation and the level function agree near `ρ`, hence so do their derivatives
  have hagree : (fun s : ℝ => S τ t s) =ᶠ[𝓝 ρ] (fun s : ℝ => chartLev W τ t s) := by
    have hmem : Set.Ioo (-(ρ₀ / 2)) (ρ₀ / 2) ∈ 𝓝 ρ :=
      isOpen_Ioo.mem_nhds (abs_lt.mp hρlt)
    filter_upwards [hmem] with s hs
    rw [Set.mem_Ioo] at hs
    rw [hS_eq τ hτ t s (abs_lt.mpr hs)]
    exact hF_eq τ hτ t s ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hderiv : deriv (fun s : ℝ => S τ t s) ρ = deriv (fun s : ℝ => chartLev W τ t s) ρ :=
    Filter.EventuallyEq.deriv_eq hagree
  show δ ≤ deriv (fun s : ℝ => chartLev W τ t s) ρ
  rw [← hderiv]
  exact (hbnd τ hτ t ρ (Set.mem_Icc.mpr
    ⟨by linarith [neg_abs_le ρ, hρle], by linarith [le_abs_self ρ, hρle]⟩)).1

end Work.RPB.B5
