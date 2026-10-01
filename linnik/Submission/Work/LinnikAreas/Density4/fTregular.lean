import Mathlib
import Submission.Work.LinnikAreas.Density4.TestFun
import Submission.Work.LinnikAreas.Density4.testfun_basic
import Submission.Work.LinnikAreas.Density4.testfun_lapl_pos

namespace Work.LinnikAreas.Density4

/-- On its support `[0, 2γ]` the closed form `fTclosed` agrees with `fT`, and at the right endpoint
`2γ` (i.e. `ζx = 2θ`) the trigonometric bracket `brT` vanishes; hence `fTclosed 2γ = 0`.  This is
what makes `fT` continuous at `2γ` and supported there. -/
lemma fTclosed_two_gammaT {θ lam : ℝ} (hθ1 : Real.pi / 2 < θ) (hθ2 : θ < Real.pi)
    (hlam : 0 < lam) : fTclosed θ lam (2 * gammaT θ lam) = 0 := by
  have hζ := zetaT_pos hθ1 hθ2 hlam
  rw [fTclosed_eq_bracketT θ lam _ (ne_of_gt hζ), zetaT_mul_two_gammaT (ne_of_gt hζ)]
  have h : bracketT θ (2 * θ) = 0 := by
    rw [show bracketT θ (2 * θ) = brT θ (2 * θ) from rfl, brT_two_theta]
  rw [h, zero_div, mul_zero]

/-- **HB §12**: regularity of the §7 test function on the half-line `[0,∞)`.  For `π/2 < θ < π`
and `λ̂ > 0` the clamped closed form `fT` is

* continuous on `[0,∞)` (it agrees with the continuous `fTclosed` on `[0,2γ]` and vanishes on
  `[2γ,∞)`, the two pieces matching at `2γ` since `fTclosed 2γ = 0`);
* strictly positive at `0` (the bracket `brT θ 0 = θ(1+2cos²θ) - 3 sinθ cosθ` is positive);
* `C²` on the open interval `(0,2γ)`, where it is the smooth trigonometric polynomial `fTclosed`;
* with bounded second derivative on `(0,2γ)`, by compactness of `[0,2γ]` and continuity there. -/
theorem fTregular {θ lam : ℝ} (hθ1 : Real.pi / 2 < θ) (hθ2 : θ < Real.pi) (hlam : 0 < lam) :
    ContinuousOn (fT θ lam) (Set.Ici 0) ∧
    0 < fT θ lam 0 ∧
    ContDiffOn ℝ 2 (fT θ lam) (Set.Ioo (0:ℝ) (2 * gammaT θ lam)) ∧
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Set.Ioo (0:ℝ) (2 * gammaT θ lam),
      ‖iteratedDeriv 2 (fT θ lam) t‖ ≤ B := by
  have hγ := gammaT_pos hθ1 hθ2 hlam
  have h2γ : 0 < 2 * gammaT θ lam := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- continuity on `[0,∞)`: glue `[0,2γ]` (where `fT = fTclosed`) to `[2γ,∞)` (where `fT = 0`)
    have hA : ContinuousOn (fT θ lam) (Set.Icc 0 (2 * gammaT θ lam)) := by
      refine ContinuousOn.congr (continuous_fTclosed θ lam).continuousOn ?_
      intro x hx
      exact fT_eq_fTclosed θ lam x ⟨hx.1, hx.2⟩
    have hB : ContinuousOn (fT θ lam) (Set.Ici (2 * gammaT θ lam)) := by
      refine ContinuousOn.congr (continuousOn_const : ContinuousOn (fun _ : ℝ => (0:ℝ))
        (Set.Ici (2 * gammaT θ lam))) ?_
      intro x hx
      exact fT_eq_zero_of_two_gammaT_le θ lam hθ1 hθ2 hlam x hx
    have hUU : Set.Icc (0:ℝ) (2 * gammaT θ lam) ∪ Set.Ici (2 * gammaT θ lam)
        = Set.Ici 0 := by
      rw [Set.Icc_union_Ici (le_max_right _ _), min_eq_left (by positivity)]
    rw [← hUU]
    exact hA.union_of_isClosed hB isClosed_Icc isClosed_Ici
  · -- positivity at `0`, via the explicit value `fT θ λ̂ 0 = λ̂(1+tan²θ)(3 - θ tanθ - 3θ/tanθ)`
    have hT : Real.tan θ < 0 := tan_neg_of_half_pi_lt hθ1 hθ2
    have hθpos : 0 < θ := lt_trans (by linarith [Real.pi_pos]) hθ1
    have hv : 0 < -Real.tan θ := neg_pos.mpr hT
    rw [fT_zero θ lam hθ1 hθ2 hlam]
    have h3 : 0 < 3 + θ * (-Real.tan θ) + 3 * θ / (-Real.tan θ) := by positivity
    have key : 3 - θ * Real.tan θ - 3 * θ / Real.tan θ
        = 3 + θ * (-Real.tan θ) + 3 * θ / (-Real.tan θ) := by
      field_simp; ring
    rw [key]
    exact mul_pos (by positivity) h3
  · -- `C²` on `(0,2γ)`: `fT` agrees there with the `C^∞` closed form `fTclosed`
    have hcd : ContDiff ℝ 2 (fTclosed θ lam) := by unfold fTclosed; fun_prop
    exact ContDiffOn.congr hcd.contDiffOn (fun x hx => fT_eq_fTclosed θ lam x
      ⟨le_of_lt hx.1, le_of_lt hx.2⟩)
  · -- the second derivative is continuous (hence bounded) on the compact `[0,2γ]`
    have hcd : ContDiff ℝ 2 (fTclosed θ lam) := by unfold fTclosed; fun_prop
    have hcont : Continuous (fun t : ℝ => iteratedDeriv 2 (fTclosed θ lam) t) :=
      hcd.continuous_iteratedDeriv 2 le_rfl
    obtain ⟨C, hC⟩ := IsCompact.exists_bound_of_continuousOn isCompact_Icc
      (f := fun t : ℝ => iteratedDeriv 2 (fTclosed θ lam) t) hcont.continuousOn
    refine ⟨max C 0, le_max_right _ _, ?_⟩
    intro t ht
    have hev : fT θ lam =ᶠ[nhds t] fTclosed θ lam := by
      rw [Filter.eventuallyEq_iff_exists_mem]
      exact ⟨Set.Ioo 0 (2 * gammaT θ lam), IsOpen.mem_nhds isOpen_Ioo ht,
        fun y hy => fT_eq_fTclosed θ lam y ⟨le_of_lt hy.1, le_of_lt hy.2⟩⟩
    rw [Filter.EventuallyEq.iteratedDeriv_eq 2 hev]
    exact le_trans (hC t ⟨le_of_lt ht.1, le_of_lt ht.2⟩) (le_max_left _ _)

end Work.LinnikAreas.Density4
