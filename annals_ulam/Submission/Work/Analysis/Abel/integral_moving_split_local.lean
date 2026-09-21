import Mathlib
import Submission.Commons.Analysis.Calculus.intervalIntegral_hasDerivAt_of_continuous_parametric

namespace Work.Analysis.Abel

open MeasureTheory Set Filter
open scoped Topology Interval

/-- **Leibniz rule for an integral over a moving interval (local version).**

`∫_{-x u}^{y u} P = ∫_{-x b}^{y b} P + ∫_u^b (P(yσ)·(-y'(σ)) + P(-x(σ))·(-x'(σ))) dσ`.
No monotonicity of `x` or `y` is needed: both sides have the same derivative in `u`, and
they agree at `u = b` (this is just the fundamental result of calculus applied to
`σ ↦ ∫_{-x σ}^{y σ} P`, whose derivative is `P(yσ)y'(σ) - P(-xσ)·(-x'(σ))`).  The
hypotheses only supply: `C^∞`-regularity of `x, y` on `(0,∞)`, `0 < u ≤ b`, and
continuity of `P` on an interval `[c,d]` containing every section `[-xσ, yσ]`,
`σ ∈ [u,b]`. -/
theorem integral_moving_split_local {x y P : ℝ → ℝ} {c d u b : ℝ}
    (hx : ContDiffOn ℝ (⊤ : ℕ∞) x (Set.Ioi 0)) (hy : ContDiffOn ℝ (⊤ : ℕ∞) y (Set.Ioi 0))
    (hu : 0 < u) (hub : u ≤ b)
    (hP : ContinuousOn P (Set.Icc c d))
    (hcontain : ∀ σ ∈ Set.Icc u b, c < -(x σ) ∧ -(x σ) ≤ d ∧ c ≤ y σ ∧ y σ < d) :
    (∫ t in (-x u)..(y u), P t) = (∫ t in (-x b)..(y b), P t)
      + ∫ σ in u..b, (P (y σ) * (-(deriv y σ)) + P (-(x σ)) * (-(deriv x σ))) := by
  -- the interval of integration is non-degenerate
  have hcd : c < d := by
    obtain ⟨h1, h2, _, _⟩ := hcontain u ⟨le_refl u, hub⟩
    linarith
  -- extend `P` to a globally continuous function by clamping the argument into `[c,d]`
  set Q : ℝ → ℝ := fun t => P (max c (min d t)) with hQ
  have hQcont : Continuous Q := by
    rw [hQ]
    have hclamp : Continuous fun t : ℝ => max c (min d t) :=
      continuous_const.max (continuous_const.min continuous_id)
    have hmaps : MapsTo (fun t : ℝ => max c (min d t)) univ (Icc c d) := by
      intro t _
      exact ⟨le_max_left _ _, max_le hcd.le (min_le_left _ _)⟩
    exact continuousOn_univ.mp (hP.comp hclamp.continuousOn hmaps)
  have hQeq : ∀ t ∈ Icc c d, Q t = P t := by
    intro t ht
    simp only [hQ]
    rw [min_eq_right ht.2, max_eq_right ht.1]
  -- endpoints stay in `[c,d]`
  have hend : ∀ σ ∈ Icc u b, c ≤ -(x σ) ∧ -(x σ) ≤ d ∧ c ≤ y σ ∧ y σ ≤ d := by
    intro σ hσ
    obtain ⟨h1, h2, h3, h4⟩ := hcontain σ hσ
    exact ⟨h1.le, h2, h3, h4.le⟩
  have hsub : Icc u b ⊆ Ioi (0 : ℝ) := fun σ hσ => lt_of_lt_of_le hu hσ.1
  -- differentiability of the two profile functions
  have hxd : ∀ σ : ℝ, 0 < σ → HasDerivAt x (deriv x σ) σ := fun σ hσ =>
    ((hx.contDiffAt (isOpen_Ioi.mem_nhds hσ)).differentiableAt (by simp)).hasDerivAt
  have hyd : ∀ σ : ℝ, 0 < σ → HasDerivAt y (deriv y σ) σ := fun σ hσ =>
    ((hy.contDiffAt (isOpen_Ioi.mem_nhds hσ)).differentiableAt (by simp)).hasDerivAt
  -- the derivative datum of the moving integral of the extended profile
  set D : ℝ → ℝ := fun σ => deriv y σ * Q (y σ) + deriv x σ * Q (-(x σ)) with hD
  have hFp_deriv : ∀ σ : ℝ, 0 < σ →
      HasDerivAt (fun s : ℝ => ∫ t in (-(x s))..(y s), Q t) (D σ) σ := by
    intro σ hσpos
    have hxd' := hxd σ hσpos
    have hyd' := hyd σ hσpos
    have hmain :=
      Commons.Analysis.Calculus.intervalIntegral_hasDerivAt_of_continuous_parametric
        (F := fun (_ : ℝ) (t : ℝ) => Q t) (F' := fun (_ : ℝ) (_ : ℝ) => (0 : ℝ))
        (x := x) (y := y) (x' := deriv x σ) (y' := deriv y σ) (s := σ)
        (hQcont.comp continuous_snd) continuous_const
        (fun u t => hasDerivAt_const u (Q t)) hxd' hyd' hxd'.continuousAt hyd'.continuousAt
    have hv : Q (y σ) * deriv y σ - Q (-(x σ)) * (-(deriv x σ))
        + ∫ t in (-(x σ))..(y σ), (0 : ℝ) = D σ := by
      simp only [intervalIntegral.integral_zero, add_zero, hD]
      ring
    exact hmain.congr_deriv hv
  -- continuity of the derivative datum on `[u,b]`
  have hDcont : ContinuousOn D (Icc u b) := by
    have hdx : ContinuousOn (deriv x) (Icc u b) :=
      (hx.continuousOn_deriv_of_isOpen isOpen_Ioi (by simp)).mono hsub
    have hdy : ContinuousOn (deriv y) (Icc u b) :=
      (hy.continuousOn_deriv_of_isOpen isOpen_Ioi (by simp)).mono hsub
    have hxcont : ContinuousOn x (Icc u b) := hx.continuousOn.mono hsub
    have hycont : ContinuousOn y (Icc u b) := hy.continuousOn.mono hsub
    have hQy : ContinuousOn (fun σ => Q (y σ)) (Icc u b) := hQcont.comp_continuousOn hycont
    have hQx : ContinuousOn (fun σ => Q (-(x σ))) (Icc u b) :=
      hQcont.comp_continuousOn hxcont.neg
    rw [hD]
    exact (hdy.mul hQy).add (hdx.mul hQx)
  have hDint : IntervalIntegrable D volume u b :=
    (show ContinuousOn D (uIcc u b) by rwa [uIcc_of_le hub]).intervalIntegrable
  have hpos : ∀ σ ∈ uIcc u b, 0 < σ := by
    intro σ hσ
    rw [uIcc_of_le hub] at hσ
    exact lt_of_lt_of_le hu hσ.1
  -- fundamental theorem of calculus
  have hFTC : ∫ σ in u..b, D σ
      = (∫ t in (-(x b))..(y b), Q t) - (∫ t in (-(x u))..(y u), Q t) := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun s : ℝ => ∫ t in (-(x s))..(y s), Q t) (f' := D) (a := u) (b := b)
      (fun σ hσ => hFp_deriv σ (hpos σ hσ)) hDint
    simpa using h
  -- the extended and original moving integrals agree on `[u,b]`
  have hFp_eq : ∀ σ ∈ Icc u b,
      (∫ t in (-(x σ))..(y σ), Q t) = (∫ t in (-(x σ))..(y σ), P t) := by
    intro σ hσ
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    obtain ⟨ha1, ha2, ha3, ha4⟩ := hend σ hσ
    have ht_mem : t ∈ Icc c d :=
      ⟨le_trans (le_min ha1 ha3) ht.1, le_trans ht.2 (max_le ha2 ha4)⟩
    exact hQeq t ht_mem
  -- the integrand of the statement is minus the derivative datum
  have hg : ∀ σ ∈ Icc u b,
      P (y σ) * (-(deriv y σ)) + P (-(x σ)) * (-(deriv x σ)) = -(D σ) := by
    intro σ hσ
    obtain ⟨ha1, ha2, ha3, ha4⟩ := hend σ hσ
    have h1 : Q (y σ) = P (y σ) := hQeq (y σ) ⟨ha3, ha4⟩
    have h2 : Q (-(x σ)) = P (-(x σ)) := hQeq (-(x σ)) ⟨ha1, ha2⟩
    simp only [hD]
    rw [← h1, ← h2]
    ring
  have hG : (∫ σ in u..b, (P (y σ) * (-(deriv y σ)) + P (-(x σ)) * (-(deriv x σ))))
      = -(∫ σ in u..b, D σ) := by
    rw [← intervalIntegral.integral_neg (f := D)]
    refine intervalIntegral.integral_congr (fun σ hσ => ?_)
    rw [uIcc_of_le hub] at hσ
    exact hg σ hσ
  have hG' : (∫ σ in u..b, (P (y σ) * (-(deriv y σ)) + P (-(x σ)) * (-(deriv x σ))))
      = -((∫ t in (-(x b))..(y b), Q t) - (∫ t in (-(x u))..(y u), Q t)) := by
    rw [hG, hFTC]
  have hu_mem : u ∈ Icc u b := ⟨le_refl u, hub⟩
  have hb_mem : b ∈ Icc u b := ⟨hub, le_refl b⟩
  rw [← hFp_eq u hu_mem, ← hFp_eq b hb_mem, hG']
  ring

end Work.Analysis.Abel
