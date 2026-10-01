import Mathlib
import Submission.Work.LinnikAreas2.thetaF_monotone_seq_bound

/-!
# Unimodality of `x ↦ x^(σ-1) · (e^{-x/A} − e^{-x/B})`

For `0 < σ ≤ 1` and `0 < B < A` the function

`F(x) = x^(σ-1) · (e^{-x/A} − e^{-x/B})`,   `x > 0`,

is nonnegative, integrable on `(0,∞)`, and unimodal: there is a point
`x₀ ≤ 2·B·(1 + log(A/B))` such that `F` is monotone on `[0,x₀]` and antitone on `[x₀,∞)`.

This is assembled from the auxiliary development `thetaF_defs`, `thetaF_monotone_seq`,
`thetaF_monotone_seq_bound`, where the threshold is obtained as the (unique) zero of the
auxiliary function `Φ` and `F = exp ∘ Lfun` on `(0,∞)`.
-/

noncomputable section

open Set MeasureTheory

namespace Work.LinnikAreas2

/-- `gfun σ A B` is strictly positive on `(0,∞)`. -/
theorem thetaG_gfun_pos {σ A B : ℝ} (hB : 0 < B) (hBA : B < A) {x : ℝ} (hx : 0 < x) :
    0 < gfun σ A B x := by
  rw [← thetaF_exp_Lfun_eq_gfun σ A B hB hBA x hx]
  exact Real.exp_pos _

/-- `gfun σ A B 0 = 0`. -/
theorem thetaG_gfun_zero (σ A B : ℝ) : gfun σ A B 0 = 0 := by
  simp [gfun]

theorem thetaG_unimodal {σ A B : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hB : 0 < B) (hBA : B < A) :
    ∃ x₀ : ℝ, 0 < x₀ ∧ x₀ ≤ 2 * B * (1 + Real.log (A / B)) ∧
      MonotoneOn (fun t : ℝ => t ^ (σ - 1) * (Real.exp (-(t / A)) - Real.exp (-(t / B))))
        (Set.Icc 0 x₀) ∧
      AntitoneOn (fun t : ℝ => t ^ (σ - 1) * (Real.exp (-(t / A)) - Real.exp (-(t / B))))
        (Set.Ici x₀) ∧
      (∀ t ∈ Set.Ioi (0 : ℝ),
        0 ≤ t ^ (σ - 1) * (Real.exp (-(t / A)) - Real.exp (-(t / B)))) ∧
      MeasureTheory.IntegrableOn
        (fun t : ℝ => t ^ (σ - 1) * (Real.exp (-(t / A)) - Real.exp (-(t / B)))) (Set.Ioi 0) := by
  have hA : 0 < A := lt_trans hB hBA
  obtain ⟨x₀, hx₀pos, hx₀bnd, hx₀pos', hx₀neg'⟩ :=
    thetaF_Phi_exists_zero_bounded σ A B hσ hσ1 hB hBA
  have hLcont : ContinuousOn (Lfun σ A B) (Set.Ioi (0 : ℝ)) :=
    fun x hx => (thetaF_hasDerivAt_Lfun σ A B hB hBA x hx).continuousAt.continuousWithinAt
  have hFcont : ContinuousOn (fun x : ℝ => Real.exp (Lfun σ A B x)) (Set.Ioi (0 : ℝ)) :=
    Real.continuous_exp.comp_continuousOn hLcont
  have hFmono : StrictMonoOn (fun x : ℝ => Real.exp (Lfun σ A B x)) (Set.Ioc 0 x₀) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioc (0 : ℝ) x₀)
    · exact hFcont.mono (fun x hx => hx.1)
    · intro x hx
      rw [interior_Ioc] at hx
      rw [(thetaF_hasDerivAt_Lfun σ A B hB hBA x hx.1).exp.deriv]
      exact mul_pos (Real.exp_pos _) (div_pos (hx₀pos' x hx.1 hx.2) hx.1)
  have hFanti : StrictAntiOn (fun x : ℝ => Real.exp (Lfun σ A B x)) (Set.Ici x₀) := by
    apply strictAntiOn_of_deriv_neg (convex_Ici x₀)
    · exact hFcont.mono (fun x hx => lt_of_lt_of_le hx₀pos hx)
    · intro x hx
      rw [interior_Ici] at hx
      have hxpos : 0 < x := lt_trans hx₀pos hx
      rw [(thetaF_hasDerivAt_Lfun σ A B hB hBA x hxpos).exp.deriv]
      exact mul_neg_of_pos_of_neg (Real.exp_pos _)
        (div_neg_of_neg_of_pos (hx₀neg' x hx) hxpos)
  have haux : ∀ x : ℝ, 0 < x → gfun σ A B x = Real.exp (Lfun σ A B x) :=
    fun x hx => (thetaF_exp_Lfun_eq_gfun σ A B hB hBA x hx).symm
  have hgmonoIoc : StrictMonoOn (gfun σ A B) (Set.Ioc 0 x₀) := fun a ha b hb hab => by
    rw [haux a ha.1, haux b hb.1]
    exact hFmono ha hb hab
  have hgantiIci : StrictAntiOn (gfun σ A B) (Set.Ici x₀) := fun a ha b hb hab => by
    rw [haux b (lt_of_lt_of_le hx₀pos hb), haux a (lt_of_lt_of_le hx₀pos ha)]
    exact hFanti ha hb hab
  have hgpos : ∀ x : ℝ, 0 < x → 0 < gfun σ A B x := fun x hx => thetaG_gfun_pos hB hBA hx
  refine ⟨x₀, hx₀pos, hx₀bnd, ?_, ?_, ?_, ?_⟩
  · change MonotoneOn (gfun σ A B) (Set.Icc 0 x₀)
    intro a ha b hb hab
    rcases eq_or_lt_of_le hab with heq | hlt
    · rw [← heq]
    · have hbpos : 0 < b := lt_of_le_of_lt ha.1 hlt
      rcases lt_or_eq_of_le ha.1 with ha0 | h0a
      · exact (hgmonoIoc ⟨ha0, ha.2⟩ ⟨hbpos, hb.2⟩ hlt).le
      · rw [← h0a, thetaG_gfun_zero σ A B]
        exact le_of_lt (hgpos b hbpos)
  · change AntitoneOn (gfun σ A B) (Set.Ici x₀)
    intro a ha b hb hab
    rcases eq_or_lt_of_le hab with heq | hlt
    · rw [← heq]
    · exact (hgantiIci ha hb hlt).le
  · change ∀ t ∈ Set.Ioi (0 : ℝ), 0 ≤ gfun σ A B t
    intro t ht
    exact le_of_lt (hgpos t ht)
  · change MeasureTheory.IntegrableOn (gfun σ A B) (Set.Ioi 0)
    have hg_int : IntegrableOn (fun t : ℝ => t ^ (σ - 1) * Real.exp (-(t / A))) (Set.Ioi 0) := by
      have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := (1 : ℝ)) (s := σ - 1) (b := 1 / A)
        (by linarith) one_pos (by positivity)
      refine h.congr_fun (fun x hx => ?_) measurableSet_Ioi
      simp only [Real.rpow_one]
      rw [show -(1 / A) * x = -(x / A) by ring]
    have hcont_Ioi : ContinuousOn (gfun σ A B) (Set.Ioi 0) := by
      apply ContinuousOn.mul
      · intro x hx
        exact (Real.continuousAt_rpow_const x (σ - 1) (Or.inl (ne_of_gt hx))).continuousWithinAt
      · exact ((Real.continuous_exp.comp ((continuous_id.div_const A).neg)).continuousOn).sub
          ((Real.continuous_exp.comp ((continuous_id.div_const B).neg)).continuousOn)
    refine Integrable.mono' hg_int (hcont_Ioi.aestronglyMeasurable measurableSet_Ioi) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 < x := hx
    have hfx : 0 ≤ gfun σ A B x := le_of_lt (hgpos x hx0)
    change ‖gfun σ A B x‖ ≤ x ^ (σ - 1) * Real.exp (-(x / A))
    rw [Real.norm_of_nonneg hfx]
    rw [gfun]
    exact mul_le_mul_of_nonneg_left (by linarith [Real.exp_nonneg (-(x / B))])
      (le_of_lt (Real.rpow_pos_of_pos hx0 (σ - 1)))

end Work.LinnikAreas2
