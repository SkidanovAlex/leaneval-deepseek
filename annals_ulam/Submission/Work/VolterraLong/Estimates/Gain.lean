import Submission.Work.VolterraLong.Weighted.Basic

/-!
# The Volterra gain `1/λ`

In the exponentially weighted supremum norm the Volterra integral operator
gains a factor `1/λ`: if `‖G σ‖ ≤ L ‖W σ - V σ‖` on `[a,b]`, then

`‖∫_s^b G‖ ≤ (L/λ) * wdist lam W V * e^{λ(b-s)}`.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology Interval

namespace Work.VolterraLong

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `∫_s^b e^{λ(b-σ)} dσ ≤ e^{λ(b-s)}/λ` for `λ > 0`. -/
theorem integral_exp_weight_le {lam : ℝ} (hlam : 0 < lam) {s b : ℝ} (hsb : s ≤ b) :
    ∫ σ in s..b, Real.exp (lam * (b - σ)) ≤ Real.exp (lam * (b - s)) / lam := by
  have hderiv : ∀ σ ∈ Set.uIcc s b,
      HasDerivAt (fun σ : ℝ => -(Real.exp (lam * (b - σ)) / lam))
        (Real.exp (lam * (b - σ))) σ := by
    intro σ _
    have h1 : HasDerivAt (fun σ : ℝ => lam * (b - σ)) (-lam) σ := by
      have h2 : HasDerivAt (fun σ : ℝ => b - σ) (-1) σ := by
        simpa using (hasDerivAt_id σ).const_sub b
      simpa using h2.const_mul lam
    have h3 : HasDerivAt (fun σ : ℝ => Real.exp (lam * (b - σ)))
        (Real.exp (lam * (b - σ)) * (-lam)) σ := h1.exp
    have h4 : HasDerivAt (fun σ : ℝ => -(Real.exp (lam * (b - σ)) / lam))
        (-(Real.exp (lam * (b - σ)) * (-lam) / lam)) σ := (h3.div_const lam).neg
    have heq : -(Real.exp (lam * (b - σ)) * (-lam) / lam) = Real.exp (lam * (b - σ)) := by
      have hne : lam ≠ 0 := ne_of_gt hlam
      field_simp
    rwa [heq] at h4
  have hint : IntervalIntegrable (fun σ : ℝ => Real.exp (lam * (b - σ))) volume s b := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have h1 : -(1 / lam) ≤ 0 := by
    rw [neg_nonpos]
    exact div_nonneg zero_le_one hlam.le
  rw [hFTC]
  simp only [sub_self, mul_zero, Real.exp_zero]
  linarith

/-- The Volterra gain: the weighted norm of the integral of a function bounded
by `L ‖W - V‖` gains a factor `1/λ`. -/
theorem weighted_integral_le {a b lam L : ℝ} (hab : a ≤ b) (hlam : 0 < lam) (hL : 0 ≤ L)
    (W V : BoundedContinuousFunction (Set.Icc a b) E)
    {G : ℝ → E}
    (hG : ∀ σ : Set.Icc a b, ‖G (σ : ℝ)‖ ≤ L * ‖W σ - V σ‖)
    (hGint : IntervalIntegrable G volume a b)
    (s : Set.Icc a b) :
    ‖∫ σ in (s : ℝ)..b, G σ‖ ≤ (L / lam) * wdist lam W V *
      Real.exp (lam * (b - (s : ℝ))) := by
  have hb : (s : ℝ) ≤ b := s.2.2
  have hwnn : 0 ≤ wdist lam W V := wdist_nonneg W V
  have hgcont : Continuous (fun σ : ℝ => L * wdist lam W V * Real.exp (lam * (b - σ))) := by
    fun_prop
  have hstep : ‖∫ σ in (s : ℝ)..b, G σ‖ ≤
      ∫ σ in (s : ℝ)..b, L * wdist lam W V * Real.exp (lam * (b - σ)) := by
    refine intervalIntegral.norm_integral_le_of_norm_le hb
      (g := fun σ : ℝ => L * wdist lam W V * Real.exp (lam * (b - σ)))
      (Filter.Eventually.of_forall (fun σ hσ => ?_)) (hgcont.intervalIntegrable _ _)
    have hσab : σ ∈ Set.Icc a b := ⟨le_trans s.2.1 (le_of_lt hσ.1), hσ.2⟩
    have h1 := hG ⟨σ, hσab⟩
    have h2 : ‖W ⟨σ, hσab⟩ - V ⟨σ, hσab⟩‖ ≤
        wdist lam W V * Real.exp (lam * (b - σ)) := by
      have h3 := le_wdist (le_of_lt hlam) W V ⟨σ, hσab⟩
      have h4 : ‖W ⟨σ, hσab⟩ - V ⟨σ, hσab⟩‖ * Real.exp (-(lam * (b - σ))) *
          Real.exp (lam * (b - σ)) ≤ wdist lam W V * Real.exp (lam * (b - σ)) :=
        mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
      have h5 : Real.exp (-(lam * (b - σ))) * Real.exp (lam * (b - σ)) = 1 := by
        rw [← Real.exp_add]
        simp
      rwa [mul_assoc, h5, mul_one] at h4
    calc ‖G σ‖ ≤ L * ‖W ⟨σ, hσab⟩ - V ⟨σ, hσab⟩‖ := h1
      _ ≤ L * (wdist lam W V * Real.exp (lam * (b - σ))) := mul_le_mul_of_nonneg_left h2 hL
      _ = L * wdist lam W V * Real.exp (lam * (b - σ)) := by ring
  refine hstep.trans ?_
  have hconst : (∫ σ in (s : ℝ)..b, L * wdist lam W V * Real.exp (lam * (b - σ))) =
      L * wdist lam W V * (∫ σ in (s : ℝ)..b, Real.exp (lam * (b - σ))) :=
    intervalIntegral.integral_const_mul (L * wdist lam W V) _
  rw [hconst]
  have hI := integral_exp_weight_le hlam hb
  calc L * wdist lam W V * (∫ σ in (s : ℝ)..b, Real.exp (lam * (b - σ)))
      ≤ L * wdist lam W V * (Real.exp (lam * (b - (s : ℝ))) / lam) :=
        mul_le_mul_of_nonneg_left hI (mul_nonneg hL hwnn)
    _ = (L / lam) * wdist lam W V * Real.exp (lam * (b - (s : ℝ))) := by ring

end Work.VolterraLong
