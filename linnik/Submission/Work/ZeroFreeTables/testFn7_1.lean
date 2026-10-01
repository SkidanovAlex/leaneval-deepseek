/-
# ZeroFreeTables — testFn7_1

**HB Lemma 7.1's optimal test function** as an element of Heath-Brown's class of
test functions (`TestFn`, Conditions 1 and 2): the `0 < θ < π/2` branch of the
§7 variational problem, whose `θ → 0` limit is the `θ`-independent Lemma 7.2
(`testFn7_2`).  It is the family from which HB's Tables 2, 3, 9, 10, 11 are read.

With `ζ = λ tan θ`, `γ = θ/ζ`, HB's auxiliary function is

  `g(t) = λ(1+tan²θ)(cos(ζt) − cos θ)` on `[-γ,γ]`, `0` outside,

and the test function is `f = g ⊛ g`, given in closed form on `[0,2γ]` by
`tf71cf`.  HB Lemma 7.1 states that this test function has

  `x₀ = 2γ`,  `f 0 = λ(1+tan²θ)[θ tan θ + 3θ cot θ − 3]`,
  `F 0 = 2(1+tan²θ)(1 − θ cot θ)²`,
  `F(−λ) = 2 tan²θ + 3 − 3θ tan θ − 3θ cot θ`.

The definitions and the elementary structural facts are in `testFn71_defs`; the
crux (`f = g ⊛ g` on `[0,2γ]`, whence `f ≥ 0`) and the transcendental value
lemmas are delegated auxiliary modules.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.Engine
import Submission.Work.ZeroFreeTables.HB4_1
import Submission.Work.ZeroFreeTables.testFn71_defs
import Submission.Work.ZeroFreeTables.tf71conv_eq_f
import Submission.Work.ZeroFreeTables.tf71Fc_imag_re_nonneg
import Submission.Work.ZeroFreeTables.tf71Fc_analytic
import Submission.Work.ZeroFreeTables.tf71Fc_zero_re
import Submission.Work.ZeroFreeTables.tf71Fc_neglam_re
import Submission.Work.ZeroFreeTables.tf71_trig_pos

namespace Work.ZeroFreeTables

noncomputable section

/-- `f ≥ 0`: on `[0,2γ]` the closed form is the convolution `g ⊛ g` of the
non-negative `g` (the crux `tf71conv_eq_f`), and outside it is `0`. -/
theorem tf71f_nonneg (θ lam : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) (hlam : 0 < lam) :
    ∀ x : ℝ, 0 ≤ tf71f θ lam x := by
  intro x
  by_cases hx : x ∈ Set.Icc 0 (2 * tf71γ θ lam)
  · rw [← tf71conv_eq_f θ lam hθ0 hθ1 hlam x hx]
    unfold tf71conv
    exact MeasureTheory.integral_nonneg
      (fun s => mul_nonneg (tf71g_nonneg hθ0 hθ1 hlam s) (tf71g_nonneg hθ0 hθ1 hlam (x - s)))
  · unfold tf71f
    by_cases hx0 : 0 ≤ x
    · rw [if_pos hx0]
      have hx2 : 2 * tf71γ θ lam ≤ x := by
        rcases lt_or_ge x (2 * tf71γ θ lam) with hlt | hge
        · exact absurd ⟨hx0, le_of_lt hlt⟩ hx
        · exact hge
      rw [min_eq_right hx2, tf71cf_at_twoγ hθ0 hθ1 hlam]
    · rw [if_neg hx0]

/-- `f 0 > 0` (needed for HB's Condition 1), from the explicit value of `f 0` and
`tf71_trig_pos`. -/
theorem tf71f_zero_pos (θ lam : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) (hlam : 0 < lam) :
    0 < tf71f θ lam 0 := by
  rw [tf71f_at_zero hθ0 hθ1 hlam]
  exact mul_pos (by positivity) (tf71_trig_pos hθ0 hθ1)

/-- HB Lemma 4.1 applied to the Laplace transform of HB Lemma 7.1's test function:
`Re (F z) ≥ 0` throughout `Re z ≥ 0` (HB's Condition 2). -/
theorem tf71Fc_re_nonneg (θ lam : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) (hlam : 0 < lam) :
    ∀ z : ℂ, 0 ≤ z.re → 0 ≤ (tf71Fc θ lam z).re := by
  obtain ⟨hd, hc, hdec⟩ := tf71Fc_analytic θ lam hθ0 hθ1 hlam
  have hbd : ∀ y : ℝ,
      (tf71Fc θ lam ((y : ℂ) * Complex.I)).re ≥ ‖(fun _ : ℂ => (0:ℂ)) ((y : ℂ) * Complex.I)‖ :=
    fun y => by simpa using tf71Fc_imag_re_nonneg θ lam hθ0 hθ1 hlam y
  have hdec' : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧ ∀ z : ℂ, 0 ≤ z.re → R ≤ ‖z‖ →
      ‖tf71Fc θ lam z‖ < ε ∧ ‖(fun _ : ℂ => (0:ℂ)) z‖ < ε := fun ε hε => by
    obtain ⟨R, hR, hRz⟩ := hdec ε hε
    exact ⟨R, hR, fun z hz hRz' => ⟨hRz z hz hRz', by simpa using hε⟩⟩
  simpa using hb_lemma4_1 (F1 := tf71Fc θ lam) (F2 := fun _ : ℂ => (0:ℂ)) hd
    (differentiableOn_const (0:ℂ)) hc continuousOn_const hbd hdec'

/-- HB Lemma 7.1's optimal test function, as an element of HB's class of test
functions satisfying Conditions 1 and 2. -/
def tf71T (θ lam : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) (hlam : 0 < lam) : TestFn where
  x₀ := 2 * tf71γ θ lam
  f := tf71f θ lam
  Fc := tf71Fc θ lam
  x₀_pos := by have := tf71γ_pos hθ0 hθ1 hlam; positivity
  f0_pos := tf71f_zero_pos θ lam hθ0 hθ1 hlam
  f_nonneg := tf71f_nonneg θ lam hθ0 hθ1 hlam
  f_cont := tf71f_cont θ lam
  f_diff := tf71f_diff θ lam (tf71γ_pos hθ0 hθ1 hlam)
  f_bound := tf71f_bound θ lam (tf71γ_pos hθ0 hθ1 hlam)
  f_supp := tf71f_supp hθ0 hθ1 hlam
  Fc_spec := fun z => rfl
  Fc_re_nonneg := tf71Fc_re_nonneg θ lam hθ0 hθ1 hlam

theorem testFn7_1 (θ lam : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) (hlam : 0 < lam) :
    ∃ T : TestFn, T.x₀ = 2 * tf71γ θ lam ∧
      T.f 0 = lam * (1 + Real.tan θ ^ 2) *
        (θ * Real.tan θ + 3 * θ * (Real.tan θ)⁻¹ - 3) ∧
      T.F 0 = 2 * (1 + Real.tan θ ^ 2) * (1 - θ * (Real.tan θ)⁻¹) ^ 2 ∧
      T.F (-lam) = 2 * Real.tan θ ^ 2 + 3 - 3 * θ * Real.tan θ - 3 * θ * (Real.tan θ)⁻¹ := by
  refine ⟨tf71T θ lam hθ0 hθ1 hlam, rfl, tf71f_at_zero hθ0 hθ1 hlam, ?_, ?_⟩
  · show (tf71Fc θ lam ((0:ℝ) : ℂ)).re
        = 2 * (1 + Real.tan θ ^ 2) * (1 - θ * (Real.tan θ)⁻¹) ^ 2
    rw [show ((0:ℝ) : ℂ) = (0:ℂ) from rfl]
    exact tf71Fc_zero_re θ lam hθ0 hθ1 hlam
  · show (tf71Fc θ lam (((-lam : ℝ)) : ℂ)).re
        = 2 * Real.tan θ ^ 2 + 3 - 3 * θ * Real.tan θ - 3 * θ * (Real.tan θ)⁻¹
    exact tf71Fc_neglam_re θ lam hθ0 hθ1 hlam

end
end Work.ZeroFreeTables
