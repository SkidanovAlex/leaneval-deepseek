import Mathlib
import Submission.Work.RPB.B5.regDefs
import Submission.Work.RPB.B5.pds_eq_deriv
import Submission.Work.RPB.B5.regF_contDiff

/-!
# B5: the regularised phase integrand

Given a smooth family `hc : ℝ → ℝ → ℝ → ℂ` which is even in its third variable, we produce a
smooth function `g` which is odd in its third variable and which, on the strip `τ ∈ [0,1]`,
`|s| < ρa`, agrees with the phase derivative `Im (∂₃ hc / hc)`.

The construction (`Work.RPB.B5.regF`) regularises the denominator `|hc|²` by adding the smooth
non-negative bump `phaseBumpK ρa τ s`, whose zero set is exactly `[0,1] × [-ρa,ρa]`: on that set
`hc` is known to be non-vanishing (because `ρa < ρb < δ` and `hne`), so the regularised integrand
equals `Im (∂₃ hc / hc)` there, while the denominator is everywhere strictly positive.  The
regularised integrand is automatically odd in `s` because `hc` is even in `s`.

The two analytic ingredients (`pds_eq_deriv`, `regF_contDiff`) are proved in the sibling modules
`Submission/Work/RPB/B5/pds_eq_deriv.lean` and `Submission/Work/RPB/B5/regF_contDiff.lean`.
-/

open scoped ContDiff

set_option autoImplicit false
-- `hδ` and `ha0` are hypotheses of the requested statement that the construction does not need.
set_option linter.unusedVariables false

namespace Work.RPB.B5

/-- The derivative of an even function is odd. -/
lemma deriv_eq_neg_of_even (f : ℝ → ℂ) (h : ∀ x, f (-x) = f x) (s : ℝ) :
    deriv f (-s) = -deriv f s := by
  have h1 : deriv (fun x => f (-x)) s = -deriv f (-s) := deriv_comp_neg f s
  have h2 : (fun x => f (-x)) = f := by funext x; exact h x
  rw [h2] at h1
  rw [h1]; ring

/-- `pds hc τ t ·` is odd in its last argument when `hc` is even in its third argument. -/
lemma pds_neg (hc : ℝ → ℝ → ℝ → ℂ)
    (hc_sm : ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) (fun z : ℝ × (ℝ × ℝ) => hc z.1 z.2.1 z.2.2))
    (hc_even : ∀ τ t r, hc τ t (-r) = hc τ t r) (τ t s : ℝ) :
    pds hc τ t (-s) = -pds hc τ t s := by
  rw [pds_eq_deriv hc hc_sm τ t (-s), pds_eq_deriv hc hc_sm τ t s]
  exact deriv_eq_neg_of_even (fun u => hc τ t u) (fun u => hc_even τ t u) s

/-- The regularised denominator never vanishes, using that `hc` is non-zero on the closed box
`τ ∈ [0,1]`, `|s| ≤ ρa`. -/
lemma regDen_ne_zero (hc : ℝ → ℝ → ℝ → ℂ) (δ : ℝ)
    (hne : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t r, |r| < δ → hc τ t r ≠ 0)
    (ρa ρb : ℝ) (hab : ρa < ρb) (hbδ : ρb < δ) (τ t s : ℝ) :
    regDen hc ρa τ t s ≠ 0 := by
  intro h
  unfold regDen at h
  have ha : 0 ≤ (hc τ t s).re * (hc τ t s).re := mul_self_nonneg _
  have hb : 0 ≤ (hc τ t s).im * (hc τ t s).im := mul_self_nonneg _
  have hk : 0 ≤ phaseBumpK ρa τ s := phaseBumpK_nonneg ρa τ s
  have hre : (hc τ t s).re = 0 := mul_self_eq_zero.mp (by linarith)
  have him : (hc τ t s).im = 0 := mul_self_eq_zero.mp (by linarith)
  have hκ : phaseBumpK ρa τ s = 0 := by linarith
  obtain ⟨hτ, hs⟩ := (phaseBumpK_eq_zero_iff ρa τ s).mp hκ
  have hsδ : |s| < δ := lt_of_le_of_lt (le_trans hs (le_of_lt hab)) hbδ
  exact hne τ hτ t s hsδ (Complex.ext hre him)

/-- The regularised phase integrand is odd in its last argument. -/
lemma regF_neg (hc : ℝ → ℝ → ℝ → ℂ)
    (hc_sm : ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) (fun z : ℝ × (ℝ × ℝ) => hc z.1 z.2.1 z.2.2))
    (hc_even : ∀ τ t r, hc τ t (-r) = hc τ t r) (ρa τ t s : ℝ) :
    regF hc ρa τ t (-s) = -regF hc ρa τ t s := by
  have hpdsn : pds hc τ t (-s) = -pds hc τ t s := pds_neg hc hc_sm hc_even τ t s
  have hhcn : hc τ t (-s) = hc τ t s := hc_even τ t s
  have hdenn : regDen hc ρa τ t (-s) = regDen hc ρa τ t s := by
    unfold regDen
    rw [hhcn, phaseBumpK_neg]
  unfold regF regNum
  rw [hdenn, hpdsn, hhcn, Complex.neg_im, Complex.neg_re]
  ring

/-- On the strip `τ ∈ [0,1]`, `|s| < ρa` the regularised integrand is the phase derivative. -/
lemma regF_eq (hc : ℝ → ℝ → ℝ → ℂ)
    (hc_sm : ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) (fun z : ℝ × (ℝ × ℝ) => hc z.1 z.2.1 z.2.2))
    (ρa : ℝ) {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) {t s : ℝ} (hs : |s| < ρa) :
    regF hc ρa τ t s = Complex.im (deriv (fun u : ℝ => hc τ t u) s / hc τ t s) := by
  have hκ : phaseBumpK ρa τ s = 0 :=
    (phaseBumpK_eq_zero_iff ρa τ s).mpr ⟨hτ, le_of_lt hs⟩
  have hden : regDen hc ρa τ t s = Complex.normSq (hc τ t s) := by
    unfold regDen
    rw [hκ, add_zero, Complex.normSq_apply]
  unfold regF regNum
  rw [hden, pds_eq_deriv hc hc_sm τ t s, Complex.div_im, sub_div]

theorem regularizedPhaseIntegrand (hc : ℝ → ℝ → ℝ → ℂ)
    (hc_sm : ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) (fun z : ℝ × (ℝ × ℝ) => hc z.1 z.2.1 z.2.2))
    (hc_even : ∀ τ t r, hc τ t (-r) = hc τ t r)
    (δ : ℝ) (hδ : 0 < δ)
    (hne : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t r, |r| < δ → hc τ t r ≠ 0)
    (ρa ρb : ℝ) (ha0 : 0 < ρa) (hab : ρa < ρb) (hbδ : ρb < δ) :
    ∃ g : ℝ → ℝ → ℝ → ℝ,
      ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) (fun z : ℝ × (ℝ × ℝ) => g z.1 z.2.1 z.2.2) ∧
      (∀ τ t s, g τ t (-s) = -g τ t s) ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t s, |s| < ρa →
        g τ t s = Complex.im (deriv (fun u : ℝ => hc τ t u) s / hc τ t s)) := by
  refine ⟨fun τ t s => regF hc ρa τ t s, ?_, ?_, ?_⟩
  · exact regF_contDiff hc ρa hc_sm
      (fun τ t s => regDen_ne_zero hc δ hne ρa ρb hab hbδ τ t s)
  · intro τ t s
    exact regF_neg hc hc_sm hc_even ρa τ t s
  · intro τ hτ t s hs
    exact regF_eq hc hc_sm ρa hτ hs

end Work.RPB.B5
