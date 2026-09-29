import Mathlib
import Submission.Work.Holonomy3.mv_lex_defs
import Submission.Work.Holonomy3.mv_lex_general_case
import Submission.Work.Holonomy3.mv_lexmin_coeff_le_integral
import Submission.Work.Holonomy3.mv_lex_trunc_tendsto_integral
import Submission.Work.Holonomy3.mv_lex_log_poly_integrable
import Submission.Work.Holonomy3.mv_lex_general_defs

namespace Work.Holonomy3

open scoped BigOperators
open MeasureTheory

noncomputable section

/-! ### The per-truncation smoothed step

This is a verbatim copy of the `private` theorem `mv_lex_step_N` of
`Submission/Work/Holonomy3/mv_lex_general_case.lean`, with the single change that the
integrability of the smoothed truncated character sum is obtained from the public lemma
`integrable_log_norm_pevalF` instead of being reproved through
`continuous_pevalF_tor` (whose name occurs in two imported modules). -/

private theorem mv_lex_step_N_local {d : ℕ} (g : MvPowerSeries (Fin d) ℂ)
    (hpoly : ∀ (c : (Fin d →₀ ℕ) →₀ ℂ) (D : ℕ) (n : Fin d →₀ ℕ),
      (∀ m ∈ c.support, D ≤ m.degree) → n ∈ c.support → n.degree = D →
      (∀ m ∈ c.support, m.degree = D → toLex n ≤ toLex m) →
      Real.log ‖c n‖ ≤ ∫ s : Fin d → ℝ, Real.log ‖pevalF c (tor s)‖ ∂(torMeasure d))
    (hInt : ∀ (c : (Fin d →₀ ℕ) →₀ ℂ), c ≠ 0 →
      MeasureTheory.Integrable (fun s : Fin d → ℝ => Real.log ‖pevalF c (tor s)‖) (torMeasure d))
    {n : Fin d →₀ ℕ} (hn : MvPowerSeries.coeff n g ≠ 0)
    (hmin : ∀ m : Fin d →₀ ℕ, m.degree < n.degree → MvPowerSeries.coeff m g = 0)
    (hlex : ∀ m : Fin d →₀ ℕ, m.degree = n.degree → MvPowerSeries.coeff m g ≠ 0 →
      m = n ∨ ∃ j : Fin d, (∀ i : Fin d, i < j → m i = n i) ∧ n j < m j)
    (N : ℕ) (hN : n.degree ≤ N) {δ : ℝ} (hδ : 0 < δ) :
    Real.log ‖MvPowerSeries.coeff n g‖ ≤
      ∫ t : Fin d → ℝ,
        Real.log (‖pevalF (truncF (fun m => MvPowerSeries.coeff m g) N) (tor t)‖ + δ)
        ∂(torMeasure d) := by
  have hdeg : ∀ m ∈ (truncF (fun m => MvPowerSeries.coeff m g) N).support,
      n.degree ≤ m.degree := by
    intro m hm
    have hdegN : m.degree ≤ N := mem_degLe.mp (support_truncF_subset _ N hm)
    by_contra hcon
    rw [not_le] at hcon
    rw [Finsupp.mem_support_iff, truncF_apply, if_pos hdegN, hmin m hcon] at hm
    exact hm rfl
  have hmem : n ∈ (truncF (fun m => MvPowerSeries.coeff m g) N).support := by
    rw [Finsupp.mem_support_iff, truncF_apply, if_pos hN]
    exact hn
  have hlex' : ∀ m ∈ (truncF (fun m => MvPowerSeries.coeff m g) N).support,
      m.degree = n.degree → toLex n ≤ toLex m := by
    intro m hm hdegm
    have ham : MvPowerSeries.coeff m g ≠ 0 := by
      have h2 := Finsupp.mem_support_iff.mp hm
      rwa [truncF_apply, if_pos (mem_degLe.mp (support_truncF_subset _ N hm))] at h2
    rcases hlex m hdegm ham with heq | ⟨j, hj, hlt⟩
    · rw [heq]
    · refine le_of_lt ?_
      rw [Finsupp.Lex.lt_iff]
      refine ⟨j, fun i hi => ?_, ?_⟩
      · simpa [eq_comm] using hj i hi
      · simpa using hlt
  have hcN : truncF (fun m => MvPowerSeries.coeff m g) N ≠ 0 := truncF_ne_zero_of hn hN
  have hpolyN := hpoly (truncF (fun m => MvPowerSeries.coeff m g) N) n.degree n hdeg hmem rfl hlex'
  have hcn : truncF (fun m => MvPowerSeries.coeff m g) N n = MvPowerSeries.coeff n g := by
    rw [truncF_apply, if_pos hN]
  rw [hcn] at hpolyN
  have hint : Integrable (fun t : Fin d → ℝ =>
      Real.log ‖pevalF (truncF (fun m => MvPowerSeries.coeff m g) N) (tor t)‖) (torMeasure d) :=
    hInt _ hcN
  have hintδ : Integrable (fun t : Fin d → ℝ =>
      Real.log (‖pevalF (truncF (fun m => MvPowerSeries.coeff m g) N) (tor t)‖ + δ))
      (torMeasure d) :=
    integrable_log_norm_pevalF (truncF (fun m => MvPowerSeries.coeff m g) N) hδ
  have hsm := mv_lex_trunc_smoothed_ge (fun m => MvPowerSeries.coeff m g) N hδ hcN hint hintδ
  linarith

/-- **The smoothed multivariable lexicographic-minimum coefficient bound.**

This is the intermediate statement `key` inside the proof of `Work.Holonomy3.mv_lex_general_case`
(see `Submission/Work/Holonomy3/mv_lex_general_case.lean`): for EVERY `δ > 0` the smoothed
quantity `log (‖G‖ + δ)` may be integrated.  It is what one needs when the majorant of `log ‖G‖`
on the torus is allowed to be negative (Lean's `Real.log 0 = 0` would otherwise break the
pointwise comparison at the zeros of `G`).

The proof of `key` there is: for each `N ≥ n.degree`, apply the per-truncation estimate
`mv_lex_step_N` (private in that file; its statement takes the two hypotheses `hpoly`, `hInt`,
here instantiated by the public lemmas `poly_case` of `mv_lexmin_coeff_le_integral.lean` and
`mv_lex_log_poly_integrable`; its ~90-line proof body may be copied verbatim into the new file),
then pass to the limit `N → ∞` with `mv_lex_trunc_tendsto_integral` and `ge_of_tendsto`. -/
theorem mv_lexmin_coeff_le_integral_smoothed {d : ℕ} (g : MvPowerSeries (Fin d) ℂ)
    (G : (Fin d → ℂ) → ℂ) (ρ : ℝ) (hρ : 1 < ρ)
    (hG : ∀ z : Fin d → ℂ, (∀ j, ‖z j‖ ≤ ρ) →
      HasSum (fun m : Fin d →₀ ℕ => MvPowerSeries.coeff m g * ∏ j, (z j) ^ (m j)) (G z))
    (n : Fin d →₀ ℕ) (hn : MvPowerSeries.coeff n g ≠ 0)
    (hmin : ∀ m : Fin d →₀ ℕ, m.degree < n.degree → MvPowerSeries.coeff m g = 0)
    (hlex : ∀ m : Fin d →₀ ℕ, m.degree = n.degree → MvPowerSeries.coeff m g ≠ 0 →
      m = n ∨ ∃ j : Fin d, (∀ i : Fin d, i < j → m i = n i) ∧ n j < m j)
    (δ : ℝ) (hδ : 0 < δ) :
    Real.log ‖MvPowerSeries.coeff n g‖ ≤
      ∫ t : Fin d → ℝ, Real.log (‖G (fun j => tor t j)‖ + δ) ∂(torMeasure d) := by
  have hpoly : ∀ (c : (Fin d →₀ ℕ) →₀ ℂ) (D : ℕ) (n : Fin d →₀ ℕ),
      (∀ m ∈ c.support, D ≤ m.degree) → n ∈ c.support → n.degree = D →
      (∀ m ∈ c.support, m.degree = D → toLex n ≤ toLex m) →
      Real.log ‖c n‖ ≤ ∫ s : Fin d → ℝ, Real.log ‖pevalF c (tor s)‖ ∂(torMeasure d) :=
    fun c D n hmin' hn' hdeg hlex' => poly_case c hmin' hn' hdeg hlex'
  have hlim := mv_lex_trunc_tendsto_integral g G hρ hG hδ
  refine ge_of_tendsto hlim (Filter.eventually_atTop.mpr ⟨n.degree, fun N hN => ?_⟩)
  exact mv_lex_step_N_local g hpoly mv_lex_log_poly_integrable hn hmin hlex N hN hδ

end

end Work.Holonomy3
