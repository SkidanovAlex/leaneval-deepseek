import Mathlib
import Submission.Work.Holonomy3.antitone_integral_tendsto
import Submission.Work.Holonomy3.not_integrable_exists_integral_le_zero

namespace Work.Holonomy3

open MeasureTheory Filter

/-- If `c₀` is the limit of an antitone sequence `c` with `c n ≤ ∫ log (g + ε n)`, where
`ε n ↓ 0` with `0 < ε n ≤ 1` and `g ≥ 0` has `log (g + 1)` bounded above by `C`, then
`c₀ ≤ ∫ log g`.

The proof compares `∫ log (g + ε n)` with the integral of the "smoothed" family
`v n := 1_{g ≠ 0} · log (g + ε n)`. Off the zero set of `g` this is a decreasing family
converging pointwise to `log g` and bounded above by `C`; on the zero set it vanishes. The
zero set only *decreases* `∫ log (g + ε n)` (there the integrand equals the non-positive
constant `log (ε n)`), so `c₀ ≤ ∫ v n` for all `n`. If `log g` is integrable, dominated
convergence gives `∫ v n → ∫ log g`; otherwise `∫ log g = 0` and the non-integrability forces
`∫ v n ≤ 0` for some `n`. -/
theorem le_integral_log_of_smoothed {X : Type*} [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    [MeasureTheory.IsProbabilityMeasure μ] {g : X → ℝ} (hgm : Measurable g) (hg0 : ∀ x, 0 ≤ g x)
    {C : ℝ} (hC0 : 0 ≤ C) (hCg : ∀ x, Real.log (g x + 1) ≤ C)
    {ε : ℕ → ℝ} (hε0 : ∀ n, 0 < ε n) (hε1 : ∀ n, ε n ≤ 1)
    (hεt : Filter.Tendsto ε Filter.atTop (nhds 0)) (hεm : Antitone ε)
    {c : ℕ → ℝ} (hc : ∀ n, c n ≤ ∫ x, Real.log (g x + ε n) ∂μ) (hcm : Antitone c)
    {c₀ : ℝ} (hct : Filter.Tendsto c Filter.atTop (nhds c₀)) :
    c₀ ≤ ∫ x, Real.log (g x) ∂μ := by
  let A : Set X := {x | g x = 0}
  have hA : MeasurableSet A := by
    change MeasurableSet {x | g x = 0}
    exact hgm (measurableSet_singleton 0)
  have hNotMemA : ∀ x ∈ A, x ∉ Aᶜ := by
    intro x hx; simp only [Set.mem_compl_iff, not_not]; exact hx
  have hMemCompl : ∀ x, x ∉ A → x ∈ Aᶜ := by
    intro x hx; exact (Set.mem_compl_iff A x).mpr hx
  -- Integrability of `log (g · + ε n)` via the two-sided bound `log (ε n) ≤ · ≤ C`.
  have h_int : ∀ n, Integrable (fun x => Real.log (g x + ε n)) μ := by
    intro n
    refine Integrable.of_bound ?_ (max C (-Real.log (ε n))) (Filter.Eventually.of_forall (fun x => ?_))
    · exact (hgm.add_const _).log.aestronglyMeasurable
    · have hge : (0:ℝ) < g x + ε n := by linarith [hg0 x, hε0 n]
      have hle : g x + ε n ≤ g x + 1 := by linarith [hε1 n]
      have hu : Real.log (g x + ε n) ≤ C := le_trans (Real.log_le_log hge hle) (hCg x)
      have hle2 : ε n ≤ g x + ε n := by linarith [hg0 x]
      have hl : Real.log (ε n) ≤ Real.log (g x + ε n) := Real.log_le_log (hε0 n) hle2
      rw [Real.norm_eq_abs, abs_le]
      exact ⟨by linarith [le_max_right C (-Real.log (ε n)), hl],
             by linarith [le_max_left C (-Real.log (ε n)), hu]⟩
  -- `v n := 1_{g ≠ 0} · log (g + ε n)`.
  have h_vle : ∀ n x, Aᶜ.indicator (fun x => Real.log (g x + ε n)) x ≤ C := by
    intro n x
    by_cases hx : x ∈ A
    · rw [Set.indicator_of_notMem (hNotMemA x hx)]; exact hC0
    · rw [Set.indicator_of_mem (hMemCompl x hx)]
      have hge : (0:ℝ) < g x + ε n := by linarith [hg0 x, hε0 n]
      exact le_trans (Real.log_le_log hge (by linarith [hε1 n])) (hCg x)
  have h_vge : ∀ n x, Real.log (g x) ≤ Aᶜ.indicator (fun x => Real.log (g x + ε n)) x := by
    intro n x
    by_cases hx : x ∈ A
    · have hgx : g x = 0 := hx
      rw [Set.indicator_of_notMem (hNotMemA x hx), hgx, Real.log_zero]
    · rw [Set.indicator_of_mem (hMemCompl x hx)]
      have hgx : 0 < g x := by
        have h1 : 0 ≤ g x := hg0 x
        rcases lt_or_eq_of_le h1 with h | h
        · exact h
        · exact absurd (show x ∈ A from h.symm) hx
      exact Real.log_le_log hgx (by linarith [hε0 n])
  have h_vmono : ∀ x, Antitone (fun n => Aᶜ.indicator (fun x => Real.log (g x + ε n)) x) := by
    intro x
    by_cases hx : x ∈ A
    · intro a b hab
      show Aᶜ.indicator (fun x => Real.log (g x + ε b)) x
          ≤ Aᶜ.indicator (fun x => Real.log (g x + ε a)) x
      rw [Set.indicator_of_notMem (hNotMemA x hx), Set.indicator_of_notMem (hNotMemA x hx)]
    · intro a b hab
      show Aᶜ.indicator (fun x => Real.log (g x + ε b)) x
          ≤ Aᶜ.indicator (fun x => Real.log (g x + ε a)) x
      rw [Set.indicator_of_mem (hMemCompl x hx), Set.indicator_of_mem (hMemCompl x hx)]
      apply Real.log_le_log
      · linarith [hε0 b, hg0 x]
      · have := hεm hab; linarith
  have h_vtend : ∀ x, Tendsto (fun n => Aᶜ.indicator (fun x => Real.log (g x + ε n)) x) atTop
      (nhds (Real.log (g x))) := by
    intro x
    by_cases hx : x ∈ A
    · have hgx : g x = 0 := hx
      have hconst : (fun n => Aᶜ.indicator (fun x => Real.log (g x + ε n)) x) = fun _ => (0:ℝ) := by
        funext n; rw [Set.indicator_of_notMem (hNotMemA x hx)]
      rw [hconst, hgx, Real.log_zero]
      exact tendsto_const_nhds
    · have hgx : 0 < g x := by
        have h1 : 0 ≤ g x := hg0 x
        rcases lt_or_eq_of_le h1 with h | h
        · exact h
        · exact absurd (show x ∈ A from h.symm) hx
      have hconst : (fun n => Aᶜ.indicator (fun x => Real.log (g x + ε n)) x)
          = fun n => Real.log (g x + ε n) := by
        funext n; rw [Set.indicator_of_mem (hMemCompl x hx)]
      rw [hconst]
      have htend : Tendsto (fun n => g x + ε n) atTop (nhds (g x)) := by
        simpa using hεt.const_add (g x)
      exact (Real.continuousAt_log (ne_of_gt hgx)).tendsto.comp htend
  have h_vint : ∀ n, Integrable (Aᶜ.indicator (fun x => Real.log (g x + ε n))) μ :=
    fun n => (h_int n).indicator hA.compl
  -- On the zero set the integrand is the non-positive constant `log (ε n)`, so `∫ log (g + ε n) ≤ ∫ v n`.
  have h_comp : ∀ n, ∫ x, Real.log (g x + ε n) ∂μ
      ≤ ∫ x, Aᶜ.indicator (fun x => Real.log (g x + ε n)) x ∂μ := by
    intro n
    have hsplit := integral_add_compl hA (h_int n)
    have hAint : ∫ x in A, Real.log (g x + ε n) ∂μ = (μ.real A) * Real.log (ε n) := by
      rw [setIntegral_congr_fun hA (fun x hx => by rw [show g x = 0 from hx, zero_add]),
          setIntegral_const, smul_eq_mul]
    have hAle : ∫ x in A, Real.log (g x + ε n) ∂μ ≤ 0 := by
      rw [hAint]
      exact mul_nonpos_of_nonneg_of_nonpos (by positivity)
        (Real.log_nonpos (le_of_lt (hε0 n)) (hε1 n))
    have hind : ∫ x, Aᶜ.indicator (fun x => Real.log (g x + ε n)) x ∂μ
        = ∫ x in Aᶜ, Real.log (g x + ε n) ∂μ := integral_indicator hA.compl
    rw [hind]
    linarith [hsplit, hAle]
  have hc_le : ∀ n, c₀ ≤ c n := by
    intro n
    exact le_of_tendsto hct (Filter.eventually_atTop.2 ⟨n, fun m hm => hcm hm⟩)
  have hc0v : ∀ n, c₀ ≤ ∫ x, Aᶜ.indicator (fun x => Real.log (g x + ε n)) x ∂μ := by
    intro n
    linarith [hc_le n, hc n, h_comp n]
  by_cases hInt : Integrable (fun x => Real.log (g x)) μ
  · have htend := antitone_integral_tendsto hInt h_vint h_vge h_vmono h_vtend
    exact ge_of_tendsto htend (Filter.Eventually.of_forall hc0v)
  · obtain ⟨n, hn⟩ :=
      not_integrable_exists_integral_le_zero hC0 h_vint h_vle h_vge h_vmono h_vtend hInt
    have hzero : ∫ x, Real.log (g x) ∂μ = 0 := integral_undef hInt
    linarith [hc0v n, hn]

end Work.Holonomy3
