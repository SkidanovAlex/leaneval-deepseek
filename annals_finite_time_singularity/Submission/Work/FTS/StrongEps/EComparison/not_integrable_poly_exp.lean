import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Measure.Haar.Unique

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EComparison

open MeasureTheory

/-- If a real function is bounded below by a positive constant `ε` on a half-line
`[a, ∞)`, it cannot be integrable: the set `{t | ε ≤ g t}` then contains `Ici a`,
which has infinite measure, contradicting `Integrable.measure_ge_lt_top`. -/
lemma not_integrable_of_forall_ge_atTop {g : ℝ → ℝ} {ε a : ℝ} (hε : 0 < ε)
    (h : ∀ t, a ≤ t → ε ≤ g t) : ¬ MeasureTheory.Integrable g := by
  intro hg
  have hfin : volume {t : ℝ | ε ≤ g t} < ⊤ := hg.measure_ge_lt_top hε
  have hle : volume (Set.Ici a) ≤ volume {t : ℝ | ε ≤ g t} :=
    MeasureTheory.measure_mono fun t ht => h t ht
  rw [Real.volume_Ici] at hle
  exact absurd hle (not_le.mpr hfin)

/-- Same statement on a half-line `(-∞, a]`, obtained by reflecting `t ↦ -t`
(Lebesgue measure on `ℝ` is invariant under negation). -/
lemma not_integrable_of_forall_ge_atBot {g : ℝ → ℝ} {ε a : ℝ} (hε : 0 < ε)
    (h : ∀ t, t ≤ a → ε ≤ g t) : ¬ MeasureTheory.Integrable g := by
  intro hg
  have hg' : MeasureTheory.Integrable (fun t : ℝ => g (-t)) := hg.comp_neg
  exact not_integrable_of_forall_ge_atTop (g := fun t : ℝ => g (-t)) (ε := ε) (a := -a) hε
    (fun t ht => by simpa using h (-t) (by linarith)) hg'

/-- For `c2 ≠ 0` the affine function `c1 + c2 * t` has absolute value at least `1`
as soon as `|t|` is large enough. -/
lemma exists_abs_ge_one_of_ne_zero {c1 c2 : ℝ} (hc2 : c2 ≠ 0) :
    ∃ a : ℝ, 0 ≤ a ∧ ∀ t : ℝ, a ≤ |t| → (1 : ℝ) ≤ |c1 + c2 * t| := by
  have hc2pos : 0 < |c2| := abs_pos.mpr hc2
  refine ⟨(|c1| + 1) / |c2|, by positivity, fun t ht => ?_⟩
  have ht' : |c1| + 1 ≤ |t| * |c2| := (div_le_iff₀ hc2pos).mp ht
  have h3 : |c1| + 1 ≤ |c2 * t| := by
    rw [abs_mul]
    calc |c1| + 1 ≤ |t| * |c2| := ht'
      _ = |c2| * |t| := mul_comm _ _
  have h4 := abs_sub_abs_le_abs_sub (c2 * t) (-c1)
  rw [abs_neg, sub_neg_eq_add] at h4
  have hcomm : |c1 + c2 * t| = |c2 * t + c1| := by rw [add_comm]
  rw [hcomm]
  linarith

theorem not_integrable_poly_exp {r c1 c2 : ℝ}
    (hint : MeasureTheory.Integrable (fun t : ℝ => ((c1 + c2 * t) * Real.exp (r * t)) ^ 2)) :
    c1 = 0 ∧ c2 = 0 := by
  by_contra hcon
  have hcon' : c1 ≠ 0 ∨ c2 ≠ 0 := not_and_or.mp hcon
  have hg : ¬ MeasureTheory.Integrable
      (fun t : ℝ => ((c1 + c2 * t) * Real.exp (r * t)) ^ 2) := by
    by_cases hr : 0 ≤ r
    · -- `r ≥ 0`: look at `t → +∞`
      rcases eq_or_ne c2 0 with hc2 | hc2
      · -- `c2 = 0`, `c1 ≠ 0`: `g t = c1^2 * exp (2 r t) ≥ c1^2` for `t ≥ 0`
        have hc1 : c1 ≠ 0 := by
          rcases hcon' with h | h
          · exact h
          · exact (h hc2).elim
        refine not_integrable_of_forall_ge_atTop
          (g := fun t : ℝ => ((c1 + c2 * t) * Real.exp (r * t)) ^ 2)
          (ε := c1 ^ 2) (a := 0) (sq_pos_of_ne_zero hc1) ?_
        intro t ht
        have hexp : 1 ≤ Real.exp (r * t) := by
          rw [← Real.exp_zero]
          exact Real.exp_le_exp.mpr (mul_nonneg hr ht)
        have hrew : ((c1 + c2 * t) * Real.exp (r * t)) ^ 2
            = c1 ^ 2 * (Real.exp (r * t)) ^ 2 := by
          rw [hc2]; ring
        rw [hrew]
        have h2 : 1 ≤ (Real.exp (r * t)) ^ 2 := by
          nlinarith [hexp, Real.exp_pos (r * t)]
        nlinarith [sq_nonneg c1]
      · -- `c2 ≠ 0`, `r ≥ 0`
        obtain ⟨a, ha0, ha⟩ := exists_abs_ge_one_of_ne_zero hc2
        refine not_integrable_of_forall_ge_atTop
          (g := fun t : ℝ => ((c1 + c2 * t) * Real.exp (r * t)) ^ 2)
          (ε := 1) (a := a) one_pos ?_
        intro t ht
        have ht0 : 0 ≤ t := le_trans ha0 ht
        have habs : 1 ≤ |c1 + c2 * t| := ha t (by rw [abs_of_nonneg ht0]; exact ht)
        have hexp : 1 ≤ Real.exp (r * t) := by
          rw [← Real.exp_zero]
          exact Real.exp_le_exp.mpr (mul_nonneg hr ht0)
        have hmul : 1 ≤ |(c1 + c2 * t) * Real.exp (r * t)| := by
          rw [abs_mul, abs_of_pos (Real.exp_pos (r * t))]
          exact one_le_mul_of_one_le_of_one_le habs hexp
        calc (1 : ℝ) = 1 ^ 2 := by ring
          _ ≤ |(c1 + c2 * t) * Real.exp (r * t)| ^ 2 := by
              nlinarith [hmul, abs_nonneg ((c1 + c2 * t) * Real.exp (r * t))]
          _ = ((c1 + c2 * t) * Real.exp (r * t)) ^ 2 := by rw [sq_abs]
    · -- `r < 0`: look at `t → -∞`
      have hr' : r < 0 := not_le.mp hr
      rcases eq_or_ne c2 0 with hc2 | hc2
      · -- `c2 = 0`, `c1 ≠ 0`: `g t = c1^2 * exp (2 r t) ≥ c1^2` for `t ≤ 0`
        have hc1 : c1 ≠ 0 := by
          rcases hcon' with h | h
          · exact h
          · exact (h hc2).elim
        refine not_integrable_of_forall_ge_atBot
          (g := fun t : ℝ => ((c1 + c2 * t) * Real.exp (r * t)) ^ 2)
          (ε := c1 ^ 2) (a := 0) (sq_pos_of_ne_zero hc1) ?_
        intro t ht
        have hexp : 1 ≤ Real.exp (r * t) := by
          rw [← Real.exp_zero]
          exact Real.exp_le_exp.mpr (mul_nonneg_of_nonpos_of_nonpos hr'.le ht)
        have hrew : ((c1 + c2 * t) * Real.exp (r * t)) ^ 2
            = c1 ^ 2 * (Real.exp (r * t)) ^ 2 := by
          rw [hc2]; ring
        rw [hrew]
        have h2 : 1 ≤ (Real.exp (r * t)) ^ 2 := by
          nlinarith [hexp, Real.exp_pos (r * t)]
        nlinarith [sq_nonneg c1]
      · -- `c2 ≠ 0`, `r < 0`
        obtain ⟨a, ha0, ha⟩ := exists_abs_ge_one_of_ne_zero hc2
        refine not_integrable_of_forall_ge_atBot
          (g := fun t : ℝ => ((c1 + c2 * t) * Real.exp (r * t)) ^ 2)
          (ε := 1) (a := -a) one_pos ?_
        intro t ht
        have ht0 : t ≤ 0 := by linarith
        have hleabs : a ≤ |t| := by rw [abs_of_nonpos ht0]; linarith
        have habs : 1 ≤ |c1 + c2 * t| := ha t hleabs
        have hexp : 1 ≤ Real.exp (r * t) := by
          rw [← Real.exp_zero]
          exact Real.exp_le_exp.mpr (mul_nonneg_of_nonpos_of_nonpos hr'.le ht0)
        have hmul : 1 ≤ |(c1 + c2 * t) * Real.exp (r * t)| := by
          rw [abs_mul, abs_of_pos (Real.exp_pos (r * t))]
          exact one_le_mul_of_one_le_of_one_le habs hexp
        calc (1 : ℝ) = 1 ^ 2 := by ring
          _ ≤ |(c1 + c2 * t) * Real.exp (r * t)| ^ 2 := by
              nlinarith [hmul, abs_nonneg ((c1 + c2 * t) * Real.exp (r * t))]
          _ = ((c1 + c2 * t) * Real.exp (r * t)) ^ 2 := by rw [sq_abs]
  exact hg hint

end Work.FTS.StrongEps.EComparison
