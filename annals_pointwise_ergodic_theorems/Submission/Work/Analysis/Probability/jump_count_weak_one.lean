import Mathlib
import Submission.Work.Analysis.Probability.kpath_le_greedy_jumps
import Submission.Work.Analysis.Probability.greedy_count_weak_one
import Submission.Port.Aesm

/-!
# The weak `(1,1)` jump-count estimate for martingales of conditional expectations

The `λ`-jump counting functional `Jcount F λ` of Krause--Mirek--Tao (`jumpCount.lean`) counts, for
a path, the maximal number of gaps exceeding `λ` over all subsequences.  Here we prove the sharp
weak `(1,1)` bound

  `μ {ω | y < Jcount (E[f | ℱ n]) λ ω} ≤ C / (λ √y) · ‖f‖₁`

for the martingale `E[f | ℱ n]` of an integrable function `f` on a σ-finite filtered measure
space.  This is the `r = 2` endpoint of Lépingle's inequality, i.e. the martingale jump
inequality of Jones--Seeger--Wright (Trans. AMS 360 (2008), (5)) with `r = 2`.

The proof has two ingredients, both isolated in this directory:

* `kpath_le_greedy_jumps`: the oscillation count `Kpath` is dominated by the number of greedy
  `δ`-jumps of the path (`δ = λ/2`), because inside a greedy block the path varies by at most
  `2 δ ≤ λ`;
* `greedy_count_weak_one`: the greedy `δ`-jump count of a martingale `H` with
  `sup n ∫ |H n| ≤ B` satisfies the weak `(1,1)` estimate `μ {y < N_δ} ≤ C B / (δ √y)`.

The final constant is `2 C`; the arithmetic is the `δ = λ/2` substitution combined with
`eLpNorm f 1 μ = ofReal (∫ |f|)`.
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace Work.Analysis.Probability

theorem jump_count_weak_one :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
      [MeasureTheory.SigmaFinite μ] (ℱ : MeasureTheory.Filtration ℕ ‹MeasurableSpace Ω›)
      [MeasureTheory.SigmaFiniteFiltration μ ℱ] (f : Ω → ℝ),
      MeasureTheory.Integrable f μ →
      ∀ lam : ℝ, 0 < lam → ∀ y : ℝ, 0 < y →
        μ {ω | ENNReal.ofReal y < Work.Analysis.Probability.Jcount (fun n => MeasureTheory.condExp (ℱ n) μ f) lam ω}
          ≤ ENNReal.ofReal (C / (lam * Real.sqrt y)) * MeasureTheory.eLpNorm f 1 μ := by
  classical
  obtain ⟨C, hCpos, hCrux⟩ := greedy_count_weak_one
  refine ⟨2 * C, by positivity, ?_⟩
  intro Ω _ μ _ ℱ _ f hf lam hlam y hy
  set B : ℝ := ∫ ω, |f ω| ∂μ with hBdef
  have harg : 2 * (lam / 2) ≤ lam := by linarith
  have hset : {ω | ENNReal.ofReal y < Jcount (fun n => MeasureTheory.condExp (ℱ n) μ f) lam ω}
      ⊆ {ω | ENNReal.ofReal y
            < greedyJumps (fun n => MeasureTheory.condExp (ℱ n) μ f ω) (lam / 2)} := by
    intro ω hω
    have h1 : Jcount (fun n => MeasureTheory.condExp (ℱ n) μ f) lam ω
        = Kpath (fun n => MeasureTheory.condExp (ℱ n) μ f ω) lam := rfl
    simp only [Set.mem_ofPred_eq] at hω
    rw [h1] at hω
    exact lt_of_lt_of_le hω (kpath_le_greedy_jumps _ (by linarith) harg)
  have hJensen : ∀ n, ∫ ω, |MeasureTheory.condExp (ℱ n) μ f ω| ∂μ ≤ B := by
    intro n
    rw [hBdef]
    have h1 : (fun ω => |MeasureTheory.condExp (ℱ n) μ f ω|) ≤ᵐ[μ]
        (fun ω => MeasureTheory.condExp (ℱ n) μ (fun ω => |f ω|) ω) := by
      simpa only [Real.norm_eq_abs] using
        (norm_condExp_le (m := ℱ n) (μ := μ) (f := f))
    calc ∫ ω, |MeasureTheory.condExp (ℱ n) μ f ω| ∂μ
        ≤ ∫ ω, MeasureTheory.condExp (ℱ n) μ (fun ω => |f ω|) ω ∂μ :=
          integral_mono_ae
            (MeasureTheory.integrable_condExp (μ := μ) (m := ℱ n) (f := f)).abs
            (MeasureTheory.integrable_condExp (μ := μ) (m := ℱ n) (f := fun ω => |f ω|)) h1
      _ = ∫ ω, |f ω| ∂μ := MeasureTheory.integral_condExp (μ := μ) (m := ℱ n) (ℱ.le n)
  have hcrux := hCrux (μ := μ) (ℱ := ℱ) (H := fun n => MeasureTheory.condExp (ℱ n) μ f)
      (MeasureTheory.martingale_condExp f ℱ μ) B hJensen (lam / 2) (by linarith) y hy
  have heLp : MeasureTheory.eLpNorm f 1 μ = ENNReal.ofReal B := by
    rw [MeasureTheory.eLpNorm_one_eq_lintegral_enorm (hf := by pw_aesm),
      ← MeasureTheory.ofReal_integral_norm_eq_lintegral_enorm hf, hBdef]
    rw [show (∫ (x : Ω), ‖f x‖ ∂μ) = ∫ (ω : Ω), |f ω| ∂μ from
      integral_congr_ae (Filter.Eventually.of_forall fun ω => Real.norm_eq_abs (f ω))]
  calc μ {ω | ENNReal.ofReal y < Jcount (fun n => MeasureTheory.condExp (ℱ n) μ f) lam ω}
      ≤ μ {ω | ENNReal.ofReal y
              < greedyJumps (fun n => MeasureTheory.condExp (ℱ n) μ f ω) (lam / 2)} :=
        measure_mono hset
    _ ≤ ENNReal.ofReal (C * B / (lam / 2 * Real.sqrt y)) := hcrux
    _ = ENNReal.ofReal (2 * C / (lam * Real.sqrt y)) * MeasureTheory.eLpNorm f 1 μ := by
        rw [heLp, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp

end Work.Analysis.Probability
