import Mathlib
import Submission.Work.RPB.B5.chartLev_inverse
import Submission.Work.RPB.B5.chart_C12
import Submission.Work.RPB.B5.chartLev_eq_sq_mul_hc
import Submission.Work.RPB.B5.chartLev_strip_facts
import Submission.Work.RPB.B5.level_confine
import Submission.Work.RPB.B5.deriv_slice_ne_zero

/-!
# B5: monotonicity of a level inverse of the chord chart

Given the `ρ = r²`-chart `W` of the chord annulus and a level inverse `ρh` of its level
function `chartLev W τ t ρ = K₀ (W τ t ρ) + 1` on the interval `(-ε, ε)`
(`chartLev W τ t (ρh τ t σ) = -σ` and `ρh τ t 0 = 0`), we produce a possibly smaller interval
`(-κ, κ)`, `κ ≤ ε`, on which

* the `σ`-derivative of `ρh τ t` never vanishes, and
* `ρh τ t σ > 0` for `σ ∈ (-κ, 0)`.

## Proof

The level function `chartLev W` is `C¹²` on the box `[0,1] × ℝ × (-ρ₀,ρ₀)` and `2π`-periodic
in `t`; it vanishes at `ρ = 0` and its `ρ`-derivative at `0` is `‖c_τ'(t)‖² > 0`
(`chartLev_deriv_zero`, from the chord identity `hWchord`).  After extending it in `τ`
(`slabExtendPeriodic`) and globalising (`slabGlobalExtendPeriodic_C12`), the uniform strip
bound `slabDerivBounds` gives `δ > 0` and `η > 0` such that, uniformly in `(τ, t)`,

* `chartLev` is negative on `(-δ, 0)` and positive on `(0, δ)` (strict monotonicity on the
  strip), and
* `η ≤ chartLev(δ/2)` and `chartLev(-δ/2) ≤ -η` (mean value theorem).

This is `Work.RPB.B5.chartLev_strip_facts`.  With `κ := min (ε/2) η`, the elementary
confinement lemma `Work.RPB.B5.level_confine` (intermediate value theorem, using that
`ρh τ t σ` is a preimage of `-σ` under `chartLev`) gives `|ρh τ t σ| < δ` for `|σ| ≤ κ` — so
the argument of `chartLev` stays in the open interval where it is smooth — and
`ρh τ t σ > 0` for `σ ∈ (-κ, 0)`.  Finally the chain rule applied to
`chartLev W τ t (ρh τ t σ) = -σ` on `(-κ, κ) ⊆ (-ε, ε)` gives
`deriv (chartLev) (ρh τ t σ) * deriv (ρh τ t) σ = -1`, hence the non-vanishing of the
derivative (`Work.RPB.B5.deriv_slice_ne_zero`).
-/

namespace Work.RPB.B5

/-- Slicing a `C¹²` function of `(τ, t, σ)` in its last variable: for fixed `(τ, t)` with
`τ ∈ [0,1]`, the slice `σ ↦ f (τ, (t, σ))` is `C¹²` on `(-a, a)`. -/
private lemma contDiffOn_slice_box {f : ℝ × (ℝ × ℝ) → ℝ} {a : ℝ}
    (h : ContDiffOn ℝ 12 f (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-a) a))
    {τ t : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    ContDiffOn ℝ 12 (fun σ : ℝ => f (τ, (t, σ))) (Set.Ioo (-a) a) :=
  h.comp (by fun_prop) (fun σ hσ => ⟨hτ, trivial, hσ⟩)

theorem chart_rho_mono (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (ρ₀ ε : ℝ) (W : ℝ → ℝ → ℝ → Work.RPV.PS) (ρh : ℝ → ℝ → ℝ → ℝ)
    (hρ₀ : 0 < ρ₀)
    (hW : ContDiffOn ℝ 12 (fun z : ℝ × (ℝ × ℝ) => W z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-ρ₀) ρ₀))
    (hWchord : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ r ∈ Set.Ioc (0 : ℝ) (Real.pi / 2),
      W τ t (r ^ 2) = Work.RPB.chordSurf CI.c a τ t r)
    (hWper : ∀ τ t ρ, W τ (t + 2 * Real.pi) ρ = Work.RPV.Tk 1 (W τ t ρ))
    (hε : 0 < ε) (hεle : ε ≤ ρ₀)
    (hρh : ContDiffOn ℝ 12 (fun z : ℝ × (ℝ × ℝ) => ρh z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-ε) ε))
    (hρh0 : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ρh τ t 0 = 0)
    (hρhl : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-ε) ε,
      Work.RPV.K0 (W τ t (ρh τ t σ)) + 1 = -σ) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ ε ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-κ) κ,
        deriv (fun s : ℝ => ρh τ t s) σ ≠ 0) ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-κ) 0, 0 < ρh τ t σ) := by
  -- the level identity, written with the level function
  have hρhl' : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-ε) ε,
      Work.RPB.B5.chartLev W τ t (ρh τ t σ) = -σ :=
    fun τ hτ t σ hσ => hρhl τ hτ t σ hσ
  -- the uniform sign facts and the quantitative bounds for the level function
  obtain ⟨δ, hδpos, hδρ₀, η, hηpos, hstrip⟩ :=
    Work.RPB.B5.chartLev_strip_facts CI a ρ₀ ε W ρh hρ₀ hW hWchord hWper hε hρh0 hρhl'
  -- smoothness of the `σ`-slices of `ρh`
  have hρhsl : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ,
      ContDiffOn ℝ 12 (fun σ : ℝ => ρh τ t σ) (Set.Ioo (-ε) ε) :=
    fun τ hτ t =>
      contDiffOn_slice_box (f := fun z : ℝ × (ℝ × ℝ) => ρh z.1 z.2.1 z.2.2) hρh hτ
  have hκ0pos : 0 < min (ε / 2) η := lt_min (by linarith) hηpos
  have hκ0ε : min (ε / 2) η ≤ ε := le_trans (min_le_left _ _) (by linarith)
  -- the confinement of the level inverse, uniformly in `(τ, t)`
  have key : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ,
      (∀ σ ∈ Set.Icc (-(min (ε / 2) η)) (min (ε / 2) η), |ρh τ t σ| < δ) ∧
      (∀ σ ∈ Set.Ioo (-(min (ε / 2) η)) 0, 0 < ρh τ t σ) := by
    intro τ hτ t
    refine Work.RPB.B5.level_confine (fun ρ => chartLev W τ t ρ) (fun s => ρh τ t s) δ η
      (min (ε / 2) η) hδpos hηpos (min_le_right _ _) ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · -- the level function vanishes at `ρ = 0`
      have h := hρhl τ hτ t 0 (Set.mem_Ioo.mpr ⟨by linarith, hε⟩)
      rw [hρh0 τ hτ t] at h
      simpa [chartLev] using h
    · -- negative on `(-δ, 0)`
      exact (hstrip τ hτ t).1
    · -- `η ≤ chartLev (δ/2)`
      exact (hstrip τ hτ t).2.2.1
    · -- `chartLev (-δ/2) ≤ -η`
      exact (hstrip τ hτ t).2.2.2
    · -- continuity of the `σ`-slice on the closed interval
      refine ((hρhsl τ hτ t).continuousOn).mono ?_
      intro σ hσ
      obtain ⟨h1, h2⟩ := Set.mem_Icc.mp hσ
      exact Set.mem_Ioo.mpr ⟨by linarith [h1, min_le_left (ε / 2) η, hε],
        by linarith [h2, min_le_left (ε / 2) η, hε]⟩
    · -- vanishing at `σ = 0`
      exact hρh0 τ hτ t
    · -- the level identity
      intro σ hσ
      obtain ⟨h1, h2⟩ := Set.mem_Icc.mp hσ
      exact hρhl' τ hτ t σ (Set.mem_Ioo.mpr ⟨by linarith [h1, min_le_left (ε / 2) η, hε],
        by linarith [h2, min_le_left (ε / 2) η, hε]⟩)
  refine ⟨min (ε / 2) η, hκ0pos, hκ0ε, ?_, ?_⟩
  · -- non-vanishing of the derivative, by the chain rule
    intro τ hτ t σ hσ
    exact Work.RPB.B5.deriv_slice_ne_zero W ρh ρ₀ ε δ (min (ε / 2) η) hW hρh hρhl'
      (fun τ hτ t σ hσ => (key τ hτ t).1 σ hσ) hδρ₀ hκ0ε τ hτ t σ hσ
  · -- positivity on the negative half of the interval
    intro τ hτ t σ hσ
    exact (key τ hτ t).2 σ hσ

end Work.RPB.B5
