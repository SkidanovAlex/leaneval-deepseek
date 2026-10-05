import Mathlib
import Submission.Work.RPB.Defs
import Submission.Work.RPB.B5.uniform_small_rho

/-!
# B5: `ρh` is uniformly small in a one-sided small `σ`-strip

`ρh τ t σ` vanishes identically at `σ = 0` (`hρh0`), is `2π`-periodic in `t` (`hρhper`) and is
`C¹` (indeed `C^12`) on `Icc 0 1 ×ˢ univ ×ˢ Ioo (-κ) κ`.  Joint continuity on the compact box
`Icc 0 1 ×ˢ Icc 0 (2π) ×ˢ Icc (-κ/2) (κ/2)`, together with the periodicity in `t` to reduce an
arbitrary `t` to a fundamental interval, yields a single `δ ≤ κ` with `|ρh τ t σ| < ε` for every
`τ ∈ [0,1]`, every `t` and every `σ ∈ (-δ, 0)`.

The uniform-continuity bookkeeping is exactly `Work.RPB.B5.uniform_small_rho`, applied with the
smaller radius `min κ ε`; the periodic reduction to `t ∈ [0, 2π]` lives there.
-/

open scoped ContDiff

namespace Work.RPB.B5

theorem kappa_rho_small (ρh : ℝ → ℝ → ℝ → ℝ) (κ : ℝ) (hκ : 0 < κ)
    (hρh : ContDiffOn ℝ 12 (fun z : ℝ × (ℝ × ℝ) => ρh z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-κ) κ))
    (hρh0 : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ρh τ t 0 = 0)
    (hρhper : ∀ τ t σ, ρh τ (t + 2 * Real.pi) σ = ρh τ t σ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ κ ∧
      ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-δ) 0,
        |ρh τ t σ| < ε := by
  have hmin : 0 < min κ ε := lt_min hκ hε
  -- `C¹` on the smaller strip `Ioo (-(min κ ε)) (min κ ε) ⊆ Ioo (-κ) κ`.
  have hC1 : ContDiffOn ℝ 1 (fun z : ℝ × (ℝ × ℝ) => ρh z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-(min κ ε)) (min κ ε)) :=
    (hρh.of_le (by norm_num)).mono (fun p hp =>
      ⟨hp.1, trivial,
        ⟨by linarith [hp.2.2.1, min_le_left κ ε],
         by linarith [hp.2.2.2, min_le_left κ ε]⟩⟩)
  obtain ⟨δ, hδpos, hδle, hbound⟩ :=
    uniform_small_rho (rho := ρh) (ε := min κ ε) hmin hC1 hρh0 hρhper
  refine ⟨δ, hδpos, le_trans hδle (min_le_left κ ε), ?_⟩
  intro τ hτ t σ hσ
  have hσabs : |σ| ≤ δ := le_of_lt (abs_lt.mpr ⟨hσ.1, by linarith [hσ.2, hδpos]⟩)
  have hb := hbound τ hτ σ hσabs t
  have hfin : min κ ε / 2 < ε := by linarith [min_le_right κ ε, hε]
  linarith

end Work.RPB.B5
