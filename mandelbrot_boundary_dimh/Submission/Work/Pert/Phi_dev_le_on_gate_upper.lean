import Mathlib
import Submission.Work.Pert.Setup
import Submission.Work.Pert.Basic
import Submission.Work.Pert.liftF_defect_le_tauC
import Submission.Work.Pert.scale_lattice
import Submission.Work.Pert.tauC_upper_decay
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Interfaces.Fatou
import Submission.Work.Interfaces.FatouNarrow

/-!
# `Work.Pert.Phi_dev_le_on_gate_upper`

Deviation bound for a Fatou coordinate `Φm` of the lift `F_f = liftF u σ α` on the *upper end* of
the gate `Qm Ξ α`: there are `Y₀ K > 0` with

  `‖Φm z - z‖ ≤ 2 + K (1 + log (2 + M) + Ξ + log (2 + z.im))`

for every `z ∈ Qm Ξ α` with `-(Ξ+1) ≤ z.re ≤ 2` and `Y₀ ≤ z.im`.

**Route.**  The deviation is *bounded* on the upper end, and the logarithmic shape of the bound is
a very generous weakening of that.  The boundedness comes from the end asymptotics `FatouEnds` of
the FATOU contract: at the upper end of `Qm Ξ α` the lift is exponentially close to the translation
by `1` (`Work.Pert.tauC_upper_decay` gives `‖τ_f‖ ≤ M exp (-(κ z.im))` on the gate, and
`Work.Pert.liftF_defect_le_tauC` upgrades this to `‖F z - (z+1)‖ ≤ C ‖τ_f z‖`), so `FatouEnds`
applied with `ρ = 1` yields `Φm z - z → c` uniformly on every vertical strip of width `4`.  The
`Re`-range `[-(Ξ+1), 2]` is covered by finitely many such strips and we take the maximum of the
finitely many thresholds.

The pinning data (`z₀`, `M`) are not used; they only appear in the (very slack) right-hand side.
-/

namespace Work.Pert

open MandelDim Complex

noncomputable section

theorem Phi_dev_le_on_gate_upper {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    (hF : MandelDim.FatouStatement)
    {Ξ rr M : ℝ} {α σ : ℂ} {u Φm : ℂ → ℂ} {z₀ : ℂ}
    (hΞ : 0 < Ξ) (hrr : 0 < rr) (hM : 0 ≤ M)
    (hInF1 : MandelDim.InF1 α) (hα64 : ‖α‖ ≤ 1 / 64)
    (hQAdm : MandelDim.QAdm (some ((Ξ : ℂ) - 1 / α)) (some (-(Ξ : ℂ))))
    (hσ : σ ≠ 0) (hnorm : 1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α))
    (hu : DifferentiableOn ℂ u (Metric.ball (0 : ℂ) rr))
    (hu2 : ∀ z ∈ Metric.ball (0 : ℂ) rr, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2)
    (hτQ : ∀ z ∈ Work.Pert.Qm Ξ α, Work.Pert.tauC σ α z ∈ Metric.ball (0 : ℂ) rr)
    (hNT : MandelDim.NearTranslationL1 (Work.Pert.liftF u σ α) (Work.Pert.Qm Ξ α))
    (hΦm : MandelDim.IsFatouCoordOn (Work.Pert.liftF u σ α) Φm (Work.Pert.Qm Ξ α))
    (hz₀ : z₀ ∈ Work.Pert.Qm Ξ α) (hz₀re : -(M + 1) ≤ z₀.re) (hz₀re' : z₀.re ≤ -M + 1)
    (hz₀im : |z₀.im| ≤ 1)
    (hpin : Φm z₀ = (((-M : ℝ)) : ℂ)) :
    ∃ Y₀ K : ℝ, 0 < Y₀ ∧ 0 < K ∧ ∀ z : ℂ, z ∈ Work.Pert.Qm Ξ α → -(Ξ + 1) ≤ z.re →
      z.re ≤ 2 → Y₀ ≤ z.im →
      ‖Φm z - z‖ ≤ 2 + K * (1 + Real.log (2 + M) + Ξ + Real.log (2 + z.im)) := by
  -- ## Step 0: `α ≠ 0` (from `InF1 α`)
  have hα0 : α ≠ 0 := by
    intro h
    have h1 : 0 < α.re := lt_of_le_of_lt (abs_nonneg α.im) hInF1
    rw [h] at h1
    simp only [Complex.zero_re] at h1
    exact lt_irrefl 0 h1
  -- ## Step 1: the near-translation defect of `F` is `O ‖τ_f‖` on the gate
  have hNT32 : ∀ z ∈ Work.Pert.Qm Ξ α,
      ‖Work.Pert.liftF u σ α z - (z + 1)‖ ≤ 1 / 32 :=
    fun z hz => (hNT.1.2 z hz).1
  obtain ⟨C, hCpos, hCbound⟩ :=
    Work.Pert.liftF_defect_le_tauC hΞ hα0 hσ hrr hInF1 hα64 hnorm hu hu2 hτQ hNT32
  -- ## Step 2: exponential decay of `τ_f` at the upper end
  obtain ⟨Mτ, κ, Yτ, hMτpos, hκpos, hτdec⟩ := Work.Pert.tauC_upper_decay hΞ hInF1 hσ
  -- ## Step 3: exponential decay of the defect
  have hdecay : ∀ z ∈ Work.Pert.Qm Ξ α, Yτ < z.im →
      ‖Work.Pert.liftF u σ α z - (z + 1)‖ ≤ (C * Mτ) * Real.exp (-(κ * z.im)) := by
    intro z hz hY
    calc ‖Work.Pert.liftF u σ α z - (z + 1)‖
        ≤ C * ‖Work.Pert.tauC σ α z‖ := hCbound z hz
      _ ≤ C * (Mτ * Real.exp (-(κ * z.im))) :=
            mul_le_mul_of_nonneg_left (hτdec z hz hY) (le_of_lt hCpos)
      _ = (C * Mτ) * Real.exp (-(κ * z.im)) := by ring
  -- ## Step 4: the end asymptotics of the Fatou coordinate, via the FATOU contract
  obtain ⟨_, _, _, _, _, hEnds⟩ := hF
  obtain ⟨c, hc⟩ := (hEnds (some ((Ξ : ℂ) - 1 / α)) (some (-(Ξ : ℂ)))
      (Work.Pert.liftF u σ α) Φm (1 : ℂ) (C * Mτ) κ Yτ hQAdm hNT.1 hΦm hκpos
      (by norm_num)).1 hdecay
  -- `hc : ∀ x, ∀ ε > 0, ∃ Y', ∀ z ∈ Qm Ξ α, Y' < z.im → |z.re - x| ≤ 2 → ‖Φm z - z - c‖ < ε`
  -- ## Step 5: cover `[-(Ξ+1), 2]` by finitely many strips of half-width `2`
  set a : ℝ := -(Ξ + 1) with hadef
  set N : ℕ := ⌊(2 - a) / 2⌋₊ + 1 with hNdef
  have hN1 : 0 < N := by rw [hNdef]; omega
  have hchoice : ∀ j : ℕ, ∃ Y' : ℝ, ∀ z ∈ Work.Pert.Qm Ξ α,
      Y' < z.im → |z.re - (a + 2 * (j : ℝ) + 1)| ≤ 2 → ‖Φm z - z - c‖ < 1 := by
    intro j
    obtain ⟨Y', hY'⟩ := hc (a + 2 * (j : ℝ) + 1) 1 (by norm_num)
    exact ⟨Y', fun z hz h1 h2 => by simpa using hY' z hz h1 h2⟩
  choose Yf hYf using hchoice
  set Ysup : ℝ := (Finset.range N).sup' ⟨0, Finset.mem_range.mpr hN1⟩ Yf with hYsupdef
  refine ⟨max (Ysup + 1) 1, ‖c‖ + 1, ?_, ?_, ?_⟩
  · exact lt_of_lt_of_le one_pos (le_max_right _ _)
  · positivity
  · intro z hz hre1 hre2 him
    -- the window whose centre `a + 2j + 1` captures `z.re`
    have hzre_le : z.re ≤ 2 := hre2
    set j : ℕ := ⌊(z.re - a) / 2⌋₊ with hjdef
    have hfl1 : (j : ℝ) ≤ (z.re - a) / 2 := by
      rw [hjdef]; exact Nat.floor_le (by positivity)
    have hfl2 : (z.re - a) / 2 < (j : ℝ) + 1 := by
      rw [hjdef]; exact Nat.lt_floor_add_one _
    have hjle : j ≤ ⌊(2 - a) / 2⌋₊ := Nat.le_floor (by linarith)
    have hjN : j < N := by rw [hNdef]; omega
    have hwin : |z.re - (a + 2 * (j : ℝ) + 1)| ≤ 2 := by
      have hs : z.re - (a + 2 * (j : ℝ) + 1) = (z.re - a) - 2 * (j : ℝ) - 1 := by ring
      rw [hs, abs_le]
      constructor <;> linarith
    have hsup : Yf j ≤ Ysup := by
      rw [hYsupdef]
      exact Finset.le_sup' Yf (Finset.mem_range.mpr hjN)
    have hYj : Yf j < z.im := by
      have h2 :  Ysup + 1 ≤ max (Ysup + 1) 1 := le_max_left _ _
      linarith
    have hdev : ‖Φm z - z - c‖ < 1 := hYf j z hz hYj hwin
    -- ## Step 6: the elementary arithmetic, using that `K` is unrestricted
    have hzge1 : (1 : ℝ) ≤ z.im := le_trans (le_max_right ( Ysup + 1) 1) him
    have hlogM : 0 ≤ Real.log (2 + M) := Real.log_nonneg (by linarith)
    have hlogy : 0 ≤ Real.log (2 + z.im) := Real.log_nonneg (by linarith)
    have hL : 1 ≤ 1 + Real.log (2 + M) + Ξ + Real.log (2 + z.im) := by linarith
    have h1 : ‖Φm z - z‖ ≤ 1 + ‖c‖ := by
      calc ‖Φm z - z‖ = ‖(Φm z - z - c) + c‖ := by congr 1; ring
        _ ≤ ‖Φm z - z - c‖ + ‖c‖ := norm_add_le _ _
        _ ≤ 1 + ‖c‖ := by linarith [le_of_lt hdev]
    have h2 : 1 + ‖c‖ ≤ 2 + (‖c‖ + 1) * (1 + Real.log (2 + M) + Ξ + Real.log (2 + z.im)) := by
      have := mul_le_mul_of_nonneg_left hL (by positivity : (0 : ℝ) ≤ ‖c‖ + 1)
      linarith
    linarith [h1, h2]

end

end Work.Pert
