import Mathlib
import Submission.Work.FatouWindow.fatouDerivSetup
import Submission.Work.FatouWindow.fatouU_apriori_bound
import Submission.Work.FatouWindow.fatouU_compact_bound
import Submission.Work.FatouWindow.fatouU_deep_bound

/-!
# FATOU-L1: the a-priori strip bound on the WIDE strip `(x₀ - 3/4, x₀ + 3)`

`Work.FatouWindow.fatouU_apriori_bound` bounds `fatouU = Φ' - 1` and `Φ''` (for the canonical Fatou
coordinate `Φ = fatouCoord hadm hF`) on the strip `(x₀ - 1/2, x₀ + 2)`.  Here the same bound is
proved on the strictly wider strip `(x₀ - 3/4, x₀ + 3)`, which is what the downstream assembly
needs.

The proof is the same deep/shallow dichotomy:

* **deep**, `T < min (vmLeft a z) (vmRight b z)` with `T = 2 (R₁ + δ)`, `δ = min (1/8) (R₁/2)`
  (and `a ∈ b₁`, `b ∈ b₂` chosen vertices): the disc of radius `R₁` around every nearby point is
  inside `Qreg`, and Shishikura's estimate `A.2.4(i)` (`Work.FatouCH.fatouDerivEstimate`) plus
  Cauchy's estimate give the *uniform* bounds `C₂/R₁ + 1/31` (for `fatouU`) and
  `(C₂/R₁ + 1/31)/δ` (for `Φ''`).  This is `Work.FatouWindow.fatouU_deep_bound`; it is uniform over the
  whole real window, so widening `(x₀ - 1/2, x₀ + 2)` to `(x₀ - 3/4, x₀ + 3)` costs nothing here.
* **shallow**, `min ≤ T`: then `|z.im| ≤ T + max |a.im| |b.im| =: τ`, so `z` lies in the compact
  rectangle `{x₀ - 3/4 ≤ Re ≤ x₀ + 3, |Im| ≤ τ}`.  On that rectangle (which is still contained in
  `Qreg b₁ b₂`, since `Re z - a.re > 1/4 > 0` and `b.re - Re z > 0`) the compactness bound
  `Work.FatouWindow.fatouU_compact_bound` applies verbatim.

Only the geometry of the rectangle changes with respect to `fatouU_apriori_bound`; the analytic
inputs are reused unchanged.
-/

namespace Work.FatouWindow

open Work.FatouL1

open MandelDim Set Metric

noncomputable section

variable {b₁ b₂ : Option ℂ} {F : ℂ → ℂ} {x₀ : ℝ}

/-- The rectangle `{l ≤ Re z ≤ u, |Im z| ≤ τ}` is compact (the general-bounds version of
`Work.FatouWindow.isCompact_rect`). -/
lemma isCompact_rect_wide (l u τ : ℝ) :
    IsCompact {z : ℂ | l ≤ z.re ∧ z.re ≤ u ∧ |z.im| ≤ τ} := by
  have heq : {z : ℂ | l ≤ z.re ∧ z.re ≤ u ∧ |z.im| ≤ τ}
      = Set.Icc l u ×ℂ Set.Icc (-τ) τ := by
    ext z
    simp only [Set.mem_ofPred_eq, Complex.mem_reProdIm, Set.mem_Icc, abs_le]
    tauto
  rw [heq]
  exact isCompact_Icc.reProdIm isCompact_Icc

theorem fatouU_apriori_bound_wide {b₁ b₂ : Option ℂ} {F : ℂ → ℂ} {x₀ : ℝ}
    (hadm : MandelDim.QAdm b₁ b₂) (hF : MandelDim.NearTranslationL1 F (MandelDim.Qreg b₁ b₂))
    (h₁ : ∀ a ∈ b₁, a.re + 1 < x₀) (h₂ : ∀ b ∈ b₂, x₀ + 3 < b.re) :
    ∃ B : ℝ, ∀ z : ℂ, x₀ - 3 / 4 < z.re → z.re < x₀ + 3 →
      ‖Work.FatouWindow.fatouU hadm hF z‖ ≤ B ∧
      ‖iteratedDeriv 2 (Work.FatouWindow.fatouCoord hadm hF) z‖ ≤ B := by
  obtain ⟨R₁, C₁, C₂, hR₁pos, _hC₁pos, hC₂pos, hEst⟩ := Work.FatouCH.fatouDerivEstimate
  set δ : ℝ := min (1 / 8) (R₁ / 2) with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]; exact lt_min (by norm_num) (by linarith)
  have hδlt : δ < R₁ := by
    rw [hδdef]
    have := min_le_right (1 / 8 : ℝ) (R₁ / 2)
    linarith
  set T : ℝ := 2 * (R₁ + δ) with hTdef
  have hTpos : 0 < T := by rw [hTdef]; linarith
  have core : ∀ (a b : ℂ), a.re + 1 < x₀ → x₀ + 3 < b.re →
      MandelDim.Qreg (some a) (some b) ⊆ MandelDim.Qreg b₁ b₂ →
      ∃ B : ℝ, ∀ z : ℂ, x₀ - 3 / 4 < z.re → z.re < x₀ + 3 →
        ‖Work.FatouWindow.fatouU hadm hF z‖ ≤ B ∧
        ‖iteratedDeriv 2 (Work.FatouWindow.fatouCoord hadm hF) z‖ ≤ B := by
    intro a b ha hb hsub
    set τ : ℝ := T + max |a.im| |b.im| with hτdef
    set K : Set ℂ := {z : ℂ | x₀ - 3 / 4 ≤ z.re ∧ z.re ≤ x₀ + 3 ∧ |z.im| ≤ τ} with hKdef
    have hKc : IsCompact K := by
      rw [hKdef]
      exact isCompact_rect_wide (x₀ - 3 / 4) (x₀ + 3) τ
    have hKQ : K ⊆ MandelDim.Qreg b₁ b₂ := by
      intro z hz
      rw [hKdef] at hz
      obtain ⟨h1, h2, h3⟩ := hz
      refine hsub ?_
      rw [mem_Qreg_some_some]
      refine ⟨?_, ?_⟩
      · simp only [vmLeft]
        linarith [h1, ha, abs_nonneg (z.im - a.im)]
      · simp only [vmRight]
        linarith [h2, hb, abs_nonneg (z.im - b.im)]
    obtain ⟨BK, _hBK0, hBK⟩ := fatouU_compact_bound hadm hF hKc hKQ
    have hdeep : ∀ z : ℂ, T < min (vmLeft a z) (vmRight b z) →
        ‖Work.FatouWindow.fatouU hadm hF z‖ ≤ C₂ / R₁ + 1 / 31 ∧
        ‖iteratedDeriv 2 (Work.FatouWindow.fatouCoord hadm hF) z‖ ≤ (C₂ / R₁ + 1 / 31) / δ := by
      intro z hz
      have hz2 : 2 * (R₁ + δ) < min (vmLeft a z) (vmRight b z) := by
        rw [hTdef] at hz
        exact hz
      refine fatouU_deep_bound (z := z) hadm hF hR₁pos hC₂pos hδpos (le_of_lt hδlt) ?_ ?_ ?_
      · intro Φ v z₀ R hR hΦ hinj hv hv1 hAbel
        exact (hEst Φ v z₀ R hR hΦ hinj hv hv1 hAbel).2
      · intro w hw
        refine hsub (ball_subset_Qreg_some_some ?_ hw)
        have hw' : ‖w - z‖ < 2 * δ := by
          rw [Metric.mem_ball, dist_eq_norm] at hw
          exact hw
        have : 4 * δ < 2 * (R₁ + δ) := by linarith
        linarith
      · intro w hw
        exact fun y hy => hsub (ball_subset_Qreg_some_some (deep_ball (R := R₁) (δ := δ) hz2 hw) hy)
    refine ⟨max BK (max (C₂ / R₁ + 1 / 31) ((C₂ / R₁ + 1 / 31) / δ)), ?_⟩
    intro z hz1 hz2
    by_cases hzK : z ∈ K
    · exact ⟨le_trans (hBK z hzK).1 (le_max_left _ _),
             le_trans (hBK z hzK).2 (le_max_left _ _)⟩
    · have hzK' : ¬ (x₀ - 3 / 4 ≤ z.re ∧ z.re ≤ x₀ + 3 ∧ |z.im| ≤ τ) := by
        intro h
        exact hzK (by rw [hKdef]; exact h)
      have him : τ < |z.im| := by
        by_contra hcon
        exact hzK' ⟨by linarith, by linarith, not_lt.mp hcon⟩
      have hTmin : T < min (vmLeft a z) (vmRight b z) := by
        by_contra hcon
        have himb := vm_im_bound (a := a) (b := b) (z := z) (T := T)
          (by linarith) (by linarith) (not_lt.mp hcon)
        rw [hτdef] at him
        linarith
      have hd := hdeep z hTmin
      exact ⟨le_trans (le_trans hd.1 (le_max_left _ _)) (le_max_right _ _),
             le_trans (le_trans hd.2 (le_max_right _ _)) (le_max_right _ _)⟩
  rcases b₁ with _ | a₀
  · rcases b₂ with _ | b₀
    · obtain ⟨B, hB⟩ := core ((x₀ - T - 10 : ℝ) : ℂ) ((x₀ + T + 10 : ℝ) : ℂ)
        (by simp; linarith [hTpos]) (by simp; linarith [hTpos])
        (by intro z hz; simp [MandelDim.Qreg])
      exact ⟨B, hB⟩
    · obtain ⟨B, hB⟩ := core ((x₀ - T - 10 : ℝ) : ℂ) b₀
        (by simp; linarith [hTpos]) (by simpa using h₂ b₀ (by simp))
        (by intro z hz; exact ⟨by intro c hc; simp at hc, hz.2⟩)
      exact ⟨B, hB⟩
  · rcases b₂ with _ | b₀
    · obtain ⟨B, hB⟩ := core a₀ ((x₀ + T + 10 : ℝ) : ℂ)
        (by simpa using h₁ a₀ (by simp)) (by simp; linarith [hTpos])
        (by intro z hz; exact ⟨hz.1, by intro c hc; simp at hc⟩)
      exact ⟨B, hB⟩
    · obtain ⟨B, hB⟩ := core a₀ b₀ (by simpa using h₁ a₀ (by simp)) (by simpa using h₂ b₀ (by simp))
        (by intro z hz; exact hz)
      exact ⟨B, hB⟩

end

end Work.FatouWindow

-- the target rests only on the permitted axioms
#print axioms Work.FatouWindow.fatouU_apriori_bound_wide
