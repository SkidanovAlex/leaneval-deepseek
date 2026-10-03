import Mathlib
import Submission.Work.Pert.pert2v2.gate_coord_end_asymptotic

namespace Work.Pert.pert2v2.EndWindowBounded

theorem end_asymptotic_bounded_window {Φ : ℂ → ℂ} {Q : Set ℂ} {c : ℂ} {B : ℝ} (hB : 0 ≤ B)
    (hEnd : ∀ x : ℝ, ∀ ε > 0, ∃ Y' : ℝ, ∀ z ∈ Q, Y' < Complex.im z →
      |Complex.re z - x| ≤ 2 → ‖Φ z - z - c‖ < ε) :
    ∀ ε > 0, ∃ Y' : ℝ, ∀ z ∈ Q, Y' < Complex.im z → |Complex.re z| ≤ B →
      ‖Φ z - z - c‖ < ε := by
  intro ε hε
  -- The bounded real window `[-B, B]` is covered by the (open) width-4 windows
  -- `Metric.ball x 2`; compactness yields a finite subcover.
  have hsub : Set.Icc (-B) B ⊆ ⋃ x : ℝ, Metric.ball x (2:ℝ) :=
    fun y _ => Set.mem_iUnion.mpr ⟨y, Metric.mem_ball_self (by norm_num)⟩
  obtain ⟨t, ht⟩ := isCompact_Icc.elim_finite_subcover (fun x : ℝ => Metric.ball x (2:ℝ))
      (fun x => Metric.isOpen_ball) hsub
  -- the finite subcover is non-empty because `0 ∈ [-B, B]` (as `B ≥ 0`)
  have htne : t.Nonempty := by
    have h0 : (0:ℝ) ∈ Set.Icc (-B) B := ⟨by linarith, hB⟩
    rcases Set.mem_iUnion.mp (ht h0) with ⟨x, hx⟩
    exact ⟨x, (Set.mem_iUnion.mp hx).1⟩
  -- the uniform threshold is the maximum of the finitely many window thresholds
  refine ⟨t.sup' htne (fun x => Classical.choose (hEnd x ε hε)), ?_⟩
  intro z hzQ hzim hzre
  have hzI : Complex.re z ∈ Set.Icc (-B) B := by
    have h := abs_le.mp hzre
    exact ⟨h.1, h.2⟩
  rcases Set.mem_iUnion.mp (ht hzI) with ⟨x, hx⟩
  rcases Set.mem_iUnion.mp hx with ⟨hxt, hxball⟩
  have hxd : |Complex.re z - x| ≤ 2 := by
    have h2 := Metric.mem_ball.mp hxball
    rw [Real.dist_eq] at h2
    linarith
  have hYle : Classical.choose (hEnd x ε hε) ≤
      t.sup' htne (fun x => Classical.choose (hEnd x ε hε)) :=
    Finset.le_sup' (fun x => Classical.choose (hEnd x ε hε)) hxt
  exact Classical.choose_spec (hEnd x ε hε) z hzQ (lt_of_le_of_lt hYle hzim) hxd

end Work.Pert.pert2v2.EndWindowBounded
