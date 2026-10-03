import Mathlib
import Submission.Work.Motion.Basic
import Submission.Work.Motion.Coding

namespace Work.Motion

open Metric Set Filter
open MandelDim
open LeanEval.Dynamics.MandelbrotBoundary

/-- **Separation of the perturbed level-1 pieces.** There is a radius `ρ ≤ D.ρ` and a gap `g > 0`
such that for every `c ∈ ball c₀ ρ` the perturbed pieces `τc c i '' closedBall p (r/2)` of
distinct branches are at distance at least `g`. -/
theorem exists_sep {c₀ : ℂ} {N : ℕ} {τ : Fin N → ℂ → ℂ} {n : Fin N → ℕ} {p : ℂ} {r K : ℝ}
    (hN : 1 ≤ N) (hIFS : IsConformalIFS N τ p r K) (D : PertData c₀ N τ n p r K) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ D.ρ ∧ ∃ g : ℝ, 0 < g ∧ ∀ (i j : Fin N), i ≠ j →
      ∀ c ∈ ball c₀ ρ, ∀ x ∈ closedBall p (r / 2), ∀ y ∈ closedBall p (r / 2),
        g ≤ ‖D.τc c i x - D.τc c j y‖ := by
  classical
  obtain ⟨hr, hK, hdiff, hinj, hmaps, hdisj, hder⟩ := hIFS
  have hsub : closedBall p (r / 2) ⊆ ball p r := by
    intro z hz
    rw [mem_closedBall] at hz
    rw [mem_ball]
    linarith [hr]
  have hKne : (closedBall p (r / 2)).Nonempty :=
    ⟨p, mem_closedBall_self (by linarith : (0 : ℝ) ≤ r / 2)⟩
  -- Unperturbed separation of two distinct level-1 pieces.
  have hpair : ∀ i j : Fin N, i ≠ j →
      ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ closedBall p (r / 2), ∀ y ∈ closedBall p (r / 2),
        δ ≤ ‖τ i x - τ j y‖ := by
    intro i j hij
    have hi : ContinuousOn (fun q : ℂ × ℂ => τ i q.1)
        (closedBall p (r / 2) ×ˢ closedBall p (r / 2)) :=
      ((hdiff i).continuousOn.mono hsub).comp continuous_fst.continuousOn (fun q hq => hq.1)
    have hj : ContinuousOn (fun q : ℂ × ℂ => τ j q.2)
        (closedBall p (r / 2) ×ˢ closedBall p (r / 2)) :=
      ((hdiff j).continuousOn.mono hsub).comp continuous_snd.continuousOn (fun q hq => hq.2)
    have hcont : ContinuousOn (fun q : ℂ × ℂ => ‖τ i q.1 - τ j q.2‖)
        (closedBall p (r / 2) ×ˢ closedBall p (r / 2)) := (hi.sub hj).norm
    have hKc : IsCompact (closedBall p (r / 2) ×ˢ closedBall p (r / 2)) :=
      IsCompact.prod (isCompact_closedBall p (r / 2)) (isCompact_closedBall p (r / 2))
    obtain ⟨q, hq, hmin⟩ := hKc.exists_isMinOn (hKne.prod hKne) hcont
    refine ⟨‖τ i q.1 - τ j q.2‖, ?_, ?_⟩
    · rw [norm_pos_iff]
      intro heq
      have heq' : τ i q.1 = τ j q.2 := sub_eq_zero.mp heq
      have h1 : τ i q.1 ∈ τ i '' ball p r := ⟨q.1, hsub hq.1, rfl⟩
      have h2 : τ i q.1 ∈ τ j '' ball p r := ⟨q.2, hsub hq.2, heq'.symm⟩
      exact (Set.disjoint_left.mp (hdisj hij)) h1 h2
    · intro x hx y hy
      have := hmin (show (x, y) ∈ closedBall p (r / 2) ×ˢ closedBall p (r / 2) from ⟨hx, hy⟩)
      simpa using this
  -- Combine the finitely many pair bounds into one gap.
  let P : Finset (Fin N × Fin N) := Finset.univ.filter (fun q => q.1 ≠ q.2)
  have hPmem : ∀ i j : Fin N, i ≠ j → (i, j) ∈ P := by
    intro i j hij
    simp only [P, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hij
  have hchoice : ∀ q : Fin N × Fin N, q ∈ P →
      ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ closedBall p (r / 2), ∀ y ∈ closedBall p (r / 2),
        δ ≤ ‖τ q.1 x - τ q.2 y‖ := by
    intro q hq
    exact hpair q.1 q.2 (Finset.mem_filter.mp hq).2
  let δf : Fin N × Fin N → ℝ :=
    fun q => if hq : q ∈ P then Classical.choose (hchoice q hq) else 1
  have hδfpos : ∀ q ∈ P, 0 < δf q := by
    intro q hq
    simp only [δf, dite_eq_left hq]
    exact (Classical.choose_spec (hchoice q hq)).1
  have hδfbd : ∀ q ∈ P, ∀ x ∈ closedBall p (r / 2), ∀ y ∈ closedBall p (r / 2),
      δf q ≤ ‖τ q.1 x - τ q.2 y‖ := by
    intro q hq x hx y hy
    simp only [δf, dite_eq_left hq]
    exact (Classical.choose_spec (hchoice q hq)).2 x hx y hy
  let g : ℝ := if h : P.Nonempty then P.inf' h (fun q => δf q / 2) else 1
  have hgpos : 0 < g := by
    simp only [g]
    split
    · next h =>
      rw [Finset.lt_inf'_iff]
      intro q hq
      have := hδfpos q hq
      linarith
    · norm_num
  have hgbd : ∀ q ∈ P, g ≤ δf q / 2 := by
    intro q hq
    have hne : P.Nonempty := ⟨q, hq⟩
    simp only [g]
    rw [dite_eq_left hne]
    exact Finset.inf'_le (fun q => δf q / 2) hq
  have hden : (0 : ℝ) < 4 * (D.Lc + 1) := by linarith [D.hLc]
  refine ⟨min D.ρ (g / (4 * (D.Lc + 1))), ?_, min_le_left _ _, g, hgpos, ?_⟩
  · exact lt_min D.hρ (div_pos hgpos hden)
  · intro i j hij c hc x hx y hy
    have hqP : (i, j) ∈ P := hPmem i j hij
    have hbase : δf (i, j) ≤ ‖τ i x - τ j y‖ := hδfbd (i, j) hqP x hx y hy
    have h2g : 2 * g ≤ δf (i, j) := by have h := hgbd (i, j) hqP; linarith
    have hdist : 2 * g ≤ ‖τ i x - τ j y‖ := le_trans h2g hbase
    have hcD : c ∈ ball c₀ D.ρ := ball_subset_ball (min_le_left _ _) hc
    have hc0D : c₀ ∈ ball c₀ D.ρ := mem_ball_self D.hρ
    have hx1 : x ∈ ball p D.r₁ := PertData.closedBall_half_subset D hx
    have hy1 : y ∈ ball p D.r₁ := PertData.closedBall_half_subset D hy
    have hb1 : ‖D.τc c i x - τ i x‖ ≤ D.Lc * ‖c - c₀‖ := by
      have h := D.lips_c i x hx c hcD c₀ hc0D
      rwa [D.base i x hx1] at h
    have hb2 : ‖D.τc c j y - τ j y‖ ≤ D.Lc * ‖c - c₀‖ := by
      have h := D.lips_c j y hy c hcD c₀ hc0D
      rwa [D.base j y hy1] at h
    have hcl : ‖c - c₀‖ ≤ g / (4 * (D.Lc + 1)) := by
      have h1 : ‖c - c₀‖ < min D.ρ (g / (4 * (D.Lc + 1))) := by
        have hh := hc
        rw [mem_ball, dist_eq_norm] at hh
        exact hh
      exact le_trans h1.le (min_le_right _ _)
    have hLcg : D.Lc * ‖c - c₀‖ ≤ g / 4 := by
      have h1 : D.Lc * ‖c - c₀‖ ≤ D.Lc * (g / (4 * (D.Lc + 1))) :=
        mul_le_mul_of_nonneg_left hcl D.hLc
      have h2 : D.Lc * (g / (4 * (D.Lc + 1))) ≤ g / 4 := by
        rw [← mul_div_assoc, div_le_iff₀ hden]
        have : g / 4 * (4 * (D.Lc + 1)) = g * (D.Lc + 1) := by ring
        rw [this]
        nlinarith [hgpos]
      linarith
    have hb1' : ‖D.τc c i x - τ i x‖ ≤ g / 4 := le_trans hb1 hLcg
    have hb2' : ‖D.τc c j y - τ j y‖ ≤ g / 4 := le_trans hb2 hLcg
    have htri : ‖τ i x - τ j y‖ ≤ ‖D.τc c i x - D.τc c j y‖
        + ‖D.τc c i x - τ i x‖ + ‖D.τc c j y - τ j y‖ := by
      have heq : τ i x - τ j y
          = (D.τc c i x - D.τc c j y) - (D.τc c i x - τ i x)
              + (D.τc c j y - τ j y) := by ring
      calc ‖τ i x - τ j y‖
          = ‖(D.τc c i x - D.τc c j y) - (D.τc c i x - τ i x)
              + (D.τc c j y - τ j y)‖ := by rw [heq]
        _ ≤ ‖(D.τc c i x - D.τc c j y) - (D.τc c i x - τ i x)‖
              + ‖D.τc c j y - τ j y‖ := norm_add_le _ _
        _ ≤ (‖D.τc c i x - D.τc c j y‖ + ‖D.τc c i x - τ i x‖)
              + ‖D.τc c j y - τ j y‖ := by
            gcongr
            exact norm_sub_le _ _
        _ = ‖D.τc c i x - D.τc c j y‖ + ‖D.τc c i x - τ i x‖
              + ‖D.τc c j y - τ j y‖ := by ring
    linarith

end Work.Motion
