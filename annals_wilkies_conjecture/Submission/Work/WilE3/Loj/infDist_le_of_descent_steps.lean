import Mathlib

namespace Work.WilE3.Loj

set_option autoImplicit false
open Classical Metric

/-!
  ### Bounding `infDist` by a discrete descent

  We are given a nonnegative function `F`, a set `Z` containing the zeros of `F`, a point `x` with
  `F x / μ' ≤ ρ`, and a *descent step*: every `z` in the closed ball of radius `ρ` about `x` with
  `F z > 0` can be moved to `z + h • d` with `h ∈ (0, h₀]`, `‖d‖ ≤ 1`, `F (z + h • d) ≤ F z - h μ'`,
  and either `h = h₀` (a "full" step) or `F (z + h • d) = 0` (the descent hits a zero).

  Iterating the step produces a sequence `dseq`; the two facts that make it terminate are
  * every iterate stays inside `closedBall x ρ` (the total travelled distance is at most the total
    drop `F x / μ' ≤ ρ`), and
  * as long as no zero has been hit, every step is *full*, so `F` drops by `h₀ μ'` per step.

  Hence within `⌈F x / (h₀ μ')⌉` steps we reach a zero `z ∈ Z`, and the path from `x` to `z` has
  length at most the total drop `F x / μ'`.  This yields `infDist x Z ≤ F x / μ'`.
-/

variable {k : ℕ}

/-- The descent hypothesis of `infDist_le_of_descent_steps`, as a named predicate. -/
abbrev DescentHyp (F : (Fin k → ℝ) → ℝ) (x : Fin k → ℝ) (ρ h₀ μ' : ℝ) : Prop :=
  ∀ z ∈ Metric.closedBall x ρ, 0 < F z → ∃ h ∈ Set.Ioc 0 h₀, ∃ d : Fin k → ℝ, ‖d‖ ≤ 1 ∧
        F (z + h • d) ≤ F z - h * μ' ∧ (h = h₀ ∨ F (z + h • d) = 0)

variable {F : (Fin k → ℝ) → ℝ} {x : Fin k → ℝ} {ρ h₀ μ' : ℝ}

/-- The displacement `(h, d)` chosen at `z`: a genuine descent step when `z` lies in the closed ball
and `F z > 0`, and the trivial displacement `(0, 0)` otherwise. -/
noncomputable def stepDisp (hstep : DescentHyp F x ρ h₀ μ') (z : Fin k → ℝ) : ℝ × (Fin k → ℝ) :=
  if h : z ∈ Metric.closedBall x ρ ∧ 0 < F z then
    (Classical.choose (hstep z h.1 h.2),
     Classical.choose (Classical.choose_spec (hstep z h.1 h.2)).2)
  else (0, 0)

lemma stepDisp_pos (hstep : DescentHyp F x ρ h₀ μ') {z : Fin k → ℝ}
    (hz : z ∈ Metric.closedBall x ρ) (hzF : 0 < F z) :
    stepDisp hstep z =
      (Classical.choose (hstep z hz hzF),
       Classical.choose (Classical.choose_spec (hstep z hz hzF)).2) := by
  rw [stepDisp, dif_pos (show z ∈ Metric.closedBall x ρ ∧ 0 < F z from ⟨hz, hzF⟩)]

lemma stepDisp_neg (hstep : DescentHyp F x ρ h₀ μ') {z : Fin k → ℝ}
    (h : ¬ (z ∈ Metric.closedBall x ρ ∧ 0 < F z)) :
    stepDisp hstep z = (0, 0) := by
  rw [stepDisp, dif_neg h]

/-- The descent sequence starting at `x`, each step following `stepDisp`. -/
noncomputable def dseq (hstep : DescentHyp F x ρ h₀ μ') : ℕ → (Fin k → ℝ)
  | 0 => x
  | n + 1 => dseq hstep n +
      (stepDisp hstep (dseq hstep n)).1 • (stepDisp hstep (dseq hstep n)).2

/-- The defining properties of `stepDisp` at a point of the ball with `F z > 0`. -/
lemma stepDisp_spec (hstep : DescentHyp F x ρ h₀ μ') {z : Fin k → ℝ}
    (hz : z ∈ Metric.closedBall x ρ) (hzF : 0 < F z) :
    (stepDisp hstep z).1 ∈ Set.Ioc 0 h₀ ∧ ‖(stepDisp hstep z).2‖ ≤ 1 ∧
      F (z + (stepDisp hstep z).1 • (stepDisp hstep z).2) ≤ F z - (stepDisp hstep z).1 * μ' ∧
      ((stepDisp hstep z).1 = h₀ ∨ F (z + (stepDisp hstep z).1 • (stepDisp hstep z).2) = 0) := by
  rw [stepDisp_pos hstep hz hzF]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (Classical.choose_spec (hstep z hz hzF)).1
  · exact (Classical.choose_spec (Classical.choose_spec (hstep z hz hzF)).2).1
  · exact (Classical.choose_spec (Classical.choose_spec (hstep z hz hzF)).2).2.1
  · exact (Classical.choose_spec (Classical.choose_spec (hstep z hz hzF)).2).2.2

/-- One descent step preserves the invariant `‖z - x‖ ≤ (F x - F z) / μ'`: the step moves `z` by
`h ≤ h₀` in a direction of norm at most `1`, while the value of `F` drops by at least `h μ'`. -/
lemma dseq_succ_bound (hstep : DescentHyp F x ρ h₀ μ') (hμ' : 0 < μ')
    {z : Fin k → ℝ} (hz : z ∈ Metric.closedBall x ρ) (hzF : 0 < F z)
    (hzx : ‖z - x‖ ≤ (F x - F z) / μ') :
    ‖z + (stepDisp hstep z).1 • (stepDisp hstep z).2 - x‖ ≤
      (F x - F (z + (stepDisp hstep z).1 • (stepDisp hstep z).2)) / μ' := by
  obtain ⟨hmem, hnorm, hdrop, -⟩ := stepDisp_spec hstep hz hzF
  set z' := z + (stepDisp hstep z).1 • (stepDisp hstep z).2 with hz'_def
  have htri : ‖z' - x‖ ≤ ‖z - x‖ + ‖(stepDisp hstep z).1 • (stepDisp hstep z).2‖ := by
    rw [hz'_def]
    have heq : z + (stepDisp hstep z).1 • (stepDisp hstep z).2 - x
        = (z - x) + (stepDisp hstep z).1 • (stepDisp hstep z).2 := by abel
    rw [heq]; exact norm_add_le _ _
  have hsmul : ‖(stepDisp hstep z).1 • (stepDisp hstep z).2‖ ≤ (stepDisp hstep z).1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hmem.1]
    calc (stepDisp hstep z).1 * ‖(stepDisp hstep z).2‖
        ≤ (stepDisp hstep z).1 * 1 := mul_le_mul_of_nonneg_left hnorm (le_of_lt hmem.1)
      _ = (stepDisp hstep z).1 := mul_one _
  have hh : (stepDisp hstep z).1 ≤ (F z - F z') / μ' := by
    rw [le_div_iff₀ hμ', ← hz'_def] at *
    linarith [hdrop]
  have hmid : ‖z - x‖ + ‖(stepDisp hstep z).1 • (stepDisp hstep z).2‖ ≤
      (F x - F z) / μ' + (stepDisp hstep z).1 := add_le_add hzx hsmul
  have h1 : ‖z' - x‖ ≤ (F x - F z) / μ' + (F z - F z') / μ' := by
    linarith [htri, hmid, hh]
  have hfin : (F x - F z) / μ' + (F z - F z') / μ' = (F x - F z') / μ' := by
    rw [← add_div]; ring_nf
  rw [hfin] at h1
  exact h1

/-- **Distance invariant.** Every iterate of the descent sequence satisfies
`‖dseq n - x‖ ≤ (F x - F (dseq n)) / μ'`: the path length is bounded by the total drop of `F`. -/
lemma dseq_invA (hstep : DescentHyp F x ρ h₀ μ') (hμ' : 0 < μ') :
    ∀ n, ‖dseq hstep n - x‖ ≤ (F x - F (dseq hstep n)) / μ' := by
  intro n
  induction n with
  | zero => simp [dseq]
  | succ n ih =>
    by_cases h : dseq hstep n ∈ Metric.closedBall x ρ ∧ 0 < F (dseq hstep n)
    · rw [dseq]
      exact dseq_succ_bound hstep hμ' h.1 h.2 ih
    · rw [dseq, stepDisp_neg hstep h]
      simpa using ih

/-- **Drop invariant.** If `F` is positive on the first `n + 1` iterates, then all of those steps
are full and `F (dseq n) ≤ F x - n h₀ μ'`. -/
lemma dseq_invB (hstep : DescentHyp F x ρ h₀ μ') (hμ' : 0 < μ')
    (hFnn : ∀ z, 0 ≤ F z) (hρ : F x / μ' ≤ ρ) :
    ∀ n, (∀ i ≤ n, 0 < F (dseq hstep i)) → F (dseq hstep n) ≤ F x - (n : ℝ) * (h₀ * μ') := by
  intro n
  induction n with
  | zero => intro _; simp [dseq]
  | succ n ih =>
    intro hpos
    have ih' : F (dseq hstep n) ≤ F x - (n : ℝ) * (h₀ * μ') :=
      ih (fun i hi => hpos i (le_trans hi (Nat.le_succ n)))
    have hzF : 0 < F (dseq hstep n) := hpos n (Nat.le_succ n)
    have hball : dseq hstep n ∈ Metric.closedBall x ρ := by
      rw [Metric.mem_closedBall]
      have hA := dseq_invA hstep hμ' n
      have hle : ‖dseq hstep n - x‖ ≤ F x / μ' := by
        refine le_trans hA ?_
        rw [div_le_div_iff_of_pos_right hμ']
        linarith [hFnn (dseq hstep n)]
      calc dist (dseq hstep n) x = ‖dseq hstep n - x‖ := by rw [dist_eq_norm]
        _ ≤ F x / μ' := hle
        _ ≤ ρ := hρ
    obtain ⟨hmem, -, hdrop, hfull⟩ := stepDisp_spec hstep hball hzF
    have hseq : dseq hstep (n+1) = dseq hstep n +
        (stepDisp hstep (dseq hstep n)).1 • (stepDisp hstep (dseq hstep n)).2 := by rw [dseq]
    have hzF' : 0 < F (dseq hstep n +
        (stepDisp hstep (dseq hstep n)).1 • (stepDisp hstep (dseq hstep n)).2) := by
      rw [← hseq]; exact hpos (n+1) (le_refl _)
    have hh₀ : (stepDisp hstep (dseq hstep n)).1 = h₀ := by
      rcases hfull with h | h
      · exact h
      · exfalso; rw [h] at hzF'; exact lt_irrefl 0 hzF'
    have hcast : ((n+1 : ℕ) : ℝ) * (h₀ * μ') = (n : ℝ) * (h₀ * μ') + (h₀ * μ') := by
      push_cast; ring
    rw [dseq]
    rw [hh₀] at hdrop ⊢
    linarith [ih', hdrop, hcast]

theorem infDist_le_of_descent_steps {k : ℕ} {F : (Fin k → ℝ) → ℝ} {Z : Set (Fin k → ℝ)}
    {x : Fin k → ℝ} {ρ h₀ μ' : ℝ} (hμ' : 0 < μ') (hh₀ : 0 < h₀) (hρ : F x / μ' ≤ ρ)
    (hFnn : ∀ z, 0 ≤ F z) (hZ : ∀ z, F z = 0 → z ∈ Z)
    (hstep : ∀ z ∈ Metric.closedBall x ρ, 0 < F z → ∃ h ∈ Set.Ioc 0 h₀, ∃ d : Fin k → ℝ, ‖d‖ ≤ 1 ∧
        F (z + h • d) ≤ F z - h * μ' ∧ (h = h₀ ∨ F (z + h • d) = 0)) :
    Metric.infDist x Z ≤ F x / μ' := by
  have hstep' : DescentHyp F x ρ h₀ μ' := hstep
  have hpos : 0 < h₀ * μ' := mul_pos hh₀ hμ'
  obtain ⟨N, hN⟩ := exists_nat_gt (F x / (h₀ * μ'))
  have hN' : F x < (N : ℝ) * (h₀ * μ') := (div_lt_iff₀ hpos).mp hN
  have hex : ∃ n, n ≤ N ∧ F (dseq hstep' n) = 0 := by
    by_contra hc
    push Not at hc
    have hposall : ∀ i ≤ N, 0 < F (dseq hstep' i) := fun i hi =>
      lt_of_le_of_ne (hFnn _) (Ne.symm (hc i hi))
    have hb := dseq_invB hstep' hμ' hFnn hρ N hposall
    have : F (dseq hstep' N) < 0 := by linarith [hN']
    linarith [hFnn (dseq hstep' N)]
  obtain ⟨n, hnN, hFn⟩ := hex
  have hmemZ : dseq hstep' n ∈ Z := hZ _ hFn
  calc Metric.infDist x Z ≤ dist x (dseq hstep' n) := Metric.infDist_le_dist_of_mem hmemZ
    _ = ‖dseq hstep' n - x‖ := by rw [dist_eq_norm, norm_sub_rev]
    _ ≤ (F x - F (dseq hstep' n)) / μ' := dseq_invA hstep' hμ' n
    _ = F x / μ' := by rw [hFn, sub_zero]

end Work.WilE3.Loj
