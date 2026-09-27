import Mathlib
import Submission.Work.Drive.chartShiftHsurj

/-!
# `Work.Drive.threeBlock_dense_point`

**Three open sets, each dense at every point of a small ball, meet in that ball.**

The hypothesis `hdense` says that `A k` meets every neighbourhood of every `x` with `‖x‖ ≤ 1` and
`(blk k x) 0 ≥ 0` — a *half-space* condition on the `k`-th block, not a global one.  The point of
the statement is that a single ball `B` can be chosen on which **all three** conditions
`(blk k x) 0 > 0` (`k = 0, 1, 2`) hold simultaneously, and then the three density statements apply
at *every* point of `B`.

The construction: `vBlock ∈ ℝ¹²` is the vector whose `k`-th block is the constant-one vector of `ℝ⁴`
(so `(blk k vBlock) 0 = 1` for every `k`), `t > 0` is small enough that
`t * (‖vBlock‖ + 1) < min 1 ρ`, and `B = Metric.ball (t • vBlock) (t/2)`.  For `x ∈ B` and any `k`,

* `(blk k x) 0 = t + (blk k (x - t • vBlock)) 0 ≥ t - ‖x - t • vBlock‖ > t/2 > 0`
  (component bound `|w 0| ≤ ‖w‖`, `‖blk k w‖ ≤ ‖w‖`),
* `‖x‖ ≤ ‖t • vBlock‖ + ‖x - t • vBlock‖ < t * ‖vBlock‖ + t/2 < t * (‖vBlock‖ + 1) < min 1 ρ ≤ 1`.

So `A k` is dense at every point of `B` for every `k`, and the three-fold nesting argument
(`dense_at_of_three`: pick a point of `A 0`, then a point of `A 1` inside a ball around it that
stays in `A 0`, then a point of `A 2` inside a ball that stays in both) produces a point of
`A 0 ∩ A 1 ∩ A 2 ∩ B`, whose norm is `< min 1 ρ ≤ ρ`.

This is the last step of the parametric-Sard route of `CHART_SHIFT_HSURJ_STATUS.md`: with the three
block directions one independently recovers the three chains, and this lemma turns the
"dense near the origin" shape of the input into an honest point of the intersection.
-/

namespace Work.Drive

/-- The vector of `ℝ¹²` whose every block (`k = 0, 1, 2`) is the constant-one vector of `ℝ⁴`. -/
private def vBlock : EuclideanSpace ℝ (Fin 12) :=
  WithLp.toLp 2 (fun i : Fin 12 => if i.val % 4 = 0 then (1 : ℝ) else 0)

/-- The `0`-th coordinate of the `k`-th block of `vBlock` is `1`. -/
private lemma blk_vBlock_zero (k : Fin 3) : (blk k vBlock) 0 = 1 := by
  rw [blk_apply]
  show (if (blkIdx k 0).val % 4 = 0 then (1 : ℝ) else 0) = 1
  have h : (blkIdx k 0).val = 4 * k.val := rfl
  rw [h, Nat.mul_mod_right]
  norm_num

/-- **Positivity of the `k`-th block on the ball `ball (t • vBlock) (t/2)`** (`t > 0`). -/
private lemma blk_pos_of_mem_ball (k : Fin 3) {t : ℝ} (ht : 0 < t)
    (x : EuclideanSpace ℝ (Fin 12)) (hx : ‖x - t • vBlock‖ < t / 2) : 0 < (blk k x) 0 := by
  have hsplit : x = t • vBlock + (x - t • vBlock) := by abel
  have hdecomp : (blk k x) 0 = (blk k (t • vBlock)) 0 + (blk k (x - t • vBlock)) 0 := by
    conv_lhs => rw [hsplit]
    rw [map_add]; rfl
  have hk : (blk k (t • vBlock)) 0 = t := by
    rw [map_smul]
    simp [blk_vBlock_zero k]
  have hbound : -(t / 2) < (blk k (x - t • vBlock)) 0 := by
    have h1 : |(blk k (x - t • vBlock)) 0| ≤ ‖x - t • vBlock‖ := by
      have h2 := PiLp.norm_apply_le (blk k (x - t • vBlock)) 0
      calc |(blk k (x - t • vBlock)) 0| = ‖(blk k (x - t • vBlock)).ofLp 0‖ := by
            rw [Real.norm_eq_abs]
        _ ≤ ‖blk k (x - t • vBlock)‖ := h2
        _ ≤ ‖x - t • vBlock‖ := norm_blk_le k _
    have h3 := neg_abs_le ((blk k (x - t • vBlock)) 0)
    linarith
  rw [hdecomp, hk]
  linarith

/-- **Smallness of the norm on the ball `ball (t • vBlock) (t/2)`** (`t > 0`). -/
private lemma norm_lt_of_mem_ball {t : ℝ} (ht : 0 < t) (x : EuclideanSpace ℝ (Fin 12))
    (hx : ‖x - t • vBlock‖ < t / 2) : ‖x‖ < t * (‖vBlock‖ + 1) := by
  have hsum : ‖x‖ ≤ ‖t • vBlock‖ + ‖x - t • vBlock‖ := by
    have heq : t • vBlock + (x - t • vBlock) = x := by abel
    calc ‖x‖ = ‖t • vBlock + (x - t • vBlock)‖ := by rw [heq]
      _ ≤ ‖t • vBlock‖ + ‖x - t • vBlock‖ := norm_add_le _ _
  have hsm : ‖t • vBlock‖ = t * ‖vBlock‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
  rw [hsm] at hsum
  nlinarith [norm_nonneg vBlock]

/-- **Three dense-in-`B` open sets meet in `B`.**  The finite nesting argument: a point of `A 0` in
`B`, then a point of `A 1` in a ball around it that stays inside `A 0 ∩ B`, then a point of `A 2` in
a ball around *that* which stays inside `A 1 ∩ A 0 ∩ B`. -/
private lemma dense_at_of_three
    (A : Fin 3 → Set (EuclideanSpace ℝ (Fin 12)))
    {B : Set (EuclideanSpace ℝ (Fin 12))} (hB : IsOpen B) (hBne : B.Nonempty)
    (hopen : ∀ k : Fin 3, IsOpen (A k))
    (h : ∀ x ∈ B, ∀ k : Fin 3, ∀ δ : ℝ, 0 < δ → ∃ y, y ∈ A k ∧ ‖y - x‖ < δ) :
    ∃ s ∈ B, ∀ k : Fin 3, s ∈ A k := by
  obtain ⟨x, hx⟩ := hBne
  obtain ⟨ε, hε, hεB⟩ := Metric.isOpen_iff.mp hB x hx
  obtain ⟨y0, hy0A, hy0d⟩ := h x hx 0 ε hε
  have hy0B : y0 ∈ B := hεB (by rw [Metric.mem_ball, dist_eq_norm]; exact hy0d)
  obtain ⟨ε0, hε0, hε0sub⟩ := Metric.isOpen_iff.mp ((hopen 0).inter Metric.isOpen_ball) y0
    ⟨hy0A, by rw [Metric.mem_ball, dist_eq_norm]; exact hy0d⟩
  obtain ⟨y1, hy1A, hy1d⟩ := h y0 hy0B 1 ε0 hε0
  have hy1mem : y1 ∈ A 0 ∩ Metric.ball x ε :=
    hε0sub (by rw [Metric.mem_ball, dist_eq_norm]; exact hy1d)
  have hy1B : y1 ∈ B := hεB hy1mem.2
  obtain ⟨ε1, hε1, hε1sub⟩ := Metric.isOpen_iff.mp ((hopen 1).inter Metric.isOpen_ball) y1
    ⟨hy1A, by rw [Metric.mem_ball, dist_eq_norm]; exact hy1d⟩
  obtain ⟨y2, hy2A, hy2d⟩ := h y1 hy1B 2 ε1 hε1
  have hy2mem : y2 ∈ A 1 ∩ Metric.ball y0 ε0 :=
    hε1sub (by rw [Metric.mem_ball, dist_eq_norm]; exact hy2d)
  have hy2A0 : y2 ∈ A 0 := (hε0sub hy2mem.2).1
  have hy2B : y2 ∈ B := hεB (hε0sub hy2mem.2).2
  refine ⟨y2, hy2B, fun k => ?_⟩
  have hk : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases hk with h | h | h
  · rw [h]; exact hy2A0
  · rw [h]; exact hy2mem.1
  · rw [h]; exact hy2A

theorem threeBlock_dense_point
    (A : Fin 3 → Set (EuclideanSpace ℝ (Fin 12)))
    (hopen : ∀ k : Fin 3, IsOpen (A k))
    (hdense : ∀ (k : Fin 3) (x : EuclideanSpace ℝ (Fin 12)), ‖x‖ ≤ 1 → 0 ≤ (Work.Drive.blk k x) 0 →
      ∀ δ : ℝ, 0 < δ → ∃ y, y ∈ A k ∧ ‖y - x‖ < δ)
    (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ s : EuclideanSpace ℝ (Fin 12), ‖s‖ < ρ ∧ ∀ k : Fin 3, s ∈ A k := by
  obtain ⟨t, htpos, ht⟩ : ∃ t : ℝ, 0 < t ∧ t * (‖vBlock‖ + 1) < min 1 ρ := by
    refine ⟨min 1 ρ / (2 * (‖vBlock‖ + 1)), ?_, ?_⟩
    · have : (0 : ℝ) < min 1 ρ := lt_min one_pos hρ
      positivity
    · have hmul : min 1 ρ / (2 * (‖vBlock‖ + 1)) * (‖vBlock‖ + 1) = min 1 ρ / 2 := by
        field_simp
      rw [hmul]
      have : (0 : ℝ) < min 1 ρ := lt_min one_pos hρ
      linarith
  have hr : 0 < t / 2 := by linarith
  have hball : ∀ x ∈ Metric.ball (t • vBlock) (t / 2), ‖x‖ < min 1 ρ := by
    intro x hx
    rw [Metric.mem_ball, dist_eq_norm] at hx
    have h1 := norm_lt_of_mem_ball htpos x hx
    linarith
  have hdens : ∀ x ∈ Metric.ball (t • vBlock) (t / 2), ∀ k : Fin 3, ∀ δ : ℝ, 0 < δ →
      ∃ y, y ∈ A k ∧ ‖y - x‖ < δ := by
    intro x hx k δ hδ
    have hxd : ‖x - t • vBlock‖ < t / 2 := by
      rw [Metric.mem_ball, dist_eq_norm] at hx
      exact hx
    refine hdense k x ?_ ?_ δ hδ
    · exact le_of_lt (lt_of_lt_of_le (hball x hx) (min_le_left 1 ρ))
    · exact le_of_lt (blk_pos_of_mem_ball k htpos x hxd)
  obtain ⟨s, hsB, hsA⟩ := dense_at_of_three A Metric.isOpen_ball
    ⟨t • vBlock, by rw [Metric.mem_ball, dist_self]; exact hr⟩ hopen hdens
  exact ⟨s, lt_of_lt_of_le (hball s hsB) (min_le_right 1 ρ), hsA⟩

end Work.Drive
