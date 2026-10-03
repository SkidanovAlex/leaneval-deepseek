import Mathlib
import Submission.Work.Repel.V10.chain_v9_src
import Submission.Work.Repel.V10.chain_v9_diff
import Submission.Work.Repel.V10.chain_v9_walk
import Submission.Work.Repel.V10.wOfCell_surj_SrcC
import Submission.Work.Repel.V10.SrcC_sub_Dflat
import Submission.Work.Repel.phi_close_to_p

/-!
# `Work.Repel.chain_v9_isl` : the islands of the §6 cells

For a cell `q = (j, k, n)` of the §6 count, the *island* is the set of points of the dynamical
plane whose level-0 Fatou coordinate lies in the source region `SrcC j k n` and whose target
`φ₀ (wOfCell q w)` lies in the concluding disc `ball p r`:

  `Giw j k n = SrcC j k n ∩ {w | φ₀ (wOfCell q w) ∈ ball p r}`   (in the Fatou plane),
  `Isl j k n = φ₀ '' Giw j k n`                                  (in the dynamical plane).

By `SrcC_uniform_iterate` a single iterate `f^[N]` of the cell realises the composite, so
`f^[N]` maps `Isl j k n` **onto** `ball p r` (`Isl_surj`, the `hsurj` field of
`Work.Repel.ReturnData`).

The remaining fields of `ReturnData` for the island are:

* `hΩhalf`: `Isl j k n ⊆ ball p (r / 2)` — `Work.Repel.Isl_sub_halfball`;
* `hΩsub`, `hdisj`, `hinj`: disjoint enclosing balls, each inside the image of the source region
  (on which `f^[N]` is a biholomorphism) — `Work.Repel.Isl_balls` and
  `Work.Repel.Isl_injOn_cell`;
* `hderiv`: the derivative bound `Work.Repel.Isl_deriv`.
-/

set_option linter.style.haveILetI false

namespace Work.Repel

open MandelDim Complex Set Metric Filter Topology

noncomputable section

namespace V10

variable (V : V10)

/-- The `w`-plane island of the cell: source points whose target lies in `ball p r`. -/
def Giw (j : ℕ) (k n : ℤ) : Set ℂ :=
  V.SrcC j k n ∩ {w : ℂ | V.P₀.φ (V.wOfCell (j, k, n) w) ∈ Metric.ball V.p V.r}

/-- The island of the cell in the dynamical plane. -/
def Isl (j : ℕ) (k n : ℤ) : Set ℂ := V.P₀.φ '' V.Giw j k n

/-- The source point of the cell whose target is the centre `p` of the concluding disc. -/
def hp (j : ℕ) (k n : ℤ) : ℂ :=
  Function.invFunOn (fun w : ℂ => V.P₀.φ (V.wOfCell (j, k, n) w)) (V.SrcC j k n) V.p

lemma Isl_sub_cell (j : ℕ) (k n : ℤ) : V.Isl j k n ⊆ V.P₀.φ '' V.SrcC j k n :=
  Set.image_mono Set.inter_subset_left

/-- `‖p‖ = 1.05/η`. -/
lemma norm_p : ‖V.p‖ = 1.05 / V.η := by
  have h105 : ‖(((105 : ℝ) / 100 : ℝ) : ℂ)‖ = 105 / 100 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by norm_num)]
  rw [V10.p, norm_div, norm_mul, Complex.norm_I, mul_one,
    show (1.05 : ℂ) = (((105 : ℝ) / 100 : ℝ) : ℂ) by norm_num, h105,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos V.hηpos]
  norm_num

/-- `ball p r` sits inside `ball 0 σ₀`. -/
lemma norm_p_add_r_le : ‖V.p‖ + V.r ≤ V.σ₀ := by
  rw [norm_p, V10.r]
  have hhalf : 1.5 / V.η ≤ 4 / V.η :=
    div_le_div_of_nonneg_right (by norm_num) V.hηpos.le
  have h4 : 1.05 / V.η + 9 / (20 * V.η) = 1.5 / V.η := by field_simp; ring
  linarith [V.hσ₀big, hhalf, h4]

lemma p_mem_ball_sigma : V.p ∈ Metric.ball 0 V.σ₀ := by
  rw [Metric.mem_ball, dist_zero_right]
  linarith [norm_p_add_r_le V, V.r_pos]

lemma Giw_nonempty {j : ℕ} (hj : 1 ≤ j) {k n : ℤ} (hSm : V.fib j k ⊆ V.Sm1) :
    (V.Giw j k n).Nonempty := by
  obtain ⟨w₁, hw₁, hw₁eq⟩ := V.hcov₀ (p_mem_ball_sigma V)
  have hw₁σ : V.P₀.φ w₁ ∈ Metric.ball 0 V.σ₀ := by
    rw [hw₁eq]; exact p_mem_ball_sigma V
  have hw₁' : w₁ ∈ V.wOfCell (j, k, n) '' V.SrcC j k n :=
    wOfCell_mem_image_of_phi_mem V hj hSm hw₁ hw₁σ
  obtain ⟨w, hw, hweq⟩ := hw₁'
  refine ⟨w, hw, ?_⟩
  change V.P₀.φ (V.wOfCell (j, k, n) w) ∈ Metric.ball V.p V.r
  rw [hweq, hw₁eq]
  exact Metric.mem_ball_self V.r_pos

/-- **The island is mapped onto the concluding disc by the cell iterate.** -/
theorem Isl_surj {j : ℕ} (hj : 1 ≤ j) {k n : ℤ} (hSm : V.fib j k ⊆ V.Sm1)
    {N : ℕ} (hN : ∀ w ∈ V.SrcC j k n, V.f ^[N] (V.P₀.φ w) = V.P₀.φ (V.wOfCell (j, k, n) w)) :
    Metric.ball V.p V.r ⊆ (V.f ^[N]) '' V.Isl j k n := by
  intro z hz
  rw [Metric.mem_ball, dist_eq_norm] at hz
  have hzd : ‖z - V.p‖ < V.r := by simpa [dist_eq_norm] using hz
  have hzσ : z ∈ Metric.ball 0 V.σ₀ := by
    rw [Metric.mem_ball, dist_zero_right]
    have h1 : ‖z‖ ≤ ‖z - V.p‖ + ‖V.p‖ :=
      calc ‖z‖ = ‖(z - V.p) + V.p‖ := by congr 1; ring
        _ ≤ ‖z - V.p‖ + ‖V.p‖ := norm_add_le _ _
    linarith [norm_p_add_r_le V, h1, hzd]
  obtain ⟨w₁, hw₁, hw₁eq⟩ := V.hcov₀ hzσ
  have hw₁σ : V.P₀.φ w₁ ∈ Metric.ball 0 V.σ₀ := by rw [hw₁eq]; exact hzσ
  have hw₁' : w₁ ∈ V.wOfCell (j, k, n) '' V.SrcC j k n :=
    wOfCell_mem_image_of_phi_mem V hj hSm hw₁ hw₁σ
  obtain ⟨w, hw, hweq⟩ := hw₁'
  refine ⟨V.P₀.φ w, ⟨w, ?_, rfl⟩, ?_⟩
  · refine ⟨hw, ?_⟩
    change V.P₀.φ (V.wOfCell (j, k, n) w) ∈ Metric.ball V.p V.r
    rw [hweq, hw₁eq]
    exact Metric.mem_ball.mpr (by rw [dist_eq_norm]; exact hzd)
  · rw [hN w hw, hweq, hw₁eq]

end V10

end

end Work.Repel
