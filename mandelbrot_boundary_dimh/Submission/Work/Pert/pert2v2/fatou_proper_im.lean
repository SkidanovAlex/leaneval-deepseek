import Mathlib
import Submission.Work.Pert.RBlock3
import Submission.Work.Pert.Basic
import Submission.Work.Pert.Setup
import Submission.Work.Pert.Gates
import Submission.Work.Pert.Phi_dev_geom
import Submission.Work.Pert.pert2v2.steps
import Submission.Work.Pert.pert2v2.walk_right_deep
import Submission.Work.Pert.pert2v2.walk_left_deep

/-!
# PERT · `Work.Pert.pert2v2.fatou_proper_im`

**Properness of the Fatou coordinate at the lower end of the gate.**  For a Fatou coordinate `Φ`
of a near-translation `F` on the lower gate `Qm Ξ α = Qreg (some (Ξ - 1/α)) (some (-Ξ))` which is
asymptotic to a translation by `ρ` (`‖ρ - 1‖ ≤ 1/32`) at the lower end, the imaginary part of `Φ`
is bounded above on every half plane `{Im ≤ R}` of the gate:

`∀ R, ∃ N, ∀ ζ ∈ Qm Ξ α, ζ.im ≤ R → (Φ ζ).im ≤ N`.

## The structure of the proof

Write `Q = Qm Ξ α` and fix a "spine" `x₀` inside every slice.  Three regimes.

* **The strip** `{|Re z - x₀| ≤ 3, Im z < -Y₁}`: by `FatouEnds` (applied in the three half-width-2
  windows `x₀ - 1`, `x₀`, `x₀ + 1`, whose common additive constant is `c`) one has
  `Φ z = z/ρ + c + o(1)`, and `Im(z/ρ) → -∞` at the lower end since `ρ.re > 0`; this gives the
  bound `N₁` (`hstrip`).

* **Deep below** (`Im z < -Y₂`): the walk of `F` (backwards if `z` is to the right of the spine,
  forwards if it is to the left — `walk_right_deep` / `walk_left_deep`) moves `z` into the strip
  preserving `Im Φ`; hence `Im (Φ z) ≤ N₁`.

* **The remaining bounded height range**: at least one of the two margins
  `margA_g Ξ α z = z.re - Ξ + Re(1/α) + |z.im + Im(1/α)|`,
  `margB_g Ξ z = |z.im| - Ξ - z.re`
  is `≥ 2` (their sum exceeds `4`), so one step of `F` (forward with `fwdStep`, backward with
  `backStep_exists`) lands in the compact "roomy" set
  `{margA_g ≥ 1/2, margB_g ≥ 1/2, height bounded}`, where `Im Φ` is bounded
  (`exists_bound_roomy`); this gives `N₀`.
-/

namespace Work.Pert.pert2v2

open MandelDim Complex Metric Set

noncomputable section

variable {Ξ : ℝ} {α : ℂ}

/-! ## The compact "roomy" part of the gate -/

/-- **The roomy part of the gate at bounded heights is compact**, so `Im Φ` is bounded above
there. -/
theorem exists_bound_roomy {Φ : ℂ → ℂ}
    (hΦ : DifferentiableOn ℂ Φ (Work.Pert.Qm Ξ α)) (B R : ℝ) :
    ∃ N : ℝ, ∀ z ∈ Work.Pert.Qm Ξ α, 1 / 2 ≤ Work.Pert.margA_g Ξ α z →
      1 / 2 ≤ Work.Pert.margB_g Ξ z → B ≤ z.im → z.im ≤ R → (Φ z).im ≤ N := by
  classical
  set C : ℝ := |B| + |R| + |Ξ| + |(1 / α).re| + |(1 / α).im| + 2 with hC
  set K : Set ℂ := {z : ℂ | 1 / 2 ≤ Work.Pert.margA_g Ξ α z ∧ 1 / 2 ≤ Work.Pert.margB_g Ξ z ∧
    B ≤ z.im ∧ z.im ≤ R} with hK
  have hcl : IsClosed K := by
    have h1 : IsClosed {z : ℂ | 1 / 2 ≤ Work.Pert.margA_g Ξ α z} :=
      isClosed_le continuous_const continuous_margA_g
    have h2 : IsClosed {z : ℂ | 1 / 2 ≤ Work.Pert.margB_g Ξ z} :=
      isClosed_le continuous_const continuous_margB_g
    have h3 : IsClosed {z : ℂ | B ≤ z.im} := isClosed_le continuous_const continuous_im
    have h4 : IsClosed {z : ℂ | z.im ≤ R} := isClosed_le continuous_im continuous_const
    have he : K = {z : ℂ | 1 / 2 ≤ Work.Pert.margA_g Ξ α z}
        ∩ {z : ℂ | 1 / 2 ≤ Work.Pert.margB_g Ξ z}
        ∩ {z : ℂ | B ≤ z.im} ∩ {z : ℂ | z.im ≤ R} := by
      rw [hK]
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
      tauto
    rw [he]
    exact ((h1.inter h2).inter h3).inter h4
  have hCnn : 0 ≤ C := by rw [hC]; positivity
  have hCb : |B| ≤ C := by
    rw [hC]; linarith [abs_nonneg R, abs_nonneg Ξ, abs_nonneg ((1 / α).re), abs_nonneg ((1 / α).im)]
  have hCR : |R| ≤ C := by
    rw [hC]; linarith [abs_nonneg B, abs_nonneg Ξ, abs_nonneg ((1 / α).re), abs_nonneg ((1 / α).im)]
  have hCΞ : |Ξ| ≤ C := by
    rw [hC]; linarith [abs_nonneg B, abs_nonneg R, abs_nonneg ((1 / α).re), abs_nonneg ((1 / α).im)]
  have hCre : |(1 / α).re| ≤ C := by
    rw [hC]; linarith [abs_nonneg B, abs_nonneg R, abs_nonneg Ξ, abs_nonneg ((1 / α).im)]
  have hCim : |(1 / α).im| ≤ C := by
    rw [hC]; linarith [abs_nonneg B, abs_nonneg R, abs_nonneg Ξ, abs_nonneg ((1 / α).re)]
  have hbdd : K ⊆ Metric.closedBall 0 (16 * C) := by
    intro z hz
    obtain ⟨h1, h2, h3, h4⟩ := hz
    have h1' : 1 / 2 ≤ z.re - Ξ + (1 / α).re + |z.im + (1 / α).im| := by
      simpa only [Work.Pert.margA_g] using h1
    have h2' : 1 / 2 ≤ |z.im| - Ξ - z.re := by
      simpa only [Work.Pert.margB_g] using h2
    have hR : |z.im| ≤ |B| + |R| := by
      rw [abs_le]
      constructor <;> linarith [neg_abs_le B, le_abs_self R, abs_nonneg B, abs_nonneg R]
    have himC : |z.im| ≤ 6 * C := by linarith [hR, hCb, hCR, hCnn]
    have h5 : |z.im + (1 / α).im| ≤ |B| + |R| + |(1 / α).im| := by
      have h := abs_add_le z.im ((1 / α).im)
      linarith [h, hR, le_abs_self ((1 / α).im)]
    have h5C : |z.im + (1 / α).im| ≤ 6 * C := by linarith [h5, hCb, hCR, hCim, hCnn]
    have hzre_le : z.re ≤ 6 * C := by
      have h6 : z.re ≤ |z.im| - Ξ - 1 / 2 := by linarith
      have h7 : -Ξ ≤ |Ξ| := neg_le_abs Ξ
      linarith [h6, himC, hCΞ, hCnn]
    have hzre_ge : -(6 * C) ≤ z.re := by
      have h8 : Ξ - (1 / α).re - |z.im + (1 / α).im| + 1 / 2 ≤ z.re := by linarith
      have h9 : (1 / α).re ≤ C := le_trans (le_abs_self _) hCre
      have h10 : -Ξ ≤ C := le_trans (neg_le_abs Ξ) hCΞ
      linarith [h8, h5C, h9, h10, hCnn]
    have habs_re : |z.re| ≤ 6 * C := abs_le.mpr ⟨hzre_ge, hzre_le⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    have h11 : ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
    linarith [h11, habs_re, himC, hCnn]
  have hcomp : IsCompact K :=
    (isCompact_closedBall (0 : ℂ) _).of_isClosed_subset hcl hbdd
  have hsub : K ⊆ Work.Pert.Qm Ξ α := by
    intro z hz
    rw [Work.Pert.mem_Qm_iff_g]
    exact ⟨lt_of_lt_of_le (by norm_num) hz.1, lt_of_lt_of_le (by norm_num) hz.2.1⟩
  have hcont : ContinuousOn Φ K := hΦ.continuousOn.mono hsub
  obtain ⟨N, hN⟩ := hcomp.exists_bound_of_continuousOn hcont
  refine ⟨N, fun z hzQ h1 h2 h3 h4 => ?_⟩
  have hzK : z ∈ K := by
    rw [hK]
    exact ⟨h1, h2, h3, h4⟩
  exact le_trans (Complex.im_le_norm (Φ z)) (hN z hzK)

/-- The two margins of a point of the gate sum to more than `4`. -/
theorem marg_sum_gt_four
    (hQAdm : MandelDim.QAdm (some ((Ξ : ℂ) - 1 / α)) (some (-(Ξ : ℂ)))) (z : ℂ) :
    4 < Work.Pert.margA_g Ξ α z + Work.Pert.margB_g Ξ z := by
  have hadm := hQAdm ((Ξ : ℂ) - 1 / α) (by simp) (-(Ξ : ℂ)) (by simp)
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.neg_re] at hadm
  have h2 : |(1 / α).im| ≤ |z.im + (1 / α).im| + |z.im| := by
    have h3 := abs_sub (z.im + (1 / α).im) z.im
    have he : (z.im + (1 / α).im) - z.im = (1 / α).im := by ring
    rw [he] at h3
    linarith
  simp only [Work.Pert.margA_g, Work.Pert.margB_g]
  linarith [abs_nonneg ((1 / α).im)]

/-! ## The two one-step margin estimates -/

/-- Forward step of `F` shifts the margins quantitatively. -/
theorem marg_fwd {z w : ℂ} (h : ‖w - (z + 1)‖ ≤ 1 / 32) :
    Work.Pert.margA_g Ξ α z + (1 - 1 / 16) ≤ Work.Pert.margA_g Ξ α w ∧
      Work.Pert.margB_g Ξ z - (1 + 1 / 16) ≤ Work.Pert.margB_g Ξ w ∧
      |w.im - z.im| ≤ 1 / 32 := by
  have hε_im : |(w - (z + 1)).im| ≤ 1 / 32 := le_trans (Complex.abs_im_le_norm _) h
  have hε_re : |(w - (z + 1)).re| ≤ 1 / 32 := le_trans (Complex.abs_re_le_norm _) h
  have him : w.im = z.im + (w - (z + 1)).im := by simp
  have hre : w.re = z.re + 1 + (w - (z + 1)).re := by simp
  have h2 : |w.im - z.im| ≤ 1 / 32 := by
    have he : w.im - z.im = (w - (z + 1)).im := by rw [him]; ring
    rw [he]; exact hε_im
  refine ⟨?_, ?_, h2⟩
  · have h1 : |z.im + (1 / α).im| - 1 / 32 ≤ |w.im + (1 / α).im| := by
      have habs := abs_sub (w.im + (1 / α).im) (w.im - z.im)
      have heq : (w.im + (1 / α).im) - (w.im - z.im) = z.im + (1 / α).im := by ring
      rw [heq] at habs
      linarith
    simp only [Work.Pert.margA_g]
    linarith [neg_abs_le (w - (z + 1)).re]
  · have h1 : |z.im| - 1 / 32 ≤ |w.im| := by
      have habs := abs_sub w.im (w.im - z.im)
      have heq : w.im - (w.im - z.im) = z.im := by ring
      rw [heq] at habs
      linarith
    simp only [Work.Pert.margB_g]
    linarith [le_abs_self (w - (z + 1)).re]

/-- Backward step of `F` shifts the margins quantitatively. -/
theorem marg_bwd {z w : ℂ} (h : ‖w - (z - 1)‖ ≤ 1 / 32) :
    Work.Pert.margA_g Ξ α z - (1 + 1 / 16) ≤ Work.Pert.margA_g Ξ α w ∧
      Work.Pert.margB_g Ξ z + (1 - 1 / 16) ≤ Work.Pert.margB_g Ξ w ∧
      |w.im - z.im| ≤ 1 / 32 := by
  have hε_im : |(w - (z - 1)).im| ≤ 1 / 32 := le_trans (Complex.abs_im_le_norm _) h
  have hA := margA_g_sub_one (Ξ := Ξ) (α := α) z
  have hB := margB_g_sub_one (Ξ := Ξ) z
  have h1 : Work.Pert.margA_g Ξ α (z - 1) - 2 * ‖w - (z - 1)‖ ≤ Work.Pert.margA_g Ξ α w := by
    have hh := Work.Pert.margA_sub_le Ξ α w (z - 1)
    linarith
  have h2 : Work.Pert.margB_g Ξ (z - 1) - 2 * ‖w - (z - 1)‖ ≤ Work.Pert.margB_g Ξ w := by
    have hh := Work.Pert.margB_sub_le Ξ w (z - 1)
    linarith
  refine ⟨by linarith, by linarith, ?_⟩
  have he : w.im - z.im = (w - (z - 1)).im := by simp
  rw [he]; exact hε_im

/-! ## Height bookkeeping along the two long walks -/

/-- Reaching the strip by the rightwards walk: the reached point is below `-Y₁`. -/
theorem im_bound_walk_right {x₀ Y₁ Y₂ Kc : ℝ}
    (hKc : |Ξ| + |x₀| + 4 ≤ Kc) (hY₂ : 2 * (Y₁ + Kc + 1) ≤ Y₂) {ζ w : ℂ}
    (hdeep : ζ.im ≤ -Y₂) (hzre : ζ.re ≤ -ζ.im - Ξ)
    (hwim : w.im ≤ ζ.im + (ζ.re - x₀) / 2 + 1) : w.im < -Y₁ := by
  have h2 : (ζ.re - x₀) / 2 ≤ (-ζ.im - Ξ - x₀) / 2 := by linarith
  have h3 : ζ.im + (ζ.re - x₀) / 2 + 1 ≤ -Y₂ / 2 + (|Ξ| + |x₀|) / 2 + 1 := by
    have h4 : ζ.im / 2 ≤ -Y₂ / 2 := by linarith
    have h5 : -Ξ ≤ |Ξ| := neg_le_abs Ξ
    have h6 : -x₀ ≤ |x₀| := neg_le_abs x₀
    linarith
  have h7 : -Y₂ / 2 + (|Ξ| + |x₀|) / 2 + 1 ≤ -Y₂ / 2 + Kc := by
    have h8 : (0 : ℝ) ≤ |Ξ| := abs_nonneg Ξ
    have h9 : (0 : ℝ) ≤ |x₀| := abs_nonneg x₀
    linarith
  have h10 : -Y₂ / 2 + Kc ≤ -Y₁ - 1 := by linarith
  linarith [hwim, h3, h7, h10]

/-- Reaching the strip by the leftwards walk: the reached point is below `-Y₁`. -/
theorem im_bound_walk_left {x₀ Y₁ Y₂ Kc : ℝ}
    (hKc : |Ξ| + |x₀| + (1 / α).re + |(1 / α).im| + 4 ≤ Kc)
    (hY₂ : 2 * (Y₁ + Kc + 1) ≤ Y₂) (hY₂pos : 0 < Y₂) (hre : 0 ≤ (1 / α).re) {ζ w : ℂ}
    (hdeep : ζ.im ≤ -Y₂) (hzre : Ξ - (1 / α).re - |ζ.im + (1 / α).im| ≤ ζ.re)
    (hwim : w.im ≤ ζ.im + (x₀ - ζ.re) / 2 + 1) : w.im < -Y₁ := by
  have h1 : |ζ.im| = -ζ.im := abs_of_neg (by linarith)
  have h2 : Y₂ ≤ |ζ.im| := by rw [h1]; linarith
  have h3 : |ζ.im + (1 / α).im| ≤ |ζ.im| + |(1 / α).im| := abs_add_le _ _
  have h4 : x₀ ≤ |x₀| := le_abs_self x₀
  have h5 : -Ξ ≤ |Ξ| := neg_le_abs Ξ
  have h6 : -ζ.re ≤ -(Ξ - (1 / α).re) + |(1 / α).im| + |ζ.im| := by linarith [hzre, h3]
  have h7 : x₀ - ζ.re ≤ |x₀| + |Ξ| + (1 / α).re + |(1 / α).im| + |ζ.im| := by linarith
  have h8 : ζ.im ≤ -|ζ.im| := by linarith
  have h9 : ζ.im + (x₀ - ζ.re) / 2 + 1 ≤
      -Y₂ / 2 + (|x₀| + |Ξ| + (1 / α).re + |(1 / α).im|) / 2 + 1 := by
    linarith [h7, h8, h2]
  have h10 : -Y₂ / 2 + (|x₀| + |Ξ| + (1 / α).re + |(1 / α).im|) / 2 + 1 ≤ -Y₂ / 2 + Kc := by
    have h11 : (0 : ℝ) ≤ |x₀| := abs_nonneg x₀
    have h12 : (0 : ℝ) ≤ |Ξ| := abs_nonneg Ξ
    have h13 : (0 : ℝ) ≤ |(1 / α).im| := abs_nonneg _
    linarith
  have h14 : -Y₂ / 2 + Kc ≤ -Y₁ - 1 := by linarith
  linarith [hwim, h9, h10, h14]

/-! ## The main lemma -/

/-- **The main lemma**: `Im Φ` is bounded above on the gate below any height. -/
theorem fatou_proper_im {u : ℂ → ℂ} {σ α : ℂ} {Ξ : ℝ} {Φ : ℂ → ℂ}
    (hF : MandelDim.FatouStatement) (hΞ : 0 < Ξ)
    (hQAdm : MandelDim.QAdm (some ((Ξ : ℂ) - 1 / α)) (some (-(Ξ : ℂ))))
    (hNT : MandelDim.NearTranslationL1 (Work.Pert.liftF u σ α) (Work.Pert.Qm Ξ α))
    (hΦ : MandelDim.IsFatouCoordOn (Work.Pert.liftF u σ α) Φ (Work.Pert.Qm Ξ α))
    (hdecU : ∃ M κ Y : ℝ, 0 < M ∧ 0 < κ ∧ ∀ z ∈ Work.Pert.Qm Ξ α, Y < z.im →
      ‖Work.Pert.liftF u σ α z - (z + 1)‖ ≤ M * Real.exp (-(κ * z.im)))
    (hdecL : ∃ (ρ : ℂ) (M κ Y : ℝ), ‖ρ - 1‖ ≤ 1 / 32 ∧ 0 < M ∧ 0 < κ ∧
      ∀ z ∈ Work.Pert.Qm Ξ α, z.im < -Y →
        ‖Work.Pert.liftF u σ α z - (z + ρ)‖ ≤ M * Real.exp (κ * z.im)) :
    ∀ R : ℝ, ∃ N : ℝ, ∀ ζ ∈ Work.Pert.Qm Ξ α, ζ.im ≤ R → (Φ ζ).im ≤ N := by
  intro R
  obtain ⟨ρ, M, κ, Y, hρ, hM, hκ, hdec⟩ := hdecL
  have hNTon : MandelDim.NearTranslationOn (Work.Pert.liftF u σ α) (Work.Pert.Qm Ξ α) := hNT.1
  have hdiff : DifferentiableOn ℂ (Work.Pert.liftF u σ α) (Work.Pert.Qm Ξ α) := hNT.1.1
  have hNT' : ∀ w ∈ Work.Pert.Qm Ξ α,
      ‖Work.Pert.liftF u σ α w - (w + 1)‖ ≤ 1 / 32 ∧
        ‖deriv (Work.Pert.liftF u σ α) w - 1‖ ≤ 1 / 32 := hNT.1.2
  have hre_nonneg : (0 : ℝ) ≤ (1 / α).re := by
    have h2 := hQAdm ((Ξ : ℂ) - 1 / α) (by simp) (-(Ξ : ℂ)) (by simp)
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.neg_re] at h2
    linarith
  -- ## the lower-end asymptotics of `Φ` in the three windows around the spine
  obtain ⟨c, hc⟩ := (hF.2.2.2.2.2 (some ((Ξ : ℂ) - 1 / α)) (some (-(Ξ : ℂ)))
      (Work.Pert.liftF u σ α) Φ ρ M κ Y hQAdm hNTon hΦ hκ hρ).2 hdec
  set x₀ : ℝ := -((1 / α).re) / 2 with hx₀
  obtain ⟨Y₁c, hY₁c⟩ := hc x₀ 1 one_pos
  obtain ⟨Y₁m, hY₁m⟩ := hc (x₀ - 1) 1 one_pos
  obtain ⟨Y₁p, hY₁p⟩ := hc (x₀ + 1) 1 one_pos
  set Y₁ : ℝ := max (max Y₁c Y₁m) Y₁p with hY₁
  have hY₁c' : Y₁c ≤ Y₁ := le_trans (le_max_left _ _) (le_max_left _ _)
  have hY₁m' : Y₁m ≤ Y₁ := le_trans (le_max_right _ _) (le_max_left _ _)
  have hY₁p' : Y₁p ≤ Y₁ := le_max_right _ _
  set N₁ : ℝ := (ρ.re / Complex.normSq ρ) * (-Y₁) + |ρ.im / Complex.normSq ρ| * (|x₀| + 3)
    + c.im + 1 with hN₁
  have hρne : ρ ≠ 0 := by
    intro h0
    have h1 := hρ
    rw [h0] at h1
    norm_num at h1
  have hnsq : 0 < Complex.normSq ρ := Complex.normSq_pos.mpr hρne
  have hpre : 0 < ρ.re := by
    have h1 := (abs_le.mp (Complex.abs_re_le_norm (ρ - 1))).1
    have h2 : (ρ - 1).re = ρ.re - 1 := by simp
    rw [h2] at h1
    linarith
  -- ## the strip bound
  have hstrip : ∀ z ∈ Work.Pert.Qm Ξ α, z.im < -Y₁ → |z.re - x₀| ≤ 3 → (Φ z).im ≤ N₁ := by
    intro z hzQ hzY hzre
    have hzre' : |z.re| ≤ |x₀| + 3 := by
      have h := abs_add_le x₀ (z.re - x₀)
      have h4 : x₀ + (z.re - x₀) = z.re := by ring
      have h5 : |z.re - x₀| ≤ 3 := abs_le.mpr ⟨(abs_le.mp hzre).1, (abs_le.mp hzre).2⟩
      rw [h4] at h
      linarith
    have hsmall : ‖Φ z - z / ρ - c‖ < 1 := by
      by_cases h' : z.re ≤ x₀ - 1
      · refine hY₁m z hzQ (by linarith) ?_
        rw [abs_le]
        constructor <;> linarith [abs_le.mp hzre]
      · push_neg at h'
        by_cases h'' : z.re ≤ x₀ + 1
        · refine hY₁c z hzQ (by linarith) ?_
          rw [abs_le]
          constructor <;> linarith [abs_le.mp hzre]
        · push_neg at h''
          refine hY₁p z hzQ (by linarith) ?_
          rw [abs_le]
          constructor <;> linarith [abs_le.mp hzre]
    have h2 : (Φ z).im ≤ (z / ρ).im + c.im + 1 := by
      have him := Complex.abs_im_le_norm (Φ z - z / ρ - c)
      have h3 : (Φ z - z / ρ - c).im = (Φ z).im - (z / ρ).im - c.im := by simp
      rw [h3] at him
      rw [abs_le] at him
      linarith
    have h3 : (z / ρ).im ≤
        (ρ.re / Complex.normSq ρ) * (-Y₁) + |ρ.im / Complex.normSq ρ| * (|x₀| + 3) := by
      rw [Complex.div_im]
      have h4 : (ρ.re / Complex.normSq ρ) * z.im ≤ (ρ.re / Complex.normSq ρ) * (-Y₁) :=
        mul_le_mul_of_nonneg_left (le_of_lt hzY) (div_nonneg (le_of_lt hpre) (le_of_lt hnsq))
      have h6 : -((z.re * ρ.im) / Complex.normSq ρ) ≤ |ρ.im / Complex.normSq ρ| * (|x₀| + 3) := by
        have h7 : (z.re * ρ.im) / Complex.normSq ρ = (ρ.im / Complex.normSq ρ) * z.re := by ring
        rw [h7]
        calc -((ρ.im / Complex.normSq ρ) * z.re) ≤ |(ρ.im / Complex.normSq ρ) * z.re| :=
              neg_le_abs _
          _ = |ρ.im / Complex.normSq ρ| * |z.re| := abs_mul _ _
          _ ≤ |ρ.im / Complex.normSq ρ| * (|x₀| + 3) :=
              mul_le_mul_of_nonneg_left hzre' (abs_nonneg _)
      have h12 : (z.im * ρ.re) / Complex.normSq ρ = (ρ.re / Complex.normSq ρ) * z.im := by ring
      rw [h12]
      linarith [h4, h6]
    linarith
  -- ## the two long walks
  have hfwdStep : ∀ z ∈ Work.Pert.Qm Ξ α, 1 + 1 / 8 ≤ Work.Pert.margB_g Ξ z →
      Work.Pert.liftF u σ α z ∈ Work.Pert.Qm Ξ α ∧
        Φ (Work.Pert.liftF u σ α z) = Φ z + 1 := by
    intro z hz hroom
    exact fwdStep (Ξ := Ξ) (α := α) (F := Work.Pert.liftF u σ α) (Φ := Φ)
      (fun w hw => (hNT' w hw).1) hz hroom (fun w hwQ hFw => hΦ.2.2 w hwQ hFw)
  have hbwdStep : ∀ z ∈ Work.Pert.Qm Ξ α, 1 + 1 / 4 ≤ Work.Pert.margA_g Ξ α z →
      ∃ w : ℂ, ‖w - (z - 1)‖ ≤ 1 / 32 ∧ Work.Pert.liftF u σ α w = z ∧
        w ∈ Work.Pert.Qm Ξ α ∧ Φ w = Φ z - 1 := by
    intro z hz hroom
    exact backStep_exists (Ξ := Ξ) (α := α) (F := Work.Pert.liftF u σ α) (Φ := Φ)
      hdiff (fun w hw => hNT' w hw) hz hroom (fun w hwQ hFw => hΦ.2.2 w hwQ hFw)
  obtain ⟨Y₂r, hwalkR⟩ := walk_right_deep (Ξ := Ξ) (α := α) (F := Work.Pert.liftF u σ α)
    (Φ := Φ) (x₀ := x₀) hM hκ hρ hbwdStep hdec
  obtain ⟨Y₂l, hwalkL⟩ := walk_left_deep (Ξ := Ξ) (α := α) (F := Work.Pert.liftF u σ α)
    (Φ := Φ) (x₀ := x₀) hM hκ hρ hfwdStep hdec
  -- ## the deep threshold
  set Kc : ℝ := |Ξ| + |x₀| + (1 / α).re + |(1 / α).im| + 4 with hKc
  have hKc0 : 0 ≤ Kc := by
    rw [hKc]
    linarith [abs_nonneg Ξ, abs_nonneg x₀, abs_nonneg ((1 / α).im), hre_nonneg]
  have hKc' : |Ξ| + |x₀| + 4 ≤ Kc := by
    rw [hKc]
    linarith [hre_nonneg, abs_nonneg ((1 / α).im)]
  set Yt : ℝ := max (2 * (Y₁ + Kc + 1)) 1 with hYt
  set Y₂ : ℝ := max (max Y₂r Y₂l) (max Y₁ Yt) with hY₂
  have hY₂r : Y₂r ≤ Y₂ := le_trans (le_max_left _ _) (le_max_left _ _)
  have hY₂l : Y₂l ≤ Y₂ := le_trans (le_max_right _ _) (le_max_left _ _)
  have hY₂Y₁ : Y₁ ≤ Y₂ := le_trans (le_max_left _ _) (le_max_right _ _)
  have hY₂Yt : Yt ≤ Y₂ := le_trans (le_max_right _ _) (le_max_right _ _)
  have hYtK : 2 * (Y₁ + Kc + 1) ≤ Yt := le_max_left _ _
  have hY₂K : 2 * (Y₁ + Kc + 1) ≤ Y₂ := le_trans hYtK hY₂Yt
  have hYt1 : (1 : ℝ) ≤ Yt := le_max_right _ _
  have hY₂pos : (0 : ℝ) < Y₂ := lt_of_lt_of_le one_pos (le_trans hYt1 hY₂Yt)
  have hgateA : ∀ z ∈ Work.Pert.Qm Ξ α,
      z.re > Ξ - (1 / α).re - |z.im + (1 / α).im| ∧ z.re < |z.im| - Ξ := by
    intro z hz
    have h := (Work.Pert.mem_Qm_iff_g z).mp hz
    simp only [Work.Pert.margA_g, Work.Pert.margB_g] at h
    exact ⟨by linarith, by linarith⟩
  -- ## the middle bound
  obtain ⟨N₀, hN₀⟩ := exists_bound_roomy (Ξ := Ξ) (α := α) (Φ := Φ) hΦ.1 (-Y₂ - 1) (R + 1)
  refine ⟨max N₀ N₁, ?_⟩
  intro ζ hζ hζR
  by_cases hdeep : ζ.im ≤ -Y₂
  · -- ## deep below
    have hdeepR : ζ.im ≤ -Y₂r := le_trans hdeep (by linarith)
    have hdeepL : ζ.im ≤ -Y₂l := le_trans hdeep (by linarith)
    have hneg : ζ.im < 0 := by linarith
    have hzY : ζ.im < -Y₁ := by linarith
    by_cases hright : x₀ + 3 ≤ ζ.re
    · obtain ⟨k, w, hwQ, hΦw, hwre, hwim⟩ := hwalkR ζ hζ hdeepR hright
      have hzre : ζ.re ≤ -ζ.im - Ξ := by
        have htmp := (hgateA ζ hζ).2
        rw [abs_of_neg hneg] at htmp
        exact htmp.le
      have hwY : w.im < -Y₁ :=
        im_bound_walk_right (Ξ := Ξ) (x₀ := x₀) (Kc := Kc) hKc' hY₂K hdeep hzre hwim
      have hstripw := hstrip w hwQ hwY hwre
      have heq : (Φ w).im = (Φ ζ).im := by rw [hΦw]; simp
      rw [← heq]
      exact le_trans hstripw (le_max_right _ _)
    · by_cases hleft : ζ.re ≤ x₀ - 3
      · obtain ⟨k, w, hwQ, hΦw, hwre, hwim⟩ := hwalkL ζ hζ hdeepL hleft
        have hzre : Ξ - (1 / α).re - |ζ.im + (1 / α).im| ≤ ζ.re := (hgateA ζ hζ).1.le
        have hwY : w.im < -Y₁ :=
          im_bound_walk_left (Ξ := Ξ) (α := α) (x₀ := x₀) (Kc := Kc) (by rw [hKc]) hY₂K
            hY₂pos hre_nonneg hdeep hzre hwim
        have hstripw := hstrip w hwQ hwY hwre
        have heq : (Φ w).im = (Φ ζ).im := by rw [hΦw]; simp
        rw [← heq]
        exact le_trans hstripw (le_max_right _ _)
      · -- `ζ` itself already lies in the strip
        push_neg at hleft
        have hzre : |ζ.re - x₀| ≤ 3 := by
          rw [abs_le]
          constructor <;> linarith
        exact le_trans (hstrip ζ hζ hzY hzre) (le_max_right _ _)
  · -- ## bounded height
    push_neg at hdeep
    have hζmid : -Y₂ ≤ ζ.im := le_of_lt hdeep
    have hsum := marg_sum_gt_four (Ξ := Ξ) (α := α) hQAdm ζ
    by_cases hroom : 2 ≤ Work.Pert.margB_g Ξ ζ
    · -- forward step
      have hstep := fwdStep (Ξ := Ξ) (α := α) (F := Work.Pert.liftF u σ α) (Φ := Φ)
        (fun w hw => (hNT' w hw).1) hζ (by linarith) (fun w hwQ hFw => hΦ.2.2 w hwQ hFw)
      have hm := marg_fwd (Ξ := Ξ) (α := α) (z := ζ) (w := Work.Pert.liftF u σ α ζ)
        (hNT' ζ hζ).1
      have ha := (Work.Pert.mem_Qm_iff_g ζ).mp hζ
      have hA : 1 / 2 ≤ Work.Pert.margA_g Ξ α (Work.Pert.liftF u σ α ζ) := by
        linarith [hm.1, ha.1]
      have hB : 1 / 2 ≤ Work.Pert.margB_g Ξ (Work.Pert.liftF u σ α ζ) := by linarith [hm.2.1]
      have h1 : -Y₂ - 1 ≤ (Work.Pert.liftF u σ α ζ).im := by
        have h := (abs_le.mp hm.2.2).1
        linarith
      have h2 : (Work.Pert.liftF u σ α ζ).im ≤ R + 1 := by
        have h := (abs_le.mp hm.2.2).2
        linarith
      have hN := hN₀ _ hstep.1 hA hB h1 h2
      have heq : (Φ (Work.Pert.liftF u σ α ζ)).im = (Φ ζ).im := by rw [hstep.2]; simp
      rw [← heq]
      exact le_trans hN (le_max_left _ _)
    · -- backward step
      push_neg at hroom
      obtain ⟨w, hdist, hFw, hwQ, hΦw⟩ := backStep_exists (Ξ := Ξ) (α := α)
        (F := Work.Pert.liftF u σ α) (Φ := Φ) hdiff (fun w hw => hNT' w hw) hζ (by linarith)
        (fun w hwQ hFw => hΦ.2.2 w hwQ hFw)
      have hm := marg_bwd (Ξ := Ξ) (α := α) (z := ζ) (w := w) hdist
      have ha := (Work.Pert.mem_Qm_iff_g ζ).mp hζ
      have hB : 1 / 2 ≤ Work.Pert.margB_g Ξ w := by linarith [hm.2.1, ha.2]
      have hA : 1 / 2 ≤ Work.Pert.margA_g Ξ α w := by linarith [hm.1]
      have h1 : -Y₂ - 1 ≤ w.im := by
        have h := (abs_le.mp hm.2.2).1
        linarith
      have h2 : w.im ≤ R + 1 := by
        have h := (abs_le.mp hm.2.2).2
        linarith
      have hN := hN₀ w hwQ hA hB h1 h2
      have heq : (Φ w).im = (Φ ζ).im := by rw [hΦw]; simp
      rw [← heq]
      exact le_trans hN (le_max_left _ _)

end

end Work.Pert.pert2v2
