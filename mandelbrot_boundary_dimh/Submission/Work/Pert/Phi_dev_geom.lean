import Mathlib
import Submission.Work.Pert.Setup
import Submission.Work.Pert.Basic

/-!
# `Work.Pert.Phi_dev_geom`

Geometry of the lower gate `Qm Ξ α = Qreg (some (Ξ - 1/α)) (some (-Ξ))`, used by the deviation
bound `Work.Pert.Phi_dev_le_on_gate`.

The gate is the complement of two closed 90° cones with apices `b₁ = Ξ - 1/α` and `b₂ = -Ξ`.  We
use the two "margin" functions

* `margB_g z = |z.im| - Ξ - z.re`,
* `margA_g z = z.re - Ξ + (1/α).re + |z.im + (1/α).im|`,

so that `Qm Ξ α = {z | 0 < margA_g z ∧ 0 < margB_g z}`, each is `2`-Lipschitz for the Euclidean norm,
and `ball z R ⊆ Qm Ξ α` as soon as `2 * R ≤ margA_g z` and `2 * R ≤ margB_g z`.
-/

namespace Work.Pert

open Complex Metric Set

noncomputable section

variable {Ξ : ℝ} {α : ℂ}

/-- Twice the distance from `z` to the cone of `Qm Ξ α` with apex `-Ξ`. -/
def margB_g (Ξ : ℝ) (z : ℂ) : ℝ := |z.im| - Ξ - z.re

/-- Twice the distance from `z` to the cone of `Qm Ξ α` with apex `Ξ - 1/α`. -/
def margA_g (Ξ : ℝ) (α : ℂ) (z : ℂ) : ℝ := z.re - Ξ + (1 / α).re + |z.im + (1 / α).im|

/-- Membership in the gate, in terms of the two margins. -/
theorem mem_Qm_iff_g (z : ℂ) : z ∈ Qm Ξ α ↔ 0 < margA_g Ξ α z ∧ 0 < margB_g Ξ z := by
  constructor
  · intro hz
    obtain ⟨h1, h2⟩ := hz
    have h1' := h1 ((Ξ : ℂ) - 1 / α) (by simp)
    have h2' := h2 (-(Ξ : ℂ)) (by simp)
    constructor
    · have e : (z - ((Ξ : ℂ) - 1 / α)).re = z.re - Ξ + (1 / α).re := by
        simp only [Complex.sub_re, Complex.ofReal_re]; ring
      have e' : (z - ((Ξ : ℂ) - 1 / α)).im = z.im + (1 / α).im := by
        simp only [Complex.sub_im, Complex.ofReal_im]; ring
      rw [margA_g, ← e, ← e']
      linarith
    · have e : (z - (-(Ξ : ℂ))).re = z.re + Ξ := by
        simp only [Complex.sub_re, Complex.neg_re, Complex.ofReal_re]; ring
      have e' : (z - (-(Ξ : ℂ))).im = z.im := by
        simp only [Complex.sub_im, Complex.neg_im, Complex.ofReal_im]; ring
      rw [margB_g]
      have h := h2'
      rw [e, e'] at h
      linarith
  · intro ⟨h1, h2⟩
    constructor
    · intro b hb
      simp only [Option.mem_some_iff] at hb
      subst hb
      have e : (z - ((Ξ : ℂ) - 1 / α)).re = z.re - Ξ + (1 / α).re := by
        simp only [Complex.sub_re, Complex.ofReal_re]; ring
      have e' : (z - ((Ξ : ℂ) - 1 / α)).im = z.im + (1 / α).im := by
        simp only [Complex.sub_im, Complex.ofReal_im]; ring
      rw [e, e']
      simp only [margA_g] at h1
      linarith
    · intro b hb
      simp only [Option.mem_some_iff] at hb
      subst hb
      have e : (z - (-(Ξ : ℂ))).re = z.re + Ξ := by
        simp only [Complex.sub_re, Complex.neg_re, Complex.ofReal_re]; ring
      have e' : (z - (-(Ξ : ℂ))).im = z.im := by
        simp only [Complex.sub_im, Complex.neg_im, Complex.ofReal_im]; ring
      rw [e, e']
      have h := h2
      simp only [margB_g] at h
      linarith

/-- On a vertical line at height `y ≥ 0`, `margB_g` is affine. -/
lemma margB_vert {Ξ x y : ℝ} (hy : 0 ≤ y) :
    margB_g Ξ ((x : ℂ) + (y : ℂ) * Complex.I) = y - Ξ - x := by
  rw [margB_g]
  have him : (((x : ℂ) + (y : ℂ) * Complex.I)).im = y := by simp
  have hre : (((x : ℂ) + (y : ℂ) * Complex.I)).re = x := by simp
  rw [him, hre, abs_of_nonneg hy]

/-- On a vertical line, `margA_g` is explicit. -/
lemma margA_vert {Ξ : ℝ} {α : ℂ} {x y : ℝ} :
    margA_g Ξ α ((x : ℂ) + (y : ℂ) * Complex.I)
      = x - Ξ + (1 / α).re + |y + (1 / α).im| := by
  rw [margA_g]
  have him : (((x : ℂ) + (y : ℂ) * Complex.I)).im = y := by simp
  have hre : (((x : ℂ) + (y : ℂ) * Complex.I)).re = x := by simp
  rw [him, hre]

/-- `margA_g Ξ α z - margA_g Ξ α w ≤ 2 * ‖w - z‖`. -/
lemma margA_sub_le (Ξ : ℝ) (α : ℂ) (w z : ℂ) :
    margA_g Ξ α z - margA_g Ξ α w ≤ 2 * ‖w - z‖ := by
  have hre : |w.re - z.re| ≤ ‖w - z‖ := by
    have h := Complex.abs_re_le_norm (w - z)
    simpa using h
  have hre2 : z.re - w.re ≤ ‖w - z‖ := by
    have h := (abs_le.mp hre).1
    linarith
  have hAim : |z.im + (1 / α).im| - |w.im + (1 / α).im| ≤ ‖w - z‖ := by
    have h := abs_abs_sub_abs_le_abs_sub (z.im + (1 / α).im) (w.im + (1 / α).im)
    have e : (z.im + (1 / α).im) - (w.im + (1 / α).im) = z.im - w.im := by ring
    rw [e] at h
    have h2 := (abs_le.mp h).2
    have h3 : |z.im - w.im| ≤ ‖w - z‖ := by
      have h4 : |z.im - w.im| = |(z - w).im| := by simp
      rw [h4]
      calc |(z - w).im| ≤ ‖z - w‖ := Complex.abs_im_le_norm _
        _ = ‖w - z‖ := norm_sub_rev z w
    linarith
  have e : margA_g Ξ α z - margA_g Ξ α w
      = (z.re - w.re) + (|z.im + (1 / α).im| - |w.im + (1 / α).im|) := by
    simp only [margA_g]; ring
  rw [e]; linarith

/-- `margB_g Ξ z - margB_g Ξ w ≤ 2 * ‖w - z‖`. -/
lemma margB_sub_le (Ξ : ℝ) (w z : ℂ) :
    margB_g Ξ z - margB_g Ξ w ≤ 2 * ‖w - z‖ := by
  have hre : |w.re - z.re| ≤ ‖w - z‖ := by
    have h := Complex.abs_re_le_norm (w - z)
    simpa using h
  have hre2 : w.re - z.re ≤ ‖w - z‖ := by
    have h := (abs_le.mp hre).2
    linarith
  have him : |z.im| - |w.im| ≤ ‖w - z‖ := by
    have h := abs_abs_sub_abs_le_abs_sub z.im w.im
    have h2 := (abs_le.mp h).2
    have h3 : |z.im - w.im| ≤ ‖w - z‖ := by
      have h4 : |z.im - w.im| = |(z - w).im| := by simp
      rw [h4]
      calc |(z - w).im| ≤ ‖z - w‖ := Complex.abs_im_le_norm _
        _ = ‖w - z‖ := norm_sub_rev z w
    linarith
  have e : margB_g Ξ z - margB_g Ξ w = (|z.im| - |w.im|) + (w.re - z.re) := by
    simp only [margB_g]; ring
  rw [e]; linarith

/-- **A ball inside the gate.**  If the two margins at `z` dominate `2 R`, then the open ball of
radius `R` around `z` lies in the gate. -/
lemma ball_subset_Qm_of_margin {Ξ R : ℝ} {α : ℂ} {z : ℂ}
    (hA : 2 * R ≤ margA_g Ξ α z) (hB : 2 * R ≤ margB_g Ξ z) :
    Metric.ball z R ⊆ Qm Ξ α := by
  intro w hw
  rw [mem_Qm_iff_g]
  rw [Metric.mem_ball, dist_eq_norm] at hw
  constructor
  · have h := margA_sub_le Ξ α w z
    linarith
  · have h := margB_sub_le Ξ w z
    linarith

/-- The points of the target region of `Work.Pert.Phi_dev_le_on_gate` lie in the gate. -/
lemma mem_Qm_of_target {Ξ : ℝ} {α : ℂ} {z : ℂ} (hΞ : 0 < Ξ)
    (hQAdm : MandelDim.QAdm (some ((Ξ : ℂ) - 1 / α)) (some (-(Ξ : ℂ))))
    (hre1 : -(Ξ + 1) ≤ z.re) (hre2 : z.re ≤ 2) (him : Ξ + 3 ≤ z.im) :
    z ∈ Qm Ξ α := by
  have hadm := hQAdm ((Ξ : ℂ) - 1 / α) (by simp) (-(Ξ : ℂ)) (by simp)
  have hadm' : 2 * Ξ + 4 < (1 / α).re := by
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.neg_re] at hadm
    linarith
  rw [mem_Qm_iff_g]
  constructor
  · rw [margA_g]
    have h3 : |z.im + (1 / α).im| ≥ 0 := abs_nonneg _
    linarith
  · rw [margB_g]
    have h1 : z.im ≤ |z.im| := le_abs_self z.im
    linarith

/-- The horizontal rectangle of the target region is compact. -/
lemma isCompact_targetBox (Ξ Y : ℝ) :
    IsCompact {z : ℂ | -(Ξ + 1) ≤ z.re ∧ z.re ≤ 2 ∧ Ξ + 3 ≤ z.im ∧ z.im ≤ Y} := by
  have hcl : IsClosed {z : ℂ | -(Ξ + 1) ≤ z.re ∧ z.re ≤ 2 ∧ Ξ + 3 ≤ z.im ∧ z.im ≤ Y} := by
    have h1 : IsClosed (Complex.re ⁻¹' (Set.Icc (-(Ξ + 1)) 2)) :=
      IsClosed.preimage continuous_re isClosed_Icc
    have h2 : IsClosed (Complex.im ⁻¹' (Set.Icc (Ξ + 3) Y)) :=
      IsClosed.preimage continuous_im isClosed_Icc
    have he : {z : ℂ | -(Ξ + 1) ≤ z.re ∧ z.re ≤ 2 ∧ Ξ + 3 ≤ z.im ∧ z.im ≤ Y}
        = Complex.re ⁻¹' (Set.Icc (-(Ξ + 1)) 2) ∩ Complex.im ⁻¹' (Set.Icc (Ξ + 3) Y) := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Icc, Set.mem_inter_iff]
      tauto
    rw [he]
    exact h1.inter h2
  have hbdd : {z : ℂ | -(Ξ + 1) ≤ z.re ∧ z.re ≤ 2 ∧ Ξ + 3 ≤ z.im ∧ z.im ≤ Y}
      ⊆ Metric.closedBall 0 (|Ξ + 1| + 2 + (|Ξ + 3| + |Y|) + 1) := by
    intro z hz
    obtain ⟨h1, h2, h3, h4⟩ := hz
    rw [Metric.mem_closedBall, dist_zero_right]
    have h7 : |z.re| ≤ |Ξ + 1| + 2 := by
      rw [abs_le]
      constructor
      · have h : (Ξ + 1) ≤ |Ξ + 1| := le_abs_self _
        linarith
      · have h : (0 : ℝ) ≤ |Ξ + 1| := abs_nonneg _
        linarith
    have h8 : |z.im| ≤ |Ξ + 3| + |Y| := by
      rw [abs_le]
      constructor
      · have h : (Ξ + 3) ≤ |Ξ + 3| := le_abs_self _
        have hY : (0 : ℝ) ≤ |Y| := abs_nonneg Y
        linarith
      · have h : Y ≤ |Y| := le_abs_self Y
        have h' : (0 : ℝ) ≤ |Ξ + 3| := abs_nonneg _
        linarith
    have h9 := Complex.norm_le_abs_re_add_abs_im z
    linarith
  exact (isCompact_closedBall (0 : ℂ) _).of_isClosed_subset hcl hbdd

/-- **Bound on the compact part.**  A holomorphic function on the gate is bounded on the compact
rectangle `{-(Ξ+1) ≤ re ≤ 2, Ξ+3 ≤ im ≤ Y}`. -/
theorem exists_bound_on_targetBox {Ξ : ℝ} {α : ℂ} {Φ : ℂ → ℂ} (hΞ : 0 < Ξ) (Y : ℝ)
    (hQAdm : MandelDim.QAdm (some ((Ξ : ℂ) - 1 / α)) (some (-(Ξ : ℂ))))
    (hΦ : DifferentiableOn ℂ Φ (Qm Ξ α)) :
    ∃ C : ℝ, ∀ z : ℂ, -(Ξ + 1) ≤ z.re → z.re ≤ 2 → Ξ + 3 ≤ z.im → z.im ≤ Y →
      ‖Φ z - z‖ ≤ C := by
  have hbox : {z : ℂ | -(Ξ + 1) ≤ z.re ∧ z.re ≤ 2 ∧ Ξ + 3 ≤ z.im ∧ z.im ≤ Y} ⊆ Qm Ξ α := by
    intro z hz
    exact mem_Qm_of_target hΞ hQAdm hz.1 hz.2.1 hz.2.2.1
  have hcont : ContinuousOn (fun z : ℂ => Φ z - z)
      {z : ℂ | -(Ξ + 1) ≤ z.re ∧ z.re ≤ 2 ∧ Ξ + 3 ≤ z.im ∧ z.im ≤ Y} :=
    (hΦ.continuousOn.mono hbox).sub continuousOn_id
  obtain ⟨C, hC⟩ := IsCompact.exists_bound_of_continuousOn (isCompact_targetBox Ξ Y) hcont
  exact ⟨C, fun z h1 h2 h3 h4 => hC z ⟨h1, h2, h3, h4⟩⟩

end

end Work.Pert
