import Mathlib
import Submission.Work.Pert.V5.Basics
import Submission.Work.Pert.gate_walk_legal

namespace Work.Pert.V5

open Set Metric Filter
open scoped _root_.Topology

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

noncomputable section

/-!
# `Work.Pert.V5.walk_data`

Data collected along a legal walk of the near-translation `F = liftF u σ α` inside the lower gate
`Qm Ξ α`, of the length `m` prescribed by the room hypothesis `(17/16) m + 1 ≤ mgB w`.

Everything is a consequence of the single pointwise estimate `‖F z - (z + 1)‖ ≤ 1/32` on the gate:

* the walk stays in the gate (`Work.Pert.gate_walk_legal`);
* `F^[j] w - (w + j)` telescopes into `j` error terms, hence
  `‖F^[m] w - (w + m)‖ ≤ m/32`, giving the real/imaginary drifts and the deviation estimate once the
  Fatou coordinate is iterated;
* the two gate marginals move by at least `+30/32` resp. `-17/16` per step.
-/

/-- One step of a near-translation increases the `b₁`-marginal `mgA` by at least `30/32`. -/
private lemma mgA_step {Ξ : ℝ} {α : ℂ} {F : ℂ → ℂ} {z : ℂ}
    (h : ‖F z - (z + 1)‖ ≤ (1 / 32 : ℝ)) :
    mgA Ξ α z + 30 / 32 ≤ mgA Ξ α (F z) := by
  have hε : ‖F z - z - 1‖ ≤ (1 / 32 : ℝ) := by
    rwa [show F z - z - 1 = F z - (z + 1) by ring]
  set ε : ℂ := F z - z - 1 with hεdef
  have hre : (F z).re = z.re + 1 + ε.re := by
    rw [hεdef]; simp only [Complex.sub_re, Complex.add_re, Complex.one_re]; ring
  have him : (F z).im = z.im + ε.im := by
    rw [hεdef]; simp only [Complex.sub_im, Complex.add_im, Complex.one_im]; ring
  have h1 : -‖ε‖ ≤ ε.re := (abs_le.mp (Complex.abs_re_le_norm ε)).1
  have h2 : |z.im + (1 / α).im| - ‖ε‖ ≤ |z.im + ε.im + (1 / α).im| := by
    have h3 : |ε.im| ≤ ‖ε‖ := Complex.abs_im_le_norm ε
    have h4 := abs_sub_abs_le_abs_sub (z.im + (1 / α).im) (-ε.im)
    rw [abs_neg] at h4
    have h5 : (z.im + (1 / α).im) - -ε.im = z.im + ε.im + (1 / α).im := by ring
    rw [h5] at h4
    linarith
  simp only [mgA]
  rw [hre, him]
  linarith

/-- One step of a near-translation decreases the `b₂`-marginal `mgB` by at most `17/16`. -/
private lemma mgB_step {Ξ : ℝ} {F : ℂ → ℂ} {z : ℂ}
    (h : ‖F z - (z + 1)‖ ≤ (1 / 32 : ℝ)) :
    mgB Ξ z - 17 / 16 ≤ mgB Ξ (F z) := by
  set ε : ℂ := F z - z - 1 with hεdef
  have hε : ‖ε‖ ≤ (1 / 32 : ℝ) := by
    rw [hεdef]; rwa [show F z - (z + 1) = F z - z - 1 by ring] at h
  have hre : (F z).re = z.re + 1 + ε.re := by
    rw [hεdef]; simp only [Complex.sub_re, Complex.add_re, Complex.one_re]; ring
  have him : (F z).im = z.im + ε.im := by
    rw [hεdef]; simp only [Complex.sub_im, Complex.add_im, Complex.one_im]; ring
  have h1 : ε.re ≤ ‖ε‖ := (abs_le.mp (Complex.abs_re_le_norm ε)).2
  have h2 : |z.im| - ‖ε‖ ≤ |z.im + ε.im| := by
    have h3 : |ε.im| ≤ ‖ε‖ := Complex.abs_im_le_norm ε
    have h4 := abs_sub_abs_le_abs_sub z.im (-ε.im)
    rw [abs_neg] at h4
    have h5 : z.im - -ε.im = z.im + ε.im := by ring
    rw [h5] at h4
    linarith
  simp only [mgB]
  rw [hre, him]
  linarith

/-- **Telescoped drift.**  If the walk `z, F z, … , F^[m] z` stays in `Q`, then
`‖F^[m] z - (z + m)‖ ≤ m / 32`. -/
private lemma iterate_norm_le {F : ℂ → ℂ} {Q : Set ℂ} {z : ℂ} {m : ℕ}
    (hwalk : ∀ j ≤ m, F^[j] z ∈ Q)
    (hstep : ∀ u ∈ Q, ‖F u - (u + 1)‖ ≤ (1 / 32 : ℝ)) :
    ‖F^[m] z - (z + (m : ℂ))‖ ≤ (m : ℝ) / 32 := by
  induction m with
  | zero => simp
  | succ k ih =>
    have hwalk' : ∀ j ≤ k, F^[j] z ∈ Q := fun j hj => hwalk j (by omega)
    have hk : F^[k] z ∈ Q := hwalk k (by omega)
    have hsplit : F^[k+1] z - (z + ((k + 1 : ℕ) : ℂ))
        = (F (F^[k] z) - (F^[k] z + 1)) + (F^[k] z - (z + (k : ℂ))) := by
      rw [Function.iterate_succ_apply']; push_cast; ring
    rw [hsplit]
    calc ‖(F (F^[k] z) - (F^[k] z + 1)) + (F^[k] z - (z + (k : ℂ)))‖
        ≤ ‖F (F^[k] z) - (F^[k] z + 1)‖ + ‖F^[k] z - (z + (k : ℂ))‖ := norm_add_le _ _
      _ ≤ 1 / 32 + (k : ℝ) / 32 := add_le_add (hstep _ hk) (ih hwalk')
      _ = ((k + 1 : ℕ) : ℝ) / 32 := by push_cast; ring

/-- Real-part drift along the walk. -/
private lemma iterate_re_le {F : ℂ → ℂ} {Q : Set ℂ} {z : ℂ} {m : ℕ}
    (hwalk : ∀ j ≤ m, F^[j] z ∈ Q)
    (hstep : ∀ u ∈ Q, ‖F u - (u + 1)‖ ≤ (1 / 32 : ℝ)) :
    |(F^[m] z).re - (z.re + (m : ℝ))| ≤ (m : ℝ) / 32 := by
  have h := Complex.abs_re_le_norm (F^[m] z - (z + (m : ℂ)))
  have h2 : (F^[m] z - (z + (m : ℂ))).re = (F^[m] z).re - (z.re + (m : ℝ)) := by
    simp [Complex.sub_re, Complex.add_re, Complex.ofReal_re]
  rw [h2] at h
  exact le_trans h (iterate_norm_le hwalk hstep)

/-- Imaginary-part drift along the walk. -/
private lemma iterate_im_le {F : ℂ → ℂ} {Q : Set ℂ} {z : ℂ} {m : ℕ}
    (hwalk : ∀ j ≤ m, F^[j] z ∈ Q)
    (hstep : ∀ u ∈ Q, ‖F u - (u + 1)‖ ≤ (1 / 32 : ℝ)) :
    |(F^[m] z).im - z.im| ≤ (m : ℝ) / 32 := by
  have h := Complex.abs_im_le_norm (F^[m] z - (z + (m : ℂ)))
  have h2 : (F^[m] z - (z + (m : ℂ))).im = (F^[m] z).im - z.im := by
    simp [Complex.sub_im, Complex.add_im, Complex.ofReal_im]
  rw [h2] at h
  exact le_trans h (iterate_norm_le hwalk hstep)

/-- **The Fatou coordinate is additive along the walk**: `Φ (F^[m] z) = Φ z + m`. -/
private lemma coord_iterate {F Φ : ℂ → ℂ} {Q : Set ℂ} {z : ℂ} {m : ℕ}
    (hΦ : MandelDim.IsFatouCoordOn F Φ Q)
    (hwalk : ∀ j ≤ m, F^[j] z ∈ Q) :
    Φ (F^[m] z) = Φ z + (m : ℂ) := by
  induction m with
  | zero => simp
  | succ k ih =>
    have hwalk' : ∀ j ≤ k, F^[j] z ∈ Q := fun j hj => hwalk j (by omega)
    have hk : F^[k] z ∈ Q := hwalk k (by omega)
    have hk1 : F (F^[k] z) ∈ Q := by
      have he : F^[k+1] z = F (F^[k] z) := Function.iterate_succ_apply' F k z
      rw [← he]; exact hwalk (k + 1) (by omega)
    rw [Function.iterate_succ_apply', hΦ.2.2 _ hk hk1, ih hwalk']
    push_cast; ring

/-- `mgA` grows by at least `30/32` per step of the walk. -/
private lemma iterate_mgA {Ξ : ℝ} {α : ℂ} {F : ℂ → ℂ} {Q : Set ℂ} {z : ℂ} {m : ℕ}
    (hwalk : ∀ j ≤ m, F^[j] z ∈ Q)
    (hstep : ∀ u ∈ Q, ‖F u - (u + 1)‖ ≤ (1 / 32 : ℝ)) :
    mgA Ξ α z + (30 / 32 : ℝ) * (m : ℝ) ≤ mgA Ξ α (F^[m] z) := by
  induction m with
  | zero => simp
  | succ k ih =>
    have hwalk' : ∀ j ≤ k, F^[j] z ∈ Q := fun j hj => hwalk j (by omega)
    have hk : F^[k] z ∈ Q := hwalk k (by omega)
    have h1 := ih hwalk'
    have h2 := mgA_step (Ξ := Ξ) (α := α) (F := F) (z := F^[k] z) (hstep _ hk)
    rw [Function.iterate_succ_apply']
    push_cast
    linarith

/-- `mgB` decreases by at most `17/16` per step of the walk. -/
private lemma iterate_mgB {Ξ : ℝ} {F : ℂ → ℂ} {Q : Set ℂ} {z : ℂ} {m : ℕ}
    (hwalk : ∀ j ≤ m, F^[j] z ∈ Q)
    (hstep : ∀ u ∈ Q, ‖F u - (u + 1)‖ ≤ (1 / 32 : ℝ)) :
    mgB Ξ z ≤ mgB Ξ (F^[m] z) + (17 / 16 : ℝ) * (m : ℝ) := by
  induction m with
  | zero => simp
  | succ k ih =>
    have hwalk' : ∀ j ≤ k, F^[j] z ∈ Q := fun j hj => hwalk j (by omega)
    have hk : F^[k] z ∈ Q := hwalk k (by omega)
    have h1 := ih hwalk'
    have h2 := mgB_step (Ξ := Ξ) (F := F) (z := F^[k] z) (hstep _ hk)
    rw [Function.iterate_succ_apply']
    push_cast
    linarith

theorem walk_data {Ξ rr M : ℝ} {α σ : ℂ} {u Φm : ℂ → ℂ} {w : ℂ} {m : ℕ}
    (hΞ : 0 < Ξ) (hrr : 0 < rr) (hM : 2 ^ 10 ≤ M)
    (hInF1 : MandelDim.InF1 α) (hα : ‖α‖ ≤ 1 / (32 * (M + 2 + Ξ)))
    (hQAdm : MandelDim.QAdm (some ((Ξ : ℂ) - 1 / α)) (some (-(Ξ : ℂ))))
    (hNT : MandelDim.NearTranslationL1 (Work.Pert.liftF u σ α) (Work.Pert.Qm Ξ α))
    (hΦm : MandelDim.IsFatouCoordOn (Work.Pert.liftF u σ α) Φm (Work.Pert.Qm Ξ α))
    (hw : w ∈ Work.Pert.Qm Ξ α)
    (hroom : (17 / 16 : ℝ) * (m : ℝ) + 1 ≤ |w.im| - Ξ - w.re) :
    (∀ j ≤ m, (Work.Pert.liftF u σ α)^[j] w ∈ Work.Pert.Qm Ξ α) ∧
      ‖(Φm ((Work.Pert.liftF u σ α)^[m] w) - (Work.Pert.liftF u σ α)^[m] w) - (Φm w - w)‖
        ≤ (m : ℝ) / 32 ∧
      w.re + (31 / 32 : ℝ) * (m : ℝ) ≤ ((Work.Pert.liftF u σ α)^[m] w).re ∧
      ((Work.Pert.liftF u σ α)^[m] w).re ≤ w.re + (33 / 32 : ℝ) * (m : ℝ) ∧
      |((Work.Pert.liftF u σ α)^[m] w).im - w.im| ≤ (m : ℝ) / 32 ∧
      Work.Pert.V5.mgA Ξ α w + (30 / 32 : ℝ) * (m : ℝ) ≤ Work.Pert.V5.mgA Ξ α ((Work.Pert.liftF u σ α)^[m] w) ∧
      Work.Pert.V5.mgB Ξ w ≤ Work.Pert.V5.mgB Ξ ((Work.Pert.liftF u σ α)^[m] w) + (17 / 16 : ℝ) * (m : ℝ) := by
  have hstep : ∀ z ∈ Work.Pert.Qm Ξ α,
      ‖Work.Pert.liftF u σ α z - (z + 1)‖ ≤ (1 / 32 : ℝ) :=
    fun z hz => (hNT.1.2 z hz).1
  have hwalk : ∀ j ≤ m, (Work.Pert.liftF u σ α)^[j] w ∈ Work.Pert.Qm Ξ α :=
    gate_walk_legal hΞ hstep hw hroom
  refine ⟨hwalk, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hc := coord_iterate (F := Work.Pert.liftF u σ α) (Φ := Φm)
      (Q := Work.Pert.Qm Ξ α) hΦm hwalk
    have hdev := iterate_norm_le (F := Work.Pert.liftF u σ α) (Q := Work.Pert.Qm Ξ α) hwalk hstep
    rw [hc]
    have he : (Φm w + (m : ℂ) - (Work.Pert.liftF u σ α)^[m] w) - (Φm w - w)
        = -((Work.Pert.liftF u σ α)^[m] w - (w + (m : ℂ))) := by ring
    rw [he, norm_neg]
    exact hdev
  · have hre := iterate_re_le (F := Work.Pert.liftF u σ α) (Q := Work.Pert.Qm Ξ α) hwalk hstep
    have h := (abs_le.mp hre).1
    linarith
  · have hre := iterate_re_le (F := Work.Pert.liftF u σ α) (Q := Work.Pert.Qm Ξ α) hwalk hstep
    have h := (abs_le.mp hre).2
    linarith
  · exact iterate_im_le (F := Work.Pert.liftF u σ α) (Q := Work.Pert.Qm Ξ α) hwalk hstep
  · exact iterate_mgA (Ξ := Ξ) (α := α) (F := Work.Pert.liftF u σ α)
      (Q := Work.Pert.Qm Ξ α) hwalk hstep
  · exact iterate_mgB (Ξ := Ξ) (F := Work.Pert.liftF u σ α)
      (Q := Work.Pert.Qm Ξ α) hwalk hstep

end

end Work.Pert.V5
