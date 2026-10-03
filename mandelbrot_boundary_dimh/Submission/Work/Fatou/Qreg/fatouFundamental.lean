import Mathlib
import Submission.Work.Interfaces.Fatou
import Submission.Work.Fatou.Qreg.Setup
import Submission.Work.Fatou.Qreg.stripInjOn
import Submission.Work.Fatou.Qreg.forwardIterate
import Submission.Work.Fatou.Qreg.backwardIterate

/-!
# Shishikura A.2.1(i): the fundamental strip of a near-translation

This file assembles `MandelDim.FatouFundamental` (Prop. A.2.1(i) of Shishikura, *The Hausdorff
dimension of the boundary of the Mandelbrot set and Julia sets*, Annals 1998) from three
independent pieces, each proved in a sibling file of this directory:

* `Work.Fatou.Qreg.stripInjOn`: `F` is injective on the vertical strip `x₀ - 1 < Re z < x₀ + 3`
  (the strip is convex and lies in `Qreg b₁ b₂`, so the mean value inequality applied to
  `F - id` gives `‖F v - F u‖ ≥ (31/32)‖v - u‖`);
* `Work.Fatou.Qreg.forwardIterate`: forward iteration from `Re z < x₀` reaches the line `Re = x₀`,
  never leaving `Qreg b₁ b₂`;
* `Work.Fatou.Qreg.backwardIterate`: backward iteration from `Re z ≥ x₀` reaches `fundStrip`.

The statement: with `x₀` a vertical line of `𝒬 = Qreg b₁ b₂` (i.e. `Re b₁ + 1 < x₀` and
`x₀ + 3 < Re b₂`), every point of `𝒬` has an orbit point in
`fundStrip F 𝒬 x₀ = {z ∈ 𝒬 | x₀ ≤ Re z ∧ every 𝒬-preimage of z has Re < x₀}`,
reached by forward or by backward iteration inside `𝒬`.

* If `Re z < x₀`, iterate forwards to the first landing point `s` with `Re s ≥ x₀`; then `s` is in
  the strip, because a second `𝒬`-preimage `w` of `s` with `Re w ≥ x₀` would be within `1/16` of
  the predecessor of `s` on the orbit, and both points lie in the strip on which `F` is injective.
* If `Re z ≥ x₀`, iterate backwards while a `𝒬`-preimage with real part `≥ x₀` exists; the real
  part decreases by at least `31/32` at every step, so the process stops, and it can only stop at a
  point of `fundStrip`.
-/

namespace Work.Fatou.Qreg

open Set Metric Complex
open scoped Topology

theorem fatouFundamental : MandelDim.FatouFundamental := by
  intro b₁ b₂ F x₀ _hadm hF h₁ h₂ z hz
  by_cases hx : x₀ ≤ z.re
  · -- `z` is already to the right of the line: iterate backwards.
    obtain ⟨k, s, hs, hsk, hQ⟩ :=
      backwardIterate (b₁ := b₁) (b₂ := b₂) (F := F) (x₀ := x₀) hF hz hx
    exact ⟨k, s, hs, Or.inr ⟨hQ, hsk⟩⟩
  · -- `z` is to the left of the line: iterate forwards.
    have hzx : z.re < x₀ := lt_of_not_ge hx
    obtain ⟨k, hk0, hchain, hkx, hprev⟩ :=
      forwardIterate (b₁ := b₁) (b₂ := b₂) (F := F) (x₀ := x₀) h₁ h₂ hF hz hzx
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hk0)
    simp only [Nat.succ_eq_add_one] at hchain hkx hprev
    refine ⟨m + 1, F^[m + 1] z, ?_, Or.inl ⟨hchain, rfl⟩⟩
    refine ⟨hchain (m + 1) le_rfl, hkx, ?_⟩
    -- the landing point is in the fundamental strip
    intro w hwQ hFw
    by_contra hcon
    have hwge : x₀ ≤ w.re := not_lt.mp hcon
    set v : ℂ := F^[m] z with hv
    have hvQ : v ∈ MandelDim.Qreg b₁ b₂ := by rw [hv]; exact hchain m (Nat.le_succ m)
    have hvre : v.re < x₀ := by rw [hv]; exact hprev m (Nat.lt_succ_self m)
    have hFv : F v = F^[m + 1] z := by rw [hv, Function.iterate_succ_apply']
    have hvw : F v = F w := by rw [hFv, hFw]
    have hva : (F v).re ≤ v.re + 33 / 32 :=
      (re_step_bounds (F := F) (u := v) (hF.2 v hvQ).1).2
    have hwb : w.re + 31 / 32 ≤ (F w).re :=
      (re_step_bounds (F := F) (u := w) (hF.2 w hwQ).1).1
    -- the two preimages of `F v` are `1/16`-close
    have hdist : ‖v - w‖ ≤ 1 / 16 := by
      have heq : v - w = (F w - (w + 1)) - (F v - (v + 1)) := by rw [hvw]; ring
      rw [heq]
      calc ‖(F w - (w + 1)) - (F v - (v + 1))‖
          ≤ ‖F w - (w + 1)‖ + ‖F v - (v + 1)‖ := norm_sub_le _ _
        _ ≤ 1 / 32 + 1 / 32 := by
            have h1 := (hF.2 w hwQ).1
            have h2 := (hF.2 v hvQ).1
            linarith
        _ = 1 / 16 := by norm_num
    have hv_lo : x₀ - 1 < v.re := by
      have h5 : |(v - w).re| ≤ 1 / 16 := le_trans (Complex.abs_re_le_norm _) hdist
      have h6 : -(1 / 16 : ℝ) ≤ v.re - w.re := by
        have := (abs_le.mp h5).1
        simp only [Complex.sub_re] at this
        linarith
      linarith
    have hw_hi : w.re < x₀ + 3 := by
      have h3 : (F w).re = (F v).re := by rw [hvw]
      linarith
    have hv_hi : v.re < x₀ + 3 := by linarith
    have hw_lo : x₀ - 1 < w.re := by linarith
    have hmemv : v ∈ {z : ℂ | x₀ - 1 < z.re ∧ z.re < x₀ + 3} := ⟨hv_lo, hv_hi⟩
    have hmemw : w ∈ {z : ℂ | x₀ - 1 < z.re ∧ z.re < x₀ + 3} := ⟨hw_lo, hw_hi⟩
    have heq2 : v = w := stripInjOn h₁ h₂ hF hmemv hmemw hvw
    rw [heq2] at hvre
    linarith

end Work.Fatou.Qreg
