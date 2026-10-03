import Mathlib
import Submission.Work.Pert.V5.Basics
import Submission.Work.FatouL1.preimage_of_re_ge
import Submission.Work.Interfaces.FatouNarrow

/-!
# `Work.Pert.Pin.back_two_clear` — the statement AS REQUESTED is FALSE (mis-stated)

## The defect

The conclusion asks for `z₂ ∈ Qm Ξ α` with `(liftF u σ α)^[2] z₂ = z`, together with

* `‖z₂ - (z - 2)‖ ≤ 2 / 32`  — i.e. `z₂` is within `1/16` of `z - 2`,
* `|z₂.re - z.re| ≤ 2 / 32`  — i.e. `z₂` is within `1/16` of `z` in real part.

The first is what a two-step backward pull-back must satisfy: `F = liftF u σ α` is a
near-translation (`‖F w - (w + 1)‖ ≤ 1/32` on the gate), so `F^[2] z₂ = z` forces
`z₂ ≈ z - 2`; this is also exactly the reason for the constant `17/8 = 2 · (1 + 2/32)` in `hbig`
(two pull-backs cost `1 + 2/32 = 17/16` of `mgA` each; each pull-back *gains* `15/16` of `mgB`).
The second conjunct is incompatible with it: for every pair `z, z₂ : ℂ`,

  `|z₂.re - z.re + 2| ≤ 2/32` (from the norm bound) and `|z₂.re - z.re| ≤ 2/32` give
  `2 = |(z₂.re - z.re + 2) - (z₂.re - z.re)| ≤ 2/32 + 2/32 = 1/8`,

a contradiction.  See `conj_contradiction` below: the two conjuncts are formally inconsistent.
Hence **no `z₂` whatsoever satisfies the conjunction**, and the requested statement is false for
every instance in which its hypotheses hold.

The hypotheses are *not* vacuous — they are precisely the PERT-area setting: `hNT` is what
`Work.Pert.gate_scale_L1` produces for the design's Cauchy data `(u, σ, α)`, and `hΦm` is then
supplied by `Work.FatouL1.fatouL1 : MandelDim.FatouStatementL1` (both files are sorry-free), while
`hbig`/`hzB` hold at points of `Qm Ξ α` of large height.  So the lemma is not merely unproved: it
is false, and it cannot be repaired by adding slack anywhere except in the fifth conjunct itself.

## The fix

Replace the conjunct `|z₂.re - z.re| ≤ 2 / 32` by `|(z₂ + 2).re - z.re| ≤ 2 / 32`
(equivalently `|z₂.re - (z.re - 2)| ≤ 2 / 32`), or simply delete it: the intended information
about the real part *is* `‖z₂ - (z - 2)‖ ≤ 2/32` (the shift by two is real, so the imaginary part is
preserved and the real part is shifted), and the corrected conjunct is implied by the norm bound.

`back_two_clear_fixed` below is the requested statement with **exactly** that one change; it is
proved, sorry-free, and imports nothing beyond this file.  It is a drop-in replacement: same name
suffix `_fixed`, same hypotheses (including the unused ones), same constants.

## The proof of the fixed statement (summary)

The pull-back step is Banach's fixed point theorem in the form
`Work.FatouL1.exists_preimage_in_closedBall`: if `B̄(v - 1, 1/32) ⊆ Qm Ξ α` then `v` has a
preimage in that ball.  The ball lies in the gate because a pull-back step sends

* `mgA Ξ α v ↦ ≥ mgA Ξ α v - (1 + 2/32) = mgA Ξ α v - 17/16`
  (`Work.Pert.V5.mgA Ξ α v = v.re - Ξ + Re(1/α) + |v.im + Im(1/α)|`, and `Re` decreases by at
  most `1 + 1/32` while `|·|` decreases by at most `1/32`), and
* `mgB Ξ v ↦ ≥ mgB Ξ v + (1 - 2/32) = mgB Ξ v + 15/16`
  (`Work.Pert.V5.mgB Ξ v = |v.im| - Ξ - v.re`),

which are `mgA_pullback` / `mgB_pullback`.  Iterating twice from `z` (allowed by
`hbig`/`hzB`: `mgA` is at least `25/8` at `z`, so it stays positive, and `mgB` grows) produces
`z₂ ∈ Qm Ξ α` with `F z₂ = z₁`, `F z₁ = z`, the clearance
`max (√2 Rde) 1 ≤ min (mgA Ξ α z₂) (mgB Ξ z₂)`, and the deviation bound from the exact recursion
`Work.Pert.V5.dev_step` (each step changes `Φm - id` by at most `1/32`).
-/

set_option linter.unusedVariables false

namespace Work.Pert.Pin

open Set Metric

/-- **The conclusion of the requested `back_two_clear` is self-contradictory.**  For every `z z₂`,
`‖z₂ - (z - 2)‖ ≤ 2/32` and `|z₂.re - z.re| ≤ 2/32` cannot both hold: writing `a := z₂.re - z.re`,
the first gives `|a + 2| ≤ 1/16` and the second `|a| ≤ 1/16`, whence
`2 = |(a + 2) - a| ≤ 1/16 + 1/16 = 1/8`. -/
theorem conj_contradiction (z z₂ : ℂ)
    (h₁ : ‖z₂ - (z - 2)‖ ≤ 2 / 32) (h₂ : |z₂.re - z.re| ≤ 2 / 32) : False := by
  set a : ℝ := z₂.re - z.re with ha
  have hre : (z₂ - (z - 2)).re = a + 2 := by
    rw [ha]; norm_num; ring
  have h₁' : |a + 2| ≤ 2 / 32 := by
    have := Complex.abs_re_le_norm (z₂ - (z - 2))
    rw [hre] at this
    exact le_trans this h₁
  have h₂' : |a| ≤ 2 / 32 := by rw [ha]; exact h₂
  have := abs_le.mp h₁'
  have := abs_le.mp h₂'
  norm_num at *
  linarith

/-- **One backward pull-back step under a near-translation decreases the `b₁`-margin `mgA` by at
most `1 + 2/32 = 17/16`.**  If `‖w - (z - 1)‖ ≤ 1/32` then
`mgA Ξ α z - 17/16 ≤ mgA Ξ α w`. -/
theorem mgA_pullback {Ξ : ℝ} {α : ℂ} {z w : ℂ} (h : ‖w - (z - 1)‖ ≤ 1 / 32) :
    Work.Pert.V5.mgA Ξ α z - 17 / 16 ≤ Work.Pert.V5.mgA Ξ α w := by
  set ε : ℂ := w - (z - 1) with hε
  have heq : w = z - 1 + ε := by rw [hε]; ring
  have hεn : ‖ε‖ ≤ 1 / 32 := by rw [hε]; exact h
  have hre : |ε.re| ≤ 1 / 32 := le_trans (Complex.abs_re_le_norm ε) hεn
  have him : |ε.im| ≤ 1 / 32 := le_trans (Complex.abs_im_le_norm ε) hεn
  have h1 : w.re = z.re - 1 + ε.re := by rw [heq]; simp
  have h2 : w.im = z.im + ε.im := by rw [heq]; simp
  have h3 : |z.im + (1 / α).im| - 1 / 32 ≤ |z.im + ε.im + (1 / α).im| := by
    have := abs_sub_abs_le_abs_add (z.im + (1 / α).im) ε.im
    have h4 : |(z.im + (1 / α).im) + ε.im| = |z.im + ε.im + (1 / α).im| := by ring_nf
    rw [h4] at this
    linarith [(abs_le.mp him).2]
  rw [Work.Pert.V5.mgA, Work.Pert.V5.mgA, h1, h2]
  have := (abs_le.mp hre).1
  linarith

/-- **One backward pull-back step under a near-translation increases the `b₂`-margin `mgB` by at
least `1 - 2/32 = 15/16`.**  If `‖w - (z - 1)‖ ≤ 1/32` then
`mgB Ξ z + 15/16 ≤ mgB Ξ w`. -/
theorem mgB_pullback {Ξ : ℝ} {z w : ℂ} (h : ‖w - (z - 1)‖ ≤ 1 / 32) :
    Work.Pert.V5.mgB Ξ z + 15 / 16 ≤ Work.Pert.V5.mgB Ξ w := by
  set ε : ℂ := w - (z - 1) with hε
  have heq : w = z - 1 + ε := by rw [hε]; ring
  have hεn : ‖ε‖ ≤ 1 / 32 := by rw [hε]; exact h
  have hre : |ε.re| ≤ 1 / 32 := le_trans (Complex.abs_re_le_norm ε) hεn
  have him : |ε.im| ≤ 1 / 32 := le_trans (Complex.abs_im_le_norm ε) hεn
  have h1 : w.re = z.re - 1 + ε.re := by rw [heq]; simp
  have h2 : w.im = z.im + ε.im := by rw [heq]; simp
  have h3 : |z.im| - 1 / 32 ≤ |w.im| := by
    rw [h2]
    have := abs_sub_abs_le_abs_add (z.im) ε.im
    linarith [(abs_le.mp him).2]
  rw [Work.Pert.V5.mgB, Work.Pert.V5.mgB, h1]
  have h4 := (abs_le.mp hre).2
  linarith

/-- **`back_two_clear` with the fifth conjunct repaired** (`|z₂.re - z.re|` replaced by
`|(z₂ + 2).re - z.re|`, i.e. the real part is shifted by `2`, as it must be).  Same hypotheses,
same constants, same conclusion otherwise.  The hypotheses `hΞ hM hInF1 hα hQAdm` are not needed
for this part of the argument; they are kept so that the statement is a drop-in replacement. -/
theorem back_two_clear_fixed {Ξ M Rde : ℝ} {α σ : ℂ} {u Φm : ℂ → ℂ}
    (hΞ : 0 < Ξ) (hM : 2 ^ 10 ≤ M) (hInF1 : MandelDim.InF1 α)
    (hα : ‖α‖ ≤ 1 / (32 * (M + 2 + Ξ)))
    (hQAdm : MandelDim.QAdm (some ((Ξ : ℂ) - 1 / α)) (some (-(Ξ : ℂ))))
    (hRde : 0 < Rde)
    (hNT : MandelDim.NearTranslationL1 (Work.Pert.liftF u σ α) (Work.Pert.Qm Ξ α))
    (hΦm : MandelDim.IsFatouCoordOn (Work.Pert.liftF u σ α) Φm (Work.Pert.Qm Ξ α))
    {z : ℂ} (hz : z ∈ Work.Pert.Qm Ξ α)
    (hbig : max (Real.sqrt 2 * Rde) 1 + 17 / 8 < Work.Pert.V5.mgA Ξ α z)
    (hzB : Real.sqrt 2 * Rde ≤ Work.Pert.V5.mgB Ξ z) :
    ∃ z₂ ∈ Work.Pert.Qm Ξ α,
      (Work.Pert.liftF u σ α)^[2] z₂ = z ∧
      ‖z₂ - (z - 2)‖ ≤ 2 / 32 ∧
      max (Real.sqrt 2 * Rde) 1 ≤ min (Work.Pert.V5.mgA Ξ α z₂) (Work.Pert.V5.mgB Ξ z₂) ∧
      |z₂.im - z.im| ≤ 2 / 32 ∧
      |(z₂ + 2).re - z.re| ≤ 2 / 32 ∧
      ‖(Φm z - z) - (Φm z₂ - z₂)‖ ≤ 2 / 32 := by
  -- at `z` the `b₁`-margin is already `> 25/8` and the `b₂`-margin is positive
  have hzA : (25 : ℝ) / 8 < Work.Pert.V5.mgA Ξ α z := by
    have : (1 : ℝ) ≤ max (Real.sqrt 2 * Rde) 1 := le_max_right _ _
    linarith
  have hzBpos : (0 : ℝ) < Work.Pert.V5.mgB Ξ z := by
    have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have := mul_pos hs2 hRde
    linarith
  -- the pull-back ball of a point whose margins exceed the pull-back loss lies in the gate
  have hball_of : ∀ v : ℂ, (0 : ℝ) < Work.Pert.V5.mgA Ξ α v - 17 / 16 →
      (0 : ℝ) < Work.Pert.V5.mgB Ξ v + 15 / 16 →
      Metric.closedBall (v - 1) (1 / 32) ⊆ Work.Pert.Qm Ξ α := by
    intro v hvA hvB w hw
    rw [Metric.mem_closedBall, dist_eq_norm] at hw
    rw [Work.Pert.V5.mem_Qm_iff_mg]
    exact ⟨lt_of_lt_of_le hvA (mgA_pullback hw), lt_of_lt_of_le hvB (mgB_pullback hw)⟩
  have hQopen : IsOpen (Work.Pert.Qm Ξ α) := by
    rw [Work.Pert.Qm]; exact Work.Fatou.Qreg.isOpen_Qreg _ _
  have hdiff : DifferentiableOn ℂ (Work.Pert.liftF u σ α) (Work.Pert.Qm Ξ α) := hNT.1.1
  have hFb : ∀ w ∈ Work.Pert.Qm Ξ α, ‖Work.Pert.liftF u σ α w - (w + 1)‖ ≤ 1 / 32 :=
    fun w hw => (hNT.1.2 w hw).1
  have hFd : ∀ w ∈ Work.Pert.Qm Ξ α, ‖deriv (Work.Pert.liftF u σ α) w - 1‖ ≤ 1 / 32 :=
    fun w hw => (hNT.1.2 w hw).2
  -- first backward step: a preimage `z₁ ≈ z - 1` of `z`
  have hballz : Metric.closedBall (z - 1) (1 / 32) ⊆ Work.Pert.Qm Ξ α :=
    hball_of z (by linarith) (by linarith)
  obtain ⟨z₁, hz₁b, hz₁F⟩ :=
    Work.FatouL1.exists_preimage_in_closedBall hQopen hballz hdiff hFb hFd
  have hz₁n : ‖z₁ - (z - 1)‖ ≤ 1 / 32 := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hz₁b
  have hz₁Q : z₁ ∈ Work.Pert.Qm Ξ α := hballz hz₁b
  have hz₁A : Work.Pert.V5.mgA Ξ α z - 17 / 16 ≤ Work.Pert.V5.mgA Ξ α z₁ := mgA_pullback hz₁n
  have hz₁B : Work.Pert.V5.mgB Ξ z + 15 / 16 ≤ Work.Pert.V5.mgB Ξ z₁ := mgB_pullback hz₁n
  -- second backward step: a preimage `z₂ ≈ z - 2` of `z₁`
  have hballz₁ : Metric.closedBall (z₁ - 1) (1 / 32) ⊆ Work.Pert.Qm Ξ α :=
    hball_of z₁ (by linarith) (by linarith)
  obtain ⟨z₂, hz₂b, hz₂F⟩ :=
    Work.FatouL1.exists_preimage_in_closedBall hQopen hballz₁ hdiff hFb hFd
  have hz₂n : ‖z₂ - (z₁ - 1)‖ ≤ 1 / 32 := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hz₂b
  have hz₂Q : z₂ ∈ Work.Pert.Qm Ξ α := hballz₁ hz₂b
  have hz₂A : Work.Pert.V5.mgA Ξ α z₁ - 17 / 16 ≤ Work.Pert.V5.mgA Ξ α z₂ := mgA_pullback hz₂n
  have hz₂B : Work.Pert.V5.mgB Ξ z₁ + 15 / 16 ≤ Work.Pert.V5.mgB Ξ z₂ := mgB_pullback hz₂n
  -- `z₂` is within `2/32` of `z - 2`
  have hnorm : ‖z₂ - (z - 2)‖ ≤ 2 / 32 := by
    have := norm_add_le (z₂ - (z₁ - 1)) (z₁ - (z - 1))
    have he : z₂ - (z - 2) = (z₂ - (z₁ - 1)) + (z₁ - (z - 1)) := by ring
    rw [he]
    linarith
  refine ⟨z₂, hz₂Q, ?_, hnorm, ?_, ?_, ?_, ?_⟩
  · -- the two-step orbit relation
    have h2 : (Work.Pert.liftF u σ α)^[2] z₂
        = Work.Pert.liftF u σ α (Work.Pert.liftF u σ α z₂) := by
      norm_num [Function.iterate_succ_apply', Function.iterate_one]
    rw [h2, hz₂F, hz₁F]
  · -- the clearance at `z₂`
    have hA : max (Real.sqrt 2 * Rde) 1 < Work.Pert.V5.mgA Ξ α z₂ := by linarith
    have hB : max (Real.sqrt 2 * Rde) 1 ≤ Work.Pert.V5.mgB Ξ z₂ := by
      have hs2 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
      have h0 : (0 : ℝ) ≤ Real.sqrt 2 * Rde := mul_nonneg hs2 hRde.le
      have hmax : max (Real.sqrt 2 * Rde) 1 ≤ Real.sqrt 2 * Rde + 15 / 8 := by
        rw [max_le_iff]; exact ⟨by linarith, by linarith⟩
      linarith
    exact le_min hA.le hB
  · -- imaginary part: the two-step shift is by the real number `2`
    have h := Complex.abs_im_le_norm (z₂ - (z - 2))
    have he : (z₂ - (z - 2)).im = z₂.im - z.im := by simp
    rw [he] at h
    linarith
  · -- real part, measured from `z - 2`
    have h := Complex.abs_re_le_norm (z₂ - (z - 2))
    have he : (z₂ - (z - 2)).re = (z₂ + 2).re - z.re := by simp; ring
    rw [he] at h
    linarith
  · -- the deviation `Φm - id` changes by at most `1/32` per step
    have hst₁ := Work.Pert.V5.dev_step hΦm (w := z₁) hz₁Q (by rw [hz₁F]; exact hz)
    have hst₂ := Work.Pert.V5.dev_step hΦm (w := z₂) hz₂Q (by rw [hz₂F]; exact hz₁Q)
    rw [hz₁F] at hst₁
    rw [hz₂F] at hst₂
    have e₁ : ‖(Φm z - z) - (Φm z₁ - z₁)‖ ≤ 1 / 32 := by
      rw [hst₁, norm_neg]
      have he : z - (z₁ + 1) = -(z₁ - (z - 1)) := by ring
      rw [he, norm_neg]
      exact hz₁n
    have e₂ : ‖(Φm z₁ - z₁) - (Φm z₂ - z₂)‖ ≤ 1 / 32 := by
      rw [hst₂, norm_neg]
      have he : z₁ - (z₂ + 1) = -(z₂ - (z₁ - 1)) := by ring
      rw [he, norm_neg]
      exact hz₂n
    have := norm_add_le ((Φm z - z) - (Φm z₁ - z₁)) ((Φm z₁ - z₁) - (Φm z₂ - z₂))
    have he : (Φm z - z) - (Φm z₂ - z₂)
        = ((Φm z - z) - (Φm z₁ - z₁)) + ((Φm z₁ - z₁) - (Φm z₂ - z₂)) := by ring
    rw [he]
    linarith

end Work.Pert.Pin
