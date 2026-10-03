import Mathlib
import Submission.Work.Pert.Basic
import Submission.Work.Pert.Setup
import Submission.Work.Pert.abel
import Submission.Work.Interfaces.FatouNarrow
import Submission.Work.Pert.Ksub2.exp_ne_one_of_tauC_bounded

/-!
# `Work.Pert.Ksub2.abel_on_gate`

The Abel relation `τ_f ∘ F_f = f ∘ τ_f` of Shishikura (A.1.7)(iii) **on the gate `Qm ξ α`**,
with all the non-degeneracy hypotheses of the purely algebraic identity `Work.Pert.abel`
discharged from the *geometric* hypotheses of the perturbation setting:

* the near-translation hypothesis `NearTranslationL1 (liftF u σ α) (Qm ξ α)` rules out the points
  where the algebra degenerates: whenever `1 + τ u(τ) = 0`, or `(σ - τ) u(τ) = 1`, or
  `sfun u σ α w = 1`, the junk value of `Complex.log 0` makes `liftF` the identity at `w`, and
  then `‖liftF w - (w + 1)‖ = 1 > 1/32`;
* the pole-exclusion `Work.Pert.Ksub2.exp_ne_one_of_tauC_bounded` (proved separately) rules out
  `exp (-(2πi α w)) = 1`: there `tauC` has a pole, so on the *open* gate `tauC` is unbounded,
  contradicting `hτQ`;
* the remaining case `σ = 0` is trivial (`tauC 0 α · ≡ 0` and `f 0 = 0`).

The conclusion is the local form of `Work.Pert.abel`, which is stated for a *global* normal form
`f z = z + z (z - σ) u z`; here `f` is only known to have that form on `ball 0 rr`, and the
identity is applied at the point `τ_f w ∈ ball 0 rr`.
-/

set_option linter.unusedVariables false

namespace Work.Pert.Ksub2

noncomputable section

/-! ## Elementary consequences of the near-translation hypothesis on the gate -/

/-- If `sfun u σ α w = 1` then `liftF u σ α w = w`: the argument of the logarithm is `0`, and
`Complex.log 0 = 0`. -/
lemma liftF_eq_self_of_sfun_eq_one {u : ℂ → ℂ} {σ α w : ℂ}
    (h : Work.Pert.sfun u σ α w = 1) : Work.Pert.liftF u σ α w = w := by
  unfold Work.Pert.liftF
  rw [show 1 - Work.Pert.sfun u σ α w = 0 by rw [h, sub_self], Complex.log_zero, mul_zero,
    add_zero]

/-- `liftF u σ α` is never the identity at a point of the gate on which it is a near-translation:
`F w = w` would give `‖F w - (w + 1)‖ = 1 > 1/32`. -/
lemma liftF_ne_self {u : ℂ → ℂ} {σ α : ℂ} {ξ : ℝ} {w : ℂ} (hw : w ∈ Work.Pert.Qm ξ α)
    (hNT : MandelDim.NearTranslationL1 (Work.Pert.liftF u σ α) (Work.Pert.Qm ξ α)) :
    Work.Pert.liftF u σ α w ≠ w := by
  have hle : ‖Work.Pert.liftF u σ α w - (w + 1)‖ ≤ 1 / 32 := (hNT.1.2 w hw).1
  intro h
  rw [h] at hle
  have h1 : ‖w - (w + 1)‖ = 1 := by
    rw [show w - (w + 1) = -1 by ring, norm_neg, norm_one]
  rw [h1] at hle
  norm_num at hle

/-- The auxiliary quantity `sfun u σ α w` is never `1` on the gate. -/
lemma sfun_ne_one {u : ℂ → ℂ} {σ α : ℂ} {ξ : ℝ} {w : ℂ} (hw : w ∈ Work.Pert.Qm ξ α)
    (hNT : MandelDim.NearTranslationL1 (Work.Pert.liftF u σ α) (Work.Pert.Qm ξ α)) :
    Work.Pert.sfun u σ α w ≠ 1 :=
  fun h => liftF_ne_self hw hNT (liftF_eq_self_of_sfun_eq_one h)

/-- `1 + τ u(τ) ≠ 0` on the gate: otherwise `sfun` is the junk value `0`, whence
`liftF u σ α w = w`. -/
lemma one_add_mul_ne_zero {u : ℂ → ℂ} {σ α : ℂ} {ξ : ℝ} {w : ℂ} (hw : w ∈ Work.Pert.Qm ξ α)
    (hNT : MandelDim.NearTranslationL1 (Work.Pert.liftF u σ α) (Work.Pert.Qm ξ α)) :
    1 + Work.Pert.tauC σ α w * u (Work.Pert.tauC σ α w) ≠ 0 := by
  intro h1
  refine liftF_ne_self hw hNT ?_
  unfold Work.Pert.liftF Work.Pert.sfun
  rw [h1, div_zero, sub_zero, Complex.log_one, mul_zero, add_zero]

/-- `1 + τ u(τ) - σ u(τ) ≠ 0` on the gate: if `1 + τ u(τ) = 0` this is
`one_add_mul_ne_zero`, and otherwise `sfun u σ α w = 1`, whence `liftF u σ α w = w`. -/
lemma one_add_mul_sub_mul_ne_zero {u : ℂ → ℂ} {σ α : ℂ} {ξ : ℝ} {w : ℂ}
    (hw : w ∈ Work.Pert.Qm ξ α)
    (hNT : MandelDim.NearTranslationL1 (Work.Pert.liftF u σ α) (Work.Pert.Qm ξ α)) :
    1 + Work.Pert.tauC σ α w * u (Work.Pert.tauC σ α w) - σ * u (Work.Pert.tauC σ α w) ≠ 0 := by
  intro h1
  rcases eq_or_ne (1 + Work.Pert.tauC σ α w * u (Work.Pert.tauC σ α w)) 0 with h2 | h2
  · exact one_add_mul_ne_zero hw hNT h2
  · refine sfun_ne_one hw hNT ?_
    rw [Work.Pert.sfun, div_eq_one_iff_eq h2]
    exact (sub_eq_zero.mp h1).symm

/-! ## The Abel relation on the gate -/

/-- Shishikura (A.1.7)(iii) on the gate: `τ_f (F_f w) = f (τ_f w)` for `w ∈ Qm ξ α`. -/
theorem abel_on_gate {f : ℂ → ℂ} {u : ℂ → ℂ} {σ α : ℂ} {rr ξ : ℝ} (hrr : 0 < rr) (hξ : 0 < ξ)
    (hNT : MandelDim.NearTranslationL1 (Work.Pert.liftF u σ α) (Work.Pert.Qm ξ α))
    (hτQ : ∀ z ∈ Work.Pert.Qm ξ α, Work.Pert.tauC σ α z ∈ Metric.ball 0 rr)
    (hform : ∀ z ∈ Metric.ball 0 rr, f z = z + z * (z - σ) * u z)
    (hα : α ≠ 0) (hnorm : 1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α))
    (hbnd : ∀ z ∈ Metric.ball 0 rr, 1 / 2 ≤ ‖u z‖) :
    ∀ w ∈ Work.Pert.Qm ξ α, Work.Pert.tauC σ α (Work.Pert.liftF u σ α w) = f (Work.Pert.tauC σ α w) := by
  intro w hw
  by_cases hσ : σ = 0
  · -- `τ_{0} ≡ 0` and `f 0 = 0`: both sides vanish
    have hf0 : f 0 = 0 := by
      have h := hform 0 (by rw [Metric.mem_ball, dist_self]; exact hrr)
      rw [h]; ring
    subst hσ
    rw [show Work.Pert.tauC 0 α (Work.Pert.liftF u 0 α w) = 0 by simp [Work.Pert.tauC],
      show Work.Pert.tauC 0 α w = 0 by simp [Work.Pert.tauC]]
    exact hf0.symm
  · -- `σ ≠ 0`: discharge the algebraic hypotheses of `Work.Pert.abel`
    have hE : Complex.exp (-(2 * Real.pi * Complex.I * α * w)) ≠ 1 :=
      exp_ne_one_of_tauC_bounded hrr hσ hα hw hτQ
    have hz : Work.Pert.tauC σ α w ≠ 0 := by
      rw [Work.Pert.tauC, div_ne_zero_iff]
      exact ⟨hσ, sub_ne_zero.mpr (Ne.symm hE)⟩
    have hu2 := one_add_mul_ne_zero hw hNT
    have hk := one_add_mul_sub_mul_ne_zero hw hNT
    have hs : 1 - Work.Pert.sfun u σ α w ≠ 0 := sub_ne_zero.mpr (Ne.symm (sfun_ne_one hw hNT))
    have habel : Work.Pert.tauC σ α (Work.Pert.liftF u σ α w)
        = (fun z : ℂ => z + z * (z - σ) * u z) (Work.Pert.tauC σ α w) :=
      Work.Pert.abel hα hσ hz hu2 hk hE hs (fun z => rfl)
    rw [habel]
    exact (hform (Work.Pert.tauC σ α w) (hτQ w hw)).symm

end

end Work.Pert.Ksub2
