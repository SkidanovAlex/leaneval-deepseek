import Mathlib
import Submission.Work.Pert.pert2v2.PhiMinusDef
import Submission.Work.Pert.nearTranslation_F0
import Submission.Work.Pert.pert2v2.exists_Psi_lower

/-!
# `Work.Pert.pert2v2.Psi_Xc_constant`

Compatibility between the model lower Fatou coordinate (`FATOU` contract) and the datum's curve
(`PARAB`).  `F₀ w = τ₀ (f₀ (τ₀ w))` is the model map, `Xc d u = τ₀ (d.φ u)` the datum's curve, a
semi-conjugacy from the shift `u ↦ u + 1` to `F₀`.  The statement says: every Fatou coordinate `Ψ`
of `F₀` on the left cone `Qreg none (some (-Ξ'))` satisfies `Ψ (Xc d u) = u + c` on the region of
the `u`-plane where the curve stays in the cone.
-/

namespace Work.Pert.pert2v2

open MandelDim Complex Set

noncomputable section

/-- `Xc d u` does not vanish on the left cone (it has modulus `> Ξ'/2` there). -/
theorem Xc_ne_zero_of_mem {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀) {Ξ' : ℝ}
    (hΞ' : 0 < Ξ') {u : ℂ} (hu : Work.Pert.Xc d u ∈ MandelDim.Qreg none (some (-(Ξ' : ℂ)))) :
    Work.Pert.Xc d u ≠ 0 := by
  have h := Work.Pert.NTF0.norm_gt_of_mem_left hu
  intro h0
  rw [h0, norm_zero] at h
  linarith

/-- `τ₀` undoes the curve: `τ₀ (Xc d u) = d.φ u`. -/
theorem tau0_Xc {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀) {u : ℂ}
    (h : Work.Pert.Xc d u ≠ 0) : MandelDim.tau0 (Work.Pert.Xc d u) = d.φ u := by
  have hφ : d.φ u ≠ 0 := by
    intro h0
    exact h (by simp [Work.Pert.Xc, h0, MandelDim.tau0])
  simp only [Work.Pert.Xc, MandelDim.tau0] at h ⊢
  field_simp

/-- On the left cone the datum's coordinate has small modulus: `‖d.φ u‖ ≤ 2/Ξ'`. -/
theorem phi_norm_le {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀) {Ξ' : ℝ}
    (hΞ' : 0 < Ξ') {u : ℂ} (hu : Work.Pert.Xc d u ∈ MandelDim.Qreg none (some (-(Ξ' : ℂ)))) :
    ‖d.φ u‖ ≤ 2 / Ξ' := by
  have hne := Xc_ne_zero_of_mem d hΞ' hu
  have hnorm := Work.Pert.NTF0.norm_gt_of_mem_left hu
  have hφ : d.φ u = MandelDim.tau0 (Work.Pert.Xc d u) := (tau0_Xc d hne).symm
  rw [hφ, Work.Pert.NTF0.norm_tau0]
  have hpos : (0:ℝ) < ‖Work.Pert.Xc d u‖ := norm_pos_iff.mpr hne
  rw [div_le_div_iff₀ hpos hΞ']
  linarith [hnorm]

/-- The uniformizing coordinate is defined at points whose curve value lies in the cone: the
curve value has modulus `> Ξ'/2`, so `d.φ u = τ₀ (Xc d u)` has modulus `≤ 2/Ξ' < r₀`, which lies in
`D₀` (an open neighbourhood of `0`) and hence, by `ParabData.succ_iff`, `u + 1 ∈ d.Dφ`. -/
theorem succ_mem_Dphi {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀) {Ξ' r : ℝ}
    (hΞ' : 0 < Ξ') (hr : 0 < r) (hball : Metric.ball (0 : ℂ) r ⊆ D₀)
    (hbig : 2 / Ξ' < r) {u : ℂ} (hu : u ∈ d.Dφ)
    (hXc : Work.Pert.Xc d u ∈ MandelDim.Qreg none (some (-(Ξ' : ℂ)))) : u + 1 ∈ d.Dφ := by
  have hne := Xc_ne_zero_of_mem d hΞ' hXc
  have hφ : d.φ u = MandelDim.tau0 (Work.Pert.Xc d u) := (tau0_Xc d hne).symm
  have hmem : d.φ u ∈ D₀ := by
    apply hball
    rw [Metric.mem_ball, dist_zero_right, hφ, Work.Pert.NTF0.norm_tau0]
    have hnorm := Work.Pert.NTF0.norm_gt_of_mem_left hXc
    have hpos : (0:ℝ) < ‖Work.Pert.Xc d u‖ := norm_pos_iff.mpr hne
    have h1 : 1 < r * ‖Work.Pert.Xc d u‖ := by
      have h2 : (2 / Ξ') * (Ξ' / 2) < r * (Ξ' / 2) :=
        mul_lt_mul_of_pos_right hbig (by positivity)
      have h3 : r * (Ξ' / 2) < r * ‖Work.Pert.Xc d u‖ :=
        mul_lt_mul_of_pos_left hnorm hr
      have h4 : (2 / Ξ') * (Ξ' / 2) = 1 := by field_simp
      linarith
    rw [div_lt_iff₀ hpos]
    linarith
  exact (d.succ_iff u hu).mpr hmem

/-- The curve's step: `Xc d (u+1) = F₀ (Xc d u)`. -/
theorem Xc_add_one' {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀) {u : ℂ}
    (hu : u ∈ d.Dφ) (hu1 : u + 1 ∈ d.Dφ) :
    Work.Pert.Xc d (u + 1) = Work.Pert.F0f f₀ (Work.Pert.Xc d u) :=
  Work.Pert.Xc_add_one d hu hu1

/-- **Periodicity of `h = Ψ ∘ Xc d - id`**: along a legal step of the curve inside the cone,
`h (u+1) = h u`. -/
theorem h_periodic {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀) {Ξ' : ℝ}
    {Ψ : ℂ → ℂ} (hΨ : MandelDim.IsFatouCoordOn (fun w : ℂ => MandelDim.tau0 (f₀ (MandelDim.tau0 w)))
      Ψ (MandelDim.Qreg none (some (-(Ξ' : ℂ))))) {u : ℂ} (hu : u ∈ d.Dφ) (hu1 : u + 1 ∈ d.Dφ)
    (h1 : Work.Pert.Xc d u ∈ MandelDim.Qreg none (some (-(Ξ' : ℂ))))
    (h2 : (fun w : ℂ => MandelDim.tau0 (f₀ (MandelDim.tau0 w))) (Work.Pert.Xc d u)
      ∈ MandelDim.Qreg none (some (-(Ξ' : ℂ)))) :
    Ψ (Work.Pert.Xc d (u + 1)) - (u + 1) = Ψ (Work.Pert.Xc d u) - u := by
  have hstep := hΨ.2.2 (Work.Pert.Xc d u) h1 h2
  rw [Work.Pert.Xc_add_one d hu hu1]
  change Ψ (MandelDim.tau0 (f₀ (MandelDim.tau0 (Work.Pert.Xc d u)))) - (u + 1)
    = Ψ (Work.Pert.Xc d u) - u
  rw [hstep]
  ring

/-- `Xc d` is differentiable at every point of `d.Dφ` where `d.φ` does not vanish. -/
theorem differentiableAt_Xc {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀) {u : ℂ}
    (hu : u ∈ d.Dφ) (hne : d.φ u ≠ 0) : DifferentiableAt ℂ (Work.Pert.Xc d) u := by
  have h1 : DifferentiableAt ℂ d.φ u := d.φ_holo.differentiableAt (d.Dφ_open.mem_nhds hu)
  have h2 : DifferentiableAt ℂ (fun v => (-1 : ℂ) / d.φ v) u := by
    have h3 : DifferentiableAt ℂ (fun v => ((-1 : ℂ) * d.φ v)⁻¹) u :=
      (h1.const_mul (-1)).inv (by simp [hne])
    simpa [div_eq_mul_inv, mul_inv] using h3
  exact h2

/-- `τ₀ w ≠ 0` when `w ≠ 0`. -/
theorem tau0_ne_zero_of_ne_zero {w : ℂ} (h : w ≠ 0) : MandelDim.tau0 w ≠ 0 :=
  Work.Pert.NTF0.tau0_ne_zero h

/-- **The branch of the inverse of the curve through the sector** `QLeft d.ξ₀`: for `z` in the
image of `Xc d` on the sector it returns a point of the sector mapping to `z`; junk (`0`)
elsewhere. -/
noncomputable def PhiSec {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀) (z : ℂ) : ℂ :=
  by
  classical
  exact if h : ∃ u : ℂ, u ∈ MandelDim.QLeft d.ξ₀ ∧ Work.Pert.Xc d u = z then Classical.choose h else 0

/-- The defining property of `PhiSec`: on the sectorial image, `Xc d (PhiSec d z) = z` and the
chosen point lies in the sector. -/
theorem PhiSec_spec {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀) {z : ℂ}
    (h : ∃ u : ℂ, u ∈ MandelDim.QLeft d.ξ₀ ∧ Work.Pert.Xc d u = z) :
    PhiSec d z ∈ MandelDim.QLeft d.ξ₀ ∧ Work.Pert.Xc d (PhiSec d z) = z := by
  classical
  have := Classical.choose_spec h
  simpa [PhiSec, dif_pos h] using this

/-- On the sector the curve is injective (`ParabData.φ_inj`), so **the branch is the genuine
inverse**: if `u ∈ QLeft ξ₀` and `z = Xc d u` lies in the sectorial image, then `PhiSec d z = u`. -/
theorem PhiSec_eq_of {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀) {u z : ℂ}
    (hu : u ∈ MandelDim.QLeft d.ξ₀) (hz : z = Work.Pert.Xc d u) (hzu : z ≠ 0)
    (h : ∃ u' : ℂ, u' ∈ MandelDim.QLeft d.ξ₀ ∧ Work.Pert.Xc d u' = z) : PhiSec d z = u := by
  obtain ⟨hu', hXc'⟩ := PhiSec_spec d h
  have hne' : Work.Pert.Xc d (PhiSec d z) ≠ 0 := by rw [hXc']; exact hzu
  have hne : Work.Pert.Xc d u ≠ 0 := by rw [← hz]; exact hzu
  have hφ : d.φ (PhiSec d z) = d.φ u := by
    rw [(tau0_Xc d hne').symm, hXc', hz, (tau0_Xc d hne).symm]
  exact d.φ_inj hu' hu hφ

end

end Work.Pert.pert2v2
