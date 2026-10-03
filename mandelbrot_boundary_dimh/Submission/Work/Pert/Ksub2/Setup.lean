import Mathlib
import Submission.Work.Pert.Basic
import Submission.Work.Pert.Setup
import Submission.Work.Pert.MaxDom
import Submission.Work.Pert.AsmDefs
import Submission.Work.Pert.exhaust_level_bound
import Submission.Work.Pert.Qm_slice
import Submission.Work.Pert.tools
import Submission.Work.Parab.Setup
import Submission.Work.Pert.exists_norm_add_clog_bound
import Submission.Work.Pert.exists_fatouCoord_inv_tau0_phi
import Submission.Work.Pert.deriv_psi0_close
import Submission.Work.Pert.tau0_phi_local_cover
import Submission.Work.Interfaces.Fatou

/-!
# `Work.Pert.Ksub2.Setup`

Language layer for the proof of `Work.Pert.Ksub_phi_close_v2`.

* `F0f f₀ = τ₀ ∘ f₀ ∘ τ₀` — the limit dynamics in the `w`-plane;
* `Xc d u = τ₀ (d.φ u)` — the datum's curve, a semi-conjugacy from `u ↦ u + 1` to `F0f`;
* `Dstrip M T` — the deep horizontal strip `{-M-1 ≤ Re u ≤ -M, |Im u| ≤ T}` on which the
  perturbed coordinate is compared with the datum's;
* `exists_anchor` — the datum-side anchor: a deep point `u₀` of the curve together with a Fatou
  coordinate `Φ₀` of `F₀` on a ball around `Xc d u₀` which inverts the curve there.
-/

namespace Work.Pert

open MandelDim Complex Set

noncomputable section

/-- The limit dynamics `F₀ = τ₀ ∘ f₀ ∘ τ₀` of the `w`-plane. -/
def F0f (f₀ : ℂ → ℂ) : ℂ → ℂ := fun w => MandelDim.tau0 (f₀ (MandelDim.tau0 w))

/-- The datum's curve `u ↦ τ₀ (φ₀ u)`: a semi-conjugacy from the shift `u ↦ u + 1` to `F0f`. -/
def Xc {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀) : ℂ → ℂ :=
  fun u => MandelDim.tau0 (d.φ u)

/-- The curve step: `Xc (u+1) = F0f (Xc u)`. -/
theorem Xc_add_one {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀) {u : ℂ}
    (hu : u ∈ d.Dφ) (hu1 : u + 1 ∈ d.Dφ) : Xc d (u + 1) = F0f f₀ (Xc d u) := by
  have habel : d.φ (u + 1) = f₀ (d.φ u) := d.φ_abel u hu hu1
  simp only [Xc, F0f, habel]
  rw [tau0_tau0]

/-- The deep strip `{-M-1 ≤ Re u ≤ -M, |Im u| ≤ T}`. -/
def Dstrip (M T : ℝ) : Set ℂ := {u : ℂ | -M - 1 ≤ u.re ∧ u.re ≤ -M ∧ |u.im| ≤ T}

theorem Dstrip_sub_QLeft {M T ξ : ℝ} (h : ξ + 1 ≤ M) : Dstrip M T ⊆ MandelDim.QLeft ξ := by
  intro u hu
  exact Work.Parab.halfplane_subset_QLeft ξ (lt_of_le_of_lt hu.2.1 (by linarith))

theorem Dstrip_sub_Qm {M T ξ : ℝ} {α : ℂ} (hξ : 0 < ξ) (hM : ξ + 1 ≤ M)
    (hD : M + 1 + ξ < (1 / α).re) : Dstrip M T ⊆ Qm ξ α := by
  intro u hu
  rw [Qm_mem_iff]
  have hre1 : -M - 1 ≤ u.re := hu.1
  have hre2 : u.re ≤ -M := hu.2.1
  constructor
  · have h2 := abs_nonneg (u.im + (1 / α).im)
    linarith
  · have h3 := abs_nonneg u.im
    linarith

/-- Every `w` with `-M-1 < Re w` and `|Im w| ≤ T` has a nonnegative integer translate in the
strip `Dstrip M T`. -/
theorem exists_nat_sub_mem_Dstrip {M T : ℝ} {w : ℂ} (hre : -M - 1 < w.re) (him : |w.im| ≤ T) :
    ∃ n : ℕ, w - (n : ℂ) ∈ Dstrip M T := by
  by_cases h : w.re ≤ -M
  · refine ⟨0, ?_⟩
    have hw : w - ((0 : ℕ) : ℂ) = w := by simp
    rw [hw]
    exact ⟨le_of_lt hre, h, him⟩
  · push Not at h
    refine ⟨(⌈w.re + M⌉).toNat, ?_⟩
    have hpos : 0 < ⌈w.re + M⌉ := Int.ceil_pos.mpr (by linarith)
    have hcast : ((⌈w.re + M⌉).toNat : ℝ) = (⌈w.re + M⌉ : ℝ) := by
      have h := Int.toNat_of_nonneg hpos.le
      exact_mod_cast h
    have hle : w.re + M ≤ (⌈w.re + M⌉ : ℝ) := Int.le_ceil _
    have hlt : (⌈w.re + M⌉ : ℝ) ≤ w.re + M + 1 := by
      have := Int.ceil_lt_add_one (w.re + M); linarith
    have hre' : (w - ((⌈w.re + M⌉).toNat : ℂ)).re = w.re - ((⌈w.re + M⌉).toNat : ℝ) := by
      simp
    have him' : (w - ((⌈w.re + M⌉).toNat : ℂ)).im = w.im := by
      simp
    refine ⟨?_, ?_, ?_⟩
    · rw [hre', hcast]; linarith
    · rw [hre', hcast]; linarith
    · rw [him']; exact him

/-- **Coverage from a deviation bound.**  If the closed ball `closedBall u r` is inside `Q`, the
coordinate `Ψ` is holomorphic on it with `‖Ψ' - 1‖ ≤ 1/2`, and `Ψ` displaces `u` by less than
`r/4`, then `u` lies in the image `Ψ '' Q`.  (This is `image_cover_centered` read at the centre.) -/
theorem mem_image_of_dev_le {Ψ : ℂ → ℂ} {Q : Set ℂ} {u : ℂ} {r : ℝ}
    (hr : 0 < r) (hball : Metric.closedBall u r ⊆ Q)
    (hdiff : ∀ z ∈ Metric.closedBall u r, DifferentiableAt ℂ Ψ z)
    (hder : ∀ z ∈ Metric.closedBall u r, ‖deriv Ψ z - 1‖ ≤ 1 / 2)
    (hdev : ‖Ψ u - u‖ < r / 4) : u ∈ Ψ '' Q := by
  have hcov := image_cover_centered (Φ := Ψ) (z₀ := u) (r := r) hr hdiff hder
  obtain ⟨ζ, hζ, hζeq⟩ := hcov (by
    rw [Metric.mem_ball, dist_eq_norm, norm_sub_rev]
    exact hdev)
  exact ⟨ζ, hball hζ, hζeq⟩


end

end Work.Pert
