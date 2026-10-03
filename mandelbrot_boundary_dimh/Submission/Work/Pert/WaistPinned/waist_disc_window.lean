import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Pert.Setup
import Submission.Work.Pert.Gates
import Submission.Work.Pert.Qm_slice
import Submission.Work.Pert.I_mul_half_eta_mem_Qm

/-!
# PERT · `Work.Pert.WaistPinned.waist_disc_window`

**The waist disc window.**  If `z₀` sits on the imaginary axis (`Re z₀ = 0`), `T = |Im z₀|`,
`ρ ≥ 0` and `ξ + 2ρ < T`, then the closed disc of radius `ρ` about `z₀` lies in the *waist*
`Qm ξ α ∩ Qp ξ α` of the two §4.2 gates — for every `α ∈ 𝓕₁` (`MandelDim.InF1 α`), and with no
hypothesis at all relating `T` to `1/α`.

Writing `z = x + i y ∈ closedBall z₀ ρ` and `a = 1/α`, the disc conditions give

* `|x| ≤ ρ`,
* `T - ρ ≤ |y|`, hence `ξ + ρ < |y|` by `ξ + 2ρ < T`,

and `α ∈ 𝓕₁` gives `|Im a| ≤ Re a` (`Work.Pert.abs_im_one_div_le_re_one_div`, the sector
`|Im α| < Re α` being inversion stable).  The four gate inequalities of
`Work.Pert.Qm_mem_iff` / `Work.Pert.Qp_mem_iff` are then

* `Qm`, left: `ξ - Re a - |y + Im a| ≤ ξ - Re a - |y| + |Im a| < -Re a - ρ + |Im a| ≤ -ρ ≤ x`,
  using the reverse triangle inequality `|y + Im a| ≥ |y| - |Im a|`,
* `Qm`, right: `x ≤ ρ < |y| - ξ`,
* `Qp`, left: `ξ - |y| < -ρ ≤ x`,
* `Qp`, right: `x ≤ ρ ≤ Re a + ρ - |Im a| < Re a - ξ + |y - Im a|`,
  using `|y - Im a| ≥ |y| - |Im a|`.

Note that `ξ` cancels in the two `abs`-inequalities, which is exactly why no lower bound on `T`
beyond the waist condition `ξ + 2ρ < T` is needed.
-/

namespace Work.Pert.WaistPinned

open Metric Complex

theorem waist_disc_window {ξ T ρ : ℝ} {α z₀ : ℂ} (hF1 : MandelDim.InF1 α)
    (hρ : 0 ≤ ρ) (hT : ξ + 2 * ρ < T) (hz₀re : z₀.re = 0) (hz₀im : |z₀.im| = T) :
    Metric.closedBall z₀ ρ ⊆ Work.Pert.Qm ξ α ∩ Work.Pert.Qp ξ α := by
  intro z hz
  rw [Metric.mem_closedBall, dist_eq_norm] at hz
  -- coordinate bounds for a point of the disc
  have hzre : |z.re| ≤ ρ := by
    have h := Complex.abs_re_le_norm (z - z₀)
    rw [Complex.sub_re, hz₀re, sub_zero] at h
    exact le_trans h hz
  have hzim : T - ρ ≤ |z.im| := by
    have h := Complex.abs_im_le_norm (z - z₀)
    rw [Complex.sub_im] at h
    have h2 : |z₀.im| - |z.im| ≤ |z₀.im - z.im| :=
      abs_sub_abs_le_abs_sub z₀.im z.im
    have h3 : |z₀.im - z.im| = |z.im - z₀.im| := abs_sub_comm _ _
    have h4 : |z.im - z₀.im| ≤ ρ := le_trans h hz
    have h5 : |z₀.im| - ρ ≤ |z.im| := by linarith
    rwa [hz₀im] at h5
  have hxlo : -ρ ≤ z.re := (abs_le.mp hzre).1
  have hxhi : z.re ≤ ρ := (abs_le.mp hzre).2
  have hhigh : ξ + ρ < |z.im| := by linarith
  -- `α ∈ 𝓕₁` gives `|Im (1/α)| ≤ Re (1/α)`
  have hab : |(1 / α).im| ≤ (1 / α).re := Work.Pert.abs_im_one_div_le_re_one_div hF1
  -- the reverse triangle inequalities
  have htriA : |z.im| - |(1 / α).im| ≤ |z.im + (1 / α).im| := by
    have h := abs_sub_abs_le_abs_sub z.im (-(1 / α).im)
    rw [abs_neg, sub_neg_eq_add] at h
    exact h
  have htriB : |z.im| - |(1 / α).im| ≤ |z.im - (1 / α).im| :=
    abs_sub_abs_le_abs_sub z.im (1 / α).im
  -- the four gate inequalities
  have hQm1 : ξ - (1 / α).re - |z.im + (1 / α).im| < z.re := by
    linarith [htriA, hhigh, hab, hxlo]
  have hQm2 : z.re < |z.im| - ξ := by linarith
  have hQp1 : ξ - |z.im| < z.re := by linarith
  have hQp2 : z.re < (1 / α).re - ξ + |z.im - (1 / α).im| := by
    linarith [htriB, hhigh, hab, hxhi]
  rw [Set.mem_inter_iff, Work.Pert.Qm_mem_iff, Work.Pert.Qp_mem_iff]
  exact ⟨⟨hQm1, hQm2⟩, hQp1, hQp2⟩

end Work.Pert.WaistPinned
