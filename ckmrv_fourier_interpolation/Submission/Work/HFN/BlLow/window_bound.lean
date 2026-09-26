import Mathlib
import Submission.Work.Asymptotics.BlLow.Defs
import Submission.Work.Asymptotics.BlLow.ClearTS
import Submission.Work.HFN.BlLow.window_geom
import Submission.Work.HFN.BlLow.window_Mnum_bound
import Submission.Work.HFN.BlLow.window_jDiff_lower

namespace Work.HFN.BlLow
open Work.Asymptotics Work.Asymptotics.BlLow  -- ck-hfn-fix: fork moved out of Work.Asymptotics

noncomputable section

open UpperHalfPlane
open Work.Kernels
open Work.Asymptotics.HalfFunnel Work.HFN.HalfFunnel

/-- **Window (spike) bound of the CKMRV kernel on the low bad-line region.** For `τ` in
`blLowSet` (`{τ ∈ 𝒟 : 2/5 ≤ Im τ ≤ 1/2, |Re τ| > 3/4}`) and `0 < t ≤ lowT = 3` with
`|t - Im τ| ≤ 1/8`, the pole-subtracted kernel
`Kaxis (Kfun ℓ d) τ t - tpole τ t` is bounded by a constant independent of `τ` and `t`, where
`tpole τ t = (tsign τ/2π)/(it - (τ - tsign τ))`.

The proof combines

* the master identity `Kaxis Kfun τ t - tpole τ t
  = -Mnum/((j (it) - j (zpole τ)) ((it : ℂ) - (zpole τ : ℂ)))`
  (`HalfFunnel.Kfun_sub_tpole_eq`), valid off the coincidence `j τ = j (i t)`;
* the three-zeros numerator bound `window_Mnum_bound`
  (`‖Mnum‖ ≤ CM ‖it - zpole τ‖² ‖it - crossedPt τ‖`, the double zero at the translate pole
  `zpole τ = τ - tsign τ` and the simple zero at the crossed orbit point
  `crossedPt τ = tsign τ + S·τ`);
* the two-branch lower bound `window_jDiff_lower`
  (`c ‖it - zpole τ‖ ‖it - crossedPt τ‖ ≤ ‖j (i t) - j (zpole τ)‖`);
* the coincidence classification `coincidence_classification`, which shows that on `blLowSet`
  the contour never meets the pole set (`j (i t) ≠ j (zpole τ)`): a coincidence would force
  either `τ.re = ±1` or `τ` on a tangency arc `|τ ∓ 1/2| = 1/2`, both excluded by `τ ∈ 𝒟`
  together with `|Re τ| ∈ (3/4,1)`.
-/
theorem window_bound (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (τ : UpperHalfPlane) (t : ℝ),
      Work.Asymptotics.BlLow.blLowSet τ → 0 < t →
      t ≤ Work.Asymptotics.HalfFunnel.lowT → |t - τ.im| ≤ 1 / 8 →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
        - Work.Asymptotics.HalfFunnel.tpole τ t‖ ≤ C := by
  obtain ⟨CM, hCM, hM⟩ := window_Mnum_bound ℓ d hd
  obtain ⟨c, hc, hj⟩ := window_jDiff_lower
  refine ⟨CM / c, div_nonneg hCM hc.le, fun τ t hτ ht _htT hw => ?_⟩
  have hτbox : τ ∈ clBox := blLowSet_subset_clBox hτ
  have hwin := blLow_window_bounds hτ ht hw
  -- no coincidence: `j (i t) ≠ j (zpole τ)`
  have hne : Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)
      ≠ Work.Kernels.jInvariantFun (Work.Asymptotics.HalfFunnel.zpole τ) := by
    intro hcoin
    have hcoin' : Work.Kernels.jInvariantFun τ
        = Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) := by
      rw [← Work.HFN.HalfFunnel.zpole_jInvariantFun τ]; exact hcoin.symm
    rcases coincidence_classification hτbox ht hwin.1 hwin.2 hcoin' with h | h
    · -- `it = zpole τ` forces `τ.re = tsign τ`, impossible in `𝒟`
      have hre : τ.re = tsign τ := by
        have h' : ((Work.Kernels.imagAxis t ht : ℍ) : ℂ).re
            = (((Work.Asymptotics.HalfFunnel.zpole τ) : ℍ) : ℂ).re := by rw [h]
        rw [imagAxis_re_zero] at h'
        have h'' : (Work.Asymptotics.HalfFunnel.zpole τ).re = 0 := by
          rw [← UpperHalfPlane.coe_re]; exact h'.symm
        rw [Work.HFN.HalfFunnel.zpole_re] at h''
        linarith
      have hD : τ ∈ Work.Asymptotics.DomainD := hτ.1
      rcases lt_or_ge 0 τ.re with hp | hn
      · have : tsign τ = 1 := (Work.HFN.HalfFunnel.tsign_eq_one_iff τ).mpr hp
        rw [this] at hre; linarith [hD.2.1]
      · have : tsign τ = -1 := (Work.HFN.HalfFunnel.tsign_eq_neg_one_iff τ).mpr hn
        rw [this] at hre; linarith [hD.1]
    · -- `it = crossedPt τ` forces `τ` onto a tangency arc, impossible in `𝒟`
      have hz : (crossedPt τ).re = 0 := by
        have h' : ((Work.Kernels.imagAxis t ht : ℍ) : ℂ).re = ((crossedPt τ : ℍ) : ℂ).re := by rw [h]
        rw [imagAxis_re_zero] at h'
        rw [← UpperHalfPlane.coe_re]; exact h'.symm
      have hsq : ‖(τ : ℂ)‖ ^ 2 = τ.re ^ 2 + τ.im ^ 2 := normSq_coe τ
      have hD : τ ∈ Work.Asymptotics.DomainD := hτ.1
      have hpos : (0 : ℝ) < ‖(τ : ℂ)‖ ^ 2 := by nlinarith [hsq, τ.im_pos, sq_nonneg τ.re]
      rw [crossedPt_re] at hz
      rcases lt_or_ge 0 τ.re with hp | hn
      · rw [(Work.HFN.HalfFunnel.tsign_eq_one_iff τ).mpr hp] at hz
        have h1' : τ.re / ‖(τ : ℂ)‖ ^ 2 = 1 := by linarith [hz]
        rw [div_eq_iff (ne_of_gt hpos)] at h1'
        have h1 : τ.re = ‖(τ : ℂ)‖ ^ 2 := by linarith [h1']
        rw [hsq] at h1
        have harc : ‖(τ : ℂ) - (1 / 2 : ℂ)‖ ^ 2 = (1 / 2 : ℝ) ^ 2 := by
          rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
          have h2 : ((τ : ℂ) - (1 / 2 : ℂ)).re = τ.re - 1 / 2 := by simp
          have h3 : ((τ : ℂ) - (1 / 2 : ℂ)).im = τ.im := by simp
          rw [h2, h3]; nlinarith [h1]
        have := hD.2.2.1
        nlinarith [harc, norm_nonneg ((τ : ℂ) - (1 / 2 : ℂ))]
      · rw [(Work.HFN.HalfFunnel.tsign_eq_neg_one_iff τ).mpr hn] at hz
        have h1' : τ.re / ‖(τ : ℂ)‖ ^ 2 = -1 := by linarith [hz]
        rw [div_eq_iff (ne_of_gt hpos)] at h1'
        have h1 : -τ.re = ‖(τ : ℂ)‖ ^ 2 := by linarith [h1']
        rw [hsq] at h1
        have harc : ‖(τ : ℂ) + (1 / 2 : ℂ)‖ ^ 2 = (1 / 2 : ℝ) ^ 2 := by
          rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
          have h2 : ((τ : ℂ) + (1 / 2 : ℂ)).re = τ.re + 1 / 2 := by simp
          have h3 : ((τ : ℂ) + (1 / 2 : ℂ)).im = τ.im := by simp
          rw [h2, h3]; nlinarith [h1]
        have := hD.2.2.2
        nlinarith [harc, norm_nonneg ((τ : ℂ) + (1 / 2 : ℂ))]
  -- the master identity
  have hK : Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
      = Work.Kernels.Kfun ℓ d τ (Work.Kernels.imagAxis t ht) :=
    Work.HFN.HalfFunnel.Kaxis_eq_Kfun ℓ d ht
  have hkey := Work.HFN.HalfFunnel.Kfun_sub_tpole_eq ℓ d hd ht hne
  rw [hK, hkey, norm_div, norm_neg, norm_mul]
  set a : ℝ := ‖((Work.Kernels.imagAxis t ht : ℍ) : ℂ)
      - ((Work.Asymptotics.HalfFunnel.zpole τ : ℍ) : ℂ)‖ with ha
  set b : ℝ := ‖((Work.Kernels.imagAxis t ht : ℍ) : ℂ) - ((crossedPt τ : ℍ) : ℂ)‖ with hb
  have hane : ((Work.Kernels.imagAxis t ht : ℍ) : ℂ)
      ≠ ((Work.Asymptotics.HalfFunnel.zpole τ : ℍ) : ℂ) := by
    intro hzz
    apply hne
    rw [show Work.Kernels.imagAxis t ht = Work.Asymptotics.HalfFunnel.zpole τ from
      UpperHalfPlane.ext hzz]
  have hapos : 0 < a := norm_pos_iff.mpr (sub_ne_zero.mpr hane)
  have hdne : Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)
      - Work.Kernels.jInvariantFun (Work.Asymptotics.HalfFunnel.zpole τ) ≠ 0 :=
    sub_ne_zero.mpr hne
  have hdpos : 0 < ‖Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)
      - Work.Kernels.jInvariantFun (Work.Asymptotics.HalfFunnel.zpole τ)‖ :=
    norm_pos_iff.mpr hdne
  have hM' := hM τ t ht hτ hw
  have hj' := hj τ t ht hτ hw
  rw [div_le_iff₀ (mul_pos hdpos hapos)]
  calc ‖Work.Asymptotics.HalfFunnel.Mnum ℓ d τ t ht‖ ≤ CM * a ^ 2 * b := hM'
    _ = CM / c * (c * a * b) * a := by rw [div_eq_mul_inv]; field_simp
    _ ≤ CM / c * ‖Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)
            - Work.Kernels.jInvariantFun (Work.Asymptotics.HalfFunnel.zpole τ)‖ * a := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hj' (div_nonneg hCM hc.le)) (le_of_lt hapos)
    _ = CM / c * (‖Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)
            - Work.Kernels.jInvariantFun (Work.Asymptotics.HalfFunnel.zpole τ)‖ * a) := by ring

end

end Work.HFN.BlLow
