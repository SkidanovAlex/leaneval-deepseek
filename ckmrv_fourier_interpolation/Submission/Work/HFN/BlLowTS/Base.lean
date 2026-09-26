import Mathlib
import Submission.Work.Asymptotics.BlLow.Defs
import Submission.Work.HFN.BlLow.AexpTail
import Submission.Work.HFN.BlLow.Phi12
import Submission.Work.HFN.HalfFunnel.lowBadAux
import Submission.Work.HFN.HalfFunnel.lowBad_Tspike_bound

/-!
# Elementary facts about the low bad-line region `blLowSet`

`blLowSet = {τ ∈ 𝒟 : 2/5 ≤ Im τ ≤ 1/2, |Re τ| > 3/4}` is the height range `[2/5,1/2]`
companion of `Work.Asymptotics.HalfFunnel.lowBadSet` (heights `[1/2,2]`).  This file collects
the small geometric / analytic facts about `blLowSet` that the assembly needs, mirroring
`Work.Asymptotics.HalfFunnel.lowBadAux`:

* the translate `τ - tsign τ` is a translate pole of `z ↦ K(τ,z)` whose real part does not
  vanish (`blLow_eps_ne`), so that `tpole` is continuous (`blLow_continuous_tpole`) and bounded
  on the region (`blLow_norm_tpole_le_of_sep`);
* the window `lowWin τ` sits in `(0,∞)` (`blLow_win_bound`), and its complement gives the
  separation `lowRho ≤ |t - Im τ|` (`blLow_off_win_gives_sep`);
* the cusp expansion `Aexp (Gcusp ℓ d)` is bounded on the region at heights `≤ lowT`
  (`blLow_Aexp_le`).
-/

noncomputable section

open MeasureTheory Filter Topology UpperHalfPlane
open scoped Topology ContDiff

namespace Work.HFN.BlLowTS
open Work.Asymptotics  -- ck-hfn-fix: fork moved out of Work.Asymptotics

open Work.Asymptotics.HalfFunnel Work.HFN.HalfFunnel
open Work.Kernels

/-- `|Re τ - tsign τ| = 1 - |Re τ|` when `3/4 ≤ |Re τ| ≤ 1`. -/
lemma tsign_abs_of_abs_re {τ : ℍ} (hre : 3 / 4 ≤ |τ.re|) (hre1 : |τ.re| ≤ 1) :
    |τ.re - tsign τ| = 1 - |τ.re| := by
  obtain ⟨h2, h3⟩ := abs_le.mp hre1
  have hne : τ.re ≠ 0 := by
    intro h; rw [h, abs_zero] at hre; norm_num at hre
  rcases lt_or_gt_of_ne hne with h | h
  · have ha : |τ.re| = -τ.re := abs_of_neg h
    unfold tsign
    rw [if_neg (not_lt.mpr h.le), show τ.re - (-1) = τ.re + 1 by ring,
      abs_of_nonneg (by linarith), ha]
    ring
  · have ha : |τ.re| = τ.re := abs_of_pos h
    unfold tsign
    rw [if_pos h, show τ.re - 1 = -(1 - τ.re) by ring, abs_neg,
      abs_of_nonneg (by linarith), ha]

/-- `|Re τ - tsign τ| = 1 - |Re τ|` on `blLowSet`. -/
lemma blLow_tsign_abs {τ : ℍ} (hτ : Work.Asymptotics.BlLow.blLowSet τ) :
    |τ.re - tsign τ| = 1 - |τ.re| := by
  obtain ⟨hr1, hr2⟩ := Work.Asymptotics.BlLow.blLowSet_re_abs_bounds hτ
  exact tsign_abs_of_abs_re (le_of_lt hr1) (le_of_lt hr2)

/-- On `blLowSet` the translate pole `z = τ - tsign τ` misses the imaginary axis, i.e.
`Re τ ≠ tsign τ`. -/
lemma blLow_eps_ne {τ : ℍ} (hτ : Work.Asymptotics.BlLow.blLowSet τ) :
    τ.re - tsign τ ≠ 0 := by
  obtain ⟨hr1, hr2⟩ := Work.Asymptotics.BlLow.blLowSet_re_abs_bounds hτ
  rw [abs_lt] at hr2
  intro h
  unfold tsign at h
  rcases lt_or_ge 0 τ.re with hpos | hneg
  · rw [if_pos hpos] at h; linarith [hr2.2]
  · rw [if_neg (not_lt.mpr hneg)] at h; linarith [hr2.1]

/-- On `blLowSet` the translate pole `z = τ - tsign τ` has `|Re| = 1 - |Re τ| ≤ 1/4`. -/
lemma blLow_zpole_re_abs {τ : ℍ} (hτ : Work.Asymptotics.BlLow.blLowSet τ) :
    |(τ.re - tsign τ)| ≤ 1 / 4 := by
  rw [blLow_tsign_abs hτ]
  obtain ⟨hr1, _⟩ := Work.Asymptotics.BlLow.blLowSet_re_abs_bounds hτ
  linarith

/-- `‖tpole τ t‖ ≤ 1/(2π) / |τ.re - tsign τ|` on `blLowSet` (a bound valid on the whole window). -/
lemma blLow_norm_tpole_le {τ : ℍ} (hτ : Work.Asymptotics.BlLow.blLowSet τ) (t : ℝ) :
    ‖tpole τ t‖ ≤ 1 / (2 * Real.pi * |τ.re - tsign τ|) := by
  have heps := blLow_eps_ne hτ
  have hnum : ‖(tsign τ : ℂ)‖ = 1 := by unfold tsign; split <;> norm_num
  have hpi : ‖(2:ℂ) * (Real.pi:ℂ)‖ = 2 * Real.pi := by
    rw [norm_mul, Complex.norm_ofNat, Complex.norm_of_nonneg Real.pi_pos.le]
  have hge : |τ.re - tsign τ| ≤ ‖((t:ℂ) * Complex.I - ((τ:ℂ) - (tsign τ : ℂ)))‖ := by
    have hre : (((t:ℂ) * Complex.I - ((τ:ℂ) - (tsign τ : ℂ)))).re = tsign τ - τ.re := by
      simp only [Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im, mul_one,
        mul_zero, zero_sub, sub_zero, Complex.ofReal_re, Complex.intCast_re, Complex.ofReal_im,
        Complex.intCast_im, UpperHalfPlane.coe_re]
      ring
    have h1 := Complex.abs_re_le_norm ((t:ℂ) * Complex.I - ((τ:ℂ) - (tsign τ : ℂ)))
    rw [hre, abs_sub_comm] at h1
    exact h1
  have hpos : 0 < |τ.re - tsign τ| := abs_pos.mpr heps
  rw [tpole, norm_div, norm_div, hnum, hpi]
  have h1 : (1 / (2 * Real.pi)) / ‖((t:ℂ) * Complex.I - ((τ:ℂ) - (tsign τ : ℂ)))‖
      ≤ (1 / (2 * Real.pi)) / |τ.re - tsign τ| :=
    div_le_div_of_nonneg_left (by positivity) hpos hge
  have h2 : (1 / (2 * Real.pi)) / |τ.re - tsign τ| = 1 / (2 * Real.pi * |τ.re - tsign τ|) := by
    rw [div_div]
  linarith [h1, h2.le, h2.ge]

/-- The translate pole `tpole τ ·` is continuous for `τ ∈ blLowSet`. -/
lemma blLow_continuous_tpole {τ : ℍ} (hτ : Work.Asymptotics.BlLow.blLowSet τ) :
    Continuous (fun t : ℝ => tpole τ t) := by
  have h1 : Continuous (fun t : ℝ => (t:ℂ) * Complex.I - ((τ:ℂ) - (tsign τ : ℂ))) :=
    (Complex.continuous_ofReal.mul continuous_const).sub continuous_const
  have hne : ∀ t : ℝ, (t:ℂ) * Complex.I - ((τ:ℂ) - (tsign τ : ℂ)) ≠ 0 := by
    intro t h
    have h2 : ((t:ℂ) * Complex.I - ((τ:ℂ) - (tsign τ : ℂ))).re = 0 := by rw [h]; simp
    rw [show ((t:ℂ) * Complex.I - ((τ:ℂ) - (tsign τ : ℂ))).re = tsign τ - τ.re from by
      simp only [Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im, mul_one, mul_zero,
        zero_sub, sub_zero, Complex.ofReal_re, Complex.intCast_re, Complex.ofReal_im,
        Complex.intCast_im, UpperHalfPlane.coe_re]
      ring] at h2
    exact blLow_eps_ne hτ (by linarith [h2])
  exact continuous_const.div h1 hne

/-- `‖tpole τ t‖ ≤ 1/(2π lowRho)` as soon as the contour point keeps distance `≥ lowRho` from
the pole height `Im τ` (the pole `z = τ - tsign τ` has imaginary part `Im τ`, so the distance from
`i t` to the pole is at least `|t - Im τ|`). -/
lemma blLow_norm_tpole_le_of_sep {τ : ℍ} (hτ : Work.Asymptotics.BlLow.blLowSet τ) {t : ℝ}
    (h : lowRho ≤ |t - τ.im|) : ‖tpole τ t‖ ≤ 1 / (2 * Real.pi * lowRho) := by
  have hρ : 0 < lowRho := Work.HFN.BlLow.lowRho_pos
  have hnum : ‖(tsign τ : ℂ) / (2 * (Real.pi : ℂ))‖ = 1 / (2 * Real.pi) := by
    rw [norm_div]
    have h1 : ‖(tsign τ : ℂ)‖ = 1 := by unfold tsign; split <;> norm_num
    have h2 : ‖(2 : ℂ) * (Real.pi : ℂ)‖ = 2 * Real.pi := by
      rw [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos]
    rw [h1, h2]
  have hden : |t - τ.im| ≤ ‖((t : ℂ) * Complex.I - ((τ : ℂ) - (tsign τ : ℂ)))‖ := by
    have h1 := Complex.abs_im_le_norm ((t : ℂ) * Complex.I - ((τ : ℂ) - (tsign τ : ℂ)))
    have h2 : (((t : ℂ) * Complex.I - ((τ : ℂ) - (tsign τ : ℂ)))).im = t - τ.im := by
      simp only [Complex.sub_im, Complex.mul_im, Complex.I_re, Complex.I_im, mul_one, mul_zero,
        Complex.ofReal_re, Complex.ofReal_im, sub_zero, UpperHalfPlane.coe_im]
      ring
    rwa [h2] at h1
  have hDpos : 0 < ‖((t : ℂ) * Complex.I - ((τ : ℂ) - (tsign τ : ℂ)))‖ :=
    lt_of_lt_of_le hρ (le_trans h hden)
  rw [tpole, norm_div, hnum]
  have h1 : (1 / (2 * Real.pi)) / ‖((t : ℂ) * Complex.I - ((τ : ℂ) - (tsign τ : ℂ)))‖
      ≤ (1 / (2 * Real.pi)) / lowRho :=
    div_le_div_of_nonneg_left (by positivity) hρ (le_trans h hden)
  have h2 : (1 / (2 * Real.pi)) / lowRho = 1 / (2 * Real.pi * lowRho) := by
    rw [div_div]
  linarith [h1, h2.le, h2.ge]

/-- The window `lowWin τ` is contained in `(3/8, 5/8)` for `τ ∈ blLowSet`. -/
lemma blLow_win_bound {τ : ℍ} (hτ : Work.Asymptotics.BlLow.blLowSet τ) {t : ℝ}
    (ht : t ∈ lowWin τ) : 11 / 40 < t ∧ t < 5 / 8 := by
  rw [lowWin, Set.mem_Ioo] at ht
  obtain ⟨him1, him2⟩ := Work.Asymptotics.BlLow.blLowSet_im_bounds hτ
  have hρ : lowRho = 1 / 8 := rfl
  constructor
  · have h1 : τ.im - lowRho < t := ht.1
    rw [hρ] at h1; linarith
  · have h2 : t < τ.im + lowRho := ht.2
    rw [hρ] at h2; linarith

/-- `lowWin τ ⊆ (0,∞)` on `blLowSet`. -/
lemma blLow_win_subset_Ioi {τ : ℍ} (hτ : Work.Asymptotics.BlLow.blLowSet τ) :
    lowWin τ ⊆ Set.Ioi (0 : ℝ) :=
  fun _ ht => lt_trans (by norm_num) (blLow_win_bound hτ ht).1

/-- `t ∉ lowWin τ` gives the separation `lowRho ≤ |t - Im τ|`. -/
lemma blLow_off_win_gives_sep {τ : ℍ} {t : ℝ} (ht : t ∉ lowWin τ) :
    lowRho ≤ |t - τ.im| := by
  have hρ : 0 < lowRho := Work.HFN.BlLow.lowRho_pos
  rcases Work.HFN.BlLow.not_mem_lowWin_iff.mp ht with h | h
  · rw [abs_of_nonpos (by linarith)]; linarith
  · rw [abs_of_nonneg (by linarith)]; linarith


/-- The cusp expansion `Aexp (Gcusp ℓ d)` is bounded on `blLowSet` for heights in `[1,lowT]`. -/
lemma blLow_Aexp_le (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ CB : ℝ, 0 ≤ CB ∧ ∀ (τ : ℍ), Work.Asymptotics.BlLow.blLowSet τ → ∀ t : ℝ,
      1 ≤ t → t ≤ lowT → ‖Aexp (Gcusp ℓ d) τ t‖ ≤ CB := by
  obtain ⟨CB, hCB, hb⟩ := Work.HFN.BlLow.Aexp_bound_on ℓ d hd lowT
  refine ⟨CB, hCB, fun τ hτ t ht1 htT => ?_⟩
  exact hb τ hτ t (by rw [abs_of_nonneg (by linarith [ht1])]; exact htT)

end Work.HFN.BlLowTS
