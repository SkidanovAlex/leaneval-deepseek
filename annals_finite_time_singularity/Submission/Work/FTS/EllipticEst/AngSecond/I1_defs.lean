import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Submission.Work.FTS.EllipticEst.AngSecond.Defs
import Submission.Work.FTS.EllipticEst.hardy_shift_two_same_weight
import Submission.Work.FTS.EllipticEst.interpol_trunc_defs
import Submission.Work.FTS.H2.CS1D
import Submission.Work.Spaces.mixed_comm
import Submission.Work.Spaces.CurrySmooth
import Submission.Work.FTS.EllipticEst.zHardyDefs
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.Spaces.cs_integral
import Submission.Work.FTS.H2.SliceFacts

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Topology Real ContDiff

namespace Work.FTS.EllipticEst.AngSecond

/-! ## Integrability on the half-line of a compactly supported function -/

/-- A function continuous on `[a,b]` (`0 < a ≤ b`) and vanishing outside `[a,b]` is integrable
on `(0,∞)`; its support is the compact subset `[a,b] ⊆ (0,∞)`. -/
private theorem integrableOn_Ioi_of_Icc_support {f : ℝ → ℝ} {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) (hcont : ContinuousOn f (Set.Icc a b))
    (hzero : ∀ z, z ∉ Set.Icc a b → f z = 0) :
    MeasureTheory.IntegrableOn f (Set.Ioi 0) := by
  have hInd : MeasureTheory.Integrable ((Set.Icc a b).indicator f) volume :=
    (MeasureTheory.integrable_indicator_iff measurableSet_Icc).mpr
      (hcont.integrableOn_compact isCompact_Icc)
  have hfun : f = (Set.Icc a b).indicator f := by
    funext z
    by_cases hz : z ∈ Set.Icc a b
    · rw [Set.indicator_of_mem hz]
    · rw [Set.indicator_of_notMem hz, hzero z hz]
  rw [hfun]
  refine ⟨hInd.aestronglyMeasurable.mono_measure Measure.restrict_le_self, ?_⟩
  calc ∫⁻ z, ‖(Set.Icc a b).indicator f z‖₊ ∂(volume.restrict (Set.Ioi 0))
      ≤ ∫⁻ z, ‖(Set.Icc a b).indicator f z‖₊ ∂(volume : MeasureTheory.Measure ℝ) :=
        lintegral_mono' Measure.restrict_le_self le_rfl
    _ < ⊤ := hInd.hasFiniteIntegral

/-! ## The vocabulary of the `I₁` computation -/

/-- `G(Ψ) = z · ∂_zΨ`: the first-order radial term. -/
noncomputable def G (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => z * Work.Spaces.pz Ψ z θ

/-- `Φ(Ψ) = ∂_θθΨ`: the angular term paired with `I₁`. -/
noncomputable def Phi (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := Work.Spaces.pthIter 2 Ψ

/-- `H(Ψ) = z · ∂_z(∂_θθΨ) = ∂_θθ(z ∂_zΨ)`: the angular derivative of `G`, which the angular
integration by parts turns into `(∂_θ G)²`. -/
noncomputable def H (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ

/-- `cw z = 2(z-1)/(1+z) = 2 - 4/(1+z)`: the weight of the drift term produced by the radial
integration by parts (`z (w²)'/w² = -4/(1+z)`). -/
noncomputable def cw (z : ℝ) : ℝ := 2 * (z - 1) / (1 + z)

/-! ## Part 0: the derivative of the weight `w²` -/

theorem hasDerivAt_w2 {z : ℝ} (hz : 0 < z) :
    HasDerivAt w2 (2 * Work.Spaces.w z * Work.FTS.EllipticEst.zDw z) z := by
  have h := (Work.FTS.EllipticEst.hasDerivAt_w hz).pow 2
  have h2 : (2 : ℝ) * Work.Spaces.w z ^ (2 - 1) * Work.FTS.EllipticEst.zDw z
      = 2 * Work.Spaces.w z * Work.FTS.EllipticEst.zDw z := by norm_num
  exact h.congr_deriv h2

theorem deriv_w2_eq {z : ℝ} (hz : 0 < z) :
    deriv w2 z = 2 * Work.Spaces.w z * Work.FTS.EllipticEst.zDw z :=
  (hasDerivAt_w2 hz).deriv

theorem z_mul_deriv_w2 {z : ℝ} (hz : 0 < z) :
    z * deriv w2 z = -4 * w2 z / (1 + z) := by
  rw [deriv_w2_eq hz]
  have hz0 : z ≠ 0 := ne_of_gt hz
  have h1 : (1 : ℝ) + z ≠ 0 := by linarith
  simp only [Work.FTS.EllipticEst.zDw, w2, Work.Spaces.w]
  field_simp
  ring

theorem deriv_w2_eq' {z : ℝ} (hz : 0 < z) :
    deriv w2 z = -4 * w2 z / ((1 + z) * z) := by
  have hw := z_mul_deriv_w2 hz
  have hz0 : z ≠ 0 := ne_of_gt hz
  have h1 : (1 : ℝ) + z ≠ 0 := by linarith
  field_simp at hw ⊢
  linarith [hw]

/-! ## Part 1: the pointwise expansion of the `z`-derivative of `z² φ χ w²` -/

theorem hasDerivAt_z2_phi_chi_w2 (n : ℕ) (Ψ : ℝ → ℝ → ℝ) (hΨ : Work.Spaces.SmoothNbhd Ψ)
    {z : ℝ} (hz : 0 < z) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    HasDerivAt (fun z' => z' ^ 2 * Work.Spaces.pthIter 2 Ψ z' θ * cut n z' * w2 z')
      (2 * z * Work.Spaces.pthIter 2 Ψ z θ * cut n z * w2 z
        + z ^ 2 * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ * cut n z * w2 z
        + z ^ 2 * Work.Spaces.pthIter 2 Ψ z θ * deriv (cut n) z * w2 z
        + z ^ 2 * Work.Spaces.pthIter 2 Ψ z θ * cut n z * deriv w2 z) z := by
  have hz1 : z ∈ Set.Ioi (-1 : ℝ) := by simp only [Set.mem_Ioi]; linarith
  have hsm2 : Work.Spaces.SmoothNbhd (Work.Spaces.pthIter 2 Ψ) := hΨ.pth.pth
  have h1 : HasDerivAt (fun z' : ℝ => z' ^ 2) (2 * z) z := by
    have h := (hasDerivAt_id z).pow 2
    have h2 : ((2 : ℕ) : ℝ) * z ^ (2 - 1) * (1 : ℝ) = 2 * z := by norm_num
    exact h.congr_deriv h2
  have h2 : HasDerivAt (fun z' : ℝ => Work.Spaces.pthIter 2 Ψ z' θ)
      (Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ) z :=
    Work.Spaces.hardyZ_hasDerivAt_slice (Work.Spaces.pthIter 2 Ψ) hsm2 hθ hz1
  have h3 : HasDerivAt (fun z' : ℝ => cut n z') (deriv (cut n) z) z :=
    ((Work.FTS.EllipticEst.cut_contDiff n).differentiable (by simp)).differentiableAt.hasDerivAt
  have h4 : HasDerivAt w2 (deriv w2 z) z := (hasDerivAt_w2 hz).differentiableAt.hasDerivAt
  have htot := ((h1.mul h2).mul h3).mul h4
  refine htot.congr_deriv ?_
  simp only [Pi.mul_apply]
  ring

theorem pz_mul_deriv_expansion (n : ℕ) (Ψ : ℝ → ℝ → ℝ) (hΨ : Work.Spaces.SmoothNbhd Ψ)
    {z : ℝ} (hz : 0 < z) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.pz Ψ z θ
        * deriv (fun z' => z' ^ 2 * Work.Spaces.pthIter 2 Ψ z' θ * cut n z' * w2 z') z
      = cut n z * w2 z
          * (2 * (z * Work.Spaces.pz Ψ z θ) * (Work.Spaces.pthIter 2 Ψ z θ)
              + (z * Work.Spaces.pz Ψ z θ) * (z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ)
              - 4 * (z * Work.Spaces.pz Ψ z θ) * (Work.Spaces.pthIter 2 Ψ z θ) / (1 + z))
        + w2 z * ((z * Work.Spaces.pz Ψ z θ) * (Work.Spaces.pthIter 2 Ψ z θ))
            * (z * deriv (cut n) z) := by
  rw [(hasDerivAt_z2_phi_chi_w2 n Ψ hΨ hz hθ).deriv]
  rw [deriv_w2_eq' hz]
  have hz0 : z ≠ 0 := ne_of_gt hz
  have h1z : (1 : ℝ) + z ≠ 0 := by linarith
  field_simp
  ring

/-! ## Part 2: the per-`θ` integration by parts -/

/-- The explicit `z`-derivative of `z' ↦ z'² ∂_θθΨ(z',θ) · χ(z') · w²(z')` (raw form). -/
noncomputable def Dv (n : ℕ) (Ψ : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  2 * z * Work.Spaces.pthIter 2 Ψ z θ * cut n z * w2 z
    + z ^ 2 * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ * cut n z * w2 z
    + z ^ 2 * Work.Spaces.pthIter 2 Ψ z θ * deriv (cut n) z * w2 z
    + z ^ 2 * Work.Spaces.pthIter 2 Ψ z θ * cut n z * deriv w2 z

theorem hasDerivAt_v_eq_Dv (n : ℕ) (Ψ : ℝ → ℝ → ℝ) (hΨ : Work.Spaces.SmoothNbhd Ψ)
    {z : ℝ} (hz : 0 < z) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    HasDerivAt (fun z' => z' ^ 2 * Work.Spaces.pthIter 2 Ψ z' θ * cut n z' * w2 z')
      (Dv n Ψ z θ) z :=
  hasDerivAt_z2_phi_chi_w2 n Ψ hΨ hz hθ

/-- `z * (cut n)' z = 0` far away from the transition regions. -/
theorem deriv_cut_eq_zero_of_lt (n : ℕ) {z : ℝ} (hz : z < 1 / (n + 1 : ℝ)) :
    deriv (cut n) z = 0 := by
  have hEq : (fun y : ℝ => cut n y) =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
    filter_upwards [isOpen_Iio.mem_nhds hz] with y hy
    exact Work.FTS.EllipticEst.cut_apply_zero_of_le n hy.le
  have := hEq.deriv_eq
  simpa using this

theorem deriv_cut_eq_zero_of_gt (n : ℕ) {z : ℝ} (hz : 3 * (n + 1 : ℝ) < z) :
    deriv (cut n) z = 0 := by
  have hEq : (fun y : ℝ => cut n y) =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with y hy
    exact Work.FTS.EllipticEst.cut_apply_zero_of_ge n hy.le
  have := hEq.deriv_eq
  simpa using this

theorem Dv_eq_zero_of_notMem (n : ℕ) (Ψ : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hz : z ∉ Set.Icc (1 / (2 * (n + 1 : ℝ))) (4 * (n + 1 : ℝ))) : Dv n Ψ z θ = 0 := by
  have hn : (0 : ℝ) < (n + 1 : ℝ) := by positivity
  have hhalf : 1 / (2 * (n + 1 : ℝ)) ≤ 1 / (n + 1 : ℝ) :=
    one_div_le_one_div_of_le hn (by linarith)
  simp only [Set.mem_Icc, not_and_or, not_le] at hz
  rcases hz with hzlt | hzgt
  · have h1 : z ≤ 1 / (n + 1 : ℝ) := by linarith
    have hzlt' : z < 1 / (n + 1 : ℝ) := by linarith
    have hχ : cut n z = 0 := Work.FTS.EllipticEst.cut_apply_zero_of_le n h1
    have hχ' : deriv (cut n) z = 0 := deriv_cut_eq_zero_of_lt n hzlt'
    simp [Dv, hχ, hχ']
  · have h1 : 3 * (n + 1 : ℝ) ≤ z := by linarith
    have hχ : cut n z = 0 := Work.FTS.EllipticEst.cut_apply_zero_of_ge n h1
    have hχ' : deriv (cut n) z = 0 := deriv_cut_eq_zero_of_gt n (by linarith)
    simp [Dv, hχ, hχ']

section Continuity

open Work.Spaces in
theorem smoothNbhd_pthIter (Ψ : ℝ → ℝ → ℝ) (hΨ : Work.Spaces.SmoothNbhd Ψ) :
    ∀ k : ℕ, Work.Spaces.SmoothNbhd (Work.Spaces.pthIter k Ψ)
  | 0 => by simpa only [Work.Spaces.pthIter_zero] using hΨ
  | k + 1 => by
      have h := (smoothNbhd_pthIter Ψ hΨ k).pth
      simpa only [Work.Spaces.pthIter_succ] using h

theorem continuous_deriv_cut (n : ℕ) : Continuous (deriv (Work.FTS.EllipticEst.cut n)) := by
  have hcut : ContDiff ℝ ∞ (Work.FTS.EllipticEst.cut n) := Work.FTS.EllipticEst.cut_contDiff n
  exact ((contDiff_infty_iff_deriv.mp hcut).2).continuous

end Continuity

section Helpers

theorem continuousOn_w' {a b : ℝ} (ha : 0 < a) :
    ContinuousOn Work.Spaces.w (Set.Icc a b) := by
  unfold Work.Spaces.w
  have hnum : ContinuousOn (fun z : ℝ => (1 + z) ^ 2) (Set.Icc a b) :=
    ((continuous_const.add continuous_id).pow 2).continuousOn
  have hden : ContinuousOn (fun z : ℝ => z ^ 2) (Set.Icc a b) :=
    (continuous_id.pow 2).continuousOn
  exact hnum.div hden (fun z hz => by
    have hz0 : (0 : ℝ) < z := lt_of_lt_of_le ha hz.1
    exact pow_ne_zero 2 (ne_of_gt hz0))

theorem continuousOn_zDw' {a b : ℝ} (ha : 0 < a) :
    ContinuousOn Work.FTS.EllipticEst.zDw (Set.Icc a b) := by
  unfold Work.FTS.EllipticEst.zDw
  have h1 : ContinuousOn (fun z : ℝ => 2 * (1 + z) / z ^ 2) (Set.Icc a b) := by
    refine ContinuousOn.div ?_ ?_ ?_
    · exact (continuous_const.mul (continuous_const.add continuous_id)).continuousOn
    · exact (continuous_id.pow 2).continuousOn
    · intro z hz
      have hz0 : (0 : ℝ) < z := lt_of_lt_of_le ha hz.1
      exact pow_ne_zero 2 (ne_of_gt hz0)
  have h2 : ContinuousOn (fun z : ℝ => 2 * (1 + z) ^ 2 / z ^ 3) (Set.Icc a b) := by
    refine ContinuousOn.div ?_ ?_ ?_
    · exact (continuous_const.mul ((continuous_const.add continuous_id).pow 2)).continuousOn
    · exact (continuous_id.pow 3).continuousOn
    · intro z hz
      have hz0 : (0 : ℝ) < z := lt_of_lt_of_le ha hz.1
      exact pow_ne_zero 3 (ne_of_gt hz0)
  exact h1.sub h2

theorem continuousOn_w2' {a b : ℝ} (ha : 0 < a) : ContinuousOn w2 (Set.Icc a b) := by
  unfold w2
  exact (continuousOn_w' (a := a) (b := b) ha).pow 2

theorem continuousOn_deriv_w2' {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun z => deriv w2 z) (Set.Icc a b) := by
  have h4 : ContinuousOn (fun _ : ℝ => (-4 : ℝ)) (Set.Icc a b) := continuousOn_const
  have hden : ContinuousOn (fun z : ℝ => (1 + z) * z) (Set.Icc a b) :=
    (((continuous_const.add continuous_id).mul continuous_id)).continuousOn
  have h : ContinuousOn (fun z : ℝ => -4 * w2 z / ((1 + z) * z)) (Set.Icc a b) :=
    h4.mul (continuousOn_w2' (a := a) (b := b) ha) |>.div hden (fun z hz => by
      have hz0 : (0 : ℝ) < z := lt_of_lt_of_le ha hz.1
      have h1 : (1 : ℝ) + z ≠ 0 := by linarith
      exact mul_ne_zero h1 (ne_of_gt hz0))
  have heq : Set.EqOn (fun z => deriv w2 z) (fun z : ℝ => -4 * w2 z / ((1 + z) * z))
      (Set.Icc a b) := fun z hz => deriv_w2_eq' (lt_of_lt_of_le ha hz.1)
  exact (continuousOn_congr heq).mpr h

theorem continuousOn_slice_pthIter' (Ψ : ℝ → ℝ → ℝ) (hΨ : Work.Spaces.SmoothNbhd Ψ) (k : ℕ)
    {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun z => Work.Spaces.pthIter k Ψ z θ) (Set.Icc a b) := by
  have hsub : Set.Icc a b ⊆ Set.Ioi (-1 : ℝ) := by
    intro z hz
    have hz0 : (0 : ℝ) < z := lt_of_lt_of_le ha hz.1
    exact show (-1 : ℝ) < z by linarith
  exact ((Work.Spaces.hardyZ_contDiffOn_slice (Work.Spaces.pthIter k Ψ)
    (smoothNbhd_pthIter Ψ hΨ k) hθ).continuousOn).mono hsub

theorem continuousOn_slice_pz_pthIter' (Ψ : ℝ → ℝ → ℝ) (hΨ : Work.Spaces.SmoothNbhd Ψ) (k : ℕ)
    {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun z => Work.Spaces.pz (Work.Spaces.pthIter k Ψ) z θ) (Set.Icc a b) := by
  have hsub : Set.Icc a b ⊆ Set.Ioi (-1 : ℝ) := by
    intro z hz
    have hz0 : (0 : ℝ) < z := lt_of_lt_of_le ha hz.1
    exact show (-1 : ℝ) < z by linarith
  exact ((Work.Spaces.hardyZ_continuousOn_pz_slice (Work.Spaces.pthIter k Ψ)
    (smoothNbhd_pthIter Ψ hΨ k) hθ)).mono hsub

theorem continuousOn_slice_pzIter' (Ψ : ℝ → ℝ → ℝ) (hΨ : Work.Spaces.SmoothNbhd Ψ) (k : ℕ)
    {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun z => Work.Spaces.pzIter k Ψ z θ) (Set.Icc a b) := by
  have hsub : Set.Icc a b ⊆ Set.Ioi (-1 : ℝ) := by
    intro z hz
    have hz0 : (0 : ℝ) < z := lt_of_lt_of_le ha hz.1
    exact show (-1 : ℝ) < z by linarith
  exact ((Work.Spaces.hardyZ_contDiffOn_slice (Work.Spaces.pzIter k Ψ)
    (Work.Spaces.smoothNbhd_pzIter hΨ k) hθ).continuousOn).mono hsub

end Helpers

section IBP

theorem continuousOn_slice_pz' (Ψ : ℝ → ℝ → ℝ) (hΨ : Work.Spaces.SmoothNbhd Ψ)
    {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun z => Work.Spaces.pz Ψ z θ) (Set.Icc a b) :=
  continuousOn_slice_pzIter' Ψ hΨ 1 hθ ha

theorem slice_ibp_halfline (n : ℕ) (Ψ : ℝ → ℝ → ℝ) (hΨ : Work.Spaces.SmoothNbhd Ψ)
    {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (∫ z in Set.Ioi (0 : ℝ), Work.Spaces.pz Ψ z θ * Dv n Ψ z θ)
      = -∫ z in Set.Ioi (0 : ℝ),
          Work.Spaces.pzIter 2 Ψ z θ * (z ^ 2 * Work.Spaces.pthIter 2 Ψ z θ * cut n z * w2 z) := by
  have ha : (0 : ℝ) < 1 / (2 * (n + 1 : ℝ)) := by positivity
  have hab : 1 / (2 * (n + 1 : ℝ)) ≤ 4 * (n + 1 : ℝ) := by
    have h1 : 1 / (2 * (n + 1 : ℝ)) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith
    have h2 : (1 : ℝ) ≤ 4 * (n + 1 : ℝ) := by
      have : (0 : ℝ) < (n + 1 : ℝ) := by positivity
      linarith
    linarith
  have hu : ∀ x ∈ Set.Ioi (0 : ℝ), HasDerivAt (fun z => Work.Spaces.pz Ψ z θ)
      (Work.Spaces.pzIter 2 Ψ x θ) x := by
    intro x hx
    have hx1 : x ∈ Set.Ioi (-1 : ℝ) := by
      simp only [Set.mem_Ioi] at hx ⊢; linarith
    have h := Work.Spaces.hardyZ_hasDerivAt_slice (Work.Spaces.pz Ψ)
      (Work.Spaces.smoothNbhd_pzIter hΨ 1) hθ hx1
    simpa only [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero] using h
  have hv : ∀ x ∈ Set.Ioi (0 : ℝ), HasDerivAt
      (fun z => z ^ 2 * Work.Spaces.pthIter 2 Ψ z θ * cut n z * w2 z) (Dv n Ψ x θ) x :=
    fun x hx => hasDerivAt_v_eq_Dv n Ψ hΨ hx hθ
  have hDv : ContinuousOn (fun z => Dv n Ψ z θ) (Set.Icc (1 / (2 * (n + 1 : ℝ))) (4 * (n + 1 : ℝ))) := by
    have hφ : ContinuousOn (fun z => Work.Spaces.pthIter 2 Ψ z θ)
        (Set.Icc (1 / (2 * (n + 1 : ℝ))) (4 * (n + 1 : ℝ))) :=
      continuousOn_slice_pthIter' Ψ hΨ 2 hθ ha
    have hφ' : ContinuousOn (fun z => Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ)
        (Set.Icc (1 / (2 * (n + 1 : ℝ))) (4 * (n + 1 : ℝ))) :=
      continuousOn_slice_pz_pthIter' Ψ hΨ 2 hθ ha
    have hχ : ContinuousOn (fun z => cut n z) (Set.Icc (1 / (2 * (n + 1 : ℝ))) (4 * (n + 1 : ℝ))) :=
      (Work.FTS.EllipticEst.cut_contDiff n).continuous.continuousOn
    have hχ' : ContinuousOn (fun z => deriv (cut n) z)
        (Set.Icc (1 / (2 * (n + 1 : ℝ))) (4 * (n + 1 : ℝ))) :=
      (continuous_deriv_cut n).continuousOn
    have hw : ContinuousOn (fun z => w2 z) (Set.Icc (1 / (2 * (n + 1 : ℝ))) (4 * (n + 1 : ℝ))) :=
      continuousOn_w2' ha
    have hw' : ContinuousOn (fun z => deriv w2 z)
        (Set.Icc (1 / (2 * (n + 1 : ℝ))) (4 * (n + 1 : ℝ))) :=
      continuousOn_deriv_w2' ha
    simp only [Dv]
    fun_prop
  have hI1 : MeasureTheory.IntegrableOn (fun z => Work.Spaces.pz Ψ z θ * Dv n Ψ z θ) (Set.Ioi 0) := by
    refine integrableOn_Ioi_of_Icc_support (f := fun z => Work.Spaces.pz Ψ z θ * Dv n Ψ z θ) ha hab ?_ ?_
    · exact (continuousOn_slice_pz' Ψ hΨ hθ ha).mul hDv
    · intro z hz
      rw [Dv_eq_zero_of_notMem n Ψ hz, mul_zero]
  have hI2 : MeasureTheory.IntegrableOn (fun z => Work.Spaces.pzIter 2 Ψ z θ
      * (z ^ 2 * Work.Spaces.pthIter 2 Ψ z θ * cut n z * w2 z)) (Set.Ioi 0) := by
    refine integrableOn_Ioi_of_Icc_support
      (f := fun z => Work.Spaces.pzIter 2 Ψ z θ * (z ^ 2 * Work.Spaces.pthIter 2 Ψ z θ * cut n z * w2 z))
      ha hab ?_ ?_
    · have hz2χφ : ContinuousOn
          (fun z : ℝ => z ^ 2 * Work.Spaces.pthIter 2 Ψ z θ * cut n z * w2 z)
          (Set.Icc (1 / (2 * (n + 1 : ℝ))) (4 * (n + 1 : ℝ))) := by
        have h1 : ContinuousOn (fun z : ℝ => z ^ 2)
            (Set.Icc (1 / (2 * (n + 1 : ℝ))) (4 * (n + 1 : ℝ))) :=
          (continuous_id.pow 2).continuousOn
        have h2 : ContinuousOn (fun z : ℝ => Work.Spaces.pthIter 2 Ψ z θ)
            (Set.Icc (1 / (2 * (n + 1 : ℝ))) (4 * (n + 1 : ℝ))) :=
          continuousOn_slice_pthIter' Ψ hΨ 2 hθ ha
        have h3 : ContinuousOn (fun z : ℝ => cut n z)
            (Set.Icc (1 / (2 * (n + 1 : ℝ))) (4 * (n + 1 : ℝ))) :=
          (Work.FTS.EllipticEst.cut_contDiff n).continuous.continuousOn
        have h4 : ContinuousOn (fun z : ℝ => w2 z)
            (Set.Icc (1 / (2 * (n + 1 : ℝ))) (4 * (n + 1 : ℝ))) := continuousOn_w2' ha
        exact ((h1.mul h2).mul h3).mul h4
      exact (continuousOn_slice_pzIter' Ψ hΨ 2 hθ ha).mul hz2χφ
    · intro z hz
      have hn : (0 : ℝ) < (n + 1 : ℝ) := by positivity
      have ha' : 1 / (2 * (n + 1 : ℝ)) ≤ 1 / (n + 1 : ℝ) :=
        one_div_le_one_div_of_le hn (by linarith)
      simp only [Set.mem_Icc, not_and_or, not_le] at hz
      rcases hz with hzlt | hzgt
      · have h1 : z ≤ 1 / (n + 1 : ℝ) := by linarith
        simp [Work.FTS.EllipticEst.cut_apply_zero_of_le n h1]
      · have h1 : 3 * (n + 1 : ℝ) ≤ z := by linarith
        simp [Work.FTS.EllipticEst.cut_apply_zero_of_ge n h1]
  have hmem0 : ∀ᶠ z in 𝓝[>] (0 : ℝ), z < 1 / (n + 1 : ℝ) := by
    have hpos : (0 : ℝ) < 1 / (n + 1 : ℝ) := by positivity
    have hmem : Set.Iio (1 / (n + 1 : ℝ)) ∈ 𝓝 (0 : ℝ) :=
      isOpen_Iio.mem_nhds (show (0 : ℝ) ∈ Set.Iio (1 / (n + 1 : ℝ)) from hpos)
    exact nhdsWithin_le_nhds hmem
  have hbnd0 : Filter.Tendsto (fun z => Work.Spaces.pz Ψ z θ
      * (z ^ 2 * Work.Spaces.pthIter 2 Ψ z θ * cut n z * w2 z))
      (𝓝[>] (0 : ℝ)) (nhds 0) := by
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [hmem0] with z hz
    simp [Work.FTS.EllipticEst.cut_apply_zero_of_le n hz.le]
  have hbndT : Filter.Tendsto (fun z => Work.Spaces.pz Ψ z θ
      * (z ^ 2 * Work.Spaces.pthIter 2 Ψ z θ * cut n z * w2 z)) Filter.atTop (nhds 0) := by
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_ge_atTop (3 * (n + 1 : ℝ))] with z hz
    simp [Work.FTS.EllipticEst.cut_apply_zero_of_ge n hz]
  have hIBP := MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul (a := (0 : ℝ)) (a' := (0 : ℝ))
    (b' := (0 : ℝ))
    (u := fun z => Work.Spaces.pz Ψ z θ) (u' := fun z => Work.Spaces.pzIter 2 Ψ z θ)
    (v := fun z => z ^ 2 * Work.Spaces.pthIter 2 Ψ z θ * cut n z * w2 z)
    (v' := fun z => Dv n Ψ z θ)
    hu hv hI1 hI2 hbnd0 hbndT
  simpa using hIBP

end IBP

section Fubini

/-- The pointwise form of the RHS integrand of the cut-off identity. -/
noncomputable def nice (n : ℕ) (Ψ : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  cut n z * w2 z
      * (2 * G Ψ z θ * Phi Ψ z θ + G Ψ z θ * H Ψ z θ - 4 * G Ψ z θ * Phi Ψ z θ / (1 + z))
    + w2 z * (G Ψ z θ * Phi Ψ z θ) * (z * deriv (cut n) z)

theorem pz_mul_Dv_eq_nice (n : ℕ) (Ψ : ℝ → ℝ → ℝ) (hΨ : Work.Spaces.SmoothNbhd Ψ)
    {z : ℝ} (hz : 0 < z) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.pz Ψ z θ * Dv n Ψ z θ = nice n Ψ z θ := by
  have h := pz_mul_deriv_expansion n Ψ hΨ hz hθ
  have hd : deriv (fun z' => z' ^ 2 * Work.Spaces.pthIter 2 Ψ z' θ * cut n z' * w2 z') z
      = Dv n Ψ z θ := (hasDerivAt_v_eq_Dv n Ψ hΨ hz hθ).deriv
  rw [hd] at h
  rw [h]
  simp only [nice, G, Phi, H]

end Fubini

section Joint

theorem continuousOn_uncurry_smoothNbhd {g : ℝ → ℝ → ℝ} (hg : Work.Spaces.SmoothNbhd g)
    {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (Function.uncurry g)
      (Set.Icc a b ×ˢ Work.Spaces.Iθ) := by
  have hsub : Set.Icc a b ×ˢ Work.Spaces.Iθ
      ⊆ Set.Ioi (-1 : ℝ) ×ˢ Set.Ioo (-1) (Real.pi / 2 + 1) := by
    rintro ⟨z, θ⟩ ⟨hz, hθ⟩
    refine ⟨?_, ?_⟩
    · have : (0 : ℝ) < z := lt_of_lt_of_le ha hz.1
      exact show (-1 : ℝ) < z by linarith
    · exact ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  exact hg.continuousOn.mono hsub

theorem continuousOn_uncurry_mul_zw2 (n : ℕ) (Ψ : ℝ → ℝ → ℝ) (hΨ : Work.Spaces.SmoothNbhd Ψ) :
    ContinuousOn (fun p : ℝ × ℝ =>
        p.1 ^ 2 * Work.Spaces.pzIter 2 Ψ p.1 p.2 * Work.Spaces.pthIter 2 Ψ p.1 p.2
          * cut n p.1 * w2 p.1)
      (Set.Icc (1 / (2 * (n + 1 : ℝ))) (4 * (n + 1 : ℝ)) ×ˢ Work.Spaces.Iθ) := by
  have ha : (0 : ℝ) < 1 / (2 * (n + 1 : ℝ)) := by positivity
  have h1 : ContinuousOn (fun p : ℝ × ℝ => p.1 ^ 2)
      (Set.Icc (1 / (2 * (n + 1 : ℝ))) (4 * (n + 1 : ℝ)) ×ˢ Work.Spaces.Iθ) :=
    ((continuous_fst.pow 2).continuousOn)
  have h2 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pzIter 2 Ψ p.1 p.2)
      (Set.Icc (1 / (2 * (n + 1 : ℝ))) (4 * (n + 1 : ℝ)) ×ˢ Work.Spaces.Iθ) :=
    continuousOn_uncurry_smoothNbhd (Work.Spaces.smoothNbhd_pzIter hΨ 2) ha
  have h3 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pthIter 2 Ψ p.1 p.2)
      (Set.Icc (1 / (2 * (n + 1 : ℝ))) (4 * (n + 1 : ℝ)) ×ˢ Work.Spaces.Iθ) :=
    continuousOn_uncurry_smoothNbhd (smoothNbhd_pthIter Ψ hΨ 2) ha
  have h4 : ContinuousOn (fun p : ℝ × ℝ => cut n p.1)
      (Set.Icc (1 / (2 * (n + 1 : ℝ))) (4 * (n + 1 : ℝ)) ×ˢ Work.Spaces.Iθ) :=
    ((Work.FTS.EllipticEst.cut_contDiff n).continuous.comp continuous_fst).continuousOn
  have h5 : ContinuousOn (fun p : ℝ × ℝ => w2 p.1)
      (Set.Icc (1 / (2 * (n + 1 : ℝ))) (4 * (n + 1 : ℝ)) ×ˢ Work.Spaces.Iθ) :=
    (continuousOn_w2' ha).comp continuous_fst.continuousOn (fun p hp => hp.1)
  exact (((h1.mul h2).mul h3).mul h4).mul h5

theorem continuousOn_uncurry_nice (n : ℕ) (Ψ : ℝ → ℝ → ℝ) (hΨ : Work.Spaces.SmoothNbhd Ψ) :
    ContinuousOn (fun p : ℝ × ℝ => nice n Ψ p.1 p.2)
      (Set.Icc (1 / (2 * (n + 1 : ℝ))) (4 * (n + 1 : ℝ)) ×ˢ Work.Spaces.Iθ) := by
  have ha : (0 : ℝ) < 1 / (2 * (n + 1 : ℝ)) := by positivity
  have hz : ContinuousOn (fun p : ℝ × ℝ => p.1)
      (Set.Icc (1 / (2 * (n + 1 : ℝ))) (4 * (n + 1 : ℝ)) ×ˢ Work.Spaces.Iθ) :=
    continuous_fst.continuousOn
  have hG : ContinuousOn (fun p : ℝ × ℝ => p.1 * Work.Spaces.pz Ψ p.1 p.2)
      (Set.Icc (1 / (2 * (n + 1 : ℝ))) (4 * (n + 1 : ℝ)) ×ˢ Work.Spaces.Iθ) :=
    hz.mul (continuousOn_uncurry_smoothNbhd (Work.Spaces.smoothNbhd_pzIter hΨ 1) ha)
  have hφ : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pthIter 2 Ψ p.1 p.2)
      (Set.Icc (1 / (2 * (n + 1 : ℝ))) (4 * (n + 1 : ℝ)) ×ˢ Work.Spaces.Iθ) :=
    continuousOn_uncurry_smoothNbhd (smoothNbhd_pthIter Ψ hΨ 2) ha
  have hH : ContinuousOn (fun p : ℝ × ℝ => p.1 * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) p.1 p.2)
      (Set.Icc (1 / (2 * (n + 1 : ℝ))) (4 * (n + 1 : ℝ)) ×ˢ Work.Spaces.Iθ) :=
    hz.mul (continuousOn_uncurry_smoothNbhd
      (Work.Spaces.smoothNbhd_pzIter (smoothNbhd_pthIter Ψ hΨ 2) 1) ha)
  have hχ : ContinuousOn (fun p : ℝ × ℝ => cut n p.1)
      (Set.Icc (1 / (2 * (n + 1 : ℝ))) (4 * (n + 1 : ℝ)) ×ˢ Work.Spaces.Iθ) :=
    ((Work.FTS.EllipticEst.cut_contDiff n).continuous.comp continuous_fst).continuousOn
  have hχ' : ContinuousOn (fun p : ℝ × ℝ => deriv (cut n) p.1)
      (Set.Icc (1 / (2 * (n + 1 : ℝ))) (4 * (n + 1 : ℝ)) ×ˢ Work.Spaces.Iθ) :=
    ((continuous_deriv_cut n).comp continuous_fst).continuousOn
  have hw : ContinuousOn (fun p : ℝ × ℝ => w2 p.1)
      (Set.Icc (1 / (2 * (n + 1 : ℝ))) (4 * (n + 1 : ℝ)) ×ˢ Work.Spaces.Iθ) :=
    (continuousOn_w2' ha).comp continuous_fst.continuousOn (fun p hp => hp.1)
  have hone : ContinuousOn (fun p : ℝ × ℝ => (1 : ℝ) + p.1)
      (Set.Icc (1 / (2 * (n + 1 : ℝ))) (4 * (n + 1 : ℝ)) ×ˢ Work.Spaces.Iθ) :=
    (continuous_const.add continuous_fst).continuousOn
  have hne : ∀ p ∈ Set.Icc (1 / (2 * (n + 1 : ℝ))) (4 * (n + 1 : ℝ)) ×ˢ Work.Spaces.Iθ,
      (1 : ℝ) + p.1 ≠ 0 := by
    rintro ⟨z, θ⟩ ⟨hz', _⟩
    have : (0 : ℝ) < z := lt_of_lt_of_le ha hz'.1
    linarith
  have hc4 : ContinuousOn (fun _ : ℝ × ℝ => (4 : ℝ))
      (Set.Icc (1 / (2 * (n + 1 : ℝ))) (4 * (n + 1 : ℝ)) ×ˢ Work.Spaces.Iθ) :=
    continuousOn_const
  have hfrac : ContinuousOn
      (fun p : ℝ × ℝ => 4 * (p.1 * Work.Spaces.pz Ψ p.1 p.2) * (Work.Spaces.pthIter 2 Ψ p.1 p.2)
        / (1 + p.1))
      (Set.Icc (1 / (2 * (n + 1 : ℝ))) (4 * (n + 1 : ℝ)) ×ˢ Work.Spaces.Iθ) :=
    ((hc4.mul hG).mul hφ).div hone hne
  have hc2 : ContinuousOn (fun _ : ℝ × ℝ => (2 : ℝ))
      (Set.Icc (1 / (2 * (n + 1 : ℝ))) (4 * (n + 1 : ℝ)) ×ˢ Work.Spaces.Iθ) :=
    continuousOn_const
  have hsum : ContinuousOn
      (fun p : ℝ × ℝ => 2 * (p.1 * Work.Spaces.pz Ψ p.1 p.2) * (Work.Spaces.pthIter 2 Ψ p.1 p.2)
          + (p.1 * Work.Spaces.pz Ψ p.1 p.2) * (p.1 * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) p.1 p.2)
          - 4 * (p.1 * Work.Spaces.pz Ψ p.1 p.2) * (Work.Spaces.pthIter 2 Ψ p.1 p.2) / (1 + p.1))
      (Set.Icc (1 / (2 * (n + 1 : ℝ))) (4 * (n + 1 : ℝ)) ×ˢ Work.Spaces.Iθ) :=
    (((hc2.mul hG).mul hφ).add (hG.mul hH)).sub hfrac
  simp only [nice, G, Phi, H]
  exact ((hχ.mul hw).mul hsum).add ((hw.mul (hG.mul hφ)).mul (hz.mul hχ'))

end Joint



section SmoothNbhdAux

/-- The first coordinate is smooth on a neighbourhood of the closed quadrant. -/
theorem smoothNbhd_fst : Work.Spaces.SmoothNbhd (fun z _ : ℝ => z) :=
  contDiff_fst.contDiffOn

/-- `SmoothNbhd` is closed under pointwise products. -/
theorem smoothNbhd_mul {f g : ℝ → ℝ → ℝ} (hf : Work.Spaces.SmoothNbhd f)
    (hg : Work.Spaces.SmoothNbhd g) :
    Work.Spaces.SmoothNbhd (fun z θ => f z θ * g z θ) := by
  have hfun : Function.uncurry (fun z θ => f z θ * g z θ)
      = fun p : ℝ × ℝ => Function.uncurry f p * Function.uncurry g p := rfl
  show ContDiffOn ℝ ⊤ (Function.uncurry (fun z θ => f z θ * g z θ)) Work.Spaces.nbhU
  rw [hfun]
  exact hf.mul hg

theorem smoothNbhd_G (Ψ : ℝ → ℝ → ℝ) (hΨ : Work.Spaces.SmoothNbhd Ψ) :
    Work.Spaces.SmoothNbhd (G Ψ) :=
  smoothNbhd_mul smoothNbhd_fst hΨ.pz

theorem smoothNbhd_Phi (Ψ : ℝ → ℝ → ℝ) (hΨ : Work.Spaces.SmoothNbhd Ψ) :
    Work.Spaces.SmoothNbhd (Phi Ψ) := hΨ.pth.pth

theorem smoothNbhd_H (Ψ : ℝ → ℝ → ℝ) (hΨ : Work.Spaces.SmoothNbhd Ψ) :
    Work.Spaces.SmoothNbhd (H Ψ) :=
  smoothNbhd_mul smoothNbhd_fst hΨ.pth.pth.pz

/-- The function `(z,θ) ↦ cw z = 2(z-1)/(1+z)` is smooth on a neighbourhood of the quadrant. -/
theorem smoothNbhd_cw : Work.Spaces.SmoothNbhd (fun z _ : ℝ => cw z) := by
  have hfun : Function.uncurry (fun z _ : ℝ => cw z)
      = fun p : ℝ × ℝ => 2 * (p.1 - 1) / (1 + p.1) := by
    funext p
    simp only [Function.uncurry, cw]
  show ContDiffOn ℝ ⊤ (Function.uncurry (fun z _ : ℝ => cw z)) Work.Spaces.nbhU
  rw [hfun]
  refine ContDiffOn.div ?_ ?_ ?_
  · exact (contDiff_const.mul (contDiff_fst.sub contDiff_const)).contDiffOn
  · exact (contDiff_const.add contDiff_fst).contDiffOn
  · intro p hp
    have h1 : (-1 : ℝ) < p.1 := hp.1
    have : (0 : ℝ) < 1 + p.1 := by linarith
    exact ne_of_gt this

theorem smoothNbhd_cw_Phi (Ψ : ℝ → ℝ → ℝ) (hΨ : Work.Spaces.SmoothNbhd Ψ) :
    Work.Spaces.SmoothNbhd (fun z θ => cw z * Phi Ψ z θ) :=
  smoothNbhd_mul smoothNbhd_cw (smoothNbhd_Phi Ψ hΨ)

end SmoothNbhdAux

end Work.FTS.EllipticEst.AngSecond
