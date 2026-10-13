/-
Copyright: work module for the Elgindi finite-time singularity project.

# Auxiliary lemmas for the weighted radial Hardy inequality `zHardy_weighted`

* `zHardy_finint`: the finite-interval integrated form of the pointwise inequality of
  `zHardyDefs.zHardy_pointwise`.
* `zHardy_seq_bot`, `zHardy_seq_top`: the boundary term `zFlux h` vanishes along sequences
  tending to `0` (dyadic annuli) resp. to `∞` (intervals `[k+1,2k+2]`), using only the
  integrability of the weight times `h²`.
* `zHardy_tendsto_setIntegral_Ioc`: the truncated integrals over `(ε k, M k)` converge to
  the integral over `(0,∞)`.
* `zHardy_rDzIter_contDiffOn`: `rDzIter n` preserves smoothness on `(0,∞)`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Interval.Basic
import Submission.Work.FTS.EllipticEst.zHardyDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Elementary continuity facts on `[a,b] ⊆ (0,∞)` -/

theorem continuousOn_w_Icc {a b : ℝ} (ha : 0 < a) :
    ContinuousOn Work.Spaces.w (Set.Icc a b) := by
  unfold Work.Spaces.w
  apply ContinuousOn.div
  · exact (continuousOn_const.add continuousOn_id).pow 2
  · exact continuousOn_id.pow 2
  · intro y hy
    have h1 : (0 : ℝ) < y := lt_of_lt_of_le ha hy.1
    positivity

theorem continuousOn_zA_Icc {a b : ℝ} (ha : -1 < a) :
    ContinuousOn zA (Set.Icc a b) := by
  unfold zA
  apply ContinuousOn.div
  · exact continuousOn_id.sub continuousOn_const
  · exact continuousOn_const.mul (continuousOn_const.add continuousOn_id)
  · intro y hy
    have h1 : (0 : ℝ) < 1 + y := by linarith [ha, hy.1]
    exact ne_of_gt (by positivity)

theorem continuousOn_zDA_Icc {a b : ℝ} (ha : -1 < a) :
    ContinuousOn zDA (Set.Icc a b) := by
  unfold zDA
  apply ContinuousOn.div
  · exact continuousOn_const
  · exact (continuousOn_const.add continuousOn_id).pow 2
  · intro y hy
    have h1 : (0 : ℝ) < 1 + y := by linarith [ha, hy.1]
    exact ne_of_gt (by positivity)

theorem continuousOn_zDw_Icc {a b : ℝ} (ha : 0 < a) :
    ContinuousOn zDw (Set.Icc a b) := by
  unfold zDw
  apply ContinuousOn.sub
  · apply ContinuousOn.div
    · exact continuousOn_const.mul (continuousOn_const.add continuousOn_id)
    · exact continuousOn_id.pow 2
    · intro y hy
      have h1 : 0 < y := lt_of_lt_of_le ha hy.1
      positivity
  · apply ContinuousOn.div
    · have h2 : ContinuousOn (fun y : ℝ => (2:ℝ) * (1 + y) ^ 2) (Set.Icc a b) :=
        continuousOn_const.mul ((continuousOn_const.add continuousOn_id).pow 2)
      exact h2
    · exact continuousOn_id.pow 3
    · intro y hy
      have h1 : 0 < y := lt_of_lt_of_le ha hy.1
      positivity

/-- The derivative of a function smooth on `(0,∞)` is continuous on `[a,b] ⊆ (0,∞)`. -/
theorem continuousOn_deriv_Icc (h : ℝ → ℝ) (hsm : ContDiffOn ℝ ⊤ h (Set.Ioi 0))
    {a b : ℝ} (ha : 0 < a) : ContinuousOn (fun y => deriv h y) (Set.Icc a b) := by
  have h1 : ContinuousOn (derivWithin h (Set.Ioi 0)) (Set.Ioi 0) :=
    hsm.continuousOn_derivWithin isOpen_Ioi.uniqueDiffOn le_top
  have h2 : ContinuousOn (derivWithin h (Set.Ioi 0)) (Set.Icc a b) :=
    h1.mono (fun y hy => lt_of_lt_of_le ha hy.1)
  refine h2.congr (fun y hy => ?_)
  exact (derivWithin_of_isOpen isOpen_Ioi (lt_of_lt_of_le ha hy.1)).symm

/-! ## The finite-interval inequality -/

theorem zHardy_finint (h : ℝ → ℝ) (hsm : ContDiffOn ℝ ⊤ h (Set.Ioi 0)) {ε M : ℝ}
    (hε : 0 < ε) (hεM : ε ≤ M) :
    (∫ z in ε..M, (Work.Spaces.w z) ^ 2 * (h z) ^ 2)
      ≤ 4 * (∫ z in ε..M, (Work.Spaces.w z) ^ 2 * (rDz h z) ^ 2)
        + 4 * (zFlux h M - zFlux h ε) := by
  have hmem : ∀ y ∈ Set.Icc ε M, 0 < y := fun y hy => lt_of_lt_of_le hε hy.1
  have hdh : ∀ y, 0 < y → HasDerivAt h (deriv h y) y := fun y hy =>
    (hsm.differentiableOn (by simp)).hasDerivAt (isOpen_Ioi.mem_nhds hy)
  have hhcont : ContinuousOn h (Set.Icc ε M) := hsm.continuousOn.mono (fun y hy => hmem y hy)
  have hwcont : ContinuousOn Work.Spaces.w (Set.Icc ε M) := continuousOn_w_Icc hε
  have hzAcont : ContinuousOn zA (Set.Icc ε M) := continuousOn_zA_Icc (by linarith)
  have hzDAcont : ContinuousOn zDA (Set.Icc ε M) := continuousOn_zDA_Icc (by linarith)
  have hzDwcont : ContinuousOn zDw (Set.Icc ε M) := continuousOn_zDw_Icc hε
  have hderivcont : ContinuousOn (fun y => deriv h y) (Set.Icc ε M) :=
    continuousOn_deriv_Icc h hsm hε
  have hFcont : ContinuousOn (fun y => zA y * (h y) ^ 2 * (Work.Spaces.w y) ^ 2 * y)
      (Set.Icc ε M) :=
    ((hzAcont.mul (hhcont.pow 2)).mul (hwcont.pow 2)).mul continuousOn_id
  have hGcont : ContinuousOn (fun y => zFluxD h (deriv h y) y) (Set.Icc ε M) := by
    have t1 : ContinuousOn (fun y => zDA y * (h y) ^ 2 * (Work.Spaces.w y) ^ 2 * y)
        (Set.Icc ε M) :=
      ((hzDAcont.mul (hhcont.pow 2)).mul (hwcont.pow 2)).mul continuousOn_id
    have t2 : ContinuousOn
        (fun y => zA y * (2 * h y * deriv h y) * (Work.Spaces.w y) ^ 2 * y) (Set.Icc ε M) :=
      ((hzAcont.mul ((continuousOn_const.mul hhcont).mul hderivcont)).mul
        (hwcont.pow 2)).mul continuousOn_id
    have t3 : ContinuousOn
        (fun y => zA y * (h y) ^ 2 * (2 * Work.Spaces.w y * zDw y) * y) (Set.Icc ε M) :=
      ((hzAcont.mul (hhcont.pow 2)).mul ((continuousOn_const.mul hwcont).mul hzDwcont)).mul
        continuousOn_id
    have t4 : ContinuousOn (fun y => zA y * (h y) ^ 2 * (Work.Spaces.w y) ^ 2) (Set.Icc ε M) :=
      (hzAcont.mul (hhcont.pow 2)).mul (hwcont.pow 2)
    have hsum : ContinuousOn (fun y => zDA y * (h y) ^ 2 * (Work.Spaces.w y) ^ 2 * y
        + zA y * (2 * h y * deriv h y) * (Work.Spaces.w y) ^ 2 * y
        + zA y * (h y) ^ 2 * (2 * Work.Spaces.w y * zDw y) * y
        + zA y * (h y) ^ 2 * (Work.Spaces.w y) ^ 2) (Set.Icc ε M) :=
      ((t1.add t2).add t3).add t4
    exact hsum
  have hI1 : IntervalIntegrable (fun y => (Work.Spaces.w y) ^ 2 * (h y) ^ 2) volume ε M := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hεM]
    exact (hwcont.pow 2).mul (hhcont.pow 2)
  have hI2 : IntervalIntegrable (fun y => (Work.Spaces.w y) ^ 2 * (rDz h y) ^ 2) volume ε M := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hεM]
    exact (hwcont.pow 2).mul ((continuousOn_id.mul hderivcont).pow 2)
  have hIG : IntervalIntegrable (fun y => zFluxD h (deriv h y) y) volume ε M := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hεM]
    exact hGcont
  have hpt : ∀ y ∈ Set.Icc ε M,
      0 ≤ 4 * (Work.Spaces.w y) ^ 2 * (rDz h y) ^ 2 - (Work.Spaces.w y) ^ 2 * (h y) ^ 2
        + 4 * zFluxD h (deriv h y) y := by
    intro y hy
    have hy0 := hmem y hy
    have hp := zHardy_pointwise h hy0 (hdh y hy0)
    have hderiv : deriv (fun y => zA y * (h y) ^ 2 * (Work.Spaces.w y) ^ 2 * y) y
        = zFluxD h (deriv h y) y := (hasDerivAt_zFlux h hy0 (hdh y hy0)).deriv
    rw [hderiv] at hp
    simpa only [rDz] using hp
  have hmono : ∫ y in ε..M, (Work.Spaces.w y) ^ 2 * (h y) ^ 2
      ≤ ∫ y in ε..M,
          (4 * ((Work.Spaces.w y) ^ 2 * (rDz h y) ^ 2) + 4 * zFluxD h (deriv h y) y) := by
    refine intervalIntegral.integral_mono_on hεM hI1 ((hI2.const_mul 4).add (hIG.const_mul 4)) ?_
    intro y hy
    have := hpt y hy
    linarith
  have hsplit : (∫ y in ε..M,
        (4 * ((Work.Spaces.w y) ^ 2 * (rDz h y) ^ 2) + 4 * zFluxD h (deriv h y) y))
      = 4 * (∫ y in ε..M, (Work.Spaces.w y) ^ 2 * (rDz h y) ^ 2)
        + 4 * (∫ y in ε..M, zFluxD h (deriv h y) y) := by
    rw [intervalIntegral.integral_add (hI2.const_mul 4) (hIG.const_mul 4),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hFTC : ∫ y in ε..M, zFluxD h (deriv h y) y = zFlux h M - zFlux h ε := by
    have hd : ∀ y ∈ Set.Ioo ε M,
        HasDerivAt (fun y => zA y * (h y) ^ 2 * (Work.Spaces.w y) ^ 2 * y)
          (zFluxD h (deriv h y) y) y := fun y hy => by
      have hy0 := hmem y (Set.Ioo_subset_Icc_self hy)
      exact hasDerivAt_zFlux h hy0 (hdh y hy0)
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hεM hFcont hd hIG
    simpa only [zFlux] using h
  rw [hsplit, hFTC] at hmono
  linarith

/-! ## The boundary term at `0` along dyadic annuli -/

theorem zHardy_seq_bot (H : ℝ → ℝ) (hH : IntegrableOn H (Set.Ioc (0:ℝ) 1))
    (hHnn : ∀ z, 0 ≤ H z)
    (hcont : ∀ k : ℕ, ContinuousOn H (Set.Icc ((1/2:ℝ) ^ (k + 1)) ((1/2:ℝ) ^ k))) :
    ∃ ε : ℕ → ℝ,
      (∀ k, ε k ∈ Set.Icc ((1/2:ℝ) ^ (k + 1)) ((1/2:ℝ) ^ k)) ∧
        Tendsto ε atTop (𝓝 0) ∧
        Tendsto (fun k => H (ε k) * ε k) atTop (𝓝 0) := by
  have hle : ∀ k : ℕ, (1/2:ℝ) ^ (k + 1) ≤ (1/2:ℝ) ^ k := by
    intro k
    have h0 : (0:ℝ) < (1/2:ℝ) ^ k := by positivity
    rw [pow_succ]
    nlinarith
  have hmin : ∀ k : ℕ, ∃ x : ℝ, x ∈ Set.Icc ((1/2:ℝ) ^ (k + 1)) ((1/2:ℝ) ^ k) ∧
      ∀ y ∈ Set.Icc ((1/2:ℝ) ^ (k + 1)) ((1/2:ℝ) ^ k), H x ≤ H y := by
    intro k
    obtain ⟨x, hx, hxm⟩ := isCompact_Icc.exists_isMinOn
      ⟨_, Set.left_mem_Icc.mpr (hle k)⟩ (hcont k)
    exact ⟨x, hx, fun y hy => isMinOn_iff.mp hxm y hy⟩
  choose x hxmem hxmin using hmin
  have htail : Tendsto (fun k : ℕ => ∫ z in Set.Ioc (0:ℝ) ((1/2:ℝ) ^ k), H z) atTop (𝓝 0) := by
    have hanti : Antitone (fun k : ℕ => Set.Ioc (0:ℝ) ((1/2:ℝ) ^ k)) := by
      intro a b hab
      exact Set.Ioc_subset_Ioc_right (pow_le_pow_of_le_one (by norm_num) (by norm_num) hab)
    have hInter : (⋂ k : ℕ, Set.Ioc (0:ℝ) ((1/2:ℝ) ^ k)) = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.mpr fun z hz => ?_
      have hzk : ∀ k : ℕ, z ∈ Set.Ioc (0:ℝ) ((1/2:ℝ) ^ k) := fun k => Set.mem_iInter.mp hz k
      have hpos : 0 < z := (hzk 0).1
      have ht : Tendsto (fun k : ℕ => (1/2:ℝ) ^ k) atTop (𝓝 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
      have hzle : z ≤ 0 := ge_of_tendsto ht (Eventually.of_forall fun k => (hzk k).2)
      linarith
    have h := tendsto_setIntegral_of_antitone (μ := volume) (f := H)
      (s := fun k : ℕ => Set.Ioc (0:ℝ) ((1/2:ℝ) ^ k))
      (fun k => measurableSet_Ioc) hanti ⟨0, by simpa using hH⟩
    simpa only [hInter, setIntegral_empty] using h
  refine ⟨x, hxmem, ?_, ?_⟩
  · refine squeeze_zero
      (fun k => le_of_lt (lt_of_lt_of_le (by positivity) (Set.mem_Icc.mp (hxmem k)).1))
      (fun k => (Set.mem_Icc.mp (hxmem k)).2) ?_
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  · have hbnd : ∀ k : ℕ, H (x k) * x k ≤ 2 * (∫ z in Set.Ioc (0:ℝ) ((1/2:ℝ) ^ k), H z) :=
      fun k => by
      have hxle : x k ≤ (1/2:ℝ) ^ k := (Set.mem_Icc.mp (hxmem k)).2
      have hHx : 0 ≤ H (x k) := hHnn _
      have h1 : H (x k) * x k ≤ 2 * (H (x k) * ((1/2:ℝ) ^ k - (1/2:ℝ) ^ (k + 1))) := by
        have hb : ((1/2:ℝ) ^ k - (1/2:ℝ) ^ (k + 1)) * 2 = (1/2:ℝ) ^ k := by
          rw [pow_succ]; ring
        calc H (x k) * x k ≤ H (x k) * ((1/2:ℝ) ^ k) := mul_le_mul_of_nonneg_left hxle hHx
          _ = 2 * (H (x k) * ((1/2:ℝ) ^ k - (1/2:ℝ) ^ (k + 1))) := by rw [← hb]; ring
      have h3 : H (x k) * ((1/2:ℝ) ^ k - (1/2:ℝ) ^ (k + 1))
          ≤ ∫ y in (1/2:ℝ) ^ (k + 1)..(1/2:ℝ) ^ k, H y := by
        have hci : IntervalIntegrable H volume ((1/2:ℝ) ^ (k + 1)) ((1/2:ℝ) ^ k) := by
          apply ContinuousOn.intervalIntegrable
          rw [Set.uIcc_of_le (hle k)]
          exact hcont k
        have h := intervalIntegral.integral_mono_on (hle k)
          (intervalIntegrable_const (c := H (x k))) hci (fun y hy => hxmin k y hy)
        rw [intervalIntegral.integral_const] at h
        calc H (x k) * ((1/2:ℝ) ^ k - (1/2:ℝ) ^ (k + 1))
            = ((1/2:ℝ) ^ k - (1/2:ℝ) ^ (k + 1)) * H (x k) := by ring
          _ ≤ ∫ y in (1/2:ℝ) ^ (k + 1)..(1/2:ℝ) ^ k, H y := h
      have h4 : ∫ y in (1/2:ℝ) ^ (k + 1)..(1/2:ℝ) ^ k, H y
          ≤ ∫ y in Set.Ioc (0:ℝ) ((1/2:ℝ) ^ k), H y := by
        rw [intervalIntegral.integral_of_le (hle k)]
        refine setIntegral_mono_set ?_ ?_ ?_
        · refine hH.mono_set fun y hy => ⟨hy.1, ?_⟩
          exact le_trans hy.2 (pow_le_one₀ (by norm_num) (by norm_num))
        · exact Eventually.of_forall hHnn
        · exact Eventually.of_forall fun y hy => ⟨lt_of_lt_of_le (by positivity) hy.1.le, hy.2⟩
      exact le_trans h1
        (le_trans (mul_le_mul_of_nonneg_left h3 (by norm_num : (0:ℝ) ≤ 2))
          (mul_le_mul_of_nonneg_left h4 (by norm_num : (0:ℝ) ≤ 2)))
    have htend : Tendsto (fun k : ℕ => 2 * (∫ z in Set.Ioc (0:ℝ) ((1/2:ℝ) ^ k), H z))
        atTop (𝓝 0) := by
      simpa using htail.const_mul 2
    exact squeeze_zero
      (fun k => mul_nonneg (hHnn _)
        (le_of_lt (lt_of_lt_of_le (by positivity) (Set.mem_Icc.mp (hxmem k)).1)))
      hbnd htend

/-! ## The boundary term at `∞` along `[k+1, 2k+2]` -/

theorem zHardy_seq_top (H : ℝ → ℝ) (hH : IntegrableOn H (Set.Ioi (1:ℝ)))
    (hHnn : ∀ z, 0 ≤ H z)
    (hcont : ∀ k : ℕ, ContinuousOn H (Set.Icc ((k:ℝ) + 1) (2 * ((k:ℝ) + 1)))) :
    ∃ M : ℕ → ℝ,
      (∀ k : ℕ, M k ∈ Set.Icc ((k:ℝ) + 1) (2 * ((k:ℝ) + 1))) ∧
        Tendsto M atTop atTop ∧
        Tendsto (fun k => H (M k) * M k) atTop (𝓝 0) := by
  have hle : ∀ k : ℕ, (k:ℝ) + 1 ≤ 2 * ((k:ℝ) + 1) := by
    intro k
    have hk : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
    linarith
  have hmin : ∀ k : ℕ, ∃ x : ℝ, x ∈ Set.Icc ((k:ℝ) + 1) (2 * ((k:ℝ) + 1)) ∧
      ∀ y ∈ Set.Icc ((k:ℝ) + 1) (2 * ((k:ℝ) + 1)), H x ≤ H y := by
    intro k
    obtain ⟨x, hx, hxm⟩ := isCompact_Icc.exists_isMinOn
      ⟨_, Set.left_mem_Icc.mpr (hle k)⟩ (hcont k)
    exact ⟨x, hx, fun y hy => isMinOn_iff.mp hxm y hy⟩
  choose x hxmem hxmin using hmin
  have htail : Tendsto (fun k : ℕ => ∫ z in Set.Ioi ((k:ℝ) + 1), H z) atTop (𝓝 0) := by
    have hanti : Antitone (fun k : ℕ => Set.Ioi ((k:ℝ) + 1)) := by
      intro a b hab
      exact Set.Ioi_subset_Ioi (by
        have : (a:ℝ) ≤ (b:ℝ) := Nat.cast_le.mpr hab
        linarith)
    have hInter : (⋂ k : ℕ, Set.Ioi ((k:ℝ) + 1)) = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.mpr fun z hz => ?_
      have hzk : ∀ k : ℕ, z ∈ Set.Ioi ((k:ℝ) + 1) := fun k => Set.mem_iInter.mp hz k
      have h0 : Tendsto (fun k : ℕ => (k:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
      have ht : Tendsto (fun k : ℕ => ((k:ℝ) + 1)) atTop atTop := by
        simpa using tendsto_atTop_add_const_right atTop (1:ℝ) h0
      have hev : ∀ᶠ k : ℕ in atTop, z < (k:ℝ) + 1 := ht.eventually_gt_atTop z
      obtain ⟨n, hn⟩ := eventually_atTop.mp hev
      have h1 : (n:ℝ) + 1 < z := hzk n
      have h2 : z < (n:ℝ) + 1 := hn n le_rfl
      linarith
    have h := tendsto_setIntegral_of_antitone (μ := volume) (f := H)
      (s := fun k : ℕ => Set.Ioi ((k:ℝ) + 1)) (fun k => measurableSet_Ioi) hanti
      ⟨0, by simpa using hH⟩
    simpa only [hInter, setIntegral_empty] using h
  refine ⟨x, hxmem, ?_, ?_⟩
  · refine tendsto_atTop_mono (fun k => ?_) tendsto_natCast_atTop_atTop
    have := (Set.mem_Icc.mp (hxmem k)).1
    linarith
  · refine squeeze_zero
      (fun k => mul_nonneg (hHnn _) (by
        have := (Set.mem_Icc.mp (hxmem k)).1
        have hk : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
        linarith))
      (fun k => ?_) (by simpa using htail.const_mul 2)
    have hxle : x k ≤ 2 * ((k:ℝ) + 1) := (Set.mem_Icc.mp (hxmem k)).2
    have hHx : 0 ≤ H (x k) := hHnn _
    have h1 : H (x k) * x k ≤ 2 * (H (x k) * (2 * ((k:ℝ) + 1) - ((k:ℝ) + 1))) := by
      calc H (x k) * x k ≤ H (x k) * (2 * ((k:ℝ) + 1)) := mul_le_mul_of_nonneg_left hxle hHx
        _ = 2 * (H (x k) * (2 * ((k:ℝ) + 1) - ((k:ℝ) + 1))) := by ring
    have h3 : H (x k) * (2 * ((k:ℝ) + 1) - ((k:ℝ) + 1))
        ≤ ∫ y in ((k:ℝ) + 1)..(2 * ((k:ℝ) + 1)), H y := by
      have hci : IntervalIntegrable H volume ((k:ℝ) + 1) (2 * ((k:ℝ) + 1)) := by
        apply ContinuousOn.intervalIntegrable
        rw [Set.uIcc_of_le (hle k)]
        exact hcont k
      have h := intervalIntegral.integral_mono_on (hle k)
        (intervalIntegrable_const (c := H (x k))) hci (fun y hy => hxmin k y hy)
      rw [intervalIntegral.integral_const] at h
      calc H (x k) * (2 * ((k:ℝ) + 1) - ((k:ℝ) + 1))
          = (2 * ((k:ℝ) + 1) - ((k:ℝ) + 1)) * H (x k) := by ring
        _ ≤ ∫ y in ((k:ℝ) + 1)..(2 * ((k:ℝ) + 1)), H y := h
    have h4 : ∫ y in ((k:ℝ) + 1)..(2 * ((k:ℝ) + 1)), H y
        ≤ ∫ y in Set.Ioi ((k:ℝ) + 1), H y := by
      rw [intervalIntegral.integral_of_le (hle k)]
      refine setIntegral_mono_set ?_ ?_ ?_
      · refine hH.mono_set fun y hy => ?_
        have hy' : (k:ℝ) + 1 < y := hy
        have hk : (1:ℝ) ≤ (k:ℝ) + 1 := by
          have h0 : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
          linarith
        exact lt_of_le_of_lt hk hy'
      · exact Eventually.of_forall hHnn
      · exact Eventually.of_forall fun y hy => hy.1
    exact le_trans h1
      (le_trans (mul_le_mul_of_nonneg_left h3 (by norm_num : (0:ℝ) ≤ 2))
        (mul_le_mul_of_nonneg_left h4 (by norm_num : (0:ℝ) ≤ 2)))

/-! ## Convergence of the truncated integrals -/

theorem zHardy_tendsto_setIntegral_Ioc (G : ℝ → ℝ) (hG : IntegrableOn G (Set.Ioi (0:ℝ)))
    {ε M : ℕ → ℝ} (hε0 : ∀ k, 0 < ε k)
    (hε : Tendsto ε atTop (𝓝 0)) (hM : Tendsto M atTop atTop) :
    Tendsto (fun k => ∫ z in Set.Ioc (ε k) (M k), G z) atTop
      (𝓝 (∫ z in Set.Ioi (0:ℝ), G z)) := by
  have hGind : Integrable ((Set.Ioi (0:ℝ)).indicator G) volume :=
    (integrable_indicator_iff measurableSet_Ioi).mpr hG
  have hmain : Tendsto (fun k : ℕ => ∫ z, (Set.Ioc (ε k) (M k)).indicator G z) atTop
      (𝓝 (∫ z, (Set.Ioi (0:ℝ)).indicator G z)) := by
    refine tendsto_integral_of_dominated_convergence (μ := volume)
      (bound := fun z => ‖(Set.Ioi (0:ℝ)).indicator G z‖)
      (F := fun k z => (Set.Ioc (ε k) (M k)).indicator G z)
      (f := fun z => (Set.Ioi (0:ℝ)).indicator G z) ?_ hGind.norm ?_ ?_
    · intro k
      have h1 : AEStronglyMeasurable
          (fun z : ℝ => (Set.Ioc (ε k) (M k)).indicator ((Set.Ioi (0:ℝ)).indicator G) z)
          volume := hGind.aestronglyMeasurable.indicator measurableSet_Ioc
      refine h1.congr ?_
      filter_upwards with z
      by_cases hz : z ∈ Set.Ioc (ε k) (M k)
      · have hz0 : z ∈ Set.Ioi (0:ℝ) := lt_trans (hε0 k) hz.1
        simp only [Set.indicator_of_mem hz, Set.indicator_of_mem hz0]
      · simp only [Set.indicator_of_notMem hz]
    · intro k
      filter_upwards with z
      by_cases hz : z ∈ Set.Ioc (ε k) (M k)
      · have hz0 : z ∈ Set.Ioi (0:ℝ) := lt_trans (hε0 k) hz.1
        rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz0]
      · rw [Set.indicator_of_notMem hz, norm_zero]
        exact norm_nonneg _
    · filter_upwards with z
      by_cases hz0 : z ∈ Set.Ioi (0:ℝ)
      · have hev1 : ∀ᶠ k : ℕ in atTop, ε k < z :=
          hε (isOpen_Iio.mem_nhds (show (0:ℝ) ∈ Set.Iio z from hz0))
        have hev2 : ∀ᶠ k : ℕ in atTop, z < M k := hM (Ioi_mem_atTop z)
        refine (tendsto_const_nhds (x := (Set.Ioi (0:ℝ)).indicator G z)).congr' ?_
        filter_upwards [hev1, hev2] with k h1 h2
        rw [Set.indicator_of_mem (show z ∈ Set.Ioc (ε k) (M k) from ⟨h1, le_of_lt h2⟩),
          Set.indicator_of_mem hz0]
      · have hev : ∀ᶠ k : ℕ in atTop,
            (Set.Ioi (0:ℝ)).indicator G z = (Set.Ioc (ε k) (M k)).indicator G z := by
          filter_upwards with k
          rw [Set.indicator_of_notMem hz0,
            Set.indicator_of_notMem (fun h => hz0 (lt_trans (hε0 k) h.1))]
        exact (tendsto_const_nhds (x := (Set.Ioi (0:ℝ)).indicator G z)).congr' hev
  have h1 : ∀ k : ℕ, (∫ z, (Set.Ioc (ε k) (M k)).indicator G z)
      = ∫ z in Set.Ioc (ε k) (M k), G z := fun k =>
    MeasureTheory.integral_indicator measurableSet_Ioc
  have h2 : (∫ z, (Set.Ioi (0:ℝ)).indicator G z) = ∫ z in Set.Ioi (0:ℝ), G z :=
    MeasureTheory.integral_indicator measurableSet_Ioi
  rw [funext h1, h2] at hmain
  exact hmain

/-! ## Smoothness of the iterates of `rDz` -/

theorem zHardy_rDzIter_contDiffOn (n : ℕ) (h : ℝ → ℝ)
    (hsm : ContDiffOn ℝ ⊤ h (Set.Ioi 0)) :
    ContDiffOn ℝ ⊤ (rDzIter n h) (Set.Ioi 0) := by
  induction n with
  | zero => simpa using hsm
  | succ n ih =>
    have hd : ContDiffOn ℝ ⊤ (deriv (rDzIter n h)) (Set.Ioi 0) := by
      have h1 := ih.derivWithin isOpen_Ioi.uniqueDiffOn (le_top : (⊤ : WithTop ℕ∞) + 1 ≤ ⊤)
      refine h1.congr (fun x hx => ?_)
      exact (derivWithin_of_isOpen isOpen_Ioi hx).symm
    have h2 : ContDiffOn ℝ ⊤ (rDz (rDzIter n h)) (Set.Ioi 0) := by
      have h3 : rDz (rDzIter n h) = fun z : ℝ => z * deriv (rDzIter n h) z := rfl
      rw [h3]
      exact contDiffOn_id.mul hd
    rw [rDzIter_succ]
    exact h2

end Work.FTS.EllipticEst
