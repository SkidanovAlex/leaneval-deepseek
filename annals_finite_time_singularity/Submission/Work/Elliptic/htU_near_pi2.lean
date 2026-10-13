import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Elliptic.HardyTwoDefs
import Submission.Work.Elliptic.sin_sq_ge_half
import Submission.Work.Elliptic.integral_sin_two_pi2

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Elliptic

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ### Elementary endpoint facts -/

private lemma mem_Icc_of_Ioo_halfpi {x : ℝ} (hx : x ∈ Set.Ioo 0 (π / 2)) :
    x ∈ Set.Icc (0 : ℝ) (π / 2) := ⟨le_of_lt hx.1, le_of_lt hx.2⟩

private lemma nhds_Icc_halfpi {x : ℝ} (hx : x ∈ Set.Ioo 0 (π / 2)) :
    Set.Icc (0 : ℝ) (π / 2) ∈ 𝓝 x :=
  mem_of_superset (isOpen_Ioo.mem_nhds hx) fun _ hy => ⟨le_of_lt hy.1, le_of_lt hy.2⟩

private lemma uniqueDiffOn_Icc_halfpi : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) (π / 2)) := by
  apply uniqueDiffOn_Icc
  linarith [Real.pi_pos]

private lemma Ioo_halfpi_subset {x : ℝ} (hx : x ∈ Set.Ioo 0 (π / 2)) :
    Set.Icc x (π / 2) ⊆ Set.Icc (0 : ℝ) (π / 2) :=
  Set.Icc_subset_Icc (le_of_lt hx.1) le_rfl

/-- The auxiliary function `Φ(y) = f'(y) sin(2y) - 2 cos(2y) f(y)` has derivative
`sin(2y) (f''(y) + 4 f(y))` at every interior point. -/
theorem hasDerivAt_htAux (f : ℝ → ℝ) (hf : ContDiffOn ℝ 2 f (Set.Icc 0 (π / 2))) (x : ℝ)
    (hx : x ∈ Set.Ioo 0 (π / 2)) :
    HasDerivAt (fun y => iteratedDerivWithin 1 f (Set.Icc 0 (π / 2)) y * Real.sin (2 * y)
        - 2 * Real.cos (2 * y) * f y)
      (Real.sin (2 * x) * (iteratedDerivWithin 2 f (Set.Icc 0 (π / 2)) x + 4 * f x)) x := by
  have hU := uniqueDiffOn_Icc_halfpi
  have hmem := nhds_Icc_halfpi hx
  have hxS := mem_Icc_of_Ioo_halfpi hx
  have hd1 : HasDerivAt (iteratedDerivWithin 1 f (Set.Icc 0 (π / 2)))
      (iteratedDerivWithin 2 f (Set.Icc 0 (π / 2)) x) x := by
    have hd := hf.differentiableOn_iteratedDerivWithin (s := Set.Icc 0 (π / 2)) (m := 1) (n := 2)
      (by norm_num) hU
    have hdx := hd x hxS
    have hda := hdx.differentiableAt hmem
    have hh := hda.hasDerivAt
    have hderivg : deriv (iteratedDerivWithin 1 f (Set.Icc 0 (π / 2))) x
        = iteratedDerivWithin 2 f (Set.Icc 0 (π / 2)) x := by
      rw [← derivWithin_of_mem_nhds hmem, ← iteratedDerivWithin_succ]
    rwa [hderivg] at hh
  have hd2 : HasDerivAt f (deriv f x) x :=
    ((hf.contDiffAt hmem).differentiableAt (by norm_num)).hasDerivAt
  have h2x : HasDerivAt (fun y : ℝ => 2 * y) 2 x := by
    simpa using (hasDerivAt_id x).const_mul (2 : ℝ)
  have hsin : HasDerivAt (fun y : ℝ => Real.sin (2 * y)) (2 * Real.cos (2 * x)) x := by
    simpa [mul_comm] using h2x.sin
  have hcos : HasDerivAt (fun y : ℝ => Real.cos (2 * y)) (-2 * Real.sin (2 * x)) x := by
    simpa [mul_comm] using h2x.cos
  have h2c : HasDerivAt (fun y : ℝ => 2 * Real.cos (2 * y)) (-4 * Real.sin (2 * x)) x := by
    have h2 := h2x.cos.const_mul (2 : ℝ)
    convert h2 using 1 <;> ring
  have hgx : iteratedDerivWithin 1 f (Set.Icc 0 (π / 2)) x = deriv f x := by
    rw [iteratedDerivWithin_one, derivWithin_of_mem_nhds hmem]
  have hA := hd1.mul hsin
  have hB := h2c.mul hd2
  have h3 := hA.sub hB
  rw [hgx] at h3
  convert h3 using 1
  ring

/-- The pointwise bound `|f' sin 2θ - 2 cos 2θ f| ≤ K cos²θ` near `π/2`. -/
theorem htU_phi_bound (f : ℝ → ℝ) (hf : ContDiffOn ℝ 2 f (Set.Icc 0 (π / 2)))
    (h1 : f (π / 2) = 0) (K : ℝ) (hK : 0 ≤ K)
    (hbd : ∀ s ∈ Set.Icc 0 (π / 2),
      |iteratedDerivWithin 2 f (Set.Icc 0 (π / 2)) s + 4 * f s| ≤ K) :
    ∀ x ∈ Set.Ioo 0 (π / 2),
      |iteratedDerivWithin 1 f (Set.Icc 0 (π / 2)) x * Real.sin (2 * x)
        - 2 * Real.cos (2 * x) * f x| ≤ K * Real.cos x ^ 2 := by
  intro x hx
  have hU := uniqueDiffOn_Icc_halfpi
  have hxS := mem_Icc_of_Ioo_halfpi hx
  have hxle : x ≤ π / 2 := le_of_lt hx.2
  have hsub := Ioo_halfpi_subset hx
  have hcont_g : ContinuousOn (iteratedDerivWithin 1 f (Set.Icc 0 (π / 2)))
      (Set.Icc 0 (π / 2)) :=
    hf.continuousOn_iteratedDerivWithin (m := 1) (n := 2) (by norm_num) hU
  have hcont_g2 : ContinuousOn (iteratedDerivWithin 2 f (Set.Icc 0 (π / 2)))
      (Set.Icc 0 (π / 2)) :=
    hf.continuousOn_iteratedDerivWithin (m := 2) (n := 2) (by norm_num) hU
  have hcont_f : ContinuousOn f (Set.Icc 0 (π / 2)) := hf.continuousOn
  have hcont_sin : ContinuousOn (fun y : ℝ => Real.sin (2 * y)) (Set.Icc 0 (π / 2)) := by
    fun_prop
  have hcont_cos : ContinuousOn (fun y : ℝ => Real.cos (2 * y)) (Set.Icc 0 (π / 2)) := by
    fun_prop
  have hcontPhi : ContinuousOn (fun y => iteratedDerivWithin 1 f (Set.Icc 0 (π / 2)) y
        * Real.sin (2 * y) - 2 * Real.cos (2 * y) * f y) (Set.Icc 0 (π / 2)) :=
    (hcont_g.mul hcont_sin).sub ((continuous_const.continuousOn.mul hcont_cos).mul hcont_f)
  have hPhi_pi2 : iteratedDerivWithin 1 f (Set.Icc 0 (π / 2)) (π / 2) * Real.sin (2 * (π / 2))
      - 2 * Real.cos (2 * (π / 2)) * f (π / 2) = 0 := by
    rw [show 2 * (π / 2) = π by ring, Real.sin_pi, Real.cos_pi, h1]
    ring
  have hderiv : ∀ y ∈ Set.Ioo x (π / 2),
      HasDerivAt (fun z => iteratedDerivWithin 1 f (Set.Icc 0 (π / 2)) z * Real.sin (2 * z)
          - 2 * Real.cos (2 * z) * f z)
        (Real.sin (2 * y) * (iteratedDerivWithin 2 f (Set.Icc 0 (π / 2)) y + 4 * f y)) y :=
    fun y hy => hasDerivAt_htAux f hf y ⟨lt_trans hx.1 hy.1, hy.2⟩
  have hcontF : ContinuousOn (fun y => Real.sin (2 * y)
      * (iteratedDerivWithin 2 f (Set.Icc 0 (π / 2)) y + 4 * f y)) (Set.Icc 0 (π / 2)) :=
    hcont_sin.mul (hcont_g2.add (continuous_const.continuousOn.mul hcont_f))
  have hcontF' : ContinuousOn (fun y => Real.sin (2 * y)
      * (iteratedDerivWithin 2 f (Set.Icc 0 (π / 2)) y + 4 * f y)) (Set.Icc x (π / 2)) :=
    hcontF.mono hsub
  have hint : IntervalIntegrable (fun y => Real.sin (2 * y)
      * (iteratedDerivWithin 2 f (Set.Icc 0 (π / 2)) y + 4 * f y)) volume x (π / 2) :=
    hcontF'.intervalIntegrable_of_Icc hxle
  have hFTC : ∫ y in x..(π / 2), (Real.sin (2 * y)
        * (iteratedDerivWithin 2 f (Set.Icc 0 (π / 2)) y + 4 * f y))
      = - (iteratedDerivWithin 1 f (Set.Icc 0 (π / 2)) x * Real.sin (2 * x)
            - 2 * Real.cos (2 * x) * f x) := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hxle (hcontPhi.mono hsub) hderiv hint
    rw [h, hPhi_pi2, zero_sub]
  have hmono : ∫ y in x..(π / 2), ‖Real.sin (2 * y)
        * (iteratedDerivWithin 2 f (Set.Icc 0 (π / 2)) y + 4 * f y)‖
      ≤ ∫ y in x..(π / 2), K * Real.sin (2 * y) := by
    apply intervalIntegral.integral_mono_on hxle
    · exact hcontF'.norm.intervalIntegrable_of_Icc hxle
    · exact ((continuous_const.continuousOn.mul (hcont_sin.mono hsub))).intervalIntegrable_of_Icc hxle
    · intro y hy
      have hyS : y ∈ Set.Icc (0 : ℝ) (π / 2) := ⟨le_trans hxS.1 hy.1, hy.2⟩
      have hsin_nn : 0 ≤ Real.sin (2 * y) :=
        Real.sin_nonneg_of_mem_Icc ⟨by linarith [hyS.1], by linarith [hyS.2]⟩
      have hb := hbd y hyS
      calc ‖Real.sin (2 * y) * (iteratedDerivWithin 2 f (Set.Icc 0 (π / 2)) y + 4 * f y)‖
          = |Real.sin (2 * y)| * |iteratedDerivWithin 2 f (Set.Icc 0 (π / 2)) y + 4 * f y| := by
            rw [Real.norm_eq_abs, abs_mul]
        _ = Real.sin (2 * y) * |iteratedDerivWithin 2 f (Set.Icc 0 (π / 2)) y + 4 * f y| := by
            rw [abs_of_nonneg hsin_nn]
        _ ≤ Real.sin (2 * y) * K := mul_le_mul_of_nonneg_left hb hsin_nn
        _ = K * Real.sin (2 * y) := by ring
  have hIntval : ∫ y in x..(π / 2), K * Real.sin (2 * y) = K * Real.cos x ^ 2 := by
    rw [intervalIntegral.integral_const_mul, integral_sin_two_pi2]
  have hmain : |iteratedDerivWithin 1 f (Set.Icc 0 (π / 2)) x * Real.sin (2 * x)
        - 2 * Real.cos (2 * x) * f x|
      = ‖∫ y in x..(π / 2), (Real.sin (2 * y)
          * (iteratedDerivWithin 2 f (Set.Icc 0 (π / 2)) y + 4 * f y))‖ := by
    rw [Real.norm_eq_abs, hFTC, abs_neg]
  rw [hmain]
  exact le_trans (intervalIntegral.norm_integral_le_integral_norm hxle)
    (le_trans hmono hIntval.le)

/-- The endpoint bounds for `f`, `f'` (compared with the one-sided endpoint value) and `f''`. -/
theorem htU_endpoint_bounds (f : ℝ → ℝ) (hf : ContDiffOn ℝ 2 f (Set.Icc 0 (π / 2)))
    (h1 : f (π / 2) = 0)
    (hcomp1 : ∀ x ∈ Set.Ioo 0 (π / 2), deriv f x = iteratedDerivWithin 1 f (Set.Icc 0 (π / 2)) x)
    (hcomp2 : ∀ x ∈ Set.Ioo 0 (π / 2),
      deriv (deriv f) x = iteratedDerivWithin 2 f (Set.Icc 0 (π / 2)) x) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ x ∈ Set.Ioo (π / 4) (π / 2), |f x| ≤ C * (π / 2 - x)) ∧
      (∀ x ∈ Set.Ioo (π / 4) (π / 2),
        |deriv f x - derivWithin f (Set.Icc 0 (π / 2)) (π / 2)| ≤ C * (π / 2 - x)) ∧
      (∀ x ∈ Set.Ioo (π / 4) (π / 2), |deriv (deriv f) x| ≤ C) := by
  have hU := uniqueDiffOn_Icc_halfpi
  obtain ⟨c1, hc1⟩ := IsCompact.exists_bound_of_continuousOn isCompact_Icc
      (hf.continuousOn_iteratedDerivWithin (m := 1) (n := 2) (by norm_num) hU)
  obtain ⟨c2, hc2⟩ := IsCompact.exists_bound_of_continuousOn isCompact_Icc
      (hf.continuousOn_iteratedDerivWithin (m := 2) (n := 2) (by norm_num) hU)
  refine ⟨max (max c1 0) (max c2 0), ?_, ?_, ?_, ?_⟩
  · exact le_trans (le_max_right c1 0) (le_max_left _ _)
  · intro x hx
    have hxS : x ∈ Set.Icc (0 : ℝ) (π / 2) :=
      ⟨le_of_lt (lt_trans (by linarith [Real.pi_pos] : (0 : ℝ) < π / 4) hx.1), le_of_lt hx.2⟩
    have hsub : Set.Icc x (π / 2) ⊆ Set.Icc (0 : ℝ) (π / 2) :=
      Set.Icc_subset_Icc hxS.1 le_rfl
    have hstep : ∀ t ∈ Set.Icc x (π / 2),
        HasDerivWithinAt f (derivWithin f (Set.Icc 0 (π / 2)) t) (Set.Icc x (π / 2)) t := by
      intro t ht
      have htS : t ∈ Set.Icc (0 : ℝ) (π / 2) := ⟨le_trans hxS.1 ht.1, ht.2⟩
      exact ((hf.differentiableOn (by norm_num) t htS).hasDerivWithinAt).mono
        hsub
    have hbound : ∀ t ∈ Set.Ico x (π / 2),
        ‖derivWithin f (Set.Icc 0 (π / 2)) t‖ ≤ max (max c1 0) (max c2 0) := by
      intro t ht
      have htS : t ∈ Set.Icc (0 : ℝ) (π / 2) := ⟨le_trans hxS.1 (ht.1), le_of_lt ht.2⟩
      have h := hc1 t htS
      rw [iteratedDerivWithin_one] at h
      exact le_trans h (le_trans (le_max_left c1 0) (le_max_left (max c1 0) (max c2 0)))
    have hres := norm_image_sub_le_of_norm_deriv_le_segment' hstep hbound (π / 2)
      ⟨le_of_lt hx.2, le_rfl⟩
    simpa [h1, Real.norm_eq_abs] using hres
  · intro x hx
    have hxIoo : x ∈ Set.Ioo (0 : ℝ) (π / 2) :=
      ⟨lt_trans (by linarith [Real.pi_pos] : (0 : ℝ) < π / 4) hx.1, hx.2⟩
    have hxS : x ∈ Set.Icc (0 : ℝ) (π / 2) := mem_Icc_of_Ioo_halfpi hxIoo
    have hsub : Set.Icc x (π / 2) ⊆ Set.Icc (0 : ℝ) (π / 2) := Ioo_halfpi_subset hxIoo
    have hstep : ∀ t ∈ Set.Icc x (π / 2),
        HasDerivWithinAt (iteratedDerivWithin 1 f (Set.Icc 0 (π / 2)))
          (iteratedDerivWithin 2 f (Set.Icc 0 (π / 2)) t) (Set.Icc x (π / 2)) t := by
      intro t ht
      have htS : t ∈ Set.Icc (0 : ℝ) (π / 2) := ⟨le_trans hxS.1 ht.1, ht.2⟩
      have hd := hf.differentiableOn_iteratedDerivWithin (s := Set.Icc 0 (π / 2)) (m := 1)
        (n := 2) (by norm_num) hU
      have hh := (hd t htS).hasDerivWithinAt
      rw [← iteratedDerivWithin_succ] at hh
      exact hh.mono hsub
    have hbound : ∀ t ∈ Set.Ico x (π / 2),
        ‖iteratedDerivWithin 2 f (Set.Icc 0 (π / 2)) t‖ ≤ max (max c1 0) (max c2 0) := by
      intro t ht
      have htS : t ∈ Set.Icc (0 : ℝ) (π / 2) := ⟨le_trans hxS.1 (ht.1), le_of_lt ht.2⟩
      exact le_trans (hc2 t htS)
        (le_trans (le_max_left c2 0) (le_max_right (max c1 0) (max c2 0)))
    have hres := norm_image_sub_le_of_norm_deriv_le_segment' hstep hbound (π / 2)
      ⟨le_of_lt hx.2, le_rfl⟩
    rw [iteratedDerivWithin_one] at hres
    rw [derivWithin_of_mem_nhds (nhds_Icc_halfpi hxIoo)] at hres
    simpa [Real.norm_eq_abs, abs_sub_comm] using hres
  · intro x hx
    have hxIoo : x ∈ Set.Ioo (0 : ℝ) (π / 2) :=
      ⟨lt_trans (by linarith [Real.pi_pos] : (0 : ℝ) < π / 4) hx.1, hx.2⟩
    have hxS : x ∈ Set.Icc (0 : ℝ) (π / 2) := mem_Icc_of_Ioo_halfpi hxIoo
    rw [hcomp2 x hxIoo]
    exact le_trans (by simpa [Real.norm_eq_abs] using hc2 x hxS)
      (le_trans (le_max_left c2 0) (le_max_right (max c1 0) (max c2 0)))

theorem htU_near_pi2 (f : ℝ → ℝ) (hf : ContDiffOn ℝ 2 f (Set.Icc 0 (π / 2))) (h1 : f (π / 2) = 0)
    (hcomp1 : ∀ x ∈ Set.Ioo 0 (π / 2), deriv f x = iteratedDerivWithin 1 f (Set.Icc 0 (π / 2)) x)
    (hcomp2 : ∀ x ∈ Set.Ioo 0 (π / 2),
        deriv (deriv f) x = iteratedDerivWithin 2 f (Set.Icc 0 (π / 2)) x)
    (hid1 : ∀ x ∈ Set.Ioo 0 (π / 2),
        (Real.sin (2 * x)) ^ 2 * deriv (Work.Elliptic.htU f) x
          = deriv f x * Real.sin (2 * x) - 2 * Real.cos (2 * x) * f x)
    (hid2 : ∀ x ∈ Set.Ioo 0 (π / 2),
        Real.sin (2 * x) * deriv (deriv (Work.Elliptic.htU f)) x
          = deriv (deriv f) x + 4 * f x - 4 * Real.cos (2 * x) * deriv (Work.Elliptic.htU f) x) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧
      (∀ x ∈ Set.Ioo (π / 2 - δ) (π / 2), |f x| ≤ C * (π / 2 - x)) ∧
      (∀ x ∈ Set.Ioo (π / 2 - δ) (π / 2),
        |deriv f x - derivWithin f (Set.Icc 0 (π / 2)) (π / 2)| ≤ C * (π / 2 - x)) ∧
      (∀ x ∈ Set.Ioo (π / 2 - δ) (π / 2), |deriv (deriv f) x| ≤ C) ∧
      (∀ x ∈ Set.Ioo (π / 2 - δ) (π / 2), |Work.Elliptic.htU f x| ≤ C) ∧
      (∀ x ∈ Set.Ioo (π / 2 - δ) (π / 2), |deriv (Work.Elliptic.htU f) x| ≤ C) ∧
      (∀ x ∈ Set.Ioo (π / 2 - δ) (π / 2),
        |Real.sin (2 * x) * deriv (deriv (Work.Elliptic.htU f)) x| ≤ C) := by
  have hU := uniqueDiffOn_Icc_halfpi
  obtain ⟨c0, hc0⟩ := IsCompact.exists_bound_of_continuousOn isCompact_Icc hf.continuousOn
  obtain ⟨c2, hc2⟩ := IsCompact.exists_bound_of_continuousOn isCompact_Icc
      (hf.continuousOn_iteratedDerivWithin (m := 2) (n := 2) (by norm_num) hU)
  have hM0 : ∀ x ∈ Set.Icc (0 : ℝ) (π / 2), |f x| ≤ max c0 0 := fun x hx =>
    le_trans (by simpa [Real.norm_eq_abs] using hc0 x hx) (le_max_left _ _)
  have hM2 : ∀ x ∈ Set.Icc (0 : ℝ) (π / 2),
      |iteratedDerivWithin 2 f (Set.Icc 0 (π / 2)) x| ≤ max c2 0 := fun x hx =>
    le_trans (by simpa [Real.norm_eq_abs] using hc2 x hx) (le_max_left _ _)
  set K : ℝ := max c2 0 + 4 * max c0 0 with hKdef
  have hKnn : 0 ≤ K := by
    rw [hKdef]
    have h1' := le_max_right c2 0
    have h2' := le_max_right c0 0
    linarith
  have hbd : ∀ s ∈ Set.Icc 0 (π / 2),
      |iteratedDerivWithin 2 f (Set.Icc 0 (π / 2)) s + 4 * f s| ≤ K := by
    intro s hs
    have h2 := hM2 s hs
    have h0 := hM0 s hs
    rw [hKdef]
    calc |iteratedDerivWithin 2 f (Set.Icc 0 (π / 2)) s + 4 * f s|
        ≤ |iteratedDerivWithin 2 f (Set.Icc 0 (π / 2)) s| + |4 * f s| := abs_add_le _ _
      _ = |iteratedDerivWithin 2 f (Set.Icc 0 (π / 2)) s| + 4 * |f s| := by
            rw [abs_mul]; norm_num
      _ ≤ max c2 0 + 4 * max c0 0 := by linarith
  obtain ⟨C1, hC1nn, hC1a, hC1b, hC1c⟩ := htU_endpoint_bounds f hf h1 hcomp1 hcomp2
  have hphi := htU_phi_bound f hf h1 K hKnn hbd
  set C : ℝ := 8 * (C1 + K + 1) with hCdef
  have hCnn : 0 ≤ C := by rw [hCdef]; nlinarith [hC1nn, hKnn]
  have hC1C : C1 ≤ C := by rw [hCdef]; nlinarith [hC1nn, hKnn]
  have hC1piC : C1 * π / 4 ≤ C := by
    rw [hCdef]; nlinarith [hC1nn, hKnn, Real.pi_pos, Real.pi_le_four]
  have hK2C : K / 2 ≤ C := by rw [hCdef]; nlinarith [hC1nn, hKnn]
  have hsumC : C1 + C1 * π + 2 * K ≤ C := by
    rw [hCdef]; nlinarith [hC1nn, hKnn, Real.pi_pos, Real.pi_le_four]
  -- the bound on `u'`
  have hderivhtU : ∀ x ∈ Set.Ioo (π / 4) (π / 2), |deriv (htU f) x| ≤ K / 2 := by
    intro x hx
    have hxIoo : x ∈ Set.Ioo (0 : ℝ) (π / 2) :=
      ⟨lt_trans (by linarith [Real.pi_pos] : (0 : ℝ) < π / 4) hx.1, hx.2⟩
    have hsin_eq : Real.sin (2 * x) = Real.sin (2 * (π / 2 - x)) := by
      rw [show 2 * x = π - 2 * (π / 2 - x) by ring, Real.sin_pi_sub]
    have hsinpos : 0 < Real.sin (2 * x) := by
      rw [hsin_eq]
      exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.2]) (by linarith [hx.1, Real.pi_pos])
    have hs2pos : 0 < (Real.sin (2 * x)) ^ 2 := pow_pos hsinpos 2
    have hφ : |deriv f x * Real.sin (2 * x) - 2 * Real.cos (2 * x) * f x| ≤ K * Real.cos x ^ 2 := by
      have h := hphi x hxIoo
      rwa [← hcomp1 x hxIoo] at h
    have hval : deriv (htU f) x
        = (deriv f x * Real.sin (2 * x) - 2 * Real.cos (2 * x) * f x) / (Real.sin (2 * x)) ^ 2 := by
      rw [eq_div_iff (ne_of_gt hs2pos), mul_comm]
      exact hid1 x hxIoo
    rw [hval, abs_div, abs_of_pos hs2pos]
    have hcospos : 0 < Real.cos x :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [hx.1, Real.pi_pos], by linarith [hx.2]⟩
    have hsx2 : (1 : ℝ) / 2 ≤ Real.sin x ^ 2 := sin_sq_ge_half (le_of_lt hx.1) (le_of_lt hx.2)
    have hcos : Real.cos x ^ 2 / (Real.sin (2 * x)) ^ 2 = 1 / (4 * Real.sin x ^ 2) := by
      rw [Real.sin_two_mul]
      have hcx : Real.cos x ≠ 0 := ne_of_gt hcospos
      have hsx : Real.sin x ≠ 0 := by
        intro h0; rw [h0] at hsx2; norm_num at hsx2
      field_simp
      ring
    have hhalf : 1 / (4 * Real.sin x ^ 2) ≤ 1 / 2 := by
      rw [div_le_iff₀ (by nlinarith [hsx2] : (0 : ℝ) < 4 * Real.sin x ^ 2)]
      nlinarith [hsx2]
    have hstep : |deriv f x * Real.sin (2 * x) - 2 * Real.cos (2 * x) * f x| / (Real.sin (2 * x)) ^ 2
        ≤ K * (Real.cos x ^ 2 / (Real.sin (2 * x)) ^ 2) := by
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_right hφ (le_of_lt hs2pos)
    have hstep2 : K * (Real.cos x ^ 2 / (Real.sin (2 * x)) ^ 2) ≤ K * (1 / 2) :=
      mul_le_mul_of_nonneg_left (hcos.le.trans hhalf) hKnn
    exact le_trans hstep (le_trans hstep2 (by linarith))
  refine ⟨C, π / 4, hCnn, by linarith [Real.pi_pos], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    have hx4 : x ∈ Set.Ioo (π / 4) (π / 2) := ⟨by linarith [hx.1], hx.2⟩
    have ht : 0 ≤ π / 2 - x := by linarith [hx.2]
    exact le_trans (hC1a x hx4) (mul_le_mul_of_nonneg_right hC1C ht)
  · intro x hx
    have hx4 : x ∈ Set.Ioo (π / 4) (π / 2) := ⟨by linarith [hx.1], hx.2⟩
    have ht : 0 ≤ π / 2 - x := by linarith [hx.2]
    exact le_trans (hC1b x hx4) (mul_le_mul_of_nonneg_right hC1C ht)
  · intro x hx
    have hx4 : x ∈ Set.Ioo (π / 4) (π / 2) := ⟨by linarith [hx.1], hx.2⟩
    exact le_trans (hC1c x hx4) hC1C
  · intro x hx
    have hx4 : x ∈ Set.Ioo (π / 4) (π / 2) := ⟨by linarith [hx.1], hx.2⟩
    have ht0 : 0 < π / 2 - x := by linarith [hx.2]
    have hsin_eq : Real.sin (2 * x) = Real.sin (2 * (π / 2 - x)) := by
      rw [show 2 * x = π - 2 * (π / 2 - x) by ring, Real.sin_pi_sub]
    have hsinpos : 0 < Real.sin (2 * x) := by
      rw [hsin_eq]
      exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.2]) (by linarith [hx.1, Real.pi_pos])
    have hlow : (4 / π) * (π / 2 - x) ≤ Real.sin (2 * x) := by
      rw [hsin_eq]
      have h := Real.mul_le_sin (x := 2 * (π / 2 - x)) (by linarith [hx.2]) (by linarith [hx.1, Real.pi_pos])
      convert h using 1
      ring
    have hmain : |htU f x| = |f x| / Real.sin (2 * x) := by
      simp only [htU, abs_div, abs_of_pos hsinpos]
    rw [hmain]
    have hft : |f x| ≤ C1 * (π / 2 - x) := hC1a x hx4
    have h4pi : 0 < (4 / π) * (π / 2 - x) := mul_pos (by positivity) ht0
    have hstep : |f x| / Real.sin (2 * x) ≤ C1 * (π / 2 - x) / ((4 / π) * (π / 2 - x)) :=
      div_le_div₀ (by positivity) hft h4pi hlow
    have heq : C1 * (π / 2 - x) / ((4 / π) * (π / 2 - x)) = C1 * π / 4 := by
      have hpi : (π : ℝ) ≠ 0 := ne_of_gt Real.pi_pos
      have ht : π / 2 - x ≠ 0 := ne_of_gt ht0
      rw [mul_div_mul_right C1 (4 / π) ht]
      field_simp
    exact le_trans (le_trans hstep (le_of_eq heq)) hC1piC
  · intro x hx
    have hx4 : x ∈ Set.Ioo (π / 4) (π / 2) := ⟨by linarith [hx.1], hx.2⟩
    exact le_trans (hderivhtU x hx4) hK2C
  · intro x hx
    have hxIoo : x ∈ Set.Ioo (0 : ℝ) (π / 2) := ⟨by linarith [hx.1, Real.pi_pos], hx.2⟩
    have hx4 : x ∈ Set.Ioo (π / 4) (π / 2) := ⟨by linarith [hx.1], hx.2⟩
    rw [hid2 x hxIoo]
    have h1' : |deriv (deriv f) x| ≤ C1 := hC1c x hx4
    have h0' : |f x| ≤ C1 * (π / 2 - x) := hC1a x hx4
    have h2' : |deriv (htU f) x| ≤ K / 2 := hderivhtU x hx4
    have ht4 : π / 2 - x ≤ π / 4 := by linarith [hx.1]
    have hcos1 : |Real.cos (2 * x)| ≤ 1 := Real.abs_cos_le_one (2 * x)
    have hb4 : |4 * Real.cos (2 * x) * deriv (htU f) x| ≤ 4 * (K / 2) := by
      rw [abs_mul, abs_mul, show |(4 : ℝ)| = 4 from abs_of_nonneg (by norm_num)]
      calc 4 * |Real.cos (2 * x)| * |deriv (htU f) x| ≤ 4 * 1 * (K / 2) := by
            apply mul_le_mul
            · linarith
            · exact h2'
            · exact abs_nonneg _
            · norm_num
        _ = 4 * (K / 2) := by ring
    have hb0 : |4 * f x| ≤ 4 * (C1 * (π / 2 - x)) := by
      rw [abs_mul, show |(4 : ℝ)| = 4 from abs_of_nonneg (by norm_num)]
      exact mul_le_mul_of_nonneg_left h0' (by norm_num)
    have htri : |deriv (deriv f) x + 4 * f x - 4 * Real.cos (2 * x) * deriv (htU f) x|
        ≤ |deriv (deriv f) x + 4 * f x| + |4 * Real.cos (2 * x) * deriv (htU f) x| := by
      rw [sub_eq_add_neg, ← abs_neg (4 * Real.cos (2 * x) * deriv (htU f) x)]
      exact abs_add_le _ _
    have htri2 : |deriv (deriv f) x + 4 * f x| ≤ |deriv (deriv f) x| + |4 * f x| :=
      abs_add_le _ _
    have hfin : C1 + 4 * (C1 * (π / 2 - x)) + 4 * (K / 2) ≤ C := by
      have h4t : 4 * (C1 * (π / 2 - x)) ≤ C1 * π := by nlinarith [hC1nn, ht4]
      linarith [h4t, hsumC]
    linarith [htri, htri2, h1', hb0, hb4, hfin]

end Work.Elliptic
