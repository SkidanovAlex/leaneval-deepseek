import Mathlib
import Submission.CDTPlan.InterfacesA
import Submission.Work.ANum3.argument_principle_local

/-! Z4 -- annulus zero-free.

`f := φ_A + 1/72` is analytic on `ball 0 (500/491)`, nonvanishing on the unit circle, and
`∮_{|z|=1} logDeriv f = 2πi`.  The argument principle
(`Work.ANum3.argument_principle_fallback`, in `Submission/Work/ANum3/argument_principle_local.lean`)
says that this integral is `2πi`
times the divisor of `f` on `closedBall 0 1`, so that divisor sum is `1`.  The inner uniqueness
hypothesis (`hI`) says the only zero of `f` in `ball 0 (1/1000)` is the simple zero `z₀`; since the
divisor of an analytic function is nonnegative and is `1` at a simple zero, a further zero in
`closedBall 0 1` would contribute at least one more, a contradiction. -/

namespace Work.ANum3

open Submission.CDTPlan Complex Metric

/-- The divisor of an analytic function at a simple zero is `1`. -/
private lemma divisor_eq_one_of_simple_zero {f : ℂ → ℂ} {U : Set ℂ} {z₀ : ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hz₀ : z₀ ∈ U) (hzero : f z₀ = 0) (hd : deriv f z₀ ≠ 0) :
    (MeromorphicOn.divisor f U) z₀ = 1 := by
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hf hz₀,
    (hf z₀ hz₀).analyticOrderAt_eq_one_of_zero_deriv_ne_zero hzero hd]
  norm_num

/-- At a zero of finite order the divisor is positive. -/
private lemma one_le_divisor_of_zero {f : ℂ → ℂ} {U : Set ℂ} {z : ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hz : z ∈ U) (hzero : f z = 0)
    (hfin : analyticOrderAt f z ≠ ⊤) :
    1 ≤ (MeromorphicOn.divisor f U) z := by
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hf hz, ← Nat.cast_analyticOrderNatAt hfin]
  rw [ENat.map_natCast, WithTop.untop₀_coe]
  have h1 : 1 ≤ analyticOrderNatAt f z := by
    rw [Nat.one_le_iff_ne_zero]
    intro h0
    have h2 : analyticOrderAt f z = 0 := by
      rw [← Nat.cast_analyticOrderNatAt hfin, h0]
      simp
    exact ((hf z hz).analyticOrderAt_eq_zero).mp h2 hzero
  exact_mod_cast h1

theorem phiA_annulus_zero_free
    (hA : AnalyticOnNhd ℂ phiA (ball 0 (500 / 491)))
    (hW : (∀ z : ℂ, ‖z‖ = 1 → phiA z + 1 / 72 ≠ 0) ∧
      circleIntegral (fun z => logDeriv (fun w => phiA w + 1 / 72) z) 0 1 =
        2 * (Real.pi : ℂ) * Complex.I)
    (hI : ∃ z₀ ∈ ball (0 : ℂ) (1 / 1000), phiA z₀ + 1 / 72 = 0 ∧
      deriv (fun w => phiA w + 1 / 72) z₀ ≠ 0 ∧
      ∀ z ∈ ball (0 : ℂ) (1 / 1000), phiA z + 1 / 72 = 0 → z = z₀) :
    ∀ z : ℂ, 1 / 1000 ≤ ‖z‖ → ‖z‖ ≤ 1 → phiA z ≠ -1 / 72 := by
  obtain ⟨z₀, hz₀ball, hz₀f, hz₀d, huniq⟩ := hI
  have hz₀norm : ‖z₀‖ < 1 / 1000 := by
    simpa [mem_ball, dist_eq_norm] using hz₀ball
  set f : ℂ → ℂ := fun w => phiA w + 1 / 72 with hfdef
  have hf_apply : ∀ z, f z = phiA z + 1 / 72 := by intro z; rw [hfdef]
  have hfA : AnalyticOnNhd ℂ f (ball 0 (500 / 491)) := by
    have h := hA.add (analyticOnNhd_const (v := (1 / 72 : ℂ)) (s := ball (0 : ℂ) (500 / 491)))
    rw [hfdef]
    exact h
  have hne1 : ∀ z : ℂ, ‖z‖ = 1 → f z ≠ 0 := by
    intro z hz h
    exact hW.1 z hz (by rw [← hf_apply z]; exact h)
  have hwind : circleIntegral (fun z => logDeriv f z) 0 1 = 2 * (Real.pi : ℂ) * Complex.I := by
    simpa [hfdef] using hW.2
  have hAP := Work.ANum3.argument_principle_fallback (R := 500 / 491) (ρ := 1)
    (by norm_num) (by norm_num) hfA hne1
  have htwo : 2 * (Real.pi : ℂ) * Complex.I ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (by norm_num) ?_) Complex.I_ne_zero
    exact_mod_cast Real.pi_ne_zero
  have hsum : (∑ᶠ u : ℂ, ((MeromorphicOn.divisor f (closedBall (0 : ℂ) 1) u : ℤ) : ℂ)) = 1 := by
    refine mul_left_cancel₀ htwo ?_
    rw [mul_one]
    exact hAP.symm.trans hwind
  have hf1 : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) 1) :=
    hfA.mono (Metric.closedBall_subset_ball (by norm_num))
  have hSfin : (MeromorphicOn.divisor f (closedBall (0 : ℂ) 1)).support.Finite :=
    MeromorphicOn.divisor_support_finite_of_subset hf1.meromorphicOn (isCompact_closedBall (0 : ℂ) 1)
      (subset_refl _)
  set D : ℂ → ℤ := fun u => MeromorphicOn.divisor f (closedBall (0 : ℂ) 1) u with hDdef
  let S : Finset ℂ := hSfin.toFinset
  have hmemS : ∀ {u : ℂ}, D u ≠ 0 → u ∈ S := by
    intro u hu
    exact hSfin.mem_toFinset.mpr (show D u ≠ 0 from hu)
  have hsupp : Function.support (fun u : ℂ => ((D u : ℤ) : ℂ)) ⊆ ↑S := by
    intro u hu
    exact hmemS (fun h0 => hu (by simp [h0]))
  have hsum_finset : ∑ u ∈ S, ((D u : ℤ) : ℂ) = 1 := by
    rw [← (finsum_eq_sum_of_support_subset (fun u : ℂ => ((D u : ℤ) : ℂ)) (s := S) hsupp)]
    exact hsum
  have hsum_int : ∑ u ∈ S, D u = 1 := by
    apply Int.cast_injective (α := ℂ)
    push_cast
    exact hsum_finset
  have hz₀mem1 : z₀ ∈ closedBall (0 : ℂ) 1 := by
    rw [mem_closedBall, dist_eq_norm, sub_zero]
    linarith
  have hz₀f0 : f z₀ = 0 := by rw [hfdef]; exact hz₀f
  have hz₀d0 : deriv f z₀ ≠ 0 := by rw [hfdef]; exact hz₀d
  have hDz₀ : D z₀ = 1 := by
    rw [hDdef]
    exact divisor_eq_one_of_simple_zero hf1 hz₀mem1 hz₀f0 hz₀d0
  have hz₀S : z₀ ∈ S := hmemS (by rw [hDz₀]; norm_num)
  have hsum_erase : ∑ u ∈ S.erase z₀, D u = 0 := by
    have h := Finset.sum_erase_add S D hz₀S
    rw [hsum_int, hDz₀] at h
    linarith
  have hftop : ∀ z ∈ closedBall (0 : ℂ) 1, analyticOrderAt f z ≠ ⊤ := by
    intro z hz
    have h1mem : (1 : ℂ) ∈ ball (0 : ℂ) (500 / 491) := by
      have h : ‖(1 : ℂ) - 0‖ < 500 / 491 := by norm_num
      simpa [mem_ball, dist_eq_norm] using h
    have hord1 : analyticOrderAt f 1 ≠ ⊤ := by
      have h0 : analyticOrderAt f 1 = 0 :=
        ((hfA 1 h1mem).analyticOrderAt_eq_zero).mpr (hne1 1 (by norm_num))
      rw [h0]; exact ENat.zero_ne_top
    have hzmem : z ∈ ball (0 : ℂ) (500 / 491) := by
      have hzle : ‖z‖ ≤ 1 := by simpa [mem_closedBall, dist_eq_norm] using hz
      have h : ‖z - 0‖ < 500 / 491 := by simp; linarith
      simpa [mem_ball, dist_eq_norm] using h
    exact AnalyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected hfA Metric.isPreconnected_ball
      h1mem hzmem hord1
  intro z hz1 hz2 hcon
  have hzmem : z ∈ closedBall (0 : ℂ) 1 := by
    rw [mem_closedBall, dist_eq_norm, sub_zero]
    exact hz2
  have hfz0 : f z = 0 := by rw [hf_apply, hcon]; ring
  have hDz : D z ≠ 0 := by
    have h : (1 : ℤ) ≤ D z := by
      show (1 : ℤ) ≤ MeromorphicOn.divisor f (closedBall (0 : ℂ) 1) z
      exact one_le_divisor_of_zero hf1 hzmem hfz0 (hftop z hzmem)
    omega
  have hz_ne : z ≠ z₀ := by
    intro h
    rw [h] at hz1
    linarith
  have hzT : z ∈ S.erase z₀ := Finset.mem_erase.mpr ⟨hz_ne, hmemS hDz⟩
  have hDz0 : D z = 0 := by
    have hnn : ∀ u ∈ S.erase z₀, (0 : ℤ) ≤ D u := by
      intro u _
      rw [hDdef]
      exact MeromorphicOn.AnalyticOnNhd.divisor_nonneg hf1 u
    exact (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum_erase z hzT
  exact hDz hDz0

end Work.ANum3
