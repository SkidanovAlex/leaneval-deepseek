import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Order.CompletePartialOrder

namespace Commons.Analysis.Calculus.Taylor

open Filter Asymptotics
open scoped Topology

theorem taylor_two_isLittleO {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) :
    (fun y => f y - f x - fderiv ℝ f x (y - x)
        - (1 / 2) * (fderiv ℝ (fderiv ℝ f) x) (y - x) (y - x))
      =o[nhds x] (fun y => ‖y - x‖ ^ 2) := by
  obtain ⟨u, hu_nhds, hu⟩ := hf.contDiffOn (m := 2) le_rfl (by simp)
  obtain ⟨t, htu, ht_open, hxt⟩ := mem_nhds_iff.1 hu_nhds
  obtain ⟨r, hrpos, hr⟩ := Metric.mem_nhds_iff.1 (ht_open.mem_nhds hxt)
  set s : Set E := Metric.ball x r with hs
  have hs_open : IsOpen s := by rw [hs]; exact Metric.isOpen_ball
  have hxs : x ∈ s := by rw [hs]; exact Metric.mem_ball_self hrpos
  have hC2 : ContDiffOn ℝ 2 f s := hu.mono (fun y hy => htu (hr (by rw [hs] at hy; exact hy)))
  have hs_conv : Convex ℝ s := by rw [hs]; exact convex_ball x r
  have hs_nhds : s ∈ 𝓝 x := hs_open.mem_nhds hxs
  have hf_diff : ∀ y ∈ s, DifferentiableAt ℝ f y := fun y hy =>
    (hC2.contDiffAt (hs_open.mem_nhds hy)).differentiableAt (by norm_num)
  have hfderiv_diff : ∀ y ∈ s, DifferentiableAt ℝ (fderiv ℝ f) y := fun y hy =>
    ((hC2.contDiffAt (hs_open.mem_nhds hy)).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hcont2 : ContinuousAt (fderiv ℝ (fderiv ℝ f)) x :=
    ((hf.fderiv_right (m := 1) (by norm_num)).fderiv_right (m := 0) (by norm_num)).continuousAt
  set L : E →L[ℝ] ℝ := fderiv ℝ f x with hL
  set B : E →L[ℝ] E →L[ℝ] ℝ := fderiv ℝ (fderiv ℝ f) x with hB
  have hBsymm : ∀ v w : E, B v w = B w v := by
    intro v w
    have h := (hf.isSymmSndFDerivAt (by simp : minSmoothness ℝ 2 ≤ (2 : WithTop ℕ∞))).eq v w
    rwa [← hB] at h
  set A : E → (E →L[ℝ] ℝ) := (fun y => fderiv ℝ f y - L) - (fun y => B (y - x)) with hA
  set A' : E → (E →L[ℝ] (E →L[ℝ] ℝ)) := fun y => fderiv ℝ (fderiv ℝ f) y - B with hA'
  have hA_deriv : ∀ y ∈ s, HasFDerivWithinAt A (A' y) s y := by
    intro y hy
    have h1 : HasFDerivAt (fun z : E => fderiv ℝ f z - L) (fderiv ℝ (fderiv ℝ f) y) y :=
      (hfderiv_diff y hy).hasFDerivAt.sub_const L
    have h2 : HasFDerivAt (fun z : E => B (z - x)) B y :=
      (hasFDerivAt_comp_sub (f := (⇑B : E → E →L[ℝ] ℝ)) (f' := B) (x := y) x).2
        (ContinuousLinearMap.hasFDerivAt B)
    have h := h1.sub h2
    exact h.hasFDerivWithinAt
  -- little-o for A'
  have hA'_x : A' x = 0 := by simp [hA', hB]
  have hA'_cont : ContinuousAt A' x := by
    have h := hcont2.sub_const B
    exact h
  have hA'_littleO : A' =o[𝓝[s] x] (fun y => ‖y - x‖ ^ (0:ℕ)) := by
    show A' =o[𝓝[s] x] (fun _ => (1:ℝ))
    refine (isLittleO_one_iff (F := ℝ) (E''' := E →L[ℝ] (E →L[ℝ] ℝ))).mpr ?_
    have htend : Tendsto A' (𝓝[s] x) (𝓝 0) := by
      have hh := hA'_cont.tendsto
      rw [hA'_x] at hh
      exact hh.mono_left nhdsWithin_le_nhds
    exact htend
  have hA_app := hs_conv.isLittleO_pow_succ hxs hA_deriv hA'_littleO
  -- hA_app : (fun y => A y - A x) =o[𝓝[s] x] (fun y => ‖y-x‖^(0+1))
  have hAx : A x = 0 := by simp [hA, hL, hB]
  have hA_littleO : A =o[𝓝[s] x] (fun y => ‖y - x‖ ^ (1:ℕ)) := by
    have h := hA_app
    simp only [hAx, sub_zero] at h
    simpa using h
  set G : E → ℝ := fun y => f y - f x - L (y - x) - (1/2) * (B (y - x) (y - x)) with hG
  have hG_deriv : ∀ y ∈ s, HasFDerivWithinAt G (A y) s y := by
    intro y hy
    have h1 : HasFDerivAt (fun z : E => f z - f x) (fderiv ℝ f y) y :=
      (hf_diff y hy).hasFDerivAt.sub_const (f x)
    have h2 : HasFDerivAt (fun z : E => L (z - x)) L y :=
      (hasFDerivAt_comp_sub (f := (⇑L : E → ℝ)) (f' := L) (x := y) x).2
        (ContinuousLinearMap.hasFDerivAt L)
    have hP : HasFDerivAt (fun z : E => B (z - x) (z - x)) (B (y - x) + B.flip (y - x)) y := by
      have hc : HasFDerivAt (fun z : E => B (z - x)) B y :=
        (hasFDerivAt_comp_sub (f := (⇑B : E → E →L[ℝ] ℝ)) (f' := B) (x := y) x).2
          (ContinuousLinearMap.hasFDerivAt B)
      have hu : HasFDerivAt (fun z : E => z - x) (ContinuousLinearMap.id ℝ E) y :=
        hasFDerivAt_sub_const x
      have h := hc.clm_apply hu
      rw [ContinuousLinearMap.comp_id] at h
      exact h
    have hPsymm : B (y - x) + B.flip (y - x) = (2 : ℝ) • B (y - x) := by
      ext v
      simp only [add_apply, smul_apply,
        ContinuousLinearMap.flip_apply]
      rw [hBsymm v (y - x)]
      ring
    have hP2 : HasFDerivAt (fun z : E => B (z - x) (z - x)) ((2 : ℝ) • B (y - x)) y := by
      rw [hPsymm] at hP; exact hP
    have h3 : HasFDerivAt (fun z : E => (1/2) * (B (z - x) (z - x))) (B (y - x)) y := by
      have h := hP2.const_mul (1/2 : ℝ)
      have hsm : (1/2 : ℝ) • ((2:ℝ) • B (y - x)) = B (y - x) := by
        rw [smul_smul]; norm_num
      rw [hsm] at h
      exact h
    have hcomb : HasFDerivAt G (A y) y := (h1.sub h2).sub h3
    exact hcomb.hasFDerivWithinAt
  have hG_app := hs_conv.isLittleO_pow_succ hxs hG_deriv hA_littleO
  have hGx : G x = 0 := by simp [hG, hL, hB]
  have hG_littleO : G =o[𝓝[s] x] (fun y => ‖y - x‖ ^ 2) := by
    have h := hG_app
    simp only [hGx, sub_zero] at h
    simpa using h
  rw [(nhdsWithin_eq_nhds).mpr hs_nhds] at hG_littleO
  exact hG_littleO


end Commons.Analysis.Calculus.Taylor