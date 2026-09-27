import Mathlib
import Submission.Work.Drive.weakcase_deps

open Filter Set
open scoped Topology

namespace Work.Drive

open Classical

/-- **Superharmonicity of the clamped unit-pole potential.**

Let `h` be holomorphic on all of `X`, `y : X`, `c = chartAt ℂ y`, `a = c y`.  Suppose that in the
chart at `y` the function `h` factors as `h ∘ c.symm = (· - a)^k · ψ` near `a`, with `k ≥ 1` and
`m ≤ ‖ψ‖`, `m > 0`.  Then for any `0 < ρ ≤ r` the pasted function which is `(1/k) * (-log ‖h‖)`
on the chart ball of radius `ρ` and `(1/k) * clampedLogNorm h K` outside it, with
`K = max 0 (-log ((ρ/2)^k m))`, is superharmonic on `X \ {y}`. -/
theorem unitPoleSuperharmonic {X : Type*} [TopologicalSpace X] [T2Space X]
    [ConnectedSpace X] [SecondCountableTopology X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] {y : X} {h : X → ℂ}
    (hhol : Submission.HolomorphicOnX h Set.univ)
    {ρ r : ℝ} {k : ℕ} {ψ : ℂ → ℂ} {m : ℝ}
    (hρ : 0 < ρ) (hρr : ρ ≤ r) (hk : 1 ≤ k) (hm : 0 < m)
    (hsub : Metric.closedBall ((chartAt ℂ y) y) r ⊆ (chartAt ℂ y).target)
    (hfac : ∀ w : ℂ, dist w ((chartAt ℂ y) y) < r →
        (h ∘ (chartAt ℂ y).symm) w = (w - (chartAt ℂ y) y) ^ k * ψ w)
    (hψ : ∀ w : ℂ, dist w ((chartAt ℂ y) y) < r → m ≤ ‖ψ w‖) :
    Submission.SuperharmonicOnX
      (fun z : X => if z ∈ Submission.chartBall (chartAt ℂ y) ((chartAt ℂ y) y) ρ
        then (1 / (k : ℝ)) * (-Real.log ‖h z‖)
        else (1 / (k : ℝ)) *
          Work.SimplyConnected.ABS.clampedLogNorm h
            (max 0 (-(Real.log ((ρ / 2) ^ k * m)))) z)
      (Set.univ \ {y}) := by
  classical
  set c : OpenPartialHomeomorph X ℂ := chartAt ℂ y with hc
  set a : ℂ := c y with ha
  have hsrc : y ∈ c.source := mem_chart_source ℂ y
  have hcy : c y = a := rfl
  have hr : 0 < r := lt_of_lt_of_le hρ hρr
  have hkpos : (0 : ℝ) < (k : ℝ) := by
    have h1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  have hknn : 0 ≤ (1 : ℝ) / (k : ℝ) := div_nonneg zero_le_one hkpos.le
  have hρ2 : 0 < ρ / 2 := by linarith
  set K : ℝ := max 0 (-(Real.log ((ρ / 2) ^ k * m))) with hKdef
  have hKnn : 0 ≤ K := le_max_left _ _
  have hKge : -(Real.log ((ρ / 2) ^ k * m)) ≤ K := le_max_right _ _
  have hrm : 0 < (ρ / 2) ^ k * m := mul_pos (pow_pos hρ2 k) hm
  set D : Set X := Submission.chartBall c a ρ with hD
  have hDopen : IsOpen D := by rw [hD]; exact Submission.chartBall_isOpen c a ρ
  have hsubρ : Metric.closedBall a ρ ⊆ c.target :=
    (Metric.closedBall_subset_closedBall hρr).trans hsub
  have hclos : closure D = Submission.chartClosedBall c a ρ := by
    rw [hD]; exact Submission.closure_chartBall_eq_chartClosedBall hρ hsubρ
  set v : X → ℝ := fun x => if x ∈ D then (1 / (k : ℝ)) * (-Real.log ‖h x‖)
      else (1 / (k : ℝ)) * Work.SimplyConnected.ABS.clampedLogNorm h K x with hv
  -- ## local facts about `D`
  have hnormD : ∀ x ∈ D, ‖c x - a‖ < ρ := by
    intro x hx
    have h := hx.2
    simp only [Set.mem_preimage, Metric.mem_ball, dist_eq_norm] at h
    exact h
  have hdistD : ∀ x ∈ D, dist (c x) a < ρ := fun x hx => by
    rw [dist_eq_norm]; exact hnormD x hx
  have hfacD : ∀ x ∈ D, x ≠ y → h x = (c x - a) ^ k * ψ (c x) := by
    intro x hx hxy
    have h1 := hfac (c x) (by rw [dist_eq_norm]; exact lt_of_lt_of_le (hnormD x hx) hρr)
    have h2 : (h ∘ c.symm) (c x) = h x := by
      simp only [Function.comp_apply]; rw [c.left_inv hx.1]
    rw [← h2]; exact h1
  have hψlowD : ∀ x ∈ D, m ≤ ‖ψ (c x)‖ := fun x hx =>
    hψ (c x) (by rw [dist_eq_norm]; exact lt_of_lt_of_le (hnormD x hx) hρr)
  have hcx_ne : ∀ x ∈ D, x ≠ y → c x - a ≠ 0 := by
    intro x hx hxy h0
    exact hxy (c.injOn hx.1 hsrc (by rw [hcy]; exact sub_eq_zero.mp h0))
  have hneD : ∀ x ∈ D, x ≠ y → h x ≠ 0 := by
    intro x hx hxy
    rw [hfacD x hx hxy]
    have h1 : (c x - a) ^ k ≠ 0 := pow_ne_zero k (hcx_ne x hx hxy)
    have h2 : ψ (c x) ≠ 0 := by
      intro h0
      have h3 : ‖ψ (c x)‖ = 0 := by rw [h0, norm_zero]
      linarith [hψlowD x hx]
    exact mul_ne_zero h1 h2
  -- ## the clamp agrees with the honest potential on the outer annulus of `D`
  have hclamp : ∀ z ∈ c.source, ρ / 2 ≤ ‖c z - a‖ → ‖c z - a‖ < ρ →
      (1 / (k : ℝ)) * (-Real.log ‖h z‖)
        = (1 / (k : ℝ)) * Work.SimplyConnected.ABS.clampedLogNorm h K z := by
    intro z hzsrc hge hlt
    have hzD : z ∈ D := by
      rw [hD]
      exact ⟨hzsrc, by
        simp only [Set.mem_preimage, Metric.mem_ball, dist_eq_norm]; exact hlt⟩
    have hzpos : 0 < ‖c z - a‖ := lt_of_lt_of_le hρ2 hge
    have hzna : c z - a ≠ 0 := norm_pos_iff.mp hzpos
    have hzy : z ≠ y := by
      intro hzy; exact hzna (by rw [hzy, hcy]; simp)
    have hhz : h z = (c z - a) ^ k * ψ (c z) := hfacD z hzD hzy
    have hψlo := hψlowD z hzD
    have hbound : (ρ / 2) ^ k * m ≤ ‖h z‖ := by
      rw [hhz, norm_mul, norm_pow]
      have h1 : (ρ / 2) ^ k ≤ ‖c z - a‖ ^ k :=
        pow_le_pow_left₀ (le_of_lt hρ2) hge k
      exact mul_le_mul h1 hψlo hm.le (pow_nonneg (by linarith) k)
    have hlog : Real.log ((ρ / 2) ^ k * m) ≤ Real.log ‖h z‖ := Real.log_le_log hrm hbound
    have hle : -Real.log ‖h z‖ ≤ K := by linarith [neg_le_neg hlog]
    have hz0 : h z ≠ 0 := hneD z hzD hzy
    have hcl := Work.SimplyConnected.ABS.clampedLogNorm_of_le (g := h) (K := K) hz0 hle
    rw [hcl]
  -- ## continuity and superharmonicity of the pasted function
  have hev_in : ∀ p ∈ D, v =ᶠ[𝓝 p] (fun z => (1 / (k : ℝ)) * (-Real.log ‖h z‖)) := by
    intro p hp
    filter_upwards [hDopen.mem_nhds hp] with z hz
    simp only [hv]
    rw [if_pos hz]
  have hev_out : ∀ p ∉ closure D,
      v =ᶠ[𝓝 p] (fun z => (1 / (k : ℝ)) * Work.SimplyConnected.ABS.clampedLogNorm h K z) := by
    intro p hp
    have hopen : (closure D)ᶜ ∈ 𝓝 p := isClosed_closure.isOpen_compl.mem_nhds hp
    filter_upwards [hopen] with z hz
    have hzD : z ∉ D := fun h => hz (subset_closure h)
    simp only [hv]
    rw [if_neg hzD]
  have hfrontier : ∀ p ∈ closure D, p ∉ D → p ∈ c.source ∧ ‖c p - a‖ = ρ := by
    intro p hp hpD
    have hp' : p ∈ Submission.chartClosedBall c a ρ := by rw [← hclos]; exact hp
    have hpsrc : p ∈ c.source := hp'.1
    have hcle : ‖c p - a‖ ≤ ρ := by
      have h2 : c p ∈ Metric.closedBall a ρ := hp'.2
      rwa [Metric.mem_closedBall, dist_eq_norm] at h2
    have hcge : ρ ≤ ‖c p - a‖ := by
      by_contra hcon
      have hlt : ‖c p - a‖ < ρ := lt_of_not_ge hcon
      exact hpD (by
        rw [hD]
        exact ⟨hpsrc, by
          simp only [Set.mem_preimage, Metric.mem_ball, dist_eq_norm]; exact hlt⟩)
    exact ⟨hpsrc, le_antisymm hcle hcge⟩
  have hev_frontier : ∀ p ∈ closure D, p ∉ D →
      v =ᶠ[𝓝 p] (fun z => (1 / (k : ℝ)) * Work.SimplyConnected.ABS.clampedLogNorm h K z) := by
    intro p hp hpD
    obtain ⟨hpsrc, hpnorm⟩ := hfrontier p hp hpD
    have hN : (c.source ∩ {z : X | ρ / 2 < ‖c z - a‖}) ∈ 𝓝 p := by
      refine Filter.inter_mem (c.open_source.mem_nhds hpsrc) ?_
      have hcont : ContinuousAt (fun z : X => ‖c z - a‖) p :=
        ((c.continuousAt hpsrc).sub continuousAt_const).norm
      refine hcont.eventually (isOpen_Ioi.mem_nhds ?_)
      show ρ / 2 < ‖c p - a‖
      rw [hpnorm]; linarith
    filter_upwards [hN] with z hz
    obtain ⟨hzsrc, hzgt⟩ := hz
    by_cases hzD : z ∈ D
    · have hzlt : ‖c z - a‖ < ρ := hnormD z hzD
      have key := hclamp z hzsrc (le_of_lt hzgt) hzlt
      simp only [hv]
      rw [if_pos hzD, key]
    · simp only [hv]
      rw [if_neg hzD]
  have hv_cont : ContinuousOn v (Set.univ \ {y}) := by
    refine continuousOn_of_forall_continuousAt (fun p hp => ?_)
    by_cases hpD : p ∈ D
    · have hcont : ContinuousAt (fun z : X => (1 / (k : ℝ)) * (-Real.log ‖h z‖)) p := by
        have h1 : ContinuousAt (fun z : X => ‖h z‖) p := (hhol p (mem_univ p)).continuousAt.norm
        exact ((h1.log (norm_ne_zero_iff.mpr (hneD p hpD hp.2))).neg).const_mul _
      exact hcont.congr (hev_in p hpD).symm
    · by_cases hpcl : p ∈ closure D
      · have hcont : ContinuousAt (fun z : X => (1 / (k : ℝ)) *
            Work.SimplyConnected.ABS.clampedLogNorm h K z) p :=
          (Work.SimplyConnected.ABS.continuous_clampedLogNorm hhol K).continuousAt.const_mul _
        exact hcont.congr (hev_frontier p hpcl hpD).symm
      · have hcont : ContinuousAt (fun z : X => (1 / (k : ℝ)) *
            Work.SimplyConnected.ABS.clampedLogNorm h K z) p :=
          (Work.SimplyConnected.ABS.continuous_clampedLogNorm hhol K).continuousAt.const_mul _
        exact hcont.congr (hev_out p hpcl).symm
  have hv_sup : Submission.SuperharmonicOnX v (Set.univ \ {y}) := by
    refine ⟨hv_cont, fun p hp => ?_⟩
    by_cases hpD : p ∈ D
    · have hharm : Submission.HarmonicOnXAt (fun z : X => -Real.log ‖h z‖) p :=
        Submission.harmonicOnXAt_neg_log_norm (hhol p (mem_univ p)) (hneD p hpD hp.2)
      have h2 : Submission.SuperharmonicOnXAt
          (fun z : X => (1 / (k : ℝ)) * (-Real.log ‖h z‖)) p :=
        Submission.SuperharmonicOnXAt.const_mul hknn hharm.superharmonic
      exact Work.SimplyConnected.ABS.Submission.SuperharmonicOnXAt.congr h2 (hev_in p hpD).symm
    · have hsup : Submission.SuperharmonicOnXAt
          (fun z : X => (1 / (k : ℝ)) * Work.SimplyConnected.ABS.clampedLogNorm h K z) p :=
        Submission.SuperharmonicOnXAt.const_mul hknn
          ((Work.SimplyConnected.ABS.superharmonicOnX_clampedLogNorm hhol K).2 p (mem_univ p))
      by_cases hpcl : p ∈ closure D
      · exact Work.SimplyConnected.ABS.Submission.SuperharmonicOnXAt.congr hsup
          (hev_frontier p hpcl hpD).symm
      · exact Work.SimplyConnected.ABS.Submission.SuperharmonicOnXAt.congr hsup
          (hev_out p hpcl).symm
  exact hv_sup

end Work.Drive
