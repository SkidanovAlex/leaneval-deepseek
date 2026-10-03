import Mathlib
import Submission.Lib.Unif2.Commons.Analysis.Complex.Harmonic.harnack_inequality
import Submission.Lib.Unif2.Commons.Analysis.Complex.Harmonic.harmonic_of_circleAverage
import Submission.Lib.Unif2.Commons.Analysis.Complex.Harmonic.circleAverage_tendsto_of_tendstoUniformlyOn

noncomputable section
open Set Metric Complex InnerProductSpace Filter
open scoped Real Topology

namespace Commons.Analysis.Complex.Harmonic

/-- **Harnack's convergence theorem**: the pointwise limit of a monotonically increasing
sequence of harmonic functions on `ball 0 R` (finite-valued everywhere on the ball) is again
harmonic on the ball. -/
theorem harmonicOnNhd_of_monotone_pointwise_limit {v : ℕ → ℂ → ℝ} {u : ℂ → ℝ} {R : ℝ}
    (hv : ∀ n : ℕ, InnerProductSpace.HarmonicOnNhd (v n) (ball (0 : ℂ) R))
    (hmono : ∀ n : ℕ, ∀ z : ℂ, ‖z‖ < R → v n z ≤ v (n + 1) z)
    (hlim : ∀ z : ℂ, ‖z‖ < R → Tendsto (fun n : ℕ => v n z) atTop (𝓝 (u z))) :
    InnerProductSpace.HarmonicOnNhd u (ball (0 : ℂ) R) := by
  by_cases hRpos : 0 < R
  · -- monotonicity of the sequence (from consecutive to arbitrary indices)
    have hvmono_inc : ∀ (m : ℕ), ∀ z : ℂ, ‖z‖ < R → ∀ k : ℕ, v m z ≤ v (m + k) z := by
      intro m z hz k
      induction k with
      | zero => rfl
      | succ k ih =>
          have h2 : v (m + k) z ≤ v (m + k + 1) z := hmono (m + k) z hz
          have heq : m + k + 1 = m + (k + 1) := by omega
          simpa [heq] using le_trans ih h2
    have hvmono : ∀ ⦃m n : ℕ⦄, m ≤ n → ∀ z : ℂ, ‖z‖ < R → v m z ≤ v n z := by
      intro m n hmn z hz
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
      exact hvmono_inc m z hz k
    have hcl0 : ‖(0 : ℂ)‖ < R := by simpa using hRpos
    have hv0 : Tendsto (fun n : ℕ => v n 0) atTop (𝓝 (u 0)) := hlim 0 hcl0
    -- for every z in the ball, the monotone sequence is bounded above by its limit
    have hleU : ∀ z : ℂ, ‖z‖ < R → ∀ n : ℕ, v n z ≤ u z := by
      intro z hzR n
      refine ge_of_tendsto (hlim z hzR) ?_
      filter_upwards [eventually_ge_atTop n] with k hk
      exact hvmono (m := n) (n := k) hk z hzR
    -- uniform convergence on every closedBall 0 ρ with 0 ≤ ρ < R
    have tendstoUniformlyOn_closedBall : ∀ ⦃ρ : ℝ⦄, 0 ≤ ρ → ρ < R →
        TendstoUniformlyOn (fun n : ℕ => v n) u atTop (closedBall (0 : ℂ) ρ) := by
      intro ρ hρ0 hρR
      rcases exists_between hρR with ⟨ρ', hρρ', hρ'R⟩
      have hρ'pos : 0 < ρ' := lt_of_le_of_lt hρ0 hρρ'
      let C : ℝ := (ρ' + ρ) / (ρ' - ρ)
      have hCnonneg : 0 ≤ C := by
        dsimp [C]
        exact div_nonneg (by nlinarith) (by nlinarith)
      have hsubCl : closedBall (0 : ℂ) ρ' ⊆ ball (0 : ℂ) R := by
        intro x hx
        have hxle : ‖x‖ ≤ ρ' := by simpa [dist_eq_norm] using (mem_closedBall.mp hx)
        have hxlt : ‖x‖ < R := lt_of_le_of_lt hxle hρ'R
        simpa [mem_ball, dist_eq_norm] using hxlt
      -- Harnack bound for differences v n - v m on closedBall 0 ρ
      have hdiff_bound : ∀ ⦃m n : ℕ⦄, m ≤ n → ∀ z : ℂ, z ∈ closedBall (0 : ℂ) ρ →
          (v n z - v m z) ≤ C * (v n (0 : ℂ) - v m (0 : ℂ)) := by
        intro m n hmn z hz
        have hzle : ‖z‖ ≤ ρ := by simpa [dist_eq_norm] using (mem_closedBall.mp hz)
        let d : ℂ → ℝ := v n - v m
        have hd : InnerProductSpace.HarmonicOnNhd d (closedBall (0 : ℂ) ρ') := by
          dsimp [d]
          exact ((hv n).sub (hv m)).mono hsubCl
        have hdpos : ∀ w : ℂ, ‖w‖ ≤ ρ' → 0 ≤ d w := by
          intro w hwle
          have hwlt : ‖w‖ < R := lt_of_le_of_lt hwle hρ'R
          dsimp [d]
          exact sub_nonneg.mpr (hvmono hmn w hwlt)
        have hw : ‖z‖ < ρ' := lt_of_le_of_lt hzle hρρ'
        have harn := harnack_inequality (f := d) (R := ρ') hd hdpos (w := z) hw
        have hd0 : 0 ≤ d (0 : ℂ) := by
          dsimp [d]
          exact sub_nonneg.mpr (hvmono hmn (0 : ℂ) hcl0)
        have hden1 : 0 < ρ' - ‖z‖ := by nlinarith
        have hden2 : 0 < ρ' - ρ := by nlinarith
        have hKleC : ((ρ' + ‖z‖) / (ρ' - ‖z‖)) ≤ C := by
          dsimp [C]
          rw [div_le_div_iff₀ hden1 hden2]
          nlinarith [hρ0, hzle]
        calc
          v n z - v m z = d z := rfl
          _ ≤ ((ρ' + ‖z‖) / (ρ' - ‖z‖)) * d (0 : ℂ) := harn.2
          _ ≤ C * d (0 : ℂ) := mul_le_mul_of_nonneg_right hKleC hd0
          _ = C * (v n (0 : ℂ) - v m (0 : ℂ)) := by dsimp [d]
      -- limit n → ∞ of the Harnack bound
      have hovershoot : ∀ z : ℂ, z ∈ closedBall (0 : ℂ) ρ →
          ∀ m : ℕ, u z - v m z ≤ C * (u (0 : ℂ) - v m (0 : ℂ)) := by
        intro z hz m
        have hzR : ‖z‖ < R := lt_of_le_of_lt
          (by simpa [dist_eq_norm] using (mem_closedBall.mp hz)) hρR
        have hlimz : Tendsto (fun n : ℕ => v n z - v m z) atTop
            (𝓝 (u z - v m z)) := by
          simpa using (hlim z hzR).sub (tendsto_const_nhds (x := v m z))
        have hlim0 : Tendsto (fun n : ℕ => C * (v n (0 : ℂ) - v m (0 : ℂ))) atTop
            (𝓝 (C * (u (0 : ℂ) - v m (0 : ℂ)))) := by
          simpa using (tendsto_const_nhds (x := C)).mul ((hv0.sub (tendsto_const_nhds (x := v m (0 : ℂ)))))
        refine le_of_tendsto_of_tendsto hlimz hlim0 ?_
        filter_upwards [eventually_ge_atTop m] with n hmn
        exact hdiff_bound (m := m) (n := n) hmn z hz
      -- C * (u 0 - v m 0) → 0
      have hC0 : Tendsto (fun m : ℕ => C * (u (0 : ℂ) - v m (0 : ℂ))) atTop (𝓝 0) := by
        have hsub : Tendsto (fun m : ℕ => u (0 : ℂ) - v m (0 : ℂ)) atTop
            (𝓝 (u (0 : ℂ) - u (0 : ℂ))) :=
          (tendsto_const_nhds (x := u (0 : ℂ))).sub hv0
        simpa using (tendsto_const_nhds (x := C)).mul hsub
      -- the uniformity statement
      rw [Metric.uniformity_basis_dist.tendstoUniformlyOn_iff_of_uniformity]
      intro ε hε
      rcases (eventually_atTop.mp (hC0.eventually (Iio_mem_nhds hε))) with ⟨m₀, hm₀⟩
      filter_upwards [eventually_ge_atTop m₀] with n hnm₀
      intro z hz
      have hzR : ‖z‖ < R := lt_of_le_of_lt
        (by simpa [dist_eq_norm] using (mem_closedBall.mp hz)) hρR
      have hnonneg : 0 ≤ u z - v n z := sub_nonneg.mpr (hleU z hzR n)
      have hle : u z - v n z ≤ C * (u (0 : ℂ) - v m₀ (0 : ℂ)) := by
        calc
          u z - v n z ≤ u z - v m₀ z := by
            have : v m₀ z ≤ v n z := hvmono (m := m₀) (n := n) hnm₀ z hzR
            linarith
          _ ≤ C * (u (0 : ℂ) - v m₀ (0 : ℂ)) := hovershoot z hz m₀
      have hlt : C * (u (0 : ℂ) - v m₀ (0 : ℂ)) < ε := hm₀ m₀ (le_rfl)
      have hdist : dist (u z) (v n z) < ε := by
        rw [Real.dist_eq]
        rw [abs_of_nonneg hnonneg]
        exact lt_of_le_of_lt hle hlt
      simpa using hdist
    -- continuity of u on the open ball
    have huCont : ContinuousOn u (ball (0 : ℂ) R) := by
      refine continuousOn_of_forall_continuousAt ?_
      intro z hz
      have hzR : ‖z‖ < R := by simpa [mem_ball, dist_eq_norm] using hz
      rcases exists_between hzR with ⟨ρ, hzρ, hρR⟩
      have hρ0 : 0 ≤ ρ := by nlinarith [norm_nonneg z]
      have hUnif := tendstoUniformlyOn_closedBall hρ0 hρR
      have hfreq : ∃ᶠ n in atTop, ContinuousOn (v n) (closedBall (0 : ℂ) ρ) := by
        refine Filter.Frequently.of_forall ?_
        intro n
        exact (hv n).continuousOn.mono (by
          intro x hx
          have hxle : ‖x‖ ≤ ρ := by simpa [dist_eq_norm] using (mem_closedBall.mp hx)
          have hxlt : ‖x‖ < R := lt_of_le_of_lt hxle hρR
          simpa [mem_ball, dist_eq_norm] using hxlt)
      have hcontCl : ContinuousOn u (closedBall (0 : ℂ) ρ) :=
        hUnif.continuousOn hfreq
      have hcl_mem : closedBall (0 : ℂ) ρ ∈ 𝓝 z := by
        refine mem_of_superset ?_ Metric.ball_subset_closedBall
        exact isOpen_ball.mem_nhds (by simpa [mem_ball, dist_eq_norm] using hzρ)
      exact ContinuousOn.continuousAt hcontCl hcl_mem
    -- mean value property of u
    have hMV : ∀ p : ℂ, ‖p‖ < R → ∀ r : ℝ, 0 < r → ‖p‖ + r < R →
        Real.circleAverage u p r = u p := by
      intro p hpR r hr hpr
      let ρ : ℝ := ‖p‖ + r
      have hρ0 : 0 ≤ ρ := by dsimp [ρ]; positivity
      have hρR : ρ < R := by simpa [ρ] using hpr
      have hUnif := tendstoUniformlyOn_closedBall hρ0 hρR
      have hsphere_norm : ∀ x : ℂ, x ∈ sphere p r → ‖x‖ ≤ ‖p‖ + r := by
        intro x hx
        have hxr : ‖x - p‖ = r := by simpa [dist_eq_norm] using (mem_sphere.mp hx)
        have h := norm_add_le (x - p) p
        have hxeq : (x - p) + p = x := by ring
        rw [hxeq] at h
        rw [hxr] at h
        nlinarith
      have hclosed_norm : ∀ x : ℂ, x ∈ closedBall p r → ‖x‖ ≤ ‖p‖ + r := by
        intro x hx
        have hxr : ‖x - p‖ ≤ r := by simpa [dist_eq_norm] using (mem_closedBall.mp hx)
        have h := norm_add_le (x - p) p
        have hxeq : (x - p) + p = x := by ring
        rw [hxeq] at h
        nlinarith
      have hSphereSub : sphere p r ⊆ closedBall (0 : ℂ) ρ := by
        intro x hx
        have hxρ : ‖x‖ ≤ ρ := by
          have hxle := hsphere_norm x hx
          dsimp [ρ]
          nlinarith
        simpa [dist_eq_norm] using hxρ
      have hUnifSph : TendstoUniformlyOn (fun n : ℕ => v n) u atTop (sphere p r) :=
        hUnif.mono hSphereSub
      have hContSph : ∀ n : ℕ, ContinuousOn (v n) (sphere p r) := by
        intro n
        exact (hv n).continuousOn.mono (by
          intro x hx
          have hxlt : ‖x‖ < R := by
            have hxle := hsphere_norm x hx
            nlinarith [hpr]
          simpa [mem_ball, dist_eq_norm] using hxlt)
      have hAvgLim : Tendsto (fun n : ℕ => Real.circleAverage (v n) p r) atTop
          (𝓝 (Real.circleAverage u p r)) :=
        circleAverage_tendsto_of_tendstoUniformlyOn (r := r) hr hContSph hUnifSph
      -- forward mean value property for each v n
      have hMVn : ∀ n : ℕ, Real.circleAverage (v n) p r = v n p := by
        intro n
        have hclosed_sub : closedBall p r ⊆ ball (0 : ℂ) R := by
          intro x hx
          have hxlt : ‖x‖ < R := by
            have hxle := hclosed_norm x hx
            nlinarith [hpr]
          simpa [mem_ball, dist_eq_norm] using hxlt
        have hn : InnerProductSpace.HarmonicOnNhd (v n) (closedBall p r) :=
          (hv n).mono hclosed_sub
        have hn' : InnerProductSpace.HarmonicOnNhd (v n) (closedBall p |r|) := by
          simpa [abs_of_pos hr] using hn
        simpa using (InnerProductSpace.HarmonicOnNhd.circleAverage_eq (f := v n) (c := p) (R := r) hn')
      have hAvgUp : Tendsto (fun n : ℕ => Real.circleAverage (v n) p r) atTop (𝓝 (u p)) := by
        refine (hlim p hpR).congr' ?_
        filter_upwards with n
        exact (hMVn n).symm
      exact tendsto_nhds_unique hAvgLim hAvgUp
    exact harmonic_of_circleAverage (u := u) (R := R) huCont hMV
  · -- degenerate case R ≤ 0: the ball is empty
    intro z hz
    exfalso
    have hzR : ‖z‖ < R := by simpa [mem_ball, dist_eq_norm] using hz
    have hRle : R ≤ 0 := le_of_not_gt hRpos
    nlinarith [norm_nonneg z, hzR, hRle]

end Commons.Analysis.Complex.Harmonic
