import Mathlib
import Submission.Work.EQ.EquiLocalDefs

namespace Work.EQ

open Filter _root_.Topology

/-- Points of a chart `E` (with `ψ₁ (E ζ) = w + κ ζ^k`) lying in `S` over `ψ₁ = u`, with `u ≠ u₁`
close to `u₁`, fall into any set that is a neighbourhood in `H0` of the fibre of `S` over `u₁`,
provided the chart centre `w` is different from `u₁`. -/
theorem leg_in_sec_of_centre_ne {a : ℝ} {h : ℂ → ℂ} {r : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hh : IsStableGerm a h r) {S T : Set ChainData} {u₁ : ℂ} (hu₁ : u₁ ≠ 0)
    (hSH : S ⊆ H0 a h)
    (hScl : ∀ q ∈ closure S, q ∈ H0 a h → q ∈ S)
    (hT : ∀ q ∈ S, q.2.1 = u₁ → T ∈ 𝓝[H0 a h] q)
    {E : ℂ → ChainData} {w κ : ℂ} {k : ℕ} (hE : IsChartData a h E w κ k) (hw : w ≠ u₁) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ u ∈ Metric.ball u₁ ρ, u ≠ u₁ → ∀ ζ ∈ Metric.ball (0 : ℂ) (1/2) \ {0},
      w + κ * ζ ^ k = u → E ζ ∈ S → E ζ ∈ T := by
  obtain ⟨hk, hκ, hEmem, hEinj, hEcont⟩ := hE
  -- Suppose no such radius exists; then there is a sequence of counterexamples.
  by_contra hcon
  have hforall : ∀ ρ : ℝ, 0 < ρ → ∃ u : ℂ, u ∈ Metric.ball u₁ ρ ∧ u ≠ u₁ ∧
      ∃ ζ : ℂ, ζ ∈ Metric.ball (0 : ℂ) (1 / 2) \ {0} ∧ w + κ * ζ ^ k = u ∧
        E ζ ∈ S ∧ E ζ ∉ T := by
    intro ρ hρ
    by_contra hbad
    apply hcon
    refine ⟨ρ, hρ, ?_⟩
    intro u hu hu1 ζ hζ heq hEzS
    by_contra hno
    exact hbad ⟨u, hu, hu1, ζ, hζ, heq, hEzS, hno⟩
  have hex : ∀ n : ℕ, ∃ u : ℂ, u ∈ Metric.ball u₁ (1 / ((n : ℝ) + 1)) ∧ u ≠ u₁ ∧
      ∃ ζ : ℂ, ζ ∈ Metric.ball (0 : ℂ) (1 / 2) \ {0} ∧ w + κ * ζ ^ k = u ∧
        E ζ ∈ S ∧ E ζ ∉ T := fun n => hforall _ (by positivity)
  choose U hU_mem hU_ne Z hZ_mem heq_n hEZ_S hZ_notT using hex
  -- the base values tend to `u₁`
  have hU_tend : Tendsto U atTop (𝓝 u₁) := by
    rw [tendsto_iff_dist_tendsto_zero]
    have hbase : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) := by
      have hden : Tendsto (fun n : ℕ => ((n : ℝ) + 1)) atTop atTop :=
        (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add tendsto_const_nhds
      have h1 : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
      exact h1.div_atTop hden
    refine squeeze_zero (g := fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
      (fun n => dist_nonneg) (fun n => ?_) hbase
    have h := hU_mem n
    rw [Metric.mem_ball] at h
    exact le_of_lt h
  -- the chart parameters `ζ` live in a compact set, so pass to a convergent subsequence
  have hZ_closed : ∀ n, Z n ∈ Metric.closedBall (0 : ℂ) (1 / 2) := by
    intro n
    rw [Metric.mem_closedBall, dist_zero_right]
    have h := (hZ_mem n).1
    rw [Metric.mem_ball, dist_zero_right] at h
    linarith
  obtain ⟨z, hz_closed, φ, hφmono, hφtend⟩ :=
    IsCompact.tendsto_subseq (isCompact_closedBall (0 : ℂ) (1 / 2)) hZ_closed
  have hφT : Tendsto φ atTop atTop := hφmono.tendsto_atTop
  have hUφ_tend : Tendsto (fun n => U (φ n)) atTop (𝓝 u₁) := hU_tend.comp hφT
  -- the limit parameter satisfies the chart equation over `u₁`
  have hzg : w + κ * z ^ k = u₁ := by
    have hcont : Continuous (fun z : ℂ => w + κ * z ^ k) :=
      continuous_const.add (continuous_const.mul (continuous_pow k))
    have h1 : Tendsto (fun n => w + κ * (Z (φ n)) ^ k) atTop (𝓝 (w + κ * z ^ k)) :=
      (hcont.tendsto z).comp hφtend
    have h2 : Tendsto (fun n => w + κ * (Z (φ n)) ^ k) atTop (𝓝 u₁) := by
      refine hUφ_tend.congr ?_
      intro n
      exact (heq_n (φ n)).symm
    exact tendsto_nhds_unique h1 h2
  -- `z ≠ 0` because `w ≠ u₁`, so the limit is a genuine point of the chart
  have hz_ne : z ≠ 0 := by
    intro hz0
    have hwu : w = u₁ := by
      have h := hzg
      rw [hz0, zero_pow hk.ne', mul_zero, add_zero] at h
      exact h
    exact hw hwu
  have hz_Bbig : z ∈ Metric.ball (0 : ℂ) 1 \ {0} := by
    refine ⟨?_, hz_ne⟩
    rw [Metric.mem_ball, dist_zero_right]
    have h := hz_closed
    rw [Metric.mem_closedBall, dist_zero_right] at h
    linarith
  have hzH0 : E z ∈ H0 a h := (hEmem z hz_Bbig).1
  have hzpsi : (E z).2.1 = u₁ := by rw [(hEmem z hz_Bbig).2, hzg]
  -- `E` is continuous at `z`, hence the counterexamples converge to `E z`, which lies in `S`
  have hBbigopen : IsOpen (Metric.ball (0 : ℂ) 1 \ {0}) :=
    Metric.isOpen_ball.sdiff isClosed_singleton
  have hEcz : ContinuousAt E z := hEcont.continuousAt (hBbigopen.mem_nhds hz_Bbig)
  have hE_tend : Tendsto (fun n => E (Z (φ n))) atTop (𝓝 (E z)) :=
    (ContinuousAt.tendsto hEcz).comp hφtend
  have hEz_closure : E z ∈ closure S :=
    mem_closure_of_tendsto hE_tend (Eventually.of_forall fun x => hEZ_S (φ x))
  have hEzS : E z ∈ S := hScl (E z) hEz_closure hzH0
  -- but `T` is a neighbourhood of `E z` in `H0`, giving the desired contradiction
  obtain ⟨V, hV_nhds, hVT⟩ :=
    mem_nhdsWithin_iff_exists_mem_nhds_inter.mp (hT (E z) hEzS hzpsi)
  obtain ⟨n, hnV⟩ := (hE_tend.eventually hV_nhds).exists
  exact hZ_notT (φ n) (hVT ⟨hnV, hSH (hEZ_S (φ n))⟩)

end Work.EQ
