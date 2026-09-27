import Mathlib
import Submission.Work.EQ.fan_estimates
import Submission.Work.EQ.CycleDefs
import Submission.Work.EQ.H0_step5_aux
import Submission.Work.EQ.chart_uniform_tails_lim
import Submission.Work.EQ.subO2_invBranch
import Submission.Work.Analysis.meromorphicAt_bounded_tendsto
import Submission.Work.EQ.chain_unique_window
import Submission.Work.EQ.germC_facts
import Submission.Work.EQ.H0_invParam_ge
import Submission.Work.EQ.gpd_middle
import Submission.Work.EQ.gpd_aux
import Submission.Work.EQ.genuine_chart_window_degenerate

namespace Work.EQ

open Filter _root_.Topology
open scoped Topology

noncomputable section

set_option maxHeartbeats 1000000

/-! # The window dichotomy with tail-norm hypotheses
... -/

theorem window_lim_aux_bn {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) {e : ℂ → ChainData} {u₀ v₀ : ℂ} {k N : ℕ}
    (he : IsPuncturedChart a h e u₀ k)
    (hv : Filter.Tendsto (fun ζ : ℂ => (e ζ).2.2)
      (nhdsWithin (0 : ℂ) ({(0 : ℂ)}ᶜ : Set ℂ)) (nhds v₀))
    (hN : ∀ ζ : ℂ, 0 < ‖ζ‖ → ‖ζ‖ < 1 → ∀ n : ℕ, N ≤ n →
      (e ζ).1 (n : ℤ) = germC a h (((eqLam a : ℝ) : ℂ) ^ n * (e ζ).2.1) ∧
      (e ζ).1 (-(n : ℤ)) = ugermC a h (((eqLam a : ℝ) : ℂ) ^ n * (e ζ).2.2))
    (hN1 : 1 ≤ N)
    {Ke Lam Q δ : ℝ} (hδ : 0 < δ)
    (hF : ∀ (ε : List Bool) (v : ℂ), ‖v‖ < δ → FanGood a h Ke Lam Q ε v)
    (hreg : ∀ u : ℂ, ‖u‖ < δ → RegPair a (germC a h u) (germC a h ((eqLam a : ℂ) * u)))
    (hbn : ∀ m : ℕ, N ≤ m → ‖((eqLam a : ℝ) : ℂ) ^ m * u₀‖ < δ ∧
      ‖((eqLam a : ℝ) : ℂ) ^ m * v₀‖ < δ)
    (hH : ∀ σ : List Bool, σ.length ≤ 2 * N →
      bsq (subO1 a (bwdP a σ (germC a h (((eqLam a : ℝ) : ℂ) ^ N * u₀)))) ≠ 0 ∧
      bsq (subO2 a (bwdP a σ (germC a h (((eqLam a : ℝ) : ℂ) ^ N * u₀)))) ≠ 0) :
    ∃ q₀ : ChainData,
      Filter.Tendsto e (nhdsWithin (0 : ℂ) ({(0 : ℂ)}ᶜ : Set ℂ)) (nhds q₀) ∧
      q₀.2.1 = u₀ ∧ q₀.2.2 = v₀ ∧
      ∀ j : ℕ, j ≤ 2 * N → ∃ σ : List Bool, σ.length = j ∧
        q₀.1 ((N : ℤ) - (j : ℤ)) = bwdP a σ (germC a h (((eqLam a : ℝ) : ℂ) ^ N * u₀)) := by
  obtain ⟨hk, hu0ne, κ, hκ, hmem, hinj, hcont, hmer2, hmerC⟩ := he
  have hlam0 : 0 < eqLam a := lam_pos ha0 ha1
  have hlamlt : eqLam a < 1 := lam_lt_one ha0 ha1
  have hnormC : ‖eqLamC a‖ = eqLam a := lamC_norm ha0 ha1
  have hψ1 : Filter.Tendsto (fun ζ : ℂ => (e ζ).2.1)
      (nhdsWithin (0 : ℂ) ({(0 : ℂ)}ᶜ : Set ℂ)) (nhds u₀) := by
    have hpoly : Filter.Tendsto (fun ζ : ℂ => u₀ + κ * ζ ^ k)
        (nhdsWithin (0 : ℂ) ({(0 : ℂ)}ᶜ : Set ℂ)) (nhds (u₀ + κ * (0 : ℂ) ^ k)) :=
      (ContinuousAt.tendsto (by fun_prop)).mono_left nhdsWithin_le_nhds
    rw [zero_pow hk.ne', mul_zero, add_zero] at hpoly
    refine hpoly.congr' ?_
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) one_pos)] with ζ hζ hζb
    exact ((hmem ζ ⟨hζb, hζ⟩).2).symm
  have hgermAn : AnalyticOnNhd ℂ (germC a h) (Metric.ball (0 : ℂ) δ) := by
    intro v hv
    have hv' : ‖v‖ < δ := by simpa [Metric.mem_ball, dist_zero_right] using hv
    exact (hF [] v hv').1
  have hgermC : ∀ u ∈ Metric.ball (0 : ℂ) δ,
      bsq (subO1 a (germC a h u)) ≠ 0 ∧ bsq (subO2 a (germC a h u)) ≠ 0 ∧
        EqRelC a (germC a h u) (germC a h (eqLamC a * u)) := by
    intro u hu
    have hu' : ‖u‖ < δ := by simpa [Metric.mem_ball, dist_zero_right] using hu
    have hR : RegPair a (germC a h u) (germC a h ((eqLam a : ℂ) * u)) := hreg u hu'
    have hne1 : bsq (subO1 a (germC a h u)) ≠ 0 := by
      intro h0
      have h0' : ((germC a h u).1 + ↑(a / 2)) ^ 2 + (germC a h u).2 ^ 2 = 0 := by
        simpa only [subO1, bsq] using h0
      have hcast : ((↑(a / 2) : ℂ)) = (a : ℂ) / 2 := by push_cast; ring
      rw [hcast] at h0'
      have hpos : 0 < (((germC a h u).1 + (a / 2 : ℂ)) ^ 2 + (germC a h u).2 ^ 2).re :=
        (hF [] u hu').2.2.2.2
      rw [h0'] at hpos
      simp at hpos
    exact ⟨hne1, hR.2.1, hR.1⟩
  have hu0g : ‖eqLamC a ^ N * u₀‖ < δ := by
    simpa using (hbn N le_rfl).1
  have hv0g : ‖eqLamC a ^ N * v₀‖ < δ := by
    simpa using (hbn N le_rfl).2
  obtain ⟨q, hqN, hqmN, hqup, hqdn, hqtend, hqbsq, hqrel⟩ :=
    gpd_middle_limits ha0 ha1 hh one_pos hδ hcont (fun ζ hζ => (hmem ζ hζ).1) hψ1 hv
      (fun ζ hζ n hn => hN ζ
        (by have h2 : ζ ∈ ({(0 : ℂ)}ᶜ : Set ℂ) := hζ.2
            exact norm_pos_iff.mpr (by simpa using h2))
        (by have h1 : ζ ∈ Metric.ball (0 : ℂ) 1 := hζ.1
            simpa [Metric.mem_ball, dist_zero_right] using h1) n hn)
      hgermAn hgermC hu0g hv0g (fun σ hσ => (hH σ hσ).1)
  refine ⟨(q, u₀, v₀), ?_, rfl, rfl, ?_⟩
  · refine (Prod.tendsto_iff (fun ζ : ℂ => ((e ζ).1, (e ζ).2)) (q, (u₀, v₀))).mpr ⟨?_, ?_⟩
    · exact tendsto_pi_nhds.mpr (fun j => hqtend j)
    · exact (Prod.tendsto_iff (fun ζ : ℂ => (e ζ).2) (u₀, v₀)).mpr ⟨hψ1, hv⟩
  · intro j hj
    have key : ∀ j : ℕ, j ≤ 2 * N → ∃ σ : List Bool, σ.length = j ∧
        q ((N : ℤ) - (j : ℤ)) = bwdP a σ (germC a h (((eqLam a : ℝ) : ℂ) ^ N * u₀)) := by
      intro j
      induction j with
      | zero =>
        intro _
        exact ⟨[], rfl, by simp [hqN, eqLamC_eq]⟩
      | succ m ih =>
        intro hm
        obtain ⟨σ, hσlen, hσ⟩ := ih (by omega)
        have hidx : -((N : ℤ)) ≤ (N : ℤ) - ((m : ℤ) + 1) := by omega
        have hidx2 : (N : ℤ) - ((m : ℤ) + 1) < (N : ℤ) := by omega
        have hidx3 : -((N : ℤ)) ≤ (N : ℤ) - ((m : ℤ) + 1) + 1 := by omega
        have hidx4 : (N : ℤ) - ((m : ℤ) + 1) + 1 ≤ (N : ℤ) := by omega
        have hrel := hqrel ((N : ℤ) - ((m : ℤ) + 1)) hidx hidx2
        have hb := hqbsq ((N : ℤ) - ((m : ℤ) + 1) + 1) hidx3 hidx4
        have harith : (N : ℤ) - ((m : ℤ) + 1) + 1 = (N : ℤ) - (m : ℤ) := by ring
        have hcast : ((m + 1 : ℕ) : ℤ) = (m : ℤ) + 1 := by push_cast; ring
        rcases H0_invParam_ge_exists_invBranch hrel hb with h1 | h1
        · refine ⟨σ ++ [true], by simp [hσlen], ?_⟩
          rw [hcast, h1, harith, hσ, bwdP_snoc]
        · refine ⟨σ ++ [false], by simp [hσlen], ?_⟩
          rw [hcast, h1, harith, hσ, bwdP_snoc]
    exact key j hj


/-- `bsq (subO1 a (germC a h u)) ≠ 0` for `‖u‖ < δ` (the `O₁`-radicand of a fan value has positive
real part). -/

theorem window_isChain_aux_bn {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) {e : ℂ → ChainData} {q₀ : ChainData} {u₀ v₀ : ℂ} {k N : ℕ}
    (he : IsPuncturedChart a h e u₀ k)
    (hq0 : Filter.Tendsto e (nhdsWithin (0 : ℂ) ({(0 : ℂ)}ᶜ : Set ℂ)) (nhds q₀))
    (hv : Filter.Tendsto (fun ζ : ℂ => (e ζ).2.2)
      (nhdsWithin (0 : ℂ) ({(0 : ℂ)}ᶜ : Set ℂ)) (nhds v₀))
    (hN : ∀ ζ : ℂ, 0 < ‖ζ‖ → ‖ζ‖ < 1 → ∀ n : ℕ, N ≤ n →
      (e ζ).1 (n : ℤ) = germC a h (((eqLam a : ℝ) : ℂ) ^ n * (e ζ).2.1) ∧
      (e ζ).1 (-(n : ℤ)) = ugermC a h (((eqLam a : ℝ) : ℂ) ^ n * (e ζ).2.2))
    (hN1 : 1 ≤ N)
    {Ke Lam Q δ : ℝ} (hδ : 0 < δ)
    (hF : ∀ (ε : List Bool) (v : ℂ), ‖v‖ < δ → FanGood a h Ke Lam Q ε v)
    (hreg : ∀ u : ℂ, ‖u‖ < δ → RegPair a (germC a h u) (germC a h ((eqLam a : ℂ) * u)))
    (hbn : ∀ m : ℕ, N ≤ m → ‖((eqLam a : ℝ) : ℂ) ^ m * u₀‖ < δ ∧
      ‖((eqLam a : ℝ) : ℂ) ^ m * v₀‖ < δ)
    (hq1 : q₀.2.1 = u₀) (hq2 : q₀.2.2 = v₀)
    (hH : ∀ σ : List Bool, σ.length ≤ 2 * N →
      bsq (subO1 a (bwdP a σ (germC a h (((eqLam a : ℝ) : ℂ) ^ N * u₀)))) ≠ 0 ∧
      bsq (subO2 a (bwdP a σ (germC a h (((eqLam a : ℝ) : ℂ) ^ N * u₀)))) ≠ 0)
    (hwin : ∀ j : ℕ, j ≤ 2 * N → ∃ σ : List Bool, σ.length = j ∧
        q₀.1 ((N : ℤ) - (j : ℤ)) = bwdP a σ (germC a h (((eqLam a : ℝ) : ℂ) ^ N * u₀))) :
    IsChain a h q₀ := by
  have he_chart : IsPuncturedChart a h e u₀ k := he
  obtain ⟨hk0, hu0ne, κ, hκ, hmem, hinj_e, hcont, hmer2, hmerC⟩ := he
  have hlam0 : 0 < eqLam a := lam_pos ha0 ha1
  have hlamlt : eqLam a < 1 := lam_lt_one ha0 ha1
  have hcoord : ∀ j : ℤ, Tendsto (fun ζ : ℂ => (e ζ).1 j)
      (nhdsWithin (0 : ℂ) ({(0 : ℂ)}ᶜ : Set ℂ)) (nhds (q₀.1 j)) :=
    fun j => coord_tendsto_of_tendsto hq0 j
  have hψ1 : Tendsto (fun ζ : ℂ => (e ζ).2.1)
      (nhdsWithin (0 : ℂ) ({(0 : ℂ)}ᶜ : Set ℂ)) (nhds u₀) := by
    rw [← hq1]
    exact (continuous_fst.tendsto q₀.2).comp ((continuous_snd.tendsto q₀).comp hq0)
  -- norm bounds
  have hbnorm : ∀ m : ℕ, N ≤ m → ‖(((eqLam a : ℝ) : ℂ) ^ m * u₀)‖ < δ :=
    fun m hm => (hbn m hm).1
  have hbnormv : ∀ m : ℕ, N ≤ m → ‖(((eqLam a : ℝ) : ℂ) ^ m * v₀)‖ < δ :=
    fun m hm => (hbn m hm).2
  -- the tail formulae
  have hup : ∀ m : ℕ, N ≤ m → q₀.1 (m : ℤ) = germC a h (((eqLam a : ℝ) : ℂ) ^ m * u₀) := by
    intro m hm
    have hev : (fun ζ : ℂ => (e ζ).1 (m : ℤ)) =ᶠ[nhdsWithin (0 : ℂ) ({(0 : ℂ)}ᶜ : Set ℂ)]
        (fun ζ => germC a h (((eqLam a : ℝ) : ℂ) ^ m * (e ζ).2.1)) := by
      filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) one_pos)] with ζ hζ hζb
      exact (hN ζ (norm_pos_iff.mpr (by simpa using hζ))
        (by simpa [Metric.mem_ball, dist_zero_right] using hζb) m hm).1
    have hlim : Tendsto (fun ζ : ℂ => germC a h (((eqLam a : ℝ) : ℂ) ^ m * (e ζ).2.1))
        (nhdsWithin (0 : ℂ) ({(0 : ℂ)}ᶜ : Set ℂ))
        (nhds (germC a h (((eqLam a : ℝ) : ℂ) ^ m * u₀))) :=
      ((hF [] _ (hbnorm m hm)).1.continuousAt).tendsto.comp (hψ1.const_mul _)
    exact tendsto_nhds_unique (hcoord _) (hlim.congr' hev.symm)
  have hdn : ∀ m : ℕ, N ≤ m → q₀.1 (-(m : ℤ)) = ugermC a h (((eqLam a : ℝ) : ℂ) ^ m * v₀) := by
    intro m hm
    have hev : (fun ζ : ℂ => (e ζ).1 (-(m : ℤ))) =ᶠ[nhdsWithin (0 : ℂ) ({(0 : ℂ)}ᶜ : Set ℂ)]
        (fun ζ => ugermC a h (((eqLam a : ℝ) : ℂ) ^ m * (e ζ).2.2)) := by
      filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) one_pos)] with ζ hζ hζb
      exact (hN ζ (norm_pos_iff.mpr (by simpa using hζ))
        (by simpa [Metric.mem_ball, dist_zero_right] using hζb) m hm).2
    have hlim : Tendsto (fun ζ : ℂ => ugermC a h (((eqLam a : ℝ) : ℂ) ^ m * (e ζ).2.2))
        (nhdsWithin (0 : ℂ) ({(0 : ℂ)}ᶜ : Set ℂ))
        (nhds (ugermC a h (((eqLam a : ℝ) : ℂ) ^ m * v₀))) := by
      have hcontAt : ContinuousAt (ugermC a h) (((eqLam a : ℝ) : ℂ) ^ m * v₀) :=
        (continuous_eqMirror.continuousAt.comp (hF [] _ (hbnormv m hm)).1.continuousAt)
      exact hcontAt.tendsto.comp (hv.const_mul _)
    exact tendsto_nhds_unique (hcoord _) (hlim.congr' hev.symm)
  -- non-vanishing of the radicands at germ values
  have hu1 : ∀ w : ℂ, ‖w‖ < δ → bsq (subO1 a (germC a h w)) ≠ 0 :=
    fun w hw => germ_bsq_subO1_ne_zero hF hw
  have hu2 : ∀ w : ℂ, ‖w‖ < δ → bsq (subO2 a (germC a h w)) ≠ 0 :=
    fun w hw => (hreg w hw).2.1
  have hu1' : ∀ w : ℂ, ‖w‖ < δ → bsq (subO1 a (ugermC a h w)) ≠ 0 := by
    intro w hw
    show bsq (subO1 a (eqMirror (germC a h w))) ≠ 0
    rw [bsq_subO1_eqMirror]
    exact (hreg w hw).2.1
  have hu2' : ∀ w : ℂ, ‖w‖ < δ → bsq (subO2 a (ugermC a h w)) ≠ 0 := by
    intro w hw
    show bsq (subO2 a (eqMirror (germC a h w))) ≠ 0
    rw [bsq_subO2_eqMirror]
    exact germ_bsq_subO1_ne_zero hF hw
  -- the two radicands along the limit chain
  have hrad1 : ∀ m : ℤ, bsq (subO1 a (q₀.1 m)) ≠ 0 := by
    intro m
    by_cases hmN : (N : ℤ) ≤ m
    · obtain ⟨j, hj⟩ : ∃ j : ℕ, m = (j : ℤ) := ⟨m.toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
      have hNj : N ≤ j := by omega
      rw [hj, hup j hNj]
      exact hu1 _ (hbnorm j hNj)
    · rw [not_le] at hmN
      by_cases hmN' : m ≤ -(N : ℤ)
      · obtain ⟨j, hj⟩ : ∃ j : ℕ, m = -(j : ℤ) :=
          ⟨(-m).toNat, by rw [Int.toNat_of_nonneg (by omega)]; ring⟩
        have hNj : N ≤ j := by omega
        rw [hj, hdn j hNj]
        exact hu1' _ (hbnormv j hNj)
      · have hj0 : 0 < (N : ℤ) - m := by omega
        have hj2 : ((N : ℤ) - m).toNat ≤ 2 * N := by
          have h1 : (N : ℤ) - m ≤ ((2 * N : ℕ) : ℤ) := by push_cast; omega
          calc ((N : ℤ) - m).toNat ≤ (((2 * N : ℕ)) : ℤ).toNat := Int.toNat_le_toNat h1
            _ = 2 * N := Int.toNat_natCast _
        obtain ⟨σ, hσlen, hσ⟩ := hwin _ hj2
        have hw : q₀.1 m = bwdP a σ (germC a h (((eqLam a : ℝ) : ℂ) ^ N * u₀)) := by
          rw [← hσ]
          congr 1
          rw [Int.toNat_of_nonneg hj0.le]
          ring
        rw [hw]
        exact (hH σ (by rw [hσlen]; exact hj2)).1
  have hrad2 : ∀ m : ℤ, bsq (subO2 a (q₀.1 m)) ≠ 0 := by
    intro m
    by_cases hmN : (N : ℤ) ≤ m
    · obtain ⟨j, hj⟩ : ∃ j : ℕ, m = (j : ℤ) := ⟨m.toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
      have hNj : N ≤ j := by omega
      rw [hj, hup j hNj]
      exact hu2 _ (hbnorm j hNj)
    · rw [not_le] at hmN
      by_cases hmN' : m ≤ -(N : ℤ)
      · obtain ⟨j, hj⟩ : ∃ j : ℕ, m = -(j : ℤ) :=
          ⟨(-m).toNat, by rw [Int.toNat_of_nonneg (by omega)]; ring⟩
        have hNj : N ≤ j := by omega
        rw [hj, hdn j hNj]
        exact hu2' _ (hbnormv j hNj)
      · have hj0 : 0 < (N : ℤ) - m := by omega
        have hj2 : ((N : ℤ) - m).toNat ≤ 2 * N := by
          have h1 : (N : ℤ) - m ≤ ((2 * N : ℕ) : ℤ) := by push_cast; omega
          calc ((N : ℤ) - m).toNat ≤ (((2 * N : ℕ)) : ℤ).toNat := Int.toNat_le_toNat h1
            _ = 2 * N := Int.toNat_natCast _
        obtain ⟨σ, hσlen, hσ⟩ := hwin _ hj2
        have hw : q₀.1 m = bwdP a σ (germC a h (((eqLam a : ℝ) : ℂ) ^ N * u₀)) := by
          rw [← hσ]
          congr 1
          rw [Int.toNat_of_nonneg hj0.le]
          ring
        rw [hw]
        exact (hH σ (by rw [hσlen]; exact hj2)).2
  -- EqRelC for every consecutive pair
  have hEq : ∀ n : ℤ, EqRelC a (q₀.1 n) (q₀.1 (n + 1)) := by
    intro n
    set F : (ℂ × ℂ) × (ℂ × ℂ) → ℂ × ℂ := fun z =>
        (((z.2.1 + z.1.1) ^ 2 + (z.2.2 + z.1.2) ^ 2),
          ((z.2.1 + z.1.1) * z.1.2 - (z.2.2 + z.1.2) * (z.1.1 - ((a / 2 : ℝ) : ℂ)))) with hFdef
    have hFp : Continuous F := by rw [hFdef]; fun_prop
    have hpair : Tendsto (fun ζ : ℂ => ((e ζ).1 n, (e ζ).1 (n + 1)))
        (nhdsWithin (0 : ℂ) ({(0 : ℂ)}ᶜ : Set ℂ)) (nhds (q₀.1 n, q₀.1 (n + 1))) :=
      (Prod.tendsto_iff _ _).mpr ⟨hcoord n, hcoord (n + 1)⟩
    have hlim : Tendsto (fun ζ : ℂ => F ((e ζ).1 n, (e ζ).1 (n + 1)))
        (nhdsWithin (0 : ℂ) ({(0 : ℂ)}ᶜ : Set ℂ)) (nhds (F (q₀.1 n, q₀.1 (n + 1)))) :=
      hFp.continuousAt.tendsto.comp hpair
    have hev : (fun ζ : ℂ => F ((e ζ).1 n, (e ζ).1 (n + 1)))
        =ᶠ[nhdsWithin (0 : ℂ) ({(0 : ℂ)}ᶜ : Set ℂ)] (fun _ => ((1 : ℂ), (0 : ℂ))) := by
      filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) one_pos)] with ζ hζ hζb
      have hchain' : IsChain a h (e ζ) := isChain_of_mem_H0' (hmem ζ ⟨hζb, hζ⟩).1
      obtain ⟨hrel, -⟩ := hchain'.1 n
      rw [hFdef]
      exact Prod.ext hrel.1 (sub_eq_zero.mpr hrel.2)
    have hconst : Tendsto (fun _ : ℂ => ((1 : ℂ), (0 : ℂ)))
        (nhdsWithin (0 : ℂ) ({(0 : ℂ)}ᶜ : Set ℂ)) (nhds ((1 : ℂ), (0 : ℂ))) := tendsto_const_nhds
    have hfin : F (q₀.1 n, q₀.1 (n + 1)) = ((1 : ℂ), (0 : ℂ)) :=
      tendsto_nhds_unique hlim (hconst.congr' hev.symm)
    rw [hFdef] at hfin
    obtain ⟨h1, h2⟩ := Prod.ext_iff.mp hfin
    exact ⟨h1, sub_eq_zero.mp h2⟩
  refine ⟨fun n => ⟨hEq n, hrad2 n, hrad1 (n + 1)⟩, ?_, ?_, ?_, ?_⟩
  · rw [hq1]; exact hu0ne
  · rw [hq2]; exact gpd_v0_ne_zero ha0 ha1 hh he_chart hv
  · rw [Filter.eventually_atTop]
    exact ⟨N, fun n hn => by rw [hup n hn, hq1]⟩
  · rw [Filter.eventually_atTop]
    exact ⟨N, fun n hn => by rw [hdn n hn, hq2]⟩

/-- **A genuine puncture has a degenerate window.**  Let `e` be a punctured chart at `u₀` with
finite `ψ₂`-limit `v₀`, genuine (no limit in `⁰H`), with uniform principal tails from depth `N ≥ 1`
and with good stable fans around the window.  Then some backward word `σ` of length at most `2N`
from the stable germ at `λ^N u₀` lands on a degenerate point of the relation: either the
`O₁`-radicand or the `O₂`-radicand of `bwdP a σ (germC a h (λ^N u₀))` vanishes.

Proof (full route in `Submission/Work/EQ/DESIGN_PUNCT_CORE.md` §1, reviewed):
`c_0 := germC a h (λ^N u₀)` is the limit of the chart's index-`N` point.  Inductively down from index
`N`: if `bsq (subO1 a c_j) = 0` we are done; otherwise `P_ζ + Q_ζ` (the sum of two consecutive chart
points) satisfies `bsq (P_ζ+Q_ζ) = 1` and is parallel to `Q_ζ - O₁`, so
`P_ζ = -Q_ζ ± (Q_ζ - O₁)/brho (subO1 a Q_ζ)` with `1/brho` bounded; hence `P_ζ` is bounded, and being
meromorphic at `0` it converges (`Work.Analysis.meromorphicAt_bounded_tendsto`), its limit being one
of the two `invBranch` values of `c_j` (`Work.EQ.H0_invParam_ge_exists_invBranch`).  So either some
`c_j` is `O₁`-degenerate, or the whole window converges.  In the second case the limit chain `q₀` is
an `IsChain`: the window pairs are `EqRelC` and non-degenerate, the junction pair at `-N` is a limit
of `EqRelC` pairs, and the tail pairs are principal and regular by `hreg`.  A member of `⁰H` is an
explicit `candChain` (`Work.EQ.exists_candChain_of_mem_H0`) with finitely many possible data, so
along a subsequence of `ζ → 0` the data are constant; passing to the limit (continuity of the
candidate chain in `(ψ₁, ψ₂)` in the `FanGood` regime) exhibits `q₀` as that `candChain` with
parameters the limits `(u₀, u₀v₀)`, and the same candidate family is a continuous family of chains
through `q₀`, so `q₀ ∈ ⁰H` — contradicting genuineness. -/

theorem genuine_chart_window_degenerate_bn {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ}
    {r : ℝ} (hh : IsStableGerm a h r) {e : ℂ → ChainData} {u₀ v₀ : ℂ} {k N : ℕ}
    (he : IsPuncturedChart a h e u₀ k)
    (hgen : ¬ ∃ q ∈ H0 a h, Filter.Tendsto e (nhdsWithin (0 : ℂ) ({(0 : ℂ)}ᶜ : Set ℂ)) (nhds q))
    (hv : Filter.Tendsto (fun ζ : ℂ => (e ζ).2.2)
      (nhdsWithin (0 : ℂ) ({(0 : ℂ)}ᶜ : Set ℂ)) (nhds v₀))
    (hN : ∀ ζ : ℂ, 0 < ‖ζ‖ → ‖ζ‖ < 1 → ∀ n : ℕ, N ≤ n →
      (e ζ).1 (n : ℤ) = germC a h (((eqLam a : ℝ) : ℂ) ^ n * (e ζ).2.1) ∧
      (e ζ).1 (-(n : ℤ)) = ugermC a h (((eqLam a : ℝ) : ℂ) ^ n * (e ζ).2.2))
    {Ke Lam Q δ : ℝ} (hδ : 0 < δ) (hN1 : 1 ≤ N)
    (hF : ∀ (ε : List Bool) (v : ℂ), ‖v‖ < δ → FanGood a h Ke Lam Q ε v)
    (hreg : ∀ u : ℂ, ‖u‖ < δ → RegPair a (germC a h u) (germC a h ((eqLam a : ℂ) * u)))
    (hbn : ∀ m : ℕ, N ≤ m → ‖((eqLam a : ℝ) : ℂ) ^ m * u₀‖ < δ ∧
      ‖((eqLam a : ℝ) : ℂ) ^ m * v₀‖ < δ) :
    ∃ σ : List Bool, σ.length ≤ 2 * N ∧
      (bsq (subO1 a (bwdP a σ (germC a h (((eqLam a : ℝ) : ℂ) ^ N * u₀)))) = 0 ∨
        bsq (subO2 a (bwdP a σ (germC a h (((eqLam a : ℝ) : ℂ) ^ N * u₀)))) = 0) := by
  by_contra hcon
  have hH : ∀ σ : List Bool, σ.length ≤ 2 * N →
      bsq (subO1 a (bwdP a σ (germC a h (((eqLam a : ℝ) : ℂ) ^ N * u₀)))) ≠ 0 ∧
      bsq (subO2 a (bwdP a σ (germC a h (((eqLam a : ℝ) : ℂ) ^ N * u₀)))) ≠ 0 := by
    intro σ hσlen
    constructor
    · intro h0
      exact hcon ⟨σ, hσlen, Or.inl h0⟩
    · intro h0
      exact hcon ⟨σ, hσlen, Or.inr h0⟩
  obtain ⟨q₀, htend, hq1, hq2, hwin⟩ :=
    window_lim_aux_bn (a := a) (h := h) (r := r) (e := e) (u₀ := u₀) (v₀ := v₀) (k := k) (N := N)
      (Ke := Ke) (Lam := Lam) (Q := Q) (δ := δ) ha0 ha1 hh he hv hN hN1 hδ hF hreg hbn hH
  have hchain : IsChain a h q₀ :=
    window_isChain_aux_bn (a := a) (h := h) (r := r) (e := e) (q₀ := q₀) (u₀ := u₀) (v₀ := v₀)
      (k := k) (N := N) (Ke := Ke) (Lam := Lam) (Q := Q) (δ := δ)
      ha0 ha1 hh he htend hv hN hN1 hδ hF hreg hbn hq1 hq2 hH hwin
  have hk0 : 0 < k := he.1
  rcases eq_or_ne k 1 with hk1 | hk1
  · exact hgen ⟨q₀, mem_H0_of_k_eq_one_aux (a := a) (h := h) (r := r) (e := e) (q₀ := q₀)
      (u₀ := u₀) (v₀ := v₀) (k := k) (N := N) ha0 ha1 hh he hk1 htend hchain hq1, htend⟩
  · exact (order_le_one_aux (a := a) (h := h) (r := r) (e := e) (q₀ := q₀) (u₀ := u₀) (v₀ := v₀)
      (k := k) (N := N) ha0 ha1 hh he htend hq2 hN (by omega)).elim

end

end Work.EQ
