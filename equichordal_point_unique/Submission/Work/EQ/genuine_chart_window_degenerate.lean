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

namespace Work.EQ

open Filter _root_.Topology
open scoped Topology

noncomputable section

set_option maxHeartbeats 1000000


theorem window_lim_aux {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
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
    (hsmall : ‖u₀‖ < δ * (eqLam a) ^ N) (hvs : ‖v₀‖ < δ)
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
    rw [eqLamC_eq, norm_mul, norm_pow, Complex.norm_of_nonneg hlam0.le]
    calc eqLam a ^ N * ‖u₀‖ < eqLam a ^ N * (δ * eqLam a ^ N) :=
          mul_lt_mul_of_pos_left hsmall (pow_pos hlam0 N)
      _ = δ * (eqLam a ^ N * eqLam a ^ N) := by ring
      _ = δ * eqLam a ^ (2 * N) := by rw [← pow_add]; ring_nf
      _ ≤ δ * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ hlam0.le hlamlt.le) hδ.le
      _ = δ := mul_one δ
  have hv0g : ‖eqLamC a ^ N * v₀‖ < δ := by
    rw [eqLamC_eq, norm_mul, norm_pow, Complex.norm_of_nonneg hlam0.le]
    calc eqLam a ^ N * ‖v₀‖ ≤ 1 * ‖v₀‖ :=
          mul_le_mul_of_nonneg_right (pow_le_one₀ hlam0.le hlamlt.le) (norm_nonneg v₀)
      _ = ‖v₀‖ := one_mul _
      _ < δ := hvs
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
lemma germ_bsq_subO1_ne_zero {a : ℝ} {h : ℂ → ℂ} {Ke Lam Q δ : ℝ} {u : ℂ}
    (hF : ∀ (ε : List Bool) (v : ℂ), ‖v‖ < δ → FanGood a h Ke Lam Q ε v) (hu : ‖u‖ < δ) :
    bsq (subO1 a (germC a h u)) ≠ 0 := by
  intro h0
  have h0' : ((germC a h u).1 + ↑(a / 2)) ^ 2 + (germC a h u).2 ^ 2 = 0 := by
    simpa only [subO1, bsq] using h0
  have hcast : ((↑(a / 2) : ℂ)) = (a : ℂ) / 2 := by push_cast; ring
  rw [hcast] at h0'
  have hpos : 0 < (((germC a h u).1 + (a / 2 : ℂ)) ^ 2 + (germC a h u).2 ^ 2).re :=
    (hF [] u hu).2.2.2.2
  rw [h0'] at hpos
  simp at hpos

/-- A chain of `H0` is a chain. -/
lemma isChain_of_mem_H0' {a : ℝ} {h : ℂ → ℂ} {p : ChainData} (hp : p ∈ H0 a h) :
    IsChain a h p := by
  obtain ⟨ε, hε, f, -, hf0, hfam⟩ := hp
  rw [← hf0]
  exact (hfam p.2.1 (by rw [Metric.mem_ball, dist_self]; exact hε)).1

/-- Coordinatewise extraction of the limit of a `ChainData`-valued function. -/
lemma coord_tendsto_of_tendsto {e : ℂ → ChainData} {q : ChainData}
    (h : Tendsto e (nhdsWithin (0 : ℂ) ({(0 : ℂ)}ᶜ : Set ℂ)) (nhds q)) (j : ℤ) :
    Tendsto (fun ζ : ℂ => (e ζ).1 j) (nhdsWithin (0 : ℂ) ({(0 : ℂ)}ᶜ : Set ℂ)) (nhds (q.1 j)) :=
  (tendsto_pi_nhds.mp ((continuous_fst.tendsto q).comp h)) j

lemma psi2_tendsto_of_tendsto {e : ℂ → ChainData} {q : ChainData}
    (h : Tendsto e (nhdsWithin (0 : ℂ) ({(0 : ℂ)}ᶜ : Set ℂ)) (nhds q)) :
    Tendsto (fun ζ : ℂ => (e ζ).2.2) (nhdsWithin (0 : ℂ) ({(0 : ℂ)}ᶜ : Set ℂ)) (nhds q.2.2) :=
  (continuous_snd.tendsto q.2).comp ((continuous_snd.tendsto q).comp h)

/-- **The `k = 1` family.** -/
theorem mem_H0_of_k_eq_one_aux {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) {e : ℂ → ChainData} {q₀ : ChainData} {u₀ v₀ : ℂ} {k N : ℕ}
    (he : IsPuncturedChart a h e u₀ k) (hk1 : k = 1)
    (hq0 : Filter.Tendsto e (nhdsWithin (0 : ℂ) ({(0 : ℂ)}ᶜ : Set ℂ)) (nhds q₀))
    (hchain : IsChain a h q₀) (hq1 : q₀.2.1 = u₀) :
    q₀ ∈ H0 a h := by
  obtain ⟨hk0, hu0ne, κ, hκ, hmem, hinj_e, hcont, hmer2, hmerC⟩ := he
  have hκne : κ ≠ 0 := hκ
  set f : ℂ → ChainData := fun w => if w = u₀ then q₀ else e ((w - u₀) / κ) with hf
  simp only [H0, Set.mem_ofPred_eq]
  rw [hq1]
  refine ⟨‖κ‖, norm_pos_iff.mpr hκne, f, ?_, ?_, ?_⟩
  · -- ContinuousOn
    intro x hx
    by_cases hxu : x = u₀
    · rw [hxu] at hx ⊢
      change Tendsto f (𝓝[Metric.ball u₀ ‖κ‖] u₀) (𝓝 (f u₀))
      have hins : insert u₀ (Metric.ball u₀ ‖κ‖ \ {u₀}) = Metric.ball u₀ ‖κ‖ :=
        Set.insert_sdiff_self_of_mem (Metric.mem_ball_self (norm_pos_iff.mpr hκne))
      rw [show 𝓝[Metric.ball u₀ ‖κ‖] u₀ = 𝓝[insert u₀ (Metric.ball u₀ ‖κ‖ \ {u₀})] u₀ by rw [hins],
        nhdsWithin_insert]
      rw [tendsto_sup]
      constructor
      · show map f (pure u₀) ≤ 𝓝 (f u₀)
        rw [map_pure]
        exact pure_le_nhds _
      · have hζ : Tendsto (fun w : ℂ => (w - u₀) / κ) (𝓝[Metric.ball u₀ ‖κ‖ \ {u₀}] u₀)
            (𝓝[{(0 : ℂ)}ᶜ] (0 : ℂ)) := by
          rw [tendsto_nhdsWithin_iff]
          refine ⟨?_, ?_⟩
          · simpa using ((by fun_prop : ContinuousAt (fun w : ℂ => (w - u₀) / κ) u₀).tendsto).mono_left
              nhdsWithin_le_nhds
          filter_upwards [self_mem_nhdsWithin] with w hw
          simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
          intro h0
          exact hw.2 (sub_eq_zero.mp ((div_eq_zero_iff.mp h0).resolve_right hκne))
        have hcomp : Tendsto (fun w : ℂ => e ((w - u₀) / κ))
            (𝓝[Metric.ball u₀ ‖κ‖ \ {u₀}] u₀) (𝓝 q₀) := hq0.comp hζ
        have hev : (fun w : ℂ => e ((w - u₀) / κ)) =ᶠ[𝓝[Metric.ball u₀ ‖κ‖ \ {u₀}] u₀] f := by
          filter_upwards [self_mem_nhdsWithin] with w hw
          simp only [hf, if_neg (by simpa using hw.2)]
        have hf0 : f u₀ = q₀ := by simp only [hf]; simp
        rw [hf0]
        exact hcomp.congr' hev
    · have hxmem : (x - u₀) / κ ∈ Metric.ball (0 : ℂ) 1 \ {0} := by
        refine ⟨?_, ?_⟩
        · rw [Metric.mem_ball, dist_zero_right, norm_div, div_lt_one (norm_pos_iff.mpr hκne)]
          simpa [Metric.mem_ball, dist_eq_norm] using hx
        · exact Set.mem_compl_singleton_iff.mpr (div_ne_zero (sub_ne_zero.mpr hxu) hκne)
      have hnhds : Metric.ball (0 : ℂ) 1 \ {0} ∈ 𝓝 ((x - u₀) / κ) :=
        Filter.inter_mem (Metric.isOpen_ball.mem_nhds hxmem.1)
          (isClosed_singleton.isOpen_compl.mem_nhds hxmem.2)
      have hcontat : ContinuousAt (fun w : ℂ => e ((w - u₀) / κ)) x := by
        have hinner : ContinuousAt (fun w : ℂ => (w - u₀) / κ) x := by fun_prop
        exact ContinuousAt.comp (g := e) (f := fun w : ℂ => (w - u₀) / κ) (x := x)
          (hcont.continuousAt hnhds) hinner
      refine (hcontat.congr ?_).continuousWithinAt
      filter_upwards [isOpen_compl_singleton.mem_nhds (by simpa using hxu)] with w hw
      show e ((w - u₀) / κ) = f w
      simp only [hf]
      rw [if_neg (by simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using hw)]
  · -- f u₀ = q₀
    simp only [hf]
    simp
  · -- chain and parameter
    intro u hu
    by_cases hu0 : u = u₀
    · rw [hu0]
      have hfu : f u₀ = q₀ := by simp only [hf]; simp
      rw [hfu]
      exact ⟨hchain, hq1⟩
    · have hζmem : (u - u₀) / κ ∈ Metric.ball (0 : ℂ) 1 \ {0} := by
        refine ⟨?_, ?_⟩
        · rw [Metric.mem_ball, dist_zero_right, norm_div, div_lt_one (norm_pos_iff.mpr hκne)]
          simpa [Metric.mem_ball, dist_eq_norm] using hu
        · exact Set.mem_compl_singleton_iff.mpr (div_ne_zero (sub_ne_zero.mpr hu0) hκne)
      have hfueq : f u = e ((u - u₀) / κ) := by
        simp only [hf]
        rw [if_neg hu0]
      rw [hfueq]
      refine ⟨isChain_of_mem_H0' (hmem _ hζmem).1, ?_⟩
      have hmul : κ * ((u - u₀) / κ) = u - u₀ := by field_simp
      rw [(hmem _ hζmem).2, hk1, pow_one, hmul]
      ring

/-- Finset-indexed finite intersection of `∀ᶠ`. -/
lemma eventually_all_finset {ι α : Type*} [DecidableEq ι] (s : Finset ι) {l : Filter α}
    {p : ι → α → Prop} (h : ∀ i ∈ s, ∀ᶠ a in l, p i a) : ∀ᶠ a in l, ∀ i ∈ s, p i a := by
  classical
  induction s using Finset.induction_on with
  | empty => exact Filter.Eventually.of_forall (by simp)
  | insert i s hi ih =>
    filter_upwards [h i (Finset.mem_insert_self i s),
      ih (fun j hj => h j (Finset.mem_insert_of_mem hj))] with a ha1 ha2
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj'
    · exact ha1
    · exact ha2 j hj'

/-- **A punctured chart with a limit and principal tails has order `k = 1`.** -/
theorem order_le_one_aux {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) {e : ℂ → ChainData} {q₀ : ChainData} {u₀ v₀ : ℂ} {k N : ℕ}
    (he : IsPuncturedChart a h e u₀ k)
    (hq0 : Filter.Tendsto e (nhdsWithin (0 : ℂ) ({(0 : ℂ)}ᶜ : Set ℂ)) (nhds q₀))
    (hq2 : q₀.2.2 = v₀)
    (hN : ∀ ζ : ℂ, 0 < ‖ζ‖ → ‖ζ‖ < 1 → ∀ n : ℕ, N ≤ n →
      (e ζ).1 (n : ℤ) = germC a h (((eqLam a : ℝ) : ℂ) ^ n * (e ζ).2.1) ∧
      (e ζ).1 (-(n : ℤ)) = ugermC a h (((eqLam a : ℝ) : ℂ) ^ n * (e ζ).2.2))
    (hk2 : 2 ≤ k) : False := by
  obtain ⟨hk0, hu0ne, κ, hκ, hmem, hinj_e, hcont, hmer2, hmerC⟩ := he
  have hκne : κ ≠ 0 := hκ
  have hkne : k ≠ 0 := by omega
  obtain ⟨ρg, hρg, -, -, -, hinj, -⟩ := germC_facts ha0 ha1 hh
  have hlam0 : 0 < eqLam a := lam_pos ha0 ha1
  have hlamlt : eqLam a < 1 := lam_lt_one ha0 ha1
  obtain ⟨M₀, hM₀⟩ : ∃ M₀ : ℕ, eqLam a ^ M₀ * ‖v₀‖ < ρg := by
    have ht : Tendsto (fun n : ℕ => eqLam a ^ n * ‖v₀‖) atTop (nhds 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hlam0.le hlamlt).mul_const ‖v₀‖
    have hmem0 : ∀ᶠ n : ℕ in atTop, eqLam a ^ n * ‖v₀‖ < ρg :=
      ht.eventually ((isOpen_lt continuous_id continuous_const).mem_nhds (by simpa using hρg))
    exact hmem0.exists
  set K : ℕ := max N M₀ with hK
  have hNK : N ≤ K := le_max_left _ _
  have hM₀K : M₀ ≤ K := le_max_right _ _
  have hball : ((eqLam a : ℝ) : ℂ) ^ K * q₀.2.2 ∈ Metric.ball (0 : ℂ) ρg := by
    rw [Metric.mem_ball, dist_zero_right, norm_mul, norm_pow, Complex.norm_of_nonneg hlam0.le, hq2]
    calc eqLam a ^ K * ‖v₀‖ ≤ eqLam a ^ M₀ * ‖v₀‖ :=
          mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hlam0.le hlamlt.le hM₀K) (norm_nonneg v₀)
      _ < ρg := hM₀
  obtain ⟨ε, hεpos, huniq⟩ := chain_unique_window (p := q₀) hNK le_rfl hρg hinj hball
  have hcoord : ∀ j : ℤ, Tendsto (fun ζ : ℂ => (e ζ).1 j)
      (nhdsWithin (0 : ℂ) ({(0 : ℂ)}ᶜ : Set ℂ)) (nhds (q₀.1 j)) :=
    fun j => coord_tendsto_of_tendsto hq0 j
  have hψ2lim : Tendsto (fun ζ : ℂ => (e ζ).2.2)
      (nhdsWithin (0 : ℂ) ({(0 : ℂ)}ᶜ : Set ℂ)) (nhds v₀) := by
    rw [← hq2]
    exact psi2_tendsto_of_tendsto hq0
  have hfinset : ∀ i ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
      ∀ᶠ ζ in nhdsWithin (0 : ℂ) ({(0 : ℂ)}ᶜ : Set ℂ), ‖(e ζ).1 i - q₀.1 i‖ < ε :=
    fun i _ => by
      simpa only [dist_eq_norm] using (hcoord i).eventually (Metric.ball_mem_nhds _ hεpos)
  have hwin : ∀ᶠ ζ in nhdsWithin (0 : ℂ) ({(0 : ℂ)}ᶜ : Set ℂ),
      ∀ i ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), ‖(e ζ).1 i - q₀.1 i‖ < ε :=
    eventually_all_finset _ hfinset
  have hpsi2 : ∀ᶠ ζ in nhdsWithin (0 : ℂ) ({(0 : ℂ)}ᶜ : Set ℂ), ‖(e ζ).2.2 - v₀‖ < ε := by
    simpa only [dist_eq_norm] using hψ2lim.eventually (Metric.ball_mem_nhds _ hεpos)
  have hcomb : ∀ᶠ ζ in nhdsWithin (0 : ℂ) ({(0 : ℂ)}ᶜ : Set ℂ),
      (∀ i ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), ‖(e ζ).1 i - q₀.1 i‖ < ε) ∧
        ‖(e ζ).2.2 - v₀‖ < ε := hwin.and hpsi2
  obtain ⟨δ, hδpos, hsub⟩ := Metric.mem_nhdsWithin_iff.mp hcomb
  set ρ : ℝ := min δ 1 with hρdef
  have hρpos : 0 < ρ := lt_min hδpos one_pos
  have hρ1 : ρ ≤ 1 := min_le_right _ _
  obtain ⟨ω, hωk, hωne1, hωnorm⟩ : ∃ ω : ℂ, ω ^ k = 1 ∧ ω ≠ 1 ∧ ‖ω‖ = 1 := by
    have hroot := Complex.isPrimitiveRoot_exp k hkne
    exact ⟨_, hroot.pow_eq_one, hroot.ne_one (by omega), hroot.norm'_eq_one hkne⟩
  obtain ⟨ζ, hζ0, hζρ⟩ : ∃ ζ : ℂ, 0 < ‖ζ‖ ∧ ‖ζ‖ < ρ := by
    refine ⟨((ρ / 2 : ℝ) : ℂ), ?_, ?_⟩
    · rw [Complex.norm_of_nonneg (by positivity : (0 : ℝ) ≤ ρ / 2)]
      linarith
    · rw [Complex.norm_of_nonneg (by positivity : (0 : ℝ) ≤ ρ / 2)]
      linarith
  have hζ1 : ‖ζ‖ < 1 := lt_of_lt_of_le hζρ hρ1
  have hζmem : ζ ∈ Metric.ball (0 : ℂ) 1 \ {0} :=
    ⟨by simpa [Metric.mem_ball, dist_zero_right] using hζ1,
      Set.mem_compl_singleton_iff.mpr (norm_pos_iff.mp hζ0)⟩
  have hωζ0 : 0 < ‖ω * ζ‖ := by rw [norm_mul, hωnorm, one_mul]; exact hζ0
  have hωζ1 : ‖ω * ζ‖ < 1 := by rw [norm_mul, hωnorm, one_mul]; exact hζ1
  have hωζmem : ω * ζ ∈ Metric.ball (0 : ℂ) 1 \ {0} :=
    ⟨by simpa [Metric.mem_ball, dist_zero_right] using hωζ1,
      Set.mem_compl_singleton_iff.mpr (norm_pos_iff.mp hωζ0)⟩
  have hζδ : ζ ∈ Metric.ball (0 : ℂ) δ ∩ ({(0 : ℂ)}ᶜ : Set ℂ) :=
    ⟨by simpa [Metric.mem_ball, dist_zero_right] using lt_of_lt_of_le hζρ (min_le_left _ _),
      Set.mem_compl_singleton_iff.mpr (norm_pos_iff.mp hζ0)⟩
  have hωζδ : ω * ζ ∈ Metric.ball (0 : ℂ) δ ∩ ({(0 : ℂ)}ᶜ : Set ℂ) :=
    ⟨by
      rw [Metric.mem_ball, dist_zero_right, norm_mul, hωnorm, one_mul]
      exact lt_of_lt_of_le hζρ (min_le_left _ _),
      Set.mem_compl_singleton_iff.mpr (norm_pos_iff.mp hωζ0)⟩
  have hclos1 : ∀ k : ℤ, |k| ≤ (K : ℤ) → ‖(e ζ).1 k - q₀.1 k‖ < ε :=
    fun k hk => (hsub hζδ).1 k (Finset.mem_Icc.mpr (abs_le.mp hk))
  have hclos2 : ∀ k : ℤ, |k| ≤ (K : ℤ) → ‖(e (ω * ζ)).1 k - q₀.1 k‖ < ε :=
    fun k hk => (hsub hωζδ).1 k (Finset.mem_Icc.mpr (abs_le.mp hk))
  have hpsi1 : ‖(e ζ).2.2 - q₀.2.2‖ < ε := by
    rw [hq2]; exact (hsub hζδ).2
  have hpsi2'' : ‖(e (ω * ζ)).2.2 - q₀.2.2‖ < ε := by
    rw [hq2]; exact (hsub hωζδ).2
  have hψ1eq : (e ζ).2.1 = (e (ω * ζ)).2.1 := by
    rw [(hmem ζ hζmem).2, (hmem (ω * ζ) hωζmem).2, mul_pow, hωk, one_mul]
  have heq : e ζ = e (ω * ζ) :=
    huniq (e ζ) (e (ω * ζ)) (isChain_of_mem_H0' (hmem ζ hζmem).1)
      (isChain_of_mem_H0' (hmem (ω * ζ) hωζmem).1) hψ1eq hclos1 hclos2 hpsi1 hpsi2''
      (fun n hn => (hN ζ hζ0 hζ1 n hn).1) (fun n hn => (hN (ω * ζ) hωζ0 hωζ1 n hn).1)
      (fun n hn => (hN ζ hζ0 hζ1 n (le_trans hNK hn)).2)
      (fun n hn => (hN (ω * ζ) hωζ0 hωζ1 n (le_trans hNK hn)).2)
  have hne : ζ ≠ ω * ζ := by
    intro hcon
    have hzero : (ω - 1) * ζ = 0 := by rw [sub_mul, one_mul, ← hcon, sub_self]
    rcases mul_eq_zero.mp hzero with h1 | h2
    · exact hωne1 (sub_eq_zero.mp h1)
    · exact (norm_pos_iff.mp hζ0) h2
  exact hne (hinj_e hζmem hωζmem heq)

lemma bsq_subO2_eqMirror (a : ℝ) (P : ℂ × ℂ) :
    bsq (subO2 a (eqMirror P)) = bsq (subO1 a P) := by
  simp only [eqMirror, subO2, subO1, bsq]
  ring

lemma bsq_subO1_eqMirror (a : ℝ) (P : ℂ × ℂ) :
    bsq (subO1 a (eqMirror P)) = bsq (subO2 a P) := by
  simp only [eqMirror, subO1, subO2, bsq]
  ring

/-- **The limit chain of a punctured chart is a chain.** -/
theorem window_isChain_aux {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
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
    (hsmall : ‖u₀‖ < δ * (eqLam a) ^ N) (hvs : ‖v₀‖ < δ)
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
  have hbnorm : ∀ m : ℕ, N ≤ m → ‖(((eqLam a : ℝ) : ℂ) ^ m * u₀)‖ < δ := by
    intro m hm
    rw [norm_mul, norm_pow, Complex.norm_of_nonneg hlam0.le]
    calc eqLam a ^ m * ‖u₀‖ ≤ eqLam a ^ N * ‖u₀‖ :=
          mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hlam0.le hlamlt.le hm) (norm_nonneg u₀)
      _ < eqLam a ^ N * (δ * eqLam a ^ N) := mul_lt_mul_of_pos_left hsmall (pow_pos hlam0 N)
      _ = δ * (eqLam a ^ N * eqLam a ^ N) := by ring
      _ = δ * eqLam a ^ (2 * N) := by rw [← pow_add]; ring_nf
      _ ≤ δ * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ hlam0.le hlamlt.le) hδ.le
      _ = δ := mul_one δ
  have hbnormv : ∀ m : ℕ, N ≤ m → ‖(((eqLam a : ℝ) : ℂ) ^ m * v₀)‖ < δ := by
    intro m _
    rw [norm_mul, norm_pow, Complex.norm_of_nonneg hlam0.le]
    calc eqLam a ^ m * ‖v₀‖ ≤ 1 * ‖v₀‖ :=
          mul_le_mul_of_nonneg_right (pow_le_one₀ hlam0.le hlamlt.le) (norm_nonneg v₀)
      _ = ‖v₀‖ := one_mul _
      _ < δ := hvs
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
theorem genuine_chart_window_degenerate {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) {e : ℂ → ChainData} {u₀ v₀ : ℂ} {k N : ℕ}
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
    (hsmall : ‖u₀‖ < δ * (eqLam a) ^ N) (hvs : ‖v₀‖ < δ) :
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
    window_lim_aux (a := a) (h := h) (r := r) (e := e) (u₀ := u₀) (v₀ := v₀) (k := k) (N := N)
      (Ke := Ke) (Lam := Lam) (Q := Q) (δ := δ) ha0 ha1 hh he hv hN hN1 hδ hF hreg hsmall hvs hH
  have hchain : IsChain a h q₀ :=
    window_isChain_aux (a := a) (h := h) (r := r) (e := e) (q₀ := q₀) (u₀ := u₀) (v₀ := v₀)
      (k := k) (N := N) (Ke := Ke) (Lam := Lam) (Q := Q) (δ := δ)
      ha0 ha1 hh he htend hv hN hN1 hδ hF hreg hsmall hvs hq1 hq2 hH hwin
  have hk0 : 0 < k := he.1
  rcases eq_or_ne k 1 with hk1 | hk1
  · exact hgen ⟨q₀, mem_H0_of_k_eq_one_aux (a := a) (h := h) (r := r) (e := e) (q₀ := q₀)
      (u₀ := u₀) (v₀ := v₀) (k := k) (N := N) ha0 ha1 hh he hk1 htend hchain hq1, htend⟩
  · exact (order_le_one_aux (a := a) (h := h) (r := r) (e := e) (q₀ := q₀) (u₀ := u₀) (v₀ := v₀)
      (k := k) (N := N) ha0 ha1 hh he htend hq2 hN (by omega)).elim

end

end Work.EQ
