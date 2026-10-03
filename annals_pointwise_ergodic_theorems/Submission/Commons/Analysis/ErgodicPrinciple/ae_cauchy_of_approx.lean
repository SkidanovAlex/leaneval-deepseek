import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov

namespace Commons.Analysis.ErgodicPrinciple

open MeasureTheory Filter
open scoped ENNReal Topology

/-- If `f n : X → ℝ≥0∞` are measurable and `eLpNorm (f n) p μ → 0` for `0 < p < ∞`, then there
is a strictly increasing subsequence along which `f` tends to `0` almost everywhere. -/
theorem exists_seq_tendsto_ae_zero_of_eLpNorm_tendsto_zero
    {X : Type*} [MeasurableSpace X] {μ : MeasureTheory.Measure X} {p : ENNReal}
    (hp0 : p ≠ 0) (hpT : p ≠ ⊤) {f : ℕ → X → ENNReal}
    (hf : ∀ n, Measurable (f n))
    (htend : Filter.Tendsto (fun n => MeasureTheory.eLpNorm (f n) p μ) Filter.atTop (nhds 0)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ x ∂μ, Filter.Tendsto (fun k => f (ns k) x) Filter.atTop (nhds 0) := by
  classical
  have hpt : 0 < p.toReal := ENNReal.toReal_pos hp0 hpT
  have hev : ∀ k : ℕ, ∀ᶠ n in atTop,
      μ {x | (2 : ℝ≥0∞)⁻¹ ^ k ≤ f n x} ≤ (2 : ℝ≥0∞)⁻¹ ^ k := by
    intro k
    set c : ℝ≥0∞ := (2 : ℝ≥0∞)⁻¹ ^ k with hc
    have hcpos : 0 < c := by
      rw [hc]; exact ENNReal.pow_pos (ENNReal.inv_pos.mpr (by norm_num)) k
    have hctop : c ≠ ∞ := by rw [hc]; finiteness
    have hkey : Tendsto (fun n => μ {x | c ≤ f n x}) atTop (nhds 0) := by
      set A : ℝ≥0∞ := c ^ p.toReal with hA
      have hA0 : A ≠ 0 := by rw [hA]; exact (ENNReal.rpow_pos hcpos hctop).ne'
      have hAtop : A ≠ ∞ := by
        rw [hA]; exact (ENNReal.rpow_lt_top_of_nonneg (le_of_lt hpt) hctop).ne
      have hY : Tendsto (fun n => (eLpNorm (f n) p μ) ^ p.toReal) atTop (nhds 0) := by
        have hcont : Tendsto (fun x : ℝ≥0∞ => x ^ p.toReal) (nhds 0) (nhds (0 ^ p.toReal)) :=
          (ENNReal.continuous_rpow_const (y := p.toReal)).tendsto 0
        have hcomp := hcont.comp htend
        rw [ENNReal.zero_rpow_of_pos hpt] at hcomp
        exact hcomp
      rw [ENNReal.tendsto_nhds_zero]
      intro δ hδ
      filter_upwards [(ENNReal.tendsto_nhds_zero.mp hY) (A * δ)
        (ENNReal.mul_pos hA0 hδ.ne')] with n hn
      have hcheb : A * μ {x | c ≤ f n x} ≤ (eLpNorm (f n) p μ) ^ p.toReal := by
        have h := mul_meas_ge_le_pow_eLpNorm' μ hp0 hpT c (f := f n)
        simpa [hA] using h
      exact (ENNReal.mul_le_mul_iff_right hA0 hAtop).mp (le_trans hcheb hn)
    have := (ENNReal.tendsto_nhds_zero.mp hkey) c hcpos
    simpa [hc] using this
  have hN : ∀ k : ℕ, ∃ N : ℕ, ∀ n ≥ N,
      μ {x | (2 : ℝ≥0∞)⁻¹ ^ k ≤ f n x} ≤ (2 : ℝ≥0∞)⁻¹ ^ k :=
    fun k => eventually_atTop.mp (hev k)
  choose N hNspec using hN
  let ns : ℕ → ℕ := fun k => k + (Finset.range (k + 1)).sup N
  have hns_spec : ∀ k, μ {x | (2 : ℝ≥0∞)⁻¹ ^ k ≤ f (ns k) x} ≤ (2 : ℝ≥0∞)⁻¹ ^ k := by
    intro k
    apply hNspec k (ns k)
    have hle : N k ≤ (Finset.range (k + 1)).sup N :=
      Finset.le_sup (f := N) (Finset.mem_range.mpr (Nat.lt_succ_self k))
    simp only [ns]
    omega
  have hns_strict : StrictMono ns := by
    refine strictMono_nat_of_lt_succ (fun k => ?_)
    have hS : (Finset.range (k + 1)).sup N ≤ (Finset.range (k + 1 + 1)).sup N :=
      Finset.sup_mono (fun a ha => by simp only [Finset.mem_range] at ha ⊢; omega)
    simp only [ns]
    omega
  have hsum2 : (∑' k : ℕ, (2 : ℝ≥0∞)⁻¹ ^ k) ≠ ∞ := by
    rw [ENNReal.tsum_geometric]
    norm_num
  have hsum : (∑' k : ℕ, μ {x | (2 : ℝ≥0∞)⁻¹ ^ k ≤ f (ns k) x}) ≠ ∞ :=
    ne_top_of_le_ne_top hsum2 (ENNReal.tsum_le_tsum hns_spec)
  have hBC := measure_setOfPred_frequently_eq_zero (μ := μ)
    (p := fun k (x : X) => (2 : ℝ≥0∞)⁻¹ ^ k ≤ f (ns k) x) hsum
  refine ⟨ns, hns_strict, ?_⟩
  rw [ae_iff]
  refine le_antisymm (le_trans (measure_mono ?_) (le_of_eq hBC)) zero_le
  intro x hx
  rw [Set.mem_ofPred_eq] at hx
  have hnot : ∃ ε : ℝ≥0∞, 0 < ε ∧ ∃ᶠ k in atTop, ε < f (ns k) x := by
    have h1 := hx
    rw [ENNReal.tendsto_nhds_zero] at h1
    push Not at h1
    exact h1
  obtain ⟨ε, hεpos, hεfreq⟩ := hnot
  obtain ⟨K, hK⟩ := ENNReal.exists_inv_two_pow_lt hεpos.ne'
  have hbase : (2 : ℝ≥0∞)⁻¹ ≤ 1 := ENNReal.inv_le_one.mpr (by norm_num)
  have hmono : ∀ᶠ k in atTop, (2 : ℝ≥0∞)⁻¹ ^ k ≤ (2 : ℝ≥0∞)⁻¹ ^ K :=
    eventually_atTop.mpr ⟨K, fun k hk =>
      pow_le_pow_of_le_one (by simp : (0:ℝ≥0∞) ≤ (2:ℝ≥0∞)⁻¹) hbase hk⟩
  exact (hεfreq.and_eventually hmono).mono
    (fun k hk => le_trans hk.2 (le_of_lt (lt_trans hK hk.1)))

/-- **Abstract almost-everywhere Cauchy criterion.** If a sequence `u n` is approximated by
sequences `v j n` which converge almost everywhere, with the approximation error controlled by
`M j` in `L^p` for some `0 < p < ∞`, then `u n` is almost everywhere a Cauchy sequence. -/
theorem ae_cauchy_of_approx {X : Type*} [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    {p : ENNReal} (hp0 : p ≠ 0) (hpT : p ≠ ⊤) {u : ℕ → X → ℂ} {v : ℕ → ℕ → X → ℂ}
    {M : ℕ → X → ENNReal} (hM : ∀ j, Measurable (M j))
    (hMtend : Filter.Tendsto (fun j => MeasureTheory.eLpNorm (M j) p μ) Filter.atTop (nhds 0))
    (hbd : ∀ (j n : ℕ) (x : X), ‖u n x - v j n x‖ₑ ≤ M j x)
    (hv : ∀ j, ∀ᵐ x ∂μ, ∃ L : ℂ, Filter.Tendsto (fun n => v j n x) Filter.atTop (nhds L)) :
    ∀ᵐ x ∂μ, CauchySeq (fun n => u n x) := by
  classical
  obtain ⟨ns, hns_strict, hns_ae⟩ :=
    exists_seq_tendsto_ae_zero_of_eLpNorm_tendsto_zero hp0 hpT hM hMtend
  have hv_all : ∀ᵐ x ∂μ, ∀ j, ∃ L : ℂ, Tendsto (fun n => v j n x) atTop (nhds L) :=
    ae_all_iff.mpr hv
  filter_upwards [hns_ae, hv_all] with x hMx hvx
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨K, hK⟩ : ∃ K, M (ns K) x ≤ ENNReal.ofReal (ε / 4) := by
    obtain ⟨a, ha⟩ := Filter.eventually_atTop.mp
      ((ENNReal.tendsto_nhds_zero.mp hMx) (ENNReal.ofReal (ε / 4))
        (ENNReal.ofReal_pos.mpr (by linarith)))
    exact ⟨a, ha a le_rfl⟩
  have hKreal : (M (ns K) x).toReal ≤ ε / 4 := by
    calc (M (ns K) x).toReal ≤ (ENNReal.ofReal (ε / 4)).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hK
      _ = ε / 4 := ENNReal.toReal_ofReal (by linarith)
  obtain ⟨L, hL⟩ := hvx (ns K)
  have hLc : CauchySeq (fun n => v (ns K) n x) := hL.cauchySeq
  rw [Metric.cauchySeq_iff] at hLc
  obtain ⟨N, hN⟩ := hLc (ε / 2) (by linarith)
  have hbound : ∀ n, ‖u n x - v (ns K) n x‖ ≤ ε / 4 := by
    intro n
    calc ‖u n x - v (ns K) n x‖ = (‖u n x - v (ns K) n x‖ₑ).toReal := by simp
      _ ≤ (M (ns K) x).toReal := ENNReal.toReal_mono (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hK) (hbd (ns K) n x)
      _ ≤ ε / 4 := hKreal
  refine ⟨N, fun m hm n hn => ?_⟩
  have hmid : ‖v (ns K) m x - v (ns K) n x‖ < ε / 2 := by
    have := hN m hm n hn
    rwa [dist_eq_norm] at this
  have htri : ‖u m x - u n x‖ ≤ ‖u m x - v (ns K) m x‖
      + ‖v (ns K) m x - v (ns K) n x‖ + ‖v (ns K) n x - u n x‖ := by
    rw [show u m x - u n x = (u m x - v (ns K) m x)
        + (v (ns K) m x - v (ns K) n x) + (v (ns K) n x - u n x) by ring]
    calc ‖(u m x - v (ns K) m x) + (v (ns K) m x - v (ns K) n x)
            + (v (ns K) n x - u n x)‖
        ≤ ‖(u m x - v (ns K) m x) + (v (ns K) m x - v (ns K) n x)‖
            + ‖v (ns K) n x - u n x‖ := norm_add_le _ _
      _ ≤ (‖u m x - v (ns K) m x‖ + ‖v (ns K) m x - v (ns K) n x‖)
            + ‖v (ns K) n x - u n x‖ := by
          have := norm_add_le (u m x - v (ns K) m x) (v (ns K) m x - v (ns K) n x)
          linarith
  rw [dist_eq_norm]
  have hlast : ‖v (ns K) n x - u n x‖ ≤ ε / 4 := by
    rw [norm_sub_rev]; exact hbound n
  linarith [htri, hbound m, hmid, hlast]

end Commons.Analysis.ErgodicPrinciple