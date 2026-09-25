import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.Order.CompletePartialOrder

namespace Commons.Analysis.Oscillation

open MeasureTheory Filter Finset
open scoped BigOperators ENNReal Topology

/-- Pointwise core: if a monotone sequence `t` tends to infinity, `u` converges along `t`
to `L`, and the total variation of `u` inside the block `[t M, t (M+1))` tends to `0`,
then `u` converges to `L`. -/
lemma tendsto_of_block_difference_aux {u : ℕ → ℝ} {t : ℕ → ℕ} {L : ℝ}
    (hmono : Monotone t) (ht : Tendsto t atTop atTop)
    (hlac : Tendsto (fun n => u (t n)) atTop (𝓝 L))
    (hvar : Tendsto (fun M => ∑ j ∈ Finset.Icc (t M) (t (M + 1) - 1), |u (j + 1) - u j|)
      atTop (𝓝 0)) :
    Tendsto u atTop (𝓝 L) := by
  rw [Metric.tendsto_atTop] at hlac hvar ⊢
  intro ε hε
  have hε2 : (0 : ℝ) < ε / 2 := by linarith
  obtain ⟨M₁, h₁⟩ := hlac (ε / 2) hε2
  obtain ⟨M₂, h₂⟩ := hvar (ε / 2) hε2
  refine ⟨t (max M₁ M₂), fun n hn => ?_⟩
  have hM₁ : M₁ ≤ max M₁ M₂ := le_max_left _ _
  have hM₂ : M₂ ≤ max M₁ M₂ := le_max_right _ _
  -- the least block index whose right endpoint passes `n`
  have hex : ∃ m, t (m + 1) > n := by
    obtain ⟨i, hi⟩ := (tendsto_atTop_atTop.1 ht) (n + 1)
    have hi' : n + 1 ≤ t i := hi i le_rfl
    exact ⟨i, lt_of_lt_of_le (by omega) (hmono (by omega : i ≤ i + 1))⟩
  obtain ⟨m, hm_spec, hm_min⟩ : ∃ m, t (m + 1) > n ∧ ∀ j, j < m → ¬ (t (j + 1) > n) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun j hj => Nat.find_min hex hj⟩
  have hKm : max M₁ M₂ ≤ m := by
    by_contra h
    push Not at h
    have h1 : t (m + 1) ≤ t (max M₁ M₂) := hmono (by omega)
    omega
  have htm : t m ≤ n := by
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · subst h0
      have hmax0 : max M₁ M₂ = 0 := Nat.le_zero.1 hKm
      rw [hmax0] at hn
      exact hn
    · have hmin := hm_min (m - 1) (by omega)
      have he : m - 1 + 1 = m := by omega
      rw [he] at hmin
      exact le_of_not_gt hmin
  have hblk := h₂ m (le_trans hM₂ hKm)
  have hsum_nonneg : 0 ≤ ∑ j ∈ Finset.Icc (t m) (t (m + 1) - 1), |u (j + 1) - u j| :=
    Finset.sum_nonneg fun j _ => abs_nonneg _
  have hblk' : (∑ j ∈ Finset.Icc (t m) (t (m + 1) - 1), |u (j + 1) - u j|) < ε / 2 := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hsum_nonneg] at hblk
    exact hblk
  have hsingle : |u n - u (t m)| ≤ ∑ j ∈ Finset.Icc (t m) (t (m + 1) - 1), |u (j + 1) - u j| := by
    rw [← Finset.sum_Ico_sub u htm]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun j _ _ => abs_nonneg _)
    intro j hj
    rw [Finset.mem_Ico] at hj
    rw [Finset.mem_Icc]
    exact ⟨hj.1, by omega⟩
  have hL : |u (t m) - L| < ε / 2 := by
    have := h₁ m (le_trans hM₁ hKm)
    rwa [Real.dist_eq] at this
  have htri : |u n - L| ≤ |u n - u (t m)| + |u (t m) - L| := by
    have h := abs_add_le (u n - u (t m)) (u (t m) - L)
    have heq : (u n - u (t m)) + (u (t m) - L) = u n - L := by ring
    rwa [heq] at h
  rw [Real.dist_eq]
  linarith

/-- If a lacunary subsequence `t` of a sequence `u` converges a.e. to `L`, and the
consecutive differences of `u` inside each block `[t M, t (M+1))` are summable in `L^p`
uniformly in `M₀`, then `u` itself converges a.e. to `L`.  (This is the "short variation"
form of the oscillation argument; the pointwise input is that the total variation of `u`
inside each block tends to `0`, which follows from the uniform `L^p` bound.) -/
theorem ae_tendsto_of_block_difference {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {u : ℕ → X → ℝ} {t : ℕ → ℕ} {L : X → ℝ} {p : ℝ} (hp : 1 ≤ p)
    (hmono : Monotone t) (ht : Tendsto t atTop atTop)
    (hu : ∀ n, Measurable (u n))
    (hlac : ∀ᵐ x ∂μ, Tendsto (fun n => u (t n) x) atTop (𝓝 (L x)))
    (hbd : ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ M₀ : ℕ,
      ∫⁻ x, ‖∑ M ∈ Finset.range M₀, ∑ N ∈ Finset.Icc (t M) (t (M + 1) - 1),
          |u (N + 1) x - u N x|‖ₑ ^ p ∂μ ≤ K) :
    ∀ᵐ x ∂μ, Tendsto (fun N => u N x) atTop (𝓝 (L x)) := by
  classical
  have hp0 : (0 : ℝ) < p := by linarith
  have hp1 : (0 : ℝ) < 1 / p := div_pos one_pos hp0
  obtain ⟨K, hK, hbd⟩ := hbd
  -- the variation inside the `M`-th block
  set V : ℕ → X → ℝ :=
    fun M x => ∑ N ∈ Finset.Icc (t M) (t (M + 1) - 1), |u (N + 1) x - u N x| with hV
  have hVnn : ∀ M x, 0 ≤ V M x := by
    intro M x
    simp only [hV]
    exact Finset.sum_nonneg fun N _ => abs_nonneg _
  have hVmeas : ∀ M, Measurable (V M) := by
    intro M
    simp only [hV]
    exact Finset.measurable_sum _ fun N _ => ((hu (N + 1)).sub (hu N)).abs
  -- `F M₀ x` is the `p`-th power of the cumulative variation up to block `M₀`
  set F : ℕ → X → ℝ≥0∞ :=
    fun M₀ x => ‖∑ M ∈ Finset.range M₀, V M x‖ₑ ^ p with hF
  have hFmeas : ∀ M₀, Measurable (F M₀) := by
    intro M₀
    simp only [hF]
    have hg : Measurable fun x : X => ∑ M ∈ Finset.range M₀, V M x :=
      Finset.measurable_sum _ fun M _ => hVmeas M
    exact ENNReal.continuous_rpow_const.measurable.comp hg.enorm
  have hFmono : Monotone F := by
    intro M₀ M₁ hle x
    simp only [hF]
    have hle' : (∑ M ∈ Finset.range M₀, V M x) ≤ ∑ M ∈ Finset.range M₁, V M x :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hle)
        (fun i _ _ => hVnn i x)
    have h0 : (0 : ℝ) ≤ ∑ M ∈ Finset.range M₀, V M x := Finset.sum_nonneg fun M _ => hVnn M x
    have hen : ‖∑ M ∈ Finset.range M₀, V M x‖ₑ ≤ ‖∑ M ∈ Finset.range M₁, V M x‖ₑ := by
      rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs]
      exact ENNReal.ofReal_le_ofReal (abs_le_abs hle' (by linarith))
    exact ENNReal.rpow_le_rpow hen hp0.le
  have hbdF : ∀ M₀, ∫⁻ x, F M₀ x ∂μ ≤ K := by
    intro M₀
    simpa only [hF, hV] using hbd M₀
  have hint : ∫⁻ x, (⨆ M₀, F M₀ x) ∂μ ≤ K := by
    rw [lintegral_iSup hFmeas hFmono]
    exact iSup_le hbdF
  have hlt : ∫⁻ x, (⨆ M₀, F M₀ x) ∂μ < ⊤ := lt_of_le_of_lt hint hK
  have hae : ∀ᵐ x ∂μ, (⨆ M₀, F M₀ x) < ⊤ :=
    ae_lt_top (Measurable.iSup hFmeas) hlt.ne
  filter_upwards [hae, hlac] with x hxS hxlac
  refine tendsto_of_block_difference_aux hmono ht hxlac ?_
  -- a.e. the cumulative variation is bounded, hence the block variations tend to zero
  have hbound : ∀ k : ℕ, ∑ M ∈ Finset.range k, V M x ≤ ((⨆ M₀, F M₀ x) ^ (1 / p)).toReal := by
    intro k
    have hCtop : (⨆ M₀, F M₀ x) ^ (1 / p) ≠ ⊤ :=
      (ENNReal.rpow_lt_top_of_nonneg hp1.le (ne_of_lt hxS)).ne
    have h1 : ‖∑ M ∈ Finset.range k, V M x‖ₑ ≤ (⨆ M₀, F M₀ x) ^ (1 / p) := by
      have h2 : (‖∑ M ∈ Finset.range k, V M x‖ₑ ^ p) ^ (1 / p)
          ≤ (⨆ M₀, F M₀ x) ^ (1 / p) :=
        ENNReal.rpow_le_rpow (by simpa only [hF] using le_iSup (fun M₀ => F M₀ x) k) hp1.le
      rwa [← ENNReal.rpow_mul, mul_one_div_cancel hp0.ne', ENNReal.rpow_one] at h2
    have h3 : ENNReal.ofReal |∑ M ∈ Finset.range k, V M x| ≤ (⨆ M₀, F M₀ x) ^ (1 / p) := by
      rwa [Real.enorm_eq_ofReal_abs] at h1
    have h4 : |∑ M ∈ Finset.range k, V M x| ≤ ((⨆ M₀, F M₀ x) ^ (1 / p)).toReal :=
      (ENNReal.ofReal_le_iff_le_toReal hCtop).1 h3
    have h5 : (0 : ℝ) ≤ ∑ M ∈ Finset.range k, V M x := Finset.sum_nonneg fun M _ => hVnn M x
    rwa [abs_of_nonneg h5] at h4
  have hSmono : Monotone fun k : ℕ => ∑ M ∈ Finset.range k, V M x := by
    intro k l hkl
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hkl)
      (fun i _ _ => hVnn i x)
  have hSbdd : BddAbove (Set.range fun k : ℕ => ∑ M ∈ Finset.range k, V M x) :=
    ⟨_, by rintro _ ⟨k, rfl⟩; exact hbound k⟩
  have hStend : Tendsto (fun k : ℕ => ∑ M ∈ Finset.range k, V M x) atTop
      (𝓝 (⨆ k, ∑ M ∈ Finset.range k, V M x)) := tendsto_atTop_ciSup hSmono hSbdd
  have hshift : Tendsto (fun k : ℕ => ∑ M ∈ Finset.range (k + 1), V M x) atTop
      (𝓝 (⨆ k, ∑ M ∈ Finset.range k, V M x)) :=
    hStend.comp ((tendsto_add_atTop_iff_nat 1).2 tendsto_id)
  have hsub := hshift.sub hStend
  rw [sub_self] at hsub
  have hVtend : Tendsto (fun k : ℕ => V k x) atTop (𝓝 0) := by
    convert hsub using 1
    funext k
    rw [Finset.sum_range_succ]
    ring
  simpa only [hV] using hVtend

end Commons.Analysis.Oscillation