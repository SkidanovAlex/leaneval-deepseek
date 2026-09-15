import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

namespace Commons.Analysis.DirichletSeries

open Filter Finset
open scoped BigOperators Topology

/-!
# Abel's theorem for Dirichlet series

If `∑ a n` converges to `L` (as a limit of partial sums over `Finset.range`), then the
conditionally-summed Dirichlet series `∑'[conditional ℕ] n, a n * n ^ (-σ)` tends to `L`
as `σ → 0⁺`.
-/

/-- Summation by parts (Abel transformation) for range sums. -/
lemma sum_range_mul_eq_abel_partial (u w : ℕ → ℝ) (N : ℕ) :
    ∑ n ∈ Finset.range N, u n * w n =
      w (N - 1) * (∑ n ∈ Finset.range N, u n)
        - ∑ i ∈ Finset.range (N - 1), (w (i + 1) - w i) * (∑ n ∈ Finset.range (i + 1), u n) := by
  have h := Finset.sum_range_by_parts (f := w) (g := u) N
  simp only [smul_eq_mul] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The Abel weight `(j+1)^{-σ} - (j+2)^{-σ}`. -/
noncomputable def dirichletAbelWeight (j : ℕ) (σ : ℝ) : ℝ :=
  ((j + 1 : ℕ) : ℝ) ^ (-σ) - ((j + 2 : ℕ) : ℝ) ^ (-σ)

lemma dirichletAbelWeight_nonneg {σ : ℝ} (hσ : 0 < σ) (j : ℕ) : 0 ≤ dirichletAbelWeight j σ := by
  rw [dirichletAbelWeight]
  have hx : (0:ℝ) < ((j + 1 : ℕ) : ℝ) := by positivity
  have hxy : ((j + 1 : ℕ) : ℝ) ≤ ((j + 2 : ℕ) : ℝ) := by push_cast; linarith
  have := Real.rpow_le_rpow_of_nonpos hx hxy (by linarith : -σ ≤ 0)
  linarith

lemma sum_range_dirichletAbelWeight (σ : ℝ) (N : ℕ) :
    ∑ j ∈ Finset.range N, dirichletAbelWeight j σ = 1 - ((N + 1 : ℕ) : ℝ) ^ (-σ) := by
  have h := Finset.sum_range_sub (fun k : ℕ => ((k + 1 : ℕ) : ℝ) ^ (-σ)) N
  have key : (∑ j ∈ Finset.range N, dirichletAbelWeight j σ)
      = - ∑ i ∈ Finset.range N,
          ((((i + 1 + 1 : ℕ)) : ℝ) ^ (-σ) - (((i + 1 : ℕ)) : ℝ) ^ (-σ)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [dirichletAbelWeight]
    have hc : (((i + 1 + 1 : ℕ)) : ℝ) = (((i + 2 : ℕ)) : ℝ) := rfl
    rw [hc]
    ring
  rw [key, h]
  have h1 : (((0 + 1 : ℕ)) : ℝ) ^ (-σ) = (1:ℝ) := by
    rw [show ((0 + 1 : ℕ) : ℝ) = (1:ℝ) by norm_num, Real.one_rpow]
  rw [h1]
  ring

lemma tendsto_natCast_rpow_neg_atTop {σ : ℝ} (hσ : 0 < σ) :
    Tendsto (fun N : ℕ => ((N : ℕ) : ℝ) ^ (-σ)) atTop (nhds 0) :=
  (tendsto_rpow_neg_atTop hσ).comp tendsto_natCast_atTop_atTop

lemma tendsto_sum_range_dirichletAbelWeight (K : ℕ) :
    Tendsto (fun σ : ℝ => ∑ j ∈ Finset.range K, dirichletAbelWeight j σ)
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0) := by
  have h1 : Tendsto (fun σ : ℝ => ((K + 1 : ℕ) : ℝ) ^ (-σ))
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 1) := by
    have hneg : Tendsto (fun σ : ℝ => -σ) (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0) := by
      simpa using (continuous_neg.tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds
    have hc := (Real.continuousAt_const_rpow (a := ((K + 1 : ℕ) : ℝ)) (b := 0)
      (by positivity)).tendsto
    have := hc.comp hneg
    simpa [Function.comp_def, Real.rpow_zero] using this
  have h2 := (tendsto_const_nhds (x := (1:ℝ))).sub h1
  rw [sub_self] at h2
  refine h2.congr' ?_
  filter_upwards with σ
  rw [sum_range_dirichletAbelWeight]

lemma hasSum_dirichletAbelWeight {σ : ℝ} (hσ : 0 < σ) : HasSum (fun j => dirichletAbelWeight j σ) 1 := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun j => dirichletAbelWeight_nonneg hσ j)]
  have h1 : Tendsto (fun N : ℕ => ((N + 1 : ℕ) : ℝ) ^ (-σ)) atTop (nhds 0) :=
    tendsto_natCast_rpow_neg_atTop hσ |>.comp (Filter.tendsto_add_atTop_nat 1)
  have h2 := (tendsto_const_nhds (x := (1:ℝ))).sub h1
  rw [sub_zero] at h2
  refine h2.congr' ?_
  filter_upwards with N
  rw [sum_range_dirichletAbelWeight]

/-- Abel's summation formula in the shape needed for Dirichlet series: writing `S m = ∑_{n<m} a n`
the partial sums `∑_{n<N+2} a n * n^{-σ}` are rewritten in terms of the weights
`dirichletAbelWeight j σ` and the "tails" `S (j+2) - L`. -/
lemma dirichlet_abel_partial_sums (a : ℕ → ℝ) (ha0 : a 0 = 0) {σ : ℝ} (hσ : 0 < σ) (L : ℝ) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 2), a n * (n : ℝ) ^ (-σ)
      = ((N + 1 : ℕ) : ℝ) ^ (-σ) * ((∑ n ∈ Finset.range (N + 2), a n) - L) + L
        + ∑ j ∈ Finset.range N, dirichletAbelWeight j σ * ((∑ n ∈ Finset.range (j + 2), a n) - L) := by
  have habel := sum_range_mul_eq_abel_partial a (fun n : ℕ => (n : ℝ) ^ (-σ)) (N + 2)
  rw [show N + 2 - 1 = N + 1 by omega] at habel
  have hshift : (∑ i ∈ Finset.range (N + 1),
        ((((i + 1 : ℕ)) : ℝ) ^ (-σ) - ((i : ℕ) : ℝ) ^ (-σ)) * (∑ n ∈ Finset.range (i + 1), a n))
      = - ∑ i ∈ Finset.range N, dirichletAbelWeight i σ * (∑ n ∈ Finset.range (i + 2), a n) := by
    rw [Finset.sum_range_succ']
    have h0 : ((((0 + 1 : ℕ)) : ℝ) ^ (-σ) - ((0 : ℕ) : ℝ) ^ (-σ))
        * (∑ n ∈ Finset.range (0 + 1), a n) = 0 := by
      have h1 : (((0 + 1 : ℕ)) : ℝ) = 1 := by norm_num
      have h2 : ((0 : ℕ) : ℝ) = 0 := by norm_num
      have h3 : (∑ n ∈ Finset.range (0 + 1), a n) = a 0 := by simp
      rw [h1, h2, h3, Real.one_rpow, Real.zero_rpow (by linarith : (-σ) ≠ 0), ha0]
      ring
    rw [h0, add_zero, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [dirichletAbelWeight]
    have hc1 : (((k + 1 + 1 : ℕ)) : ℝ) = (((k + 2 : ℕ)) : ℝ) := rfl
    have hc2 : (∑ n ∈ Finset.range (k + 1 + 1), a n) = (∑ n ∈ Finset.range (k + 2), a n) := rfl
    rw [hc1, hc2]
    ring
  have htel : (∑ i ∈ Finset.range N, dirichletAbelWeight i σ) = 1 - (((N + 1 : ℕ)) : ℝ) ^ (-σ) :=
    sum_range_dirichletAbelWeight σ N
  have hsplit : (∑ i ∈ Finset.range N, dirichletAbelWeight i σ * (∑ n ∈ Finset.range (i + 2), a n))
      = (∑ i ∈ Finset.range N,
          dirichletAbelWeight i σ * ((∑ n ∈ Finset.range (i + 2), a n) - L))
        + L * (∑ i ∈ Finset.range N, dirichletAbelWeight i σ) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [habel, hshift, hsplit, htel]
  ring

/-- Characterisation of conditional sums over `ℕ` by convergence of range sums. -/
lemma hasSum_conditionalNat_iff (f : ℕ → ℝ) (x : ℝ) :
    HasSum f x (SummationFilter.conditional ℕ) ↔
      Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, f n) atTop (nhds x) := by
  rw [HasSum, SummationFilter.conditional_filter_eq_map_range, tendsto_map'_iff]
  rfl

/-- An abstract limit lemma: if `c j → 0` and `w · σ` is a probability family on `ℕ` whose mass
escapes to `∞` as `σ → 0⁺` (in the weak sense that every finite initial segment has mass tending
to `0`), then `∑' j, c j * w j σ → 0` as `σ → 0⁺`. -/
theorem tendsto_tsum_mul_of_tendsto_zero {c : ℕ → ℝ} (hc : Tendsto c atTop (nhds 0))
    {w : ℕ → ℝ → ℝ} (hw_nonneg : ∀ σ, 0 < σ → ∀ j, 0 ≤ w j σ)
    (hw_sum : ∀ σ, 0 < σ → HasSum (fun j => w j σ) 1)
    (hw_partial : ∀ K, Tendsto (fun σ => ∑ j ∈ Finset.range K, w j σ)
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0)) :
    Tendsto (fun σ : ℝ => ∑' j, c j * w j σ) (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  obtain ⟨K, hK⟩ : ∃ K, ∀ j ≥ K, |c j| ≤ ε / 2 := by
    obtain ⟨K, hK⟩ := (Metric.tendsto_atTop.mp hc) (ε / 2) hε2
    exact ⟨K, fun j hj => by
      have := hK j hj
      rw [dist_zero_right, Real.norm_eq_abs] at this
      linarith⟩
  obtain ⟨C, hC⟩ : ∃ C, ∀ j, |c j| ≤ C := by
    obtain ⟨K₀, hK₀⟩ := (Metric.tendsto_atTop.mp hc) 1 one_pos
    refine ⟨1 + ∑ j ∈ Finset.range K₀, |c j|, fun j => ?_⟩
    by_cases hj : j < K₀
    · refine le_trans ?_ (le_add_of_nonneg_left zero_le_one)
      exact Finset.single_le_sum (fun i _ => abs_nonneg (c i)) (Finset.mem_range.mpr hj)
    · simp only [not_lt] at hj
      have := hK₀ j hj
      rw [dist_zero_right, Real.norm_eq_abs] at this
      have : (0:ℝ) ≤ ∑ i ∈ Finset.range K₀, |c i| := Finset.sum_nonneg fun i _ => abs_nonneg (c i)
      linarith
  have hsmall : ∀ᶠ σ in nhdsWithin (0:ℝ) (Set.Ioi 0),
      (∑ j ∈ Finset.range K, |c j|) * (∑ j ∈ Finset.range K, w j σ) < ε / 2 := by
    have hlim : Tendsto (fun σ : ℝ => (∑ j ∈ Finset.range K, |c j|)
        * (∑ j ∈ Finset.range K, w j σ)) (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0) := by
      simpa using (hw_partial K).const_mul (∑ j ∈ Finset.range K, |c j|)
    have h := (Metric.tendsto_nhds.mp hlim) (ε / 2) hε2
    filter_upwards [h] with σ hσ
    rw [dist_zero_right] at hσ
    exact lt_of_le_of_lt (le_abs_self _) hσ
  filter_upwards [hsmall, self_mem_nhdsWithin] with σ hσsmall hσmem
  have hσ : 0 < σ := hσmem
  have hsumw : Summable (fun j => w j σ) := ⟨1, hw_sum σ hσ⟩
  have hsumcw : Summable (fun j => c j * w j σ) := by
    refine Summable.of_norm_bounded (g := fun j => C * w j σ) (hsumw.mul_left C) fun j => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw_nonneg σ hσ j)]
    exact mul_le_mul_of_nonneg_right (hC j) (hw_nonneg σ hσ j)
  have hwle : ∀ n, ∑ j ∈ Finset.range n, w j σ ≤ 1 := fun n => by
    have := hsumw.sum_le_tsum (Finset.range n) (fun j _ => hw_nonneg σ hσ j)
    rwa [(hw_sum σ hσ).tsum_eq] at this
  have hA : (0:ℝ) ≤ ∑ j ∈ Finset.range K, |c j| := Finset.sum_nonneg fun j _ => abs_nonneg (c j)
  have hpartial : ∀ᶠ N in (atTop : Filter ℕ),
      |∑ j ∈ Finset.range N, c j * w j σ|
        ≤ (∑ j ∈ Finset.range K, |c j|) * (∑ j ∈ Finset.range K, w j σ) + ε / 2 := by
    filter_upwards [eventually_ge_atTop K] with N hN
    have hNK : N = K + (N - K) := (Nat.add_sub_cancel' hN).symm
    have hstep : (∑ j ∈ Finset.range N, |c j| * w j σ)
        = (∑ j ∈ Finset.range K, |c j| * w j σ)
          + ∑ j ∈ Finset.range (N - K), |c (K + j)| * w (K + j) σ := by
      conv_lhs => rw [hNK]
      rw [Finset.sum_range_add]
    have h1 : (∑ j ∈ Finset.range K, |c j| * w j σ)
        ≤ (∑ j ∈ Finset.range K, |c j|) * (∑ j ∈ Finset.range K, w j σ) := by
      calc (∑ j ∈ Finset.range K, |c j| * w j σ)
          ≤ ∑ j ∈ Finset.range K, (∑ i ∈ Finset.range K, |c i|) * w j σ := by
            apply Finset.sum_le_sum
            intro j hj
            exact mul_le_mul_of_nonneg_right
              (Finset.single_le_sum (fun i _ => abs_nonneg (c i)) hj) (hw_nonneg σ hσ j)
        _ = (∑ i ∈ Finset.range K, |c i|) * (∑ j ∈ Finset.range K, w j σ) := by
            rw [Finset.mul_sum]
    have h2 : (∑ j ∈ Finset.range (N - K), |c (K + j)| * w (K + j) σ) ≤ ε / 2 := by
      have hstep2 : (∑ j ∈ Finset.range (N - K), |c (K + j)| * w (K + j) σ)
          ≤ ∑ j ∈ Finset.range (N - K), (ε / 2) * w (K + j) σ := by
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_right (hK (K + j) (by omega)) (hw_nonneg σ hσ (K + j))
      rw [← Finset.mul_sum] at hstep2
      refine le_trans hstep2 ?_
      have hsumle : ∑ j ∈ Finset.range (N - K), w (K + j) σ ≤ 1 := by
        have h := hwle (K + (N - K))
        rw [Finset.sum_range_add] at h
        exact le_trans (le_add_of_nonneg_left (Finset.sum_nonneg fun j _ => hw_nonneg σ hσ j)) h
      calc (ε / 2) * ∑ j ∈ Finset.range (N - K), w (K + j) σ
          ≤ (ε / 2) * 1 := mul_le_mul_of_nonneg_left hsumle hε2.le
        _ = ε / 2 := by ring
    calc |∑ j ∈ Finset.range N, c j * w j σ|
        ≤ ∑ j ∈ Finset.range N, |c j * w j σ| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j ∈ Finset.range N, |c j| * w j σ := by
          apply Finset.sum_congr rfl
          intro j _
          rw [abs_mul, abs_of_nonneg (hw_nonneg σ hσ j)]
      _ = (∑ j ∈ Finset.range K, |c j| * w j σ)
            + ∑ j ∈ Finset.range (N - K), |c (K + j)| * w (K + j) σ := hstep
      _ ≤ (∑ j ∈ Finset.range K, |c j|) * (∑ j ∈ Finset.range K, w j σ) + ε / 2 :=
          add_le_add h1 h2
  have habs := le_of_tendsto hsumcw.hasSum.tendsto_sum_nat.abs hpartial
  rw [dist_zero_right, Real.norm_eq_abs]
  linarith

theorem abel_tendsto_tsum_mul_rpow_conditional {a : ℕ → ℝ} (ha0 : a 0 = 0) {L : ℝ}
    (h : Filter.Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, a n) Filter.atTop
      (nhds L)) :
    Filter.Tendsto
      (fun σ : ℝ => ∑'[SummationFilter.conditional ℕ] n : ℕ, a n * (n : ℝ) ^ (-σ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds L) := by
  set c : ℕ → ℝ := fun j => (∑ n ∈ Finset.range (j + 2), a n) - L with hcdef
  have hc : Tendsto c atTop (nhds 0) := by
    have h1 : Tendsto (fun j : ℕ => ∑ n ∈ Finset.range (j + 2), a n) atTop (nhds L) :=
      h.comp (Filter.tendsto_add_atTop_nat 2)
    simpa [hcdef] using h1.sub_const L
  have hW := tendsto_tsum_mul_of_tendsto_zero hc
    (fun _ hσ j => dirichletAbelWeight_nonneg hσ j)
    (fun σ hσ => hasSum_dirichletAbelWeight hσ)
    (fun K => tendsto_sum_range_dirichletAbelWeight K)
  have hmain : ∀ σ ∈ Set.Ioi (0:ℝ),
      (∑'[SummationFilter.conditional ℕ] n : ℕ, a n * (n : ℝ) ^ (-σ))
        = L + ∑' j, c j * dirichletAbelWeight j σ := by
    intro σ hσ
    have hhas : HasSum (fun n : ℕ => a n * (n : ℝ) ^ (-σ))
        (L + ∑' j, c j * dirichletAbelWeight j σ) (SummationFilter.conditional ℕ) := by
      rw [hasSum_conditionalNat_iff]
      have hsumcw : Summable (fun j => c j * dirichletAbelWeight j σ) := by
        have hsumw : Summable (fun j => dirichletAbelWeight j σ) := ⟨1, hasSum_dirichletAbelWeight hσ⟩
        obtain ⟨C, hC⟩ : ∃ C, ∀ j, |c j| ≤ C := by
          obtain ⟨K₀, hK₀⟩ := (Metric.tendsto_atTop.mp hc) 1 one_pos
          refine ⟨1 + ∑ j ∈ Finset.range K₀, |c j|, fun j => ?_⟩
          by_cases hj : j < K₀
          · refine le_trans ?_ (le_add_of_nonneg_left zero_le_one)
            exact Finset.single_le_sum (fun i _ => abs_nonneg (c i)) (Finset.mem_range.mpr hj)
          · simp only [not_lt] at hj
            have := hK₀ j hj
            rw [dist_zero_right, Real.norm_eq_abs] at this
            have h0 : (0:ℝ) ≤ ∑ i ∈ Finset.range K₀, |c i| := Finset.sum_nonneg fun i _ => abs_nonneg (c i)
            linarith
        refine Summable.of_norm_bounded (g := fun j => C * dirichletAbelWeight j σ) (hsumw.mul_left C) fun j => ?_
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (dirichletAbelWeight_nonneg hσ j)]
        exact mul_le_mul_of_nonneg_right (hC j) (dirichletAbelWeight_nonneg hσ j)
      have h2 : Tendsto (fun N : ℕ => ∑ j ∈ Finset.range N, c j * dirichletAbelWeight j σ) atTop
          (nhds (∑' j, c j * dirichletAbelWeight j σ)) := hsumcw.hasSum.tendsto_sum_nat
      have h1 : Tendsto (fun N : ℕ => ((N + 1 : ℕ) : ℝ) ^ (-σ)
          * ((∑ n ∈ Finset.range (N + 2), a n) - L)) atTop (nhds 0) := by
        have hrpow : Tendsto (fun N : ℕ => ((N + 1 : ℕ) : ℝ) ^ (-σ)) atTop (nhds 0) :=
          tendsto_natCast_rpow_neg_atTop hσ |>.comp (Filter.tendsto_add_atTop_nat 1)
        have hS : Tendsto (fun N : ℕ => (∑ n ∈ Finset.range (N + 2), a n) - L) atTop (nhds 0) := by
          have := h.comp (Filter.tendsto_add_atTop_nat 2)
          simpa using this.sub_const L
        simpa using hrpow.mul hS
      have hlim := ((h1.add_const L).add h2)
      rw [zero_add] at hlim
      have hlim' : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range (N + 2), a n * (n : ℝ) ^ (-σ))
          atTop (nhds (L + ∑' j, c j * dirichletAbelWeight j σ)) := by
        refine hlim.congr' ?_
        filter_upwards with N
        rw [dirichlet_abel_partial_sums a ha0 hσ L N]
        congr 1
        apply Finset.sum_congr rfl
        intro j _
        simp only [hcdef]
        ring
      exact (Filter.tendsto_add_atTop_iff_nat 2).mp hlim'
    exact hhas.tsum_eq
  have hfinal : Tendsto (fun σ : ℝ => L + ∑' j, c j * dirichletAbelWeight j σ)
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds L) := by
    simpa using hW.const_add L
  refine hfinal.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  exact (hmain σ hσ).symm

end Commons.Analysis.DirichletSeries