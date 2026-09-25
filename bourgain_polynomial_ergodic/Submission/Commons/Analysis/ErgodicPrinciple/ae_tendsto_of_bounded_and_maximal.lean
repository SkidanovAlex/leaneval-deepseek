import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Order.Group.Lattice

set_option linter.unusedVariables false

namespace Commons.Analysis.ErgodicPrinciple

open MeasureTheory Filter
open scoped BigOperators ENNReal Topology

/-- The threshold sequence `1/(k+1)`. -/
private noncomputable def thr (k : ℕ) : ℝ := 1 / ((k : ℝ) + 1)

private lemma thr_pos (k : ℕ) : 0 < thr k := by
  unfold thr; positivity

/-- If a real sequence is not Cauchy, then there is a threshold `1/(k+1)` which is
exceeded by the oscillations along arbitrarily large indices. -/
private lemma not_cauchySeq_exists_threshold {u : ℕ → ℝ} (h : ¬ CauchySeq u) :
    ∃ k : ℕ, ∀ N : ℕ, ∃ n ≥ N, ∃ m ≥ N, thr k < |u n - u m| := by
  rw [Metric.cauchySeq_iff] at h
  push Not at h
  obtain ⟨ε, hεpos, hε⟩ := h
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hεpos
  refine ⟨k, fun N => ?_⟩
  obtain ⟨m, hm, n, hn, hmn⟩ := hε N
  refine ⟨n, hn, m, hm, ?_⟩
  rw [Real.dist_eq] at hmn
  rw [abs_sub_comm] at hmn
  have hk' : thr k < ε := by unfold thr; exact hk
  linarith

/-- Truncation of an `L^p` (`p > 0`) function by a bounded measurable function, with
convergence of the `L^p` (lintegral) distance to `0`. -/
lemma exists_bounded_measurable_lintegral_rpow_tendsto_zero {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {p : ℝ} (hp : 0 < p)
    {f : X → ℝ} (hf : Measurable f) (hfin : ∫⁻ x, ‖f x‖ₑ ^ p ∂μ < ⊤) :
    ∃ g : ℕ → X → ℝ, (∀ n, Measurable (g n)) ∧
      (∀ n, ∃ B : ℝ, ∀ x, ‖g n x‖ ≤ B) ∧
      Tendsto (fun n => ∫⁻ x, ‖f x - g n x‖ₑ ^ p ∂μ) atTop (𝓝 0) := by
  let g : ℕ → X → ℝ := fun n => ({x : X | |f x| ≤ (n : ℝ)}).indicator f
  refine ⟨g, ?_, ?_, ?_⟩
  · intro n
    exact hf.indicator (measurableSet_le hf.abs measurable_const)
  · intro n
    refine ⟨(n : ℝ), fun x => ?_⟩
    by_cases hx : x ∈ {x : X | |f x| ≤ (n : ℝ)}
    · simp only [g, Set.indicator_of_mem hx, Real.norm_eq_abs]
      exact hx
    · simp only [g, Set.indicator_of_notMem hx, norm_zero]
      positivity
  · have hmeas : ∀ n, Measurable (fun x => ‖f x - g n x‖ₑ ^ p) := by
      intro n
      have h1 : Measurable (fun x => f x - g n x) :=
        hf.sub (hf.indicator (measurableSet_le hf.abs measurable_const))
      exact (ENNReal.continuous_rpow_const (y := p)).measurable.comp h1.enorm
    have hbound : ∀ n, (fun x => ‖f x - g n x‖ₑ ^ p) ≤ᵐ[μ] (fun x => ‖f x‖ₑ ^ p) := by
      intro n
      apply Filter.Eventually.of_forall
      intro x
      apply ENNReal.rpow_le_rpow _ hp.le
      rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs]
      apply ENNReal.ofReal_le_ofReal
      by_cases hx : x ∈ {x : X | |f x| ≤ (n : ℝ)}
      · simp only [g, Set.indicator_of_mem hx]; simp
      · simp only [g, Set.indicator_of_notMem hx]; simp
    have hconv : ∀ᵐ x ∂μ,
        Tendsto (fun n => ‖f x - g n x‖ₑ ^ p) atTop (𝓝 ((fun _ => (0 : ℝ≥0∞)) x)) := by
      apply Filter.Eventually.of_forall
      intro x
      apply tendsto_nhds_of_eventually_eq
      filter_upwards [eventually_ge_atTop (Nat.ceil |f x|)] with n hn
      have hxS : x ∈ {x : X | |f x| ≤ (n : ℝ)} := by
        simp only [Set.mem_ofPred_eq]
        calc |f x| ≤ (Nat.ceil |f x| : ℝ) := Nat.le_ceil _
          _ ≤ (n : ℝ) := by exact_mod_cast hn
      simp only [g, Set.indicator_of_mem hxS, sub_self, enorm_zero, ENNReal.zero_rpow_of_pos hp]
    have hDCT := tendsto_lintegral_of_dominated_convergence (fun x => ‖f x‖ₑ ^ p)
      hmeas hbound hfin.ne hconv
    simpa using hDCT

theorem ae_tendsto_of_bounded_and_maximal {X : Type*} [MeasurableSpace X] {μ : Measure X}
    [IsFiniteMeasure μ]
    {p : ℝ} (hp : 1 ≤ p) {C : ℝ} (hC : 0 < C)
    {A : ℕ → (X → ℝ) → X → ℝ} {M : (X → ℝ) → X → ℝ≥0∞}
    (hA_sub : ∀ (n : ℕ) (g h : X → ℝ) (x : X), A n (g - h) x = A n g x - A n h x)
    (hbd : ∀ (g : X → ℝ) (x : X) (n : ℕ), ‖A n g x‖ₑ ≤ M g x)
    (hweak : ∀ (g : X → ℝ), Measurable g → ∀ (ε : ℝ), 0 < ε →
      μ {x | ENNReal.ofReal ε < M g x}
        ≤ ENNReal.ofReal (C / ε ^ p) * ∫⁻ x, ‖g x‖ₑ ^ p ∂μ)
    (hbounded : ∀ (g : X → ℝ), Measurable g → (∃ B : ℝ, ∀ x, ‖g x‖ ≤ B) →
      ∀ᵐ x ∂μ, ∃ L : ℝ, Tendsto (fun n : ℕ => A n g x) atTop (𝓝 L))
    (f : X → ℝ) (hf : Measurable f) (hfin : ∫⁻ x, ‖f x‖ₑ ^ p ∂μ < ⊤) :
    ∀ᵐ x ∂μ, ∃ L : ℝ, Tendsto (fun n : ℕ => A n f x) atTop (𝓝 L) := by
  classical
  -- The bad set (non convergence) is contained in the union of the oscillation sets.
  have hsub_bad : {x : X | ¬ ∃ L : ℝ, Tendsto (fun n : ℕ => A n f x) atTop (𝓝 L)}
      ⊆ ⋃ k : ℕ, {x : X | ∀ N : ℕ, ∃ n ≥ N, ∃ m ≥ N, thr k < |A n f x - A m f x|} := by
    intro x hx
    have hnc : ¬ CauchySeq (fun n : ℕ => A n f x) := by
      intro hc
      obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hc
      exact hx ⟨L, hL⟩
    obtain ⟨k, hk⟩ := not_cauchySeq_exists_threshold hnc
    exact Set.mem_iUnion.mpr ⟨k, hk⟩
  -- Key estimate: for every bounded measurable `g`, the `k`-th oscillation set is
  -- controlled by the weak `(p,p)` inequality applied to `f - g`.
  have hGnull : ∀ k : ℕ,
      μ {x : X | ∀ N : ℕ, ∃ n ≥ N, ∃ m ≥ N, thr k < |A n f x - A m f x|} = 0 := by
    intro k
    have hkey : ∀ g : X → ℝ, Measurable g → (∃ B : ℝ, ∀ x, ‖g x‖ ≤ B) →
        μ {x : X | ∀ N : ℕ, ∃ n ≥ N, ∃ m ≥ N, thr k < |A n f x - A m f x|}
          ≤ ENNReal.ofReal (C / (3 * thr k / 8) ^ p)
              * ∫⁻ x, ‖f x - g x‖ₑ ^ p ∂μ := by
      intro g hg hgbd
      set H : Set X := {x : X | ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N, |A n g x - A m g x| < thr k / 4}
        with hH
      have hHae : ∀ᵐ x ∂μ, x ∈ H := by
        filter_upwards [hbounded g hg hgbd] with x hx
        obtain ⟨L, hL⟩ := hx
        have hcauchy : CauchySeq (fun n : ℕ => A n g x) := hL.cauchySeq
        rw [Metric.cauchySeq_iff] at hcauchy
        obtain ⟨N, hN⟩ := hcauchy (thr k / 4) (by linarith [thr_pos k])
        refine ⟨N, fun n hn m hm => ?_⟩
        have := hN n hn m hm
        rwa [Real.dist_eq] at this
      have hHnull : μ {x : X | x ∉ H} = 0 := by
        have h := ae_iff.mp hHae
        simpa using h
      have hsubH : {x : X | ∀ N : ℕ, ∃ n ≥ N, ∃ m ≥ N, thr k < |A n f x - A m f x|}
          ⊆ {x : X | x ∉ H} ∪ {x : X | ENNReal.ofReal (3 * thr k / 8) < M (f - g) x} := by
        intro x hx
        by_cases hxH : x ∈ H
        · right
          obtain ⟨N0, hN0⟩ := hxH
          obtain ⟨n, hn, m, hm, hnm⟩ := hx N0
          have hAn : A n f x = A n (f - g) x + A n g x := by
            have hh := hA_sub n f g x; linarith
          have hAm : A m f x = A m (f - g) x + A m g x := by
            have hh := hA_sub m f g x; linarith
          have htri : |A n f x - A m f x|
              ≤ |A n (f - g) x| + |A m (f - g) x| + |A n g x - A m g x| := by
            have h1 : A n f x - A m f x
                = (A n (f - g) x - A m (f - g) x) + (A n g x - A m g x) := by linarith
            rw [h1]
            have h2 := abs_add_le (A n (f - g) x - A m (f - g) x) (A n g x - A m g x)
            have h3 : |A n (f - g) x - A m (f - g) x|
                ≤ |A n (f - g) x| + |A m (f - g) x| := by
              have h4 := abs_sub_le (A n (f - g) x) 0 (A m (f - g) x)
              rw [sub_zero, zero_sub, abs_neg] at h4
              exact h4
            linarith
          have hlt2 : |A n g x - A m g x| < thr k / 4 := hN0 n hn m hm
          have hsum : 3 * thr k / 4 < |A n (f - g) x| + |A m (f - g) x| := by linarith
          have hcase : 3 * thr k / 8 < |A n (f - g) x| ∨ 3 * thr k / 8 < |A m (f - g) x| := by
            by_contra hc
            push Not at hc
            linarith [hc.1, hc.2, hsum]
          rcases hcase with hc | hc
          · have hpos : 0 < |A n (f - g) x| := lt_trans (by linarith [thr_pos k]) hc
            have h1 : ENNReal.ofReal (3 * thr k / 8) < ENNReal.ofReal |A n (f - g) x| :=
              (ENNReal.ofReal_lt_ofReal_iff hpos).mpr hc
            have h2 : ENNReal.ofReal |A n (f - g) x| = ‖A n (f - g) x‖ₑ :=
              (Real.enorm_eq_ofReal_abs _).symm
            have h3 : ‖A n (f - g) x‖ₑ ≤ M (f - g) x := hbd (f - g) x n
            calc ENNReal.ofReal (3 * thr k / 8) < ENNReal.ofReal |A n (f - g) x| := h1
              _ = ‖A n (f - g) x‖ₑ := h2
              _ ≤ M (f - g) x := h3
          · have hpos : 0 < |A m (f - g) x| := lt_trans (by linarith [thr_pos k]) hc
            have h1 : ENNReal.ofReal (3 * thr k / 8) < ENNReal.ofReal |A m (f - g) x| :=
              (ENNReal.ofReal_lt_ofReal_iff hpos).mpr hc
            have h2 : ENNReal.ofReal |A m (f - g) x| = ‖A m (f - g) x‖ₑ :=
              (Real.enorm_eq_ofReal_abs _).symm
            have h3 : ‖A m (f - g) x‖ₑ ≤ M (f - g) x := hbd (f - g) x m
            calc ENNReal.ofReal (3 * thr k / 8) < ENNReal.ofReal |A m (f - g) x| := h1
              _ = ‖A m (f - g) x‖ₑ := h2
              _ ≤ M (f - g) x := h3
        · left; exact hxH
      have hwk : μ {x : X | ENNReal.ofReal (3 * thr k / 8) < M (f - g) x}
          ≤ ENNReal.ofReal (C / (3 * thr k / 8) ^ p)
              * ∫⁻ x, ‖f x - g x‖ₑ ^ p ∂μ := by
        simpa [Pi.sub_apply] using
          hweak (f - g) (hf.sub hg) (3 * thr k / 8) (by linarith [thr_pos k])
      calc μ {x : X | ∀ N : ℕ, ∃ n ≥ N, ∃ m ≥ N, thr k < |A n f x - A m f x|}
          ≤ μ ({x : X | x ∉ H} ∪ {x : X | ENNReal.ofReal (3 * thr k / 8) < M (f - g) x}) :=
            measure_mono hsubH
        _ ≤ μ {x : X | x ∉ H} + μ {x : X | ENNReal.ofReal (3 * thr k / 8) < M (f - g) x} :=
            measure_union_le _ _
        _ = μ {x : X | ENNReal.ofReal (3 * thr k / 8) < M (f - g) x} := by
            rw [hHnull, zero_add]
        _ ≤ ENNReal.ofReal (C / (3 * thr k / 8) ^ p)
              * ∫⁻ x, ‖f x - g x‖ₑ ^ p ∂μ := hwk
    -- Approximate `f` by bounded measurable functions.
    obtain ⟨g, hgmeas, hgbd, hgtend⟩ :=
      exists_bounded_measurable_lintegral_rpow_tendsto_zero (μ := μ)
        (lt_of_lt_of_le zero_lt_one hp) hf hfin
    have hineq : ∀ n, μ {x : X | ∀ N : ℕ, ∃ n ≥ N, ∃ m ≥ N, thr k < |A n f x - A m f x|}
        ≤ ENNReal.ofReal (C / (3 * thr k / 8) ^ p)
            * ∫⁻ x, ‖f x - g n x‖ₑ ^ p ∂μ :=
      fun n => hkey (g n) (hgmeas n) (hgbd n)
    have hlim : Tendsto (fun n => ENNReal.ofReal (C / (3 * thr k / 8) ^ p)
        * ∫⁻ x, ‖f x - g n x‖ₑ ^ p ∂μ) atTop (𝓝 0) := by
      have h0 := ENNReal.Tendsto.const_mul
        (a := ENNReal.ofReal (C / (3 * thr k / 8) ^ p)) hgtend
        (Or.inr (ENNReal.ofReal_lt_top.ne))
      simpa using h0
    exact le_antisymm (ge_of_tendsto hlim (Filter.Eventually.of_forall hineq)) zero_le
  have hunion : μ (⋃ k : ℕ,
      {x : X | ∀ N : ℕ, ∃ n ≥ N, ∃ m ≥ N, thr k < |A n f x - A m f x|}) = 0 := by
    refine le_antisymm ?_ zero_le
    calc μ (⋃ k : ℕ, {x : X | ∀ N : ℕ, ∃ n ≥ N, ∃ m ≥ N, thr k < |A n f x - A m f x|})
        ≤ ∑' k : ℕ, μ {x : X | ∀ N : ℕ, ∃ n ≥ N, ∃ m ≥ N,
            thr k < |A n f x - A m f x|} := measure_iUnion_le _
      _ = ∑' k : ℕ, (0 : ℝ≥0∞) := tsum_congr hGnull
      _ = 0 := tsum_zero
  rw [ae_iff]
  exact le_antisymm (le_trans (measure_mono hsub_bad) (le_of_eq hunion)) zero_le

end Commons.Analysis.ErgodicPrinciple