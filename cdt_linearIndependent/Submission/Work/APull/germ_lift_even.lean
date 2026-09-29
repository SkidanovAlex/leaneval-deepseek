import Mathlib
import Submission.Work.CPull.c_pullbacks
import Submission.Work.CPull.germs

namespace Work.APull

open PowerSeries Metric Filter
open scoped Topology BigOperators

/-- From the two relations of a lift `Φ` of `g = φ ∘ (·^2)` through the symmetrising
involution (`Φ z + Φ (-z) = g z = Φ z * Φ (-z)`, as in `hΦrel`): `Φ (-z) = Φ z / (Φ z - 1)`.
(Generalisation of `Work.CPull.lift_neg_eq`, whose statement is specialised to `phiC`.) -/
lemma lift_neg_eq_gen (Φ g : ℂ → ℂ)
    (h : ∀ z ∈ Metric.ball (0 : ℂ) 1, Φ z + Φ (-z) = g z ∧ Φ z * Φ (-z) = g z)
    (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) 1) : Φ (-z) = Φ z / (Φ z - 1) := by
  have h1 := (h z hz).1
  have h2 := (h z hz).2
  have hne : Φ z - 1 ≠ 0 := by
    intro hc
    have hz1 : Φ z = 1 := sub_eq_zero.mp hc
    rw [hz1, one_mul] at h2
    rw [hz1] at h1
    have : (1 : ℂ) = 0 := by linear_combination h1 - h2
    exact one_ne_zero this
  have hsum : Φ z + Φ (-z) = Φ z * Φ (-z) := by rw [h1, h2]
  have key : Φ z - Φ (-z) * (Φ z - 1) = 0 := by
    have : Φ z - Φ (-z) * (Φ z - 1) = Φ z + Φ (-z) - Φ z * Φ (-z) := by ring
    rw [this, hsum]; ring
  rw [eq_div_iff hne]
  exact (sub_eq_zero.mp key).symm

/-- A germ for `f` along a lift `Φ` of `φ` (through the square map) descends to a germ for the
symmetrisation `Sym⁺f` along `φ`.  The even part `z ↦ F z + F (-z)` of the germ function is a
function of `φ (z ^ 2)`, and `germ_of_even` removes the square. -/
theorem germ_lift_even (f : PowerSeries ℚ) (φ Φ F : ℂ → ℂ)
    (hφ0 : φ 0 = 0) (hΦ0 : Φ 0 = 0)
    (hΦdiff : DifferentiableOn ℂ Φ (Metric.ball 0 1))
    (hΦrel : ∀ z ∈ Metric.ball (0 : ℂ) 1,
      Φ z + Φ (-z) = φ (z ^ 2) ∧ Φ z * Φ (-z) = φ (z ^ 2))
    (hΦzero : ∀ z ∈ Metric.ball (0 : ℂ) 1, Φ z = 0 → z = 0)
    (hFdiff : DifferentiableOn ℂ F (Metric.ball 0 1))
    (hFsum : Filter.Eventually (fun z : ℂ => HasSum (fun k : ℕ =>
      ((PowerSeries.coeff k f : ℚ) : ℂ) * Φ z ^ k) (F z)) (nhds 0)) :
    ∃ N : ℂ → ℂ, DifferentiableOn ℂ N (Metric.ball 0 1) ∧
      Filter.Eventually (fun w : ℂ => HasSum (fun k : ℕ =>
        ((PowerSeries.coeff k (Submission.CDT.sympSym f) : ℚ) : ℂ) * φ w ^ k) (N w)) (nhds 0) := by
  classical
  have hneg : Set.MapsTo (fun z : ℂ => -z) (Metric.ball 0 1) (Metric.ball 0 1) := by
    intro z hz
    rw [Metric.mem_ball, dist_zero_right] at hz ⊢
    simpa using hz
  -- the germ of the even part along `φ (z ^ 2)`
  have hgerm : ∀ᶠ z in 𝓝 (0 : ℂ), HasSum (fun k : ℕ =>
      ((PowerSeries.coeff k (Submission.CDT.sympSym f) : ℚ) : ℂ) * φ (z ^ 2) ^ k)
        (F z + F (-z)) := by
    obtain ⟨V, hVmem, hV⟩ := Filter.eventually_iff_exists_mem.mp hFsum
    obtain ⟨δ, hδpos, hδsub⟩ := Metric.mem_nhds_iff.mp hVmem
    set δ₁ : ℝ := min δ 1 with hδ₁def
    have hδ₁pos : 0 < δ₁ := lt_min hδpos one_pos
    have hδ₁le : δ₁ ≤ δ := min_le_left _ _
    have hδ₁sub : Metric.ball (0 : ℂ) δ₁ ⊆ V := fun z hz =>
      hδsub (Metric.ball_subset_ball hδ₁le hz)
    have hz₁n : ‖((δ₁ / 2 : ℝ) : ℂ)‖ = δ₁ / 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hz₁mem : ((δ₁ / 2 : ℝ) : ℂ) ∈ V := by
      apply hδ₁sub
      rw [Metric.mem_ball, dist_zero_right, hz₁n]
      linarith
    have hz₁ball : ((δ₁ / 2 : ℝ) : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
      rw [Metric.mem_ball, dist_zero_right, hz₁n]
      have h : δ₁ / 2 < 1 := by
        have h2 : δ₁ ≤ 1 := min_le_right _ _
        linarith
      exact h
    have hz₁ne : ((δ₁ / 2 : ℝ) : ℂ) ≠ 0 := by
      simp only [ne_eq, Complex.ofReal_eq_zero]
      positivity
    set ρ : ℝ := ‖Φ ((δ₁ / 2 : ℝ) : ℂ)‖ with hρdef
    have hρpos : 0 < ρ := by
      rw [hρdef, norm_pos_iff]
      exact fun h => hz₁ne (hΦzero _ hz₁ball h)
    have hPsumρ : Summable fun k : ℕ =>
        ‖((PowerSeries.coeff k f : ℚ) : ℂ)‖ * ρ ^ k := by
      have h := (hV _ hz₁mem).summable.norm
      simpa [ρ, norm_mul, norm_pow] using h
    obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp
      (hPsumρ.tendsto_atTop_zero.eventually (eventually_lt_nhds (show (0:ℝ) < 1 by norm_num)))
    set C : ℝ := max 1 ((Finset.range (K + 1)).sup' ⟨0, by simp⟩
      (fun k => ‖((PowerSeries.coeff k f : ℚ) : ℂ)‖ * ρ ^ k)) with hCdef
    have hCpos : 0 < C := lt_of_lt_of_le one_pos (le_max_left _ _)
    have hPbound : ∀ k : ℕ, ‖((PowerSeries.coeff k f : ℚ) : ℂ)‖ ≤ C * (ρ⁻¹) ^ k := by
      intro k
      have h1 : ‖((PowerSeries.coeff k f : ℚ) : ℂ)‖ * ρ ^ k ≤ C := by
        rcases lt_or_ge k K with hk | hk
        · refine le_trans (Finset.le_sup' (s := Finset.range (K + 1))
            (f := fun k => ‖((PowerSeries.coeff k f : ℚ) : ℂ)‖ * ρ ^ k)
            (Finset.mem_range.mpr (by omega))) (le_max_right _ _)
        · exact le_trans (le_of_lt (hK k hk)) (le_max_left _ _)
      have h2 : ρ ^ k * ρ⁻¹ ^ k = 1 := by
        rw [← mul_pow, mul_inv_cancel₀ (ne_of_gt hρpos), one_pow]
      calc ‖((PowerSeries.coeff k f : ℚ) : ℂ)‖
          = ‖((PowerSeries.coeff k f : ℚ) : ℂ)‖ * (ρ ^ k * ρ⁻¹ ^ k) := by rw [h2, mul_one]
        _ = (‖((PowerSeries.coeff k f : ℚ) : ℂ)‖ * ρ ^ k) * ρ⁻¹ ^ k := by ring
        _ ≤ C * ρ⁻¹ ^ k := mul_le_mul_of_nonneg_right h1 (by positivity)
    obtain ⟨C', R', hC'pos, hR'pos, hGC⟩ :=
      Work.CPull.sympSym_radius f C ρ⁻¹ hCpos (by positivity) hPbound
    -- the small neighbourhood
    set ε : ℝ := min (1/4) (min (ρ/4) (1/(4*(R'+1)))) with hεdef
    have hεpos : 0 < ε := lt_min (by norm_num) (lt_min (by positivity) (by positivity))
    have hεle4 : ε ≤ 1/4 := min_le_left _ _
    have hεleρ : ε ≤ ρ/4 := le_trans (min_le_right _ _) (min_le_left _ _)
    have hεleR : ε ≤ 1/(4*(R'+1)) := le_trans (min_le_right _ _) (min_le_right _ _)
    have hΦcont : ContinuousAt Φ 0 :=
      hΦdiff.continuousOn.continuousAt (Metric.ball_mem_nhds 0 one_pos)
    obtain ⟨r1, hr1pos, hr1⟩ := Metric.continuousAt_iff.mp hΦcont ε hεpos
    have hrpos : 0 < min (min δ₁ r1) 1 :=
      lt_min (lt_min hδ₁pos hr1pos) one_pos
    refine Filter.Eventually.mono (Metric.ball_mem_nhds (0 : ℂ) hrpos) ?_
    intro z hz
    have hzr : ‖z‖ < min (min δ₁ r1) 1 := by simpa [dist_eq_norm] using hz
    have hzδ : ‖z‖ < δ₁ := lt_of_lt_of_le hzr (le_trans (min_le_left _ _) (min_le_left _ _))
    have hzr1 : ‖z‖ < r1 := lt_of_lt_of_le hzr (le_trans (min_le_left _ _) (min_le_right _ _))
    have hz1 : ‖z‖ < 1 := lt_of_lt_of_le hzr (min_le_right _ _)
    have hzV : z ∈ V := hδ₁sub (by rwa [Metric.mem_ball, dist_zero_right])
    have hnzV : -z ∈ V := by
      apply hδ₁sub
      rw [Metric.mem_ball, dist_zero_right, norm_neg]
      exact hzδ
    have hzball : z ∈ Metric.ball (0 : ℂ) 1 := by
      rw [Metric.mem_ball, dist_zero_right]; exact hz1
    have hΦzlt : ‖Φ z‖ < ε := by
      have h : dist (Φ z) (Φ 0) < ε := hr1 (by simpa [dist_eq_norm] using hzr1)
      rw [hΦ0, dist_zero_right] at h
      exact h
    have hΦnzlt : ‖Φ (-z)‖ < ε := by
      have h : dist (Φ (-z)) (Φ 0) < ε := hr1 (by rw [dist_eq_norm, sub_zero, norm_neg]; exact hzr1)
      rw [hΦ0, dist_zero_right] at h
      exact h
    rw [(hΦrel z hzball).2.symm]
    have hΦz1 : ‖Φ z‖ < 1 := by linarith [hεle4, hεpos]
    -- bounds on the two `σ`'s
    have hσPhi : (∑' j : ℕ, ‖((PowerSeries.coeff j Submission.CDT.sympPhi : ℚ) : ℂ)‖ * ‖Φ z‖ ^ j) ≤ ρ := by
      refine le_trans (Work.CPull.tsum_sympPhi_abs (Φ z) hΦz1) ?_
      have h3 : (1 : ℝ) - ‖Φ z‖ ≥ 3/4 := by linarith [hεle4, hεpos]
      have h4 : (1 - ‖Φ z‖)⁻¹ ≤ 4/3 := by
        rw [inv_le_comm₀ (by linarith [norm_nonneg (Φ z), hΦz1]) (by norm_num)]
        linarith
      calc ‖Φ z‖ * (1 - ‖Φ z‖)⁻¹ ≤ (ρ/4) * (4/3) :=
            mul_le_mul (le_trans hΦzlt.le hεleρ) h4 (by positivity) (by positivity)
        _ ≤ ρ := by nlinarith [hρpos]
    have hσY : R' * (∑' j : ℕ, ‖((PowerSeries.coeff j Submission.CDT.sympY : ℚ) : ℂ)‖ * ‖Φ z‖ ^ j) ≤ 1/2 := by
      have h3 : (1 - ‖Φ z‖)⁻¹ ≤ 4/3 := by
        rw [inv_le_comm₀ (by linarith [norm_nonneg (Φ z), hΦz1]) (by norm_num)]
        linarith [hεle4, hεpos]
      have h4 : ‖Φ z‖ ^ 2 * (1 - ‖Φ z‖)⁻¹ ≤ ε ^ 2 * (4/3) := by
        refine mul_le_mul ?_ h3 (by positivity) (by positivity)
        rw [pow_two, pow_two]
        exact mul_self_le_mul_self (norm_nonneg _) hΦzlt.le
      have h5 : R' * (ε ^ 2 * (4/3)) ≤ 1/2 := by
        have hR1 : R'/(R'+1) ≤ 1 := by
          rw [div_le_one (by positivity)]; linarith
        have h6 : ε ^ 2 ≤ ε * (1/(4*(R'+1))) := by
          rw [pow_two]
          exact mul_le_mul_of_nonneg_left hεleR hεpos.le
        have h7 : R' * (ε ^ 2 * (4/3)) ≤ R' * ((ε * (1/(4*(R'+1)))) * (4/3)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h6 (by norm_num)) hR'pos.le
        have h8 : R' * ((ε * (1/(4*(R'+1)))) * (4/3)) = ε * (R'/(R'+1)) * (1/3) := by
          field_simp <;> ring
        have h9 : ε * (R'/(R'+1)) * (1/3) ≤ (1/4) * 1 * (1/3) := by
          refine mul_le_mul_of_nonneg_right ?_ (by norm_num)
          exact mul_le_mul hεle4 hR1 (by positivity) (by norm_num)
        rw [h8] at h7
        linarith [h7, h9]
      calc R' * (∑' j : ℕ, ‖((PowerSeries.coeff j Submission.CDT.sympY : ℚ) : ℂ)‖ * ‖Φ z‖ ^ j)
          ≤ R' * (‖Φ z‖ ^ 2 * (1 - ‖Φ z‖)⁻¹) :=
            mul_le_mul_of_nonneg_left (Work.CPull.tsum_sympY_abs (Φ z) hΦz1) hR'pos.le
        _ ≤ R' * (ε ^ 2 * (4/3)) := mul_le_mul_of_nonneg_left h4 hR'pos.le
        _ ≤ 1/2 := h5
    -- the summability hypotheses of `evp_subst`
    have hYsum : Summable fun j : ℕ => ‖((PowerSeries.coeff j Submission.CDT.sympY : ℚ) : ℂ)‖ * ‖Φ z‖ ^ j :=
      Summable.of_nonneg_of_le (fun j => by positivity)
        (fun j => mul_le_of_le_one_left (by positivity) (Work.CPull.norm_coeff_sympY_le j))
        (summable_geometric_iff_norm_lt_one.mpr
          (by rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]; exact hΦz1))
    have hPhisum : Summable fun j : ℕ => ‖((PowerSeries.coeff j Submission.CDT.sympPhi : ℚ) : ℂ)‖ * ‖Φ z‖ ^ j :=
      Summable.of_nonneg_of_le (fun j => by positivity)
        (fun j => mul_le_of_le_one_left (by positivity) (Work.CPull.norm_coeff_sympPhi_le j))
        (summable_geometric_iff_norm_lt_one.mpr
          (by rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]; exact hΦz1))
    have hGCsum : Summable fun k : ℕ => ‖((PowerSeries.coeff k (Submission.CDT.sympSym f) : ℚ) : ℂ)‖ *
        (∑' j : ℕ, ‖((PowerSeries.coeff j Submission.CDT.sympY : ℚ) : ℂ)‖ * ‖Φ z‖ ^ j) ^ k := by
      have hb : ∀ k : ℕ, ‖((PowerSeries.coeff k (Submission.CDT.sympSym f) : ℚ) : ℂ)‖ *
          (∑' j : ℕ, ‖((PowerSeries.coeff j Submission.CDT.sympY : ℚ) : ℂ)‖ * ‖Φ z‖ ^ j) ^ k
          ≤ C' * (1/2) ^ k := by
        intro k
        have hRσ : R' ^ k * (∑' j : ℕ, ‖((PowerSeries.coeff j Submission.CDT.sympY : ℚ) : ℂ)‖ * ‖Φ z‖ ^ j) ^ k
            ≤ (1/2) ^ k := by
          have h1 : (R' * (∑' j : ℕ, ‖((PowerSeries.coeff j Submission.CDT.sympY : ℚ) : ℂ)‖ * ‖Φ z‖ ^ j)) ^ k
              ≤ (1/2) ^ k := by
            exact pow_le_pow_left₀ (by positivity) hσY k
          rwa [mul_pow] at h1
        calc ‖((PowerSeries.coeff k (Submission.CDT.sympSym f) : ℚ) : ℂ)‖ *
              (∑' j : ℕ, ‖((PowerSeries.coeff j Submission.CDT.sympY : ℚ) : ℂ)‖ * ‖Φ z‖ ^ j) ^ k
            ≤ (C' * R' ^ k) *
              (∑' j : ℕ, ‖((PowerSeries.coeff j Submission.CDT.sympY : ℚ) : ℂ)‖ * ‖Φ z‖ ^ j) ^ k :=
              mul_le_mul_of_nonneg_right (hGC k) (by positivity)
          _ = C' * (R' ^ k *
              (∑' j : ℕ, ‖((PowerSeries.coeff j Submission.CDT.sympY : ℚ) : ℂ)‖ * ‖Φ z‖ ^ j) ^ k) := by ring
          _ ≤ C' * (1/2) ^ k := mul_le_mul_of_nonneg_left hRσ hC'pos.le
      refine Summable.of_nonneg_of_le (fun k => by positivity) hb ?_
      exact (summable_geometric_iff_norm_lt_one.mpr (by norm_num : |(1/2 : ℝ)| < 1)).mul_left C'
    -- the chain of evaluations
    have hysym : Work.CPull.evp Submission.CDT.sympY (Φ z) = Φ z * Φ (-z) := by
      rw [(Work.CPull.evp_sympPhi (Φ z) hΦz1).2,
        lift_neg_eq_gen Φ (fun w => φ (w ^ 2)) hΦrel z hzball, div_eq_mul_inv, div_eq_mul_inv]
      ring
    have h1 := (Work.CPull.evp_subst (Submission.CDT.sympSym f) Submission.CDT.sympY (Φ z)
      (by rw [Submission.CDT.sympY, map_mul, PowerSeries.constantCoeff_X, zero_mul])
      hYsum hGCsum).2
    rw [hysym] at h1
    have h2 := Submission.CDT.sympSym_subst f
    have h3 := Work.CPull.evp_subst f Submission.CDT.sympPhi (Φ z)
      (by rw [Submission.CDT.sympPhi, map_mul, PowerSeries.constantCoeff_X, zero_mul])
      hPhisum (by
        refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hPsumρ
        have : (∑' j : ℕ, ‖((PowerSeries.coeff j Submission.CDT.sympPhi : ℚ) : ℂ)‖ * ‖Φ z‖ ^ j) ^ n
            ≤ ρ ^ n := pow_le_pow_left₀ (by positivity) hσPhi n
        exact mul_le_mul_of_nonneg_left this (by positivity))
    have h4 := (Work.CPull.evp_add_mul f (f.subst Submission.CDT.sympPhi) (Φ z)
      (hV z hzV).summable (h3.1)).1
    have h5 : Work.CPull.evp ((Submission.CDT.sympSym f).subst Submission.CDT.sympY) (Φ z)
        = Work.CPull.evp f (Φ z) + Work.CPull.evp f (Φ (-z)) := by
      rw [h2, h4, h3.2, (Work.CPull.evp_sympPhi (Φ z) hΦz1).1,
        lift_neg_eq_gen Φ (fun w => φ (w ^ 2)) hΦrel z hzball]
    have h6 : Work.CPull.evp f (Φ z) = F z := (hV z hzV).tsum_eq
    have h7 : Work.CPull.evp f (Φ (-z)) = F (-z) := (hV (-z) hnzV).tsum_eq
    have hval : Work.CPull.evp (Submission.CDT.sympSym f) (Φ z * Φ (-z)) = F z + F (-z) := by
      rw [← h1, h5, h6, h7]
    -- summability of the `Sym⁺f` series at this point
    have hy : R' * ‖Φ z * Φ (-z)‖ < 1 := by
      have hle : ‖Φ z * Φ (-z)‖ ≤ ε * ε := by
        rw [norm_mul]
        exact mul_le_mul hΦzlt.le hΦnzlt.le (norm_nonneg _) hεpos.le
      have h6 : R' * (ε * ε) ≤ 1/2 := by
        have hε4 : ε ≤ 1/(4*(R'+1)) := hεleR
        have h7 : ε * ε ≤ ε * (1/(4*(R'+1))) := mul_le_mul_of_nonneg_left hε4 hεpos.le
        have h8 : R' * (ε * ε) ≤ R' * (ε * (1/(4*(R'+1)))) := mul_le_mul_of_nonneg_left h7 hR'pos.le
        have h9 : R' * (ε * (1/(4*(R'+1)))) ≤ 1/4 := by
          have h10 : ε * (1/(4*(R'+1))) ≤ (1/4) * (1/(4*(R'+1))) :=
            mul_le_mul_of_nonneg_right hεle4 (by positivity)
          have h11 : R' * ((1/4) * (1/(4*(R'+1)))) ≤ 1/4 := by
            rw [show R' * ((1/4) * (1/(4*(R'+1)))) = R' / (16*(R'+1)) by field_simp <;> ring]
            rw [div_le_iff₀ (by positivity)]
            nlinarith [hR'pos]
          linarith [h10, h11, mul_le_mul_of_nonneg_left h10 hR'pos.le, hR'pos]
        linarith [h8, h9]
      nlinarith [hle, hR'pos, h6, hεpos]
    have hyC : Summable fun k : ℕ => ((PowerSeries.coeff k (Submission.CDT.sympSym f) : ℚ) : ℂ) *
        (Φ z * Φ (-z)) ^ k := by
      refine Summable.of_norm_bounded (g := fun k : ℕ => C' * (R' * ‖Φ z * Φ (-z)‖) ^ k) ?_ ?_
      · exact (summable_geometric_iff_norm_lt_one.mpr
          (by rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; exact hy)).mul_left C'
      · intro k
        have h1 : ‖((PowerSeries.coeff k (Submission.CDT.sympSym f) : ℚ) : ℂ) *
            (Φ z * Φ (-z)) ^ k‖
            = ‖((PowerSeries.coeff k (Submission.CDT.sympSym f) : ℚ) : ℂ)‖ * ‖Φ z * Φ (-z)‖ ^ k := by
          rw [norm_mul, norm_pow]
        rw [h1]
        calc ‖((PowerSeries.coeff k (Submission.CDT.sympSym f) : ℚ) : ℂ)‖ * ‖Φ z * Φ (-z)‖ ^ k
            ≤ (C' * R' ^ k) * ‖Φ z * Φ (-z)‖ ^ k :=
              mul_le_mul_of_nonneg_right (hGC k) (by positivity)
          _ = C' * (R' * ‖Φ z * Φ (-z)‖) ^ k := by rw [mul_pow]; ring
    have hfinal : HasSum (fun k : ℕ =>
        ((PowerSeries.coeff k (Submission.CDT.sympSym f) : ℚ) : ℂ) * (Φ z * Φ (-z)) ^ k) (F z + F (-z)) := by
      have := hyC.hasSum
      rwa [show (∑' k : ℕ, ((PowerSeries.coeff k (Submission.CDT.sympSym f) : ℚ) : ℂ) *
          (Φ z * Φ (-z)) ^ k) = F z + F (-z) from hval] at this
    exact hfinal
  exact Work.CPull.germ_of_even (f := Submission.CDT.sympSym f) (Ψ := φ)
    (E := fun z => F z + F (-z))
    (hFdiff.add (hFdiff.comp differentiable_neg.differentiableOn hneg))
    (fun z hz => by simp only [neg_neg]; ring) hgerm

end Work.APull
