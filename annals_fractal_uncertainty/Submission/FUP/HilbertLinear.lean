import Submission.FUP.HilbertPointwise
import Submission.FUP.Truncation

open MeasureTheory Metric Filter Set
open scoped Real BigOperators Topology ContDiff

set_option autoImplicit false
set_option maxHeartbeats 3200000
variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

namespace Submission.FUP

/-!
# Linearity of the Hilbert transform of the derivative along a line

In §4 condition (i) of Proposition `prop:Ew_is_psh` is verified for the compactly supported
truncations `T_n = ∑_{k<n} ω̃_k` by summing the estimate `sum_abs_hilbertLine_le_any` over the
pieces.  This requires the Hilbert transform of the derivative to be additive in the function:

  `hilbertLine (∑_{k<n} f_k) x y = ∑_{k<n} hilbertLine (f_k) x y`.

The proof is the obvious one — `fderiv` is additive, and finite sums integrate termwise — but it
requires the integrability of the integrand, which we establish here for compactly supported `C²`
functions with a global bound on the second derivative.
-/

/-- `fderiv ℝ f` vanishes outside the topological support of `f`. -/
lemma fderiv_eq_zero_of_notMem_tsupport {f : ℝᵈ → ℝ} {z : ℝᵈ} (hz : z ∉ tsupport f) :
    fderiv ℝ f z = 0 := by
  have h0 : f =ᶠ[𝓝 z] 0 := by
    filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds hz] with y hy
    by_contra hy'
    exact hy (subset_tsupport f hy')
  exact ((hasFDerivAt_const (x := z) (c := (0 : ℝ))).congr_of_eventuallyEq h0).fderiv

/-- A compactly supported function has `fderiv` vanishing far away. -/
lemma exists_fderiv_eq_zero_of_hasCompactSupport {f : ℝᵈ → ℝ} (hcs : HasCompactSupport f) :
    ∃ R : ℝ, ∀ z : ℝᵈ, R < ‖z‖ → fderiv ℝ f z = 0 := by
  obtain ⟨R, hR⟩ := (hcs.isCompact.isBounded.subset_closedBall (0 : ℝᵈ))
  refine ⟨R, fun z hz => fderiv_eq_zero_of_notMem_tsupport fun hzmem => ?_⟩
  have h1 : ‖z‖ ≤ R := by
    have := hR hzmem
    simpa [Metric.mem_closedBall, dist_eq_norm] using this
  linarith

/-- **Integrability of the Hilbert-transform integrand.**  For a compactly supported `C²` function
with `‖D²f‖ ≤ L`, the function `t ↦ (∂_y f(x + tŷ) - ∂_y f(x - tŷ))/t` is integrable on `(0,∞)`:
it vanishes for `t > ‖x‖ + R` and is bounded by `2L` on the window. -/
theorem integrableOn_hilbertIntegrand {f : ℝᵈ → ℝ} (hf : ContDiff ℝ 2 f)
    (hcs : HasCompactSupport f) {L : ℝ} (hL : 0 ≤ L)
    (hD2 : ∀ z : ℝᵈ, ‖iteratedFDeriv ℝ 2 f z‖ ≤ L) (x y : ℝᵈ) (hy : ‖y‖ = 1) :
    IntegrableOn (fun t : ℝ => (dirDeriv f (x + t • y) y - dirDeriv f (x - t • y) y) / t)
      (Set.Ioi 0) := by
  obtain ⟨R₀, hR₀⟩ := exists_fderiv_eq_zero_of_hasCompactSupport hcs
  set R : ℝ := max R₀ 0 with hRdef
  have hR : ∀ z : ℝᵈ, R < ‖z‖ → fderiv ℝ f z = 0 := fun z hz =>
    hR₀ z (lt_of_le_of_lt (le_max_left _ _) hz)
  have hRnn : 0 ≤ R := le_max_right _ _
  -- the Lipschitz bound for `fderiv`
  have hlip : ∀ z₁ z₂ : ℝᵈ, ‖fderiv ℝ f z₂ - fderiv ℝ f z₁‖ ≤ L * ‖z₂ - z₁‖ :=
    fun z₁ z₂ => Commons.Analysis.Calculus.norm_fderiv_sub_le hL hf hD2 z₁ z₂
  have hnorm : ∀ s : ℝ, ‖s • y‖ = |s| := fun s => by
    rw [norm_smul, Real.norm_eq_abs, hy, mul_one]
  -- the integrand vanishes for `t > ‖x‖ + R`
  have hvanish : ∀ t : ℝ, ‖x‖ + R < t →
      (dirDeriv f (x + t • y) y - dirDeriv f (x - t • y) y) / t = 0 := by
    intro t ht
    have hpos : 0 < t := by have := norm_nonneg x; linarith
    have hA : dirDeriv f (x + t • y) y = 0 := by
      have h : R < ‖x + t • y‖ := by
        have h2 : ‖(x + t • y) - x‖ ≤ ‖x + t • y‖ + ‖x‖ := norm_sub_le _ _
        rw [add_sub_cancel_left, hnorm, abs_of_pos hpos] at h2
        linarith
      rw [dirDeriv_apply, hR _ h]; simp
    have hB : dirDeriv f (x - t • y) y = 0 := by
      have h : R < ‖x - t • y‖ := by
        have h2 : ‖(x - t • y) - x‖ ≤ ‖x - t • y‖ + ‖x‖ := norm_sub_le _ _
        have h3 : ‖(x - t • y) - x‖ = t := by
          have h4 : (x - t • y) - x = -(t • y) := by abel
          rw [h4, norm_neg, hnorm, abs_of_pos hpos]
        rw [h3] at h2
        linarith
      rw [dirDeriv_apply, hR _ h]; simp
    rw [hA, hB, sub_zero, zero_div]
  -- the integrand is bounded by `2L` on `(0, ‖x‖ + R]`
  have hbound : ∀ t : ℝ, 0 < t →
      ‖(dirDeriv f (x + t • y) y - dirDeriv f (x - t • y) y) / t‖ ≤ 2 * L := by
    intro t ht
    have h1 : dirDeriv f (x + t • y) y - dirDeriv f (x - t • y) y
        = (fderiv ℝ f (x + t • y) - fderiv ℝ f (x - t • y)) y := by
      rw [dirDeriv_apply, dirDeriv_apply, sub_apply]
    have h2 : ‖(fderiv ℝ f (x + t • y) - fderiv ℝ f (x - t • y)) y‖
        ≤ ‖fderiv ℝ f (x + t • y) - fderiv ℝ f (x - t • y)‖ * ‖y‖ :=
      ContinuousLinearMap.le_opNorm _ _
    rw [hy, mul_one] at h2
    have hsub : x + t • y - (x - t • y) = (2 * t) • y := by module
    have h3 : ‖fderiv ℝ f (x + t • y) - fderiv ℝ f (x - t • y)‖ ≤ L * (2 * t) := by
      have h := hlip (x - t • y) (x + t • y)
      rw [hsub, norm_smul, Real.norm_eq_abs, hy, mul_one, abs_of_pos (by linarith)] at h
      linarith
    have htabs : ‖t‖ = t := by rw [Real.norm_eq_abs, abs_of_pos ht]
    rw [h1, norm_div, Real.norm_eq_abs, htabs]
    calc ‖(fderiv ℝ f (x + t • y) - fderiv ℝ f (x - t • y)) y‖ / t
        ≤ (L * (2 * t)) / t := div_le_div_of_nonneg_right (le_trans h2 h3) ht.le
      _ = 2 * L := by
        rw [div_eq_iff (ne_of_gt ht)]
        ring
  -- measurability
  have hfd : Continuous (fun z : ℝᵈ => fderiv ℝ f z) := hf.continuous_fderiv (by norm_num)
  have hnum : Continuous (fun t : ℝ =>
      dirDeriv f (x + t • y) y - dirDeriv f (x - t • y) y) := by
    have hbase : Continuous (fun t : ℝ => fderiv ℝ f (x + t • y)) :=
      hfd.comp (continuous_const.add (continuous_id.smul continuous_const))
    have hbase' : Continuous (fun t : ℝ => fderiv ℝ f (x - t • y)) :=
      hfd.comp (continuous_const.sub (continuous_id.smul continuous_const))
    have h1 : Continuous (fun t : ℝ => (fderiv ℝ f (x + t • y)) y) :=
      (ContinuousLinearMap.apply ℝ ℝ y).continuous.comp hbase
    have h2 : Continuous (fun t : ℝ => (fderiv ℝ f (x - t • y)) y) :=
      (ContinuousLinearMap.apply ℝ ℝ y).continuous.comp hbase'
    exact ((h1.sub h2).congr fun t => by simp only [dirDeriv_apply, Pi.sub_apply])
  have hcont : ContinuousOn (fun t : ℝ =>
      (dirDeriv f (x + t • y) y - dirDeriv f (x - t • y) y) / t) (Set.Ioi 0) :=
    hnum.continuousOn.div continuousOn_id (fun t ht => ne_of_gt ht)
  -- integrability of the integrand on the finite-measure window
  have hmeas : AEStronglyMeasurable (fun t : ℝ =>
      (dirDeriv f (x + t • y) y - dirDeriv f (x - t • y) y) / t)
      (volume.restrict (Set.Ioc (0:ℝ) (‖x‖ + R))) :=
    (hcont.mono Set.Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc
  have hfin : volume (Set.Ioc (0:ℝ) (‖x‖ + R)) < ⊤ := by
    rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
  have hInt : IntegrableOn (fun t : ℝ =>
      (dirDeriv f (x + t • y) y - dirDeriv f (x - t • y) y) / t)
      (Set.Ioc (0:ℝ) (‖x‖ + R)) :=
    IntegrableOn.of_bound hfin hmeas (2 * L) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact hbound t ht.1)
  -- transfer to the half-line: the integrand vanishes beyond the window
  have hwindow : (0 : ℝ) ≤ ‖x‖ + R := by have := norm_nonneg x; linarith
  have hEq : (fun t : ℝ => (dirDeriv f (x + t • y) y - dirDeriv f (x - t • y) y) / t)
      =ᵐ[volume.restrict (Set.Ioi 0)]
      (Set.Ioc (0:ℝ) (‖x‖ + R)).indicator
        (fun t : ℝ => (dirDeriv f (x + t • y) y - dirDeriv f (x - t • y) y) / t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    by_cases hmem : t ∈ Set.Ioc (0:ℝ) (‖x‖ + R)
    · rw [Set.indicator_of_mem hmem]
    · rw [Set.indicator_of_notMem hmem]
      exact (hvanish t (by
        by_contra hc
        push Not at hc
        exact hmem ⟨ht, hc⟩))
  have hind : Integrable ((Set.Ioc (0:ℝ) (‖x‖ + R)).indicator (fun t : ℝ =>
      (dirDeriv f (x + t • y) y - dirDeriv f (x - t • y) y) / t)) :=
    (integrable_indicator_iff measurableSet_Ioc).mpr hInt
  exact (hind.integrableOn).congr hEq.symm

/-! ## Linearity of `hilbertLine` and the Hilbert condition for the truncations -/

/-- The Hilbert transform of the zero function vanishes. -/
lemma hilbertLine_zero (x y : ℝᵈ) : hilbertLine (fun _ : ℝᵈ => (0 : ℝ)) x y = 0 := by
  rw [hilbertLine_def]
  simp

/-- `dirDeriv` is additive. -/
lemma dirDeriv_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℝᵈ → ℝ) (x y : ℝᵈ)
    (hcd : ∀ k ∈ s, DifferentiableAt ℝ (f k) x) :
    dirDeriv (fun z => ∑ k ∈ s, f k z) x y = ∑ k ∈ s, dirDeriv (f k) x y := by
  have h1 : (fun z => ∑ k ∈ s, f k z) = (∑ k ∈ s, f k) := by
    funext z; rw [Finset.sum_apply]
  rw [h1, dirDeriv_apply, fderiv_sum hcd, ContinuousLinearMap.sum_apply]
  simp only [dirDeriv_apply]

/-- **Additivity of `hilbertLine` in the function.** -/
theorem hilbertLine_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℝᵈ → ℝ)
    (hcd : ∀ k ∈ s, ContDiff ℝ 2 (f k))
    (hcs : ∀ k ∈ s, HasCompactSupport (f k))
    {L : ℝ} (hL : 0 ≤ L) (hD2 : ∀ k ∈ s, ∀ z : ℝᵈ, ‖iteratedFDeriv ℝ 2 (f k) z‖ ≤ L)
    (x y : ℝᵈ) (hy : ‖y‖ = 1) :
    hilbertLine (fun z => ∑ k ∈ s, f k z) x y = ∑ k ∈ s, hilbertLine (f k) x y := by
  have hpoint : ∀ t : ℝ, (dirDeriv (fun z => ∑ k ∈ s, f k z) (x + t • y) y
        - dirDeriv (fun z => ∑ k ∈ s, f k z) (x - t • y) y) / t
      = ∑ k ∈ s, (dirDeriv (f k) (x + t • y) y - dirDeriv (f k) (x - t • y) y) / t := by
    intro t
    rw [dirDeriv_finset_sum s f _ _
        (fun k hk => ((hcd k hk).differentiable (by norm_num)).differentiableAt),
      dirDeriv_finset_sum s f _ _
        (fun k hk => ((hcd k hk).differentiable (by norm_num)).differentiableAt),
      ← Finset.sum_sub_distrib, Finset.sum_div]
  rw [hilbertLine_def]
  rw [show (fun t : ℝ => (dirDeriv (fun z => ∑ k ∈ s, f k z) (x + t • y) y
        - dirDeriv (fun z => ∑ k ∈ s, f k z) (x - t • y) y) / t)
      = fun t : ℝ => ∑ k ∈ s,
          (dirDeriv (f k) (x + t • y) y - dirDeriv (f k) (x - t • y) y) / t
    from funext hpoint]
  rw [integral_finset_sum]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [hilbertLine_def]
  · intro k hk
    exact integrableOn_hilbertIntegrand (hcd k hk) (hcs k hk) hL (hD2 k hk) x y hy

/-- `ω̃_0 = 0`: the first piece vanishes (its radial cutoff is supported in `‖x‖ ≤ 2`, where `w`
vanishes). -/
lemma omegaTildePiece_zero_eq_zero (w : ℝᵈ → ℝ) (hwzero : ∀ x, ‖x‖ ≤ 2 → w x = 0) (x : ℝᵈ) :
    omegaTildePiece (d := d) 0 w x = 0 := by
  rw [omegaTildePiece_eq]
  rcases lt_or_ge ‖x‖ 2 with h | h
  · rw [hwzero x (le_of_lt h), zero_add, if_pos (by norm_num), mul_zero]
  · rw [radialPsi_eq_zero_of_norm_ge 0 (by simpa using h), zero_mul]

/-- The second derivative of a modified piece is uniformly bounded. -/
lemma norm_iteratedFDeriv_two_omegaTildePiece_le (hd : 1 ≤ d) (k : ℕ) {w : ℝᵈ → ℝ}
    (hw : ContDiff ℝ 3 w) (hwzero : ∀ x, ‖x‖ ≤ 2 → w x = 0)
    {Creg : ℝ} (hCreg : 0 < Creg)
    (hwbound : ∀ b : ℕ, b ≤ 3 → ∀ x : ℝᵈ,
      ‖iteratedFDeriv ℝ b w x‖ ≤ Creg * (1 + ‖x‖ ^ 2) ^ ((1 - (b : ℝ)) / 2))
    (z : ℝᵈ) :
    ‖iteratedFDeriv ℝ 2 (omegaTildePiece (d := d) k w) z‖
      ≤ Creg * (tildeConst d + pieceConst d) := by
  rcases Nat.eq_zero_or_pos k with h0 | h1
  · subst h0
    rw [funext (omegaTildePiece_zero_eq_zero w hwzero)]
    have hz : iteratedFDeriv ℝ 2 (fun _ : ℝᵈ => (0 : ℝ)) z = 0 := by
      ext m; simp
    rw [hz, norm_zero]
    exact mul_nonneg hCreg.le (add_nonneg (tildeConst_nonneg d) (pieceConst_pos d).le)
  · rcases eq_or_lt_of_le (show 1 ≤ k from h1) with h1' | h2
    · -- `k = 1`: the piece is `ω_1 = ψ_1 w`
      have hk1 : k = 1 := h1'.symm
      rw [hk1]
      rw [show omegaTildePiece (d := d) 1 w = omegaPiece 1 w from
        funext fun x => omegaTildePiece_of_lt 1 w (by norm_num) x]
      refine le_trans (omegaPiece_iteratedFDeriv_le 1 2 (by norm_num) hCreg hw hwzero hwbound z) ?_
      have h1'' : (2 : ℝ) ^ (((1 : ℕ) : ℝ) * (1 - ((2 : ℕ) : ℝ))) = 1 / 2 := by
        rw [show (((1 : ℕ) : ℝ) * (1 - ((2 : ℕ) : ℝ))) = -(1 : ℝ) by norm_num,
          Real.rpow_neg_one]
        norm_num
      rw [h1'']
      nlinarith [pieceConst_pos d, hCreg.le, tildeConst_nonneg d]
    · have h2' : 2 ≤ k := by omega
      have hb := norm_iteratedFDeriv_omegaTildePiece_le (d := d) hd k 2 (by norm_num)
        (by omega) hw hwzero hCreg hwbound z
      have hCnn : (0 : ℝ) ≤ Creg * tildeConst d := mul_nonneg hCreg.le (tildeConst_nonneg d)
      have hk2 : (2 : ℝ) ^ ((1 - ((2 : ℕ) : ℝ)) * (k : ℝ)) ≤ 1 := by
        have hexp : (1 - ((2 : ℕ) : ℝ)) * (k : ℝ) = -(k : ℝ) := by
          push_cast; ring
        have hrw : (2 : ℝ) ^ (-(k : ℝ)) = ((2 : ℝ) ^ (k : ℝ))⁻¹ :=
          Real.rpow_neg (x := 2) (by norm_num) (k : ℝ)
        rw [hexp, hrw]
        have hpos : (0 : ℝ) < (2 : ℝ) ^ (k : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
        have hge : (1 : ℝ) ≤ (2 : ℝ) ^ (k : ℝ) :=
          Real.one_le_rpow (by norm_num) (by positivity)
        exact (inv_le_one₀ hpos).mpr hge
      calc ‖iteratedFDeriv ℝ 2 (omegaTildePiece (d := d) k w) z‖
          ≤ Creg * tildeConst d * (2 : ℝ) ^ ((1 - ((2 : ℕ) : ℝ)) * (k : ℝ)) := hb
        _ ≤ Creg * tildeConst d * 1 := mul_le_mul_of_nonneg_left hk2 hCnn
        _ ≤ Creg * (tildeConst d + pieceConst d) := by
            nlinarith [hCreg.le, tildeConst_nonneg d, pieceConst_pos d]

/-- The Hilbert transform of `truncSum n w` is the sum of the transforms of the pieces. -/
theorem hilbertLine_truncSum (n : ℕ) {w : ℝᵈ → ℝ} (hd : 1 ≤ d) (hw : ContDiff ℝ 3 w)
    (hwzero : ∀ x, ‖x‖ ≤ 2 → w x = 0) {Creg : ℝ} (hCreg : 0 < Creg)
    (hwbound : ∀ b : ℕ, b ≤ 3 → ∀ x : ℝᵈ,
      ‖iteratedFDeriv ℝ b w x‖ ≤ Creg * (1 + ‖x‖ ^ 2) ^ ((1 - (b : ℝ)) / 2))
    (x y : ℝᵈ) (hy : ‖y‖ = 1) :
    hilbertLine (truncSum (d := d) n w) x y
      = ∑ k ∈ Finset.range n, hilbertLine (omegaTildePiece (d := d) k w) x y := by
  have htrunc : truncSum (d := d) n w
      = fun z => ∑ k ∈ Finset.range n, omegaTildePiece (d := d) k w z := by
    funext z; exact truncSum_apply n w z
  rw [htrunc]
  refine hilbertLine_finset_sum _ _ (fun k hk => ?_) (fun k _ => hasCompactSupport_omegaTildePiece k w)
    (L := Creg * (tildeConst d + pieceConst d))
    (mul_nonneg hCreg.le (add_nonneg (tildeConst_nonneg d) (pieceConst_pos d).le))
    (fun k _ z => ?_) x y hy
  · by_cases hk1 : 1 ≤ k
    · exact (contDiff_omegaTildePiece k hw hk1).of_le
        (show (2 : WithTop ℕ∞) ≤ 3 by norm_num)
    · rw [show omegaTildePiece (d := d) k w = omegaPiece k w from
        funext fun x => omegaTildePiece_of_lt k w (by omega) x]
      exact (contDiff_omegaPiece hw k (b := 2) (by norm_num))
  · exact norm_iteratedFDeriv_two_omegaTildePiece_le hd k hw hwzero hCreg hwbound z

/-- **Condition (i) of `prop:Ew_is_psh` for the truncations.**  The sum of the Hilbert transforms
of the pieces is bounded by `400 C_reg C̃ + 256 C_gr`, uniformly in the truncation. -/
theorem abs_hilbertLine_truncSum_le (hd : 1 ≤ d) (n : ℕ) {w : ℝᵈ → ℝ}
    (hw : ContDiff ℝ 3 w) (hwnonpos : ∀ x, w x ≤ 0) (hwzero : ∀ x, ‖x‖ ≤ 2 → w x = 0)
    {Creg Cgr : ℝ} (hCreg : 0 < Creg)
    (hwbound : ∀ b : ℕ, b ≤ 3 → ∀ x : ℝᵈ,
      ‖iteratedFDeriv ℝ b w x‖ ≤ Creg * (1 + ‖x‖ ^ 2) ^ ((1 - (b : ℝ)) / 2))
    (hgrowth : HasFiniteGrowth w Cgr)
    (hwk : ∀ (k : ℕ) (x : ℝᵈ), omegaTildePiece (d := d) k w x ≤ 0)
    (x y : ℝᵈ) (hy : ‖y‖ = 1) :
    |hilbertLine (truncSum (d := d) n w) x y| ≤ 400 * (Creg * tildeConst d) + 256 * Cgr := by
  rw [hilbertLine_truncSum n hd hw hwzero hCreg hwbound x y hy]
  have h0 : |hilbertLine (omegaTildePiece (d := d) 0 w) x y| = 0 := by
    rw [funext (omegaTildePiece_zero_eq_zero w hwzero), hilbertLine_zero, abs_zero]
  have hstep : (∑ k ∈ Finset.range n, |hilbertLine (omegaTildePiece (d := d) k w) x y|)
      ≤ ∑ k ∈ Finset.Icc 1 n, |hilbertLine (omegaTildePiece (d := d) k w) x y| := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · rw [hn]; simp
    · have hmem : (0 : ℕ) ∈ Finset.range n := Finset.mem_range.mpr hn
      have h1 := Finset.sum_erase_add (Finset.range n)
        (fun k => |hilbertLine (omegaTildePiece (d := d) k w) x y|) hmem
      rw [h0, add_zero] at h1
      rw [← h1]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun k _ _ => abs_nonneg _)
      intro k hk
      rw [Finset.mem_erase, Finset.mem_range] at hk
      exact Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hk.1, by omega⟩
  refine le_trans (le_trans (Finset.abs_sum_le_sum_abs _ _) hstep) ?_
  exact sum_abs_hilbertLine_le_any (d := d) hd hw hwnonpos hwzero hCreg hwbound hgrowth hwk
    x y hy

end Submission.FUP

