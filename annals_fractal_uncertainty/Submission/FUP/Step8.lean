import Submission.FUP.HilbertLinear
import Submission.Commons.Measure.EuclideanSpace.integral_line_shift

open MeasureTheory Metric Filter Set
open scoped Real BigOperators Topology ContDiff

set_option autoImplicit false
set_option maxHeartbeats 3200000
variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

namespace Submission.FUP

/-!
# §4, step 8: the two conditions of `exact_psh_extension_statement` for the truncations

This module proves, for the compactly supported truncations `T_n = ∑_{k<n} ω̃_k` of §4,

* the uniform Lipschitz bound (`lipschitz_truncSum`),
* condition (i) of `prop:Ew_is_psh` (`abs_hilbertLine_truncSum_le`, in `HilbertLinear`),
* condition (ii) of `prop:Ew_is_psh`, i.e. the lower bound for the integral of the second
  derivative over lines (`integral_iteratedFDeriv_two_truncSum_ge`).
-/

/-! ## The uniform Lipschitz bound for the truncations -/

/-- **The truncations are Lipschitz, uniformly in `n`.**  At any point at most four of the pieces
`ω̃_k` are nonzero, so the finite sum `∑_{k<n} ω̃_k` has the same Lipschitz constant as `ω̃`. -/
theorem lipschitz_truncSum (hd : 1 ≤ d) (N : ℕ) {w : ℝᵈ → ℝ} (hw : ContDiff ℝ 3 w)
    (hwzero : ∀ x, ‖x‖ ≤ 2 → w x = 0) {Creg : ℝ} (hCreg : 0 < Creg)
    (hwbound : ∀ b : ℕ, b ≤ 3 → ∀ x : ℝᵈ,
      ‖iteratedFDeriv ℝ b w x‖ ≤ Creg * (1 + ‖x‖ ^ 2) ^ ((1 - (b : ℝ)) / 2))
    (x₁ x₂ : ℝᵈ) :
    |truncSum (d := d) N w x₁ - truncSum (d := d) N w x₂|
      ≤ Creg * omegaLipConst d * ‖x₁ - x₂‖ := by
  classical
  rw [truncSum_apply, truncSum_apply, ← Finset.sum_sub_distrib]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  set A := (Finset.range N).filter
    (fun k => omegaTildePiece (d := d) k w x₁ ≠ 0 ∨ omegaTildePiece (d := d) k w x₂ ≠ 0)
    with hA
  have hAsub : A ⊆ Finset.range N := Finset.filter_subset _ _
  have hzero : ∀ k ∈ Finset.range N, k ∉ A →
      |omegaTildePiece (d := d) k w x₁ - omegaTildePiece (d := d) k w x₂| = 0 := by
    intro k hk hkA
    have hne : ¬(omegaTildePiece (d := d) k w x₁ ≠ 0
        ∨ omegaTildePiece (d := d) k w x₂ ≠ 0) :=
      fun hc => hkA (Finset.mem_filter.mpr ⟨hk, hc⟩)
    push Not at hne
    rw [hne.1, hne.2, sub_self, abs_zero]
  rw [← Finset.sum_subset hAsub hzero]
  have hterm : ∀ k ∈ A, |omegaTildePiece (d := d) k w x₁ - omegaTildePiece (d := d) k w x₂|
      ≤ Creg * tildeLipConst d * ‖x₁ - x₂‖ := fun k _ =>
    lipschitz_omegaTildePiece hd k hw hwzero hCreg hwbound x₁ x₂
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : A.card ≤ 8 := by
    set T₁ := (Finset.range N).filter (fun k => omegaTildePiece (d := d) k w x₁ ≠ 0) with hT₁
    set T₂ := (Finset.range N).filter (fun k => omegaTildePiece (d := d) k w x₂ ≠ 0) with hT₂
    have hsub : A ⊆ T₁ ∪ T₂ := by
      intro k hk
      rw [hA, Finset.mem_filter] at hk
      rw [hT₁, hT₂, Finset.mem_union]
      rcases hk.2 with h | h
      · exact Or.inl (Finset.mem_filter.mpr ⟨hk.1, h⟩)
      · exact Or.inr (Finset.mem_filter.mpr ⟨hk.1, h⟩)
    have h1 : T₁.card ≤ 4 := by rw [hT₁]; exact card_omegaTildePiece_support_le N w x₁
    have h2 : T₂.card ≤ 4 := by rw [hT₂]; exact card_omegaTildePiece_support_le N w x₂
    calc A.card ≤ (T₁ ∪ T₂).card := Finset.card_le_card hsub
      _ ≤ T₁.card + T₂.card := Finset.card_union_le _ _
      _ ≤ 4 + 4 := by omega
  have hnn : (0 : ℝ) ≤ Creg * tildeLipConst d * ‖x₁ - x₂‖ :=
    mul_nonneg (mul_nonneg hCreg.le (tildeLipConst_nonneg d)) (norm_nonneg _)
  calc (A.card : ℝ) * (Creg * tildeLipConst d * ‖x₁ - x₂‖)
      ≤ 8 * (Creg * tildeLipConst d * ‖x₁ - x₂‖) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hnn
    _ = Creg * omegaLipConst d * ‖x₁ - x₂‖ := by rw [omegaLipConst]; ring

/-! ## The term `k = 1` of the second-derivative estimate -/

/-- The integrand `t ↦ ⟨D²ω̃_k(x + tŷ)v, v⟩` of the second-derivative estimate. -/
lemma lineSecondDeriv_apply (k : ℕ) (w : ℝᵈ → ℝ) (x y v : ℝᵈ) (t : ℝ) :
    lineSecondDeriv (d := d) k w x y v t
      = (iteratedFDeriv ℝ 2 (omegaTildePiece (d := d) k w) (x + t • y))
          (fun _ : Fin 2 => v) := rfl

/-- `ω̃_1` is supported in the ball of radius `2^{2} = 4`. -/
lemma lineSecondDeriv_one_eq_zero_of_norm_gt {w : ℝᵈ → ℝ} {x y v : ℝᵈ} {t : ℝ}
    (h : (2 : ℝ) ^ 2 < ‖x + t • y‖) :
    lineSecondDeriv (d := d) 1 w x y v t = 0 := by
  rw [lineSecondDeriv_apply, iteratedFDeriv_omegaTildePiece_eq_zero_of_norm_gt 1 w h 2]
  simp

/-- **The `k = 1` term of the second-derivative estimate.**  Since `ω̃_1` is supported in the ball
of radius `4`, the integral over the line is bounded by `‖D²ω̃_1‖_∞` times the length `8` of the
intersection of the line with that ball. -/
lemma abs_integral_lineSecondDeriv_one_le (hd : 1 ≤ d) {w : ℝᵈ → ℝ} (hw : ContDiff ℝ 3 w)
    (hwzero : ∀ x, ‖x‖ ≤ 2 → w x = 0) {Creg : ℝ} (hCreg : 0 < Creg)
    (hwbound : ∀ b : ℕ, b ≤ 3 → ∀ x : ℝᵈ,
      ‖iteratedFDeriv ℝ b w x‖ ≤ Creg * (1 + ‖x‖ ^ 2) ^ ((1 - (b : ℝ)) / 2))
    (x₀ y v : ℝᵈ) (hy : ‖y‖ = 1) (hv : ‖v‖ = 1) (hvperp : inner ℝ y v = 0) :
    |∫ t : ℝ, lineSecondDeriv (d := d) 1 w x₀ y v t| ≤ 4 * (Creg * pieceConst d) := by
  set L : ℝ := Creg * pieceConst d * (1 / 2) with hL
  have hLnn : 0 ≤ L := by
    rw [hL]; have := pieceConst_pos d; positivity
  -- the pointwise bound
  have hpoint : ∀ t : ℝ, ‖lineSecondDeriv (d := d) 1 w x₀ y v t‖ ≤ L := by
    intro t
    rw [lineSecondDeriv_apply]
    have hle : ‖(iteratedFDeriv ℝ 2 (omegaTildePiece (d := d) 1 w) (x₀ + t • y))
        (fun _ : Fin 2 => v)‖
        ≤ ‖iteratedFDeriv ℝ 2 (omegaTildePiece (d := d) 1 w) (x₀ + t • y)‖ := by
      have h := ContinuousMultilinearMap.le_opNorm
        (iteratedFDeriv ℝ 2 (omegaTildePiece (d := d) 1 w) (x₀ + t • y))
        (fun _ : Fin 2 => v)
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, hv] at h
      simpa using h
    refine le_trans hle ?_
    rw [show omegaTildePiece (d := d) 1 w = omegaPiece 1 w from
      funext fun x => omegaTildePiece_of_lt 1 w (by norm_num) x]
    refine le_trans (omegaPiece_iteratedFDeriv_le 1 2 (by norm_num) hCreg hw hwzero hwbound
      (x₀ + t • y)) ?_
    have hrw : (2 : ℝ) ^ (((1 : ℕ) : ℝ) * (1 - ((2 : ℕ) : ℝ))) = 1 / 2 := by
      have hexp : (((1 : ℕ) : ℝ) * (1 - ((2 : ℕ) : ℝ))) = -(1 : ℝ) := by push_cast; ring
      rw [hexp, Real.rpow_neg_one]; norm_num
    rw [hrw, hL]
  -- the measure of the window
  set s : Set ℝ := {t : ℝ | ‖x₀ + t • y‖ ≤ (2 : ℝ) ^ 2} with hs
  have hs_meas : MeasurableSet s :=
    (isClosed_le ((continuous_const.add (continuous_id.smul continuous_const)).norm)
      continuous_const).measurableSet
  have hs_fin : volume s < ⊤ := by
    refine lt_of_le_of_lt (Commons.Measure.EuclideanSpace.volume_line_ball x₀ y hy ((2 : ℝ) ^ 2))
      ENNReal.ofReal_lt_top
  -- the integrand vanishes off `s`
  have hzero : ∀ t : ℝ, t ∉ s → lineSecondDeriv (d := d) 1 w x₀ y v t = 0 := by
    intro t ht
    rw [hs, Set.mem_ofPred_eq, not_le] at ht
    exact lineSecondDeriv_one_eq_zero_of_norm_gt ht
  have hEq : (∫ t : ℝ, lineSecondDeriv (d := d) 1 w x₀ y v t)
      = ∫ t in s, lineSecondDeriv (d := d) 1 w x₀ y v t := by
    rw [← integral_indicator hs_meas]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    by_cases ht : t ∈ s
    · rw [Set.indicator_of_mem ht]
    · rw [Set.indicator_of_notMem ht, hzero t ht]
  rw [hEq]
  have hbound := norm_setIntegral_le_of_norm_le_const_ae' hs_fin
    (show ∀ᵐ t ∂(volume : Measure ℝ), t ∈ s → ‖lineSecondDeriv (d := d) 1 w x₀ y v t‖ ≤ L from
      Eventually.of_forall fun t _ => hpoint t)
  refine le_trans hbound ?_
  have hvol : (volume : Measure ℝ).real s ≤ 8 := by
    have h1 := ENNReal.toReal_mono ENNReal.ofReal_ne_top
      (Commons.Measure.EuclideanSpace.volume_line_ball x₀ y hy ((2 : ℝ) ^ 2))
    rw [ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 2 * (2 : ℝ) ^ 2)] at h1
    norm_num at h1
    have h4 : (2 : ℝ) ^ 2 = 4 := by norm_num
    rw [hs, h4]
    simpa [MeasureTheory.Measure.real] using h1
  calc L * (volume : Measure ℝ).real s ≤ L * 8 := mul_le_mul_of_nonneg_left hvol hLnn
    _ = 4 * (Creg * pieceConst d) := by rw [hL]; ring

/-! ## The line integrals of the second derivative of the pieces -/

/-- The shifted second-derivative integrand is continuous. -/
lemma continuous_lineSecondDeriv (k : ℕ) {w : ℝᵈ → ℝ} (hw : ContDiff ℝ 3 w)
    (hwzero : ∀ x, ‖x‖ ≤ 2 → w x = 0) (x y v : ℝᵈ) :
    Continuous (fun t : ℝ => lineSecondDeriv (d := d) k w x y v t) := by
  rcases Nat.eq_zero_or_pos k with h0 | h1
  · subst h0
    have hz : lineSecondDeriv (d := d) 0 w x y v = fun _ => (0 : ℝ) := by
      funext t
      rw [lineSecondDeriv_apply, funext (omegaTildePiece_zero_eq_zero w hwzero)]
      simp
    rw [hz]; exact continuous_const
  · have hcd : ContDiff ℝ 3 (omegaTildePiece (d := d) k w) := contDiff_omegaTildePiece k hw h1
    have hcont : Continuous (fun t : ℝ => iteratedFDeriv ℝ 2 (omegaTildePiece (d := d) k w)
        (x + t • y)) :=
      (ContDiff.continuous_iteratedFDeriv (𝕜 := ℝ) (f := omegaTildePiece (d := d) k w)
        (n := (3 : ℕ∞ω)) (m := 2) (by norm_num) hcd).comp
        (continuous_const.add (continuous_id.smul continuous_const))
    exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => ℝᵈ) ℝ
      (fun _ : Fin 2 => v)).continuous.comp hcont

/-- The shifted second-derivative integrand is compactly supported. -/
lemma hasCompactSupport_lineSecondDeriv (k : ℕ) (w : ℝᵈ → ℝ) (x y v : ℝᵈ) (hy : ‖y‖ = 1) :
    HasCompactSupport (fun t : ℝ => lineSecondDeriv (d := d) k w x y v t) := by
  have hsub : tsupport (fun t : ℝ => lineSecondDeriv (d := d) k w x y v t) ⊆
      Set.Icc (-(‖x‖ + (2 : ℝ) ^ (k + 1))) (‖x‖ + (2 : ℝ) ^ (k + 1)) := by
    rw [tsupport]
    refine closure_minimal ?_ isClosed_Icc
    intro t ht
    rw [Function.mem_support] at ht
    simp only [lineSecondDeriv_apply] at ht
    have hle : ‖x + t • y‖ ≤ (2 : ℝ) ^ (k + 1) := by
      by_contra hc
      push Not at hc
      exact ht (by rw [iteratedFDeriv_omegaTildePiece_eq_zero_of_norm_gt k w hc 2]; simp)
    have hb : |t| ≤ ‖x‖ + (2 : ℝ) ^ (k + 1) := by
      have h2 : ‖t • y‖ = |t| := by rw [norm_smul, Real.norm_eq_abs, hy, mul_one]
      have h3 : ‖t • y‖ ≤ ‖x + t • y‖ + ‖x‖ := by
        calc ‖t • y‖ = ‖(x + t • y) - x‖ := by rw [add_sub_cancel_left]
          _ ≤ ‖x + t • y‖ + ‖x‖ := norm_sub_le _ _
      rw [h2] at h3
      linarith
    exact Set.mem_Icc.mpr (abs_le.mp hb)
  exact (isCompact_Icc).of_isClosed_subset (isClosed_tsupport _) hsub

/-- **Translation of the line integral.**  The integral of the second derivative over a line only
depends on the line, so we may replace the base point by the foot of the perpendicular from the
origin. -/
lemma integral_lineSecondDeriv_shift (k : ℕ) (w : ℝᵈ → ℝ) (x y v : ℝᵈ) (hy : ‖y‖ = 1) :
    (∫ t : ℝ, lineSecondDeriv (d := d) k w x y v t)
      = ∫ t : ℝ, lineSecondDeriv (d := d) k w
          (x - (inner ℝ x y) • y) y v t := by
  set x₀ : ℝᵈ := x - (inner ℝ x y) • y with hx₀
  have hperp : inner ℝ x₀ y = 0 := by
    rw [hx₀, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hy]
    ring
  have hx : x = x₀ + (inner ℝ x y) • y := by rw [hx₀]; abel
  rw [hx]
  exact Commons.Measure.EuclideanSpace.integral_line_shift
    (fun z : ℝᵈ => (iteratedFDeriv ℝ 2 (omegaTildePiece (d := d) k w) z)
      (fun _ : Fin 2 => v))
    x₀ y hy hperp (inner ℝ x y)

/-! ## Condition (ii) of `prop:Ew_is_psh` for the truncations -/

/-- **Condition (ii) for the truncations.**  The integral over any line of the second derivative of
`T_n = ∑_{k<n} ω̃_k` in the direction of a perpendicular unit vector is bounded below by `-C₂`,
with `C₂` independent of `n`. -/
theorem integral_iteratedFDeriv_two_truncSum_ge (hd : 1 ≤ d) (N : ℕ) {w : ℝᵈ → ℝ}
    (hw : ContDiff ℝ 3 w) (hwnonpos : ∀ x, w x ≤ 0) (hwzero : ∀ x, ‖x‖ ≤ 2 → w x = 0)
    {Creg Cgr : ℝ} (hCreg : 0 < Creg)
    (hwbound : ∀ b : ℕ, b ≤ 3 → ∀ x : ℝᵈ,
      ‖iteratedFDeriv ℝ b w x‖ ≤ Creg * (1 + ‖x‖ ^ 2) ^ ((1 - (b : ℝ)) / 2))
    (hgrowth : HasFiniteGrowth w Cgr)
    (x y v : ℝᵈ) (hy : ‖y‖ = 1) (hv : ‖v‖ = 1) (hvperp : inner ℝ y v = 0) :
    -(32 * Creg * tildeConst d + 256 * Cgr + 4 * (Creg * pieceConst d) + 1)
      ≤ (1 / π) * ∫ t : ℝ, ((iteratedFDeriv ℝ 2 (truncSum (d := d) N w) (x + t • y))
          (fun _ : Fin 2 => v)) := by
  set x₀ : ℝᵈ := x - (inner ℝ x y) • y with hx₀
  -- the finite-sum decomposition of the integrand and the translation
  have hmain : (∫ t : ℝ, ((iteratedFDeriv ℝ 2 (truncSum (d := d) N w) (x + t • y))
        (fun _ : Fin 2 => v)))
      = ∑ k ∈ Finset.range N, ∫ t : ℝ, lineSecondDeriv (d := d) k w x₀ y v t := by
    have hpoint : ∀ t : ℝ, ((iteratedFDeriv ℝ 2 (truncSum (d := d) N w) (x + t • y))
        (fun _ : Fin 2 => v))
        = ∑ k ∈ Finset.range N, lineSecondDeriv (d := d) k w x y v t := by
      intro t
      rw [iteratedFDeriv_truncSum N 2 (by norm_num) hw (x + t • y),
        ContinuousMultilinearMap.sum_apply]
      rfl
    rw [funext hpoint, integral_finset_sum]
    · refine Finset.sum_congr rfl fun k _ => integral_lineSecondDeriv_shift k w x y v hy
    · intro k _
      rcases Nat.eq_zero_or_pos k with h0 | h1
      · subst h0
        have hz : lineSecondDeriv (d := d) 0 w x y v = fun _ => (0 : ℝ) := by
          funext t
          rw [lineSecondDeriv_apply, funext (omegaTildePiece_zero_eq_zero w hwzero)]
          simp
        rw [hz]; exact integrable_zero _ _ _
      · exact (continuous_lineSecondDeriv k hw hwzero x y v).integrable_of_hasCompactSupport
          (hasCompactSupport_lineSecondDeriv k w x y v hy)
  rw [hmain]
  -- the upper bound for the sum of absolute values
  set B : ℝ := 32 * Creg * tildeConst d + 256 * Cgr + 4 * (Creg * pieceConst d) with hB
  have hsum : (∑ k ∈ Finset.range N, |∫ t : ℝ, lineSecondDeriv (d := d) k w x₀ y v t|) ≤ B := by
    set f : ℕ → ℝ := fun k => |∫ t : ℝ, lineSecondDeriv (d := d) k w x₀ y v t| with hf
    have hcover : Finset.range N ⊆ ({0, 1} : Finset ℕ) ∪ Finset.Icc 2 N := by
      intro k hk
      rw [Finset.mem_range] at hk
      rcases lt_or_ge k 2 with h | h
      · interval_cases k <;> simp
      · exact Finset.mem_union_right _ (Finset.mem_Icc.mpr ⟨h, by omega⟩)
    have hdisj : Disjoint ({0, 1} : Finset ℕ) (Finset.Icc 2 N) := by
      rw [Finset.disjoint_left]
      intro a ha hb
      rw [Finset.mem_Icc] at hb
      fin_cases ha <;> omega
    have hstep1 : (∑ k ∈ Finset.range N, f k) ≤ ∑ k ∈ ({0, 1} : Finset ℕ) ∪ Finset.Icc 2 N, f k :=
      Finset.sum_le_sum_of_subset_of_nonneg hcover (fun k _ _ => abs_nonneg _)
    rw [Finset.sum_union hdisj] at hstep1
    have hpair : (∑ k ∈ ({0, 1} : Finset ℕ), f k) = f 0 + f 1 := by
      rw [Finset.sum_pair (by norm_num : (0 : ℕ) ≠ 1)]
    rw [hpair] at hstep1
    have hf0 : f 0 = 0 := by
      change |∫ t : ℝ, lineSecondDeriv (d := d) 0 w x₀ y v t| = 0
      have hz : lineSecondDeriv (d := d) 0 w x₀ y v = fun _ => (0 : ℝ) := by
        funext t
        rw [lineSecondDeriv_apply, funext (omegaTildePiece_zero_eq_zero w hwzero)]
        simp
      rw [hz, integral_zero, abs_zero]
    have hf1 : f 1 ≤ 4 * (Creg * pieceConst d) := by
      rw [hf]
      exact abs_integral_lineSecondDeriv_one_le hd hw hwzero hCreg hwbound x₀ y v hy hv hvperp
    have htail : (∑ k ∈ Finset.Icc 2 N, f k) ≤ 32 * Creg * tildeConst d + 256 * Cgr := by
      have hperp₀ : inner ℝ x₀ y = 0 := by
        rw [hx₀, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hy]
        ring
      have := sum_abs_integral_second_deriv_le (d := d) hd (K := N) hw hwnonpos hwzero hCreg
        hwbound hgrowth x₀ y v hy hv hvperp hperp₀
      simpa [hf] using this
    rw [hf0] at hstep1
    linarith [hstep1, hf1, htail]
  -- conclude
  have hge : -B ≤ ∑ k ∈ Finset.range N, ∫ t : ℝ, lineSecondDeriv (d := d) k w x₀ y v t := by
    have h1 : -(∑ k ∈ Finset.range N, |∫ t : ℝ, lineSecondDeriv (d := d) k w x₀ y v t|)
        ≤ ∑ k ∈ Finset.range N, ∫ t : ℝ, lineSecondDeriv (d := d) k w x₀ y v t := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_le_sum fun k _ => neg_abs_le _
    linarith
  have hCgr0 : 0 ≤ Cgr := by
    obtain ⟨hint, hle⟩ := hgrowth
    have h1 : (0 : ℝ) ≤ ∫ r in Set.Ioi (0 : ℝ), Gstar w r / (1 + r ^ 2) :=
      setIntegral_nonneg measurableSet_Ioi (fun r _ =>
        div_nonneg (Gstar_nonneg w r) (by positivity))
    rw [← growthFunctional_eq_Gstar] at h1
    linarith
  have hBnn : 0 ≤ B := by
    rw [hB]
    have h1 := tildeConst_nonneg d
    have h2 := (pieceConst_pos d).le
    nlinarith [hCreg.le, hCgr0]
  have hπpos : (0 : ℝ) < 1 / π := by positivity
  have hπle : (1 : ℝ) / π ≤ 1 := by
    rw [div_le_one (by positivity : (0 : ℝ) < π)]
    linarith [Real.pi_gt_three]
  have h1 : (1 / π) * (-B) ≤ (1 / π) * (∑ k ∈ Finset.range N,
      ∫ t : ℝ, lineSecondDeriv (d := d) k w x₀ y v t) :=
    mul_le_mul_of_nonneg_left hge hπpos.le
  have h3 : (1 / π) * (-B) = -((1 / π) * B) := by ring
  rw [h3] at h1
  have h2 : (1 / π) * B ≤ B := by nlinarith
  linarith

end Submission.FUP

