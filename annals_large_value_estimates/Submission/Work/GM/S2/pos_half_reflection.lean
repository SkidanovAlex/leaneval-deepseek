import Mathlib
import Submission.Work.GM.S2.pair_sum_defs
import Submission.Work.GM.S2.hhat_sum_tail
import Submission.Work.GM.S2.tail_nat_hhat
import Submission.Work.GM.S2.Spos_split
import Submission.Work.GM.S2.polysum_basic

/-!
# The reflection Cauchy–Schwarz step of GM §6 (`pos_half_reflection`)

The reflection lemma of Guth–Maynard §6 (`hrefl`, `Work.GM.S2.ReflHyp`) bounds the finite
`m`-sum `Σ_{m ≤ ⌊Y⌋} ĥ_t(mN)` by the integral

`∫ ξ, ‖ĝ₁(ξ)‖ (1+|t+2πξ|)^{-1/2} ‖Σ_{m ≤ ⌊Y⌋} m^{i(t+2πξ)}‖ dξ`.

Here we turn that `L¹` bound into the `L²` bound that the pair sum needs: writing
`gwt ξ = ‖ĝ₁ ξ‖ (1+|2πξ|)^{1/2}` (the "mass" weight), Cauchy–Schwarz with the two factors

`F ξ = gwt ξ^{1/2} ‖PolySum Y (t+2πξ)‖`,  `G ξ = gwt ξ^{1/2} (1+|2πξ|)^{-1/2}(1+|t+2πξ|)^{-1/2}`

gives, using `(1+|2πξ|)(1+|t+2πξ|) ≥ 1+|t|`,

`(Σ_{m ≤ ⌊Y⌋} ĥ_t(mN))² ≪ (1+|t|)^{-1} (∫ gwt) (∫ gwt ξ ‖PolySum Y (t+2πξ)‖²)`

(and `∫ gwt ≤ m1` is the hypothesis `hmass`).  The infinite tail of the positive half is
estimated separately (`tail_nat_hhat`).
-/

open Complex Finset MeasureTheory
open scoped BigOperators Topology

set_option autoImplicit false

namespace Work.GM.S2

/-- The weight `gwt ξ = ‖ĝ₁ ξ‖ (1+|2πξ|)^{1/2}` is nonnegative. -/
lemma gwt_nonneg (ξ : ℝ) : 0 ≤ gwt ξ := by
  rw [gwt]
  have := Real.rpow_nonneg (show (0 : ℝ) ≤ 1 + |2 * Real.pi * ξ| by positivity) (1 / 2 : ℝ)
  positivity

/-- `gwt` with the half power removed reproduces `‖ĝ₁ ξ‖`. -/
lemma gwt_mul_rpow_neg_half (ξ : ℝ) :
    gwt ξ * (1 + |2 * Real.pi * ξ|) ^ (-(1 / 2 : ℝ)) = ‖ghat1 ξ‖ := by
  rw [gwt, mul_assoc, ← Real.rpow_add (show (0 : ℝ) < 1 + |2 * Real.pi * ξ| by positivity)]
  norm_num

/-- The elementary triangle-inequality input for the reflection: with `a = 2πξ` and
`b = t + 2πξ` one has `|a - b| = |t|`, hence `(1+|2πξ|)(1+|t+2πξ|) ≥ 1+|t|`. -/
lemma inv_mul_one_add_abs_le (t ξ : ℝ) :
    ((1 + |2 * Real.pi * ξ|) * (1 + |t + 2 * Real.pi * ξ|))⁻¹ ≤ (1 + |t|)⁻¹ := by
  have h1 : |t| ≤ |t + 2 * Real.pi * ξ| + |2 * Real.pi * ξ| := by
    have h := abs_add_le (t + 2 * Real.pi * ξ) (-(2 * Real.pi * ξ))
    simpa using h
  have ha : (0 : ℝ) ≤ |2 * Real.pi * ξ| := abs_nonneg _
  have hb : (0 : ℝ) ≤ |t + 2 * Real.pi * ξ| := abs_nonneg _
  have hprod : 1 + |t| ≤ (1 + |2 * Real.pi * ξ|) * (1 + |t + 2 * Real.pi * ξ|) := by
    nlinarith [mul_nonneg ha hb]
  exact inv_anti₀ (by positivity) hprod

/-- **The reflection Cauch–Schwarz step.**  The finite `m`-sum of the reflection lemma,
squared, is bounded by `(1+|t|)^{-1} m1 ∫ gwt ξ ‖PolySum Y (t+2πξ)‖²`. -/
lemma refl_sq_le (hrefl : ReflHyp) (m1 : ℝ) (hm1 : 0 ≤ m1)
    (hgwt : Integrable gwt) (hmass : (∫ ξ, gwt ξ) ≤ m1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ), 1 ≤ N → ∀ (t Y : ℝ), 1 ≤ |t| → 1 ≤ Y →
      ‖∑ m ∈ Finset.Icc 1 (Nat.floor Y), Submission.GM.hhat t ((m : ℝ) * (N : ℝ))‖ ^ 2
        ≤ C * ((1 + |t|)⁻¹ * (m1 * ∫ ξ, gwt ξ * ‖PolySum Y (t + 2 * Real.pi * ξ)‖ ^ 2)) := by
  obtain ⟨Cr, hCrpos, hrefl'⟩ := hrefl
  refine ⟨Cr ^ 2, by positivity, fun N hN t Y ht hY => ?_⟩
  have hPScont : Continuous (fun ξ : ℝ => PolySum Y (t + 2 * Real.pi * ξ)) := continuous_polysum_affine Y t
  have hPSbdd : ∀ ξ : ℝ, ‖PolySum Y (t + 2 * Real.pi * ξ)‖ ≤ (Nat.floor Y : ℝ) :=
    fun ξ => norm_polysum_le Y _
  set w1 : ℝ → ℝ := fun ξ => (Real.sqrt (1 + |2 * Real.pi * ξ|))⁻¹ with hw1
  set w2 : ℝ → ℝ := fun ξ => (Real.sqrt (1 + |t + 2 * Real.pi * ξ|))⁻¹ with hw2
  set F : ℝ → ℝ := fun ξ => Real.sqrt (gwt ξ) * ‖PolySum Y (t + 2 * Real.pi * ξ)‖ with hF
  set G : ℝ → ℝ := fun ξ => Real.sqrt (gwt ξ) * (w1 ξ * w2 ξ) with hG
  -- elementary evaluations of the two weights
  have hw1eval : ∀ ξ, w1 ξ = (Real.sqrt (1 + |2 * Real.pi * ξ|))⁻¹ := fun ξ => by rw [hw1]
  have hw2eval : ∀ ξ, w2 ξ = (Real.sqrt (1 + |t + 2 * Real.pi * ξ|))⁻¹ := fun ξ => by rw [hw2]
  have hw1sq : ∀ ξ, w1 ξ ^ 2 = (1 + |2 * Real.pi * ξ|)⁻¹ := by
    intro ξ
    rw [hw1eval ξ, inv_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 1 + |2 * Real.pi * ξ|)]
  have hw2sq : ∀ ξ, w2 ξ ^ 2 = (1 + |t + 2 * Real.pi * ξ|)⁻¹ := by
    intro ξ
    rw [hw2eval ξ, inv_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 1 + |t + 2 * Real.pi * ξ|)]
  -- the two weights are jointly bounded by `(1+|t|)^{-1}`
  have hwprod : ∀ ξ, w1 ξ ^ 2 * w2 ξ ^ 2 ≤ (1 + |t|)⁻¹ := by
    intro ξ
    rw [hw1sq ξ, hw2sq ξ, ← mul_inv]
    exact inv_mul_one_add_abs_le t ξ
  have hwnn : ∀ ξ, 0 ≤ w1 ξ := fun ξ => by rw [hw1eval ξ]; positivity
  have hwnn2 : ∀ ξ, 0 ≤ w2 ξ := fun ξ => by rw [hw2eval ξ]; positivity
  -- pointwise evaluations of `F` and `G`
  have hFeval : ∀ ξ, F ξ = Real.sqrt (gwt ξ) * ‖PolySum Y (t + 2 * Real.pi * ξ)‖ := fun ξ => by
    rw [hF]
  have hGeval : ∀ ξ, G ξ = Real.sqrt (gwt ξ) * (w1 ξ * w2 ξ) := fun ξ => by rw [hG]
  have hF2 : ∀ ξ, F ξ ^ 2 = gwt ξ * ‖PolySum Y (t + 2 * Real.pi * ξ)‖ ^ 2 := by
    intro ξ
    rw [hFeval ξ, mul_pow, Real.sq_sqrt (gwt_nonneg ξ)]
  have hFnn : ∀ ξ, 0 ≤ F ξ := by
    intro ξ
    rw [hFeval ξ]
    positivity
  have hGnn : ∀ ξ, 0 ≤ G ξ := by
    intro ξ
    rw [hGeval ξ]
    exact mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg (hwnn ξ) (hwnn2 ξ))
  have hG2 : ∀ ξ, G ξ ^ 2 ≤ (1 + |t|)⁻¹ * gwt ξ := by
    intro ξ
    rw [hGeval ξ, mul_pow, mul_pow, Real.sq_sqrt (gwt_nonneg ξ)]
    calc gwt ξ * (w1 ξ ^ 2 * w2 ξ ^ 2) ≤ gwt ξ * (1 + |t|)⁻¹ :=
          mul_le_mul_of_nonneg_left (hwprod ξ) (gwt_nonneg ξ)
      _ = (1 + |t|)⁻¹ * gwt ξ := by ring
  -- the product of `F` and `G` is the integrand of the reflection lemma
  have hsqgwt : ∀ ξ, Real.sqrt (gwt ξ) * Real.sqrt (gwt ξ) = gwt ξ :=
    fun ξ => Real.mul_self_sqrt (gwt_nonneg ξ)
  have hFG : ∀ ξ, F ξ * G ξ
      = ‖ghat1 ξ‖ * (1 + |t + 2 * Real.pi * ξ|) ^ (-(1 / 2 : ℝ))
          * ‖PolySum Y (t + 2 * Real.pi * ξ)‖ := by
    intro ξ
    -- first express `G ξ` through the `rpow` weights of the reflection hypothesis
    have hw1r : (1 + |2 * Real.pi * ξ|) ^ (1 / 2 : ℝ) * w1 ξ = 1 := by
      rw [hw1eval ξ, Real.sqrt_eq_rpow]
      exact mul_inv_cancel₀ (ne_of_gt (Real.rpow_pos_of_pos (by positivity) _))
    have hw2r : w2 ξ = (1 + |t + 2 * Real.pi * ξ|) ^ (-(1 / 2 : ℝ)) := by
      rw [hw2eval ξ, Real.sqrt_eq_rpow,
        ← Real.rpow_neg (by positivity : (0 : ℝ) ≤ 1 + |t + 2 * Real.pi * ξ|)]
    have hgwtmul : gwt ξ * w1 ξ = ‖ghat1 ξ‖ := by
      rw [gwt, mul_assoc, hw1r]
      ring
    have hsplit : Real.sqrt (gwt ξ) * ‖PolySum Y (t + 2 * Real.pi * ξ)‖
          * (Real.sqrt (gwt ξ) * (w1 ξ * w2 ξ))
        = (Real.sqrt (gwt ξ) * Real.sqrt (gwt ξ)) * w1 ξ * w2 ξ
            * ‖PolySum Y (t + 2 * Real.pi * ξ)‖ := by ring
    rw [hFeval ξ, hGeval ξ, hsplit, hsqgwt ξ, hgwtmul, hw2r]
  -- integrability / membership in `L²`
  have hIntF2 : Integrable (fun ξ : ℝ => gwt ξ * ‖PolySum Y (t + 2 * Real.pi * ξ)‖ ^ 2) := by
    have hmaj : Integrable (fun ξ : ℝ => ((Nat.floor Y : ℝ) ^ 2) * gwt ξ) :=
      hgwt.const_mul _
    refine hmaj.mono' ?_ ?_
    · exact AEStronglyMeasurable.mul hgwt.aestronglyMeasurable
        (hPScont.aestronglyMeasurable.norm.pow 2)
    · filter_upwards with ξ
      rw [Real.norm_of_nonneg (mul_nonneg (gwt_nonneg ξ)
        (sq_nonneg (‖PolySum Y (t + 2 * Real.pi * ξ)‖)))]
      have h1 : ‖PolySum Y (t + 2 * Real.pi * ξ)‖ ^ 2 ≤ (Nat.floor Y : ℝ) ^ 2 := by
        have hb := hPSbdd ξ
        have hnn := norm_nonneg (PolySum Y (t + 2 * Real.pi * ξ))
        have hY : (0 : ℝ) ≤ (Nat.floor Y : ℝ) := Nat.cast_nonneg _
        nlinarith [hb, hnn, hY]
      calc gwt ξ * ‖PolySum Y (t + 2 * Real.pi * ξ)‖ ^ 2
          ≤ gwt ξ * (Nat.floor Y : ℝ) ^ 2 := mul_le_mul_of_nonneg_left h1 (gwt_nonneg ξ)
        _ = (Nat.floor Y : ℝ) ^ 2 * gwt ξ := by ring
  have hFae : AEStronglyMeasurable F volume := by
    rw [show F = fun ξ => Real.sqrt (gwt ξ) * ‖PolySum Y (t + 2 * Real.pi * ξ)‖ from funext hFeval]
    exact (Real.continuous_sqrt.comp_aestronglyMeasurable hgwt.aestronglyMeasurable).mul
      hPScont.aestronglyMeasurable.norm
  have hGae : AEStronglyMeasurable G volume := by
    rw [show G = fun ξ => Real.sqrt (gwt ξ) * (w1 ξ * w2 ξ) from funext hGeval]
    have hw1ae : AEStronglyMeasurable w1 volume := by
      rw [show w1 = fun ξ => (Real.sqrt (1 + |2 * Real.pi * ξ|))⁻¹ from funext hw1eval]
      exact ((by fun_prop : AEMeasurable (fun ξ : ℝ => (Real.sqrt (1 + |2 * Real.pi * ξ|))⁻¹)
        volume)).aestronglyMeasurable
    have hw2ae : AEStronglyMeasurable w2 volume := by
      rw [show w2 = fun ξ => (Real.sqrt (1 + |t + 2 * Real.pi * ξ|))⁻¹ from funext hw2eval]
      exact ((by fun_prop : AEMeasurable (fun ξ : ℝ =>
        (Real.sqrt (1 + |t + 2 * Real.pi * ξ|))⁻¹) volume)).aestronglyMeasurable
    exact (Real.continuous_sqrt.comp_aestronglyMeasurable hgwt.aestronglyMeasurable).mul
      (hw1ae.mul hw2ae)
  have hFLp : MemLp F 2 volume :=
    (memLp_two_iff_integrable_sq hFae).mpr (by
      refine hIntF2.congr ?_
      filter_upwards with ξ
      exact (hF2 ξ).symm)
  have hGLp : MemLp G 2 volume :=
    (memLp_two_iff_integrable_sq hGae).mpr (by
      refine ((hgwt.const_mul ((1 + |t|)⁻¹))).mono' (hGae.pow 2) ?_
      filter_upwards with ξ
      rw [Real.norm_of_nonneg (by positivity)]
      exact hG2 ξ)
  -- Cauchy–Schwarz
  have hpq : (2 : ℝ).HolderConjugate 2 := Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have hFLp' : MemLp F (ENNReal.ofReal 2) volume := by simpa using hFLp
  have hGLp' : MemLp G (ENNReal.ofReal 2) volume := by simpa using hGLp
  have hCS := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume) (p := 2) (q := 2) hpq
    (Filter.Eventually.of_forall hFnn) (Filter.Eventually.of_forall hGnn) hFLp' hGLp'
  -- rewrite the reflection bound in terms of `F * G`
  have hFGint : (∫ ξ, F ξ * G ξ) = ∫ ξ, ‖ghat1 ξ‖ * (1 + |t + 2 * Real.pi * ξ|) ^ (-(1 / 2 : ℝ))
      * ‖PolySum Y (t + 2 * Real.pi * ξ)‖ :=
    integral_congr_ae (Filter.Eventually.of_forall hFG)
  have hA : ‖∑ m ∈ Finset.Icc 1 (Nat.floor Y), Submission.GM.hhat t ((m : ℝ) * (N : ℝ))‖
      ≤ Cr * ∫ ξ, F ξ * G ξ := by
    have h : ‖∑ m ∈ Finset.Icc 1 (Nat.floor Y), Submission.GM.hhat t ((m : ℝ) * (N : ℝ))‖
        ≤ Cr * ∫ ξ, ‖ghat1 ξ‖ * (1 + |t + 2 * Real.pi * ξ|) ^ (-(1 / 2 : ℝ))
            * ‖PolySum Y (t + 2 * Real.pi * ξ)‖ := by
      simpa only [PolySum] using hrefl' N hN t Y ht hY
    rw [← hFGint] at h
    exact h
  -- square the Cauchy–Schwarz bound
  have hF2val : (∫ ξ, F ξ ^ 2) = ∫ ξ, gwt ξ * ‖PolySum Y (t + 2 * Real.pi * ξ)‖ ^ 2 :=
    integral_congr_ae (Filter.Eventually.of_forall hF2)
  have hG2le : (∫ ξ, G ξ ^ 2) ≤ (1 + |t|)⁻¹ * m1 := by
    have hIntG2 : Integrable (fun ξ : ℝ => G ξ ^ 2) :=
      (hgwt.const_mul ((1 + |t|)⁻¹)).mono' (hGae.pow 2)
        (by filter_upwards with ξ
            rw [Real.norm_of_nonneg (sq_nonneg _)]
            exact hG2 ξ)
    have hmono : (∫ ξ, G ξ ^ 2) ≤ ∫ ξ, (1 + |t|)⁻¹ * gwt ξ :=
      integral_mono hIntG2 (hgwt.const_mul _) (fun ξ => hG2 ξ)
    rw [integral_const_mul] at hmono
    have h2 := mul_le_mul_of_nonneg_left hmass (by positivity : (0 : ℝ) ≤ (1 + |t|)⁻¹)
    linarith
  have hCSsqrt : (∫ ξ, F ξ * G ξ) ≤ Real.sqrt (∫ ξ, F ξ ^ 2) * Real.sqrt (∫ ξ, G ξ ^ 2) := by
    have h1 : (∫ ξ, F ξ ^ (2 : ℝ)) = ∫ ξ, F ξ ^ 2 :=
      integral_congr_ae (Filter.Eventually.of_forall (fun ξ => Real.rpow_natCast _ 2))
    have h2 : (∫ ξ, G ξ ^ (2 : ℝ)) = ∫ ξ, G ξ ^ 2 :=
      integral_congr_ae (Filter.Eventually.of_forall (fun ξ => Real.rpow_natCast _ 2))
    rw [h1, h2, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hCS
    exact hCS
  have hCS2 : (∫ ξ, F ξ * G ξ) ^ 2 ≤ (∫ ξ, F ξ ^ 2) * (∫ ξ, G ξ ^ 2) := by
    have h0 : 0 ≤ ∫ ξ, F ξ * G ξ := integral_nonneg (fun ξ => mul_nonneg (hFnn ξ) (hGnn ξ))
    have hA1 : 0 ≤ ∫ ξ, F ξ ^ 2 := integral_nonneg (fun ξ => sq_nonneg _)
    have hB1 : 0 ≤ ∫ ξ, G ξ ^ 2 := integral_nonneg (fun ξ => sq_nonneg _)
    have h := pow_le_pow_left₀ h0 hCSsqrt 2
    rw [mul_pow, Real.sq_sqrt hA1, Real.sq_sqrt hB1] at h
    exact h
  have hA2 : ‖∑ m ∈ Finset.Icc 1 (Nat.floor Y), Submission.GM.hhat t ((m : ℝ) * (N : ℝ))‖ ^ 2
      ≤ Cr ^ 2 * (∫ ξ, F ξ * G ξ) ^ 2 := by
    have h := pow_le_pow_left₀ (norm_nonneg _) hA 2
    rwa [mul_pow] at h
  have hBnn : 0 ≤ ∫ ξ, gwt ξ * ‖PolySum Y (t + 2 * Real.pi * ξ)‖ ^ 2 :=
    integral_nonneg (fun ξ => mul_nonneg (gwt_nonneg ξ) (sq_nonneg _))
  calc ‖∑ m ∈ Finset.Icc 1 (Nat.floor Y), Submission.GM.hhat t ((m : ℝ) * (N : ℝ))‖ ^ 2
      ≤ Cr ^ 2 * (∫ ξ, F ξ * G ξ) ^ 2 := hA2
    _ ≤ Cr ^ 2 * ((∫ ξ, F ξ ^ 2) * (∫ ξ, G ξ ^ 2)) :=
        mul_le_mul_of_nonneg_left hCS2 (by positivity)
    _ = Cr ^ 2 * ((∫ ξ, gwt ξ * ‖PolySum Y (t + 2 * Real.pi * ξ)‖ ^ 2) * (∫ ξ, G ξ ^ 2)) := by
        rw [hF2val]
    _ ≤ Cr ^ 2 * ((∫ ξ, gwt ξ * ‖PolySum Y (t + 2 * Real.pi * ξ)‖ ^ 2) * ((1 + |t|)⁻¹ * m1)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hG2le hBnn) (by positivity)
    _ = Cr ^ 2 * ((1 + |t|)⁻¹ * (m1 * ∫ ξ, gwt ξ * ‖PolySum Y (t + 2 * Real.pi * ξ)‖ ^ 2)) := by
        ring

/-- **The positive half reflection bound.**  Combining the reflection lemma `hrefl`
(GM Lemma 6.2 in `L¹` form) with Cauchy–Schwarz (`refl_sq_le`) for the finite block and the
decay tail `hdec` for the infinite remainder, the whole positive half `Spos N t` of the
pair sum is bounded by the reflected Dirichlet polynomial, plus the truncation error. -/
theorem pos_half_reflection
    (hrefl : Work.GM.S2.ReflHyp) (hdec : Work.GM.S2.DecHyp)
    (j : ℕ) (hj : 2 ≤ j) (m1 : ℝ) (hm1 : 0 ≤ m1)
    (hgwt : MeasureTheory.Integrable Work.GM.S2.gwt)
    (hmass : (∫ ξ, Work.GM.S2.gwt ξ) ≤ m1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ), 1 ≤ N → ∀ (t Y : ℝ), 1 ≤ |t| → 1 ≤ Y →
      ‖Work.GM.S2.Spos N t‖ ^ 2
        ≤ C * ((1 + |t|)⁻¹ * (m1 * ∫ ξ, Work.GM.S2.gwt ξ * ‖Work.GM.S2.PolySum Y (t + 2 * Real.pi * ξ)‖ ^ 2)
          + ((1 + |t|) ^ j / ((N : ℝ) ^ j * Y ^ (j - 1))) ^ 2) := by
  obtain ⟨Ccs, hCcspos, hcs⟩ := refl_sq_le hrefl m1 hm1 hgwt hmass
  obtain ⟨Ctl, hCtlpos, hsumm, htail⟩ := tail_nat_hhat hdec j hj
  refine ⟨1 + 2 * Ccs + 2 * Ctl ^ 2, by positivity, fun N hN t Y ht hY => ?_⟩
  -- the finite block and the tail of the positive half
  have hsum : Summable (fun k : ℕ => Submission.GM.hhat t (((k + 1 : ℕ) : ℝ) * (N : ℝ))) :=
    (hsumm N hN t).of_norm
  have hshnorm : Summable
      (fun k : ℕ => ‖Submission.GM.hhat t (((k + Nat.floor Y + 1 : ℕ) : ℝ) * (N : ℝ))‖) := by
    have h := (summable_nat_add_iff (Nat.floor Y)).mpr (hsumm N hN t)
    simpa only [Nat.add_assoc] using h
  rw [Spos_split N t Y hsum]
  set A : ℂ := ∑ m ∈ Finset.Icc 1 (Nat.floor Y), Submission.GM.hhat t ((m : ℝ) * (N : ℝ)) with hAdef
  set B : ℂ := ∑' k : ℕ, Submission.GM.hhat t (((k + Nat.floor Y + 1 : ℕ) : ℝ) * (N : ℝ)) with hBdef
  set P : ℝ := (1 + |t|)⁻¹ * (m1 * ∫ ξ, gwt ξ * ‖PolySum Y (t + 2 * Real.pi * ξ)‖ ^ 2) with hPdef
  set Q : ℝ := (1 + |t|) ^ j / ((N : ℝ) ^ j * Y ^ (j - 1)) with hQdef
  have hAcs : ‖A‖ ^ 2 ≤ Ccs * P := hcs N hN t Y ht hY
  have hBcs : ‖B‖ ^ 2 ≤ Ctl ^ 2 * Q ^ 2 := by
    have h : ‖B‖ ≤ Ctl * Q := by
      rw [hQdef]
      have h' := le_trans (norm_tsum_le_tsum_norm hshnorm) (htail N hN t Y ht hY)
      rwa [mul_div_assoc] at h'
    have h2 := pow_le_pow_left₀ (norm_nonneg B) h 2
    rwa [mul_pow] at h2
  have hPnn : 0 ≤ P := by
    rw [hPdef]
    exact mul_nonneg (by positivity)
      (mul_nonneg hm1 (integral_nonneg (fun ξ => mul_nonneg (gwt_nonneg ξ) (sq_nonneg _))))
  have hQnn : 0 ≤ Q := by
    rw [hQdef]
    apply div_nonneg
    · positivity
    · have h1 : (1 : ℝ) ≤ Y ^ (j - 1) := one_le_pow₀ hY
      positivity
  have hCcsP : 0 ≤ 2 * Ccs * P := mul_nonneg (by linarith) hPnn
  have hCtlQ : 0 ≤ 2 * Ctl ^ 2 * P := mul_nonneg (by positivity) hPnn
  have hCcsQ : 0 ≤ 2 * Ccs * Q ^ 2 := mul_nonneg (by linarith) (sq_nonneg Q)
  have hCtlQ2 : 0 ≤ 2 * Ctl ^ 2 * Q ^ 2 := mul_nonneg (by positivity) (sq_nonneg Q)
  have htwo : (‖A‖ + ‖B‖) ^ 2 ≤ 2 * ‖A‖ ^ 2 + 2 * ‖B‖ ^ 2 := by
    nlinarith [sq_nonneg (‖A‖ - ‖B‖)]
  have hfin : 2 * ‖A‖ ^ 2 + 2 * ‖B‖ ^ 2 ≤ (1 + 2 * Ccs + 2 * Ctl ^ 2) * (P + Q ^ 2) := by
    have h1 : 2 * ‖A‖ ^ 2 ≤ 2 * Ccs * P := by linarith
    have h2 : 2 * ‖B‖ ^ 2 ≤ 2 * Ctl ^ 2 * Q ^ 2 := by linarith
    have hexp : (1 + 2 * Ccs + 2 * Ctl ^ 2) * (P + Q ^ 2)
        = P + Q ^ 2 + 2 * Ccs * P + 2 * Ccs * Q ^ 2 + 2 * Ctl ^ 2 * P
          + 2 * Ctl ^ 2 * Q ^ 2 := by ring
    rw [hexp]
    linarith [h1, h2, hPnn, sq_nonneg Q, hCcsP, hCtlQ, hCcsQ, hCtlQ2]
  calc ‖A + B‖ ^ 2 ≤ (‖A‖ + ‖B‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_add_le A B) 2
    _ ≤ 2 * ‖A‖ ^ 2 + 2 * ‖B‖ ^ 2 := htwo
    _ ≤ (1 + 2 * Ccs + 2 * Ctl ^ 2) * (P + Q ^ 2) := hfin

end Work.GM.S2
