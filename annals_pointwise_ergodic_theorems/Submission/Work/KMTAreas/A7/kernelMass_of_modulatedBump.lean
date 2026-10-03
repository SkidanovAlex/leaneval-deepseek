import Mathlib
import Submission.Work.KMTAreas.A7.Tle_varphiNt_single_scale

set_option maxHeartbeats 8000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Finset
open scoped ENNReal NNReal BigOperators FourierTransform
open Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier

local notation "Circ" => Work.Analysis.IonescuWainger.Circle

/-! ## Elementary inequalities for the pointwise majorant -/
/-- `min u w ≤ 2uw/(u+w)` for positive `u, w` (twice the harmonic mean dominates the minimum). -/
private lemma min_le_two_mul_div_add {u w : ℝ} (hu : 0 < u) (hw : 0 < w) :
    min u w ≤ 2 * u * w / (u + w) := by
  have hden : 0 < u + w := by linarith
  rcases le_total u w with hle | hle
  · rw [min_eq_left hle, le_div_iff₀ hden]
    nlinarith [hle, hu]
  · rw [min_eq_right hle, le_div_iff₀ hden]
    nlinarith [hle, hw]

/-- `min u (v/t²) ≤ 2u/(1 + (u/v)t²)`: the minimum of the `L¹`-bound `u` and the decay bound
`v/t²` is at most twice their harmonic mean.  No hypothesis on `t` is needed (the convention
`v/0 = 0` is harmless because the right-hand side is then positive). -/
private lemma min_le_harmonic {u v t : ℝ} (hu : 0 < u) (hv : 0 < v) :
    min u (v / t ^ 2) ≤ 2 * u * v / (u * t ^ 2 + v) := by
  rcases eq_or_ne t 0 with h0 | h0
  · subst h0
    have hL : min u (v / (0 : ℝ) ^ 2) = 0 := by
      rw [zero_pow (by norm_num : (2 : ℕ) ≠ 0), div_zero, min_eq_right (le_of_lt hu)]
    have hR : (0 : ℝ) < 2 * u * v / (u * (0 : ℝ) ^ 2 + v) := by
      rw [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, zero_add]
      positivity
    rw [hL]
    exact le_of_lt hR
  · have ht2 : 0 < t ^ 2 := by positivity
    have hw : 0 < v / t ^ 2 := div_pos hv ht2
    have hden : u + v / t ^ 2 = (u * t ^ 2 + v) / t ^ 2 := by
      rw [add_div, mul_div_cancel_right₀ _ (ne_of_gt ht2)]
    have hcancel : v / t ^ 2 * t ^ 2 = v := div_mul_cancel₀ v (ne_of_gt ht2)
    have hid : 2 * u * (v / t ^ 2) / (u + v / t ^ 2) = 2 * u * v / (u * t ^ 2 + v) := by
      rw [hden, div_div_eq_mul_div, mul_assoc, hcancel]
    rw [← hid]
    exact min_le_two_mul_div_add hu hw

/-! ## §3. The `ℓ¹` mass of the kernel of the modulated narrow bump -/

/-! ## The `ℓ¹` mass of the kernel of the modulated narrow bump (the requested lemma) -/

theorem kernelMass_of_modulatedBump (A : Finset Work.Analysis.IonescuWainger.Circle) (φ : ℝ → ℂ)
    (c a A₀ B₀ : ℝ)
    (hφcd : ContDiff ℝ 2 φ) (hφcs : HasCompactSupport φ) (ha1 : 1 ≤ a)
    (hA₀ : 0 ≤ A₀) (hB₀ : 0 ≤ B₀)
    (h1 : (∫ y : ℝ, ‖φ y‖) ≤ A₀ / a)
    (h2 : (∫ y : ℝ, ‖iteratedDeriv 2 φ y‖) ≤ B₀ * a) :
    Summable (fun j : ℤ => ‖Work.Analysis.IWMultiplier.iwKernel
        (Work.Analysis.IonescuWainger.iwSymbolSet A
          (Work.Analysis.IonescuWainger.periodize
            (fun y : ℝ => φ y * Work.KMTAreas.A7.ee (c * y)))) j‖) ∧
    (∑' j : ℤ, ‖Work.Analysis.IWMultiplier.iwKernel
        (Work.Analysis.IonescuWainger.iwSymbolSet A
          (Work.Analysis.IonescuWainger.periodize
            (fun y : ℝ => φ y * Work.KMTAreas.A7.ee (c * y)))) j‖)
      ≤ 4 * ((A.card : ℝ) * A₀ + 1)
        + 2 * Real.pi * Real.sqrt (((A.card : ℝ) * A₀ + 1)
            * ((A.card : ℝ) * B₀ / (4 * Real.pi ^ 2) + 1)) := by
  set cc : ℝ := (A.card : ℝ) with hcc
  have hcc0 : 0 ≤ cc := by rw [hcc]; exact Nat.cast_nonneg _
  set P : ℝ := cc * A₀ + 1 with hP
  set Q : ℝ := cc * B₀ / (4 * Real.pi ^ 2) with hQ
  have hP0 : 0 < P := by rw [hP]; nlinarith
  have hQ0 : 0 ≤ Q := by rw [hQ]; positivity
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha1
  have ha_ne : a ≠ 0 := ne_of_gt ha0
  set aα : Circ → ℝ := fun α => (AddCircle.equivIco (1 : ℝ) 0 α).val with haα
  set F : ℝ → ℂ := fun y => φ y * ee (c * y) with hF
  have hFcd : ContDiff ℝ 2 F := by
    rw [hF]; exact hφcd.mul (contDiff_ee_const_mul 2 c)
  have hFcs : HasCompactSupport F := by
    rw [hF]; exact HasCompactSupport.mul_right hφcs
  set H : ℝ → ℂ := fun y => ∑ α ∈ A, ee (-(c * aα α)) * φ (y - aα α) with hH
  have hHcd : ContDiff ℝ 2 H := by
    rw [hH]
    exact ContDiff.sum (fun α _ => contDiff_const.mul (hφcd.comp (contDiff_id.sub contDiff_const)))
  have hφ_int : Integrable φ := hφcd.continuous.integrable_of_hasCompactSupport hφcs
  have hiter_int : ∀ n : ℕ, n ≤ 2 → Integrable (fun y : ℝ => ‖iteratedDeriv n φ y‖) := by
    intro n hn
    have hcont : Continuous (iteratedDeriv n φ) :=
      hφcd.continuous_iteratedDeriv n (by exact_mod_cast hn)
    have hcs : HasCompactSupport (iteratedDeriv n φ) := by
      interval_cases n
      · rw [iteratedDeriv_zero]; exact hφcs
      · rw [iteratedDeriv_one]; exact hφcs.deriv
      · rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
        exact hφcs.deriv.deriv
    exact (hcont.integrable_of_hasCompactSupport hcs).norm
  have hH_int : Integrable H := by
    rw [hH]
    exact integrable_finsetSum _ (fun α _ => (hφ_int.comp_sub_right (aα α)).const_mul _)
  have hG : ∀ y : ℝ, (∑ α ∈ A, F (y - aα α)) = H y * ee (c * y) := by
    intro y
    rw [hH, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun α _ => ?_)
    show φ (y - aα α) * ee (c * (y - aα α))
      = (ee (-(c * aα α)) * φ (y - aα α)) * ee (c * y)
    have harg : c * (y - aα α) = -(c * aα α) + c * y := by ring
    rw [harg, ← ee_add_]
    ring
  have hderiv : ∀ (n : ℕ), (n : ℕ∞) ≤ (2 : ℕ∞) → ∀ y : ℝ,
      iteratedDeriv n H y = ∑ α ∈ A, ee (-(c * aα α)) * iteratedDeriv n φ (y - aα α) := by
    intro n hn y
    have hn2 : n ≤ 2 := by exact_mod_cast hn
    have hφn : ContDiff ℝ n φ := hφcd.of_le (by exact_mod_cast hn2)
    have hfuns : (∑ α ∈ A, fun y : ℝ => ee (-(c * aα α)) * φ (y - aα α))
        = fun y : ℝ => ∑ α ∈ A, ee (-(c * aα α)) * φ (y - aα α) := by
      funext z
      rw [Finset.sum_apply]
    rw [hH, ← hfuns, iteratedDeriv_sum]
    · refine Finset.sum_congr rfl (fun α _ => ?_)
      rw [iteratedDeriv_const_mul]
      · rw [congrFun (iteratedDeriv_comp_sub_const n φ (aα α)) y]
      · exact (hφn.comp (contDiff_id.sub contDiff_const)).contDiffAt
    · intro α _
      exact (contDiff_const.mul (hφn.comp (contDiff_id.sub contDiff_const))).contDiffAt
  have hpt2 : ∀ y : ℝ, ‖iteratedDeriv 2 H y‖ ≤ ∑ α ∈ A, ‖iteratedDeriv 2 φ (y - aα α)‖ := by
    intro y
    rw [hderiv 2 le_rfl y]
    calc ‖∑ α ∈ A, ee (-(c * aα α)) * iteratedDeriv 2 φ (y - aα α)‖
        ≤ ∑ α ∈ A, ‖ee (-(c * aα α)) * iteratedDeriv 2 φ (y - aα α)‖ := norm_sum_le _ _
      _ ≤ ∑ α ∈ A, ‖iteratedDeriv 2 φ (y - aα α)‖ := by
          refine Finset.sum_le_sum (fun α _ => ?_)
          rw [norm_mul, norm_ee_, one_mul]
  have hdom2 : Integrable (fun y : ℝ => ∑ α ∈ A, ‖iteratedDeriv 2 φ (y - aα α)‖) :=
    integrable_finsetSum _ (fun α _ => (hiter_int 2 le_rfl).comp_sub_right (aα α))
  have hH2_int : Integrable (fun y : ℝ => iteratedDeriv 2 H y) := by
    have hcont : Continuous (iteratedDeriv 2 H) := hHcd.continuous_iteratedDeriv 2 le_rfl
    exact Integrable.mono' hdom2 hcont.aestronglyMeasurable
      (Filter.Eventually.of_forall hpt2)
  have hpt0 : ∀ y : ℝ, ‖H y‖ ≤ ∑ α ∈ A, ‖φ (y - aα α)‖ := by
    intro y
    rw [hH]
    calc ‖∑ α ∈ A, ee (-(c * aα α)) * φ (y - aα α)‖
        ≤ ∑ α ∈ A, ‖ee (-(c * aα α)) * φ (y - aα α)‖ := norm_sum_le _ _
      _ ≤ ∑ α ∈ A, ‖φ (y - aα α)‖ := by
          refine Finset.sum_le_sum (fun α _ => ?_)
          rw [norm_mul, norm_ee_, one_mul]
  have hdom0 : Integrable (fun y : ℝ => ∑ α ∈ A, ‖φ (y - aα α)‖) :=
    integrable_finsetSum _ (fun α _ => (hφ_int.comp_sub_right (aα α)).norm)
  have hIntH : (∫ y : ℝ, ‖H y‖) ≤ cc * (∫ y : ℝ, ‖φ y‖) := by
    calc (∫ y : ℝ, ‖H y‖) ≤ ∫ y : ℝ, ∑ α ∈ A, ‖φ (y - aα α)‖ :=
          integral_mono hH_int.norm hdom0 hpt0
      _ = ∑ α ∈ A, ∫ y : ℝ, ‖φ (y - aα α)‖ :=
          integral_finsetSum _ (fun α _ => (hφ_int.comp_sub_right (aα α)).norm)
      _ = ∑ α ∈ A, ∫ y : ℝ, ‖φ y‖ := by
          refine Finset.sum_congr rfl (fun α _ => ?_)
          exact integral_sub_right_eq_self (fun y : ℝ => ‖φ y‖) (aα α)
      _ = cc * ∫ y : ℝ, ‖φ y‖ := by
          rw [Finset.sum_const, nsmul_eq_mul, hcc]
  have hIntH2 : (∫ y : ℝ, ‖iteratedDeriv 2 H y‖) ≤ cc * (∫ y : ℝ, ‖iteratedDeriv 2 φ y‖) := by
    calc (∫ y : ℝ, ‖iteratedDeriv 2 H y‖)
        ≤ ∫ y : ℝ, ∑ α ∈ A, ‖iteratedDeriv 2 φ (y - aα α)‖ :=
          integral_mono hH2_int.norm hdom2 hpt2
      _ = ∑ α ∈ A, ∫ y : ℝ, ‖iteratedDeriv 2 φ (y - aα α)‖ :=
          integral_finsetSum _ (fun α _ => (hiter_int 2 le_rfl).comp_sub_right (aα α))
      _ = ∑ α ∈ A, ∫ y : ℝ, ‖iteratedDeriv 2 φ y‖ := by
          refine Finset.sum_congr rfl (fun α _ => ?_)
          exact integral_sub_right_eq_self (fun y : ℝ => ‖iteratedDeriv 2 φ y‖) (aα α)
      _ = cc * ∫ y : ℝ, ‖iteratedDeriv 2 φ y‖ := by
          rw [Finset.sum_const, nsmul_eq_mul, hcc]
  have hH_int_all : ∀ n : ℕ, (n : ℕ∞) ≤ (2 : ℕ∞) → Integrable (iteratedDeriv n H) := by
    intro n hn
    have hn2 : n ≤ 2 := by exact_mod_cast hn
    have hcont : Continuous (iteratedDeriv n H) :=
      hHcd.continuous_iteratedDeriv n (by exact_mod_cast hn)
    have hdom : Integrable (fun y : ℝ => ∑ α ∈ A, ‖iteratedDeriv n φ (y - aα α)‖) :=
      integrable_finsetSum _ (fun α _ => (hiter_int n hn2).comp_sub_right (aα α))
    refine Integrable.mono' hdom hcont.aestronglyMeasurable (Filter.Eventually.of_forall ?_)
    intro y
    rw [hderiv n hn y]
    calc ‖∑ α ∈ A, ee (-(c * aα α)) * iteratedDeriv n φ (y - aα α)‖
        ≤ ∑ α ∈ A, ‖ee (-(c * aα α)) * iteratedDeriv n φ (y - aα α)‖ := norm_sum_le _ _
      _ ≤ ∑ α ∈ A, ‖iteratedDeriv n φ (y - aα α)‖ := by
          refine Finset.sum_le_sum (fun α _ => ?_)
          rw [norm_mul, norm_ee_, one_mul]
  have hker : ∀ j : ℤ, iwKernel (iwSymbolSet A (periodize F)) j = 𝓕 H ((j : ℝ) - c) := by
    intro j
    rw [Work.KMTPlan.A6.iwKernel_periodize_fourier A hFcd.continuous hFcs j]
    rw [funext hG]
    exact fourier_mul_ee H c (j : ℝ)
  have hb1 : ∀ x : ℝ, ‖𝓕 H x‖ ≤ (∫ y : ℝ, ‖H y‖) :=
    fun x => VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
  have hb2 : ∀ x : ℝ, x ≠ 0 →
      ‖𝓕 H x‖ ≤ (∫ y : ℝ, ‖iteratedDeriv 2 H y‖) / (2 * Real.pi * |x|) ^ 2 := by
    intro x hx
    have hF2 := Real.fourier_iteratedDeriv (f := H) (N := 2) (n := 2) hHcd hH_int_all
      (by norm_num)
    have hpt := congrFun hF2 x
    have hnorm : ‖𝓕 (iteratedDeriv 2 H) x‖ = (2 * Real.pi * |x|) ^ 2 * ‖𝓕 H x‖ := by
      rw [hpt, norm_smul, norm_pow]
      congr 1
      have hc1 : ‖(2 : ℂ)‖ = 2 := by norm_num
      have hc2 : ‖(Real.pi : ℂ)‖ = |Real.pi| := RCLike.norm_ofReal Real.pi
      have hc3 : ‖((x : ℝ) : ℂ)‖ = |x| := RCLike.norm_ofReal x
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, mul_one, hc1, hc2, hc3,
        abs_of_nonneg Real.pi_pos.le]
    have hbdd : ‖𝓕 (iteratedDeriv 2 H) x‖ ≤ (∫ y : ℝ, ‖iteratedDeriv 2 H y‖) :=
      VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
    have hden : 0 < (2 * Real.pi * |x|) ^ 2 := by
      have hxpos : 0 < |x| := abs_pos.mpr hx
      positivity
    rw [le_div_iff₀ hden, mul_comm, ← hnorm]
    exact hbdd
  set A' : ℝ := (∫ y : ℝ, ‖H y‖) + 1 / a with hA'
  set B' : ℝ := (∫ y : ℝ, ‖iteratedDeriv 2 H y‖) / (4 * Real.pi ^ 2) + 1 / a with hB'
  have hA'pos : 0 < A' := by rw [hA']; positivity
  have hB'pos : 0 < B' := by rw [hB']; positivity
  set s : ℝ := Real.sqrt (A' / B') with hs
  have hspos : 0 < s := Real.sqrt_pos.mpr (div_pos hA'pos hB'pos)
  have hs2 : s ^ 2 = A' / B' := Real.sq_sqrt (le_of_lt (div_pos hA'pos hB'pos))
  have hid : ∀ x : ℝ, 2 * A' * B' / (A' * x ^ 2 + B')
      = 2 * A' * (1 / (1 + (s * x) ^ 2)) := by
    intro x
    have hB'ne : B' ≠ 0 := ne_of_gt hB'pos
    have hden : (1 : ℝ) + (s * x) ^ 2 = (A' * x ^ 2 + B') / B' := by
      rw [mul_pow, hs2]
      field_simp
      try ring
    rw [hden, one_div_div, mul_div_assoc]
  have hpt_bound : ∀ j : ℤ,
      ‖iwKernel (iwSymbolSet A (periodize F)) j‖ ≤ 2 * A' / (1 + (s * ((j : ℝ) - c)) ^ 2) := by
    intro j
    rw [hker j]
    rcases eq_or_ne ((j : ℝ) - c) 0 with h0 | h0
    · rw [h0]
      have hb := hb1 0
      have hInt_nn : (0 : ℝ) ≤ ∫ y : ℝ, ‖H y‖ := integral_nonneg (fun y => norm_nonneg _)
      have hd : 2 * A' / (1 + (s * (0:ℝ)) ^ 2) = 2 * A' := by
        rw [mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero, div_one]
      rw [hd, hA']
      linarith [hb, hInt_nn, one_div_pos.mpr ha0]
    · have hA'ub : ‖𝓕 H ((j : ℝ) - c)‖ ≤ A' := by
        have hb := hb1 ((j : ℝ) - c)
        rw [hA']
        linarith [hb, one_div_pos.mpr ha0]
      have hB'ub : ‖𝓕 H ((j : ℝ) - c)‖ ≤ B' / ((j : ℝ) - c) ^ 2 := by
        have hb := hb2 ((j : ℝ) - c) h0
        have hden : (2 * Real.pi * |(j : ℝ) - c|) ^ 2
            = 4 * Real.pi ^ 2 * ((j : ℝ) - c) ^ 2 := by
          rw [mul_pow, sq_abs]
          ring
        rw [hden] at hb
        rw [hB']
        calc ‖𝓕 H ((j : ℝ) - c)‖
            ≤ (∫ y : ℝ, ‖iteratedDeriv 2 H y‖)
                / (4 * Real.pi ^ 2 * ((j : ℝ) - c) ^ 2) := hb
          _ = ((∫ y : ℝ, ‖iteratedDeriv 2 H y‖) / (4 * Real.pi ^ 2))
                / ((j : ℝ) - c) ^ 2 := by rw [div_div]
          _ ≤ ((∫ y : ℝ, ‖iteratedDeriv 2 H y‖) / (4 * Real.pi ^ 2) + 1 / a)
                / ((j : ℝ) - c) ^ 2 := by
              refine div_le_div_of_nonneg_right ?_ (by positivity)
              exact le_add_of_nonneg_right (by positivity)
      have hmin := min_le_harmonic hA'pos hB'pos (u := A') (v := B') (t := (j : ℝ) - c)
      refine le_trans (le_min hA'ub hB'ub) ?_
      exact le_trans hmin (le_of_eq (by rw [hid ((j : ℝ) - c), mul_one_div]))
  have hmaj_summ : Summable (fun j : ℤ => 2 * A' / (1 + (s * ((j : ℝ) - c)) ^ 2)) := by
    have hbase := (tsum_one_div_one_add_sq_mul_le s hspos c).1
    simpa only [mul_one_div] using hbase.mul_left (2 * A')
  have hsumm_kern : Summable (fun j : ℤ => ‖iwKernel (iwSymbolSet A (periodize F)) j‖) :=
    Summable.of_nonneg_of_le (fun j => norm_nonneg _) hpt_bound hmaj_summ
  have hsum_le : (∑' j : ℤ, ‖iwKernel (iwSymbolSet A (periodize F)) j‖)
      ≤ ∑' j : ℤ, 2 * A' / (1 + (s * ((j : ℝ) - c)) ^ 2) :=
    Summable.tsum_le_tsum hpt_bound hsumm_kern hmaj_summ
  have hmaj_val : (∑' j : ℤ, 2 * A' / (1 + (s * ((j : ℝ) - c)) ^ 2))
      ≤ 2 * A' * (2 + Real.pi / s) := by
    have h := (tsum_one_div_one_add_sq_mul_le s hspos c).2
    calc (∑' j : ℤ, 2 * A' / (1 + (s * ((j : ℝ) - c)) ^ 2))
        = 2 * A' * ∑' j : ℤ, 1 / (1 + (s * ((j : ℝ) - c)) ^ 2) := by
          rw [← tsum_mul_left]
          exact tsum_congr (fun j => by rw [mul_one_div])
      _ ≤ 2 * A' * (2 + Real.pi / s) := mul_le_mul_of_nonneg_left h (by positivity)
  have hAs : A' / s = Real.sqrt (A' * B') := by
    have hsq : (A' / s) ^ 2 = A' * B' := by
      rw [div_pow, hs2]
      first | (field_simp; ring) | field_simp | ring_nf
    rw [← hsq, Real.sqrt_sq (by positivity)]
  have hfinal_le : (∑' j : ℤ, ‖iwKernel (iwSymbolSet A (periodize F)) j‖)
      ≤ 4 * A' + 2 * Real.pi * Real.sqrt (A' * B') := by
    calc (∑' j : ℤ, ‖iwKernel (iwSymbolSet A (periodize F)) j‖)
        ≤ 2 * A' * (2 + Real.pi / s) := le_trans hsum_le hmaj_val
      _ = 4 * A' + 2 * Real.pi * (A' / s) := by ring_nf
      _ = 4 * A' + 2 * Real.pi * Real.sqrt (A' * B') := by rw [hAs]
  have hA'le : A' ≤ P / a := by
    rw [hA', hP, add_div]
    have hInt : (∫ y : ℝ, ‖H y‖) ≤ cc * (A₀ / a) :=
      le_trans hIntH (mul_le_mul_of_nonneg_left h1 hcc0)
    rw [mul_div] at hInt
    linarith [hInt]
  have hB'le : B' ≤ Q * a + 1 / a := by
    rw [hB', hQ]
    have hInt : (∫ y : ℝ, ‖iteratedDeriv 2 H y‖) ≤ cc * (B₀ * a) :=
      le_trans hIntH2 (mul_le_mul_of_nonneg_left h2 hcc0)
    have hrew : cc * B₀ / (4 * Real.pi ^ 2) * a = cc * (B₀ * a) / (4 * Real.pi ^ 2) := by
      ring_nf
    rw [hrew]
    have hstep : (∫ y : ℝ, ‖iteratedDeriv 2 H y‖) / (4 * Real.pi ^ 2)
        ≤ cc * (B₀ * a) / (4 * Real.pi ^ 2) :=
      div_le_div_of_nonneg_right hInt (by positivity)
    linarith
  have hprod : A' * B' ≤ P * (Q + 1) := by
    have h1' : A' * B' ≤ (P / a) * (Q * a + 1 / a) :=
      mul_le_mul hA'le hB'le (le_of_lt hB'pos) (by rw [hP]; positivity)
    have heq : (P / a) * (Q * a + 1 / a) = P * Q + P / a ^ 2 := by
      first | (field_simp; ring) | field_simp | ring_nf
    have hle : P / a ^ 2 ≤ P := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < a ^ 2)]
      have ha2 : 1 ≤ a ^ 2 := by nlinarith
      nlinarith [hP0.le, ha2]
    have hdist : P * (Q + 1) = P * Q + P := by ring
    rw [hdist]
    linarith [h1', le_of_eq heq, hle]
  have hA'P : A' ≤ P := by
    refine le_trans hA'le ?_
    rw [div_le_iff₀ ha0]
    nlinarith [hP0.le, ha1]
  have hmain : (∑' j : ℤ, ‖iwKernel (iwSymbolSet A (periodize F)) j‖)
      ≤ 4 * P + 2 * Real.pi * Real.sqrt (P * (Q + 1)) := by
    refine le_trans hfinal_le ?_
    have hsq : Real.sqrt (A' * B') ≤ Real.sqrt (P * (Q + 1)) := Real.sqrt_le_sqrt hprod
    have h4 : 4 * A' ≤ 4 * P := by linarith
    have h2' : 2 * Real.pi * Real.sqrt (A' * B')
        ≤ 2 * Real.pi * Real.sqrt (P * (Q + 1)) :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    exact add_le_add h4 h2'
  have hconv : 4 * P + 2 * Real.pi * Real.sqrt (P * (Q + 1))
      = 4 * ((A.card : ℝ) * A₀ + 1)
        + 2 * Real.pi * Real.sqrt (((A.card : ℝ) * A₀ + 1)
            * ((A.card : ℝ) * B₀ / (4 * Real.pi ^ 2) + 1)) := by
    rw [hP, hQ, hcc]
  rw [hconv] at hmain
  exact ⟨hsumm_kern, hmain⟩

end

end Work.KMTAreas.A7
