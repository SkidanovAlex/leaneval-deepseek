import Mathlib
import Submission.Work.Maximal.mstWideLat_defs
import Submission.Work.Maximal.mstWideLat_integrable
import Submission.Work.Maximal.mstWideLat_fourier_support
import Submission.Work.Maximal.mstWideLat_continuous
import Submission.Work.BourgainPlan.Maximal.mstMaximal_single

namespace Work.Maximal

open MeasureTheory Finset
open scoped BigOperators ENNReal

noncomputable section

theorem wideLat_class_bound (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (χ : ℝ) (η : ℝ → ℂ)
    (s : ℕ) (F : ℤ → ℂ) (T : Finset ℤ) (hF : Memℓp F 2)
    (hηc : ContDiff ℝ 2 η) (hηsup : ∀ x : ℝ, 1 / 2 < |x| → η x = 0)
    {r : ℝ} (hr : 1 < r) (hr2 : r < 2)
    (K : ℝ) (hK : 0 < K) (Tc : Finset ℝ)
    (hTc : ∀ (n : ℕ) (ψ : ℝ → ENNReal), Measurable ψ → ∀ x : ℝ,
      ∫⁻ u in Set.Ioc 0 1, ψ (x - Polynomial.eval (2 ^ n * u) (Polynomial.map (Int.castRingHom ℝ) P))
        ≤ ENNReal.ofReal K * ∑ c ∈ Tc, Commons.Analysis.Maximal.hlMax ψ (x - c))
    (A : ℕ → MeasureTheory.Lp ℂ ⊤ (AddCircle.haarAddCircle (T := 1)))
    (hcurve : ∀ (k : ℕ) (n : ℤ), ‖Work.BourgainPlan.IonescuWainger.opMul (A k) F hF n‖ₑ ≤
      ∫⁻ u in Set.Ioc (0:ℝ) 1, ‖Work.Maximal.mstWideLat P χ η s F T
        (-(n : ℝ) - Polynomial.eval (((2 : ℝ) ^ k) * u)
          (Polynomial.map (Int.castRingHom ℝ) P))‖ₑ)
    (C_lat : ℝ) (hC_lat : 0 < C_lat)
    (hlattice : ∀ (H : ℝ → ℂ) (δ : ℝ), 0 < δ → MeasureTheory.Integrable H →
      (∀ ξ : ℝ, δ < |ξ| → FourierTransform.fourier H ξ = 0) →
      ∀ (Q : ℕ), 1 ≤ Q → δ * (Q : ℝ) ≤ 1 / 4 → ∀ (m : ℤ) (c : ℝ),
        (∑' x : ℤ, (Work.Maximal.mstHlMax (fun y : ℝ => ENNReal.ofReal ‖H y‖)
            ((Q : ℝ) * (x : ℝ) + (m : ℝ) - c)) ^ r)
          ≤ ENNReal.ofReal (C_lat ^ r) *
            ∑' x : ℤ, ENNReal.ofReal (‖H ((Q : ℝ) * (x : ℝ) + (m : ℝ))‖ ^ r))
    (V : ℤ → ℂ) (hvals : ∀ j : ℤ, Work.Maximal.mstWideLat P χ η s F T (j : ℝ) = V (-j))
    (Q : ℕ) (hQ1 : 1 ≤ Q) (hδQ : (1 / (2 * Work.Maximal.mstWideC P s)) * (Q : ℝ) ≤ 1 / 4) (m : ℤ) :
    ∫⁻ x : ℤ, (⨆ k : ℕ,
        ‖Work.BourgainPlan.IonescuWainger.opMul (A k) F hF ((Q : ℤ) * x + m)‖ₑ) ^ r
        ∂MeasureTheory.Measure.count
      ≤ ENNReal.ofReal ((K * (Tc.card : ℝ) * C_lat) ^ r * (Tc.card : ℝ)) *
          ∫⁻ x : ℤ, ENNReal.ofReal (‖V ((Q : ℤ) * x + m)‖ ^ r)
            ∂MeasureTheory.Measure.count := by
  classical
  -- ## Abbreviations
  set H : ℝ → ℂ := mstWideLat P χ η s F T with hH
  set ψ : ℝ → ENNReal := fun y => ‖H y‖ₑ with hψ
  set I : ENNReal := ∫⁻ x : ℤ, ENNReal.ofReal (‖V ((Q : ℤ) * x + m)‖ ^ r)
      ∂MeasureTheory.Measure.count with hI
  have hHint : Integrable H := by
    rw [hH]; exact mstWideLat_integrable P χ η s F T hηc hηsup
  have hHfour : ∀ ξ : ℝ, 1 / (2 * mstWideC P s) < |ξ| →
      FourierTransform.fourier H ξ = 0 := by
    intro ξ hξ
    rw [hH]; exact mstWideLat_fourier_support P χ η s F T hηc hηsup ξ hξ
  have hHcont : Continuous H := by
    rw [hH]; exact mstWideLat_continuous P χ η s F T hηc hηsup
  have hψmeas : Measurable ψ := by
    rw [hψ]; exact hHcont.enorm.measurable
  have hψeq : (fun y : ℝ => ENNReal.ofReal ‖H y‖) = ψ := by
    rw [hψ]; funext y; exact ofReal_norm (H y)
  have hδpos : 0 < 1 / (2 * mstWideC P s) := by
    have h1 : (0:ℝ) < mstWideC P s := lt_of_lt_of_le zero_lt_one (one_le_mstWideC P s)
    positivity
  have hTcne : Tc.Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    have h1 := hTc 0 (fun _ : ℝ => (1 : ENNReal)) measurable_const 0
    rw [hne] at h1
    simp only [Finset.sum_empty, mul_zero] at h1
    rw [MeasureTheory.setLIntegral_one, Real.volume_Ioc] at h1
    norm_num at h1
  have hN1 : 1 ≤ (Tc.card : ENNReal) := by
    have h2 : 1 ≤ Tc.card := Finset.card_pos.mpr hTcne
    exact_mod_cast h2
  have hr0 : (0:ℝ) ≤ r := by linarith
  have hNr : (Tc.card : ENNReal) ^ (r - 1) ≤ (Tc.card : ENNReal) ^ r :=
    ENNReal.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  -- ## The pointwise supremum bound
  have hsup_le : ∀ x : ℤ, (⨆ k : ℕ, ‖Work.BourgainPlan.IonescuWainger.opMul (A k) F hF ((Q : ℤ) * x + m)‖ₑ)
      ≤ ENNReal.ofReal K * ∑ c ∈ Tc,
          mstHlMax ψ (-((((Q : ℤ) * x + m : ℤ)) : ℝ) - c) := by
    intro x
    refine iSup_le (fun k => ?_)
    have h1 := hcurve k ((Q : ℤ) * x + m)
    have h2 := hTc k ψ hψmeas (-((((Q : ℤ) * x + m : ℤ)) : ℝ))
    have hbridge : (∫⁻ u in Set.Ioc (0:ℝ) 1, ‖H (-((((Q : ℤ) * x + m : ℤ)) : ℝ)
          - Polynomial.eval (((2 : ℝ) ^ k) * u) (Polynomial.map (Int.castRingHom ℝ) P))‖ₑ)
        = ∫⁻ u in Set.Ioc (0:ℝ) 1, ψ (-((((Q : ℤ) * x + m : ℤ)) : ℝ)
          - Polynomial.eval (((2 : ℝ) ^ k) * u) (Polynomial.map (Int.castRingHom ℝ) P)) := by
      refine lintegral_congr (fun u => ?_)
      simp only [hψ]
    exact le_trans h1 (le_trans (le_of_eq hbridge) h2)
  -- ## Splitting off the constant, and the powers-mean inequality
  have hsplit : (∫⁻ x : ℤ, (ENNReal.ofReal K * ∑ c ∈ Tc,
          mstHlMax ψ (-((((Q : ℤ) * x + m : ℤ)) : ℝ) - c)) ^ r
          ∂MeasureTheory.Measure.count)
      = ENNReal.ofReal (K ^ r) * ∫⁻ x : ℤ, (∑ c ∈ Tc,
          mstHlMax ψ (-((((Q : ℤ) * x + m : ℤ)) : ℝ) - c)) ^ r
          ∂MeasureTheory.Measure.count := by
    have hpt : ∀ x : ℤ, (ENNReal.ofReal K * ∑ c ∈ Tc,
          mstHlMax ψ (-((((Q : ℤ) * x + m : ℤ)) : ℝ) - c)) ^ r
        = ENNReal.ofReal (K ^ r) * (∑ c ∈ Tc,
          mstHlMax ψ (-((((Q : ℤ) * x + m : ℤ)) : ℝ) - c)) ^ r := by
      intro x
      rw [ENNReal.mul_rpow_of_nonneg _ _ hr0, ENNReal.ofReal_rpow_of_nonneg hK.le hr0]
    rw [lintegral_congr hpt, MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hsum_c : (∫⁻ x : ℤ, (∑ c ∈ Tc,
          mstHlMax ψ (-((((Q : ℤ) * x + m : ℤ)) : ℝ) - c)) ^ r
          ∂MeasureTheory.Measure.count)
      ≤ (Tc.card : ENNReal) ^ (r - 1) * ∑ c ∈ Tc,
          ∫⁻ x : ℤ, (mstHlMax ψ (-((((Q : ℤ) * x + m : ℤ)) : ℝ) - c)) ^ r
            ∂MeasureTheory.Measure.count := by
    have hstep : ∀ x : ℤ, (∑ c ∈ Tc,
          mstHlMax ψ (-((((Q : ℤ) * x + m : ℤ)) : ℝ) - c)) ^ r
        ≤ (Tc.card : ENNReal) ^ (r - 1) * ∑ c ∈ Tc,
          (mstHlMax ψ (-((((Q : ℤ) * x + m : ℤ)) : ℝ) - c)) ^ r :=
      fun x => ENNReal.rpow_sum_le_const_mul_sum_rpow Tc
        (fun c => mstHlMax ψ (-((((Q : ℤ) * x + m : ℤ)) : ℝ) - c)) hr.le
    calc ∫⁻ x : ℤ, (∑ c ∈ Tc,
            mstHlMax ψ (-((((Q : ℤ) * x + m : ℤ)) : ℝ) - c)) ^ r
            ∂MeasureTheory.Measure.count
        ≤ ∫⁻ x : ℤ, (Tc.card : ENNReal) ^ (r - 1) * ∑ c ∈ Tc,
            (mstHlMax ψ (-((((Q : ℤ) * x + m : ℤ)) : ℝ) - c)) ^ r
            ∂MeasureTheory.Measure.count := lintegral_mono hstep
      _ = (Tc.card : ENNReal) ^ (r - 1) * ∫⁻ x : ℤ, ∑ c ∈ Tc,
            (mstHlMax ψ (-((((Q : ℤ) * x + m : ℤ)) : ℝ) - c)) ^ r
            ∂MeasureTheory.Measure.count :=
          MeasureTheory.lintegral_const_mul' _ _
            (ENNReal.rpow_ne_top_of_nonneg (by linarith) (ENNReal.natCast_ne_top _))
      _ = (Tc.card : ENNReal) ^ (r - 1) * ∑ c ∈ Tc,
            ∫⁻ x : ℤ, (mstHlMax ψ (-((((Q : ℤ) * x + m : ℤ)) : ℝ) - c)) ^ r
              ∂MeasureTheory.Measure.count := by
          congr 1
          exact MeasureTheory.lintegral_finsetSum Tc (fun c _ => measurable_from_top)
  -- ## The lattice maximal bound for each shifted term, via the reindexing `x ↦ -x`
  have hper : ∀ c : ℝ, (∫⁻ x : ℤ,
        (mstHlMax ψ (-((((Q : ℤ) * x + m : ℤ)) : ℝ) - c)) ^ r
          ∂MeasureTheory.Measure.count)
      ≤ ENNReal.ofReal (C_lat ^ r) * I := by
    intro c
    rw [hI, MeasureTheory.lintegral_count, MeasureTheory.lintegral_count]
    have hlat := hlattice H (1 / (2 * mstWideC P s)) hδpos hHint hHfour Q hQ1 hδQ (-m) c
    rw [hψeq] at hlat
    have hL : (∑' x : ℤ, (mstHlMax ψ (-((((Q : ℤ) * x + m : ℤ)) : ℝ) - c)) ^ r)
        = ∑' y : ℤ, (mstHlMax ψ ((Q : ℝ) * (y : ℝ) + ((-m : ℤ) : ℝ) - c)) ^ r := by
      rw [← (Equiv.neg ℤ).tsum_eq
        (fun x : ℤ => (mstHlMax ψ (-((((Q : ℤ) * x + m : ℤ)) : ℝ) - c)) ^ r)]
      refine tsum_congr (fun y => ?_)
      rw [Equiv.neg_apply]
      rw [show -(((Q : ℤ) * (-y) + m : ℤ) : ℝ) - c
            = (Q : ℝ) * (y : ℝ) + ((-m : ℤ) : ℝ) - c from by push_cast; ring]
    have hR : (∑' y : ℤ,
          ENNReal.ofReal (‖H ((Q : ℝ) * (y : ℝ) + ((-m : ℤ) : ℝ))‖ ^ r))
        = ∑' x : ℤ, ENNReal.ofReal (‖V ((Q : ℤ) * x + m)‖ ^ r) := by
      rw [← (Equiv.neg ℤ).tsum_eq
        (fun y : ℤ => ENNReal.ofReal (‖H ((Q : ℝ) * (y : ℝ) + ((-m : ℤ) : ℝ))‖ ^ r))]
      refine tsum_congr (fun x => ?_)
      rw [Equiv.neg_apply]
      have harg : (Q : ℝ) * (((-x : ℤ)) : ℝ) + ((-m : ℤ) : ℝ)
          = -((((Q : ℤ) * x + m : ℤ)) : ℝ) := by push_cast; ring
      rw [harg]
      have hv : H (-((((Q : ℤ) * x + m : ℤ)) : ℝ)) = V ((Q : ℤ) * x + m) := by
        have hh := hvals (-((Q : ℤ) * x + m))
        simp only [hH] at hh ⊢
        simpa using hh
      rw [hv]
    calc (∑' x : ℤ, (mstHlMax ψ (-((((Q : ℤ) * x + m : ℤ)) : ℝ) - c)) ^ r)
        = ∑' y : ℤ, (mstHlMax ψ ((Q : ℝ) * (y : ℝ) + ((-m : ℤ) : ℝ) - c)) ^ r := hL
      _ ≤ ENNReal.ofReal (C_lat ^ r) *
            ∑' y : ℤ, ENNReal.ofReal (‖H ((Q : ℝ) * (y : ℝ) + ((-m : ℤ) : ℝ))‖ ^ r) := hlat
      _ = ENNReal.ofReal (C_lat ^ r) *
            ∑' x : ℤ, ENNReal.ofReal (‖V ((Q : ℤ) * x + m)‖ ^ r) := by rw [hR]
  -- ## The numerical comparison of constants
  have htarget : ENNReal.ofReal ((K * (Tc.card : ℝ) * C_lat) ^ r * (Tc.card : ℝ))
      = ENNReal.ofReal (K ^ r) * (Tc.card : ENNReal) ^ r
          * ENNReal.ofReal (C_lat ^ r) * (Tc.card : ENNReal) := by
    have h1 : (0:ℝ) ≤ K * (Tc.card : ℝ) * C_lat := by positivity
    have h2 : (0:ℝ) ≤ K * (Tc.card : ℝ) := by positivity
    have hX : (0:ℝ) ≤ (K * (Tc.card : ℝ) * C_lat) ^ r := Real.rpow_nonneg h1 r
    rw [ENNReal.ofReal_mul hX, ← ENNReal.ofReal_rpow_of_nonneg h1 hr0,
      ENNReal.ofReal_mul h2, ENNReal.ofReal_mul hK.le, ENNReal.ofReal_natCast,
      ENNReal.mul_rpow_of_nonneg _ _ hr0, ENNReal.mul_rpow_of_nonneg _ _ hr0,
      ENNReal.ofReal_rpow_of_nonneg hK.le hr0,
      ENNReal.ofReal_rpow_of_nonneg hC_lat.le hr0]
  -- ## Assembly
  have hkey : ENNReal.ofReal (K ^ r) * ((Tc.card : ENNReal) ^ (r - 1) *
        ((Tc.card : ENNReal) * (ENNReal.ofReal (C_lat ^ r) * I)))
      ≤ ENNReal.ofReal ((K * (Tc.card : ℝ) * C_lat) ^ r * (Tc.card : ℝ)) * I := by
    rw [htarget]
    calc ENNReal.ofReal (K ^ r) * ((Tc.card : ENNReal) ^ (r - 1) *
            ((Tc.card : ENNReal) * (ENNReal.ofReal (C_lat ^ r) * I)))
        = (ENNReal.ofReal (K ^ r) * (Tc.card : ENNReal) ^ (r - 1) * (Tc.card : ENNReal)
            * ENNReal.ofReal (C_lat ^ r)) * I := by ring
      _ ≤ (ENNReal.ofReal (K ^ r) * (Tc.card : ENNReal) ^ r * (Tc.card : ENNReal)
            * ENNReal.ofReal (C_lat ^ r)) * I := by
          refine mul_le_mul_left ?_ I
          refine mul_le_mul_left ?_ (ENNReal.ofReal (C_lat ^ r))
          refine mul_le_mul_left ?_ (Tc.card : ENNReal)
          exact mul_le_mul_right hNr _
      _ = ENNReal.ofReal (K ^ r) * (Tc.card : ENNReal) ^ r
            * ENNReal.ofReal (C_lat ^ r) * (Tc.card : ENNReal) * I := by ring
  calc ∫⁻ x : ℤ, (⨆ k : ℕ, ‖Work.BourgainPlan.IonescuWainger.opMul (A k) F hF ((Q : ℤ) * x + m)‖ₑ) ^ r
        ∂MeasureTheory.Measure.count
      ≤ ∫⁻ x : ℤ, (ENNReal.ofReal K * ∑ c ∈ Tc,
            mstHlMax ψ (-((((Q : ℤ) * x + m : ℤ)) : ℝ) - c)) ^ r
            ∂MeasureTheory.Measure.count :=
        lintegral_mono (fun x => ENNReal.rpow_le_rpow (hsup_le x) hr0)
    _ = ENNReal.ofReal (K ^ r) * ∫⁻ x : ℤ, (∑ c ∈ Tc,
            mstHlMax ψ (-((((Q : ℤ) * x + m : ℤ)) : ℝ) - c)) ^ r
            ∂MeasureTheory.Measure.count := hsplit
    _ ≤ ENNReal.ofReal (K ^ r) * ((Tc.card : ENNReal) ^ (r - 1) * ∑ c ∈ Tc,
            ∫⁻ x : ℤ, (mstHlMax ψ (-((((Q : ℤ) * x + m : ℤ)) : ℝ) - c)) ^ r
              ∂MeasureTheory.Measure.count) := by
        refine mul_le_mul_right ?_ _
        exact hsum_c
    _ ≤ ENNReal.ofReal (K ^ r) * ((Tc.card : ENNReal) ^ (r - 1) *
          ((Tc.card : ENNReal) * (ENNReal.ofReal (C_lat ^ r) * I))) := by
        refine mul_le_mul_right ?_ _
        refine mul_le_mul_right ?_ _
        refine le_trans (Finset.sum_le_sum (fun c _ => hper c)) ?_
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ENNReal.ofReal ((K * (Tc.card : ℝ) * C_lat) ^ r * (Tc.card : ℝ)) * I := hkey

end

end Work.Maximal
