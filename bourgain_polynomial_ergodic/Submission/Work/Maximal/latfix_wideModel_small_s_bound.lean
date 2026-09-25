import Mathlib
import Submission.Work.Maximal.wideModel_small_s_bound

open MeasureTheory Finset
open Work.BourgainPlan.IonescuWainger Work.BourgainPlan.Maximal Work.Maximal

set_option maxHeartbeats 32000000
open scoped BigOperators ENNReal

local notation "Circ" => Work.BourgainPlan.IonescuWainger.Circle
local notation "haarT" => (AddCircle.haarAddCircle (T := 1))

namespace Work.Maximal

noncomputable section

theorem wideModel_small_s_bound_lat (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree)
    (hc : 0 < P.leadingCoeff) (l : ℕ) (hl : 1 ≤ l) {χ : ℝ} (hχ0 : 0 < χ) (hχ1 : χ < 1 / 10)
    (η : ℝ → ℂ) (M : ℝ) (hM : 0 < M) (hηc : ContDiff ℝ 2 η)
    (hηbd : ∀ x : ℝ, ‖η x‖ ≤ M)
    (hηsup : ∀ x : ℝ, 1 / 2 ≤ |x| → η x = 0)
    (hϱml : ∀ s : ℕ, MeasureTheory.MemLp (Work.Maximal.mstWideBump P χ η s) ⊤
      (AddCircle.haarAddCircle (T := 1)))
    (hΩml : ∀ k s : ℕ, MeasureTheory.MemLp (Work.Maximal.mstWideModel P l χ η k s) ⊤
      (AddCircle.haarAddCircle (T := 1)))
    {r : ℝ} (hr : 1 < r) (hr2 : r < 2)
    (K : ℝ) (hK : 0 < K) (Tc : Finset ℝ)
    (hTc : ∀ (n : ℕ) (ψ : ℝ → ENNReal), Measurable ψ → ∀ x : ℝ,
      ∫⁻ u in Set.Ioc 0 1, ψ (x - Polynomial.eval (2 ^ n * u) (Polynomial.map (Int.castRingHom ℝ) P))
        ≤ ENNReal.ofReal K * ∑ c ∈ Tc, Commons.Analysis.Maximal.hlMax ψ (x - c))
    (C_lat : ℝ) (hC_lat : 0 < C_lat)
    (hlattice : ∀ (H : ℝ → ℂ) (δ : ℝ), 0 < δ → Continuous H → MeasureTheory.Integrable H →
      (∀ ξ : ℝ, δ < |ξ| → FourierTransform.fourier H ξ = 0) →
      ∀ (Q : ℕ), 1 ≤ Q → δ * (Q : ℝ) ≤ 1 / 4 → ∀ (m : ℤ) (c : ℝ),
        (∑' x : ℤ, (Work.Maximal.mstHlMax (fun y : ℝ => ENNReal.ofReal ‖H y‖)
            ((Q : ℝ) * (x : ℝ) + (m : ℝ) - c)) ^ r)
          ≤ ENNReal.ofReal (C_lat ^ r) *
            ∑' x : ℤ, ENNReal.ofReal (‖H ((Q : ℝ) * (x : ℝ) + (m : ℝ))‖ ^ r))
    (C_ϱop : ℝ) (hC_ϱop : 0 < C_ϱop)
    (hϱop : ∀ (s : ℕ) (g : ℤ →₀ ℂ),
      MeasureTheory.eLpNorm (fun n : ℤ => ‖Work.BourgainPlan.IonescuWainger.opMul
          ((hϱml s).toLp (Work.Maximal.mstWideBump P χ η s)) (⇑g)
          (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g) n‖ₑ)
          (ENNReal.ofReal r) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal C_ϱop
          * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal r) MeasureTheory.Measure.count)
    (s : ℕ) (g : ℤ →₀ ℂ) :
    ∫⁻ n : ℤ, (⨆ k : ℕ, ‖Work.BourgainPlan.IonescuWainger.opMul
        (Work.Maximal.mstWideModelCls P l χ η k s (hΩml k s)) (⇑g)
        (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g) n‖ₑ) ^ r
        ∂MeasureTheory.Measure.count
      ≤ ENNReal.ofReal ((((Work.BourgainPlan.Maximal.mstU l (s + 1)).card : ℝ) + K
          + (Tc.card : ℝ) + C_lat + C_ϱop + 1) ^ 6) ^ r
        * ∫⁻ n : ℤ, ‖(⇑g) n‖ₑ ^ r ∂MeasureTheory.Measure.count := by
  classical
  have hr0 : 0 < r := lt_trans zero_lt_one hr
  have hrm1 : (0 : ℝ) ≤ r - 1 := by linarith
  have hηsup' : ∀ x : ℝ, 1 / 2 < |x| → η x = 0 := fun x hx => hηsup x hx.le
  have hηcont : Continuous η := hηc.continuous
  have hg2 : Memℓp (⇑g : ℤ → ℂ) 2 := Work.BourgainPlan.IonescuWainger.memℓp_finsupp g
  set E : Finset Circ := mstAnnulus l s with hE
  set T : Finset ℤ := g.support with hT
  have hEsub : E ⊆ Work.BourgainPlan.Maximal.mstU l (s + 1) := by
    intro β hβ
    have h : β ∈ Work.BourgainPlan.Maximal.mstLevel l (s + 1)
        \ Work.BourgainPlan.Maximal.mstLevel l s := hβ
    rw [Work.BourgainPlan.Maximal.mstLevel_succ] at h
    exact (Finset.mem_sdiff.mp h).1
  have hEcard : ((E.card : ℝ)) ≤ ((Work.BourgainPlan.Maximal.mstU l (s + 1)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hEsub
  set gβd : Circ → ℤ →₀ ℂ := (fun β => Finsupp.onFinset g.support
      (fun k => (⇑g) k * fourier k β) (by
        intro k hk; rw [Finsupp.mem_support_iff]; intro h; exact hk (by rw [h, zero_mul])))
    with hgβddef
  have hgβcoe : ∀ β : Circ, (⇑(gβd β) : ℤ → ℂ) = fun k => (⇑g) k * fourier k β := by
    intro β; funext k
    simp only [hgβddef, Finsupp.onFinset_apply]
  have hmem : ∀ β : Circ, Memℓp (⇑(gβd β) : ℤ → ℂ) 2 := fun β => memℓp_finsupp _
  have hsupp : ∀ β : Circ, ∀ m ∉ T, (⇑(gβd β) : ℤ → ℂ) m = 0 := by
    intro β m hm
    rw [hgβcoe β]
    have hg0 : (⇑g : ℤ → ℂ) m = 0 := by
      by_contra h
      exact hm (by rw [hT]; exact Finsupp.mem_support_iff.mpr h)
    show (⇑g : ℤ → ℂ) m * fourier m β = 0
    rw [hg0, zero_mul]
  have hBk : ∀ k : ℕ, MemLp (fun ξ : Circ => star (mstProf P (2 ^ k) ξ) * mstWideBump P χ η s ξ)
      ⊤ haarT := fun k => memLp_star_mstProf_mul_mstWideBump P k s χ η hηcont (hϱml s)
  set ψβ : Circ → (ℝ → ℝ≥0∞) := fun β z => ‖mstWideLat P χ η s (⇑(gβd β)) T z‖ₑ with hψβ
  have hmod : ∀ β : Circ, Work.BourgainPlan.IonescuWainger.modSeq (⇑g) β = ⇑(gβd β) := by
    intro β; funext k
    simp only [hgβcoe β, Work.BourgainPlan.IonescuWainger.modSeq]
  have hsingle : ∀ (β : Circ) (n : ℤ),
      (⨆ k : ℕ, ‖opMul ((hBk k).toLp (fun ξ : Circ => star (mstProf P (2 ^ k) ξ)
            * mstWideBump P χ η s ξ)) (⇑(gβd β)) (memℓp_finsupp (gβd β)) n‖ₑ)
        ≤ ENNReal.ofReal K * ∑ c ∈ Tc, mstHlMax (ψβ β) (-(n : ℝ) - c) := by
    intro β n
    refine iSup_le (fun k => ?_)
    have hcurve := Work.Maximal.mstWideLat_curve P χ η s (⇑(gβd β)) T hηc hηsup'
      (hsupp β) (hmem β) (2 ^ k) n (hBk k)
    have hψm : Measurable (ψβ β) := by
      rw [hψβ]
      exact ((Work.Maximal.mstWideLat_continuous P χ η s (⇑(gβd β)) T hηc hηsup').enorm).measurable
    have hTc' := hTc k (ψβ β) hψm (-(n : ℝ))
    have hcast : ∀ u : ℝ, ((2 ^ k : ℕ) : ℝ) * u = (2 : ℝ) ^ k * u := fun u => by
      rw [Nat.cast_pow, Nat.cast_ofNat]
    rw [hcurve, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    refine le_trans (enorm_integral_le_lintegral_enorm _) ?_
    refine le_trans (le_of_eq ?_) hTc'
    refine MeasureTheory.lintegral_congr fun u => ?_
    rw [hcast u]
  have hpt : ∀ n : ℤ, (⨆ k : ℕ, ‖opMul (mstWideModelCls P l χ η k s (hΩml k s))
        (⇑g) hg2 n‖ₑ)
      ≤ ∑ β ∈ E, ENNReal.ofReal K * ∑ c ∈ Tc, mstHlMax (ψβ β) (-(n : ℝ) - c) := by
    intro n
    refine iSup_le (fun k => ?_)
    have hsum := opMul_modelFn_eq_sum (fun β : Circ => star (mstG P β))
        (fun ζ : Circ => star (mstProf P (2 ^ k) ζ)) (mstWideBump P χ η s) E (hBk k)
        (hΩml k s) (⇑g) hg2 n
    have hcls : mstWideModelCls P l χ η k s (hΩml k s)
        = (hΩml k s).toLp (Work.BourgainPlan.Maximal.mstModelFn (fun β : Circ => star (mstG P β))
            (fun ζ : Circ => star (mstProf P (2 ^ k) ζ)) (mstWideBump P χ η s) E) := rfl
    rw [hcls, hsum]
    refine le_trans (enorm_sum_le E _) ?_
    refine Finset.sum_le_sum (fun β _ => ?_)
    rw [enorm_mul]
    have hG1 : ‖star (mstG P β)‖ₑ ≤ 1 := by
      rw [show ‖star (mstG P β)‖ₑ = ‖mstG P β‖ₑ by simp [enorm_eq_nnnorm],
        show ‖mstG P β‖ₑ = ENNReal.ofReal ‖mstG P β‖ by simp [enorm_eq_nnnorm]]
      exact ENNReal.ofReal_le_one.mpr (mstG_norm_le_one P β)
    have hbridge : ‖opMul (Work.BourgainPlan.Maximal.mstArcTransLp β ((hBk k).toLp
          (fun ξ : Circ => star (mstProf P (2 ^ k) ξ) * mstWideBump P χ η s ξ))) (⇑g) hg2 n‖ₑ
        = ‖opMul ((hBk k).toLp (fun ξ : Circ => star (mstProf P (2 ^ k) ξ)
            * mstWideBump P χ η s ξ)) (⇑(gβd β)) (memℓp_finsupp (gβd β)) n‖ₑ := by
      have h3 : Work.BourgainPlan.IonescuWainger.opMul ((hBk k).toLp (fun ξ : Circ =>
            star (mstProf P (2 ^ k) ξ) * mstWideBump P χ η s ξ))
            (Work.BourgainPlan.IonescuWainger.modSeq (⇑g) β)
            (Work.BourgainPlan.IonescuWainger.memℓp_modSeq hg2 β)
          = Work.BourgainPlan.IonescuWainger.opMul ((hBk k).toLp (fun ξ : Circ =>
            star (mstProf P (2 ^ k) ξ) * mstWideBump P χ η s ξ))
            (⇑(gβd β)) (memℓp_finsupp (gβd β)) :=
        opMul_congr_input _ (hmod β) _ _
      have h4 : ‖Work.BourgainPlan.IonescuWainger.opMul
            (Work.BourgainPlan.Maximal.mstArcTransLp β ((hBk k).toLp (fun ξ : Circ =>
              star (mstProf P (2 ^ k) ξ) * mstWideBump P χ η s ξ))) (⇑g) hg2 n‖
          = ‖Work.BourgainPlan.IonescuWainger.opMul ((hBk k).toLp (fun ξ : Circ =>
              star (mstProf P (2 ^ k) ξ) * mstWideBump P χ η s ξ))
              (⇑(gβd β)) (memℓp_finsupp (gβd β)) n‖ := by
        rw [norm_opMul_arcTranslate ((hBk k).toLp _) (⇑g) hg2 β n]
        exact congrArg (fun f : ℤ → ℂ => ‖f n‖) h3
      rw [show ‖Work.BourgainPlan.IonescuWainger.opMul
              (Work.BourgainPlan.Maximal.mstArcTransLp β ((hBk k).toLp (fun ξ : Circ =>
                star (mstProf P (2 ^ k) ξ) * mstWideBump P χ η s ξ))) (⇑g) hg2 n‖ₑ
            = ENNReal.ofReal ‖Work.BourgainPlan.IonescuWainger.opMul
              (Work.BourgainPlan.Maximal.mstArcTransLp β ((hBk k).toLp (fun ξ : Circ =>
                star (mstProf P (2 ^ k) ξ) * mstWideBump P χ η s ξ))) (⇑g) hg2 n‖
            by simp [enorm_eq_nnnorm],
          show ‖Work.BourgainPlan.IonescuWainger.opMul ((hBk k).toLp (fun ξ : Circ =>
              star (mstProf P (2 ^ k) ξ) * mstWideBump P χ η s ξ))
              (⇑(gβd β)) (memℓp_finsupp (gβd β)) n‖ₑ
            = ENNReal.ofReal ‖Work.BourgainPlan.IonescuWainger.opMul ((hBk k).toLp (fun ξ : Circ =>
              star (mstProf P (2 ^ k) ξ) * mstWideBump P χ η s ξ))
              (⇑(gβd β)) (memℓp_finsupp (gβd β)) n‖
            by simp [enorm_eq_nnnorm],
          h4]
    rw [hbridge]
    calc ‖star (mstG P β)‖ₑ * ‖opMul ((hBk k).toLp (fun ξ : Circ => star (mstProf P (2 ^ k) ξ)
            * mstWideBump P χ η s ξ)) (⇑(gβd β)) (memℓp_finsupp (gβd β)) n‖ₑ
        ≤ 1 * ‖opMul ((hBk k).toLp (fun ξ : Circ => star (mstProf P (2 ^ k) ξ)
            * mstWideBump P χ η s ξ)) (⇑(gβd β)) (memℓp_finsupp (gβd β)) n‖ₑ :=
          mul_le_mul_of_nonneg_right hG1 (bot_le)
      _ = ‖opMul ((hBk k).toLp (fun ξ : Circ => star (mstProf P (2 ^ k) ξ)
            * mstWideBump P χ η s ξ)) (⇑(gβd β)) (memℓp_finsupp (gβd β)) n‖ₑ := one_mul _
      _ ≤ ⨆ j : ℕ, ‖opMul ((hBk j).toLp (fun ξ : Circ => star (mstProf P (2 ^ j) ξ)
            * mstWideBump P χ η s ξ)) (⇑(gβd β)) (memℓp_finsupp (gβd β)) n‖ₑ :=
          le_iSup (fun j : ℕ => ‖opMul ((hBk j).toLp (fun ξ : Circ => star (mstProf P (2 ^ j) ξ)
            * mstWideBump P χ η s ξ)) (⇑(gβd β)) (memℓp_finsupp (gβd β)) n‖ₑ) k
      _ ≤ ENNReal.ofReal K * ∑ c ∈ Tc, mstHlMax (ψβ β) (-(n : ℝ) - c) := hsingle β n
  -- ## final assembly
  set B : ℝ := ((Work.BourgainPlan.Maximal.mstU l (s + 1)).card : ℝ) + K + (Tc.card : ℝ)
    + C_lat + C_ϱop + 1 with hBdef
  have hCB : (0 : ℝ) ≤ ((Work.BourgainPlan.Maximal.mstU l (s + 1)).card : ℝ) := Nat.cast_nonneg _
  have hTcB : (0 : ℝ) ≤ (Tc.card : ℝ) := Nat.cast_nonneg _
  have hB1 : 1 ≤ B := by rw [hBdef]; linarith [hK.le, hC_lat.le, hC_ϱop.le]
  have hBpos : 0 < B := lt_of_lt_of_le one_pos hB1
  have hKleB : K ≤ B := by rw [hBdef]; linarith [hC_lat.le, hC_ϱop.le]
  have hEleB : (E.card : ℝ) ≤ B := by rw [hBdef]; linarith [hEcard, hK.le, hC_lat.le, hC_ϱop.le]
  have hTleB : (Tc.card : ℝ) ≤ B := by rw [hBdef]; linarith [hK.le, hC_lat.le, hC_ϱop.le]
  have hC_lat_leB : C_lat ≤ B := by rw [hBdef]; linarith [hK.le, hC_ϱop.le]
  have hC_ϱop_leB : C_ϱop ≤ B := by rw [hBdef]; linarith [hK.le, hC_lat.le]
  have hDle : K * ((E.card : ℝ) * (Tc.card : ℝ)) * C_lat * C_ϱop ≤ B ^ 6 := by
    have h5 : K * ((E.card : ℝ) * (Tc.card : ℝ)) * C_lat * C_ϱop ≤ B ^ 5 := by
      have hEE : (E.card : ℝ) * (Tc.card : ℝ) ≤ B * B :=
        mul_le_mul hEleB hTleB hTcB hBpos.le
      have h1 : K * ((E.card : ℝ) * (Tc.card : ℝ)) ≤ B * (B * B) :=
        mul_le_mul hKleB hEE (by positivity) hBpos.le
      have h2 : K * ((E.card : ℝ) * (Tc.card : ℝ)) * C_lat ≤ (B * (B * B)) * B :=
        mul_le_mul h1 hC_lat_leB hC_lat.le (by positivity)
      have h3 : K * ((E.card : ℝ) * (Tc.card : ℝ)) * C_lat * C_ϱop
          ≤ (B * (B * B)) * B * B :=
        mul_le_mul h2 hC_ϱop_leB hC_ϱop.le (by positivity)
      calc K * ((E.card : ℝ) * (Tc.card : ℝ)) * C_lat * C_ϱop
          ≤ (B * (B * B)) * B * B := h3
        _ = B ^ 5 := by ring
    exact le_trans h5 (pow_le_pow_right₀ hB1 (by norm_num))
  set Y : ℤ → ℝ≥0∞ := fun n => ∑ β ∈ E, ∑ c ∈ Tc, mstHlMax (ψβ β) (-(n : ℝ) - c) with hYdef
  have hpt' : ∀ n : ℤ, (⨆ k : ℕ, ‖opMul (mstWideModelCls P l χ η k s (hΩml k s))
        (⇑g) hg2 n‖ₑ) ≤ ENNReal.ofReal K * Y n := by
    intro n
    rw [hYdef, Finset.mul_sum]
    exact hpt n
  have hstep1 : (∫⁻ n : ℤ, (⨆ k : ℕ, ‖opMul (mstWideModelCls P l χ η k s (hΩml k s))
        (⇑g) hg2 n‖ₑ)^r ∂MeasureTheory.Measure.count)
      ≤ ENNReal.ofReal (K ^ r) * ∫⁻ n : ℤ, (Y n)^r ∂MeasureTheory.Measure.count := by
    calc (∫⁻ n : ℤ, (⨆ k : ℕ, ‖opMul (mstWideModelCls P l χ η k s (hΩml k s))
            (⇑g) hg2 n‖ₑ)^r ∂MeasureTheory.Measure.count)
        ≤ ∫⁻ n : ℤ, (ENNReal.ofReal K * Y n)^r ∂MeasureTheory.Measure.count :=
          MeasureTheory.lintegral_mono (fun n => ENNReal.rpow_le_rpow (hpt' n) hr0.le)
      _ = ∫⁻ n : ℤ, ENNReal.ofReal (K ^ r) * (Y n)^r ∂MeasureTheory.Measure.count := by
          refine MeasureTheory.lintegral_congr fun n => ?_
          rw [ENNReal.mul_rpow_of_nonneg _ _ hr0.le,
            ENNReal.ofReal_rpow_of_nonneg hK.le hr0.le]
      _ = ENNReal.ofReal (K ^ r) * ∫⁻ n : ℤ, (Y n)^r ∂MeasureTheory.Measure.count :=
          MeasureTheory.lintegral_const_mul' (ENNReal.ofReal (K ^ r)) (fun n : ℤ => (Y n)^r)
            ENNReal.ofReal_ne_top
  have hcard_prod : ((E.product Tc).card : ℝ≥0∞)
      = ENNReal.ofReal ((E.card : ℝ) * (Tc.card : ℝ)) := by
    have h1 : (E.product Tc).card = E.card * Tc.card := Finset.card_product E Tc
    have h2 : (((E.card * Tc.card : ℕ)) : ℝ≥0∞)
        = ENNReal.ofReal ((E.card : ℝ) * (Tc.card : ℝ)) := by
      rw [Nat.cast_mul, ENNReal.ofReal_mul (show (0 : ℝ) ≤ (E.card : ℝ) by positivity),
        ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
    rw [h1]; exact h2
  have hYprod : ∀ n : ℤ, Y n = ∑ p ∈ E.product Tc, mstHlMax (ψβ p.1) (-(n : ℝ) - p.2) := by
    intro n
    rw [hYdef]
    exact (Finset.sum_product E Tc (fun p : Circ × ℝ =>
      mstHlMax (ψβ p.1) (-(n : ℝ) - p.2))).symm

  have hstep2 : (∫⁻ n : ℤ, (Y n)^r ∂MeasureTheory.Measure.count)
      ≤ ENNReal.ofReal ((E.card : ℝ) * (Tc.card : ℝ)) ^ (r - 1) *
          ∑ p ∈ E.product Tc, ∫⁻ n : ℤ, (mstHlMax (ψβ p.1) (-(n : ℝ) - p.2))^r
            ∂MeasureTheory.Measure.count := by
    calc (∫⁻ n : ℤ, (Y n)^r ∂MeasureTheory.Measure.count)
        ≤ ∫⁻ n : ℤ, (ENNReal.ofReal ((E.card : ℝ) * (Tc.card : ℝ)))^(r - 1) *
            ∑ p ∈ E.product Tc, (mstHlMax (ψβ p.1) (-(n : ℝ) - p.2))^r
            ∂MeasureTheory.Measure.count := by
          refine MeasureTheory.lintegral_mono fun n => ?_
          rw [hYprod n]
          refine le_trans (ENNReal.rpow_sum_le_const_mul_sum_rpow (E.product Tc) _ hr.le) ?_
          rw [hcard_prod]
      _ = ENNReal.ofReal ((E.card : ℝ) * (Tc.card : ℝ)) ^ (r - 1) *
            ∫⁻ n : ℤ, ∑ p ∈ E.product Tc, (mstHlMax (ψβ p.1) (-(n : ℝ) - p.2))^r
              ∂MeasureTheory.Measure.count :=
          MeasureTheory.lintegral_const_mul' _ _ (by
            rcases eq_or_ne (ENNReal.ofReal ((E.card : ℝ) * (Tc.card : ℝ))) 0 with h0 | h0
            · rw [h0, ENNReal.zero_rpow_of_pos (by linarith : (0 : ℝ) < r - 1)]
              exact ENNReal.zero_ne_top
            · exact ENNReal.rpow_ne_top_of_ne_zero h0 ENNReal.ofReal_ne_top)
      _ = ENNReal.ofReal ((E.card : ℝ) * (Tc.card : ℝ)) ^ (r - 1) *
            ∑ p ∈ E.product Tc, ∫⁻ n : ℤ, (mstHlMax (ψβ p.1) (-(n : ℝ) - p.2))^r
              ∂MeasureTheory.Measure.count := by
          congr 1
          rw [MeasureTheory.lintegral_finsetSum]
          intro p _
          exact ((Commons.Analysis.Maximal.measurable_hlMax (ψβ p.1)).comp
            (by fun_prop : Measurable fun n : ℤ => -(n : ℝ) - p.2)).pow_const r
  have hstep3 : ∀ p ∈ E.product Tc,
      (∫⁻ n : ℤ, (mstHlMax (ψβ p.1) (-(n : ℝ) - p.2))^r ∂MeasureTheory.Measure.count)
        ≤ ENNReal.ofReal (C_lat^r) *
          ∫⁻ n : ℤ, ENNReal.ofReal (‖mstWideLat P χ η s (⇑(gβd p.1)) T (n : ℝ)‖^r)
            ∂MeasureTheory.Measure.count := by
    intro p _
    have hδpos : 0 < 1 / (2 * mstWideC P s) := by
      have h2 := two_le_mstWideC P hd s; positivity
    have hδQ : (1 / (2 * mstWideC P s)) * ((1 : ℕ) : ℝ) ≤ 1 / 4 := by
      have h2 := two_le_mstWideC P hd s
      have hc2 : (0 : ℝ) < 2 * mstWideC P s := by linarith
      rw [Nat.cast_one, mul_one, div_le_iff₀ hc2]; linarith
    have hlat := hlattice (mstWideLat P χ η s (⇑(gβd p.1)) T) (1 / (2 * mstWideC P s)) hδpos
      (mstWideLat_continuous P χ η s (⇑(gβd p.1)) T hηc hηsup')
      (mstWideLat_integrable P χ η s (⇑(gβd p.1)) T hηc hηsup')
      (mstWideLat_fourier_support P χ η s (⇑(gβd p.1)) T hηc hηsup') 1 le_rfl hδQ 0 p.2
    have hfun : (ψβ p.1) = fun y : ℝ =>
        ENNReal.ofReal ‖mstWideLat P χ η s (⇑(gβd p.1)) T y‖ := by
      funext y
      simp only [hψβ]
      simp [enorm_eq_nnnorm]
    have hψeq : mstHlMax (ψβ p.1) = mstHlMax
        (fun y : ℝ => ENNReal.ofReal ‖mstWideLat P χ η s (⇑(gβd p.1)) T y‖) := by
      rw [hfun]
    rw [MeasureTheory.lintegral_count, MeasureTheory.lintegral_count]
    simp only [Nat.cast_one, Int.cast_zero, one_mul, add_zero] at hlat
    rw [show (∑' n : ℤ, (mstHlMax (ψβ p.1) (-(n : ℝ) - p.2))^r)
          = ∑' n : ℤ, (fun x : ℤ => (mstHlMax (fun y : ℝ => ENNReal.ofReal
              ‖mstWideLat P χ η s (⇑(gβd p.1)) T y‖) ((x : ℝ) - p.2))^r) (Equiv.neg ℤ n) from
        tsum_congr (fun n => by
          simp only [hfun, Equiv.neg_apply]
          rw [show (-(n : ℝ) - p.2) = (((-n : ℤ) : ℝ) - p.2) from by push_cast; ring]),
      Equiv.tsum_eq (Equiv.neg ℤ) (fun x : ℤ => (mstHlMax (fun y : ℝ => ENNReal.ofReal
        ‖mstWideLat P χ η s (⇑(gβd p.1)) T y‖) ((x : ℝ) - p.2))^r)]
    exact hlat
  have hstep4 : ∀ β : Circ,
      (∫⁻ n : ℤ, ENNReal.ofReal (‖mstWideLat P χ η s (⇑(gβd β)) T (n : ℝ)‖^r)
          ∂MeasureTheory.Measure.count)
        ≤ ENNReal.ofReal (C_ϱop^r) * ∫⁻ n : ℤ, ‖(⇑g) n‖ₑ^r ∂MeasureTheory.Measure.count := by
    intro β
    set F1 : ℤ → ℂ := fun n => opMul ((hϱml s).toLp (mstWideBump P χ η s))
        (⇑(gβd β)) (memℓp_finsupp (gβd β)) n with hF1
    have hsample : ∀ j : ℤ, mstWideLat P χ η s (⇑(gβd β)) T (j : ℝ) = F1 (-j) :=
      fun j => Work.Maximal.mstWideLat_apply_int P χ η s (⇑(gβd β)) T hηc hηsup'
        (hsupp β) (hmem β) (hϱml s) j
    have hsum1 : (∫⁻ n : ℤ, ENNReal.ofReal (‖mstWideLat P χ η s (⇑(gβd β)) T (n : ℝ)‖^r)
          ∂MeasureTheory.Measure.count)
        = (MeasureTheory.eLpNorm F1 (ENNReal.ofReal r) MeasureTheory.Measure.count)^r := by
      rw [← tsum_ofReal_norm_rpow_eq_eLpNorm_rpow F1 hr0, MeasureTheory.lintegral_count]
      rw [show (∑' n : ℤ, ENNReal.ofReal (‖mstWideLat P χ η s (⇑(gβd β)) T (n : ℝ)‖^r))
            = ∑' n : ℤ, (fun x : ℤ => ENNReal.ofReal (‖F1 x‖^r)) (Equiv.neg ℤ n) from
          tsum_congr (fun n => by
            rw [show mstWideLat P χ η s (⇑(gβd β)) T ((n : ℤ) : ℝ) = F1 (Equiv.neg ℤ n) from by
              rw [show (Equiv.neg ℤ n : ℤ) = -n from rfl]; exact hsample n]),
        Equiv.tsum_eq (Equiv.neg ℤ) (fun x : ℤ => ENNReal.ofReal (‖F1 x‖^r))]
    have hgl : (∫⁻ n : ℤ, ‖(⇑g) n‖ₑ^r ∂MeasureTheory.Measure.count)
        = (MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal r) MeasureTheory.Measure.count)^r := by
      rw [← tsum_ofReal_norm_rpow_eq_eLpNorm_rpow (⇑g) hr0, MeasureTheory.lintegral_count]
      refine tsum_congr fun n => ?_
      rw [show ‖(⇑g) n‖ₑ = ENNReal.ofReal ‖(⇑g) n‖ by simp [enorm_eq_nnnorm],
        ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hr0.le]
    rw [hsum1, hgl, ← eLpNorm_enorm_eq F1 hr0]
    calc (MeasureTheory.eLpNorm (fun n => ‖F1 n‖ₑ) (ENNReal.ofReal r)
          MeasureTheory.Measure.count)^r
        ≤ (ENNReal.ofReal C_ϱop * MeasureTheory.eLpNorm (⇑(gβd β))
            (ENNReal.ofReal r) MeasureTheory.Measure.count)^r :=
          ENNReal.rpow_le_rpow (hϱop s (gβd β)) hr0.le
      _ = ENNReal.ofReal (C_ϱop^r) * (MeasureTheory.eLpNorm (⇑(gβd β))
            (ENNReal.ofReal r) MeasureTheory.Measure.count)^r := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hr0.le,
            ENNReal.ofReal_rpow_of_nonneg hC_ϱop.le hr0.le]
      _ = ENNReal.ofReal (C_ϱop^r) * (MeasureTheory.eLpNorm (⇑g)
            (ENNReal.ofReal r) MeasureTheory.Measure.count)^r := by
          congr 1
          rw [← tsum_ofReal_norm_rpow_eq_eLpNorm_rpow (⇑(gβd β)) hr0,
            ← tsum_ofReal_norm_rpow_eq_eLpNorm_rpow (⇑g) hr0]
          refine tsum_congr fun n => ?_
          rw [show (⇑(gβd β)) n = (⇑g) n * fourier n β from congrFun (hgβcoe β) n]
          simp only [norm_mul, Work.BourgainPlan.IonescuWainger.norm_fourier_apply', mul_one]
  have hstageB : (∑ p ∈ E.product Tc,
        ∫⁻ n : ℤ, (mstHlMax (ψβ p.1) (-(n : ℝ) - p.2))^r ∂MeasureTheory.Measure.count)
      ≤ ENNReal.ofReal ((E.card : ℝ) * (Tc.card : ℝ)) *
          (ENNReal.ofReal (C_lat^r * C_ϱop^r) *
            ∫⁻ n : ℤ, ‖(⇑g) n‖ₑ^r ∂MeasureTheory.Measure.count) := by
    have hper : ∀ p ∈ E.product Tc,
        (∫⁻ n : ℤ, (mstHlMax (ψβ p.1) (-(n : ℝ) - p.2))^r ∂MeasureTheory.Measure.count)
          ≤ ENNReal.ofReal (C_lat^r * C_ϱop^r) *
            ∫⁻ n : ℤ, ‖(⇑g) n‖ₑ^r ∂MeasureTheory.Measure.count := by
      intro p hp
      refine le_trans (hstep3 p hp) ?_
      refine le_trans (mul_le_mul_right (hstep4 p.1) (ENNReal.ofReal (C_lat^r))) ?_
      rw [← mul_assoc, ENNReal.ofReal_mul (by positivity)]
    calc (∑ p ∈ E.product Tc,
          ∫⁻ n : ℤ, (mstHlMax (ψβ p.1) (-(n : ℝ) - p.2))^r ∂MeasureTheory.Measure.count)
        ≤ ∑ p ∈ E.product Tc,
            (ENNReal.ofReal (C_lat^r * C_ϱop^r) *
              ∫⁻ n : ℤ, ‖(⇑g) n‖ₑ^r ∂MeasureTheory.Measure.count) :=
          Finset.sum_le_sum hper
      _ = ((E.product Tc).card : ℝ≥0∞) *
            (ENNReal.ofReal (C_lat^r * C_ϱop^r) *
              ∫⁻ n : ℤ, ‖(⇑g) n‖ₑ^r ∂MeasureTheory.Measure.count) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = ENNReal.ofReal ((E.card : ℝ) * (Tc.card : ℝ)) *
            (ENNReal.ofReal (C_lat^r * C_ϱop^r) *
              ∫⁻ n : ℤ, ‖(⇑g) n‖ₑ^r ∂MeasureTheory.Measure.count) := by
          rw [hcard_prod]
  have hpowmul : ENNReal.ofReal ((E.card : ℝ) * (Tc.card : ℝ)) ^ (r - 1)
        * ENNReal.ofReal ((E.card : ℝ) * (Tc.card : ℝ))
      = ENNReal.ofReal (((E.card : ℝ) * (Tc.card : ℝ))^r) := by
    have hx : (0 : ℝ) ≤ (E.card : ℝ) * (Tc.card : ℝ) := by positivity
    rw [ENNReal.ofReal_rpow_of_nonneg hx (by linarith),
      ← ENNReal.ofReal_mul (show (0 : ℝ) ≤ ((E.card : ℝ) * (Tc.card : ℝ))^(r-1) by positivity)]
    congr 1
    exact rpow_sub_one_mul_self _ hx hr0
  have hstageC : (∫⁻ n : ℤ, (Y n)^r ∂MeasureTheory.Measure.count)
      ≤ ENNReal.ofReal (((E.card : ℝ) * (Tc.card : ℝ))^r * (C_lat^r * C_ϱop^r)) *
          ∫⁻ n : ℤ, ‖(⇑g) n‖ₑ^r ∂MeasureTheory.Measure.count := by
    refine le_trans hstep2 ?_
    refine le_trans (mul_le_mul_right hstageB
      (ENNReal.ofReal ((E.card : ℝ) * (Tc.card : ℝ)) ^ (r - 1))) ?_
    rw [← mul_assoc, hpowmul, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  have hDrev : (K * ((E.card : ℝ) * (Tc.card : ℝ)) * C_lat * C_ϱop)^r
      = K^r * (((E.card : ℝ) * (Tc.card : ℝ))^r * (C_lat^r * C_ϱop^r)) :=
    mul_rpow_four K ((E.card : ℝ) * (Tc.card : ℝ)) C_lat C_ϱop (hK.le) (by positivity)
      hC_lat.le hC_ϱop.le r
  have hD : K^r * (((E.card : ℝ) * (Tc.card : ℝ))^r * (C_lat^r * C_ϱop^r))
      = (K * ((E.card : ℝ) * (Tc.card : ℝ)) * C_lat * C_ϱop)^r := hDrev.symm
  have hDle' : K^r * (((E.card : ℝ) * (Tc.card : ℝ))^r * (C_lat^r * C_ϱop^r)) ≤ (B ^ 6)^r := by
    rw [hD]
    exact Real.rpow_le_rpow (by positivity) hDle hr0.le
  have hfinal : (∫⁻ n : ℤ, (⨆ k : ℕ, ‖opMul (mstWideModelCls P l χ η k s (hΩml k s))
        (⇑g) hg2 n‖ₑ)^r ∂MeasureTheory.Measure.count)
      ≤ ENNReal.ofReal (B ^ 6) ^ r * ∫⁻ n : ℤ, ‖(⇑g) n‖ₑ^r ∂MeasureTheory.Measure.count := by
    calc (∫⁻ n : ℤ, (⨆ k : ℕ, ‖opMul (mstWideModelCls P l χ η k s (hΩml k s))
            (⇑g) hg2 n‖ₑ)^r ∂MeasureTheory.Measure.count)
        ≤ ENNReal.ofReal (K ^ r) *
            (ENNReal.ofReal (((E.card : ℝ) * (Tc.card : ℝ))^r * (C_lat^r * C_ϱop^r)) *
              ∫⁻ n : ℤ, ‖(⇑g) n‖ₑ^r ∂MeasureTheory.Measure.count) :=
          le_trans hstep1 (mul_le_mul_right hstageC _)
      _ = ENNReal.ofReal (K^r * (((E.card : ℝ) * (Tc.card : ℝ))^r * (C_lat^r * C_ϱop^r))) *
            ∫⁻ n : ℤ, ‖(⇑g) n‖ₑ^r ∂MeasureTheory.Measure.count := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
      _ ≤ ENNReal.ofReal (B ^ 6) ^ r * ∫⁻ n : ℤ, ‖(⇑g) n‖ₑ^r ∂MeasureTheory.Measure.count := by
          rw [ENNReal.ofReal_rpow_of_nonneg (by positivity : (0 : ℝ) ≤ B ^ 6) hr0.le]
          exact mul_le_mul_left (ENNReal.ofReal_le_ofReal hDle') _
  rw [hBdef] at hfinal
  exact hfinal
end

end Work.Maximal
