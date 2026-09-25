import Mathlib
import Submission.Work.BourgainPlan.Maximal.mst_major_defs
import Submission.Work.BourgainPlan.Maximal.polyProfile_decay_sharp
import Submission.Work.BourgainPlan.Maximal.sigmaN_nested
import Submission.Work.BourgainPlan.Maximal.sigmaN_separated
import Submission.Work.BourgainPlan.Maximal.sigmaN_card_le
import Submission.Work.BourgainPlan.Maximal.eLpNorm_two_opMul_le

namespace Work.BourgainPlan.Maximal

open MeasureTheory Finset
open scoped BigOperators ENNReal

noncomputable section

local notation "haarT" => (AddCircle.haarAddCircle (T := 1))

/-! ## The annuli `mstLevel l (s+1) \ mstLevel l s` tile `mstU l n` -/

private lemma mstU_le_succ (l n : ℕ) : mstU l n ⊆ mstU l (n + 1) := by
  rw [mstU_apply, mstU_apply]
  exact sigmaN_nested (mstRho l) (Nat.pow_le_pow_left (Nat.le_succ n) l)

private lemma mstLevel_of_pos (l n : ℕ) (hn : 0 < n) : mstLevel l n = mstU l n := by
  simp [mstLevel, hn.ne']

private lemma mstU_annulus_tiling_aux (l n : ℕ) (hn : 1 ≤ n)
    (f : Work.BourgainPlan.IonescuWainger.Circle → ℂ) :
    (∑ β ∈ mstU l n, f β)
      = ∑ s ∈ Finset.range n, ∑ β ∈ mstLevel l (s + 1) \ mstLevel l s, f β := by
  induction n, hn using Nat.le_induction with
  | base => rw [Finset.sum_range_one, mstLevel_succ l 0, mstLevel_zero, Finset.sdiff_empty]
  | succ n hn ih =>
      rw [Finset.sum_range_succ, ← ih, ← Finset.sum_sdiff (mstU_le_succ l n),
        mstLevel_succ l n, mstLevel_of_pos l n (by omega)]
      ring

/-! ## The pointwise value of the difference of the two model symbols -/

lemma mstErr2_pointwise (P : Polynomial ℤ) (l d : ℕ) (χ : ℝ) (η : ℝ → ℂ) (n : ℕ)
    (hn : 1 ≤ n) (ξ : Work.BourgainPlan.IonescuWainger.Circle) :
    mstNu P l d χ η n ξ - ∑ s ∈ Finset.range n, mstNuS P l d χ η n s ξ
      = ∑ s ∈ Finset.range n, ∑ β ∈ mstLevel l (s + 1) \ mstLevel l s,
          star (mstG P β) *
            (star (mstProf P (2 ^ n) (ξ - β)) *
              (mstEta d χ η n (ξ - β) - mstEta d χ η s (ξ - β))) := by
  rw [mstNu_apply, Finset.sum_congr rfl (fun s _ => mstNuS_apply P l d χ η n s ξ)]
  rw [mstU_annulus_tiling_aux l n hn
    (fun β => star (mstG P β) *
      (star (mstProf P (2 ^ n) (ξ - β)) * mstEta d χ η n (ξ - β)))]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun β _ => ?_)
  ring

/-! ## The a.e. value of the class `mstMajErr2Cls` -/

lemma mstMajErr2Cls_coeFn (P : Polynomial ℤ) (l d : ℕ) (χ : ℝ) (η : ℝ → ℂ) (n : ℕ)
    (hν : MemLp (mstNu P l d χ η n) ⊤ haarT)
    (h : ∀ s : ℕ, MemLp (mstNuS P l d χ η n s) ⊤ haarT) :
    (mstMajErr2Cls P l d χ η n hν h : Work.BourgainPlan.IonescuWainger.Circle → ℂ)
      =ᵐ[haarT] fun ξ => mstNu P l d χ η n ξ
        - ∑ s ∈ Finset.range n, mstNuS P l d χ η n s ξ := by
  have hnu' : (⇑(mstNuCls P l d χ η n hν) : Work.BourgainPlan.IonescuWainger.Circle → ℂ)
      =ᵐ[haarT] mstNu P l d χ η n := MemLp.coeFn_toLp hν
  have hsum' : (⇑(mstNuSumCls P l d χ η n h) : Work.BourgainPlan.IonescuWainger.Circle → ℂ)
      =ᵐ[haarT] fun ξ => ∑ s ∈ Finset.range n, mstNuS P l d χ η n s ξ := by
    show (⇑(∑ s ∈ Finset.range n, (h s).toLp (mstNuS P l d χ η n s)) :
        Work.BourgainPlan.IonescuWainger.Circle → ℂ)
      =ᵐ[haarT] fun ξ => ∑ s ∈ Finset.range n, mstNuS P l d χ η n s ξ
    have hsum := Lp.coeFn_finsetSum (Finset.range n)
      (fun s => (h s).toLp (mstNuS P l d χ η n s))
    have hall : ∀ᵐ ξ ∂haarT, ∀ s ∈ Finset.range n,
        ((h s).toLp (mstNuS P l d χ η n s) :
          Work.BourgainPlan.IonescuWainger.Circle → ℂ) ξ = mstNuS P l d χ η n s ξ := by
      rw [Finset.eventually_all]
      intro s _
      exact MemLp.coeFn_toLp (h s)
    filter_upwards [hsum, hall] with ξ h2 h4
    rw [h2, Finset.sum_apply]
    exact Finset.sum_congr rfl (fun s hs => h4 s hs)
  exact (Lp.coeFn_sub (mstNuCls P l d χ η n hν) (mstNuSumCls P l d χ η n h)).trans
    (hnu'.sub hsum')


/-! ## Exponential domination: `(n+1)·exp(n^{1/10})` against `2^{-c n}` -/

private lemma mul_exp_rpow_neg_le_aux (a c : ℝ) (hc : 0 < c) (hca : c < a) :
    ∃ N₁ : ℕ, ∀ n : ℕ, N₁ ≤ n →
      ((n : ℝ) + 1) * Real.exp ((n : ℝ) ^ (1 / 10 : ℝ)) * (2 : ℝ) ^ (-(a * (n : ℝ)))
        ≤ (2 : ℝ) ^ (-(c * (n : ℝ))) := by
  have hac : 0 < a - c := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  set δ : ℝ := (a - c) * Real.log 2 with hδdef
  have hδ0 : 0 < δ := mul_pos hac hlog2
  obtain ⟨C₁, hC₁3, hC₁⟩ :=
    Work.BourgainPlan.IonescuWainger.exists_log_le_rpow (6 / δ) 1 (by positivity) (by norm_num)
  obtain ⟨C₂, hC₂⟩ := exists_rpow_ge (s := (9 : ℝ) / 10) (B := 3 / δ) (by norm_num) (by positivity)
  refine ⟨max ⌈6 * Real.log 2 / δ⌉₊ (max ⌈C₁⌉₊ (max C₂ 2)), fun n hn => ?_⟩
  have hA : ⌈6 * Real.log 2 / δ⌉₊ ≤ n := le_trans (le_max_left _ _) hn
  have hB : ⌈C₁⌉₊ ≤ n :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hn)
  have hC : C₂ ≤ n :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hn))
  have hD : 2 ≤ n :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hn))
  have hnA : 6 * Real.log 2 / δ ≤ (n : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hA)
  have hnC₁ : C₁ ≤ (n : ℝ) := le_trans (Nat.le_ceil C₁) (by exact_mod_cast hB)
  have hnC₂ : (C₂ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hC
  have hn1 : 1 ≤ n := by omega
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hnR1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hlog_n : Real.log (n : ℝ) ≤ δ / 6 * (n : ℝ) := by
    have h := hC₁ n hnC₁
    rw [Real.rpow_one] at h
    have hmul : δ / 6 * (6 / δ * Real.log (n : ℝ)) = Real.log (n : ℝ) := by field_simp
    calc Real.log (n : ℝ) = δ / 6 * (6 / δ * Real.log (n : ℝ)) := hmul.symm
      _ ≤ δ / 6 * (n : ℝ) := mul_le_mul_of_nonneg_left h (by positivity)
  have hlog2le : Real.log 2 ≤ δ / 6 * (n : ℝ) := by
    have hmul : δ / 6 * (6 * Real.log 2 / δ) = Real.log 2 := by field_simp
    calc Real.log 2 = δ / 6 * (6 * Real.log 2 / δ) := hmul.symm
      _ ≤ δ / 6 * (n : ℝ) := mul_le_mul_of_nonneg_left hnA (by positivity)
  have hstep1 : (n : ℝ) + 1 ≤ Real.exp (δ / 3 * (n : ℝ)) := by
    have h2n : (n : ℝ) + 1 ≤ 2 * (n : ℝ) := by linarith
    have hlog : Real.log (2 * (n : ℝ)) ≤ δ / 3 * (n : ℝ) := by
      rw [Real.log_mul (by norm_num) (ne_of_gt hnpos)]
      linarith
    have h := (Real.log_le_iff_le_exp (by positivity : (0 : ℝ) < 2 * (n : ℝ))).mp hlog
    linarith
  have hstep2 : Real.exp ((n : ℝ) ^ (1 / 10 : ℝ)) ≤ Real.exp (δ / 3 * (n : ℝ)) := by
    have hgn : 1 ≤ (δ / 3) * (n : ℝ) ^ (9 / 10 : ℝ) := by
      have h := hC₂ n hnC₂
      have hmul : (δ / 3) * (3 / δ) = 1 := by field_simp
      calc (1 : ℝ) = (δ / 3) * (3 / δ) := hmul.symm
        _ ≤ (δ / 3) * (n : ℝ) ^ (9 / 10 : ℝ) := mul_le_mul_of_nonneg_left h (by positivity)
    have h1 : (1 : ℝ) * (n : ℝ) ^ (1 / 10 : ℝ)
        ≤ ((δ / 3) * (n : ℝ) ^ (9 / 10 : ℝ)) * (n : ℝ) ^ (1 / 10 : ℝ) :=
      mul_le_mul_of_nonneg_right hgn (Real.rpow_nonneg hnpos.le _)
    have h2 : ((δ / 3) * (n : ℝ) ^ (9 / 10 : ℝ)) * (n : ℝ) ^ (1 / 10 : ℝ)
        = (δ / 3) * (n : ℝ) := by
      rw [mul_assoc, ← Real.rpow_add hnpos]
      norm_num
    rw [h2] at h1
    exact Real.exp_le_exp.mpr (by linarith)
  have hmain : ((n : ℝ) + 1) * Real.exp ((n : ℝ) ^ (1 / 10 : ℝ)) ≤ Real.exp (δ * (n : ℝ)) := by
    have h1 := mul_le_mul hstep1 hstep2 (Real.exp_pos _).le (by positivity)
    have h2 : Real.exp (δ / 3 * (n : ℝ)) * Real.exp (δ / 3 * (n : ℝ))
        = Real.exp ((2 * δ / 3) * (n : ℝ)) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [h2] at h1
    refine h1.trans (Real.exp_le_exp.mpr ?_)
    nlinarith [hnpos]
  have hLHS : (2 : ℝ) ^ (-(a * (n : ℝ))) = Real.exp (Real.log 2 * (-(a * (n : ℝ)))) :=
    Real.rpow_def_of_pos (by norm_num) _
  have hRHS : (2 : ℝ) ^ (-(c * (n : ℝ))) = Real.exp (Real.log 2 * (-(c * (n : ℝ)))) :=
    Real.rpow_def_of_pos (by norm_num) _
  rw [hLHS, hRHS]
  calc ((n : ℝ) + 1) * Real.exp ((n : ℝ) ^ (1 / 10 : ℝ))
        * Real.exp (Real.log 2 * (-(a * (n : ℝ))))
      ≤ Real.exp (δ * (n : ℝ)) * Real.exp (Real.log 2 * (-(a * (n : ℝ)))) :=
        mul_le_mul_of_nonneg_right hmain (Real.exp_pos _).le
    _ = Real.exp (δ * (n : ℝ) + Real.log 2 * (-(a * (n : ℝ)))) := (Real.exp_add _ _).symm
    _ = Real.exp (Real.log 2 * (-(c * (n : ℝ)))) := by
        congr 1
        rw [hδdef]
        ring

/-! ## The per-term bound for the second major-arc error -/

open Commons.Analysis.ExponentialSums in
private lemma mstErr2_term_bound_aux (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree)
    {χ : ℝ} (hχ0 : 0 < χ) (hχd : χ < (P.natDegree : ℝ))
    (η : ℝ → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hηbd : ∀ x : ℝ, ‖η x‖ ≤ M)
    (hη1 : ∀ x : ℝ, |x| ≤ 1 / 4 → η x = 1)
    (hη2 : ∀ x : ℝ, 1 / 2 < |x| → η x = 0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (s n : ℕ), s ≤ n → (4 : ℝ) ≤ (2 : ℝ) ^ (χ * (n : ℝ)) →
      ∀ (β ξ : Work.BourgainPlan.IonescuWainger.Circle),
      ‖star (mstG P β) * (star (mstProf P (2 ^ n) (ξ - β)) *
        (mstEta P.natDegree χ η n (ξ - β) - mstEta P.natDegree χ η s (ξ - β)))‖
      ≤ K * (2 : ℝ) ^ (-(χ * (n : ℝ) / (P.natDegree : ℝ))) := by
  obtain ⟨C, hCpos, hC⟩ := polyProfile_decay_sharp P hd
  refine ⟨4 * M * C, by positivity, fun s n hsn h4 β ξ => ?_⟩
  set x : ℝ := Work.BourgainPlan.Maximal.iwRep (ξ - β) with hxdef
  set D : ℝ := (2 : ℝ) ^ ((n : ℝ) * ((P.natDegree : ℝ) - χ)) with hDdef
  set E : ℝ := (2 : ℝ) ^ ((s : ℝ) * ((P.natDegree : ℝ) - χ)) with hEdef
  have hEn : mstEta P.natDegree χ η n (ξ - β) = η (D * x) := by
    rw [mstEta_apply, hDdef, hxdef]
  have hEs : mstEta P.natDegree χ η s (ξ - β) = η (E * x) := by
    rw [mstEta_apply, hEdef, hxdef]
  have hdR : 0 < (P.natDegree : ℝ) := by exact_mod_cast (by omega : 0 < P.natDegree)
  have hdχ : 0 ≤ (P.natDegree : ℝ) - χ := by linarith
  have hDpos : 0 < D := Real.rpow_pos_of_pos (by norm_num) _
  have hEpos : 0 < E := Real.rpow_pos_of_pos (by norm_num) _
  by_cases hzero : mstEta P.natDegree χ η n (ξ - β) - mstEta P.natDegree χ η s (ξ - β) = 0
  · simp only [hzero, mul_zero, norm_zero]
    exact mul_nonneg (by positivity) (Real.rpow_nonneg (by norm_num) _)
  · have hquarter : 1 / 4 < D * |x| := by
      by_contra hcon
      push_neg at hcon
      have hsnR : (s : ℝ) ≤ (n : ℝ) := by exact_mod_cast hsn
      have hEl : E * |x| ≤ 1 / 4 := by
        have hle : E ≤ D := by
          rw [hDdef, hEdef]
          exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
            (by nlinarith [hsnR, hdχ])
        exact le_trans (mul_le_mul_of_nonneg_right hle (abs_nonneg x)) hcon
      apply hzero
      have h1 : η (D * x) = 1 := by
        apply hη1
        rw [abs_mul, abs_of_pos hDpos]
        exact hcon
      have h2 : η (E * x) = 1 := by
        apply hη1
        rw [abs_mul, abs_of_pos hEpos]
        exact hEl
      rw [hEn, hEs, h1, h2, sub_self]
    have hxne : x ≠ 0 := by
      intro hx0
      rw [hx0, abs_zero, mul_zero] at hquarter
      linarith
    have hx_lower : 1 / 4 / D < |x| := (div_lt_iff₀ hDpos).mpr (by rw [mul_comm]; exact hquarter)
    have hpd : polyDil P n = (2 : ℝ) ^ ((n : ℝ) * (P.natDegree : ℝ)) := by
      rw [polyDil, powDil, ← Real.rpow_natCast (2 : ℝ) n,
        ← Real.rpow_natCast ((2 : ℝ) ^ (n : ℝ)) P.natDegree,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have hDinv : D⁻¹ = (2 : ℝ) ^ (-((n : ℝ) * ((P.natDegree : ℝ) - χ))) := by
      rw [hDdef, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    have hB1 : 1 ≤ (2 : ℝ) ^ (χ * (n : ℝ) - 2) := by
      have h : (2 : ℝ) ^ (χ * (n : ℝ)) = (2 : ℝ) ^ (χ * (n : ℝ) - 2) * 4 := by
        rw [show χ * (n : ℝ) = (χ * (n : ℝ) - 2) + 2 by ring,
          Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        norm_num
      nlinarith [h4, h]
    have hBpos : 0 < (2 : ℝ) ^ (χ * (n : ℝ) - 2) := Real.rpow_pos_of_pos (by norm_num) _
    have hBlt : (2 : ℝ) ^ (χ * (n : ℝ) - 2) < |x| * polyDil P n := by
      have h1 : 1 / 4 / D * (2 : ℝ) ^ ((n : ℝ) * (P.natDegree : ℝ))
          < |x| * (2 : ℝ) ^ ((n : ℝ) * (P.natDegree : ℝ)) :=
        mul_lt_mul_of_pos_right hx_lower (Real.rpow_pos_of_pos (by norm_num) _)
      have h2 : 1 / 4 / D * (2 : ℝ) ^ ((n : ℝ) * (P.natDegree : ℝ))
          = (2 : ℝ) ^ (χ * (n : ℝ) - 2) := by
        have h4' : (1 / 4 : ℝ) = (2 : ℝ) ^ (-2 : ℝ) := by
          rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
          norm_num
        rw [div_eq_mul_inv, hDinv, h4', ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
          ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        congr 1
        ring
      rw [hpd]
      linarith [h1, h2.le, h2.ge]
    have hApos : 0 < |x| * polyDil P n := lt_trans hBpos hBlt
    have hdec := hC x hxne n (le_trans hB1 hBlt.le)
    have hstep_a : (|x| * polyDil P n) ^ (-(1 / (P.natDegree : ℝ)))
        ≤ ((2 : ℝ) ^ (χ * (n : ℝ) - 2)) ^ (-(1 / (P.natDegree : ℝ))) := by
      rw [Real.rpow_neg (le_of_lt hApos), Real.rpow_neg (le_of_lt hBpos)]
      exact (inv_le_inv₀ (Real.rpow_pos_of_pos hApos _) (Real.rpow_pos_of_pos hBpos _)).mpr
        (Real.rpow_le_rpow (le_of_lt hBpos) (le_of_lt hBlt) (by positivity))
    have hstep_b : ((2 : ℝ) ^ (χ * (n : ℝ) - 2)) ^ (-(1 / (P.natDegree : ℝ)))
        = (2 : ℝ) ^ (-((χ * (n : ℝ) - 2)) / (P.natDegree : ℝ)) := by
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      ring
    have hstep_c : (2 : ℝ) ^ (-((χ * (n : ℝ) - 2)) / (P.natDegree : ℝ))
        ≤ 2 * (2 : ℝ) ^ (-(χ * (n : ℝ) / (P.natDegree : ℝ))) := by
      have h2d : 2 / (P.natDegree : ℝ) ≤ 1 := by
        rw [div_le_one hdR]
        exact_mod_cast hd
      calc (2 : ℝ) ^ (-((χ * (n : ℝ) - 2)) / (P.natDegree : ℝ))
          = (2 : ℝ) ^ (2 / (P.natDegree : ℝ) - χ * (n : ℝ) / (P.natDegree : ℝ)) := by
            congr 1; ring
        _ = (2 : ℝ) ^ (2 / (P.natDegree : ℝ)) * (2 : ℝ) ^ (-(χ * (n : ℝ) / (P.natDegree : ℝ))) :=
            Real.rpow_add (by norm_num : (0 : ℝ) < 2) _ _
        _ ≤ 2 * (2 : ℝ) ^ (-(χ * (n : ℝ) / (P.natDegree : ℝ))) :=
            mul_le_mul_of_nonneg_right
              (by simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) h2d)
              (Real.rpow_nonneg (by norm_num) _)
    have hpown : (|x| * polyDil P n) ^ (-(1 / (P.natDegree : ℝ)))
        ≤ 2 * (2 : ℝ) ^ (-(χ * (n : ℝ) / (P.natDegree : ℝ))) :=
      hstep_a.trans (hstep_b.trans_le hstep_c)
    have hprof : ‖mstProf P (2 ^ n) (ξ - β)‖
        ≤ 2 * C * (2 : ℝ) ^ (-(χ * (n : ℝ) / (P.natDegree : ℝ))) := by
      have h1 : ‖mstProf P (2 ^ n) (ξ - β)‖ = ‖polyProfile P (2 ^ n) x‖ := by
        rw [mstProf_apply, hxdef]
      rw [h1]
      calc ‖polyProfile P (2 ^ n) x‖
          ≤ C * (|x| * polyDil P n) ^ (-(1 / (P.natDegree : ℝ))) := hdec
        _ ≤ C * (2 * (2 : ℝ) ^ (-(χ * (n : ℝ) / (P.natDegree : ℝ)))) :=
            mul_le_mul_of_nonneg_left hpown hCpos.le
        _ = 2 * C * (2 : ℝ) ^ (-(χ * (n : ℝ) / (P.natDegree : ℝ))) := by ring
    have hsub : ‖mstEta P.natDegree χ η n (ξ - β) - mstEta P.natDegree χ η s (ξ - β)‖ ≤ 2 * M := by
      have h1 : ‖mstEta P.natDegree χ η n (ξ - β)‖ = ‖η (D * x)‖ := by rw [hEn]
      have h2 : ‖mstEta P.natDegree χ η s (ξ - β)‖ = ‖η (E * x)‖ := by rw [hEs]
      calc ‖mstEta P.natDegree χ η n (ξ - β) - mstEta P.natDegree χ η s (ξ - β)‖
          ≤ ‖mstEta P.natDegree χ η n (ξ - β)‖ + ‖mstEta P.natDegree χ η s (ξ - β)‖ :=
            norm_sub_le _ _
        _ = ‖η (D * x)‖ + ‖η (E * x)‖ := by rw [h1, h2]
        _ ≤ 2 * M := by linarith [hηbd (D * x), hηbd (E * x)]
    have hG : ‖star (mstG P β)‖ ≤ 1 := by simpa using mstG_norm_le_one P β
    have hstar : ‖star (mstProf P (2 ^ n) (ξ - β))‖
        ≤ 2 * C * (2 : ℝ) ^ (-(χ * (n : ℝ) / (P.natDegree : ℝ))) := by
      rw [norm_star]; exact hprof
    calc ‖star (mstG P β) * (star (mstProf P (2 ^ n) (ξ - β)) *
            (mstEta P.natDegree χ η n (ξ - β) - mstEta P.natDegree χ η s (ξ - β)))‖
        = ‖star (mstG P β)‖ * ‖star (mstProf P (2 ^ n) (ξ - β)) *
            (mstEta P.natDegree χ η n (ξ - β) - mstEta P.natDegree χ η s (ξ - β))‖ :=
          norm_mul _ _
      _ ≤ 1 * ((2 * C * (2 : ℝ) ^ (-(χ * (n : ℝ) / (P.natDegree : ℝ)))) * (2 * M)) := by
          refine mul_le_mul hG ?_ (norm_nonneg _) (by positivity)
          exact (norm_mul_le _ _).trans (mul_le_mul hstar hsub (norm_nonneg _) (by positivity))
      _ = (4 * M * C) * (2 : ℝ) ^ (-(χ * (n : ℝ) / (P.natDegree : ℝ))) := by ring

/-! ## The pointwise bound on the annulus sum -/

private lemma mstRho_pow_eq_aux (l : ℕ) (hl : 1 ≤ l) (n : ℕ) (hn : 1 ≤ n) :
    ((n ^ l : ℕ) : ℝ) ^ (mstRho l) = (n : ℝ) ^ (1 / 10 : ℝ) := by
  have hl0 : (l : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (l : ℝ) := by exact_mod_cast (by omega : 0 < l)
    linarith
  rw [mstRho, Nat.cast_pow, ← Real.rpow_natCast (n : ℝ) l,
    ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ (n : ℝ))]
  congr 1
  field_simp

private lemma mstErr2_sum_bound_aux (P : Polynomial ℤ) (l : ℕ) (hl : 1 ≤ l) (χ : ℝ)
    (hχ0 : 0 < χ) (η : ℝ → ℂ) {K : ℝ} (hK : 0 ≤ K)
    (hterm : ∀ (s n : ℕ), s ≤ n → (4 : ℝ) ≤ (2 : ℝ) ^ (χ * (n : ℝ)) →
      ∀ (β ξ : Work.BourgainPlan.IonescuWainger.Circle),
      ‖star (mstG P β) * (star (mstProf P (2 ^ n) (ξ - β)) *
        (mstEta P.natDegree χ η n (ξ - β) - mstEta P.natDegree χ η s (ξ - β)))‖
      ≤ K * (2 : ℝ) ^ (-(χ * (n : ℝ) / (P.natDegree : ℝ)))) :
    ∃ N₁ : ℕ, ∀ n : ℕ, N₁ ≤ n → ∀ ξ : Work.BourgainPlan.IonescuWainger.Circle,
      ‖∑ s ∈ Finset.range n, ∑ β ∈ mstLevel l (s + 1) \ mstLevel l s,
        star (mstG P β) * (star (mstProf P (2 ^ n) (ξ - β)) *
          (mstEta P.natDegree χ η n (ξ - β) - mstEta P.natDegree χ η s (ξ - β)))‖
      ≤ 2 * K * ((n : ℝ) + 1) * Real.exp ((n : ℝ) ^ (1 / 10 : ℝ))
          * (2 : ℝ) ^ (-(χ * (n : ℝ) / (P.natDegree : ℝ))) := by
  have hρ : 0 < mstRho l := by rw [mstRho]; positivity
  obtain ⟨Nc, hNc⟩ := sigmaN_card_le (mstRho l) hρ
  refine ⟨max Nc (max ⌈2 / χ⌉₊ 2), fun n hn ξ => ?_⟩
  have hnNc : Nc ≤ n := le_trans (le_max_left _ _) hn
  have hnχ : 2 / χ ≤ (n : ℝ) :=
    le_trans (Nat.le_ceil _)
      (by exact_mod_cast le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hn))
  have hn2 : 2 ≤ n :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hn)
  have hn1 : 1 ≤ n := by omega
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  -- the hypothesis `4 ≤ 2^{χn}` of the per-term bound
  have h4 : (4 : ℝ) ≤ (2 : ℝ) ^ (χ * (n : ℝ)) := by
    have h2 : (2 : ℝ) ≤ χ * (n : ℝ) := by
      have := mul_le_mul_of_nonneg_left hnχ hχ0.le
      rwa [mul_div_cancel₀ _ (ne_of_gt hχ0)] at this
    calc (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) := by norm_num
      _ ≤ (2 : ℝ) ^ (χ * (n : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) h2
  -- the cardinality of the level set
  have hcardNat : (mstU l n).card ≤ ⌈Real.exp ((n : ℝ) ^ (1 / 10 : ℝ))⌉₊ := by
    have h := hNc (n ^ l) (le_trans hnNc (Nat.le_self_pow (by omega : l ≠ 0) n))
    rw [mstRho_pow_eq_aux l hl n hn1] at h
    simpa only [mstU, iwSigma, iwK] using h
  have hcardR : ((mstU l n).card : ℝ) ≤ Real.exp ((n : ℝ) ^ (1 / 10 : ℝ)) + 1 := by
    have h2 : (⌈Real.exp ((n : ℝ) ^ (1 / 10 : ℝ))⌉₊ : ℝ)
        < Real.exp ((n : ℝ) ^ (1 / 10 : ℝ)) + 1 :=
      Nat.ceil_lt_add_one (Real.exp_pos _).le
    exact le_of_lt (lt_of_le_of_lt (by exact_mod_cast hcardNat) h2)
  -- the sum over the annuli
  have hsub : ∀ s ∈ Finset.range n, mstLevel l (s + 1) \ mstLevel l s ⊆ mstU l n := by
    intro s hs
    have hsle : s + 1 ≤ n := by
      have := Finset.mem_range.mp hs
      omega
    exact (Finset.sdiff_subset.trans (by
      rw [mstLevel_succ]
      rw [mstU_apply, mstU_apply]
      exact sigmaN_nested (mstRho l) (Nat.pow_le_pow_left hsle l)))
  have hstep : ‖∑ s ∈ Finset.range n, ∑ β ∈ mstLevel l (s + 1) \ mstLevel l s,
        star (mstG P β) * (star (mstProf P (2 ^ n) (ξ - β)) *
          (mstEta P.natDegree χ η n (ξ - β) - mstEta P.natDegree χ η s (ξ - β)))‖
      ≤ ∑ s ∈ Finset.range n,
          (Real.exp ((n : ℝ) ^ (1 / 10 : ℝ)) + 1)
            * (K * (2 : ℝ) ^ (-(χ * (n : ℝ) / (P.natDegree : ℝ)))) := by
    calc ‖∑ s ∈ Finset.range n, ∑ β ∈ mstLevel l (s + 1) \ mstLevel l s,
          star (mstG P β) * (star (mstProf P (2 ^ n) (ξ - β)) *
            (mstEta P.natDegree χ η n (ξ - β) - mstEta P.natDegree χ η s (ξ - β)))‖
        ≤ ∑ s ∈ Finset.range n, ‖∑ β ∈ mstLevel l (s + 1) \ mstLevel l s,
          star (mstG P β) * (star (mstProf P (2 ^ n) (ξ - β)) *
            (mstEta P.natDegree χ η n (ξ - β) - mstEta P.natDegree χ η s (ξ - β)))‖ :=
          norm_sum_le _ _
      _ ≤ ∑ s ∈ Finset.range n,
            ∑ β ∈ mstLevel l (s + 1) \ mstLevel l s,
              ‖star (mstG P β) * (star (mstProf P (2 ^ n) (ξ - β)) *
                (mstEta P.natDegree χ η n (ξ - β) - mstEta P.natDegree χ η s (ξ - β)))‖ :=
          Finset.sum_le_sum (fun s _ => norm_sum_le _ _)
      _ ≤ ∑ s ∈ Finset.range n, ∑ _β ∈ mstLevel l (s + 1) \ mstLevel l s,
              (K * (2 : ℝ) ^ (-(χ * (n : ℝ) / (P.natDegree : ℝ)))) := by
          refine Finset.sum_le_sum (fun s hs => Finset.sum_le_sum (fun β _ => ?_))
          exact hterm s n (le_of_lt (Finset.mem_range.mp hs)) h4 β ξ
      _ = ∑ s ∈ Finset.range n,
            (((mstLevel l (s + 1) \ mstLevel l s).card : ℝ)
              * (K * (2 : ℝ) ^ (-(χ * (n : ℝ) / (P.natDegree : ℝ))))) := by
          refine Finset.sum_congr rfl (fun s _ => ?_)
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ s ∈ Finset.range n,
            ((Real.exp ((n : ℝ) ^ (1 / 10 : ℝ)) + 1)
              * (K * (2 : ℝ) ^ (-(χ * (n : ℝ) / (P.natDegree : ℝ))))) := by
          refine Finset.sum_le_sum (fun s hs => ?_)
          exact mul_le_mul_of_nonneg_right
            (le_trans (by exact_mod_cast (Finset.card_le_card (hsub s hs))) hcardR) (by positivity)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hstep
  refine hstep.trans ?_
  have hexp1 : 1 ≤ Real.exp ((n : ℝ) ^ (1 / 10 : ℝ)) :=
    Real.one_le_exp (Real.rpow_nonneg hnpos.le _)
  have hn1R : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hkey : (n : ℝ) * (Real.exp ((n : ℝ) ^ (1 / 10 : ℝ)) + 1)
      ≤ 2 * ((n : ℝ) + 1) * Real.exp ((n : ℝ) ^ (1 / 10 : ℝ)) := by
    nlinarith [hexp1, hn1R, hnpos,
      mul_nonneg (le_of_lt hnpos) (le_of_lt (Real.exp_pos ((n : ℝ) ^ (1 / 10 : ℝ))))]
  calc (n : ℝ) * ((Real.exp ((n : ℝ) ^ (1 / 10 : ℝ)) + 1)
        * (K * (2 : ℝ) ^ (-(χ * (n : ℝ) / (P.natDegree : ℝ)))))
      = ((n : ℝ) * (Real.exp ((n : ℝ) ^ (1 / 10 : ℝ)) + 1))
          * (K * (2 : ℝ) ^ (-(χ * (n : ℝ) / (P.natDegree : ℝ)))) := by ring
    _ ≤ (2 * ((n : ℝ) + 1) * Real.exp ((n : ℝ) ^ (1 / 10 : ℝ)))
          * (K * (2 : ℝ) ^ (-(χ * (n : ℝ) / (P.natDegree : ℝ)))) :=
        mul_le_mul_of_nonneg_right hkey (by positivity)
    _ = 2 * K * ((n : ℝ) + 1) * Real.exp ((n : ℝ) ^ (1 / 10 : ℝ))
          * (2 : ℝ) ^ (-(χ * (n : ℝ) / (P.natDegree : ℝ))) := by ring

/-- Mirek-Stein-Trojan, arXiv:1512.07518, §4.2, eqs. (76), (80): the `ℓ²` estimate for the second major-arc error `ν_{2^n} − Σ_{0 ≤ s < n} ν_{2^n}^s`.

The level sets use the `𝒰(0) := ∅` convention (`mstLevel l 0 = ∅`, `mstLevel l (s+1) = mstU l (s+1)` in `Maximal/mst_major_defs.lean`), so the annuli `mstLevel l (s+1) ∖ mstLevel l s`, `s = 0, …, n−1`, tile `mstU l n` (`sigmaN_nested`), and the a.e. symbol of `mstMajErr2Cls` is

  `Σ_{0 ≤ s < n} Σ_{β ∈ mstLevel l (s+1) ∖ mstLevel l s} star (G β · Φ_{2^n}(ξ−β)) · (η_s − η_n)(ξ−β)`,

with `G = mstG P`, `Φ = mstProf P (2^n)`, `η_s = mstEta d χ η s`.  In particular the trivial point `0` lies in the `s = 0` annulus and carries the level-`0` bump `η_0 = η`, which agrees with `η_n` on the support of the latter — no leftover term.

Route: `η_n` equals `1` on the ball of radius `2^{−n(d−χ)}/4` and is supported in the ball of radius `2^{−n(d−χ)}/2`, while `η_s` is supported in the ball of radius `2^{−s(d−χ)}/2`; hence any term with `(η_s − η_n)(ξ−β) ≠ 0` has `‖ξ−β‖ > 2^{−n(d−χ)}/4`, and `polyProfile_decay_sharp` (van der Corput, `hd ≥ 2`) gives `‖Φ_{2^n}(ξ−β)‖ ≤ C 2^{−χn/d}`.  At each level `s` at most one `β` contributes (disjoint bump supports; points of `mstU l (s+1)` are `exp(−2(s+1)^{1/10})`-separated by `sigmaN_separated`), so the pointwise error is `≤ C M (n + 1) 2^{−χn/d} ≤ C' 2^{−c n}` for any fixed `c < χ/d` (the factor `n` comes from the `n` levels, and is why the conclusion uses an existential `c > 0`); `|G| ≤ 1` is `mstG_norm_le_one`.  Plancherel (`eLpNorm_two_opMul_le`) then gives the `ℓ²` bound; the bookkeeping between the class difference and this pointwise sum is `=ᵐ` reasoning with `MemLp.coeFn_toLp`, `mstNu_apply`, `mstNuS_apply`. -/
theorem mst_major_err2_l2 (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (hc : 0 < P.leadingCoeff)
    {χ : ℝ} (hχ0 : 0 < χ) (hχ1 : χ < 1 / 10) (η : ℝ → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hηbd : ∀ x : ℝ, ‖η x‖ ≤ M)
    (hη1 : ∀ x : ℝ, |x| ≤ 1 / 4 → η x = 1) (hη2 : ∀ x : ℝ, 1 / 2 < |x| → η x = 0)
    (l : ℕ) (hl : 1 ≤ l)
    (hνml : ∀ n : ℕ, MeasureTheory.MemLp
      (Work.BourgainPlan.Maximal.mstNu P l P.natDegree χ η n) ⊤
      (AddCircle.haarAddCircle (T := 1)))
    (hνsml : ∀ n s : ℕ, MeasureTheory.MemLp
      (Work.BourgainPlan.Maximal.mstNuS P l P.natDegree χ η n s) ⊤
      (AddCircle.haarAddCircle (T := 1))) :
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧ ∃ N₁ : ℕ, ∀ n : ℕ, N₁ ≤ n →
      ∀ (f : ℤ → ℂ) (hf : Memℓp f 2),
        MeasureTheory.eLpNorm (Work.BourgainPlan.IonescuWainger.opMul
            (Work.BourgainPlan.Maximal.mstMajErr2Cls P l P.natDegree χ η n (hνml n) (hνsml n))
            f hf) (ENNReal.ofReal 2) MeasureTheory.Measure.count
          ≤ ENNReal.ofReal (C * (2 : ℝ) ^ (-(c * (n : ℝ))))
              * MeasureTheory.eLpNorm f (ENNReal.ofReal 2) MeasureTheory.Measure.count := by
  classical
  have hχd : χ < (P.natDegree : ℝ) := by
    have h2 : (2 : ℝ) ≤ (P.natDegree : ℝ) := by exact_mod_cast hd
    linarith
  obtain ⟨K, hK, hterm⟩ := mstErr2_term_bound_aux P hd hχ0 hχd η M hM hηbd hη1 hη2
  obtain ⟨Ns, hNs⟩ := mstErr2_sum_bound_aux P l hl χ hχ0 η hK hterm
  have hdpos : 0 < (P.natDegree : ℝ) := by exact_mod_cast (by omega : 0 < P.natDegree)
  set a : ℝ := χ / (P.natDegree : ℝ) with hadef
  set c : ℝ := χ / (2 * (P.natDegree : ℝ)) with hcdef
  have hcpos : 0 < c := by rw [hcdef]; positivity
  have hca : c < a := by
    rw [hcdef, hadef]
    have h1 : χ / (2 * (P.natDegree : ℝ)) = (χ / (P.natDegree : ℝ)) / 2 := by ring
    rw [h1]
    have h2 : 0 < χ / (P.natDegree : ℝ) := div_pos hχ0 hdpos
    linarith
  obtain ⟨Na, hNa⟩ := mul_exp_rpow_neg_le_aux a c hcpos hca
  refine ⟨max (2 * K) 1, by positivity, c, hcpos, max Ns (max Na 1), fun n hn f hf => ?_⟩
  have hnNs : Ns ≤ n := le_trans (le_max_left _ _) hn
  have hnNa : Na ≤ n := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hn)
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hn)
  have hbound_ae : ∀ᵐ ξ ∂haarT,
      ‖(mstMajErr2Cls P l P.natDegree χ η n (hνml n) (hνsml n) :
        Work.BourgainPlan.IonescuWainger.Circle → ℂ) ξ‖
        ≤ max (2 * K) 1 * (2 : ℝ) ^ (-(c * (n : ℝ))) := by
    filter_upwards [mstMajErr2Cls_coeFn P l P.natDegree χ η n (hνml n) (hνsml n)] with ξ h
    rw [h, mstErr2_pointwise P l P.natDegree χ η n hn1 ξ]
    have haeq : (2 : ℝ) ^ (-(a * (n : ℝ)))
        = (2 : ℝ) ^ (-(χ * (n : ℝ) / (P.natDegree : ℝ))) := by
      congr 1
      rw [hadef]
      ring
    have hmain : 2 * K * ((n : ℝ) + 1) * Real.exp ((n : ℝ) ^ (1 / 10 : ℝ))
          * (2 : ℝ) ^ (-(χ * (n : ℝ) / (P.natDegree : ℝ)))
        ≤ 2 * K * (2 : ℝ) ^ (-(c * (n : ℝ))) := by
      have h1 : 2 * K * ((n : ℝ) + 1) * Real.exp ((n : ℝ) ^ (1 / 10 : ℝ))
            * (2 : ℝ) ^ (-(χ * (n : ℝ) / (P.natDegree : ℝ)))
          = 2 * K * (((n : ℝ) + 1) * Real.exp ((n : ℝ) ^ (1 / 10 : ℝ))
              * (2 : ℝ) ^ (-(a * (n : ℝ)))) := by
        rw [← haeq]; ring
      rw [h1]
      exact mul_le_mul_of_nonneg_left (hNa n hnNa) (by positivity)
    exact (hNs n hnNs ξ).trans (hmain.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.rpow_nonneg (by norm_num) _)))
  exact eLpNorm_two_opMul_le hf (by positivity) hbound_ae

end

end Work.BourgainPlan.Maximal
