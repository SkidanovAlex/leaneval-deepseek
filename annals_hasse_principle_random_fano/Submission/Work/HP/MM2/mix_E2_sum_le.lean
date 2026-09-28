import Mathlib
import Submission.Work.HP.MM2.Defs
import Submission.Work.HP.MM2.mix_arith
import Submission.Work.HP.DeltaXY_gcd_detL
import Submission.Work.HP.six_le_NN
import Submission.Work.HP.EE_lower2
import Submission.Work.HP.Lat.detL_ge_one
import Submission.Work.HP.MDEstimates.veronese_linIndep
import Submission.Work.HP.MDEstimates.Sigma1_estimate
import Submission.Work.HP.bigW_le_pow
import Submission.Work.HP.MinkDefs
import Submission.Work.HP.MM2.zetaR_le_two
import Submission.Work.HP.MM2.one_le_DeltaXY

namespace Work.HP.MM2

theorem mix_E2_sum_le (d n : ℕ) [DecidableEq (Work.HP.Mon d n)] (hd : 2 ≤ d) (hdn : d ≤ n)
    (h22 : (d, n) ≠ (2, 2)) (C : ℝ) (hC : 0 < C) :
    ∃ K B₀ : ℝ, 0 < K ∧ ∀ A B : ℝ, B₀ ≤ B → B ^ ((5 : ℝ) / 6) ≤ A → A ≤ B ^ 2 →
      ∀ x y : Fin (n + 1) → ℤ, Work.HP.IsPrim x → Work.HP.IsPrim y →
        LinearIndependent ℤ ![x, y] →
        Work.HP.eNorm x ≤ B ^ (1 / ((n : ℝ) + 1 - d)) →
        (Work.HP.bigW (Work.HP.wOf B) : ℝ) * Work.HP.MM2.lamX d n x ≤ A ^ ((3 : ℝ) / 4) →
        C * (A ^ (Work.HP.NN d n - 3) * Work.HP.MM2.lamX d n x
              * (((Work.HP.gcdMinors2 x y).natAbs : ℕ) : ℝ) / Work.HP.eNorm (Work.HP.veronese d n x))
          ≤ K * (A ^ (Work.HP.NN d n - 2) * Work.HP.ballVol (Work.HP.NN d n - 2)
                * Work.HP.DeltaXY d n x y * (((Work.HP.gcdMinors2 x y).natAbs : ℕ) : ℝ)
                / (Real.log B * (Work.HP.bigW (Work.HP.wOf B) : ℝ)
                    * Work.HP.eNorm (Work.HP.veronese d n x) * Work.HP.MM2.zetaR (Work.HP.NN d n - 2)))
              / Real.log A := by
  classical
  -- Pick `B₀` beyond which `B ≥ 2`, `log B ≥ 2` and `(log B)² ≤ B^{5/24}`.
  obtain ⟨B₀, hB₀⟩ : ∃ B₀ : ℝ, ∀ B : ℝ, B₀ ≤ B →
      (2 : ℝ) ≤ B ∧ (2 : ℝ) ≤ Real.log B ∧ Real.log B ^ 2 ≤ B ^ ((5 : ℝ) / 24) := by
    have h1 : ∀ᶠ B : ℝ in Filter.atTop, (2 : ℝ) ≤ B := Filter.eventually_ge_atTop 2
    have h2 : ∀ᶠ B : ℝ in Filter.atTop, (2 : ℝ) ≤ Real.log B :=
      Real.tendsto_log_atTop.eventually_ge_atTop 2
    have h3 : ∀ᶠ B : ℝ in Filter.atTop, Real.log B ^ 2 ≤ B ^ ((5 : ℝ) / 24) := by
      have hh := eventually_const_mul_log_pow_le_rpow 1 2 (ε := (5 : ℝ) / 24) (by norm_num)
      simpa using hh
    exact Filter.eventually_atTop.mp (h1.and (h2.and h3))
  have hbVpos : 0 < Work.HP.ballVol (Work.HP.NN d n - 2) :=
    Work.HP.MDEstimates.ballVol_pos _ (by have := Work.HP.six_le_NN d n hd hdn; omega)
  refine ⟨4 * C / Work.HP.ballVol (Work.HP.NN d n - 2) + 1, B₀, ?_, ?_⟩
  · have : 0 < 4 * C / Work.HP.ballVol (Work.HP.NN d n - 2) := div_pos (by positivity) hbVpos
    linarith
  · intro A B hBge hA56 hA2 x y hx hy hLI hxn hWlam
    obtain ⟨hB2, hlogB2, hBnd⟩ := hB₀ B hBge
    -- abbreviations
    set N : ℕ := Work.HP.NN d n with hNdef
    have hN6 : 6 ≤ N := by rw [hNdef]; exact Work.HP.six_le_NN d n hd hdn
    have hN3 : 3 ≤ N := by omega
    have hN2 : 2 ≤ N := by omega
    set W : ℝ := (Work.HP.bigW (Work.HP.wOf B) : ℝ) with hWdef
    set E : ℝ := Work.HP.eNorm (Work.HP.veronese d n x) with hEdef
    set L : ℝ := Work.HP.MM2.lamX d n x with hLdef
    set LB : ℝ := Real.log B with hLBdef
    set LA : ℝ := Real.log A with hLAdef
    set z : ℝ := Work.HP.MM2.zetaR (N - 2) with hzdef
    set DV : ℝ := Work.HP.DeltaXY d n x y with hDVdef
    set bV : ℝ := Work.HP.ballVol (N - 2) with hbVdef
    set G : ℝ := (((Work.HP.gcdMinors2 x y).natAbs : ℕ) : ℝ) with hGdef
    set K : ℝ := 4 * C / bV + 1 with hKdef
    -- basic positivity
    have hBpos : 0 < B := by linarith
    have hB1 : 1 < B := by linarith
    have hLBpos : 0 < LB := by rw [hLBdef]; linarith
    have hW1 : 1 ≤ W := by rw [hWdef]; exact_mod_cast Work.HP.one_le_bigW (Work.HP.wOf B)
    have hWpos : 0 < W := lt_of_lt_of_le zero_lt_one hW1
    have hA1lt : 1 < A :=
      lt_of_lt_of_le (Real.one_lt_rpow hB1 (by norm_num : (0 : ℝ) < 5 / 6)) hA56
    have hApos : 0 < A := lt_trans zero_lt_one hA1lt
    have hAnn : 0 ≤ A := hApos.le
    have hLApos : 0 < LA := by rw [hLAdef]; exact Real.log_pos hA1lt
    have hEpos : 0 < E := by
      rw [hEdef]
      exact Work.HP.eNorm_pos_of_ne_zero
        (Work.HP.MDEstimates.veronese_ne_zero (Work.HP.isPrim_ne_zero hx))
    have hzle : z ≤ 2 := by
      rw [hzdef]; exact Work.HP.MM2.zetaR_le_two (N - 2) (by omega)
    have hDV1 : 1 ≤ DV := by
      rw [hDVdef]; exact Work.HP.MM2.one_le_DeltaXY d n hd (by omega) x y hx hy hLI
    have hGnn : 0 ≤ G := by rw [hGdef]; positivity
    have hhbVpos : 0 < bV := by
      rw [hbVdef]; exact Work.HP.MDEstimates.ballVol_pos _ (by omega)
    have hzpos : 0 < z := by
      rw [hzdef]; change 0 < ∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ (N - 2)
      have hm1 : 1 < N - 2 := by omega
      have hsum : Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ (N - 2)) := by
        have h2 : Summable (fun j : ℕ => 1 / ((j : ℕ) : ℝ) ^ (N - 2)) :=
          Real.summable_one_div_nat_pow.mpr hm1
        have h3 := (summable_nat_add_iff (f := fun j : ℕ => 1 / ((j : ℕ) : ℝ) ^ (N - 2)) 1).mpr h2
        refine h3.congr (fun k => ?_)
        simp only [Nat.cast_add, Nat.cast_one]
      exact Summable.tsum_pos hsum (fun k => by positivity) 0 (by norm_num)
    -- the logarithm comparison `log A ≤ 2 log B`
    have hlale : LA ≤ 2 * LB := by
      rw [hLAdef, hLBdef]
      have h1 : Real.log A ≤ Real.log (B ^ 2) := Real.log_le_log hApos hA2
      rw [Real.log_pow] at h1
      norm_num at h1
      linarith
    -- the power comparisons
    have hKbV : 4 * C ≤ K * bV := by
      rw [hKdef]
      have hbb : (4 * C / bV + 1) * bV = 4 * C + bV := by
        rw [add_mul, one_mul, div_mul_cancel₀ _ (ne_of_gt hhbVpos)]
      rw [hbb]; linarith [hhbVpos]
    have hBinv : B ^ (-((5 : ℝ) / 24)) * LB ^ 2 ≤ 1 := by
      have hstep : LB ^ 2 * B ^ (-((5 : ℝ) / 24)) ≤ B ^ ((5 : ℝ) / 24) * B ^ (-((5 : ℝ) / 24)) :=
        mul_le_mul_of_nonneg_right hBnd (Real.rpow_nonneg hBpos.le (-((5 : ℝ) / 24)))
      have he : B ^ ((5 : ℝ) / 24) * B ^ (-((5 : ℝ) / 24)) = 1 := by
        rw [← Real.rpow_add hBpos]
        have : (5 : ℝ) / 24 + (-((5 : ℝ) / 24)) = 0 := by ring
        rw [this, Real.rpow_zero]
      rw [he] at hstep
      nlinarith [hstep]
    have h4C : 4 * C * B ^ (-((5 : ℝ) / 24)) * LB ^ 2 ≤ 4 * C := by
      have h := mul_le_mul_of_nonneg_left hBinv (by positivity : (0 : ℝ) ≤ 4 * C)
      nlinarith [h]
    have hA14 : B ^ ((5 : ℝ) / 24) ≤ A ^ ((1 : ℝ) / 4) := by
      have h1 := Real.rpow_le_rpow (Real.rpow_nonneg hBpos.le ((5 : ℝ) / 6)) hA56
        (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 4)
      rwa [← Real.rpow_mul hBpos.le ((5 : ℝ) / 6) ((1 : ℝ) / 4),
        show (5 : ℝ) / 6 * ((1 : ℝ) / 4) = (5 : ℝ) / 24 by norm_num] at h1
    have hAinv : A ^ (-((1 : ℝ) / 4)) ≤ B ^ (-((5 : ℝ) / 24)) := by
      rw [Real.rpow_neg hAnn, Real.rpow_neg hBpos.le]
      simpa [one_div] using one_div_le_one_div_of_le (Real.rpow_pos_of_pos hBpos _) hA14
    have hLle : L ≤ A ^ ((3 : ℝ) / 4) / W := by
      rw [le_div_iff₀ hWpos, mul_comm]
      exact hWlam
    -- the core inequality, without the factor `G`
    have hcore : C * (A ^ (N - 3) * L / E) ≤ K * (A ^ (N - 2) * bV * DV / (LB * W * E * z)) / LA := by
      have hmid : C * A ^ (-((1 : ℝ) / 4)) * LB * z * LA ≤ K * bV * DV := by
        have h1 : C * A ^ (-((1 : ℝ) / 4)) * LB * z * LA ≤ C * A ^ (-((1 : ℝ) / 4)) * LB * 2 * LA := by
          have h : C * A ^ (-((1 : ℝ) / 4)) * LB * z ≤ C * A ^ (-((1 : ℝ) / 4)) * LB * 2 :=
            mul_le_mul_of_nonneg_left hzle (by positivity)
          exact mul_le_mul_of_nonneg_right h hLApos.le
        have h2 : C * A ^ (-((1 : ℝ) / 4)) * LB * 2 * LA
            ≤ C * A ^ (-((1 : ℝ) / 4)) * LB * 2 * (2 * LB) :=
          mul_le_mul_of_nonneg_left hlale (by positivity)
        have h3 : 4 * C * A ^ (-((1 : ℝ) / 4)) * LB ^ 2 ≤ 4 * C * B ^ (-((5 : ℝ) / 24)) * LB ^ 2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hAinv (by positivity)) (sq_nonneg LB)
        have hKBVnn : 0 ≤ K * bV := le_trans (by positivity : (0 : ℝ) ≤ 4 * C) hKbV
        calc C * A ^ (-((1 : ℝ) / 4)) * LB * z * LA
            ≤ C * A ^ (-((1 : ℝ) / 4)) * LB * 2 * (2 * LB) := le_trans h1 h2
          _ = 4 * C * A ^ (-((1 : ℝ) / 4)) * LB ^ 2 := by ring
          _ ≤ 4 * C * B ^ (-((5 : ℝ) / 24)) * LB ^ 2 := h3
          _ ≤ 4 * C := h4C
          _ ≤ K * bV := hKbV
          _ ≤ K * bV * DV := by simpa using mul_le_mul_of_nonneg_left hDV1 hKBVnn
      have hpow : A ^ (N - 3) * A ^ ((3 : ℝ) / 4) = A ^ (N - 2) * A ^ (-((1 : ℝ) / 4)) := by
        rw [← Real.rpow_natCast A (N - 3), ← Real.rpow_natCast A (N - 2),
            ← Real.rpow_add hApos, ← Real.rpow_add hApos]
        congr 1
        have h1 : ((N - 3 : ℕ) : ℝ) = (N : ℝ) - 3 := by rw [Nat.cast_sub hN3]; norm_num
        have h2 : ((N - 2 : ℕ) : ℝ) = (N : ℝ) - 2 := by rw [Nat.cast_sub hN2]; norm_num
        rw [h1, h2]; ring
      have hX : C * A ^ (N - 3) * A ^ ((3 : ℝ) / 4) * LB * z * LA ≤ K * A ^ (N - 2) * bV * DV := by
        have hgrp : C * A ^ (N - 3) * A ^ ((3 : ℝ) / 4) * LB * z * LA
            = (C * LB * z * LA) * (A ^ (N - 3) * A ^ ((3 : ℝ) / 4)) := by ring
        rw [hgrp, hpow]
        have k1 : (C * LB * z * LA) * (A ^ (N - 2) * A ^ (-((1 : ℝ) / 4)))
            = (C * A ^ (-((1 : ℝ) / 4)) * LB * z * LA) * A ^ (N - 2) := by ring
        have k2 : K * A ^ (N - 2) * bV * DV = (K * bV * DV) * A ^ (N - 2) := by ring
        rw [k1, k2]
        exact mul_le_mul_of_nonneg_right hmid (pow_nonneg hAnn _)
      have hY : C * (A ^ (N - 3) * L / E) ≤ C * A ^ (N - 3) * A ^ ((3 : ℝ) / 4) / (W * E) := by
        have h1 : A ^ (N - 3) * L ≤ A ^ (N - 3) * (A ^ ((3 : ℝ) / 4) / W) :=
          mul_le_mul_of_nonneg_left hLle (by positivity)
        calc C * (A ^ (N - 3) * L / E)
            ≤ C * (A ^ (N - 3) * (A ^ ((3 : ℝ) / 4) / W) / E) :=
              mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right h1 hEpos.le) hC.le
          _ = C * A ^ (N - 3) * A ^ ((3 : ℝ) / 4) / (W * E) := by ring
      have hYR : C * A ^ (N - 3) * A ^ ((3 : ℝ) / 4) / (W * E)
          ≤ K * (A ^ (N - 2) * bV * DV / (LB * W * E * z)) / LA := by
        have hWEpos : 0 < W * E := mul_pos hWpos hEpos
        rw [div_le_iff₀ hWEpos]
        have hLBzLApos : 0 < LB * z * LA := by positivity
        have e : (K * (A ^ (N - 2) * bV * DV / (LB * W * E * z)) / LA) * (W * E)
            = K * A ^ (N - 2) * bV * DV / (LB * z * LA) := by
          field_simp
        rw [e, le_div_iff₀ hLBzLApos]
        have hgoal : C * A ^ (N - 3) * A ^ ((3 : ℝ) / 4) * (LB * z * LA)
            = C * A ^ (N - 3) * A ^ ((3 : ℝ) / 4) * LB * z * LA := by ring
        rw [hgoal]
        exact hX
      exact le_trans hY hYR
    -- multiply the core inequality by the nonnegative factor `G`
    calc C * (A ^ (N - 3) * L * G / E)
        = (C * (A ^ (N - 3) * L / E)) * G := by ring
      _ ≤ (K * (A ^ (N - 2) * bV * DV / (LB * W * E * z)) / LA) * G :=
          mul_le_mul_of_nonneg_right hcore hGnn
      _ = K * (A ^ (N - 2) * bV * DV * G / (LB * W * E * z)) / LA := by ring

end Work.HP.MM2
