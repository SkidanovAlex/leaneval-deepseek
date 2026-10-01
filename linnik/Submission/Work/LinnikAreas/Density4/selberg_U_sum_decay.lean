import Mathlib
import Submission.Work.LinnikAreas.Density4.SelbergDefs
import Submission.Commons.Analysis.SpecialFunctions.Harmonic.harmonic_log_bounds
import Submission.Work.LinnikAreas.Density4.selU_sub_eq_sum_Ico
import Submission.Work.LinnikAreas.Density4.selU_floor_diff
import Submission.Work.LinnikAreas.Density4.muRecipSum_tail_bound
import Submission.Work.LinnikAreas.Density4.sum_inv_exp_neg_sqrt_log_div
import Submission.Work.LinnikAreas.Density4.selU_conv_sum

namespace Work.LinnikAreas.Density4

open scoped BigOperators
open Finset Filter

noncomputable section

/-! ## The de la Vallée Poussin decay of `muRecipSum` -/

/-- `Σ_{n ≤ x} μ n / n` decays like `exp (-(c √ log x))`. -/
lemma muRecipSum_exp_decay : ∃ K c : ℝ, 0 < c ∧ 0 < K ∧
    ∀ n : ℕ, 1 ≤ n → |Commons.NumberTheory.Moebius.muRecipSum n| ≤
      K * Real.exp (-(c * Real.sqrt (Real.log (n:ℝ)))) := by
  obtain ⟨c, C0, hc, hC0, hdecay⟩ := Commons.NumberTheory.Moebius.moebius_recip_sum_exp_decay
  refine ⟨max C0 1, c, hc, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun n hn => ?_⟩
  exact Commons.NumberTheory.Moebius.muRecipSum_decay hc hC0 hdecay n hn

/-- Uniform bound for `selU` at integer points (`= Σ_{m ≤ N} μ m (log N - log m)/m`). -/
lemma selU_natCast_abs_le : ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N → |selU (N:ℝ)| ≤ C := by
  obtain ⟨C, hC, h⟩ := Commons.NumberTheory.Moebius.log_weighted_moebius_recip_bound
  refine ⟨C, hC, fun N hN => ?_⟩
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  have hfloor : ⌊(N:ℝ)⌋₊ = N := Nat.floor_natCast N
  have heq : selU (N:ℝ)
      = ∑ m ∈ Finset.Icc 1 N,
          (ArithmeticFunction.moebius m : ℝ) * (Real.log (N:ℝ) - Real.log (m:ℝ)) / (m:ℝ) := by
    rw [selU, hfloor]
    apply Finset.sum_congr rfl
    intro m hm
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    have hmpos : (0:ℝ) < m := by exact_mod_cast hm1
    rw [Real.log_div (ne_of_gt hNpos) (ne_of_gt hmpos)]
  rw [heq]
  exact h N hN

/-! ## Rate of convergence of `selU` at integers -/

lemma selU_int_rate : ∃ C c : ℝ, 0 < c ∧ 0 < C ∧
    ∀ N M : ℕ, 2 ≤ N → N ≤ M →
      |selU (M:ℝ) - selU (N:ℝ)| ≤ C * Real.exp (-(c * Real.sqrt (Real.log (N:ℝ)))) := by
  obtain ⟨C1, c1, hc1, hC1, htail⟩ := muRecipSum_tail_bound
  refine ⟨C1, c1, hc1, hC1, ?_⟩
  intro N M hN hNM
  rw [selU_sub_eq_sum_Ico N M (by omega) hNM]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine le_trans (le_of_eq (Finset.sum_congr rfl ?_)) (htail N M hN hNM)
  intro i hi
  have hi1 : 1 ≤ i := le_trans (by omega : 1 ≤ N) (Finset.mem_Ico.mp hi).1
  have hpos : (0:ℝ) < (i:ℝ) := by exact_mod_cast hi1
  have h1 : (1:ℝ) ≤ ((i:ℝ)+1)/(i:ℝ) := by
    rw [le_div_iff₀ hpos]; linarith
  rw [abs_mul, abs_of_nonneg (Real.log_nonneg h1)]

/-! ## Existence of the limit and its rate -/

lemma exists_selU_tendsto :
    ∃ L : ℝ, Tendsto (fun N : ℕ => selU (N:ℝ)) atTop (nhds L) := by
  obtain ⟨C, c, hc, hC, hrate⟩ := selU_int_rate
  have hzero : Tendsto (fun N : ℕ => C * Real.exp (-(c * Real.sqrt (Real.log (N:ℝ)))))
      atTop (nhds 0) := by
    have h1 : Tendsto (fun N : ℕ => Real.sqrt (Real.log (N:ℝ))) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
    have h2 : Tendsto (fun N : ℕ => c * Real.sqrt (Real.log (N:ℝ))) atTop atTop :=
      h1.const_mul_atTop hc
    have h3 : Tendsto (fun N : ℕ => Real.exp (-(c * Real.sqrt (Real.log (N:ℝ)))))
        atTop (nhds 0) := Real.tendsto_exp_neg_atTop_nhds_zero.comp h2
    simpa using h3.const_mul C
  have hcauchy : CauchySeq (fun N : ℕ => selU (N:ℝ)) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N0, hN0⟩ := eventually_atTop.mp
      (hzero.eventually (isOpen_Iio.mem_nhds (show (0:ℝ) ∈ Set.Iio ε from hε)))
    refine ⟨max N0 2, ?_⟩
    intro m hm n hn
    rw [Real.dist_eq]
    have hm2 : 2 ≤ m := le_trans (le_max_right N0 2) hm
    have hn2 : 2 ≤ n := le_trans (le_max_right N0 2) hn
    have hN1 : C * Real.exp (-(c * Real.sqrt (Real.log (((max N0 2 : ℕ)):ℝ)))) < ε :=
      hN0 (max N0 2) (le_max_left N0 2)
    have hkle : (max N0 2 : ℕ) ≤ min m n := le_min hm hn
    have hlogk : Real.log (((max N0 2 : ℕ)):ℝ) ≤ Real.log ((min m n : ℕ):ℝ) :=
      Real.log_le_log (by positivity) (by exact_mod_cast hkle)
    have hsqrt : Real.sqrt (Real.log (((max N0 2 : ℕ)):ℝ))
        ≤ Real.sqrt (Real.log ((min m n : ℕ):ℝ)) := Real.sqrt_le_sqrt hlogk
    have hexp : Real.exp (-(c * Real.sqrt (Real.log ((min m n : ℕ):ℝ))))
        ≤ Real.exp (-(c * Real.sqrt (Real.log (((max N0 2 : ℕ)):ℝ)))) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have hkm : |selU (m:ℝ) - selU (n:ℝ)| ≤
        C * Real.exp (-(c * Real.sqrt (Real.log ((min m n : ℕ):ℝ)))) := by
      rcases le_total m n with hle | hle
      · rw [show min m n = m from min_eq_left hle, abs_sub_comm]
        exact hrate m n hm2 hle
      · rw [show min m n = n from min_eq_right hle]
        exact hrate n m hn2 hle
    exact lt_of_le_of_lt hkm (lt_of_le_of_lt (mul_le_mul_of_nonneg_left hexp hC.le) hN1)
  exact cauchySeq_tendsto_of_complete hcauchy

/-- `selU x` converges, with a quantitative rate, uniformly for real `x ≥ 1`. -/
lemma selU_limit_rate : ∃ L C c : ℝ, 0 < c ∧ 0 < C ∧
    ∀ x : ℝ, 1 ≤ x → |selU x - L| ≤ C * Real.exp (-(c * Real.sqrt (Real.log x))) := by
  obtain ⟨K1, c1, hc1, hK1, hmu'⟩ := muRecipSum_exp_decay
  obtain ⟨C, c, hc, hC, hrate'⟩ := selU_int_rate
  obtain ⟨L, hL⟩ := exists_selU_tendsto
  obtain ⟨Clib, hClib, hlib'⟩ := selU_natCast_abs_le
  have hInt : ∀ y : ℕ, 2 ≤ y →
      |selU (y:ℝ) - L| ≤ C * Real.exp (-(c * Real.sqrt (Real.log (y:ℝ)))) := by
    intro y hy
    have hlim : Tendsto (fun m : ℕ => |selU (m:ℝ) - selU (y:ℝ)|)
        atTop (nhds |L - selU (y:ℝ)|) := by
      have hsub : Tendsto (fun m : ℕ => selU (m:ℝ) - selU (y:ℝ))
          atTop (nhds (L - selU (y:ℝ))) := hL.sub_const _
      have hcomp := (continuous_abs.tendsto (L - selU (y:ℝ))).comp hsub
      rw [Function.comp_def] at hcomp
      exact hcomp
    have hev : ∀ᶠ m : ℕ in atTop,
        |selU (m:ℝ) - selU (y:ℝ)| ≤ C * Real.exp (-(c * Real.sqrt (Real.log (y:ℝ)))) :=
      eventually_atTop.mpr ⟨y, fun m hm => hrate' y m hy hm⟩
    have h := le_of_tendsto hlim hev
    rwa [abs_sub_comm] at h
  have hLbound : |L| ≤ C + Clib := by
    have h2 : |selU ((2:ℕ):ℝ) - L| ≤ C * Real.exp (-(c * Real.sqrt (Real.log ((2:ℕ):ℝ)))) :=
      hInt 2 (by norm_num)
    have h3 : |selU ((2:ℕ):ℝ)| ≤ Clib := hlib' 2 (by norm_num)
    have he : Real.exp (-(c * Real.sqrt (Real.log ((2:ℕ):ℝ)))) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 ≤ Real.log ((2:ℕ):ℝ) := Real.log_nonneg (by norm_num)
      nlinarith [Real.sqrt_nonneg (Real.log ((2:ℕ):ℝ))]
    have h5 : C * Real.exp (-(c * Real.sqrt (Real.log ((2:ℕ):ℝ)))) ≤ C := by
      simpa using mul_le_mul_of_nonneg_left he hC.le
    have h6 : |L| ≤ |selU ((2:ℕ):ℝ) - L| + |selU ((2:ℕ):ℝ)| := by
      have h := abs_sub_le L (selU ((2:ℕ):ℝ)) 0
      rw [sub_zero, abs_sub_comm L (selU ((2:ℕ):ℝ))] at h
      simpa only [sub_zero] using h
    linarith
  set c' : ℝ := min c c1 with hc'def
  have hc'pos : 0 < c' := lt_min hc hc1
  have hc'c : c' ≤ c := min_le_left _ _
  have hc'c1 : c' ≤ c1 := min_le_right _ _
  set C' : ℝ := max ((K1 + C) * Real.exp c')
    ((K1 + C + Clib + Real.log 2) * Real.exp (c' * Real.sqrt (Real.log 2))) with hC'def
  have hC'pos : 0 < C' := lt_of_lt_of_le (mul_pos (by linarith) (Real.exp_pos c')) (le_max_left _ _)
  refine ⟨L, C', c', hc'pos, hC'pos, ?_⟩
  intro x hx
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hN1 : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx : ((1:ℕ):ℝ) ≤ x)
  have hNpos : (0:ℝ) < (⌊x⌋₊:ℕ) := by exact_mod_cast hN1
  have hNle : ((⌊x⌋₊:ℕ):ℝ) ≤ x := Nat.floor_le (by linarith)
  have hx_lt : x < ((⌊x⌋₊:ℕ):ℝ) + 1 := Nat.lt_floor_add_one x
  have hlogratio_nonneg : 0 ≤ Real.log (x/((⌊x⌋₊:ℕ):ℝ)) :=
    Real.log_nonneg (by rw [le_div_iff₀ hNpos]; linarith)
  have hlogratio_le1 : Real.log (x/((⌊x⌋₊:ℕ):ℝ)) ≤ 1 := by
    have hy2 : x/((⌊x⌋₊:ℕ):ℝ) ≤ 2 := by
      rw [div_le_iff₀ hNpos]
      have hNr : (1:ℝ) ≤ ((⌊x⌋₊:ℕ):ℝ) := by exact_mod_cast hN1
      linarith
    have h := Real.log_le_sub_one_of_pos (by positivity : (0:ℝ) < x/((⌊x⌋₊:ℕ):ℝ))
    linarith
  have hdiff := selU_floor_diff x hx
  have hfirst : |selU x - selU ((⌊x⌋₊:ℕ):ℝ)| ≤
      K1 * Real.exp (-(c1 * Real.sqrt (Real.log ((⌊x⌋₊:ℕ):ℝ)))) := by
    rw [hdiff, abs_mul, abs_of_nonneg hlogratio_nonneg]
    have h1 := hmu' ⌊x⌋₊ hN1
    calc |Commons.NumberTheory.Moebius.muRecipSum ⌊x⌋₊| * Real.log (x/((⌊x⌋₊:ℕ):ℝ))
        ≤ (K1 * Real.exp (-(c1 * Real.sqrt (Real.log ((⌊x⌋₊:ℕ):ℝ))))) * 1 :=
          mul_le_mul h1 hlogratio_le1 hlogratio_nonneg (by positivity)
      _ = K1 * Real.exp (-(c1 * Real.sqrt (Real.log ((⌊x⌋₊:ℕ):ℝ)))) := by ring
  rcases le_or_gt 2 ⌊x⌋₊ with hN2 | hNlt
  · have hsecond : |selU ((⌊x⌋₊:ℕ):ℝ) - L| ≤
        C * Real.exp (-(c * Real.sqrt (Real.log ((⌊x⌋₊:ℕ):ℝ)))) := hInt ⌊x⌋₊ hN2
    have hlogNnonneg : 0 ≤ Real.log ((⌊x⌋₊:ℕ):ℝ) := Real.log_nonneg (by exact_mod_cast hN1)
    have htot : |selU x - L| ≤ (K1 + C) * Real.exp (-(c' * Real.sqrt (Real.log ((⌊x⌋₊:ℕ):ℝ)))) := by
      have h3 : K1 * Real.exp (-(c1 * Real.sqrt (Real.log ((⌊x⌋₊:ℕ):ℝ))))
          ≤ K1 * Real.exp (-(c' * Real.sqrt (Real.log ((⌊x⌋₊:ℕ):ℝ)))) :=
        mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (by nlinarith [hc'c1, Real.sqrt_nonneg (Real.log ((⌊x⌋₊:ℕ):ℝ))]))
          hK1.le
      have h4 : C * Real.exp (-(c * Real.sqrt (Real.log ((⌊x⌋₊:ℕ):ℝ))))
          ≤ C * Real.exp (-(c' * Real.sqrt (Real.log ((⌊x⌋₊:ℕ):ℝ)))) :=
        mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (by nlinarith [hc'c, Real.sqrt_nonneg (Real.log ((⌊x⌋₊:ℕ):ℝ))]))
          hC.le
      have h5 := abs_sub_le (selU x) (selU ((⌊x⌋₊:ℕ):ℝ)) L
      have h6 : (K1 + C) * Real.exp (-(c' * Real.sqrt (Real.log ((⌊x⌋₊:ℕ):ℝ))))
          = K1 * Real.exp (-(c' * Real.sqrt (Real.log ((⌊x⌋₊:ℕ):ℝ))))
            + C * Real.exp (-(c' * Real.sqrt (Real.log ((⌊x⌋₊:ℕ):ℝ)))) := by ring
      linarith
    have hlogx : Real.log x ≤ Real.log ((⌊x⌋₊:ℕ):ℝ) + 1 := by
      have hsplit : Real.log x = Real.log ((⌊x⌋₊:ℕ):ℝ) + Real.log (x/((⌊x⌋₊:ℕ):ℝ)) := by
        rw [← Real.log_mul hNpos.ne' (div_ne_zero hxpos.ne' hNpos.ne')]
        congr 1
        field_simp
      rw [hsplit]; linarith
    have hsqrtx : Real.sqrt (Real.log x) ≤ Real.sqrt (Real.log ((⌊x⌋₊:ℕ):ℝ)) + 1 := by
      refine le_trans (Real.sqrt_le_sqrt hlogx) ?_
      rw [Real.sqrt_le_iff]
      refine ⟨by positivity, ?_⟩
      rw [add_sq, Real.sq_sqrt hlogNnonneg, one_pow]
      nlinarith [Real.sqrt_nonneg (Real.log ((⌊x⌋₊:ℕ):ℝ))]
    have hexpconv : Real.exp (-(c' * Real.sqrt (Real.log ((⌊x⌋₊:ℕ):ℝ))))
        ≤ Real.exp c' * Real.exp (-(c' * Real.sqrt (Real.log x))) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [hsqrtx, hc'pos]
    calc |selU x - L| ≤ (K1 + C) * Real.exp (-(c' * Real.sqrt (Real.log ((⌊x⌋₊:ℕ):ℝ)))) := htot
      _ ≤ (K1 + C) * (Real.exp c' * Real.exp (-(c' * Real.sqrt (Real.log x)))) :=
          mul_le_mul_of_nonneg_left hexpconv (by linarith)
      _ = ((K1 + C) * Real.exp c') * Real.exp (-(c' * Real.sqrt (Real.log x))) := by ring
      _ ≤ C' * Real.exp (-(c' * Real.sqrt (Real.log x))) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
  · have hNone : ⌊x⌋₊ = 1 := by omega
    have htot : |selU x - L| ≤ K1 + (C + Clib) := by
      have h1 : |selU x - selU ((⌊x⌋₊:ℕ):ℝ)| ≤ K1 := by
        refine hfirst.trans ?_
        rw [hNone]
        simp
      have h2 : |selU ((⌊x⌋₊:ℕ):ℝ) - L| ≤ C + Clib := by
        rw [hNone]
        have hz : selU ((1:ℕ):ℝ) = 0 := by simp [selU]
        rw [hz, zero_sub, abs_neg]
        exact hLbound
      have h5 := abs_sub_le (selU x) (selU ((⌊x⌋₊:ℕ):ℝ)) L
      linarith
    have hx2 : x < 2 := by
      have := hx_lt; rw [hNone] at this; push_cast at this; linarith
    have hlog2ge : Real.log x ≤ Real.log 2 := Real.log_le_log hxpos (le_of_lt hx2)
    have hsqrt : Real.sqrt (Real.log x) ≤ Real.sqrt (Real.log 2) := Real.sqrt_le_sqrt hlog2ge
    have hexp1 : 1 ≤ Real.exp (c' * Real.sqrt (Real.log 2)) * Real.exp (-(c' * Real.sqrt (Real.log x))) := by
      rw [← Real.exp_add]
      apply Real.one_le_exp
      nlinarith [hsqrt, hc'pos]
    have hnn : 0 ≤ K1 + C + Clib + Real.log 2 := by
      have := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2); linarith
    calc |selU x - L| ≤ K1 + (C + Clib) := htot
      _ ≤ K1 + C + Clib + Real.log 2 := by
          have := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2); linarith
      _ = (K1 + C + Clib + Real.log 2) * 1 := by ring
      _ ≤ (K1 + C + Clib + Real.log 2) *
            (Real.exp (c' * Real.sqrt (Real.log 2)) * Real.exp (-(c' * Real.sqrt (Real.log x)))) :=
          mul_le_mul_of_nonneg_left hexp1 hnn
      _ = ((K1 + C + Clib + Real.log 2) * Real.exp (c' * Real.sqrt (Real.log 2)))
            * Real.exp (-(c' * Real.sqrt (Real.log x))) := by ring
      _ ≤ C' * Real.exp (-(c' * Real.sqrt (Real.log x))) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le

/-! ## The limit is `1` -/

lemma selU_limit_eq_one (L C c : ℝ) (hc : 0 < c) (hC : 0 < C)
    (hrate : ∀ x : ℝ, 1 ≤ x → |selU x - L| ≤ C * Real.exp (-(c * Real.sqrt (Real.log x)))) :
    L = 1 := by
  obtain ⟨K1, hK1, hsum⟩ := sum_inv_exp_neg_sqrt_log_div c hc
  have hmain : ∀ N : ℕ, 2 ≤ N →
      |Real.log (N:ℝ) - L * (∑ n ∈ Finset.Icc 1 N, (1:ℝ)/(n:ℝ))| ≤ C * K1 := by
    intro N hN
    have hN1 : 1 ≤ N := by omega
    have hconv := selU_conv_sum N hN1
    have hsplit : (∑ n ∈ Finset.Icc 1 N, (1/(n:ℝ)) * selU ((N:ℝ)/(n:ℝ)))
        = L * (∑ n ∈ Finset.Icc 1 N, (1:ℝ)/(n:ℝ))
          + ∑ n ∈ Finset.Icc 1 N, (1/(n:ℝ)) * (selU ((N:ℝ)/(n:ℝ)) - L) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro n hn
      ring
    have hbound : |∑ n ∈ Finset.Icc 1 N, (1/(n:ℝ)) * (selU ((N:ℝ)/(n:ℝ)) - L)| ≤ C * K1 := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have hstep : ∀ n ∈ Finset.Icc 1 N,
          |(1/(n:ℝ)) * (selU ((N:ℝ)/(n:ℝ)) - L)|
            ≤ C * ((1/(n:ℝ)) * Real.exp (-(c * Real.sqrt (Real.log ((N:ℝ)/(n:ℝ)))))) := by
        intro n hn
        obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hn
        have hnpos : (0:ℝ) < n := by exact_mod_cast hn1
        have hx1 : (1:ℝ) ≤ (N:ℝ)/(n:ℝ) := by
          rw [le_div_iff₀ hnpos]
          have : (n:ℝ) ≤ (N:ℝ) := by exact_mod_cast hnN
          linarith
        rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1/(n:ℝ))]
        calc (1/(n:ℝ)) * |selU ((N:ℝ)/(n:ℝ)) - L|
            ≤ (1/(n:ℝ)) * (C * Real.exp (-(c * Real.sqrt (Real.log ((N:ℝ)/(n:ℝ)))))) :=
              mul_le_mul_of_nonneg_left (hrate _ hx1) (by positivity)
          _ = C * ((1/(n:ℝ)) * Real.exp (-(c * Real.sqrt (Real.log ((N:ℝ)/(n:ℝ)))))) := by ring
      calc ∑ n ∈ Finset.Icc 1 N, |(1/(n:ℝ)) * (selU ((N:ℝ)/(n:ℝ)) - L)|
          ≤ ∑ n ∈ Finset.Icc 1 N,
              C * ((1/(n:ℝ)) * Real.exp (-(c * Real.sqrt (Real.log ((N:ℝ)/(n:ℝ)))))) :=
            Finset.sum_le_sum hstep
        _ = C * ∑ n ∈ Finset.Icc 1 N,
              (1/(n:ℝ)) * Real.exp (-(c * Real.sqrt (Real.log ((N:ℝ)/(n:ℝ))))) := by
            rw [Finset.mul_sum]
        _ ≤ C * K1 := mul_le_mul_of_nonneg_left (hsum N hN1) hC.le
    rw [hconv] at hsplit
    have heq : Real.log (N:ℝ) - L * (∑ n ∈ Finset.Icc 1 N, (1:ℝ)/(n:ℝ))
        = ∑ n ∈ Finset.Icc 1 N, (1/(n:ℝ)) * (selU ((N:ℝ)/(n:ℝ)) - L) := by linarith
    rw [heq]
    exact hbound
  have hstep2 : ∀ N : ℕ, 2 ≤ N → |1 - L| ≤ (C * K1 + |L|) / Real.log (N:ℝ) := by
    intro N hN
    have hN1 : 1 ≤ N := by omega
    have hlogpos : 0 < Real.log (N:ℝ) := Real.log_pos (by exact_mod_cast hN)
    have hHge : Real.log (N:ℝ) ≤ ∑ n ∈ Finset.Icc 1 N, (1:ℝ)/(n:ℝ) :=
      (Commons.Analysis.SpecialFunctions.Harmonic.harmonic_log_bounds).1 N hN1
    have hHle : (∑ n ∈ Finset.Icc 1 N, (1:ℝ)/(n:ℝ)) ≤ 1 + Real.log (N:ℝ) :=
      (Commons.Analysis.SpecialFunctions.Harmonic.harmonic_log_bounds).2.1 N hN1
    have hHdiff : |(∑ n ∈ Finset.Icc 1 N, (1:ℝ)/(n:ℝ)) - Real.log (N:ℝ)| ≤ 1 := by
      rw [abs_sub_le_iff]
      exact ⟨by linarith, by linarith⟩
    have hm := hmain N hN
    have hident : Real.log (N:ℝ) - L * (∑ n ∈ Finset.Icc 1 N, (1:ℝ)/(n:ℝ))
        = (1 - L) * Real.log (N:ℝ)
          - L * ((∑ n ∈ Finset.Icc 1 N, (1:ℝ)/(n:ℝ)) - Real.log (N:ℝ)) := by ring
    have h2 : |(1 - L) * Real.log (N:ℝ)
        - L * ((∑ n ∈ Finset.Icc 1 N, (1:ℝ)/(n:ℝ)) - Real.log (N:ℝ))| ≤ C * K1 := by
      rw [← hident]; exact hm
    have h3 : |L * ((∑ n ∈ Finset.Icc 1 N, (1:ℝ)/(n:ℝ)) - Real.log (N:ℝ))| ≤ |L| := by
      rw [abs_mul]
      calc |L| * |(∑ n ∈ Finset.Icc 1 N, (1:ℝ)/(n:ℝ)) - Real.log (N:ℝ)|
          ≤ |L| * 1 := mul_le_mul_of_nonneg_left hHdiff (abs_nonneg L)
        _ = |L| := by ring
    have h4 : |(1 - L) * Real.log (N:ℝ)| ≤ C * K1 + |L| := by
      have h5 := abs_add_le ((1 - L) * Real.log (N:ℝ)
          - L * ((∑ n ∈ Finset.Icc 1 N, (1:ℝ)/(n:ℝ)) - Real.log (N:ℝ)))
        (L * ((∑ n ∈ Finset.Icc 1 N, (1:ℝ)/(n:ℝ)) - Real.log (N:ℝ)))
      have h6 : (1 - L) * Real.log (N:ℝ)
            - L * ((∑ n ∈ Finset.Icc 1 N, (1:ℝ)/(n:ℝ)) - Real.log (N:ℝ))
            + L * ((∑ n ∈ Finset.Icc 1 N, (1:ℝ)/(n:ℝ)) - Real.log (N:ℝ))
          = (1 - L) * Real.log (N:ℝ) := by ring
      rw [h6] at h5
      linarith
    have h7 : |1 - L| * Real.log (N:ℝ) = |(1 - L) * Real.log (N:ℝ)| := by
      rw [abs_mul, abs_of_nonneg hlogpos.le]
    have h8 : |1 - L| * Real.log (N:ℝ) ≤ C * K1 + |L| := by
      rw [h7]; exact h4
    rw [le_div_iff₀ hlogpos]
    linarith
  have hlim : Tendsto (fun N : ℕ => (C * K1 + |L|) / Real.log (N:ℝ)) atTop (nhds 0) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_div_atTop (C * K1 + |L|)
  have hev : ∀ᶠ N : ℕ in atTop, |1 - L| ≤ (C * K1 + |L|) / Real.log (N:ℝ) :=
    eventually_atTop.mpr ⟨2, fun N hN => hstep2 N hN⟩
  have hzero : |1 - L| ≤ 0 := ge_of_tendsto hlim hev
  have hz : |1 - L| = 0 := le_antisymm hzero (abs_nonneg _)
  have h1 : 1 - L = 0 := abs_eq_zero.mp hz
  linarith

/-! ## The target -/

theorem selberg_U_sum_decay : ∃ K : ℝ, 0 < K ∧ ∀ z : ℕ, 2 ≤ z →
    (∑ n ∈ Finset.Icc 1 z, (1/(n:ℝ)) * |Work.LinnikAreas.Density4.selU ((z:ℝ)/n) - 1|) ≤ K := by
  obtain ⟨L, C, c, hc, hC, hrate⟩ := selU_limit_rate
  have hL : L = 1 := selU_limit_eq_one L C c hc hC hrate
  obtain ⟨K1, hK1, hsum⟩ := sum_inv_exp_neg_sqrt_log_div c hc
  refine ⟨max (C * K1) 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro z hz
  have hz1 : 1 ≤ z := by omega
  have hsumz := hsum z hz1
  have hstep : ∀ n ∈ Finset.Icc 1 z,
      (1/(n:ℝ)) * |selU ((z:ℝ)/n) - 1|
        ≤ C * ((1/(n:ℝ)) * Real.exp (-(c * Real.sqrt (Real.log ((z:ℝ)/(n:ℝ)))))) := by
    intro n hn
    obtain ⟨hn1, hnz⟩ := Finset.mem_Icc.mp hn
    have hnpos : (0:ℝ) < n := by exact_mod_cast hn1
    have hx1 : (1:ℝ) ≤ (z:ℝ)/(n:ℝ) := by
      rw [le_div_iff₀ hnpos]
      have : (n:ℝ) ≤ (z:ℝ) := by exact_mod_cast hnz
      linarith
    have hr := hrate ((z:ℝ)/(n:ℝ)) hx1
    rw [hL] at hr
    calc (1/(n:ℝ)) * |selU ((z:ℝ)/n) - 1|
        = (1/(n:ℝ)) * |selU ((z:ℝ)/(n:ℝ)) - 1| := by norm_num
      _ ≤ (1/(n:ℝ)) * (C * Real.exp (-(c * Real.sqrt (Real.log ((z:ℝ)/(n:ℝ)))))) :=
          mul_le_mul_of_nonneg_left hr (by positivity)
      _ = C * ((1/(n:ℝ)) * Real.exp (-(c * Real.sqrt (Real.log ((z:ℝ)/(n:ℝ)))))) := by ring
  calc ∑ n ∈ Finset.Icc 1 z, (1/(n:ℝ)) * |selU ((z:ℝ)/n) - 1|
      ≤ ∑ n ∈ Finset.Icc 1 z,
          C * ((1/(n:ℝ)) * Real.exp (-(c * Real.sqrt (Real.log ((z:ℝ)/(n:ℝ)))))) :=
        Finset.sum_le_sum hstep
    _ = C * ∑ n ∈ Finset.Icc 1 z,
          (1/(n:ℝ)) * Real.exp (-(c * Real.sqrt (Real.log ((z:ℝ)/(n:ℝ))))) := by
        rw [Finset.mul_sum]
    _ ≤ C * K1 := mul_le_mul_of_nonneg_left hsumz hC.le
    _ ≤ max (C * K1) 1 := le_max_left _ _

end

end Work.LinnikAreas.Density4
