import Mathlib
import Submission.Work.FIPiChain.Defs
import Submission.Work.FIChain.measurable_s3halves
import Submission.Work.FIChain.abs_S3minusC_le
import Submission.Work.FIChain.RhoWin2Integrable
import Submission.Work.FITop.SingleDvdTauSqLe
import Submission.Work.FITop.AseqTauEightBound
import Submission.Work.FIPiChain.P3S3.an_le_sq
import Submission.Work.FIPiChain.P3S3.Grho_measurable_t

namespace Work.FIPiChain.P3S3

open Finset MeasureTheory
open scoped BigOperators Interval

attribute [local instance] Classical.propDecidable

noncomputable section

/-
# `Work.FIPiChain.P3S3.Grho_sum_measurable_bdd`

The `W`-integrand of the `ρ`-window estimate, in its dyadic-sum form

`W z = Σ_{j < Jc x B} Grho x C (2^j · z)`,   `C = ⌊(zc x B)^{1-η}⌋`,

is (1) Borel measurable, (2) such that `W z / z` is interval integrable on the window
`[zc x B, e·zc x B]`, and (3) bounded above on that window by a constant.

* (1) is the finite sum of the measurable functions `z ↦ Grho x C (2^j · z)`
  (`Work.FIPiChain.P3S3.Grho_measurable_t` composed with the continuous dilation).
* (3) is `Jc · K_{x,C}`, where `K_{x,C} = ((x+1)^5 (2x+2)^2) · C` uniformly bounds every
  `Grho x C u` (`Grho_point_le` below, valid for every real `u`); no hypothesis on `z` is needed
  for the bound itself, only `1 ≤ C`.
* (2) follows from (1) and (3): on `[zc, e·zc]` one has `z ≥ 1`, so `0 ≤ W z / z ≤ W z ≤ V`, and a
  measurable function bounded on a compact interval is interval integrable
  (`Work.FIChain.intervalIntegrable_of_measurable_on_le`).

The pointwise bound on `Grho` is the only estimate.  Unfolding

`Grho N C t = ∫_1^C (Σ_{m ≤ N} wc m · |XrhoC atilc N m s t (2t)|) / s ds`

one bounds the *numerator* uniformly in `s` and `t` (the window indicator `t < n ≤ 2t` is
discarded), then uses `‖∫_1^C F‖ ≤ K |C - 1|`:
* `|γ(s,n)| ≤ τ(n) ≤ N` (`Work.FIChain.abs_gammaTrunc_le_card`, `Nat.card_divisors_le_self`);
* `|atilc (mn)| ≤ an (mn) ≤ (2mn+1)^2 ≤ (2N+1)^2` (`Work.FITop.atilFIa_le_an`,
  `Work.FIPiChain.P3S3.an_le_sq`) on the filtered range `mn ≤ N`;
* `wc m = τ(m)^2 ≤ m^2 ≤ N^2`.
-/

/-- `|atilc k| ≤ (2k+1)^2`, where `atilc = atilFIa = μ(k)^2 · an k`. -/
private lemma atilc_abs_le_sq (k : ℕ) : |Work.FIChain.atilc k| ≤ (2 * (k : ℝ) + 1) ^ 2 := by
  rw [abs_of_nonneg (Work.FITop.atilFIa_nonneg k)]
  exact (Work.FITop.atilFIa_le_an k).trans (an_le_sq k)

/-- `|gammaTrunc s n| ≤ n`: the truncated Möbius sum has at most `τ(n) ≤ n` terms of modulus
`≤ 1`. -/
private lemma gammaTrunc_abs_le_self (s : ℝ) (n : ℕ) : |Work.FIPlan.gammaTrunc s n| ≤ (n : ℝ) := by
  refine (Work.FIChain.abs_gammaTrunc_le_card s n).trans ?_
  exact_mod_cast Nat.card_divisors_le_self n

/-- `|XrhoC atilc N m s t (2t)| ≤ N^2 (2N+1)^2`, uniformly in `s` and `t`: every term of the
`XrhoC`-sum has `mn ≤ N`. -/
private lemma XrhoC_window_abs_le (N m : ℕ) (s t : ℝ) :
    |Work.FITop.XrhoC Work.FIChain.atilc N m s t (2 * t)|
      ≤ (N : ℝ) * (N : ℝ) * (2 * (N : ℝ) + 1) ^ 2 := by
  rw [Work.FITop.XrhoC]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hle : ∀ n ∈ (Finset.Icc 1 N).filter (fun n => m * n ≤ N),
      |(if t < ((n : ℕ) : ℝ) ∧ ((n : ℕ) : ℝ) ≤ 2 * t
        then Work.FIPlan.gammaTrunc s n * (ArithmeticFunction.moebius (m * n) : ℝ)
          * Work.FIChain.atilc (m * n) else 0)|
        ≤ (N : ℝ) * (2 * (N : ℝ) + 1) ^ 2 := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨hn1, hnN⟩, hmn⟩ := hn
    by_cases hc : t < ((n : ℕ) : ℝ) ∧ ((n : ℕ) : ℝ) ≤ 2 * t
    · rw [if_pos hc, abs_mul, abs_mul]
      have hγ : |Work.FIPlan.gammaTrunc s n| ≤ ((n : ℕ) : ℝ) := gammaTrunc_abs_le_self s n
      have hμ : |(ArithmeticFunction.moebius (m * n) : ℝ)| ≤ 1 := by
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one
      have hã : |Work.FIChain.atilc (m * n)| ≤ (2 * ((m * n : ℕ) : ℝ) + 1) ^ 2 :=
        atilc_abs_le_sq _
      have hmnR : ((m * n : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hmn
      have hnR : ((n : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hnN
      have hstep1 : |Work.FIPlan.gammaTrunc s n| * |(ArithmeticFunction.moebius (m * n) : ℝ)|
            * |Work.FIChain.atilc (m * n)|
          ≤ ((n : ℕ) : ℝ) * 1 * (2 * ((m * n : ℕ) : ℝ) + 1) ^ 2 := by
        have hgn : (0 : ℝ) ≤ ((n : ℕ) : ℝ) := by positivity
        exact mul_le_mul (mul_le_mul hγ hμ (abs_nonneg _) hgn) hã (abs_nonneg _)
          (mul_nonneg hgn zero_le_one)
      have hstep2 : ((n : ℕ) : ℝ) * 1 * (2 * ((m * n : ℕ) : ℝ) + 1) ^ 2
          ≤ (N : ℝ) * 1 * (2 * (N : ℝ) + 1) ^ 2 := by
        have hbase : (2 * ((m * n : ℕ) : ℝ) + 1) ≤ (2 * (N : ℝ) + 1) := by linarith
        have h2 : (2 * ((m * n : ℕ) : ℝ) + 1) ^ 2 ≤ (2 * (N : ℝ) + 1) ^ 2 :=
          pow_le_pow_left₀ (by positivity) hbase 2
        have hle1 : ((n : ℕ) : ℝ) * 1 ≤ (N : ℝ) * 1 :=
          mul_le_mul_of_nonneg_right hnR (by norm_num)
        calc ((n : ℕ) : ℝ) * 1 * (2 * ((m * n : ℕ) : ℝ) + 1) ^ 2
            ≤ ((N : ℝ) * 1) * (2 * ((m * n : ℕ) : ℝ) + 1) ^ 2 :=
              mul_le_mul_of_nonneg_right hle1 (by positivity)
          _ ≤ ((N : ℝ) * 1) * (2 * (N : ℝ) + 1) ^ 2 :=
              mul_le_mul_of_nonneg_left h2 (by positivity)
      calc |Work.FIPlan.gammaTrunc s n| * |(ArithmeticFunction.moebius (m * n) : ℝ)|
              * |Work.FIChain.atilc (m * n)|
          ≤ ((n : ℕ) : ℝ) * 1 * (2 * ((m * n : ℕ) : ℝ) + 1) ^ 2 := hstep1
        _ ≤ (N : ℝ) * 1 * (2 * (N : ℝ) + 1) ^ 2 := hstep2
        _ = (N : ℝ) * (2 * (N : ℝ) + 1) ^ 2 := by ring
    · rw [if_neg hc, abs_zero]
      positivity
  calc ∑ n ∈ (Finset.Icc 1 N).filter (fun n => m * n ≤ N),
          |(if t < ((n : ℕ) : ℝ) ∧ ((n : ℕ) : ℝ) ≤ 2 * t
            then Work.FIPlan.gammaTrunc s n * (ArithmeticFunction.moebius (m * n) : ℝ)
              * Work.FIChain.atilc (m * n) else 0)|
      ≤ ∑ _n ∈ (Finset.Icc 1 N).filter (fun n => m * n ≤ N),
          ((N : ℝ) * (2 * (N : ℝ) + 1) ^ 2) := Finset.sum_le_sum hle
    _ = (((Finset.Icc 1 N).filter (fun n => m * n ≤ N)).card : ℝ)
          * ((N : ℝ) * (2 * (N : ℝ) + 1) ^ 2) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (N : ℝ) * ((N : ℝ) * (2 * (N : ℝ) + 1) ^ 2) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        have hcard : ((Finset.Icc 1 N).filter (fun n => m * n ≤ N)).card ≤ N := by
          calc ((Finset.Icc 1 N).filter (fun n => m * n ≤ N)).card
              ≤ (Finset.Icc 1 N).card := Finset.card_le_card (Finset.filter_subset _ _)
            _ = N := by rw [Nat.card_Icc, Nat.add_sub_cancel]
        exact_mod_cast hcard
    _ = (N : ℝ) * (N : ℝ) * (2 * (N : ℝ) + 1) ^ 2 := by ring

/-- Uniform (in `s` and `t`) bound for the numerator `Σ_{m ≤ N} wc m |XrhoC atilc N m s t (2t)|`. -/
private lemma Grho_num_le (N : ℕ) (s t : ℝ) :
    (∑ m ∈ Finset.Icc 1 N, Work.FIChain.wc m
        * |Work.FITop.XrhoC Work.FIChain.atilc N m s t (2 * t)|)
      ≤ (N : ℝ) ^ 5 * (2 * (N : ℝ) + 1) ^ 2 := by
  have h1 : ∀ m ∈ Finset.Icc 1 N, Work.FIChain.wc m
        * |Work.FITop.XrhoC Work.FIChain.atilc N m s t (2 * t)|
      ≤ (N : ℝ) ^ 2 * ((N : ℝ) * (N : ℝ) * (2 * (N : ℝ) + 1) ^ 2) := by
    intro m hm
    rw [Finset.mem_Icc] at hm
    obtain ⟨hm1, hmN⟩ := hm
    have hmR : (m : ℝ) ≤ (N : ℝ) := by exact_mod_cast hmN
    have hw : Work.FIChain.wc m ≤ (N : ℝ) ^ 2 := by
      rw [Work.FIChain.wc, Work.FITop.w0]
      calc ((m.divisors.card : ℝ)) ^ 2 ≤ (m : ℝ) ^ 2 := by
            refine pow_le_pow_left₀ (by positivity) ?_ 2
            exact_mod_cast Nat.card_divisors_le_self m
        _ ≤ (N : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hmR 2
    exact mul_le_mul hw (XrhoC_window_abs_le N m s t) (abs_nonneg _) (by positivity)
  calc ∑ m ∈ Finset.Icc 1 N, Work.FIChain.wc m
          * |Work.FITop.XrhoC Work.FIChain.atilc N m s t (2 * t)|
      ≤ ∑ _m ∈ Finset.Icc 1 N,
          ((N : ℝ) ^ 2 * ((N : ℝ) * (N : ℝ) * (2 * (N : ℝ) + 1) ^ 2)) :=
        Finset.sum_le_sum h1
    _ = ((Finset.Icc 1 N).card : ℝ)
          * ((N : ℝ) ^ 2 * ((N : ℝ) * (N : ℝ) * (2 * (N : ℝ) + 1) ^ 2)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = (N : ℝ) * ((N : ℝ) ^ 2 * ((N : ℝ) * (N : ℝ) * (2 * (N : ℝ) + 1) ^ 2)) := by
        rw [Nat.card_Icc, Nat.add_sub_cancel]
    _ = (N : ℝ) ^ 5 * (2 * (N : ℝ) + 1) ^ 2 := by ring

/-- Pointwise bound on `Grho`, uniform in `t`. -/
private lemma Grho_point_le (N : ℕ) (C t : ℝ) (hC : 1 ≤ C) :
    Work.FIPiChain.Grho N C t ≤ ((N : ℝ) + 1) ^ 5 * (2 * (N : ℝ) + 2) ^ 2 * C := by
  set K : ℝ := (N : ℝ) ^ 5 * (2 * (N : ℝ) + 1) ^ 2 with hKdef
  have hK0 : 0 ≤ K := by rw [hKdef]; positivity
  have hC0 : 0 ≤ C := le_trans zero_le_one hC
  have hnum : ∀ x ∈ Set.uIoc (1 : ℝ) C,
      ‖(∑ m ∈ Finset.Icc 1 N, Work.FIChain.wc m
          * |Work.FITop.XrhoC Work.FIChain.atilc N m x t (2 * t)|) / x‖ ≤ K := by
    intro x hx
    rw [Set.uIoc_of_le hC] at hx
    have hx1 : 1 ≤ x := le_of_lt hx.1
    have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx1
    have hnn : 0 ≤ ∑ m ∈ Finset.Icc 1 N, Work.FIChain.wc m
        * |Work.FITop.XrhoC Work.FIChain.atilc N m x t (2 * t)| :=
      Finset.sum_nonneg (fun m _ => mul_nonneg (by
        rw [Work.FIChain.wc, Work.FITop.w0]; positivity) (abs_nonneg _))
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hnn hxpos.le), div_le_iff₀ hxpos]
    calc ∑ m ∈ Finset.Icc 1 N, Work.FIChain.wc m
            * |Work.FITop.XrhoC Work.FIChain.atilc N m x t (2 * t)|
        ≤ K := by rw [hKdef]; exact Grho_num_le N x t
      _ = K * 1 := (mul_one K).symm
      _ ≤ K * x := mul_le_mul_of_nonneg_left hx1 hK0
  have hmain := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (1 : ℝ)) (b := C)
    (f := fun x : ℝ => (∑ m ∈ Finset.Icc 1 N, Work.FIChain.wc m
        * |Work.FITop.XrhoC Work.FIChain.atilc N m x t (2 * t)|) / x) hnum
  have hgrho : (∫ x in (1 : ℝ)..C, (∑ m ∈ Finset.Icc 1 N, Work.FIChain.wc m
        * |Work.FITop.XrhoC Work.FIChain.atilc N m x t (2 * t)|) / x)
      = Work.FIPiChain.Grho N C t := rfl
  rw [hgrho, Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ C - 1)] at hmain
  calc Work.FIPiChain.Grho N C t ≤ |Work.FIPiChain.Grho N C t| := le_abs_self _
    _ ≤ K * (C - 1) := hmain
    _ ≤ K * C := by nlinarith [hK0, hC]
    _ ≤ ((N : ℝ) + 1) ^ 5 * (2 * (N : ℝ) + 2) ^ 2 * C := by
        refine mul_le_mul_of_nonneg_right ?_ hC0
        rw [hKdef]
        have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
        have h1 : (N : ℝ) ^ 5 ≤ ((N : ℝ) + 1) ^ 5 :=
          pow_le_pow_left₀ hN0 (by linarith) 5
        have h2 : (2 * (N : ℝ) + 1) ^ 2 ≤ (2 * (N : ℝ) + 2) ^ 2 :=
          pow_le_pow_left₀ (by linarith) (by linarith) 2
        exact mul_le_mul h1 h2 (by positivity) (by positivity)

/-- **Measurability, interval integrability and boundedness of the dyadic `Grho`-sum**
`W z = Σ_{j < Jc x B} Grho x C (2^j z)` on the window `[zc x B, e·zc x B]`. -/
theorem Grho_sum_measurable_bdd (x : ℕ) (B : ℝ) (hx : 1 ≤ x)
    (hzc : 1 ≤ Work.FIChain.zc x B) :
    Measurable (fun z : ℝ => ∑ j ∈ Finset.range (Work.FIChain.Jc x B),
        Work.FIPiChain.Grho x (((⌊(Work.FIChain.zc x B) ^ (1 - Work.FIChain.etac)⌋₊ : ℕ) : ℝ))
          ((2 : ℝ) ^ j * z))
    ∧ IntervalIntegrable (fun z : ℝ => (∑ j ∈ Finset.range (Work.FIChain.Jc x B),
        Work.FIPiChain.Grho x (((⌊(Work.FIChain.zc x B) ^ (1 - Work.FIChain.etac)⌋₊ : ℕ) : ℝ))
          ((2 : ℝ) ^ j * z)) / z)
        MeasureTheory.volume (Work.FIChain.zc x B) (Real.exp 1 * Work.FIChain.zc x B)
    ∧ ∃ V : ℝ, ∀ z ∈ Set.Icc (Work.FIChain.zc x B) (Real.exp 1 * Work.FIChain.zc x B),
        (∑ j ∈ Finset.range (Work.FIChain.Jc x B),
          Work.FIPiChain.Grho x (((⌊(Work.FIChain.zc x B) ^ (1 - Work.FIChain.etac)⌋₊ : ℕ) : ℝ))
            ((2 : ℝ) ^ j * z)) ≤ V := by
  classical
  set C : ℝ := ((⌊(Work.FIChain.zc x B) ^ (1 - Work.FIChain.etac)⌋₊ : ℕ) : ℝ) with hCdef
  set z0 : ℝ := Work.FIChain.zc x B with hz0def
  set J : ℕ := Work.FIChain.Jc x B with hJdef
  have hz01 : 1 ≤ z0 := by rw [hz0def]; exact hzc
  have hz00 : 0 < z0 := lt_of_lt_of_le zero_lt_one hz01
  have hC1 : 1 ≤ C := by
    rw [hCdef]
    have h1 : (1 : ℝ) ≤ (Work.FIChain.zc x B) ^ (1 - Work.FIChain.etac) := by
      refine Real.one_le_rpow hzc ?_
      rw [Work.FIChain.etac]; norm_num
    exact_mod_cast (Nat.one_le_floor_iff (Work.FIChain.zc x B ^ (1 - Work.FIChain.etac))).mpr h1
  set K : ℝ := ((x : ℝ) + 1) ^ 5 * (2 * (x : ℝ) + 2) ^ 2 * C with hKdef
  have hK0 : 0 ≤ K := by rw [hKdef]; positivity
  set V : ℝ := (J : ℝ) * K with hVdef
  have hV0 : 0 ≤ V := by rw [hVdef]; exact mul_nonneg (Nat.cast_nonneg J) hK0
  have hmeas : Measurable (fun z : ℝ => ∑ j ∈ Finset.range J,
      Work.FIPiChain.Grho x C ((2 : ℝ) ^ j * z)) := by
    refine Finset.measurable_sum _ (fun j _ => ?_)
    exact (Grho_measurable_t x C).comp (measurable_const.mul measurable_id)
  have hbdd : ∀ z : ℝ, (∑ j ∈ Finset.range J,
      Work.FIPiChain.Grho x C ((2 : ℝ) ^ j * z)) ≤ V := by
    intro z
    rw [hVdef]
    calc ∑ j ∈ Finset.range J, Work.FIPiChain.Grho x C ((2 : ℝ) ^ j * z)
        ≤ ∑ _j ∈ Finset.range J, K :=
          Finset.sum_le_sum (fun j _ => Grho_point_le x C ((2 : ℝ) ^ j * z) hC1)
      _ = (J : ℝ) * K := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hSnn : ∀ z : ℝ, 0 ≤ ∑ j ∈ Finset.range J,
      Work.FIPiChain.Grho x C ((2 : ℝ) ^ j * z) :=
    fun z => Finset.sum_nonneg (fun j _ => Grho_nonneg x hC1 _)
  have hab : z0 ≤ Real.exp 1 * z0 := by
    have h_exp : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp_iff.mpr (by norm_num)
    nlinarith [hz00]
  refine ⟨hmeas, ?_, ⟨V, fun z _ => hbdd z⟩⟩
  refine Work.FIChain.intervalIntegrable_of_measurable_of_le (M := V) hab
    (hmeas.div measurable_id) ?_
  intro z hz
  have hz1 : 1 ≤ z := le_trans hz01 (le_of_lt hz.1)
  have hzpos : 0 < z := lt_of_lt_of_le zero_lt_one hz1
  rw [abs_of_nonneg (div_nonneg (hSnn z) hzpos.le), div_le_iff₀ hzpos]
  calc ∑ j ∈ Finset.range J, Work.FIPiChain.Grho x C ((2 : ℝ) ^ j * z)
      ≤ V := hbdd z
    _ = V * 1 := (mul_one V).symm
    _ ≤ V * z := mul_le_mul_of_nonneg_left hz1 hV0

end

end Work.FIPiChain.P3S3
