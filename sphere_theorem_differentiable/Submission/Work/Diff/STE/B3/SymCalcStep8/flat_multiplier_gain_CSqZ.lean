import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.B3.SymCalcStep8.flat_multiplier_gain_no_one
import Submission.Work.Diff.STE.B3.SymCalcStep8.csqZ_neg_le_of_adjoint
import Submission.Work.Diff.STE.B3.SymCalcStep8.CSqZ
import Submission.Work.Diff.STE.B3.SymCalcStep8.lapPow_mul_comm_CSqZ_le
import Submission.Work.Diff.STE.B3.SymCalcStep1.friedrichs_pointwise_nosupp

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.B3.SymCalcStep8

/-!
# The flat multiplier commutator at **integer** exponents

`Work.Diff.STE.B3.SymCalcStep8.flat_multiplier_gain_no_one` proves the one-derivative gain of the
Friedrichs commutator `β · S_ε h - S_ε (β · h)` on the *positive* Sobolev levels: for `t : ℕ`,

  `CSq (t + 1) (fourierCoeff (β · S_ε h - S_ε (β · h))) ≤ C CSq t (fourierCoeff h)`.

The target of this file, `flat_multiplier_gain_CSqZ`, extends it to **every integer** exponent
`t ∈ ℤ`, with the same one-level gain in the `CSqZ` scale,

  `CSqZ t (fourierCoeff (β · S_ε h - S_ε (β · h))) ≤ C CSqZ (t - 1) (fourierCoeff h)`,

with a constant independent of `ε ∈ (0,1]` and of the smooth `1`-periodic `h`:

* for `t ≥ 1` this is `flat_multiplier_gain_no_one` at the index `t - 1`, read through
  `CSqZ_natCast`;
* for `t ≤ 0` it is the coefficient-level estimate `flat_multiplier_commutator_CSqZ_neg_aux`
  (proved below) applied to the family `c = fourierCoeff h`, using the two Fourier-coefficient
  identities `fourierCoeff_mul_flatCut` / `fourierCoeff_flatCut_mul`.

The pointwise content of the coefficient-level estimate is the Friedrichs bound
`friedrichs_pointwise_nosupp` (`wt (k-l) * (ρ (ε(k-l)) - ρ (ε k))² ≤ 64 (1+L²) wt l`), which for
`t ≤ 0` is combined with the two-sided Peetre inequality `wt_zpow_le` (with the *lower* bound
`wt k ≥ wt (k-l)/(2 wt l)`, the correct direction for `t ≤ 0`), the weighted Cauchy-Schwarz
`tsum_mul_sq_le` and the discrete Tonelli identity `summable_conv_nonneg_tsum`.
-/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma flat_summable_norm_mul_sq (a c : (ι → ℤ) → ℂ) (ha0 : Summable fun l => ‖a l‖)
    (hc2 : Summable fun m => ‖c m‖ ^ 2) (k : ι → ℤ) :
    Summable fun l => ‖a l‖ * ‖c (k - l)‖ ^ 2 := by
  have hb : ∀ l, ‖a l‖ ≤ ∑' l : ι → ℤ, ‖a l‖ :=
    fun l => ha0.le_tsum l (fun _ _ => norm_nonneg _)
  have hmaj : Summable fun l : ι → ℤ => (∑' l : ι → ℤ, ‖a l‖) * ‖c (k - l)‖ ^ 2 :=
    ((summable_sub_reflect (fun m => ‖c m‖ ^ 2) k).mpr hc2).mul_left _
  exact Summable.of_nonneg_of_le (fun l => mul_nonneg (norm_nonneg _) (sq_nonneg _))
    (fun l => mul_le_mul_of_nonneg_right (hb l) (sq_nonneg _)) hmaj

theorem flat_multiplier_commutator_CSqZ_neg_aux
    (ρ : (ι → ℝ) → ℝ) (hρb : ∀ y : ι → ℝ, ‖ρ y‖ ≤ 1)
    (hdiam : ∀ y : ι → ℝ, 2 < ∑ i, (y i) ^ 2 → ρ y = 0)
    (L : ℝ) (hL : 0 ≤ L) (hρlip : ∀ y z : ι → ℝ, ‖ρ y - ρ z‖ ≤ L * ‖y - z‖)
    (a : (ι → ℤ) → ℂ) (ha : RapidL1 a)
    (t : ℤ) (ht : t ≤ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ε : ℝ), 0 < ε → ε ≤ 1 → ∀ c : (ι → ℤ) → ℂ,
      Rapid c →
      CSqZ t (fun k => Work.Diff.STE.conv a (Work.Diff.STE.trunc ρ ε c) k
            - Work.Diff.STE.trunc ρ ε (Work.Diff.STE.conv a c) k)
        ≤ C * CSqZ (t - 1) c := by
  classical
  set Kk : ℝ := 64 * (1 + L ^ 2) with hKk
  have hKknn : 0 ≤ Kk := by rw [hKk]; positivity
  have ha0 : Summable fun l : ι → ℤ => ‖a l‖ := by simpa using ha 0
  set A : ℝ := ∑' l : ι → ℤ, ‖a l‖ with hA
  have hAnn : 0 ≤ A := by rw [hA]; exact tsum_nonneg fun l => norm_nonneg _
  set B : ℝ := ∑' l : ι → ℤ, (Work.Diff.STE.wt l) ^ (1 - t) * ‖a l‖ with hB
  have hBnn : 0 ≤ B := by
    rw [hB]
    exact tsum_nonneg fun l => mul_nonneg (zpow_nonneg (le_of_lt (Work.Diff.STE.wt_pos l)) _)
      (norm_nonneg _)
  have hnat : (((t.natAbs : ℕ) : ℤ)) = -t := by
    rw [← Int.natAbs_neg t]
    exact Int.natAbs_of_nonneg (by omega : (0 : ℤ) ≤ -t)
  refine ⟨A * 2 ^ (-t) * Kk * B, by positivity, ?_⟩
  intro ε hε hε1 c hc
  have hc2 : Summable fun m : ι → ℤ => ‖c m‖ ^ 2 := by simpa using hc 0
  have hconvnorm : ∀ k : ι → ℤ, Summable fun l : ι → ℤ => ‖a l‖ * ‖c (k - l)‖ := by
    intro k
    have h := summable_conv_rapid a c ha hc k 0 0
    simpa using h
  have hsq : ∀ k : ι → ℤ, Summable fun l : ι → ℤ => ‖a l‖ * ‖c (k - l)‖ ^ 2 :=
    fun k => flat_summable_norm_mul_sq a c ha0 hc2 k
  have hconvsm : ∀ k : ι → ℤ, Summable fun l : ι → ℤ => a l * c (k - l) := by
    intro k
    refine Summable.of_norm_bounded (hconvnorm k) (fun l => ?_)
    rw [norm_mul]
  -- the difference of the two profile values
  have hbdd : ∀ k l : ι → ℤ,
      |ρ (ε • fun i => ((k - l) i : ℝ)) - ρ (ε • fun i => (k i : ℝ))| ≤ 2 := by
    intro k l
    have h1' : |ρ (ε • fun i => ((k - l) i : ℝ))| ≤ 1 := by
      have h := hρb (ε • fun i => ((k - l) i : ℝ)); rwa [Real.norm_eq_abs] at h
    have h2' : |ρ (ε • fun i => (k i : ℝ))| ≤ 1 := by
      have h := hρb (ε • fun i => (k i : ℝ)); rwa [Real.norm_eq_abs] at h
    rw [abs_le] at h1' h2' ⊢
    constructor <;> linarith [h1'.1, h1'.2, h2'.1, h2'.2]
  have hdiff : ∀ k l : ι → ℤ, ‖((ρ (ε • fun i => ((k - l) i : ℝ))
        - ρ (ε • fun i => (k i : ℝ)) : ℝ) : ℂ)‖
      = |ρ (ε • fun i => ((k - l) i : ℝ)) - ρ (ε • fun i => (k i : ℝ))| := by
    intro k l
    rw [Complex.norm_real, Real.norm_eq_abs]
  -- (i) the pointwise identity for the commutator family
  have hQeq : ∀ k : ι → ℤ, Work.Diff.STE.conv a (Work.Diff.STE.trunc ρ ε c) k
        - Work.Diff.STE.trunc ρ ε (Work.Diff.STE.conv a c) k
      = ∑' l : ι → ℤ, a l * ((((ρ (ε • fun i => ((k - l) i : ℝ)))
          - ρ (ε • fun i => (k i : ℝ)) : ℝ) : ℂ) * c (k - l)) := by
    intro k
    set φ : (ι → ℤ) → ℂ := fun m => ((ρ (ε • fun i => (m i : ℝ)) : ℝ) : ℂ) with hφ
    have hφ1 : ∀ m, ‖φ m‖ ≤ 1 := by
      intro m
      rw [hφ, Complex.norm_real, Real.norm_eq_abs]
      exact hρb _
    have h1 : Summable fun l : ι → ℤ => a l * (φ (k - l) * c (k - l)) := by
      refine Summable.of_norm_bounded (hconvnorm k) (fun l => ?_)
      rw [norm_mul, norm_mul]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      calc ‖φ (k - l)‖ * ‖c (k - l)‖ ≤ 1 * ‖c (k - l)‖ :=
            mul_le_mul_of_nonneg_right (hφ1 (k - l)) (norm_nonneg _)
        _ = ‖c (k - l)‖ := one_mul _
    have h2 : Summable fun l : ι → ℤ => φ k * (a l * c (k - l)) :=
      (hconvsm k).mul_left _
    have hconv1 : Work.Diff.STE.conv a (Work.Diff.STE.trunc ρ ε c) k
        = ∑' l : ι → ℤ, a l * (φ (k - l) * c (k - l)) := by
      simp only [Work.Diff.STE.conv, Work.Diff.STE.trunc, hφ]
    have hconv2 : Work.Diff.STE.trunc ρ ε (Work.Diff.STE.conv a c) k
        = ∑' l : ι → ℤ, φ k * (a l * c (k - l)) := by
      rw [Work.Diff.STE.trunc, Work.Diff.STE.conv]
      simp only [hφ]
      rw [tsum_mul_left]
    rw [hconv1, hconv2, ← Summable.tsum_sub h1 h2]
    refine tsum_congr fun l => ?_
    rw [hφ, Complex.ofReal_sub]
    ring
  -- (ii) the norm bound
  have hQnorm : ∀ k : ι → ℤ, ‖Work.Diff.STE.conv a (Work.Diff.STE.trunc ρ ε c) k
        - Work.Diff.STE.trunc ρ ε (Work.Diff.STE.conv a c) k‖
      ≤ ∑' l : ι → ℤ, ‖a l‖ * (|ρ (ε • fun i => ((k - l) i : ℝ))
          - ρ (ε • fun i => (k i : ℝ))| * ‖c (k - l)‖) := by
    intro k
    rw [hQeq k]
    have habs : Summable fun l : ι → ℤ => ‖a l * ((((ρ (ε • fun i => ((k - l) i : ℝ)))
          - ρ (ε • fun i => (k i : ℝ)) : ℝ) : ℂ) * c (k - l))‖ := by
      refine Summable.of_nonneg_of_le (fun l => norm_nonneg _) (fun l => ?_)
        ((hconvnorm k).mul_left 2)
      rw [norm_mul, norm_mul, hdiff k l]
      calc ‖a l‖ * (|ρ (ε • fun i => ((k - l) i : ℝ)) - ρ (ε • fun i => (k i : ℝ))|
              * ‖c (k - l)‖)
          ≤ ‖a l‖ * (2 * ‖c (k - l)‖) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right (hbdd k l) (norm_nonneg (c (k - l))))
              (norm_nonneg (a l))
        _ = 2 * (‖a l‖ * ‖c (k - l)‖) := by ring
    have hnt : ‖∑' l : ι → ℤ, a l * ((((ρ (ε • fun i => ((k - l) i : ℝ)))
          - ρ (ε • fun i => (k i : ℝ)) : ℝ) : ℂ) * c (k - l))‖
        ≤ ∑' l : ι → ℤ, ‖a l * ((((ρ (ε • fun i => ((k - l) i : ℝ)))
          - ρ (ε • fun i => (k i : ℝ)) : ℝ) : ℂ) * c (k - l))‖ :=
      norm_tsum_le_tsum_norm habs
    refine hnt.trans (le_of_eq (tsum_congr fun l => ?_))
    rw [norm_mul, norm_mul, hdiff k l]
  -- (iii) the pointwise weighted bound
  have hstar : ∀ k l : ι → ℤ, (Work.Diff.STE.wt k) ^ t
      * (ρ (ε • fun i => ((k - l) i : ℝ)) - ρ (ε • fun i => (k i : ℝ))) ^ 2
      ≤ 2 ^ (-t) * Kk * (Work.Diff.STE.wt l) ^ (1 - t)
          * (Work.Diff.STE.wt (k - l)) ^ (t - 1) := by
    intro k l
    have hpt := Work.Diff.STE.B3.SymCalcStep1.friedrichs_pointwise_nosupp
      ρ hρb hdiam L hL hρlip ε hε hε1 k (k - l)
    rw [sub_sub_self] at hpt
    have hpe : (Work.Diff.STE.wt k) ^ t
        ≤ 2 ^ (-t) * ((Work.Diff.STE.wt l) ^ (-t) * (Work.Diff.STE.wt (k - l)) ^ t) := by
      have h := wt_zpow_le k l t
      rw [← zpow_natCast (2 : ℝ) t.natAbs, ← zpow_natCast (Work.Diff.STE.wt l) t.natAbs] at h
      rwa [hnat] at h
    have hwl : (0 : ℝ) < Work.Diff.STE.wt l := Work.Diff.STE.wt_pos l
    have hwp : (0 : ℝ) < Work.Diff.STE.wt (k - l) := Work.Diff.STE.wt_pos (k - l)
    have hD : (0 : ℝ) ≤ (ρ (ε • fun i => ((k - l) i : ℝ))
        - ρ (ε • fun i => (k i : ℝ))) ^ 2 := sq_nonneg _
    have h1 : (Work.Diff.STE.wt (k - l)) ^ t
        = (Work.Diff.STE.wt (k - l)) ^ (t - 1) * (Work.Diff.STE.wt (k - l)) := by
      rw [← zpow_add_one₀ (ne_of_gt hwp)]
      congr 1
      ring
    have h2 : (Work.Diff.STE.wt l) ^ (-t) * (Work.Diff.STE.wt l)
        = (Work.Diff.STE.wt l) ^ (1 - t) := by
      rw [← zpow_add_one₀ (ne_of_gt hwl)]
      congr 1
      ring
    rw [hKk]
    calc (Work.Diff.STE.wt k) ^ t
          * (ρ (ε • fun i => ((k - l) i : ℝ)) - ρ (ε • fun i => (k i : ℝ))) ^ 2
        ≤ (2 ^ (-t) * ((Work.Diff.STE.wt l) ^ (-t) * (Work.Diff.STE.wt (k - l)) ^ t))
            * (ρ (ε • fun i => ((k - l) i : ℝ)) - ρ (ε • fun i => (k i : ℝ))) ^ 2 :=
          mul_le_mul_of_nonneg_right hpe hD
      _ = 2 ^ (-t) * (Work.Diff.STE.wt l) ^ (-t)
            * ((Work.Diff.STE.wt (k - l)) ^ t
              * (ρ (ε • fun i => ((k - l) i : ℝ)) - ρ (ε • fun i => (k i : ℝ))) ^ 2) := by
          ring
      _ = 2 ^ (-t) * (Work.Diff.STE.wt l) ^ (-t)
            * (((Work.Diff.STE.wt (k - l)) ^ (t - 1) * (Work.Diff.STE.wt (k - l)))
              * (ρ (ε • fun i => ((k - l) i : ℝ)) - ρ (ε • fun i => (k i : ℝ))) ^ 2) := by
          rw [← h1]
      _ = 2 ^ (-t) * (Work.Diff.STE.wt l) ^ (-t)
            * ((Work.Diff.STE.wt (k - l)) ^ (t - 1)
              * ((Work.Diff.STE.wt (k - l))
                * (ρ (ε • fun i => ((k - l) i : ℝ)) - ρ (ε • fun i => (k i : ℝ))) ^ 2)) := by
          ring
      _ ≤ 2 ^ (-t) * (Work.Diff.STE.wt l) ^ (-t)
            * ((Work.Diff.STE.wt (k - l)) ^ (t - 1) * (64 * (1 + L ^ 2) * Work.Diff.STE.wt l)) := by
          refine mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hpt (zpow_nonneg (le_of_lt hwp) _))
            (mul_nonneg (by positivity) (zpow_nonneg (le_of_lt hwl) _))
      _ = 2 ^ (-t) * 64 * (1 + L ^ 2) * ((Work.Diff.STE.wt l) ^ (-t)
            * (Work.Diff.STE.wt l)) * (Work.Diff.STE.wt (k - l)) ^ (t - 1) := by
          ring
      _ = 2 ^ (-t) * (64 * (1 + L ^ 2)) * (Work.Diff.STE.wt l) ^ (1 - t)
            * (Work.Diff.STE.wt (k - l)) ^ (t - 1) := by
          rw [h2]
          ring
  -- (iv) the assembly
  set bn : (ι → ℤ) → ℝ := fun l => (Work.Diff.STE.wt l) ^ (1 - t) * ‖a l‖ with hbn
  set an : (ι → ℤ) → ℝ := fun m => (Work.Diff.STE.wt m) ^ (t - 1) * ‖c m‖ ^ 2 with han
  have hbn_nn : ∀ l, 0 ≤ bn l := fun l =>
    mul_nonneg (zpow_nonneg (le_of_lt (Work.Diff.STE.wt_pos l)) _) (norm_nonneg _)
  have han_nn : ∀ m, 0 ≤ an m := fun m =>
    mul_nonneg (zpow_nonneg (le_of_lt (Work.Diff.STE.wt_pos m)) _) (sq_nonneg _)
  have hbn_sum : Summable bn := by
    rw [hbn]; exact RapidL1.summable_zpow a ha (1 - t)
  have han_sum : Summable an := by
    rw [han]; exact Rapid.summable_zpow c hc (t - 1)
  obtain ⟨hAf_inner, hAf_sum, hAf_id⟩ :=
    summable_conv_nonneg_tsum an bn han_nn hbn_nn han_sum hbn_sum
  -- the pointwise step
  have hstep : ∀ k : ι → ℤ, (Work.Diff.STE.wt k) ^ t
        * ‖Work.Diff.STE.conv a (Work.Diff.STE.trunc ρ ε c) k
          - Work.Diff.STE.trunc ρ ε (Work.Diff.STE.conv a c) k‖ ^ 2
      ≤ A * 2 ^ (-t) * Kk * (∑' l : ι → ℤ, an (k - l) * bn l) := by
    intro k
    -- Cauchy-Schwarz on the frequency side
    have hcs := Work.Diff.STE.tsum_mul_sq_le (fun l : ι → ℤ => ‖a l‖)
      (fun l : ι → ℤ => |ρ (ε • fun i => ((k - l) i : ℝ)) - ρ (ε • fun i => (k i : ℝ))|
        * ‖c (k - l)‖)
      (fun l => norm_nonneg _) (fun l => mul_nonneg (abs_nonneg _) (norm_nonneg _))
      ha0 (by
        refine Summable.of_nonneg_of_le (fun l => mul_nonneg (norm_nonneg _) (sq_nonneg _))
          (fun l => ?_) ((hsq k).mul_left 4)
        calc ‖a l‖ * (|ρ (ε • fun i => ((k - l) i : ℝ)) - ρ (ε • fun i => (k i : ℝ))|
              * ‖c (k - l)‖) ^ 2
            ≤ ‖a l‖ * (2 * ‖c (k - l)‖) ^ 2 :=
              mul_le_mul_of_nonneg_left
                (pow_le_pow_left₀ (mul_nonneg (abs_nonneg _) (norm_nonneg _))
                  (mul_le_mul_of_nonneg_right (hbdd k l) (norm_nonneg _)) 2) (norm_nonneg _)
          _ = 4 * (‖a l‖ * ‖c (k - l)‖ ^ 2) := by ring)
    have hkey1 : (∑' l : ι → ℤ, ‖a l‖
          * (|ρ (ε • fun i => ((k - l) i : ℝ)) - ρ (ε • fun i => (k i : ℝ))|
            * ‖c (k - l)‖)) ^ 2
        ≤ A * ∑' l : ι → ℤ, ‖a l‖
            * (ρ (ε • fun i => ((k - l) i : ℝ)) - ρ (ε • fun i => (k i : ℝ))) ^ 2
            * ‖c (k - l)‖ ^ 2 := by
      rw [← hA] at hcs
      refine hcs.trans (le_of_eq ?_)
      congr 1
      exact tsum_congr fun l => by rw [mul_pow, sq_abs]; ring
    have hQ2 : ‖Work.Diff.STE.conv a (Work.Diff.STE.trunc ρ ε c) k
          - Work.Diff.STE.trunc ρ ε (Work.Diff.STE.conv a c) k‖ ^ 2
        ≤ A * ∑' l : ι → ℤ, ‖a l‖
            * (ρ (ε • fun i => ((k - l) i : ℝ)) - ρ (ε • fun i => (k i : ℝ))) ^ 2
            * ‖c (k - l)‖ ^ 2 :=
      (pow_le_pow_left₀ (norm_nonneg _) (hQnorm k) 2).trans hkey1
    have h4 : ∀ l, (ρ (ε • fun i => ((k - l) i : ℝ))
        - ρ (ε • fun i => (k i : ℝ))) ^ 2 ≤ 4 := by
      intro l
      have h := pow_le_pow_left₀ (abs_nonneg (ρ (ε • fun i => ((k - l) i : ℝ))
        - ρ (ε • fun i => (k i : ℝ)))) (hbdd k l) 2
      rw [sq_abs] at h
      nlinarith [h]
    have hmaj : Summable fun l : ι → ℤ => (Work.Diff.STE.wt k) ^ t * (‖a l‖
          * (ρ (ε • fun i => ((k - l) i : ℝ)) - ρ (ε • fun i => (k i : ℝ))) ^ 2
          * ‖c (k - l)‖ ^ 2) := by
      have hnn : ∀ l, 0 ≤ (Work.Diff.STE.wt k) ^ t * (‖a l‖
            * (ρ (ε • fun i => ((k - l) i : ℝ)) - ρ (ε • fun i => (k i : ℝ))) ^ 2
            * ‖c (k - l)‖ ^ 2) := fun l =>
        mul_nonneg (zpow_nonneg (le_of_lt (Work.Diff.STE.wt_pos k)) _)
          (mul_nonneg (mul_nonneg (norm_nonneg _) (sq_nonneg _)) (sq_nonneg _))
      have hle : ∀ l, (Work.Diff.STE.wt k) ^ t * (‖a l‖
            * (ρ (ε • fun i => ((k - l) i : ℝ)) - ρ (ε • fun i => (k i : ℝ))) ^ 2
            * ‖c (k - l)‖ ^ 2)
          ≤ (4 * (Work.Diff.STE.wt k) ^ t) * (‖a l‖ * ‖c (k - l)‖ ^ 2) := by
        intro l
        have hwk : (0 : ℝ) ≤ (Work.Diff.STE.wt k) ^ t :=
          zpow_nonneg (le_of_lt (Work.Diff.STE.wt_pos k)) _
        calc (Work.Diff.STE.wt k) ^ t * (‖a l‖
              * (ρ (ε • fun i => ((k - l) i : ℝ)) - ρ (ε • fun i => (k i : ℝ))) ^ 2
              * ‖c (k - l)‖ ^ 2)
            ≤ (Work.Diff.STE.wt k) ^ t * (‖a l‖ * 4 * ‖c (k - l)‖ ^ 2) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left (h4 l) (norm_nonneg _)) (sq_nonneg _)) hwk
          _ = (4 * (Work.Diff.STE.wt k) ^ t) * (‖a l‖ * ‖c (k - l)‖ ^ 2) := by ring
      exact Summable.of_nonneg_of_le hnn hle ((hsq k).mul_left _)
    have hbnd2 : Summable fun l : ι → ℤ => 2 ^ (-t) * Kk * (bn l * an (k - l)) := by
      have hbase : Summable fun l : ι → ℤ => bn l * an (k - l) :=
        Summable.congr (hAf_inner k) (fun m => by rw [mul_comm])
      exact hbase.mul_left _
    have hbnd2' : Summable fun l : ι → ℤ => (Work.Diff.STE.wt k) ^ t
        * (‖a l‖ * (ρ (ε • fun i => ((k - l) i : ℝ))
            - ρ (ε • fun i => (k i : ℝ))) ^ 2 * ‖c (k - l)‖ ^ 2) := hmaj
    have hT : (Work.Diff.STE.wt k) ^ t * (A * ∑' l : ι → ℤ, ‖a l‖
            * (ρ (ε • fun i => ((k - l) i : ℝ)) - ρ (ε • fun i => (k i : ℝ))) ^ 2
            * ‖c (k - l)‖ ^ 2)
        = A * ∑' l : ι → ℤ, (Work.Diff.STE.wt k) ^ t * (‖a l‖
            * (ρ (ε • fun i => ((k - l) i : ℝ)) - ρ (ε • fun i => (k i : ℝ))) ^ 2
            * ‖c (k - l)‖ ^ 2) := by
      rw [tsum_mul_left]
      ring
    have hstep2 : A * ∑' l : ι → ℤ, (Work.Diff.STE.wt k) ^ t * (‖a l‖
            * (ρ (ε • fun i => ((k - l) i : ℝ)) - ρ (ε • fun i => (k i : ℝ))) ^ 2
            * ‖c (k - l)‖ ^ 2)
        ≤ A * ∑' l : ι → ℤ, 2 ^ (-t) * Kk * (bn l * an (k - l)) := by
      refine mul_le_mul_of_nonneg_left ?_ hAnn
      refine Summable.tsum_le_tsum (fun l => ?_) hmaj (hbnd2.congr (fun l => by ring))
      rw [hbn, han]
      calc (Work.Diff.STE.wt k) ^ t * (‖a l‖
            * (ρ (ε • fun i => ((k - l) i : ℝ)) - ρ (ε • fun i => (k i : ℝ))) ^ 2
            * ‖c (k - l)‖ ^ 2)
          = ‖a l‖ * ((Work.Diff.STE.wt k) ^ t
              * (ρ (ε • fun i => ((k - l) i : ℝ)) - ρ (ε • fun i => (k i : ℝ))) ^ 2)
              * ‖c (k - l)‖ ^ 2 := by ring
        _ ≤ ‖a l‖ * (2 ^ (-t) * Kk * (Work.Diff.STE.wt l) ^ (1 - t)
              * (Work.Diff.STE.wt (k - l)) ^ (t - 1)) * ‖c (k - l)‖ ^ 2 := by
            refine mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (hstar k l) (norm_nonneg _)) (sq_nonneg _)
        _ = 2 ^ (-t) * Kk * (((Work.Diff.STE.wt l) ^ (1 - t) * ‖a l‖)
              * ((Work.Diff.STE.wt (k - l)) ^ (t - 1) * ‖c (k - l)‖ ^ 2)) := by ring
    calc (Work.Diff.STE.wt k) ^ t
          * ‖Work.Diff.STE.conv a (Work.Diff.STE.trunc ρ ε c) k
            - Work.Diff.STE.trunc ρ ε (Work.Diff.STE.conv a c) k‖ ^ 2
        ≤ (Work.Diff.STE.wt k) ^ t * (A * ∑' l : ι → ℤ, ‖a l‖
            * (ρ (ε • fun i => ((k - l) i : ℝ)) - ρ (ε • fun i => (k i : ℝ))) ^ 2
            * ‖c (k - l)‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hQ2 (zpow_nonneg (le_of_lt (Work.Diff.STE.wt_pos k)) _)
      _ = A * ∑' l : ι → ℤ, (Work.Diff.STE.wt k) ^ t * (‖a l‖
            * (ρ (ε • fun i => ((k - l) i : ℝ)) - ρ (ε • fun i => (k i : ℝ))) ^ 2
            * ‖c (k - l)‖ ^ 2) := hT
      _ ≤ A * ∑' l : ι → ℤ, 2 ^ (-t) * Kk * (bn l * an (k - l)) := hstep2
      _ = A * 2 ^ (-t) * Kk * (∑' l : ι → ℤ, an (k - l) * bn l) := by
          rw [tsum_mul_left]
          have hcomm : (∑' l : ι → ℤ, bn l * an (k - l)) = ∑' l : ι → ℤ, an (k - l) * bn l :=
            tsum_congr fun l => by ring
          rw [hcomm]; ring
  -- the final assembly
  have han_eq : (∑' m : ι → ℤ, an m) = CSqZ (t - 1) c := by
    simp only [han, CSqZ]
  have hbn_eq : (∑' l : ι → ℤ, bn l) = B := by
    simp only [hbn]
    exact hB.symm
  have hQS : Summable fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ t
      * ‖Work.Diff.STE.conv a (Work.Diff.STE.trunc ρ ε c) k
        - Work.Diff.STE.trunc ρ ε (Work.Diff.STE.conv a c) k‖ ^ 2 :=
    Summable.of_nonneg_of_le
      (fun k => mul_nonneg (zpow_nonneg (le_of_lt (Work.Diff.STE.wt_pos k)) _) (sq_nonneg _))
      hstep (hAf_sum.mul_left _)
  calc CSqZ t (fun k => Work.Diff.STE.conv a (Work.Diff.STE.trunc ρ ε c) k
        - Work.Diff.STE.trunc ρ ε (Work.Diff.STE.conv a c) k)
      = ∑' k : ι → ℤ, (Work.Diff.STE.wt k) ^ t
          * ‖Work.Diff.STE.conv a (Work.Diff.STE.trunc ρ ε c) k
            - Work.Diff.STE.trunc ρ ε (Work.Diff.STE.conv a c) k‖ ^ 2 := rfl
    _ ≤ ∑' k : ι → ℤ, A * 2 ^ (-t) * Kk * (∑' l : ι → ℤ, an (k - l) * bn l) :=
        Summable.tsum_le_tsum hstep hQS (hAf_sum.mul_left _)
    _ = A * 2 ^ (-t) * Kk * (∑' k : ι → ℤ, ∑' l : ι → ℤ, an (k - l) * bn l) := by
        rw [tsum_mul_left]
    _ = A * 2 ^ (-t) * Kk * ((∑' m : ι → ℤ, an m) * (∑' l : ι → ℤ, bn l)) := by
        rw [hAf_id]
    _ = (A * 2 ^ (-t) * Kk * B) * CSqZ (t - 1) c := by
        rw [han_eq, hbn_eq]
        ring


/-- **The flat multiplier commutator gains one derivative on every integer level `Hᵗ`.** -/
theorem flat_multiplier_gain_CSqZ {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : (ι → ℝ) → ℝ) (hρ : ∀ y : ι → ℝ, ‖ρ y‖ ≤ 1)
    (hρ0 : ∀ y : ι → ℝ, 2 < ∑ i, (y i) ^ 2 → ρ y = 0)
    (L0 : ℝ) (hL0 : 0 ≤ L0) (hρlip : ∀ y z : ι → ℝ, ‖ρ y - ρ z‖ ≤ L0 * ‖y - z‖)
    (β : (ι → ℝ) → ℂ) (hβ : ContDiff ℝ (⊤ : ℕ∞) β) (hβp : Work.Diff.STE.Periodic1 β)
    (t : ℤ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ε : ℝ), 0 < ε → ε ≤ 1 → ∀ h : (ι → ℝ) → ℂ,
      ContDiff ℝ (⊤ : ℕ∞) h → Work.Diff.STE.Periodic1 h →
      Work.Diff.STE.B3.SymCalcStep8.CSqZ t (Work.Diff.STE.fourierCoeff (fun x : ι → ℝ =>
          β x * Work.Diff.STE.B3.SymCalc.flatCut ρ ε h x
            - Work.Diff.STE.B3.SymCalc.flatCut ρ ε (fun y : ι → ℝ => β y * h y) x))
        ≤ C * Work.Diff.STE.B3.SymCalcStep8.CSqZ (t - 1) (Work.Diff.STE.fourierCoeff h) := by
  by_cases ht : 1 ≤ t
  · -- ## Positive levels: `flat_multiplier_gain_no_one` at the index `t - 1`
    obtain ⟨n, hn, htn⟩ : ∃ n : ℕ, 1 ≤ n ∧ t = (n : ℤ) :=
      ⟨t.toNat, by omega, (Int.toNat_of_nonneg (by omega)).symm⟩
    subst htn
    have hn2 : (n : ℤ) = (((n - 1) + 1 : ℕ) : ℤ) := by
      rw [Nat.sub_add_cancel hn]
    have hn3 : (n : ℤ) - 1 = ((n - 1 : ℕ) : ℤ) := by
      rw [hn2]; push_cast; ring
    obtain ⟨C, hC, hCb⟩ :=
      Work.Diff.STE.B3.SymCalcStep8.flat_multiplier_gain_no_one ρ hρ hρ0 L0 hL0 hρlip β hβ hβp
        (n - 1)
    refine ⟨C, hC, ?_⟩
    intro ε hε hε1 h hh hhp
    have key := hCb ε hε hε1 h hh hhp
    have e1 : CSqZ ((n : ℤ)) (Work.Diff.STE.fourierCoeff (fun x : ι → ℝ =>
          β x * Work.Diff.STE.B3.SymCalc.flatCut ρ ε h x
            - Work.Diff.STE.B3.SymCalc.flatCut ρ ε (fun y : ι → ℝ => β y * h y) x))
        = Work.Diff.STE.CSq ((n - 1) + 1) (Work.Diff.STE.fourierCoeff (fun x : ι → ℝ =>
          β x * Work.Diff.STE.B3.SymCalc.flatCut ρ ε h x
            - Work.Diff.STE.B3.SymCalc.flatCut ρ ε (fun y : ι → ℝ => β y * h y) x)) := by
      rw [hn2, CSqZ_natCast]
    have e2 : CSqZ ((n : ℤ) - 1) (Work.Diff.STE.fourierCoeff h)
        = Work.Diff.STE.CSq (n - 1) (Work.Diff.STE.fourierCoeff h) := by
      rw [hn3, CSqZ_natCast]
    rw [e1, e2]
    exact key
  · -- ## Nonpositive levels: the coefficient-level estimate on the Fourier side
    have ht0 : t ≤ 0 := by omega
    obtain ⟨C, hC, hCb⟩ :=
      flat_multiplier_commutator_CSqZ_neg_aux ρ hρ hρ0 L0 hL0 hρlip
        (Work.Diff.STE.fourierCoeff β)
        (fun N => Work.Diff.STE.B3.summable_wt_pow_mul_norm_fourierCoeff N β hβ hβp) t ht0
    refine ⟨C, hC, ?_⟩
    intro ε hε hε1 h hh hhp
    -- the Fourier coefficients of the commutator are the commutator of the coefficient families
    have hcoef : Work.Diff.STE.fourierCoeff (fun x : ι → ℝ =>
          β x * Work.Diff.STE.B3.SymCalc.flatCut ρ ε h x
        - Work.Diff.STE.B3.SymCalc.flatCut ρ ε (fun y : ι → ℝ => β y * h y) x)
        = fun k : ι → ℤ => Work.Diff.STE.conv (Work.Diff.STE.fourierCoeff β)
              (Work.Diff.STE.trunc ρ ε (Work.Diff.STE.fourierCoeff h)) k
            - Work.Diff.STE.trunc ρ ε (Work.Diff.STE.conv (Work.Diff.STE.fourierCoeff β)
                (Work.Diff.STE.fourierCoeff h)) k := by
      have hFh_sm : ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.B3.SymCalc.flatCut ρ ε h) :=
        Work.Diff.STE.B3.SymCalcStep1.flatCut_contDiff ρ hρ ε hh hhp
      have hFbh_sm : ContDiff ℝ (⊤ : ℕ∞)
          (Work.Diff.STE.B3.SymCalc.flatCut ρ ε (fun y : ι → ℝ => β y * h y)) :=
        Work.Diff.STE.B3.SymCalcStep1.flatCut_contDiff ρ hρ ε (hβ.mul hh)
          (Work.Diff.STE.B3.SymCalcStep1.Periodic1_mul' hβp hhp)
      funext k
      rw [Work.Diff.STE.flat.fourierCoeff_sub_of_continuous
        (fun x : ι → ℝ => β x * Work.Diff.STE.B3.SymCalc.flatCut ρ ε h x)
        (Work.Diff.STE.B3.SymCalc.flatCut ρ ε (fun y : ι → ℝ => β y * h y))
        (hβ.continuous.mul hFh_sm.continuous) hFbh_sm.continuous k]
      rw [Work.Diff.STE.B3.SymCalcStep7.fourierCoeff_mul_flatCut ρ hρ ε β h hβ.continuous hh hhp k]
      rw [Work.Diff.STE.B3.SymCalcStep7.fourierCoeff_flatCut_mul ρ hρ ε β h hβ hβp hh hhp k]
    rw [hcoef]
    exact hCb ε hε hε1 (Work.Diff.STE.fourierCoeff h)
      (fun N => Work.Diff.STE.summable_weighted_fourierCoeff_of_contDiff h hh hhp N)

end Work.Diff.STE.B3.SymCalcStep8
