import Mathlib
import Submission.Work.ZeroDensity.Jutila.BzCross.BzCrossDefs
import Submission.Work.ZeroDensity.Jutila.S3GAbelSharp
import Submission.Work.LinnikAreas.Density4.BzS3.sigma_half_sqrt_sum
import Submission.Work.LinnikAreas2.czLo_le_czUp
import Submission.Work.ZeroDensity.Jutila.LzAux.CzSigMul
import Submission.Work.ZeroDensity.Jutila.LzAux.CzLogSqLe


/-! Re-homing of the hard-range Abel error `cz_abel_hard_of` of
`Submission/Work/ZeroDensity/Jutila/LzAux/CzAbel.lean` into a module whose import closure avoids
`LzAux.CzSoftCross`/`LzAux.CzSoftModel` (whose `kappaBz`-importing chain clashes with
`LzBilinDefs`).  The soft-range half of `CzAbel` and the final assembly are omitted; only the
hard-range lemma `cz_abel_hard_of` (and its auxiliaries) is kept. -/

/-!
# The Abel error of the two-sided `S₃` model

`CzAbel` is the statement that the difference between the exact reindexed two-sided `S₃` sum
`czCross w y N` and its model `czModelFloor w y N - czModelB w y N` is `O(N)` for `1 ≤ w ≤ y ≤ N`.

The file proves the *hard* case `N < w·y` from scratch (`cz_abel_hard_of`, unconditional apart from
two elementary inputs supplied by `CzSigMul` and `CzLogSqLe`).  In the hard range every triple of the
summation ranges has `t < w` and `r < y`, so the shifts `α = log(w/t)`, `β = log(y/r)` are
non-negative: the proved sharp two-Abel estimate `S3GAbelSharp` applies termwise, and the resulting
`σ_{-1/2}`-weighted sum with integrable logarithms is bounded by
`O(N^{3/2}/√(w y)) ≤ O(N)`.
-/

set_option maxHeartbeats 2000000

namespace Work.ZeroDensity.Jutila.LzDiffAux

open Finset
open Work.ZeroDensity.Jutila (czCross czModelFloor czModelB czMM czAl czBe czUp czLo czQ czR czT)
open Work.ZeroDensity.Jutila.LzAux
open Work.LinnikAreas.Density4.BzS3 (s3G s3main s3c)

noncomputable section

/-! ## Part 1: the pointwise sharp Abel error, valid at every cut-off `X ≥ 1` -/

lemma cz_log_two_le_one : Real.log 2 ≤ 1 := by
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
  linarith

/-- `(1 + a)/2 ≤ 1 + |log 2 - a|` for `a ≥ 0`. -/
lemma cz_one_add_half_le (a : ℝ) (ha : 0 ≤ a) :
    (1 + a) / 2 ≤ 1 + |Real.log 2 - a| := by
  have h2 := cz_log_two_le_one
  by_cases h : a ≤ Real.log 2
  · rw [abs_of_nonneg (by linarith)]
    linarith
  · rw [abs_of_neg (by linarith)]
    linarith

lemma cz_s3G_one (c : ℕ) (α β : ℝ) : s3G c α β 1 = α * β := by
  have hf : (Finset.Icc 1 1).filter (fun m => Nat.Coprime m c ∧ Squarefree m) = {1} := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨h1, h2⟩, -, -⟩
      omega
    · rintro rfl
      exact ⟨⟨le_rfl, le_rfl⟩, Nat.coprime_one_left c, squarefree_one⟩
  rw [s3G, hf, Finset.sum_singleton]
  norm_num

lemma cz_s3main_one (c : ℕ) (α β : ℝ) :
    s3main c α β 1 = s3c c * ((α + 1) * (β + 1) + 1) := by
  rw [s3main, Nat.cast_one, Real.log_one]
  ring

/-- **The sharp Abel error of `s3G` at every cut-off `X ≥ 1`**, extending
`Work.ZeroDensity.Jutila.S3GAbelSharp` (proved there for `X ≥ 2`) to the corner `X = 1`. -/
theorem cz_s3_sharp : ∃ K : ℝ, 0 < K ∧ ∀ (c X : ℕ) (α β : ℝ), 1 ≤ c → 1 ≤ X → 0 ≤ α → 0 ≤ β →
    |s3G c α β X - s3main c α β X|
      ≤ K * Work.ZeroDensity.Jutila.s3Sig c * Real.sqrt (X : ℝ)
        * (1 + |Real.log (2 * (X : ℝ)) - α|) * (1 + |Real.log (2 * (X : ℝ)) - β|) := by
  obtain ⟨K₀, hK₀, hG⟩ := Work.ZeroDensity.Jutila.S3GAbelSharp
  refine ⟨max K₀ 16, lt_max_of_lt_left hK₀, ?_⟩
  intro c X α β hc hX hα hβ
  have hsig1 : 1 ≤ Work.ZeroDensity.Jutila.s3Sig c := Work.ZeroDensity.Jutila.s3Sig_one_le c hc
  have hsig0 : 0 ≤ Work.ZeroDensity.Jutila.s3Sig c := Work.ZeroDensity.Jutila.s3Sig_nonneg c
  rcases eq_or_lt_of_le hX with h1 | h2
  · -- the corner `X = 1`
    subst h1
    have hG1 : s3G c α β 1 = α * β := cz_s3G_one c α β
    have hM1 : s3main c α β 1 = s3c c * ((α + 1) * (β + 1) + 1) := cz_s3main_one c α β
    have hsc1 : s3c c ≤ 1 := Work.LinnikAreas.Density4.BzS3.s3c_le_one c
    have hbr : (0 : ℝ) ≤ (α + 1) * (β + 1) + 1 := by nlinarith [hα, hβ]
    have hA : (1 + α) / 2 ≤ 1 + |Real.log 2 - α| := cz_one_add_half_le α hα
    have hB : (1 + β) / 2 ≤ 1 + |Real.log 2 - β| := cz_one_add_half_le β hβ
    have hA0 : 0 ≤ 1 + |Real.log 2 - α| := by positivity
    have hB0 : 0 ≤ 1 + |Real.log 2 - β| := by positivity
    have hE : |s3G c α β 1 - s3main c α β 1| ≤ 2 * α * β + α + β + 2 := by
      rw [hG1, hM1]
      have h3 : |α * β - s3c c * ((α + 1) * (β + 1) + 1)|
          ≤ |α * β| + |s3c c * ((α + 1) * (β + 1) + 1)| := abs_sub _ _
      rw [abs_of_nonneg (mul_nonneg hα hβ),
        abs_of_nonneg (mul_nonneg (Work.LinnikAreas.Density4.BzS3.s3c_nonneg c) hbr)] at h3
      have h4 : s3c c * ((α + 1) * (β + 1) + 1) ≤ (α + 1) * (β + 1) + 1 := by
        calc s3c c * ((α + 1) * (β + 1) + 1) ≤ 1 * ((α + 1) * (β + 1) + 1) :=
              mul_le_mul_of_nonneg_right hsc1 hbr
          _ = (α + 1) * (β + 1) + 1 := by ring
      nlinarith [h3, h4, hα, hβ]
    have hprod : 4 * (1 + α) * (1 + β) ≤ 16 * (1 + |Real.log 2 - α|) * (1 + |Real.log 2 - β|) := by
      have h1' : 1 + α ≤ 2 * (1 + |Real.log 2 - α|) := by linarith
      have h2' : 1 + β ≤ 2 * (1 + |Real.log 2 - β|) := by linarith
      have h3 : (0 : ℝ) ≤ 1 + β := by linarith
      have h4 : (0 : ℝ) ≤ 2 * (1 + |Real.log 2 - α|) := by linarith
      have h5 := mul_le_mul h1' h2' h3 h4
      linarith [h5]
    have hfin : 2 * α * β + α + β + 2 ≤ 16 * (1 + |Real.log 2 - α|) * (1 + |Real.log 2 - β|) := by
      have h4 : 2 * α * β + α + β + 2 ≤ 4 * (1 + α) * (1 + β) := by nlinarith [hα, hβ]
      linarith [h4, hprod]
    have h16s : (16 : ℝ) ≤ max K₀ 16 * Work.ZeroDensity.Jutila.s3Sig c := by
      have ha : 16 * (1 : ℝ) ≤ 16 * Work.ZeroDensity.Jutila.s3Sig c :=
        mul_le_mul_of_nonneg_left hsig1 (by norm_num)
      have hb : 16 * Work.ZeroDensity.Jutila.s3Sig c
          ≤ max K₀ 16 * Work.ZeroDensity.Jutila.s3Sig c :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) hsig0
      linarith [ha, hb]
    have hAB : (0 : ℝ) ≤ (1 + |Real.log 2 - α|) * (1 + |Real.log 2 - β|) := mul_nonneg hA0 hB0
    have hlast : 16 * (1 + |Real.log 2 - α|) * (1 + |Real.log 2 - β|)
        ≤ max K₀ 16 * Work.ZeroDensity.Jutila.s3Sig c
          * (1 + |Real.log 2 - α|) * (1 + |Real.log 2 - β|) := by
      calc 16 * (1 + |Real.log 2 - α|) * (1 + |Real.log 2 - β|)
          = 16 * ((1 + |Real.log 2 - α|) * (1 + |Real.log 2 - β|)) := by ring
        _ ≤ max K₀ 16 * Work.ZeroDensity.Jutila.s3Sig c
              * ((1 + |Real.log 2 - α|) * (1 + |Real.log 2 - β|)) :=
              mul_le_mul_of_nonneg_right h16s hAB
        _ = max K₀ 16 * Work.ZeroDensity.Jutila.s3Sig c
              * (1 + |Real.log 2 - α|) * (1 + |Real.log 2 - β|) := by ring
    have hgoalR : max K₀ 16 * Work.ZeroDensity.Jutila.s3Sig c * Real.sqrt ((1 : ℕ) : ℝ)
          * (1 + |Real.log (2 * ((1 : ℕ) : ℝ)) - α|)
          * (1 + |Real.log (2 * ((1 : ℕ) : ℝ)) - β|)
        = max K₀ 16 * Work.ZeroDensity.Jutila.s3Sig c
          * (1 + |Real.log 2 - α|) * (1 + |Real.log 2 - β|) := by
      norm_num
    rw [hgoalR]
    exact le_trans hE (le_trans hfin hlast)
  · -- `X ≥ 2`: the proved sharp estimate
    have h := hG c X α β hc h2 hα hβ
    have heq : (K₀ * ∑ d ∈ c.divisors, 1 / Real.sqrt (d : ℝ)) * Real.sqrt (X : ℝ)
        * (1 + |Real.log (2 * (X : ℝ)) - α|) * (1 + |Real.log (2 * (X : ℝ)) - β|)
        = K₀ * Work.ZeroDensity.Jutila.s3Sig c * Real.sqrt (X : ℝ)
          * (1 + |Real.log (2 * (X : ℝ)) - α|) * (1 + |Real.log (2 * (X : ℝ)) - β|) := by
      rw [Work.ZeroDensity.Jutila.s3Sig]
    rw [heq] at h
    have hK : K₀ ≤ max K₀ 16 := le_max_left _ _
    have hA0 : (0 : ℝ) ≤ 1 + |Real.log (2 * (X : ℝ)) - α| := by positivity
    have hB0 : (0 : ℝ) ≤ 1 + |Real.log (2 * (X : ℝ)) - β| := by positivity
    have hnn : (0 : ℝ) ≤ Work.ZeroDensity.Jutila.s3Sig c * Real.sqrt (X : ℝ)
        * (1 + |Real.log (2 * (X : ℝ)) - α|) * (1 + |Real.log (2 * (X : ℝ)) - β|) :=
      mul_nonneg (mul_nonneg (mul_nonneg hsig0 (Real.sqrt_nonneg _)) hA0) hB0
    refine le_trans h ?_
    calc K₀ * Work.ZeroDensity.Jutila.s3Sig c * Real.sqrt (X : ℝ)
          * (1 + |Real.log (2 * (X : ℝ)) - α|) * (1 + |Real.log (2 * (X : ℝ)) - β|)
        = K₀ * (Work.ZeroDensity.Jutila.s3Sig c * Real.sqrt (X : ℝ)
            * (1 + |Real.log (2 * (X : ℝ)) - α|) * (1 + |Real.log (2 * (X : ℝ)) - β|)) := by ring
      _ ≤ max K₀ 16 * (Work.ZeroDensity.Jutila.s3Sig c * Real.sqrt (X : ℝ)
            * (1 + |Real.log (2 * (X : ℝ)) - α|) * (1 + |Real.log (2 * (X : ℝ)) - β|)) :=
            mul_le_mul_of_nonneg_right hK hnn
      _ = max K₀ 16 * Work.ZeroDensity.Jutila.s3Sig c * Real.sqrt (X : ℝ)
            * (1 + |Real.log (2 * (X : ℝ)) - α|) * (1 + |Real.log (2 * (X : ℝ)) - β|) := by ring


/-! ## Part 2: weighted divisor sums with an integrable logarithm -/

/-- `1/((n+1)·√(n+1)) ≤ 2/√n − 2/√(n+1)` for `n ≥ 1`. -/
lemma cz_inv_mul_sqrt_step {n : ℕ} (hn : 1 ≤ n) :
    (1 : ℝ) / (((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 1))
      ≤ 2 / Real.sqrt (n : ℝ) - 2 / Real.sqrt ((n : ℝ) + 1) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  have h1 : 0 < Real.sqrt ((n : ℝ) + 1) := Real.sqrt_pos.mpr hn1
  have h2 : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
  have hs1 : (Real.sqrt ((n : ℝ) + 1))^2 = (n : ℝ) + 1 := Real.sq_sqrt hn1.le
  have hs2 : (Real.sqrt (n : ℝ))^2 = (n : ℝ) := Real.sq_sqrt hn0.le
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < ((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 1))]
  have hgoal1 : (2 / Real.sqrt (n : ℝ) - 2 / Real.sqrt ((n : ℝ) + 1))
      * (((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 1))
      = 2 * (((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 1)) / Real.sqrt (n : ℝ)
        - 2 * ((n : ℝ) + 1) := by
    field_simp
  rw [hgoal1, le_sub_iff_add_le]
  rw [le_div_iff₀ h2]
  have hL : ((1 + 2 * ((n : ℝ) + 1)) * Real.sqrt (n : ℝ))^2
      = (1 + 2 * ((n : ℝ) + 1))^2 * (n : ℝ) := by
    rw [mul_pow, hs2]
  have hR : (2 * (((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 1)))^2
      = 4 * (((n : ℝ) + 1)^2 * ((n : ℝ) + 1)) := by
    rw [mul_pow, mul_pow, hs1]; ring
  have hsq : ((1 + 2 * ((n : ℝ) + 1)) * Real.sqrt (n : ℝ))^2
      ≤ (2 * (((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 1)))^2 := by
    rw [hL, hR]
    nlinarith [hn0]
  have hnn1 : (0:ℝ) ≤ 1 + 2 * ((n:ℝ) + 1) := by linarith
  have hnn2 : (0:ℝ) ≤ 2 * ((n:ℝ) + 1) := by linarith
  nlinarith [hsq, hnn1, hnn2, Real.sqrt_nonneg (n:ℝ), Real.sqrt_nonneg ((n:ℝ)+1),
    mul_nonneg hnn1 (Real.sqrt_nonneg (n:ℝ)),
    mul_nonneg hnn2 (Real.sqrt_nonneg ((n:ℝ)+1)), mul_pos h2 h1]

/-- `Σ_{d ≤ X} 1/(d·√d) ≤ 3`. -/
lemma cz_sum_inv_mul_sqrt_le (X : ℕ) :
    (∑ d ∈ Finset.Icc 1 X, (1 : ℝ) / ((d : ℝ) * Real.sqrt (d : ℝ))) ≤ 3 := by
  have hstrong : ∀ X : ℕ, 1 ≤ X →
      (∑ d ∈ Finset.Icc 1 X, (1 : ℝ) / ((d : ℝ) * Real.sqrt (d : ℝ)))
        ≤ 3 - 2 / Real.sqrt (X : ℝ) := by
    intro X
    induction X with
    | zero => intro h; omega
    | succ m ih =>
      intro hm
      rcases Nat.eq_zero_or_pos m with hm0 | hm0
      · subst hm0
        rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ 0 + 1)]
        rw [show Finset.Icc 1 (0:ℕ) = ∅ from Finset.Icc_eq_empty_iff.mpr (by omega),
          Finset.sum_empty]
        norm_num [Real.sqrt_one]
      · rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1)]
        have hstep := cz_inv_mul_sqrt_step (n := m) hm0
        have hstep' : (1 : ℝ) / (((m + 1 : ℕ) : ℝ) * Real.sqrt (((m + 1 : ℕ) : ℝ)))
            ≤ 2 / Real.sqrt ((m : ℝ)) - 2 / Real.sqrt (((m + 1 : ℕ) : ℝ)) := by
          simpa only [Nat.cast_add, Nat.cast_one] using hstep
        have ih' := ih hm0
        have hpos : (0:ℝ) < Real.sqrt (((m + 1 : ℕ) : ℝ)) :=
          Real.sqrt_pos.mpr (by positivity)
        have hposm : (0:ℝ) < Real.sqrt (m : ℝ) :=
          Real.sqrt_pos.mpr (by exact_mod_cast hm0)
        linarith [ih', hstep', hpos, hposm]
  rcases Nat.eq_zero_or_pos X with hX | hX
  · subst hX; simp
  · have h2 : 0 ≤ 2 / Real.sqrt (X:ℝ) := by positivity
    have := hstrong X hX
    linarith

/-- **The `σ_{-1/2}`-weighted `r`-sum with an integrable logarithm.**  For `1 ≤ V` and
`V ≤ A ≤ 4V`, `Σ_{r ≤ V} σ_{-1/2}(r)/√r · (1 + log(A/r)) ≤ C·√V`. -/
lemma cz_sig_sum_le : ∃ C : ℝ, 0 < C ∧ ∀ (V : ℕ) (A : ℝ), 1 ≤ V → (V : ℝ) ≤ A → A ≤ 4 * (V : ℝ) →
    (∑ r ∈ Finset.Icc 1 V, (1 / Real.sqrt (r : ℝ)) * Work.ZeroDensity.Jutila.s3Sig r
        * (1 + Real.log (A / (r : ℝ))))
      ≤ C * Real.sqrt (V : ℝ) := by
  obtain ⟨C₀, hC₀, hbound⟩ := Work.LinnikAreas.Density4.BzS3.sigma_half_sqrt_sum
  refine ⟨(1 + Real.log 4) * C₀, by positivity, ?_⟩
  intro V A hV hVA hA4
  have hVpos : (0 : ℝ) < (V : ℝ) := by exact_mod_cast hV
  have hstep : ∀ r ∈ Finset.Icc 1 V,
      (1 / Real.sqrt (r : ℝ)) * Work.ZeroDensity.Jutila.s3Sig r * (1 + Real.log (A / (r : ℝ)))
        ≤ (1 + Real.log 4) * ((1 / Real.sqrt (r : ℝ)) * Work.ZeroDensity.Jutila.s3Sig r
            * (1 + Real.log (2 * (V : ℝ) / (r : ℝ)))) := by
    intro r hr
    obtain ⟨hr1, hrV⟩ := Finset.mem_Icc.mp hr
    have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr1
    have hrV' : (r : ℝ) ≤ (V : ℝ) := by exact_mod_cast hrV
    have hlog4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    have hApos : (0 : ℝ) < A := by linarith
    have hlogA : Real.log (A / (r : ℝ)) ≤ Real.log (4 * (V : ℝ) / (r : ℝ)) := by
      apply Real.log_le_log (by positivity)
      rw [div_le_div_iff_of_pos_right hrpos]
      exact hA4
    have hsplit : Real.log (4 * (V : ℝ) / (r : ℝ))
        = Real.log 4 + Real.log ((V : ℝ) / (r : ℝ)) := by
      rw [Real.log_div (by positivity) (by positivity),
        Real.log_mul (by norm_num) (by linarith : (V : ℝ) ≠ 0),
        Real.log_div (by linarith : (V : ℝ) ≠ 0) (by linarith : (r : ℝ) ≠ 0)]
      ring
    have hlog2 : Real.log ((V : ℝ) / (r : ℝ)) ≤ Real.log (2 * (V : ℝ) / (r : ℝ)) := by
      apply Real.log_le_log (by positivity)
      rw [div_le_div_iff_of_pos_right hrpos]
      linarith
    have h2pos : (0 : ℝ) ≤ Real.log (2 * (V : ℝ) / (r : ℝ)) := by
      apply Real.log_nonneg
      rw [le_div_iff₀ hrpos]
      linarith
    have h1 : 1 + Real.log (A / (r : ℝ))
        ≤ (1 + Real.log 4) * (1 + Real.log (2 * (V : ℝ) / (r : ℝ))) := by
      rw [hsplit] at hlogA
      nlinarith [hlogA, hlog2, h2pos, hlog4]
    have hs : (0 : ℝ) ≤ (1 / Real.sqrt (r : ℝ)) * Work.ZeroDensity.Jutila.s3Sig r :=
      mul_nonneg (by positivity) (Work.ZeroDensity.Jutila.s3Sig_nonneg r)
    calc (1 / Real.sqrt (r : ℝ)) * Work.ZeroDensity.Jutila.s3Sig r * (1 + Real.log (A / (r : ℝ)))
        ≤ (1 / Real.sqrt (r : ℝ)) * Work.ZeroDensity.Jutila.s3Sig r
            * ((1 + Real.log 4) * (1 + Real.log (2 * (V : ℝ) / (r : ℝ)))) :=
          mul_le_mul_of_nonneg_left h1 hs
      _ = (1 + Real.log 4) * ((1 / Real.sqrt (r : ℝ)) * Work.ZeroDensity.Jutila.s3Sig r
            * (1 + Real.log (2 * (V : ℝ) / (r : ℝ)))) := by ring
  calc (∑ r ∈ Finset.Icc 1 V, (1 / Real.sqrt (r : ℝ)) * Work.ZeroDensity.Jutila.s3Sig r
          * (1 + Real.log (A / (r : ℝ))))
      ≤ ∑ r ∈ Finset.Icc 1 V, (1 + Real.log 4) * ((1 / Real.sqrt (r : ℝ))
          * Work.ZeroDensity.Jutila.s3Sig r * (1 + Real.log (2 * (V : ℝ) / (r : ℝ)))) :=
        Finset.sum_le_sum hstep
    _ = (1 + Real.log 4) * ∑ r ∈ Finset.Icc 1 V, ((1 / Real.sqrt (r : ℝ))
          * Work.ZeroDensity.Jutila.s3Sig r * (1 + Real.log (2 * (V : ℝ) / (r : ℝ)))) := by
        rw [Finset.mul_sum]
    _ ≤ (1 + Real.log 4) * (C₀ * Real.sqrt (V : ℝ)) :=
        mul_le_mul_of_nonneg_left (hbound V hV) (by positivity)
    _ = (1 + Real.log 4) * C₀ * Real.sqrt (V : ℝ) := by ring

/-! ## Part 3: elementary facts about the summation ranges -/

/-- Both `s3G` and `s3main` vanish at the cut-off `0`. -/
lemma cz_E_zero (c : ℕ) (α β : ℝ) : s3G c α β 0 = s3main c α β 0 := by
  rw [s3G, s3main]
  simp

lemma cz_t_le_ofR (y : ℝ) (N q t : ℕ) (hy : 0 < y) (hq : 0 < (q : ℝ)) (ht : t ≤ czT y N q) :
    (t : ℝ) ≤ (N : ℝ) / ((q : ℝ) * y) := by
  have h1 : (t : ℝ) ≤ ((czT y N q : ℕ) : ℝ) := by exact_mod_cast ht
  have h2 : ((czT y N q : ℕ) : ℝ) ≤ (N : ℝ) / ((q : ℝ) * y) := by
    rw [czT]
    exact Nat.floor_le (by positivity)
  linarith

lemma cz_r_le_ofR (w : ℝ) (N q r : ℕ) (hw : 0 < w) (hq : 0 < (q : ℝ)) (hr : r ≤ czR w N q) :
    (r : ℝ) ≤ (N : ℝ) / ((q : ℝ) * w) := by
  have h1 : (r : ℝ) ≤ ((czR w N q : ℕ) : ℝ) := by exact_mod_cast hr
  have h2 : ((czR w N q : ℕ) : ℝ) ≤ (N : ℝ) / ((q : ℝ) * w) := by
    rw [czR]
    exact Nat.floor_le (by positivity)
  linarith

/-- `x ≤ 2⌊x⌋` for `x ≥ 1`. -/
lemma cz_two_floor_ge (x : ℝ) (hx : 1 ≤ x) : x ≤ 2 * (⌊x⌋₊ : ℝ) := by
  have hm : (1 : ℝ) ≤ (⌊x⌋₊ : ℝ) := by
    have := Nat.one_le_floor_iff x
    exact_mod_cast this.mpr hx
  have h := Nat.lt_floor_add_one x
  linarith


/-! ## Part 4: the lower cut-off is dominated by the upper one -/

/-- For `1 ≤ B ≤ M` and arbitrary shifts, `√B·W(B) ≤ 25·√M·W(M)` where
`W(X) = (1+|log(2X)-α|)·(1+|log(2X)-β|)`. -/
lemma cz_lo_le_up (hlog : ∀ r : ℝ, 1 ≤ r → (1 + Real.log r) ^ 2 ≤ 25 * Real.sqrt r)
    (B M : ℕ) (hB1 : 1 ≤ B) (hBM : B ≤ M) (α β : ℝ) :
    Real.sqrt (B : ℝ) * (1 + |Real.log (2 * (B : ℝ)) - α|)
        * (1 + |Real.log (2 * (B : ℝ)) - β|)
      ≤ 25 * Real.sqrt (M : ℝ) * (1 + |Real.log (2 * (M : ℝ)) - α|)
        * (1 + |Real.log (2 * (M : ℝ)) - β|) := by
  have hB0 : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB1
  have hM1 : 1 ≤ M := le_trans hB1 hBM
  have hM0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM1
  set ratio : ℝ := (M : ℝ) / (B : ℝ) with hratio
  have hratio1 : 1 ≤ ratio := by
    rw [hratio, le_div_iff₀ hB0, one_mul]
    exact_mod_cast hBM
  have hratio0 : (0 : ℝ) < ratio := lt_of_lt_of_le zero_lt_one hratio1
  have hlogr : Real.log ratio = Real.log (M : ℝ) - Real.log (B : ℝ) := by
    rw [hratio, Real.log_div (ne_of_gt hM0) (ne_of_gt hB0)]
  -- the two weight factors
  have hfac : ∀ γ : ℝ, 1 + |Real.log (2 * (B : ℝ)) - γ|
      ≤ (1 + Real.log ratio) * (1 + |Real.log (2 * (M : ℝ)) - γ|) := by
    intro γ
    have h2B : |Real.log (2 * (B : ℝ)) - Real.log (2 * (M : ℝ))| = Real.log ratio := by
      have h2l : Real.log (2 * (M : ℝ)) - Real.log (2 * (B : ℝ)) = Real.log ratio := by
        have h1 : Real.log (2 * (M : ℝ)) - Real.log (2 * (B : ℝ))
            = Real.log ((2 * (M : ℝ)) / (2 * (B : ℝ))) := by
          rw [Real.log_div (by positivity) (by positivity)]
        rw [h1, show (2 * (M : ℝ)) / (2 * (B : ℝ)) = ratio by rw [hratio]; field_simp]
      have h2B' : Real.log (2 * (B : ℝ)) ≤ Real.log (2 * (M : ℝ)) := by
        apply Real.log_le_log (by positivity)
        linarith [show (B : ℝ) ≤ (M : ℝ) by exact_mod_cast hBM]
      rw [abs_of_nonpos (by linarith),
        show -(Real.log (2 * (B : ℝ)) - Real.log (2 * (M : ℝ)))
          = Real.log (2 * (M : ℝ)) - Real.log (2 * (B : ℝ)) from by ring]
      exact h2l
    have htri : |Real.log (2 * (B : ℝ)) - γ|
        ≤ |Real.log (2 * (M : ℝ)) - γ| + Real.log ratio := by
      have h := abs_sub_le (Real.log (2 * (B : ℝ))) γ (Real.log (2 * (M : ℝ)))
      have h2 : |Real.log (2 * (B : ℝ)) - Real.log (2 * (M : ℝ))| = Real.log ratio := h2B
      have h3 : |Real.log (2 * (B : ℝ)) - γ|
          ≤ |Real.log (2 * (M : ℝ)) - γ| + |Real.log (2 * (B : ℝ)) - Real.log (2 * (M : ℝ))| := by
        have heq : Real.log (2 * (B : ℝ)) - γ
            = (Real.log (2 * (M : ℝ)) - γ)
              + (Real.log (2 * (B : ℝ)) - Real.log (2 * (M : ℝ))) := by ring
        rw [heq]
        exact abs_add_le _ _
      rw [h2] at h3
      exact h3
    have hX0 : (0 : ℝ) ≤ |Real.log (2 * (M : ℝ)) - γ| := abs_nonneg _
    have hu0 : (0 : ℝ) ≤ Real.log ratio := Real.log_nonneg hratio1
    nlinarith [htri, hX0, hu0]
  have hW : (1 + |Real.log (2 * (B : ℝ)) - α|) * (1 + |Real.log (2 * (B : ℝ)) - β|)
      ≤ (1 + Real.log ratio) * (1 + Real.log ratio)
        * ((1 + |Real.log (2 * (M : ℝ)) - α|) * (1 + |Real.log (2 * (M : ℝ)) - β|)) := by
    have h1 := hfac α
    have h2 := hfac β
    have h1' : (0 : ℝ) ≤ 1 + |Real.log (2 * (B : ℝ)) - β| := by positivity
    have h2' : (0 : ℝ) ≤ (1 + Real.log ratio) * (1 + |Real.log (2 * (M : ℝ)) - α|) :=
      mul_nonneg (by have := Real.log_nonneg hratio1; linarith) (by positivity)
    have h3 := mul_le_mul h1 h2 h1' h2'
    nlinarith [h3]
  -- the square-root factor
  have hsq : Real.sqrt (B : ℝ) * (1 + Real.log ratio) ^ 2
      ≤ 25 * Real.sqrt (M : ℝ) := by
    have hl := hlog ratio hratio1
    have hratio_eq : ratio = (M : ℝ) / (B : ℝ) := hratio
    have hsqrt_ratio : Real.sqrt ratio = Real.sqrt (M : ℝ) / Real.sqrt (B : ℝ) := by
      rw [hratio, Real.sqrt_div (le_of_lt hM0)]
    have hsqrtB : Real.sqrt (B : ℝ) * Real.sqrt (B : ℝ) = (B : ℝ) := by
      rw [← pow_two, Real.sq_sqrt (le_of_lt hB0)]
    calc Real.sqrt (B : ℝ) * (1 + Real.log ratio) ^ 2
        ≤ Real.sqrt (B : ℝ) * (25 * Real.sqrt ratio) :=
          mul_le_mul_of_nonneg_left hl (Real.sqrt_nonneg _)
      _ = 25 * (Real.sqrt (B : ℝ) * Real.sqrt ratio) := by ring
      _ = 25 * (Real.sqrt (B : ℝ) * (Real.sqrt (M : ℝ) / Real.sqrt (B : ℝ))) := by
          rw [hsqrt_ratio]
      _ = 25 * Real.sqrt (M : ℝ) := by
          have h1 : Real.sqrt (B : ℝ) * (Real.sqrt (M : ℝ) / Real.sqrt (B : ℝ))
              = Real.sqrt (M : ℝ) := by
            field_simp
          rw [h1]
  have hW0 : (0 : ℝ) ≤ (1 + |Real.log (2 * (M : ℝ)) - α|)
      * (1 + |Real.log (2 * (M : ℝ)) - β|) := by positivity
  calc Real.sqrt (B : ℝ) * (1 + |Real.log (2 * (B : ℝ)) - α|)
        * (1 + |Real.log (2 * (B : ℝ)) - β|)
      = Real.sqrt (B : ℝ) * ((1 + |Real.log (2 * (B : ℝ)) - α|)
        * (1 + |Real.log (2 * (B : ℝ)) - β|)) := by ring
    _ ≤ Real.sqrt (B : ℝ) * ((1 + Real.log ratio) * (1 + Real.log ratio)
          * ((1 + |Real.log (2 * (M : ℝ)) - α|) * (1 + |Real.log (2 * (M : ℝ)) - β|))) :=
        mul_le_mul_of_nonneg_left hW (Real.sqrt_nonneg _)
    _ = (Real.sqrt (B : ℝ) * (1 + Real.log ratio) ^ 2)
          * ((1 + |Real.log (2 * (M : ℝ)) - α|) * (1 + |Real.log (2 * (M : ℝ)) - β|)) := by ring
    _ ≤ (25 * Real.sqrt (M : ℝ))
          * ((1 + |Real.log (2 * (M : ℝ)) - α|) * (1 + |Real.log (2 * (M : ℝ)) - β|)) :=
        mul_le_mul_of_nonneg_right hsq hW0
    _ = 25 * Real.sqrt (M : ℝ) * (1 + |Real.log (2 * (M : ℝ)) - α|)
          * (1 + |Real.log (2 * (M : ℝ)) - β|) := by ring

/-! ## Part 5: replacing `log(2⌊N/(q v u)⌋)` by its range expression -/

/-- For `M = ⌊N/(q v u)⌋ ≥ 1` and `q z v ≤ N`, one has
`|log(2M) - log(z/u)| ≤ log(2N/(q z v))`. -/
lemma cz_log_replace (z : ℝ) (hz : 0 < z) (N q u v : ℕ) (hq : 0 < (q : ℝ))
    (hu : 0 < (u : ℝ)) (hv : 0 < (v : ℝ)) (hM1 : 1 ≤ czUp N q v u)
    (hqzv : (q : ℝ) * z * (v : ℝ) ≤ (N : ℝ)) :
    |Real.log (2 * (czUp N q v u : ℝ)) - Real.log (z / (u : ℝ))|
      ≤ Real.log (2 * (N : ℝ) / ((q : ℝ) * z * (v : ℝ))) := by
  have hfloor : ((czUp N q v u : ℕ) : ℝ)
      = ((⌊(N : ℝ) / ((q : ℝ) * (v : ℝ) * (u : ℝ))⌋₊ : ℕ) : ℝ) := by
    rw [czUp]
    congr 1
    conv_rhs => rw [show ((q : ℝ) * (v : ℝ) * (u : ℝ)) = (((q * v * u : ℕ)) : ℝ) by
      push_cast; ring]
    rw [Nat.floor_div_natCast, Nat.floor_natCast]
  have hMle : (czUp N q v u : ℝ) ≤ (N : ℝ) / ((q : ℝ) * (v : ℝ) * (u : ℝ)) := by
    rw [hfloor]
    exact Nat.floor_le (by positivity)
  have hx : (N : ℝ) / ((q : ℝ) * (v : ℝ) * (u : ℝ)) ≤ 2 * (czUp N q v u : ℝ) := by
    have hlt := Nat.lt_floor_add_one ((N : ℝ) / ((q : ℝ) * (v : ℝ) * (u : ℝ)))
    have h1 : (N : ℝ) / ((q : ℝ) * (v : ℝ) * (u : ℝ)) ≤ (czUp N q v u : ℝ) + 1 := by
      rw [hfloor]
      linarith
    have h2 : (1 : ℝ) ≤ (czUp N q v u : ℝ) := by exact_mod_cast hM1
    linarith
  have hkey : Real.log (2 * (czUp N q v u : ℝ)) - Real.log (z / (u : ℝ))
      = Real.log (2 * (czUp N q v u : ℝ) * (u : ℝ) / z) := by
    rw [Real.log_div (by positivity) (by linarith : (z : ℝ) ≠ 0),
        Real.log_div (by linarith : (z : ℝ) ≠ 0) (by linarith : (u : ℝ) ≠ 0),
        Real.log_mul (by positivity) (by linarith : (u : ℝ) ≠ 0)]
    ring
  rw [hkey, abs_le]
  have hlow : (N : ℝ) / ((q : ℝ) * z * (v : ℝ))
      ≤ 2 * (czUp N q v u : ℝ) * (u : ℝ) / z := by
    rw [le_div_iff₀ hz]
    have heq : (N : ℝ) / ((q : ℝ) * z * (v : ℝ)) * z
        = (N : ℝ) / ((q : ℝ) * (v : ℝ) * (u : ℝ)) * (u : ℝ) := by
      field_simp
    rw [heq]
    exact mul_le_mul_of_nonneg_right hx (le_of_lt hu)
  have hup : 2 * (czUp N q v u : ℝ) * (u : ℝ) / z
      ≤ 2 * (N : ℝ) / ((q : ℝ) * z * (v : ℝ)) := by
    rw [div_le_iff₀ hz]
    have heq : (2 * (N : ℝ) / ((q : ℝ) * z * (v : ℝ))) * z
        = 2 * ((N : ℝ) / ((q : ℝ) * (v : ℝ) * (u : ℝ))) * (u : ℝ) := by
      field_simp
    rw [heq]
    have h3 := mul_le_mul_of_nonneg_right hMle (le_of_lt hu)
    linarith [h3]
  have hlog_low : 0 ≤ Real.log ((N : ℝ) / ((q : ℝ) * z * (v : ℝ))) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ (by positivity)]
    linarith [hqzv]
  have hNpos : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le (by positivity) hqzv
  have hpos1 : (0 : ℝ) < (N : ℝ) / ((q : ℝ) * z * (v : ℝ)) :=
    div_pos hNpos (by positivity)
  have hlog_mono1 : Real.log ((N : ℝ) / ((q : ℝ) * z * (v : ℝ)))
      ≤ Real.log (2 * (czUp N q v u : ℝ) * (u : ℝ) / z) :=
    Real.log_le_log hpos1 hlow
  have hpos2 : (0 : ℝ) < 2 * (czUp N q v u : ℝ) * (u : ℝ) / z := by
    have h1 : (1 : ℝ) ≤ (czUp N q v u : ℝ) := by exact_mod_cast hM1
    positivity
  have hlog_mono2 : Real.log (2 * (czUp N q v u : ℝ) * (u : ℝ) / z)
      ≤ Real.log (2 * (N : ℝ) / ((q : ℝ) * z * (v : ℝ))) :=
    Real.log_le_log hpos2 hup
  have h2N : 0 ≤ Real.log (2 * (N : ℝ) / ((q : ℝ) * z * (v : ℝ))) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ (by positivity)]
    linarith [hqzv]
  constructor <;> linarith

/-! ## Part 6: the hard range of the Abel error -/

/-- `√(N/(q r t)) = √(N/q)·(1/√r)·(1/√t)` for positive `q, r, t`. -/
lemma cz_sqrt_factor (N q r t : ℕ) (hq : 0 < q) (hr : 0 < r) (ht : 0 < t) :
    Real.sqrt ((N : ℝ) / ((q : ℝ) * (r : ℝ) * (t : ℝ)))
      = Real.sqrt ((N : ℝ) / (q : ℝ)) * (1 / Real.sqrt (r : ℝ)) * (1 / Real.sqrt (t : ℝ)) := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hr0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have ht0 : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  rw [Real.sqrt_div hN0 ((q : ℝ) * (r : ℝ) * (t : ℝ)),
    show ((q : ℝ) * (r : ℝ) * (t : ℝ)) = ((q : ℝ) * (r : ℝ)) * (t : ℝ) by ring,
    Real.sqrt_mul (le_of_lt (mul_pos hq0 hr0)) (t : ℝ),
    Real.sqrt_mul (le_of_lt hq0) (r : ℝ),
    Real.sqrt_div hN0 (q : ℝ)]
  field_simp

/-- **The hard range `N < w·y`**: the Abel error is `O(N)`.

Only two elementary inputs are used: `hsig` (`σ_{-1/2}` submultiplicativity) and `hlog`. -/
lemma cz_abel_hard_of
    (hsig : ∀ a b : ℕ, Work.ZeroDensity.Jutila.s3Sig (a * b)
      ≤ Work.ZeroDensity.Jutila.s3Sig a * Work.ZeroDensity.Jutila.s3Sig b)
    (hlog : ∀ r : ℝ, 1 ≤ r → (1 + Real.log r) ^ 2 ≤ 25 * Real.sqrt r) :
    ∃ C : ℝ, 0 < C ∧ ∀ (w y : ℝ) (N : ℕ), 1 ≤ w → w ≤ y → y ≤ (N : ℝ) → (N : ℝ) < w * y →
      |czCross w y N - (czModelFloor w y N - czModelB w y N)| ≤ C * (N : ℝ) := by
  obtain ⟨K, hK, hsharp⟩ := cz_s3_sharp
  obtain ⟨C₁, hC₁, hsigsum⟩ := cz_sig_sum_le
  refine ⟨(26 * (K * (C₁ * C₁))) * (1 + 3) + 1, by positivity, ?_⟩
  intro w y N hw hwy hyN hhard
  have hw0 : 0 < w := lt_of_lt_of_le zero_lt_one hw
  have hy1 : 1 ≤ y := le_trans hw hwy
  have hy0 : 0 < y := lt_of_lt_of_le zero_lt_one hy1
  have hN1 : 1 ≤ N := by
    have h : (1 : ℝ) ≤ (N : ℝ) := le_trans hy1 hyN
    exact_mod_cast h
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
  -- (1) the difference as a triple sum of Abel differences
  have hdecomp : czCross w y N - (czModelFloor w y N - czModelB w y N)
      = ∑ q ∈ Finset.Icc 1 (czQ y N), ∑ r ∈ Finset.Icc 1 (czR w N q),
          ∑ t ∈ Finset.Icc 1 (czT y N q),
            czMM r t * ((s3G (r * t) (czAl w t) (czBe y r) (czUp N q r t)
                          - s3main (r * t) (czAl w t) (czBe y r) (czUp N q r t))
                        - (s3G (r * t) (czAl w t) (czBe y r) (czLo w y r t)
                          - s3main (r * t) (czAl w t) (czBe y r) (czLo w y r t))) := by
    simp only [czCross, czModelFloor, czModelB]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    ring
  rw [hdecomp]
  -- (2) termwise bound
  have hmain : |∑ q ∈ Finset.Icc 1 (czQ y N), ∑ r ∈ Finset.Icc 1 (czR w N q),
        ∑ t ∈ Finset.Icc 1 (czT y N q),
          czMM r t * ((s3G (r * t) (czAl w t) (czBe y r) (czUp N q r t)
                        - s3main (r * t) (czAl w t) (czBe y r) (czUp N q r t))
                      - (s3G (r * t) (czAl w t) (czBe y r) (czLo w y r t)
                        - s3main (r * t) (czAl w t) (czBe y r) (czLo w y r t)))|
      ≤ ∑ q ∈ Finset.Icc 1 (czQ y N), ∑ r ∈ Finset.Icc 1 (czR w N q),
          ∑ t ∈ Finset.Icc 1 (czT y N q),
            26 * K * (Work.ZeroDensity.Jutila.s3Sig r * Work.ZeroDensity.Jutila.s3Sig t
              * Real.sqrt ((N : ℝ) / ((q : ℝ) * (r : ℝ) * (t : ℝ)))
              * (1 + Real.log (2 * (N : ℝ) / ((q : ℝ) * w * (r : ℝ))))
              * (1 + Real.log (2 * (N : ℝ) / ((q : ℝ) * y * (t : ℝ))))) := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine Finset.sum_le_sum (fun q hq => ?_)
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine Finset.sum_le_sum (fun r hr => ?_)
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine Finset.sum_le_sum (fun t ht => ?_)
    obtain ⟨hq1, hq2⟩ := Finset.mem_Icc.mp hq
    obtain ⟨hr1, hr2⟩ := Finset.mem_Icc.mp hr
    obtain ⟨ht1, ht2⟩ := Finset.mem_Icc.mp ht
    have hqr : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq1
    have hrr : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr1
    have htt : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht1
    have hrt1 : 0 < r * t := Nat.mul_pos (by omega) (by omega)
    -- range facts
    have hqrw : (q : ℝ) * w * (r : ℝ) ≤ (N : ℝ) := by
      have hrle := cz_r_le_ofR w N q r hw0 hqr hr2
      have h2 : (r : ℝ) * ((q : ℝ) * w) ≤ (N : ℝ) :=
        (le_div_iff₀ (by positivity : (0 : ℝ) < (q : ℝ) * w)).mp hrle
      linarith [h2]
    have hqyt : (q : ℝ) * y * (t : ℝ) ≤ (N : ℝ) := by
      have htle := cz_t_le_ofR y N q t hy0 hqr ht2
      have h2 : (t : ℝ) * ((q : ℝ) * y) ≤ (N : ℝ) :=
        (le_div_iff₀ (by positivity : (0 : ℝ) < (q : ℝ) * y)).mp htle
      linarith [h2]
    have ht_lt_w : (t : ℝ) < w := by
      have h1 : (q : ℝ) * (t : ℝ) * y < w * y := by
        calc (q : ℝ) * (t : ℝ) * y = (q : ℝ) * y * (t : ℝ) := by ring
          _ ≤ (N : ℝ) := hqyt
          _ < w * y := hhard
      have h2 : (q : ℝ) * (t : ℝ) < w := by
        by_contra hc
        push_neg at hc
        have h3 : w * y ≤ ((q : ℝ) * (t : ℝ)) * y :=
          mul_le_mul_of_nonneg_right hc (le_of_lt hy0)
        exact absurd (lt_of_le_of_lt h3 h1) (lt_irrefl _)
      have h3 : (t : ℝ) ≤ (q : ℝ) * (t : ℝ) := by
        have hq1R : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
        have h4 := mul_le_mul_of_nonneg_right hq1R (le_of_lt htt)
        linarith [h4]
      linarith [h2, h3]
    have hr_lt_y : (r : ℝ) < y := by
      have h1 : (q : ℝ) * (r : ℝ) * w < y * w := by
        calc (q : ℝ) * (r : ℝ) * w = (q : ℝ) * w * (r : ℝ) := by ring
          _ ≤ (N : ℝ) := hqrw
          _ < w * y := hhard
          _ = y * w := by ring
      have h2 : (q : ℝ) * (r : ℝ) < y := by
        by_contra hc
        push_neg at hc
        have h3 : y * w ≤ ((q : ℝ) * (r : ℝ)) * w :=
          mul_le_mul_of_nonneg_right hc (le_of_lt hw0)
        exact absurd (lt_of_le_of_lt h3 h1) (lt_irrefl _)
      have h3 : (r : ℝ) ≤ (q : ℝ) * (r : ℝ) := by
        have hq1R : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
        have h4 := mul_le_mul_of_nonneg_right hq1R (le_of_lt hrr)
        linarith [h4]
      linarith [h2, h3]
    have hα : 0 ≤ czAl w t := by
      rw [czAl]
      apply Real.log_nonneg
      rw [le_div_iff₀ htt]
      linarith [ht_lt_w]
    have hβ : 0 ≤ czBe y r := by
      rw [czBe]
      apply Real.log_nonneg
      rw [le_div_iff₀ hrr]
      linarith [hr_lt_y]
    have hsig_mul : Work.ZeroDensity.Jutila.s3Sig (r * t)
        ≤ Work.ZeroDensity.Jutila.s3Sig r * Work.ZeroDensity.Jutila.s3Sig t := hsig r t
    have hsig_r : (0 : ℝ) ≤ Work.ZeroDensity.Jutila.s3Sig r :=
      Work.ZeroDensity.Jutila.s3Sig_nonneg r
    have hsig_t : (0 : ℝ) ≤ Work.ZeroDensity.Jutila.s3Sig t :=
      Work.ZeroDensity.Jutila.s3Sig_nonneg t
    have hmm1 : (0 : ℝ) ≤ 26 * K := by positivity
    by_cases hup0 : czUp N q r t = 0
    · -- both Abel differences vanish
      have hlo_le : czLo w y r t ≤ czUp N q r t :=
        Work.LinnikAreas2.czLo_le_czUp w y N q r t hw hy1 hq1 hr ht
      have hlo0 : czLo w y r t = 0 := le_antisymm (by rw [← hup0]; exact hlo_le) (Nat.zero_le _)
      have hE1 := cz_E_zero (r * t) (czAl w t) (czBe y r)
      rw [hup0, hlo0, hE1]
      simp only [sub_self, mul_zero, abs_zero]
      have hgoalR : (0 : ℝ) ≤ 26 * K * (Work.ZeroDensity.Jutila.s3Sig r
            * Work.ZeroDensity.Jutila.s3Sig t
            * Real.sqrt ((N : ℝ) / ((q : ℝ) * (r : ℝ) * (t : ℝ)))
            * (1 + Real.log (2 * (N : ℝ) / ((q : ℝ) * w * (r : ℝ))))
            * (1 + Real.log (2 * (N : ℝ) / ((q : ℝ) * y * (t : ℝ))))) := by
        have h1 : (0 : ℝ) < (N : ℝ) / ((q : ℝ) * (r : ℝ) * (t : ℝ)) := by positivity
        have h2 : (0 : ℝ) < (N : ℝ) / ((q : ℝ) * w * (r : ℝ)) := by positivity
        have h3 : (0 : ℝ) < (N : ℝ) / ((q : ℝ) * y * (t : ℝ)) := by positivity
        have h4 : (0 : ℝ) ≤ Real.log (2 * (N : ℝ) / ((q : ℝ) * w * (r : ℝ))) :=
          Real.log_nonneg (by
            rw [le_div_iff₀ (by positivity)]
            linarith [hqrw])
        have h5 : (0 : ℝ) ≤ Real.log (2 * (N : ℝ) / ((q : ℝ) * y * (t : ℝ))) :=
          Real.log_nonneg (by
            rw [le_div_iff₀ (by positivity)]
            linarith [hqyt])
        positivity
      exact hgoalR
    · -- the main case
      have hup1 : 1 ≤ czUp N q r t := Nat.pos_of_ne_zero hup0
      have hup_eq : czUp N q t r = czUp N q r t := by
        rw [czUp, czUp]; congr 1; ring
      have hlogM : |Real.log (2 * (czUp N q r t : ℝ)) - czAl w t|
          ≤ Real.log (2 * (N : ℝ) / ((q : ℝ) * w * (r : ℝ))) := by
        have h := cz_log_replace w hw0 N q t r hqr htt hrr hup1 hqrw
        simpa only [czAl] using h
      have hlogM2 : |Real.log (2 * (czUp N q r t : ℝ)) - czBe y r|
          ≤ Real.log (2 * (N : ℝ) / ((q : ℝ) * y * (t : ℝ))) := by
        have hup1' : 1 ≤ czUp N q t r := by rw [hup_eq]; exact hup1
        have h := cz_log_replace y hy0 N q r t hqr hrr htt hup1' hqyt
        rw [hup_eq] at h
        simpa only [czBe] using h
      have hMpos : (0 : ℝ) < (N : ℝ) / ((q : ℝ) * (r : ℝ) * (t : ℝ)) := by positivity
      have hsqrtM : Real.sqrt ((czUp N q r t : ℕ) : ℝ)
          ≤ Real.sqrt ((N : ℝ) / ((q : ℝ) * (r : ℝ) * (t : ℝ))) := by
        have hcast : (((czUp N q r t : ℕ)) : ℝ)
            = ((⌊(N : ℝ) / ((q : ℝ) * (r : ℝ) * (t : ℝ))⌋₊ : ℕ) : ℝ) := by
          rw [czUp]
          congr 1
          conv_rhs => rw [show ((q : ℝ) * (r : ℝ) * (t : ℝ)) = (((q * r * t : ℕ)) : ℝ) by
            push_cast; ring]
          rw [Nat.floor_div_natCast, Nat.floor_natCast]
        rw [hcast]
        exact Real.sqrt_le_sqrt (Nat.floor_le (by positivity))
      have hL1 : (0 : ℝ) ≤ 1 + Real.log (2 * (N : ℝ) / ((q : ℝ) * w * (r : ℝ))) := by
        have h4 : (0 : ℝ) ≤ Real.log (2 * (N : ℝ) / ((q : ℝ) * w * (r : ℝ))) :=
          Real.log_nonneg (by
            rw [le_div_iff₀ (by positivity)]
            linarith [hqrw])
        linarith
      have hL2 : (0 : ℝ) ≤ 1 + Real.log (2 * (N : ℝ) / ((q : ℝ) * y * (t : ℝ))) := by
        have h5 : (0 : ℝ) ≤ Real.log (2 * (N : ℝ) / ((q : ℝ) * y * (t : ℝ))) :=
          Real.log_nonneg (by
            rw [le_div_iff₀ (by positivity)]
            linarith [hqyt])
        linarith
      have hEM_le : |s3G (r * t) (czAl w t) (czBe y r) (czUp N q r t)
            - s3main (r * t) (czAl w t) (czBe y r) (czUp N q r t)|
          ≤ K * Work.ZeroDensity.Jutila.s3Sig (r * t) * Real.sqrt ((czUp N q r t : ℕ) : ℝ)
            * (1 + |Real.log (2 * (czUp N q r t : ℝ)) - czAl w t|)
            * (1 + |Real.log (2 * (czUp N q r t : ℝ)) - czBe y r|) :=
        hsharp (r * t) (czUp N q r t) (czAl w t) (czBe y r) hrt1 hup1 hα hβ
      have hchainM : K * Work.ZeroDensity.Jutila.s3Sig (r * t)
            * Real.sqrt ((czUp N q r t : ℕ) : ℝ)
            * (1 + |Real.log (2 * (czUp N q r t : ℝ)) - czAl w t|)
            * (1 + |Real.log (2 * (czUp N q r t : ℝ)) - czBe y r|)
          ≤ K * (Work.ZeroDensity.Jutila.s3Sig r * Work.ZeroDensity.Jutila.s3Sig t)
            * Real.sqrt ((N : ℝ) / ((q : ℝ) * (r : ℝ) * (t : ℝ)))
            * (1 + Real.log (2 * (N : ℝ) / ((q : ℝ) * w * (r : ℝ))))
            * (1 + Real.log (2 * (N : ℝ) / ((q : ℝ) * y * (t : ℝ)))) := by
        have hlog1 : 1 + |Real.log (2 * (czUp N q r t : ℝ)) - czAl w t|
            ≤ 1 + Real.log (2 * (N : ℝ) / ((q : ℝ) * w * (r : ℝ))) := by linarith [hlogM]
        have hlog2 : 1 + |Real.log (2 * (czUp N q r t : ℝ)) - czBe y r|
            ≤ 1 + Real.log (2 * (N : ℝ) / ((q : ℝ) * y * (t : ℝ))) := by linarith [hlogM2]
        have hA0 : (0 : ℝ) ≤ 1 + |Real.log (2 * (czUp N q r t : ℝ)) - czAl w t| := by positivity
        have hB0 : (0 : ℝ) ≤ 1 + |Real.log (2 * (czUp N q r t : ℝ)) - czBe y r| := by positivity
        have hσnn : (0 : ℝ) ≤ Work.ZeroDensity.Jutila.s3Sig r
            * Work.ZeroDensity.Jutila.s3Sig t := mul_nonneg hsig_r hsig_t
        have hsq0 : (0 : ℝ) ≤ Real.sqrt ((N : ℝ) / ((q : ℝ) * (r : ℝ) * (t : ℝ))) :=
          Real.sqrt_nonneg _
        have hW1 : (0 : ℝ) ≤ 1 + Real.log (2 * (N : ℝ) / ((q : ℝ) * w * (r : ℝ))) := hL1
        have hW2 : (0 : ℝ) ≤ 1 + Real.log (2 * (N : ℝ) / ((q : ℝ) * y * (t : ℝ))) := hL2
        calc K * Work.ZeroDensity.Jutila.s3Sig (r * t)
              * Real.sqrt ((czUp N q r t : ℕ) : ℝ)
              * (1 + |Real.log (2 * (czUp N q r t : ℝ)) - czAl w t|)
              * (1 + |Real.log (2 * (czUp N q r t : ℝ)) - czBe y r|)
            = K * (Work.ZeroDensity.Jutila.s3Sig (r * t)
              * (Real.sqrt ((czUp N q r t : ℕ) : ℝ)
              * ((1 + |Real.log (2 * (czUp N q r t : ℝ)) - czAl w t|)
              * (1 + |Real.log (2 * (czUp N q r t : ℝ)) - czBe y r|)))) := by ring
          _ ≤ K * ((Work.ZeroDensity.Jutila.s3Sig r * Work.ZeroDensity.Jutila.s3Sig t)
              * (Real.sqrt ((N : ℝ) / ((q : ℝ) * (r : ℝ) * (t : ℝ)))
              * ((1 + Real.log (2 * (N : ℝ) / ((q : ℝ) * w * (r : ℝ))))
              * (1 + Real.log (2 * (N : ℝ) / ((q : ℝ) * y * (t : ℝ))))))) := by
              refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hK)
              refine mul_le_mul hsig_mul ?_ (by positivity) hσnn
              exact mul_le_mul hsqrtM (mul_le_mul hlog1 hlog2 hB0 hL1) (by positivity) hsq0
          _ = K * (Work.ZeroDensity.Jutila.s3Sig r * Work.ZeroDensity.Jutila.s3Sig t)
              * Real.sqrt ((N : ℝ) / ((q : ℝ) * (r : ℝ) * (t : ℝ)))
              * (1 + Real.log (2 * (N : ℝ) / ((q : ℝ) * w * (r : ℝ))))
              * (1 + Real.log (2 * (N : ℝ) / ((q : ℝ) * y * (t : ℝ)))) := by ring
      have hEB_le : |s3G (r * t) (czAl w t) (czBe y r) (czLo w y r t)
            - s3main (r * t) (czAl w t) (czBe y r) (czLo w y r t)|
          ≤ 25 * (K * Work.ZeroDensity.Jutila.s3Sig (r * t)
            * Real.sqrt ((czUp N q r t : ℕ) : ℝ)
            * (1 + |Real.log (2 * (czUp N q r t : ℝ)) - czAl w t|)
            * (1 + |Real.log (2 * (czUp N q r t : ℝ)) - czBe y r|)) := by
        have hle : czLo w y r t ≤ czUp N q r t :=
          Work.LinnikAreas2.czLo_le_czUp w y N q r t hw hy1 hq1 hr ht
        by_cases hlo0 : czLo w y r t = 0
        · have hpos : (0 : ℝ) ≤ 25 * (K * Work.ZeroDensity.Jutila.s3Sig (r * t)
              * Real.sqrt ((czUp N q r t : ℕ) : ℝ)
              * (1 + |Real.log (2 * (czUp N q r t : ℝ)) - czAl w t|)
              * (1 + |Real.log (2 * (czUp N q r t : ℝ)) - czBe y r|)) := by
            have h1 : (0 : ℝ) ≤ Work.ZeroDensity.Jutila.s3Sig (r * t) :=
              Work.ZeroDensity.Jutila.s3Sig_nonneg (r * t)
            positivity
          rw [hlo0, cz_E_zero (r * t) (czAl w t) (czBe y r)]
          simp only [sub_self, abs_zero]
          exact hpos
        · have hlo1 : 1 ≤ czLo w y r t := Nat.pos_of_ne_zero hlo0
          have h1 := hsharp (r * t) (czLo w y r t) (czAl w t) (czBe y r) hrt1 hlo1 hα hβ
          have h2 := cz_lo_le_up hlog (czLo w y r t) (czUp N q r t) hlo1 hle (czAl w t) (czBe y r)
          have hsig_rt : (0 : ℝ) ≤ Work.ZeroDensity.Jutila.s3Sig (r * t) :=
            Work.ZeroDensity.Jutila.s3Sig_nonneg (r * t)
          calc |s3G (r * t) (czAl w t) (czBe y r) (czLo w y r t)
                - s3main (r * t) (czAl w t) (czBe y r) (czLo w y r t)|
              ≤ K * Work.ZeroDensity.Jutila.s3Sig (r * t)
                * Real.sqrt (((czLo w y r t : ℕ)) : ℝ)
                * (1 + |Real.log (2 * ((czLo w y r t : ℕ) : ℝ)) - czAl w t|)
                * (1 + |Real.log (2 * ((czLo w y r t : ℕ) : ℝ)) - czBe y r|) := h1
            _ = (K * Work.ZeroDensity.Jutila.s3Sig (r * t))
                * (Real.sqrt (((czLo w y r t : ℕ)) : ℝ)
                * (1 + |Real.log (2 * ((czLo w y r t : ℕ) : ℝ)) - czAl w t|)
                * (1 + |Real.log (2 * ((czLo w y r t : ℕ) : ℝ)) - czBe y r|)) := by ring
            _ ≤ (K * Work.ZeroDensity.Jutila.s3Sig (r * t))
                * (25 * Real.sqrt ((czUp N q r t : ℕ) : ℝ)
                * (1 + |Real.log (2 * (czUp N q r t : ℝ)) - czAl w t|)
                * (1 + |Real.log (2 * (czUp N q r t : ℝ)) - czBe y r|)) :=
                mul_le_mul_of_nonneg_left h2 (by positivity)
            _ = 25 * (K * Work.ZeroDensity.Jutila.s3Sig (r * t)
                * Real.sqrt ((czUp N q r t : ℕ) : ℝ)
                * (1 + |Real.log (2 * (czUp N q r t : ℝ)) - czAl w t|)
                * (1 + |Real.log (2 * (czUp N q r t : ℝ)) - czBe y r|)) := by ring
      have hcz : |czMM r t| ≤ 1 := by
        rw [czMM]
        split
        · have h1 : |(ArithmeticFunction.moebius r : ℝ)| ≤ 1 := by
            have h := ArithmeticFunction.abs_moebius_le_one (n := r)
            rw [← Int.cast_abs]
            exact_mod_cast h
          have h2 : |(ArithmeticFunction.moebius t : ℝ)| ≤ 1 := by
            have h := ArithmeticFunction.abs_moebius_le_one (n := t)
            rw [← Int.cast_abs]
            exact_mod_cast h
          rw [abs_mul]
          nlinarith [abs_nonneg (ArithmeticFunction.moebius r : ℝ),
            abs_nonneg (ArithmeticFunction.moebius t : ℝ)]
        · simp
      calc |czMM r t * ((s3G (r * t) (czAl w t) (czBe y r) (czUp N q r t)
              - s3main (r * t) (czAl w t) (czBe y r) (czUp N q r t))
            - (s3G (r * t) (czAl w t) (czBe y r) (czLo w y r t)
              - s3main (r * t) (czAl w t) (czBe y r) (czLo w y r t)))|
          = |czMM r t| * |(s3G (r * t) (czAl w t) (czBe y r) (czUp N q r t)
              - s3main (r * t) (czAl w t) (czBe y r) (czUp N q r t))
            - (s3G (r * t) (czAl w t) (czBe y r) (czLo w y r t)
              - s3main (r * t) (czAl w t) (czBe y r) (czLo w y r t))| := by rw [abs_mul]
        _ ≤ 1 * (|s3G (r * t) (czAl w t) (czBe y r) (czUp N q r t)
              - s3main (r * t) (czAl w t) (czBe y r) (czUp N q r t)|
            + |s3G (r * t) (czAl w t) (czBe y r) (czLo w y r t)
              - s3main (r * t) (czAl w t) (czBe y r) (czLo w y r t)|) := by
            have hsub : |(s3G (r * t) (czAl w t) (czBe y r) (czUp N q r t)
                - s3main (r * t) (czAl w t) (czBe y r) (czUp N q r t))
              - (s3G (r * t) (czAl w t) (czBe y r) (czLo w y r t)
                - s3main (r * t) (czAl w t) (czBe y r) (czLo w y r t))|
                ≤ |s3G (r * t) (czAl w t) (czBe y r) (czUp N q r t)
                    - s3main (r * t) (czAl w t) (czBe y r) (czUp N q r t)|
                  + |s3G (r * t) (czAl w t) (czBe y r) (czLo w y r t)
                    - s3main (r * t) (czAl w t) (czBe y r) (czLo w y r t)| := by
              rw [abs_sub_le_iff]
              constructor <;>
                linarith [le_abs_self (s3G (r * t) (czAl w t) (czBe y r) (czUp N q r t)
                    - s3main (r * t) (czAl w t) (czBe y r) (czUp N q r t)),
                  neg_le_abs (s3G (r * t) (czAl w t) (czBe y r) (czLo w y r t)
                    - s3main (r * t) (czAl w t) (czBe y r) (czLo w y r t)),
                  le_abs_self (s3G (r * t) (czAl w t) (czBe y r) (czLo w y r t)
                    - s3main (r * t) (czAl w t) (czBe y r) (czLo w y r t)),
                  neg_le_abs (s3G (r * t) (czAl w t) (czBe y r) (czUp N q r t)
                    - s3main (r * t) (czAl w t) (czBe y r) (czUp N q r t))]
            have hnn : (0 : ℝ) ≤ |(s3G (r * t) (czAl w t) (czBe y r) (czUp N q r t)
                - s3main (r * t) (czAl w t) (czBe y r) (czUp N q r t))
              - (s3G (r * t) (czAl w t) (czBe y r) (czLo w y r t)
                - s3main (r * t) (czAl w t) (czBe y r) (czLo w y r t))| := abs_nonneg _
            nlinarith [hcz, hnn, hsub, abs_nonneg (s3G (r * t) (czAl w t) (czBe y r) (czUp N q r t)
              - s3main (r * t) (czAl w t) (czBe y r) (czUp N q r t))]
        _ = |s3G (r * t) (czAl w t) (czBe y r) (czUp N q r t)
              - s3main (r * t) (czAl w t) (czBe y r) (czUp N q r t)|
            + |s3G (r * t) (czAl w t) (czBe y r) (czLo w y r t)
              - s3main (r * t) (czAl w t) (czBe y r) (czLo w y r t)| := by ring
        _ ≤ (K * Work.ZeroDensity.Jutila.s3Sig (r * t)
              * Real.sqrt ((czUp N q r t : ℕ) : ℝ)
              * (1 + |Real.log (2 * (czUp N q r t : ℝ)) - czAl w t|)
              * (1 + |Real.log (2 * (czUp N q r t : ℝ)) - czBe y r|))
            + 25 * (K * Work.ZeroDensity.Jutila.s3Sig (r * t)
              * Real.sqrt ((czUp N q r t : ℕ) : ℝ)
              * (1 + |Real.log (2 * (czUp N q r t : ℝ)) - czAl w t|)
              * (1 + |Real.log (2 * (czUp N q r t : ℝ)) - czBe y r|)) :=
            add_le_add hEM_le hEB_le
        _ = 26 * (K * Work.ZeroDensity.Jutila.s3Sig (r * t)
              * Real.sqrt ((czUp N q r t : ℕ) : ℝ)
              * (1 + |Real.log (2 * (czUp N q r t : ℝ)) - czAl w t|)
              * (1 + |Real.log (2 * (czUp N q r t : ℝ)) - czBe y r|)) := by ring
        _ ≤ 26 * (K * (Work.ZeroDensity.Jutila.s3Sig r * Work.ZeroDensity.Jutila.s3Sig t)
              * Real.sqrt ((N : ℝ) / ((q : ℝ) * (r : ℝ) * (t : ℝ)))
              * (1 + Real.log (2 * (N : ℝ) / ((q : ℝ) * w * (r : ℝ))))
              * (1 + Real.log (2 * (N : ℝ) / ((q : ℝ) * y * (t : ℝ))))) :=
            mul_le_mul_of_nonneg_left hchainM (by norm_num)
        _ = 26 * K * (Work.ZeroDensity.Jutila.s3Sig r * Work.ZeroDensity.Jutila.s3Sig t
              * Real.sqrt ((N : ℝ) / ((q : ℝ) * (r : ℝ) * (t : ℝ)))
              * (1 + Real.log (2 * (N : ℝ) / ((q : ℝ) * w * (r : ℝ))))
              * (1 + Real.log (2 * (N : ℝ) / ((q : ℝ) * y * (t : ℝ))))) := by ring

  refine le_trans hmain ?_
  have hperq : ∀ q ∈ Finset.Icc 1 (czQ y N),
      (∑ r ∈ Finset.Icc 1 (czR w N q), ∑ t ∈ Finset.Icc 1 (czT y N q),
        26 * K * (Work.ZeroDensity.Jutila.s3Sig r * Work.ZeroDensity.Jutila.s3Sig t
          * Real.sqrt ((N : ℝ) / ((q : ℝ) * (r : ℝ) * (t : ℝ)))
          * (1 + Real.log (2 * (N : ℝ) / ((q : ℝ) * w * (r : ℝ))))
          * (1 + Real.log (2 * (N : ℝ) / ((q : ℝ) * y * (t : ℝ))))))
      ≤ 26 * K * (C₁ * C₁) * ((N : ℝ) * (1 / ((q : ℝ) * Real.sqrt (q : ℝ)))) := by
    intro q hq
    obtain ⟨hq1, hq2⟩ := Finset.mem_Icc.mp hq
    have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq1
    -- the `r`-sum
    have hRS : (∑ r ∈ Finset.Icc 1 (czR w N q), Work.ZeroDensity.Jutila.s3Sig r
          * (1 / Real.sqrt (r : ℝ))
          * (1 + Real.log (2 * (N : ℝ) / ((q : ℝ) * w * (r : ℝ)))))
        ≤ C₁ * Real.sqrt (((czR w N q : ℕ)) : ℝ) := by
      by_cases hR0 : czR w N q = 0
      · rw [hR0]
        simp
      · have hR1 : 1 ≤ czR w N q := Nat.pos_of_ne_zero hR0
        have hfloor_eq : (((czR w N q : ℕ)) : ℝ)
            = ((⌊(N : ℝ) / ((q : ℝ) * w)⌋₊ : ℕ) : ℝ) := by
          rw [czR]
        have hx1 : (1 : ℝ) ≤ (N : ℝ) / ((q : ℝ) * w) := by
          have hle : (((⌊(N : ℝ) / ((q : ℝ) * w)⌋₊ : ℕ)) : ℝ) ≤ (N : ℝ) / ((q : ℝ) * w) :=
            Nat.floor_le (by positivity)
          have h1 : (1 : ℝ) ≤ (((⌊(N : ℝ) / ((q : ℝ) * w)⌋₊ : ℕ)) : ℝ) := by
            rw [← hfloor_eq]; exact_mod_cast hR1
          linarith
        have hRV : (((czR w N q : ℕ)) : ℝ) ≤ 2 * ((N : ℝ) / ((q : ℝ) * w)) := by
          have hrle := cz_r_le_ofR w N q (czR w N q) hw0 hqpos (le_refl _)
          have h2 : (0 : ℝ) ≤ (N : ℝ) / ((q : ℝ) * w) := by positivity
          linarith
        have hA4 : 2 * ((N : ℝ) / ((q : ℝ) * w)) ≤ 4 * (((czR w N q : ℕ)) : ℝ) := by
          have hx : (N : ℝ) / ((q : ℝ) * w)
              ≤ 2 * (((⌊(N : ℝ) / ((q : ℝ) * w)⌋₊ : ℕ)) : ℝ) := cz_two_floor_ge _ hx1
          rw [hfloor_eq]
          linarith [hx]
        have h := hsigsum (czR w N q) (2 * ((N : ℝ) / ((q : ℝ) * w))) hR1 hRV hA4
        refine le_trans (le_of_eq (Finset.sum_congr rfl (fun r _ => ?_))) h
        have hlog : Real.log (2 * ((N : ℝ) / ((q : ℝ) * w)) / (r : ℝ))
            = Real.log (2 * (N : ℝ) / ((q : ℝ) * w * (r : ℝ))) := by
          congr 1
          ring_nf
        rw [hlog]
        ring
    -- the `t`-sum
    have hTS : (∑ t ∈ Finset.Icc 1 (czT y N q), Work.ZeroDensity.Jutila.s3Sig t
          * (1 / Real.sqrt (t : ℝ))
          * (1 + Real.log (2 * (N : ℝ) / ((q : ℝ) * y * (t : ℝ)))))
        ≤ C₁ * Real.sqrt (((czT y N q : ℕ)) : ℝ) := by
      by_cases hT0 : czT y N q = 0
      · rw [hT0]
        simp
      · have hT1 : 1 ≤ czT y N q := Nat.pos_of_ne_zero hT0
        have hfloor_eq : (((czT y N q : ℕ)) : ℝ)
            = ((⌊(N : ℝ) / ((q : ℝ) * y)⌋₊ : ℕ) : ℝ) := by
          rw [czT]
        have hx1 : (1 : ℝ) ≤ (N : ℝ) / ((q : ℝ) * y) := by
          have hle : (((⌊(N : ℝ) / ((q : ℝ) * y)⌋₊ : ℕ)) : ℝ) ≤ (N : ℝ) / ((q : ℝ) * y) :=
            Nat.floor_le (by positivity)
          have h1 : (1 : ℝ) ≤ (((⌊(N : ℝ) / ((q : ℝ) * y)⌋₊ : ℕ)) : ℝ) := by
            rw [← hfloor_eq]; exact_mod_cast hT1
          linarith
        have hTV : (((czT y N q : ℕ)) : ℝ) ≤ 2 * ((N : ℝ) / ((q : ℝ) * y)) := by
          have htle := cz_t_le_ofR y N q (czT y N q) hy0 hqpos (le_refl _)
          have h2 : (0 : ℝ) ≤ (N : ℝ) / ((q : ℝ) * y) := by positivity
          linarith
        have hA4 : 2 * ((N : ℝ) / ((q : ℝ) * y)) ≤ 4 * (((czT y N q : ℕ)) : ℝ) := by
          have hx : (N : ℝ) / ((q : ℝ) * y)
              ≤ 2 * (((⌊(N : ℝ) / ((q : ℝ) * y)⌋₊ : ℕ)) : ℝ) := cz_two_floor_ge _ hx1
          rw [hfloor_eq]
          linarith [hx]
        have h := hsigsum (czT y N q) (2 * ((N : ℝ) / ((q : ℝ) * y))) hT1 hTV hA4
        refine le_trans (le_of_eq (Finset.sum_congr rfl (fun t _ => ?_))) h
        have hlog : Real.log (2 * ((N : ℝ) / ((q : ℝ) * y)) / (t : ℝ))
            = Real.log (2 * (N : ℝ) / ((q : ℝ) * y * (t : ℝ))) := by
          congr 1
          ring_nf
        rw [hlog]
        ring
    -- the square-root factor
    have hsqrt3 : Real.sqrt ((N : ℝ) / (q : ℝ)) * Real.sqrt (((czR w N q : ℕ)) : ℝ)
          * Real.sqrt (((czT y N q : ℕ)) : ℝ)
        ≤ (N : ℝ) * (1 / ((q : ℝ) * Real.sqrt (q : ℝ))) := by
      have hR : Real.sqrt (((czR w N q : ℕ)) : ℝ) ≤ Real.sqrt ((N : ℝ) / ((q : ℝ) * w)) := by
        apply Real.sqrt_le_sqrt
        exact cz_r_le_ofR w N q (czR w N q) hw0 hqpos (le_refl _)
      have hT : Real.sqrt (((czT y N q : ℕ)) : ℝ) ≤ Real.sqrt ((N : ℝ) / ((q : ℝ) * y)) := by
        apply Real.sqrt_le_sqrt
        exact cz_t_le_ofR y N q (czT y N q) hy0 hqpos (le_refl _)
      have h1 : Real.sqrt ((N : ℝ) / (q : ℝ)) * Real.sqrt (((czR w N q : ℕ)) : ℝ)
            * Real.sqrt (((czT y N q : ℕ)) : ℝ)
          ≤ Real.sqrt ((N : ℝ) / (q : ℝ)) * Real.sqrt ((N : ℝ) / ((q : ℝ) * w))
            * Real.sqrt ((N : ℝ) / ((q : ℝ) * y)) := by
        have h2 : Real.sqrt (((czR w N q : ℕ)) : ℝ) * Real.sqrt (((czT y N q : ℕ)) : ℝ)
            ≤ Real.sqrt ((N : ℝ) / ((q : ℝ) * w)) * Real.sqrt ((N : ℝ) / ((q : ℝ) * y)) :=
          mul_le_mul hR hT (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
        calc Real.sqrt ((N : ℝ) / (q : ℝ)) * Real.sqrt (((czR w N q : ℕ)) : ℝ)
              * Real.sqrt (((czT y N q : ℕ)) : ℝ)
            = Real.sqrt ((N : ℝ) / (q : ℝ))
              * (Real.sqrt (((czR w N q : ℕ)) : ℝ) * Real.sqrt (((czT y N q : ℕ)) : ℝ)) := by ring
          _ ≤ Real.sqrt ((N : ℝ) / (q : ℝ))
              * (Real.sqrt ((N : ℝ) / ((q : ℝ) * w)) * Real.sqrt ((N : ℝ) / ((q : ℝ) * y))) :=
              mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg _)
          _ = Real.sqrt ((N : ℝ) / (q : ℝ)) * Real.sqrt ((N : ℝ) / ((q : ℝ) * w))
              * Real.sqrt ((N : ℝ) / ((q : ℝ) * y)) := by ring
      have h2 : Real.sqrt ((N : ℝ) / (q : ℝ)) * Real.sqrt ((N : ℝ) / ((q : ℝ) * w))
            * Real.sqrt ((N : ℝ) / ((q : ℝ) * y))
          = Real.sqrt ((N : ℝ)^3 / ((q : ℝ)^3 * w * y)) := by
        rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity)]
        congr 1
        ring_nf
      have h3 : Real.sqrt ((N : ℝ)^3 / ((q : ℝ)^3 * w * y))
          ≤ Real.sqrt ((N : ℝ)^2 / (q : ℝ)^3) := by
        apply Real.sqrt_le_sqrt
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have h1 : (N : ℝ) * ((N : ℝ) * ((q : ℝ)^3)) ≤ w * y * ((N : ℝ) * ((q : ℝ)^3)) :=
          mul_le_mul_of_nonneg_right (le_of_lt hhard) (by positivity)
        nlinarith [h1]
      have h4 : Real.sqrt ((N : ℝ)^2 / (q : ℝ)^3) = (N : ℝ) * (1 / ((q : ℝ) * Real.sqrt (q : ℝ))) := by
        have hq3 : Real.sqrt ((q : ℝ)^3) = (q : ℝ) * Real.sqrt (q : ℝ) := by
          rw [show ((q : ℝ)^3) = (q : ℝ)^2 * (q : ℝ) by ring, Real.sqrt_mul (by positivity),
            Real.sqrt_sq (by positivity)]
        rw [Real.sqrt_div (by positivity), Real.sqrt_sq (by positivity), hq3]
        field_simp
      linarith [h1, le_of_eq h2, h3, le_of_eq h4]
    -- assemble the `q`-slice
    have hslice : (∑ r ∈ Finset.Icc 1 (czR w N q), ∑ t ∈ Finset.Icc 1 (czT y N q),
        26 * K * (Work.ZeroDensity.Jutila.s3Sig r * Work.ZeroDensity.Jutila.s3Sig t
          * Real.sqrt ((N : ℝ) / ((q : ℝ) * (r : ℝ) * (t : ℝ)))
          * (1 + Real.log (2 * (N : ℝ) / ((q : ℝ) * w * (r : ℝ))))
          * (1 + Real.log (2 * (N : ℝ) / ((q : ℝ) * y * (t : ℝ))))))
        = 26 * K * (Real.sqrt ((N : ℝ) / (q : ℝ))
            * ((∑ r ∈ Finset.Icc 1 (czR w N q), Work.ZeroDensity.Jutila.s3Sig r
                * (1 / Real.sqrt (r : ℝ))
                * (1 + Real.log (2 * (N : ℝ) / ((q : ℝ) * w * (r : ℝ)))))
              * (∑ t ∈ Finset.Icc 1 (czT y N q), Work.ZeroDensity.Jutila.s3Sig t
                * (1 / Real.sqrt (t : ℝ))
                * (1 + Real.log (2 * (N : ℝ) / ((q : ℝ) * y * (t : ℝ))))))) := by
      have hterm : ∀ r ∈ Finset.Icc 1 (czR w N q), ∀ t ∈ Finset.Icc 1 (czT y N q),
          26 * K * (Work.ZeroDensity.Jutila.s3Sig r * Work.ZeroDensity.Jutila.s3Sig t
            * Real.sqrt ((N : ℝ) / ((q : ℝ) * (r : ℝ) * (t : ℝ)))
            * (1 + Real.log (2 * (N : ℝ) / ((q : ℝ) * w * (r : ℝ))))
            * (1 + Real.log (2 * (N : ℝ) / ((q : ℝ) * y * (t : ℝ)))))
          = (26 * K * Real.sqrt ((N : ℝ) / (q : ℝ))
              * (Work.ZeroDensity.Jutila.s3Sig r * (1 / Real.sqrt (r : ℝ))
                * (1 + Real.log (2 * (N : ℝ) / ((q : ℝ) * w * (r : ℝ)))))
              * (Work.ZeroDensity.Jutila.s3Sig t * (1 / Real.sqrt (t : ℝ))
                * (1 + Real.log (2 * (N : ℝ) / ((q : ℝ) * y * (t : ℝ)))))) := by
        intro r hr t ht
        obtain ⟨hr1, hr2⟩ := Finset.mem_Icc.mp hr
        obtain ⟨ht1, ht2⟩ := Finset.mem_Icc.mp ht
        rw [cz_sqrt_factor N q r t (by omega) (by omega) (by omega)]
        ring
      calc (∑ r ∈ Finset.Icc 1 (czR w N q), ∑ t ∈ Finset.Icc 1 (czT y N q),
            26 * K * (Work.ZeroDensity.Jutila.s3Sig r * Work.ZeroDensity.Jutila.s3Sig t
              * Real.sqrt ((N : ℝ) / ((q : ℝ) * (r : ℝ) * (t : ℝ)))
              * (1 + Real.log (2 * (N : ℝ) / ((q : ℝ) * w * (r : ℝ))))
              * (1 + Real.log (2 * (N : ℝ) / ((q : ℝ) * y * (t : ℝ))))))
          = ∑ r ∈ Finset.Icc 1 (czR w N q), ∑ t ∈ Finset.Icc 1 (czT y N q),
              (26 * K * Real.sqrt ((N : ℝ) / (q : ℝ))
                * (Work.ZeroDensity.Jutila.s3Sig r * (1 / Real.sqrt (r : ℝ))
                  * (1 + Real.log (2 * (N : ℝ) / ((q : ℝ) * w * (r : ℝ)))))
                * (Work.ZeroDensity.Jutila.s3Sig t * (1 / Real.sqrt (t : ℝ))
                  * (1 + Real.log (2 * (N : ℝ) / ((q : ℝ) * y * (t : ℝ)))))) :=
            Finset.sum_congr rfl (fun r hr => Finset.sum_congr rfl (fun t ht => hterm r hr t ht))
        _ = (∑ r ∈ Finset.Icc 1 (czR w N q), 26 * K * Real.sqrt ((N : ℝ) / (q : ℝ))
                * (Work.ZeroDensity.Jutila.s3Sig r * (1 / Real.sqrt (r : ℝ))
                  * (1 + Real.log (2 * (N : ℝ) / ((q : ℝ) * w * (r : ℝ))))))
              * (∑ t ∈ Finset.Icc 1 (czT y N q), Work.ZeroDensity.Jutila.s3Sig t
                * (1 / Real.sqrt (t : ℝ))
                * (1 + Real.log (2 * (N : ℝ) / ((q : ℝ) * y * (t : ℝ))))) :=
            (Finset.sum_mul_sum _ _ _ _).symm
        _ = 26 * K * (Real.sqrt ((N : ℝ) / (q : ℝ))
            * ((∑ r ∈ Finset.Icc 1 (czR w N q), Work.ZeroDensity.Jutila.s3Sig r
                * (1 / Real.sqrt (r : ℝ))
                * (1 + Real.log (2 * (N : ℝ) / ((q : ℝ) * w * (r : ℝ)))))
              * (∑ t ∈ Finset.Icc 1 (czT y N q), Work.ZeroDensity.Jutila.s3Sig t
                * (1 / Real.sqrt (t : ℝ))
                * (1 + Real.log (2 * (N : ℝ) / ((q : ℝ) * y * (t : ℝ))))))) := by
            rw [← Finset.mul_sum]
            ring
    rw [hslice]
    -- combine the three bounds
    have hCK : (0 : ℝ) ≤ 26 * K := by positivity
    have hsqrtq : (0 : ℝ) ≤ Real.sqrt ((N : ℝ) / (q : ℝ)) := Real.sqrt_nonneg _
    have hRnn : (0 : ℝ) ≤ C₁ * Real.sqrt (((czR w N q : ℕ)) : ℝ) := by positivity
    have hTnn : (0 : ℝ) ≤ C₁ * Real.sqrt (((czT y N q : ℕ)) : ℝ) := by positivity
    calc 26 * K * (Real.sqrt ((N : ℝ) / (q : ℝ))
          * ((∑ r ∈ Finset.Icc 1 (czR w N q), Work.ZeroDensity.Jutila.s3Sig r
              * (1 / Real.sqrt (r : ℝ))
              * (1 + Real.log (2 * (N : ℝ) / ((q : ℝ) * w * (r : ℝ)))))
            * (∑ t ∈ Finset.Icc 1 (czT y N q), Work.ZeroDensity.Jutila.s3Sig t
              * (1 / Real.sqrt (t : ℝ))
              * (1 + Real.log (2 * (N : ℝ) / ((q : ℝ) * y * (t : ℝ)))))))
        ≤ 26 * K * (Real.sqrt ((N : ℝ) / (q : ℝ))
            * ((C₁ * Real.sqrt (((czR w N q : ℕ)) : ℝ))
              * (C₁ * Real.sqrt (((czT y N q : ℕ)) : ℝ)))) := by
          refine mul_le_mul_of_nonneg_left ?_ hCK
          refine mul_le_mul_of_nonneg_left ?_ hsqrtq
          refine mul_le_mul hRS hTS ?_ hRnn
          refine Finset.sum_nonneg (fun t ht => ?_)
          obtain ⟨ht1, ht2⟩ := Finset.mem_Icc.mp ht
          have htt : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht1
          have htle := cz_t_le_ofR y N q t hy0 hqpos ht2
          have h2 : (t : ℝ) * ((q : ℝ) * y) ≤ (N : ℝ) :=
            (le_div_iff₀ (by positivity : (0 : ℝ) < (q : ℝ) * y)).mp htle
          have h3 : (1 : ℝ) ≤ 2 * (N : ℝ) / ((q : ℝ) * y * (t : ℝ)) := by
            rw [le_div_iff₀ (by positivity)]
            nlinarith [h2, hNpos]
          have h4 : (0 : ℝ) ≤ 1 + Real.log (2 * (N : ℝ) / ((q : ℝ) * y * (t : ℝ))) := by
            have := Real.log_nonneg h3
            linarith
          exact mul_nonneg (mul_nonneg (Work.ZeroDensity.Jutila.s3Sig_nonneg t) (by positivity)) h4
      _ = 26 * K * (C₁ * C₁) * (Real.sqrt ((N : ℝ) / (q : ℝ))
            * Real.sqrt (((czR w N q : ℕ)) : ℝ) * Real.sqrt (((czT y N q : ℕ)) : ℝ)) := by ring
      _ ≤ 26 * K * (C₁ * C₁) * ((N : ℝ) * (1 / ((q : ℝ) * Real.sqrt (q : ℝ)))) := by
          refine mul_le_mul_of_nonneg_left hsqrt3 ?_
          exact mul_nonneg (mul_nonneg (by norm_num) (le_of_lt hK))
            (mul_nonneg (le_of_lt hC₁) (le_of_lt hC₁))
  calc (∑ q ∈ Finset.Icc 1 (czQ y N), ∑ r ∈ Finset.Icc 1 (czR w N q),
        ∑ t ∈ Finset.Icc 1 (czT y N q),
          26 * K * (Work.ZeroDensity.Jutila.s3Sig r * Work.ZeroDensity.Jutila.s3Sig t
            * Real.sqrt ((N : ℝ) / ((q : ℝ) * (r : ℝ) * (t : ℝ)))
            * (1 + Real.log (2 * (N : ℝ) / ((q : ℝ) * w * (r : ℝ))))
            * (1 + Real.log (2 * (N : ℝ) / ((q : ℝ) * y * (t : ℝ))))))
      ≤ ∑ q ∈ Finset.Icc 1 (czQ y N),
          26 * K * (C₁ * C₁) * ((N : ℝ) * (1 / ((q : ℝ) * Real.sqrt (q : ℝ)))) :=
        Finset.sum_le_sum hperq
    _ = 26 * K * (C₁ * C₁) * (N : ℝ)
          * (∑ q ∈ Finset.Icc 1 (czQ y N), 1 / ((q : ℝ) * Real.sqrt (q : ℝ))) := by
        rw [Finset.mul_sum]
        ring_nf
    _ ≤ 26 * K * (C₁ * C₁) * (N : ℝ) * 3 := by
        refine mul_le_mul_of_nonneg_left (cz_sum_inv_mul_sqrt_le (czQ y N)) (by positivity)
    _ ≤ (26 * (K * (C₁ * C₁)) * (1 + 3) + 1) * (N : ℝ) := by
        have h1 : (0 : ℝ) ≤ (N : ℝ) := le_of_lt hNpos
        have h2 : (26 : ℝ) * K * (C₁ * C₁) * 3
            ≤ (26 * (K * (C₁ * C₁)) * (1 + 3) + 1) := by
          have h3 : (0 : ℝ) ≤ K * (C₁ * C₁) := by
            exact mul_nonneg (le_of_lt hK) (mul_nonneg (le_of_lt hC₁) (le_of_lt hC₁))
          nlinarith [h3]
        calc 26 * K * (C₁ * C₁) * (N : ℝ) * 3
            = (26 * K * (C₁ * C₁) * 3) * (N : ℝ) := by ring
          _ ≤ (26 * (K * (C₁ * C₁)) * (1 + 3) + 1) * (N : ℝ) :=
              mul_le_mul_of_nonneg_right h2 h1

/-! ## Part 7: the target theorem -/

end

end Work.ZeroDensity.Jutila.LzDiffAux
