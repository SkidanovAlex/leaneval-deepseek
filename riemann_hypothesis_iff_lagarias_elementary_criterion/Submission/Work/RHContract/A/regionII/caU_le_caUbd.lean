import Mathlib
import Submission.Work.RHContract.A.regionII.abnum
import Submission.Work.RHContract.A.regionII.Defs

/-!
# Region II: the size comparison `(36/100) caU z ≤ caUbd n`

`caU ξ = 1/(√ξ log ξ)` and `caUbd n` is the rational upper bound for `(36/100) caU`
proved in `abnum.lean`.  Here we check that, for `30000 ≤ z ≤ 10^5`, `173 ≤ n ≤ 501`
and `n ≤ √(2.5 z) + 1`, indeed `(36/100) caU z ≤ caUbd n`:

* if `n ≤ 274` we use `√z ≥ √30000 ≥ sq30000l` and `log z ≥ log 30000 ≥ lg30000l`;
* if `n ≥ 275` then `(n : ℝ) - 1 ≤ √(2.5 z)`, so
  `√z ≥ ((n : ℝ) - 1) · inv25` and `z ≥ ((n:ℝ)-1)^2/2.5`, hence
  `log z ≥ 2 log ((n:ℝ)-1) - log 2.5 ≥ 2 chordA n - lg25u`.

The numerical inputs are the certified bracketing lemmas
`ThetaBracket.ltOf_le_log` / `ThetaBracket.log_le_utOf`.
-/

namespace Work.RHContract.A.regionII

open Work.RHContract.A.RegionII

/-- `lg273 = (ltOf 273)/10^9 ≤ log 273`. -/
lemma lg273_le_log : RegionII.lg273 ≤ Real.log 273 := by
  have h := Commons.NumberTheory.Chebyshev.ThetaBracket.ltOf_le_log 273 (by norm_num)
  have hnum : (Commons.NumberTheory.Chebyshev.ThetaBracket.ltOf 273 : ℕ) = 5609470336 := by
    decide
  have h2 : ((5609470336 : ℕ) : ℝ) ≤ 10 ^ 9 * Real.log (273 : ℝ) := by rw [← hnum]; exact h
  rw [RegionII.lg273]
  norm_num at h2 ⊢
  linarith

/-- `lg513 = (ltOf 513)/10^9 ≤ log 513`. -/
lemma lg513_le_log : RegionII.lg513 ≤ Real.log 513 := by
  have h := Commons.NumberTheory.Chebyshev.ThetaBracket.ltOf_le_log 513 (by norm_num)
  have hnum : (Commons.NumberTheory.Chebyshev.ThetaBracket.ltOf 513 : ℕ) = 6240274220 := by
    decide
  have h2 : ((6240274220 : ℕ) : ℝ) ≤ 10 ^ 9 * Real.log (513 : ℝ) := by rw [← hnum]; exact h
  rw [RegionII.lg513]
  norm_num at h2 ⊢
  linarith

/-- `lg30000l = (ltOf 30000)/10^9 ≤ log 30000`. -/
lemma lg30000l_le_log : RegionII.lg30000l ≤ Real.log 30000 := by
  have h := Commons.NumberTheory.Chebyshev.ThetaBracket.ltOf_le_log 30000 (by norm_num)
  have hnum : (Commons.NumberTheory.Chebyshev.ThetaBracket.ltOf 30000 : ℕ) = 10308020696 := by
    decide
  have h2 : ((10308020696 : ℕ) : ℝ) ≤ 10 ^ 9 * Real.log (30000 : ℝ) := by rw [← hnum]; exact h
  rw [RegionII.lg30000l]
  norm_num at h2 ⊢
  linarith

/-- `log 2.5 = log 5 - log 2 ≤ (utOf 5 - ltOf 2)/10^9 = lg25u`. -/
lemma log25_le_lg25u : Real.log 2.5 ≤ RegionII.lg25u := by
  have h2ge : (693147000 : ℝ) ≤ 10 ^ 9 * Real.log 2 :=
    Commons.NumberTheory.Chebyshev.ThetaBracket.log2_ge
  have h5le : 10 ^ 9 * Real.log (5 : ℝ) ≤ (1611320000 : ℝ) := by
    have h := Commons.NumberTheory.Chebyshev.ThetaBracket.log_le_utOf 5 (by norm_num)
    have hnum : (Commons.NumberTheory.Chebyshev.ThetaBracket.utOf 5 : ℕ) = 1611320000 := by
      decide
    have h' : 10 ^ 9 * Real.log (5 : ℝ) ≤ ((1611320000 : ℕ) : ℝ) := by rw [← hnum]; exact h
    simpa using h'
  have h25 : Real.log 2.5 = Real.log 5 - Real.log 2 := by
    rw [show (2.5 : ℝ) = 5 / 2 by norm_num, Real.log_div (by norm_num) (by norm_num)]
  rw [h25, RegionII.lg25u]
  norm_num
  linarith

/-- `sq30000l ≤ √30000`. -/
lemma sq30000l_le_sqrt30000 : RegionII.sq30000l ≤ Real.sqrt 30000 := by
  rw [RegionII.sq30000l, Real.le_sqrt (by norm_num) (by norm_num)]
  norm_num

/-- `inv25 ≤ 1/√2.5`. -/
lemma inv25_le_inv_sqrt25 : RegionII.inv25 ≤ 1 / Real.sqrt 2.5 := by
  have hp : 0 < Real.sqrt 2.5 := Real.sqrt_pos.2 (by norm_num)
  rw [le_div_iff₀ hp, RegionII.inv25]
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2.5 by norm_num), Real.sqrt_nonneg 2.5]

/-- Concavity of `log`: for `275 ≤ n ≤ 501` the chord `chordA n` lies below `log (n-1)`. -/
lemma chordA_le_log (n : ℕ) (h1 : 275 ≤ n) (h2 : n ≤ 501) :
    RegionII.chordA n ≤ Real.log ((n : ℝ) - 1) := by
  have hnR : (275 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h1
  have hnR2 : (n : ℝ) ≤ 501 := by exact_mod_cast h2
  have ht274 : (274 : ℝ) ≤ (n : ℝ) - 1 := by linarith
  have ht513 : (n : ℝ) - 1 ≤ 513 := by linarith
  have hlt : (273 : ℝ) < (n : ℝ) - 1 := by linarith
  have hlt2 : (n : ℝ) - 1 < 513 := by linarith
  have htlog : 0 ≤ Real.log ((n : ℝ) - 1) := Real.log_nonneg (by linarith)
  -- concavity of `log`
  have hconc : ConcaveOn ℝ (Set.Ioi (0 : ℝ)) Real.log := strictConcaveOn_log_Ioi.concaveOn
  have h0 := ConvexOn.secant_mono_aux1 hconc.neg
    (show (273 : ℝ) ∈ Set.Ioi (0 : ℝ) from by norm_num)
    (show (513 : ℝ) ∈ Set.Ioi (0 : ℝ) from by norm_num) hlt hlt2
  simp only [Pi.neg_apply] at h0
  -- the chord bound with the exact logarithms
  have hchord : (513 - ((n : ℝ) - 1)) * Real.log 273 + (((n : ℝ) - 1) - 273) * Real.log 513
      ≤ 240 * Real.log ((n : ℝ) - 1) := by linarith [h0]
  -- rewrite `chordA` in the same shape
  have hshape : RegionII.chordA n
      = ((514 - (n : ℝ)) * RegionII.lg273 + ((n : ℝ) - 274) * RegionII.lg513) / 240 := by
    rw [RegionII.chordA]
    ring
  rw [hshape]
  have c1 : 0 ≤ 514 - (n : ℝ) := by linarith
  have c2 : 0 ≤ (n : ℝ) - 274 := by linarith
  have hA := mul_le_mul_of_nonneg_left lg273_le_log c1
  have hB := mul_le_mul_of_nonneg_left lg513_le_log c2
  have hfin : ((514 - (n : ℝ)) * Real.log 273 + ((n : ℝ) - 274) * Real.log 513) / 240
      ≤ Real.log ((n : ℝ) - 1) := by
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 240)]
    linarith
  linarith

theorem caU_le_caUbd (z n : ℕ) (hz : 30000 ≤ z) (hz2 : z ≤ 10 ^ 5) (hn : 173 ≤ n) (hn2 : n ≤ 501)
    (hlink : (n : ℝ) ≤ Real.sqrt (2.5 * z) + 1) :
    (36/100) * Work.RHContract.A.RegionII.caU (z : ℝ)
      ≤ Work.RHContract.A.RegionII.caUbd n := by
  have hzR : (30000 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
  have hsqrtz : 0 ≤ Real.sqrt (z : ℝ) := Real.sqrt_nonneg _
  rw [RegionII.caUbd]
  by_cases hn274 : n ≤ 274
  · rw [if_pos hn274, RegionII.caU]
    have hs : RegionII.sq30000l ≤ Real.sqrt (z : ℝ) :=
      le_trans sq30000l_le_sqrt30000 (Real.sqrt_le_sqrt hzR)
    have hl : RegionII.lg30000l ≤ Real.log (z : ℝ) :=
      le_trans lg30000l_le_log (Real.log_le_log (by norm_num) hzR)
    have hp1 : 0 < RegionII.sq30000l := by norm_num [RegionII.sq30000l]
    have hp2 : 0 < RegionII.lg30000l := by norm_num [RegionII.lg30000l]
    have hprod : RegionII.sq30000l * RegionII.lg30000l
        ≤ Real.sqrt (z : ℝ) * Real.log (z : ℝ) :=
      mul_le_mul hs hl (le_of_lt hp2) hsqrtz
    have h1 : 1 / (Real.sqrt (z : ℝ) * Real.log (z : ℝ))
        ≤ 1 / (RegionII.sq30000l * RegionII.lg30000l) :=
      one_div_le_one_div_of_le (mul_pos hp1 hp2) hprod
    calc (36 / 100) * (1 / (Real.sqrt (z : ℝ) * Real.log (z : ℝ)))
        ≤ (36 / 100) * (1 / (RegionII.sq30000l * RegionII.lg30000l)) :=
          mul_le_mul_of_nonneg_left h1 (by norm_num)
      _ = (36 / 100) / (RegionII.sq30000l * RegionII.lg30000l) := by ring
  · rw [if_neg hn274, RegionII.caU]
    have hn275 : 275 ≤ n := by omega
    have hnR : (275 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn275
    have hrpos : 0 < (n : ℝ) - 1 := by linarith
    have hlink' : (n : ℝ) - 1 ≤ Real.sqrt (2.5 * (z : ℝ)) := by linarith [hlink]
    -- lower bound for `√z`
    have hsqrt_le : ((n : ℝ) - 1) * RegionII.inv25 ≤ Real.sqrt (z : ℝ) := by
      have hstep1 : ((n : ℝ) - 1) * RegionII.inv25
          ≤ Real.sqrt (2.5 * (z : ℝ)) * RegionII.inv25 :=
        mul_le_mul_of_nonneg_right hlink' (by norm_num [RegionII.inv25])
      have hstep2 : Real.sqrt (2.5 * (z : ℝ)) * RegionII.inv25 ≤ Real.sqrt (z : ℝ) := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2.5) (z : ℝ)]
        have hmul : Real.sqrt 2.5 * RegionII.inv25 ≤ 1 := by
          have hs := Real.sqrt_nonneg 2.5
          have hsne : Real.sqrt 2.5 ≠ 0 :=
            ne_of_gt (Real.sqrt_pos.2 (by norm_num))
          calc Real.sqrt 2.5 * RegionII.inv25 ≤ Real.sqrt 2.5 * (1 / Real.sqrt 2.5) :=
                mul_le_mul_of_nonneg_left inv25_le_inv_sqrt25 hs
            _ = 1 := by rw [mul_one_div, div_self hsne]
        calc Real.sqrt 2.5 * Real.sqrt (z : ℝ) * RegionII.inv25
            = Real.sqrt (z : ℝ) * (Real.sqrt 2.5 * RegionII.inv25) := by ring
          _ ≤ Real.sqrt (z : ℝ) * 1 := mul_le_mul_of_nonneg_left hmul hsqrtz
          _ = Real.sqrt (z : ℝ) := by ring
      linarith
    -- lower bound for `log z`
    have hzge : ((n : ℝ) - 1) ^ 2 / 2.5 ≤ (z : ℝ) := by
      have h1 : ((n : ℝ) - 1) ^ 2 ≤ (Real.sqrt (2.5 * (z : ℝ))) ^ 2 :=
        pow_le_pow_left₀ (le_of_lt hrpos) hlink' 2
      rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2.5 * (z : ℝ))] at h1
      rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2.5)]
      linarith
    have hlogz_lb : 2 * Real.log ((n : ℝ) - 1) - Real.log 2.5 ≤ Real.log (z : ℝ) := by
      have harg : 0 < ((n : ℝ) - 1) ^ 2 / 2.5 := by positivity
      have hmono := Real.log_le_log harg hzge
      have hsplit : Real.log (((n : ℝ) - 1) ^ 2 / 2.5)
          = 2 * Real.log ((n : ℝ) - 1) - Real.log 2.5 := by
        rw [Real.log_div (by positivity) (by norm_num : (2.5 : ℝ) ≠ 0), Real.log_pow]
        push_cast
        ring
      linarith
    have hchord : RegionII.chordA n ≤ Real.log ((n : ℝ) - 1) := chordA_le_log n hn275 hn2
    have hQ : 2 * RegionII.chordA n - RegionII.lg25u ≤ Real.log (z : ℝ) := by
      linarith [log25_le_lg25u, hlogz_lb, hchord]
    -- positivity
    have hchord_ge : RegionII.lg273 ≤ RegionII.chordA n := by
      rw [RegionII.chordA]
      have h1 : 0 ≤ ((n : ℝ) - 274) * (RegionII.lg513 - RegionII.lg273) / 240 := by
        apply div_nonneg _ (by norm_num)
        apply mul_nonneg
        · have h274 : (274 : ℝ) ≤ (n : ℝ) := by
            exact_mod_cast (by omega : 274 ≤ n)
          linarith
        · have hle : RegionII.lg273 ≤ RegionII.lg513 := by
            norm_num [RegionII.lg273, RegionII.lg513]
          linarith
      linarith
    have hQpos : 0 < 2 * RegionII.chordA n - RegionII.lg25u := by
      have h1 : (0 : ℝ) < RegionII.lg273 := by norm_num [RegionII.lg273]
      have h2 : RegionII.lg25u < 2 * RegionII.lg273 := by
        norm_num [RegionII.lg25u, RegionII.lg273]
      linarith
    have hPpos : 0 < ((n : ℝ) - 1) * RegionII.inv25 :=
      mul_pos hrpos (by norm_num [RegionII.inv25])
    -- combine
    have hprod : ((n : ℝ) - 1) * RegionII.inv25 * (2 * RegionII.chordA n - RegionII.lg25u)
        ≤ Real.sqrt (z : ℝ) * Real.log (z : ℝ) :=
      mul_le_mul hsqrt_le hQ (le_of_lt hQpos) hsqrtz
    have h1 : 1 / (Real.sqrt (z : ℝ) * Real.log (z : ℝ))
        ≤ 1 / (((n : ℝ) - 1) * RegionII.inv25 * (2 * RegionII.chordA n - RegionII.lg25u)) :=
      one_div_le_one_div_of_le (mul_pos hPpos hQpos) hprod
    calc (36 / 100) * (1 / (Real.sqrt (z : ℝ) * Real.log (z : ℝ)))
        ≤ (36 / 100) * (1 / (((n : ℝ) - 1) * RegionII.inv25
            * (2 * RegionII.chordA n - RegionII.lg25u))) :=
          mul_le_mul_of_nonneg_left h1 (by norm_num)
      _ = (36 / 100) / (((n : ℝ) - 1) * RegionII.inv25
            * (2 * RegionII.chordA n - RegionII.lg25u)) := by ring

end Work.RHContract.A.regionII
