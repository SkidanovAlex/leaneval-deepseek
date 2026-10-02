import Mathlib
import Submission.Work.ZeroDensity.Jutila.BzCross.czReindexDefs
import Submission.Work.ZeroDensity.Jutila.BzCross.CzRIAux

set_option maxHeartbeats 2000000

namespace Work.ZeroDensity.Jutila.BzCross

open Finset

noncomputable section

/-! ## Quadratic deviation bounds for `exp` -/

lemma czExpDeviation (x : ℝ) (hx : |x| ≤ 1) :
    |Real.exp x * (x - 1) + 1| ≤ 3 * x ^ 2 ∧
    |Real.exp x * (x ^ 2 - x + 1) - 1| ≤ 4 * x ^ 2 := by
  have hR : |Real.exp x - 1 - x| ≤ x ^ 2 := Real.abs_exp_sub_one_sub_id_le hx
  have hxsq : (0:ℝ) ≤ x ^ 2 := sq_nonneg x
  have hx1 : x ≤ 1 := (abs_le.mp hx).2
  have hxn : (0:ℝ) ≤ |x| := abs_nonneg x
  have habs1 : |x - 1| ≤ 1 + |x| := by
    have h := abs_add_le x (-1)
    rw [abs_neg, abs_one] at h
    rw [sub_eq_add_neg]
    linarith only [h]
  have habs2 : |x ^ 2 - x| ≤ |x ^ 2| + |x| := by
    have h := abs_add_le (x ^ 2) (-x)
    rw [abs_neg] at h
    rw [sub_eq_add_neg]
    exact h
  constructor
  · have h1 : Real.exp x * (x - 1) + 1 = x ^ 2 + (Real.exp x - 1 - x) * (x - 1) := by ring
    rw [h1]
    have h2 : |(Real.exp x - 1 - x) * (x - 1)| ≤ x ^ 2 * (1 + |x|) := by
      rw [abs_mul]
      exact mul_le_mul hR habs1 (abs_nonneg _) hxsq
    calc |x ^ 2 + (Real.exp x - 1 - x) * (x - 1)|
        ≤ |x ^ 2| + |(Real.exp x - 1 - x) * (x - 1)| := abs_add_le _ _
      _ = x ^ 2 + |(Real.exp x - 1 - x) * (x - 1)| := by rw [abs_of_nonneg hxsq]
      _ ≤ x ^ 2 + x ^ 2 * (1 + |x|) := by linarith only [h2]
      _ ≤ 3 * x ^ 2 := by nlinarith only [hxsq, hxn, hx]
  · have h1 : Real.exp x * (x ^ 2 - x + 1) - 1
        = x ^ 3 + (Real.exp x - 1 - x) * (x ^ 2 - x + 1) := by ring
    rw [h1]
    have hb : |x ^ 2 - x + 1| ≤ 3 := by
      have hx2 : x ^ 2 ≤ 1 := by
        rw [← sq_abs]; nlinarith only [hxn, hx]
      calc |x ^ 2 - x + 1| ≤ |x ^ 2| + |x| + 1 := by
            calc |x ^ 2 - x + 1| ≤ |x ^ 2 - x| + |1| := abs_add_le _ _
              _ ≤ (|x ^ 2| + |x|) + 1 := by
                  rw [abs_one]
                  linarith only [habs2]
              _ = |x ^ 2| + |x| + 1 := by ring
        _ ≤ 1 + 1 + 1 := by
            rw [abs_of_nonneg hxsq]
            linarith only [hx2, hx]
        _ = 3 := by norm_num
    have h2 : |(Real.exp x - 1 - x) * (x ^ 2 - x + 1)| ≤ x ^ 2 * 3 := by
      rw [abs_mul]
      exact mul_le_mul hR hb (by norm_num) hxsq
    have hx3 : |x ^ 3| ≤ x ^ 2 := by
      rw [abs_pow]
      calc |x| ^ 3 = |x| ^ 2 * |x| := by ring
        _ = x ^ 2 * |x| := by rw [sq_abs]
        _ ≤ x ^ 2 * 1 := mul_le_mul_of_nonneg_left hx hxsq
        _ = x ^ 2 := mul_one _
    calc |x ^ 3 + (Real.exp x - 1 - x) * (x ^ 2 - x + 1)|
        ≤ |x ^ 3| + |(Real.exp x - 1 - x) * (x ^ 2 - x + 1)| := abs_add_le _ _
      _ ≤ x ^ 2 + x ^ 2 * 3 := by linarith only [h2, hx3]
      _ = 4 * x ^ 2 := by ring

/-! ## Two elementary number-theoretic bounds -/

lemma czKapDivLeSig (r : ℕ) (hr : Squarefree r) :
    Work.ZeroDensity.Jutila.kap r / (r : ℝ)
      ≤ ∑ d ∈ r.divisors, 1 / Real.sqrt (d : ℝ) := by
  have hr0 : r ≠ 0 := hr.ne_zero
  have hpm : (∏ p ∈ r.primeFactors, (p:ℝ)) = (r:ℝ) := by
    rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hr]
  have h1 : Work.ZeroDensity.Jutila.kap r / (r:ℝ)
      = ∏ p ∈ r.primeFactors, (1 + 1/(p:ℝ)) := by
    rw [Work.ZeroDensity.Jutila.kap, ← hpm, ← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun p hp => ?_
    have hp0 : (p:ℝ) ≠ 0 := by
      have := (Nat.prime_of_mem_primeFactors hp).ne_zero
      exact_mod_cast this
    field_simp
  rw [h1]
  have hinj : Set.InjOn (fun t : Finset ℕ => ∏ p ∈ t, p) ↑(r.primeFactors.powerset) := by
    intro x hx y hy hxy
    have hx' : ∀ p ∈ x, p.Prime := fun p hp =>
      Nat.prime_of_mem_primeFactors ((Finset.mem_powerset.mp hx) hp)
    have hy' : ∀ p ∈ y, p.Prime := fun p hp =>
      Nat.prime_of_mem_primeFactors ((Finset.mem_powerset.mp hy) hp)
    have hxy' : (∏ p ∈ x, p) = (∏ p ∈ y, p) := hxy
    calc x = Nat.primeFactors (∏ p ∈ x, p) := (Nat.primeFactors_prod hx').symm
      _ = Nat.primeFactors (∏ p ∈ y, p) := by rw [hxy']
      _ = y := Nat.primeFactors_prod hy'
  have hsub : (r.primeFactors.powerset.image (fun t : Finset ℕ => ∏ p ∈ t, p)) ⊆ r.divisors := by
    intro d hd
    rw [Finset.mem_image] at hd
    obtain ⟨t, ht, rfl⟩ := hd
    have hts : t ⊆ r.primeFactors := Finset.mem_powerset.mp ht
    refine Nat.mem_divisors.mpr ⟨?_, hr0⟩
    calc (∏ p ∈ t, p) ∣ (∏ p ∈ r.primeFactors, p) :=
          Finset.prod_dvd_prod_of_subset t r.primeFactors (fun x => x) hts
      _ = r := Nat.prod_primeFactors_of_squarefree hr
  calc ∏ p ∈ r.primeFactors, (1 + 1/(p:ℝ))
      = ∑ t ∈ r.primeFactors.powerset, ∏ p ∈ t, (1/(p:ℝ)) := Finset.prod_one_add _
    _ = ∑ t ∈ r.primeFactors.powerset, (((∏ p ∈ t, p : ℕ)) : ℝ)⁻¹ := by
        refine Finset.sum_congr rfl fun t _ => ?_
        simp only [one_div]
        rw [Finset.prod_inv_distrib, Nat.cast_prod]
    _ = ∑ d ∈ r.primeFactors.powerset.image (fun t : Finset ℕ => ∏ p ∈ t, p), (d:ℝ)⁻¹ := by
        rw [Finset.sum_image]
        exact hinj
    _ ≤ ∑ d ∈ r.primeFactors.powerset.image (fun t : Finset ℕ => ∏ p ∈ t, p),
          1 / Real.sqrt (d:ℝ) := by
        refine Finset.sum_le_sum fun d hd => ?_
        have hd1 : 1 ≤ d := Nat.pos_of_mem_divisors (hsub hd)
        have hdpos : 0 < (d:ℝ) := by exact_mod_cast (by omega : 0 < d)
        have hsq : 0 < Real.sqrt (d:ℝ) := Real.sqrt_pos.mpr hdpos
        have hd1R : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd1
        have hle : Real.sqrt (d:ℝ) ≤ (d:ℝ) := by
          rw [Real.sqrt_le_iff]
          exact ⟨hdpos.le, by nlinarith only [hdpos, hd1R]⟩
        simpa only [one_div] using one_div_le_one_div_of_le hsq hle
    _ ≤ ∑ d ∈ r.divisors, 1 / Real.sqrt (d:ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun d _ _ => by positivity)

lemma czMuKapWeightLe (t : ℕ) (ht : 1 ≤ t) :
    |(ArithmeticFunction.moebius t : ℝ)| / Work.ZeroDensity.Jutila.kap t ≤ 1 / (t : ℝ) := by
  have htpos : (0:ℝ) < (t:ℝ) := by exact_mod_cast (by omega : 0 < t)
  have hkpos : 0 < Work.ZeroDensity.Jutila.kap t := Work.ZeroDensity.Jutila.kap_pos t
  by_cases h : Squarefree t
  · have hmu : |(ArithmeticFunction.moebius t : ℝ)| ≤ 1 := by
      have h1 : |ArithmeticFunction.moebius t| ≤ 1 := ArithmeticFunction.abs_moebius_le_one
      rw [← Int.cast_abs]
      exact_mod_cast h1
    have hkt : (t:ℝ) ≤ Work.ZeroDensity.Jutila.kap t := kap_ge_self h
    calc |(ArithmeticFunction.moebius t : ℝ)| / Work.ZeroDensity.Jutila.kap t
        ≤ 1 / Work.ZeroDensity.Jutila.kap t := div_le_div_of_nonneg_right hmu hkpos.le
      _ ≤ 1 / (t:ℝ) := one_div_le_one_div_of_le htpos hkt
  · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree h]
    simp only [Int.cast_zero, abs_zero, zero_div]
    positivity

/-! ## Range bounds for `czTmax` -/

lemma czFloorHalf (w : ℝ) (hw : 1 ≤ w) : w / 2 ≤ ((⌊w⌋₊ : ℕ) : ℝ) := by
  by_cases h : w ≤ 2
  · have hfl : (1:ℝ) ≤ ((⌊w⌋₊ : ℕ) : ℝ) := by
      have : 1 ≤ ⌊w⌋₊ := (Nat.one_le_floor_iff w).mpr hw
      exact_mod_cast this
    linarith only [h, hfl]
  · rw [not_le] at h
    have hfl : w - 1 ≤ ((⌊w⌋₊ : ℕ) : ℝ) := by
      have := Nat.lt_floor_add_one w
      linarith only [this]
    linarith only [h, hfl]

lemma czCrossRangeBounds {w y : ℝ} {N q r : ℕ} (hw1 : 1 ≤ w) (hwy : w ≤ y)
    (hNwy : (N : ℝ) < w * y) (hr1 : 1 ≤ r) (hrR : r ≤ czR w N q) :
    (r : ℝ) < y ∧
    ((czTmax w y N q r : ℕ) : ℝ) ≤ w / 2 ∧
    ((czTmax w y N q r : ℕ) : ℝ) ≤ w * (r : ℝ) / y ∧
    (1 ≤ czTmax w y N q r → w * (r : ℝ) / y ≤ 4 * ((czTmax w y N q r : ℕ) : ℝ)) ∧
    (1 ≤ czTmax w y N q r → y / (r : ℝ) < w) := by
  have hw0 : 0 < w := by linarith only [hw1]
  have hy0 : 0 < y := by linarith only [hw1, hwy]
  have hr0 : 0 < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  have hq1 : 1 ≤ q := by
    by_contra hq
    push Not at hq
    have hq0 : q = 0 := by omega
    rw [hq0] at hrR
    simp [czR] at hrR
    omega
  have hq0' : (0:ℝ) < (q:ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hq1R : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq1
  have hry : (r:ℝ) < y := by
    have hcast : (r:ℝ) ≤ ((czR w N q : ℕ) : ℝ) := by exact_mod_cast hrR
    have hfl : ((czR w N q : ℕ) : ℝ) ≤ (N:ℝ)/((q:ℝ)*w) := by
      rw [czR]; exact Nat.floor_le (by positivity)
    have hlt : (N:ℝ)/((q:ℝ)*w) < y/(q:ℝ) := by
      rw [div_lt_div_iff₀ (by positivity) hq0']
      have h2 : (N:ℝ) * (q:ℝ) < (w*y) * (q:ℝ) :=
        mul_lt_mul_of_pos_right (by linarith only [hNwy] : (N:ℝ) < w*y) hq0'
      linarith only [h2]
    have hle : y/(q:ℝ) ≤ y := by
      rw [div_le_iff₀ hq0']
      nlinarith only [hy0, hq1R, hw1, hwy]
    linarith only [hcast, hfl, hlt, hle]
  have hκ1 : 1 ≤ ⌊y/(r:ℝ)⌋₊ := by
    rw [Nat.one_le_floor_iff, le_div_iff₀ hr0]
    linarith only [hry]
  set κ : ℕ := ⌊y/(r:ℝ)⌋₊ with hκdef
  have hκ1' : 1 ≤ κ := hκ1
  have hden : (2:ℝ) ≤ ((κ:ℕ):ℝ) + 1 := by
    have : (1:ℝ) ≤ (κ:ℝ) := by exact_mod_cast hκ1'
    linarith only [this]
  have hTle : czTmax w y N q r ≤ ⌊w / (((κ:ℕ):ℝ) + 1)⌋₊ := by
    rw [czTmax]; simp only [← hκdef]; exact min_le_right _ _
  have hTw2 : ((czTmax w y N q r : ℕ) : ℝ) ≤ w / 2 := by
    calc ((czTmax w y N q r : ℕ) : ℝ) ≤ ((⌊w / (((κ:ℕ):ℝ) + 1)⌋₊ : ℕ) : ℝ) := by
          exact_mod_cast hTle
      _ ≤ w / (((κ:ℕ):ℝ) + 1) := Nat.floor_le (by positivity)
      _ ≤ w / 2 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith only [hw0, hden, hw1]
  have hltκ : y/(r:ℝ) < ((κ:ℕ):ℝ) + 1 := by
    have hh := Nat.lt_floor_add_one (y/(r:ℝ))
    rw [← hκdef] at hh
    exact hh
  have hTρ : ((czTmax w y N q r : ℕ) : ℝ) ≤ w * (r:ℝ)/y := by
    have h1 : ((czTmax w y N q r : ℕ) : ℝ) ≤ w / (((κ:ℕ):ℝ) + 1) :=
      le_trans (by exact_mod_cast hTle) (Nat.floor_le (by positivity))
    have h2 : w / (((κ:ℕ):ℝ) + 1) < w / (y/(r:ℝ)) := by
      rw [div_lt_div_iff₀ (by positivity) (by positivity)]
      nlinarith only [hltκ, hw0, hy0, hr0, hw1]
    have h3 : w / (y/(r:ℝ)) = w * (r:ℝ)/y := by
      rw [div_div_eq_mul_div, mul_comm]
    linarith only [h1, h2, le_of_eq h3]
  have hTyw : 1 ≤ czTmax w y N q r → y / (r:ℝ) < w := by
    intro hT1
    have hthat : (1:ℕ) ≤ ⌊w / (((κ:ℕ):ℝ) + 1)⌋₊ := by omega
    have h1 : (1:ℝ) ≤ w / (((κ:ℕ):ℝ) + 1) :=
      le_trans (by exact_mod_cast hthat) (Nat.floor_le (by positivity))
    rw [le_div_iff₀ (by positivity)] at h1
    linarith only [hltκ, h1]
  refine ⟨hry, hTw2, hTρ, ?_, hTyw⟩
  intro hT1
  have hTle2 : (1:ℝ) ≤ ((czTmax w y N q r : ℕ) : ℝ) := by exact_mod_cast hT1
  have hczT1 : (1:ℝ) ≤ ((czT y N q : ℕ) : ℝ) := by
    have hle : czTmax w y N q r ≤ czT y N q := by
      rw [czTmax]; exact min_le_left _ _
    have hh : ((czTmax w y N q r : ℕ) : ℝ) ≤ ((czT y N q : ℕ) : ℝ) := by exact_mod_cast hle
    linarith only [hTle2, hh]
  have hrR' : (r:ℝ) ≤ (N:ℝ)/((q:ℝ)*w) := by
    have h1 : (r:ℝ) ≤ ((czR w N q : ℕ) : ℝ) := by exact_mod_cast hrR
    have h2 : ((czR w N q : ℕ) : ℝ) ≤ (N:ℝ)/((q:ℝ)*w) := by
      rw [czR]; exact Nat.floor_le (by positivity)
    linarith only [h1, h2]
  by_cases hcase : czT y N q ≤ ⌊w / (((κ:ℕ):ℝ) + 1)⌋₊
  · have hTeq : czTmax w y N q r = czT y N q := by
      rw [czTmax]; simp only [← hκdef]; exact min_eq_left hcase
    rw [hTeq]
    have hrR'' : (r:ℝ)*((q:ℝ)*w) ≤ (N:ℝ) := (le_div_iff₀ (by positivity)).mp hrR'
    have hwry : w*(r:ℝ)/y ≤ (N:ℝ)/((q:ℝ)*y) := by
      rw [div_le_div_iff₀ hy0 (by positivity)]
      nlinarith only [hrR'', hw0, hy0, hq0', hw1, hwy]
    have hX : (N:ℝ)/((q:ℝ)*y) < ((czT y N q : ℕ) : ℝ) + 1 := by
      have hh := Nat.lt_floor_add_one ((N:ℝ)/((q:ℝ)*y))
      rw [czT]
      exact hh
    linarith only [hwry, hX, hczT1]
  · rw [not_le] at hcase
    have hTeq : czTmax w y N q r = ⌊w / (((κ:ℕ):ℝ) + 1)⌋₊ := by
      rw [czTmax]; simp only [← hκdef]; exact min_eq_right (le_of_lt hcase)
    rw [hTeq]
    have hκR : (κ:ℝ) ≤ y/(r:ℝ) := by
      rw [hκdef]; exact Nat.floor_le (by positivity)
    have hκR' : (κ:ℝ)*(r:ℝ) ≤ y := (le_div_iff₀ hr0).mp hκR
    have hwry : w*(r:ℝ)/y ≤ w/(κ:ℝ) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith only [hκR', hw0, hw1]
    have hκ1R : (1:ℝ) ≤ (κ:ℝ) := by exact_mod_cast hκ1'
    have h2 : w/(κ:ℝ) ≤ 2 * (w/((κ:ℝ)+1)) := by
      rw [div_le_iff₀ (by positivity)]
      rw [show 2 * (w / ((κ:ℝ)+1)) * (κ:ℝ) = 2*w*(κ:ℝ)/((κ:ℝ)+1) by ring]
      rw [le_div_iff₀ (by positivity)]
      nlinarith only [hκ1R, hw0, hden, hw1]
    have hT'1 : (1:ℝ) ≤ w/((κ:ℝ)+1) := by
      have hthat : (1:ℕ) ≤ ⌊w / (((κ:ℕ):ℝ) + 1)⌋₊ := by
        rw [← hTeq]; omega
      exact le_trans (by exact_mod_cast hthat) (Nat.floor_le (by positivity))
    have hT'' : w/((κ:ℝ)+1)/2 ≤ ((⌊w / (((κ:ℕ):ℝ) + 1)⌋₊ : ℕ) : ℝ) :=
      floor_ge_half hT'1
    linarith only [hwry, h2, hT'']


/-! ## The decomposition of `czInSum`

For `k` ranging in `1 ≤ k ≤ T ≤ w/2`, write `A_k = ⌊w/k⌋`, `θ_k = w - k·A_k` (the floor defect),
`U_k = log(A_k k / w)`, `E_k = e^{U_k}`, `L_k = log(ρ/k)` with `ρ = w r / y`.  Then
`E_k·czFII = (2 - L_k) + AA_k(L_k - 1) + GG_k` with `AA_k = e^{U_k}(U_k - 1) + 1` and
`GG_k = e^{U_k}(U_k^2 - U_k + 1) - 1`, and the last two functions are `O(U_k^2) = O(θ_k^2/w^2)`. -/

def czU (w : ℝ) (k : ℕ) : ℝ := Real.log ((⌊w / (k:ℝ)⌋₊ : ℝ) * (k:ℝ) / w)
def czEE (w : ℝ) (k : ℕ) : ℝ := Real.exp (czU w k)
def czLL (ρ : ℝ) (k : ℕ) : ℝ := Real.log (ρ / (k:ℝ))
def czTh (w : ℝ) (k : ℕ) : ℝ := w - (⌊w / (k:ℝ)⌋₊ : ℝ) * (k:ℝ)
def czAA (w : ℝ) (k : ℕ) : ℝ := czEE w k * (czU w k - 1) + 1
def czGG (w : ℝ) (k : ℕ) : ℝ := czEE w k * (czU w k ^ 2 - czU w k + 1) - 1

lemma czEE_eq {w : ℝ} {k : ℕ} (h : 0 < (⌊w / (k:ℝ)⌋₊ : ℝ) * (k:ℝ) / w) :
    czEE w k = (⌊w / (k:ℝ)⌋₊ : ℝ) * (k:ℝ) / w := by
  rw [czEE, czU, Real.exp_log h]

lemma czTh_main {w : ℝ} {k : ℕ} (hw : 0 < w) (hk : 0 < (k:ℝ)) :
    czU w k = Real.log (1 - czTh w k / w) := by
  rw [czU, czTh]
  congr 1
  field_simp <;> ring

/-- The pointwise decomposition `E_k·czFII = (2 - L_k) + AA_k (L_k - 1) + GG_k`. -/
lemma czPointwise (w y : ℝ) (r k : ℕ) (ρ : ℝ) (hρ : ρ = w * (r:ℝ) / y)
    (hw : 0 < w) (hy : 0 < y) (hk : 0 < (k:ℝ)) (hA : 0 < (⌊w / (k:ℝ)⌋₊ : ℝ)) (hρ0 : 0 < ρ) :
    czEE w k * czFII w y r k = (2 - czLL ρ k) + czAA w k * (czLL ρ k - 1) + czGG w k := by
  rw [czAA, czGG]
  rw [show czEE w k = (⌊w / (k:ℝ)⌋₊ : ℝ) * (k:ℝ) / w from czEE_eq (by positivity)]
  have hv : Real.log ((⌊w / (k:ℝ)⌋₊ : ℝ) * (r:ℝ) / y) = czU w k + czLL ρ k := by
    rw [czU, czLL]
    have e1 : (⌊w / (k:ℝ)⌋₊ : ℝ) * (r:ℝ) / y
        = ((⌊w / (k:ℝ)⌋₊ : ℝ) * (k:ℝ) / w) * (ρ / (k:ℝ)) := by
      rw [hρ]; field_simp <;> ring
    rw [e1, Real.log_mul (by positivity) (by positivity)]
  rw [czFII, hv]
  simp only [czU]
  ring_nf

lemma czEE_eq' {w : ℝ} {k : ℕ} (hw : 0 < w) (hk : 0 < (k:ℝ))
    (hA : 0 < (⌊w / (k:ℝ)⌋₊ : ℝ)) :
    czEE w k = (⌊w / (k:ℝ)⌋₊ : ℝ) * (k:ℝ) / w :=
  czEE_eq (by positivity)

lemma czTh_nonneg {w : ℝ} {k : ℕ} (hw : 0 ≤ w) (hk : 0 < (k:ℝ)) :
    0 ≤ czTh w k := by
  rw [czTh]
  have h := Nat.floor_le (show (0:ℝ) ≤ w / (k:ℝ) by positivity)
  have h2 : (⌊w / (k:ℝ)⌋₊ : ℝ) * (k:ℝ) ≤ w := by
    have h3 := mul_le_mul_of_nonneg_right h hk.le
    rwa [div_mul_cancel₀ _ hk.ne'] at h3
  linarith only [h2]

lemma czTh_lt {w : ℝ} {k : ℕ} (hk : 0 < (k:ℝ)) : czTh w k < (k:ℝ) := by
  rw [czTh]
  have h := (div_lt_iff₀ hk).mp (Nat.lt_floor_add_one (w / (k:ℝ)))
  linarith only [h]

lemma czU_nonpos {w : ℝ} {k : ℕ} (hw : 0 < w) (hk : 0 < (k:ℝ)) (hth : czTh w k < w / 2) :
    czU w k ≤ 0 := by
  rw [czTh_main hw hk]
  have hθnn : 0 ≤ czTh w k := czTh_nonneg hw.le hk
  have hle : (1:ℝ) - czTh w k / w ≤ 1 := by
    have : 0 ≤ czTh w k / w := by positivity
    linarith only [this]
  have hpos : (0:ℝ) < 1 - czTh w k / w := by
    have : czTh w k / w < 1 := by rw [div_lt_one hw]; linarith only [hth, hw]
    linarith only [this]
  have h := Real.log_le_log hpos hle
  rwa [Real.log_one] at h

lemma czU_sq_le {w : ℝ} {k : ℕ} (hw : 0 < w) (hk : 0 < (k:ℝ)) (hth : czTh w k < w / 2) :
    (czU w k) ^ 2 ≤ 4 * (czTh w k) ^ 2 / w ^ 2 := by
  have hθnn : 0 ≤ czTh w k := czTh_nonneg hw.le hk
  have hU0 : czU w k ≤ 0 := czU_nonpos hw hk hth
  have habs : |czU w k| ≤ czTh w k / (w - czTh w k) := by
    rw [abs_of_nonpos hU0, czTh_main hw hk, ← Real.log_inv]
    have hne : w - czTh w k ≠ 0 := by linarith only [hth, hw]
    have h2 : (1 - czTh w k / w)⁻¹ = w / (w - czTh w k) := by field_simp <;> ring
    rw [h2]
    have h3 : 0 < w / (w - czTh w k) := div_pos hw (by linarith only [hth, hw])
    have h4 := Real.log_le_sub_one_of_pos h3
    have h5 : w / (w - czTh w k) - 1 = czTh w k / (w - czTh w k) := by field_simp <;> ring
    linarith only [h4, le_of_eq h5, h5]
  have hden : w - czTh w k > w / 2 := by linarith only [hth]
  have h2 : czTh w k / (w - czTh w k) ≤ 2 * czTh w k / w := by
    rw [div_le_div_iff₀ (by linarith only [hw, hth]) hw]
    nlinarith only [hden, hθnn, hth]
  have h3 : |czU w k| ≤ 2 * czTh w k / w := le_trans habs h2
  have h4 : (czU w k) ^ 2 ≤ (2 * czTh w k / w) ^ 2 := by
    rw [sq_le_sq, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * czTh w k / w)]
    exact h3
  have h5 : (2 * czTh w k / w) ^ 2 = 4 * (czTh w k) ^ 2 / w ^ 2 := by ring
  linarith only [h4, le_of_eq h5, h5]

lemma czU_abs_le_one {w : ℝ} {k : ℕ} (hw : 0 < w) (hk : 0 < (k:ℝ)) (hth : czTh w k < w / 2) :
    |czU w k| ≤ 1 := by
  have hθnn : 0 ≤ czTh w k := czTh_nonneg hw.le hk
  have hθw : czTh w k / w < 1 / 2 := by rw [div_lt_iff₀ hw]; linarith only [hth]
  have hU0 : czU w k ≤ 0 := czU_nonpos hw hk hth
  have hhalf : (1:ℝ) / 2 ≤ 1 - czTh w k / w := by linarith only [hθw]
  have hlow : -Real.log 2 ≤ czU w k := by
    rw [czTh_main hw hk]
    have h := Real.log_le_log (by norm_num : (0:ℝ) < 1/2) hhalf
    have h2 : Real.log (1/2) = -Real.log 2 := by rw [one_div, Real.log_inv]
    rw [h2] at h
    exact h
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
    linarith only [h]
  rw [abs_le]
  exact ⟨by linarith only [hlow, hlog2], by linarith only [hU0]⟩

lemma czTh_sq_le {w : ℝ} {k : ℕ} (hw : 0 ≤ w) (hk : 0 < (k:ℝ)) :
    (czTh w k) ^ 2 ≤ (k:ℝ) ^ 2 := by
  have h1 : 0 ≤ czTh w k := czTh_nonneg hw hk
  have h2 : czTh w k < (k:ℝ) := czTh_lt hk
  nlinarith only [h1, h2]

lemma czLL_nonneg {ρ : ℝ} {k : ℕ} (h : 1 ≤ ρ / (k:ℝ)) : 0 ≤ czLL ρ k := by
  rw [czLL]; exact Real.log_nonneg h

lemma czLL_add_one_le {ρ : ℝ} {k : ℕ} (h : 1 ≤ ρ / (k:ℝ)) : czLL ρ k + 1 ≤ ρ / (k:ℝ) := by
  rw [czLL]
  have hpos : 0 < ρ / (k:ℝ) := lt_of_lt_of_le zero_lt_one h
  have := Real.log_le_sub_one_of_pos hpos
  linarith only [this]

lemma czLL_abs_sub_one_le {ρ : ℝ} {k : ℕ} (h : 1 ≤ ρ / (k:ℝ)) :
    |czLL ρ k - 1| ≤ ρ / (k:ℝ) := by
  have h0 := czLL_nonneg h
  have h1 := czLL_add_one_le h
  rw [abs_le]
  constructor <;> linarith only [h, h0, h1]

/-- The final arithmetic step. -/
lemma czFinalStep {C0 C w σ ε x : ℝ} (hC0 : 0 < C0) (hC : C = (2 + Real.log 4) * C0 + 100)
    (hσ : 1 ≤ σ) (hw : 0 < w) (hε : 0 ≤ ε) (hx : 0 ≤ x) :
    w * (C0 * σ * (2 + Real.log 4) * ε + 64 * x) ≤ C * w * σ * (ε + x) := by
  have hlog4 : (0:ℝ) < Real.log 4 := Real.log_pos (by norm_num)
  have hCbig : (64:ℝ) ≤ C := by rw [hC]; nlinarith only [hC0, hlog4]
  have hCcoef : C0 * (2 + Real.log 4) ≤ C := by rw [hC]; linarith only [hC0, hlog4]
  have hσ0 : 0 < σ := lt_of_lt_of_le zero_lt_one hσ
  have h1 : C0 * σ * (2 + Real.log 4) * ε ≤ C * σ * ε := by
    have h2 : C0 * (2 + Real.log 4) * σ ≤ C * σ := by
      have hh := mul_le_mul_of_nonneg_right hCcoef hσ0.le
      linarith only [hh]
    nlinarith only [h2, hε]
  have h2 : 64 * x ≤ C * σ * x := by
    have h3 : (64:ℝ) ≤ C * σ := by nlinarith only [hCbig, hσ, hC0, hC, hlog4]
    nlinarith only [h3, hx]
  nlinarith only [h1, h2, hw]

end


theorem czInSum_bound2 (h : Work.ZeroDensity.Jutila.KappaMertensInput) :
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
  ∀ (w y : ℝ) (N q r : ℕ), 1 ≤ w → w ≤ y → (N:ℝ) < w*y →
    Squarefree r → 1 ≤ r → r ≤ Work.ZeroDensity.Jutila.czR w N q →
    |Work.ZeroDensity.Jutila.BzCross.czInSum w y N q r
        + w * (Real.pi^2/6) * (Work.ZeroDensity.Jutila.kap r / r)|
      ≤ C * w * (∑ d ∈ r.divisors, 1/Real.sqrt d) *
          (Work.ZeroDensity.Jutila.Dc c (Work.ZeroDensity.Jutila.BzCross.czTmax w y N q r)
            + ((Work.ZeroDensity.Jutila.BzCross.czTmax w y N q r : ℝ)/w)^2) := by
  obtain ⟨C0, c0, hC0, hc0, hK1, hK2⟩ := h
  refine ⟨(2 + Real.log 4) * C0 + 100, c0, ?_, hc0, ?_⟩
  · have h4 : (0:ℝ) < Real.log 4 := Real.log_pos (by norm_num)
    nlinarith only [hC0, h4]
  intro w y N q r hw1 hwy hNwy hsq hr1 hrR
  set T : ℕ := czTmax w y N q r with hTdef
  set σ : ℝ := ∑ d ∈ r.divisors, 1/Real.sqrt d with hσdef
  set ρ : ℝ := w * (r:ℝ) / y with hρdef
  have hw0 : 0 < w := by linarith only [hw1]
  have hy0 : 0 < y := by linarith only [hw1, hwy]
  have hr0 : 0 < (r:ℝ) := by exact_mod_cast (by omega : 0 < r)
  obtain ⟨hry, hTw2, hTleρ, hρle4T, hTyw⟩ := czCrossRangeBounds hw1 hwy hNwy hr1 hrR
  rw [← hTdef] at hTw2 hTleρ hρle4T hTyw
  rw [← hρdef] at hTleρ hρle4T
  have hρpos : 0 < ρ := by rw [hρdef]; positivity
  have hσ1 : (1:ℝ) ≤ σ := by
    rw [hσdef]
    have h1mem : 1 ∈ r.divisors := Nat.one_mem_divisors.mpr (by omega : r ≠ 0)
    calc (1:ℝ) = 1/Real.sqrt (((1:ℕ)):ℝ) := by norm_num
      _ ≤ ∑ d ∈ r.divisors, 1/Real.sqrt (d:ℝ) :=
          Finset.single_le_sum (f := fun d : ℕ => 1/Real.sqrt (d:ℝ)) (fun i _ => by positivity) h1mem
  rcases lt_or_ge T 2 with hTlt | hT2
  · -- T ≤ 1
    have hT01 : T = 0 ∨ T = 1 := by omega
    have hDc1 : Work.ZeroDensity.Jutila.Dc c0 T = 1 := by
      rcases hT01 with hh | hh <;> rw [hh] <;> simp [Work.ZeroDensity.Jutila.Dc]
    have hsmall : |czInSum w y N q r| ≤ 7 * w := by
      rcases hT01 with hT0 | hT1
      · rw [czInSum, ← hTdef, hT0]
        have hemp : Finset.Icc 1 0 = (∅ : Finset ℕ) := by simp
        rw [hemp, Finset.sum_empty, abs_zero]
        positivity
      · have hcz1 : czInSum w y N q r = (⌊w⌋₊ : ℝ) * czFII w y r 1 := by
          rw [czInSum, ← hTdef, hT1, Finset.Icc_self, Finset.sum_singleton]
          simp [Work.ZeroDensity.Jutila.kap, ArithmeticFunction.moebius_apply_one,
            Nat.coprime_one_right_iff]
        rw [hcz1]
        have hfl1 : (1:ℝ) ≤ ((⌊w⌋₊ : ℕ) : ℝ) := by
          have : 1 ≤ ⌊w⌋₊ := (Nat.one_le_floor_iff w).mpr hw1
          exact_mod_cast this
        have ha : |Real.log ((⌊w⌋₊:ℝ)/w)| ≤ Real.log 2 := by
          have hhalf : (1:ℝ)/2 ≤ (⌊w⌋₊:ℝ)/w := by
            rw [le_div_iff₀ hw0]
            have := czFloorHalf w hw1
            linarith only [this]
          have hle1 : (⌊w⌋₊:ℝ)/w ≤ 1 := by
            rw [div_le_one hw0]; exact Nat.floor_le (by positivity)
          have hpos : 0 < (⌊w⌋₊:ℝ)/w := by positivity
          rw [abs_le]
          constructor
          · have h := Real.log_le_log (by norm_num : (0:ℝ) < 1/2) hhalf
            have h2 : Real.log (1/2) = -Real.log 2 := by rw [one_div, Real.log_inv]
            rw [h2] at h
            linarith only [h]
          · have h := Real.log_le_log hpos hle1
            rw [Real.log_one] at h
            have h2 : (0:ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
            linarith only [h, h2]
        have hb : |Real.log ((⌊w⌋₊:ℝ)*(r:ℝ)/y)| ≤ Real.log 4 := by
          have h1 : (⌊w⌋₊:ℝ) ≤ w := Nat.floor_le (by positivity)
          have h2 : (0:ℝ) ≤ (r:ℝ)/y := by positivity
          have hup : (⌊w⌋₊:ℝ)*(r:ℝ)/y ≤ 4 := by
            have h3 : w * (r:ℝ) / y = ρ := by rw [hρdef]
            have h4 : ρ ≤ 4 := by
              have := hρle4T (by omega : 1 ≤ T)
              rw [hT1] at this
              norm_num at this
              exact this
            have h5 : (⌊w⌋₊:ℝ)*(r:ℝ) ≤ w*(r:ℝ) := mul_le_mul_of_nonneg_right h1 (by positivity)
            have h6 : (⌊w⌋₊:ℝ)*(r:ℝ)/y ≤ w*(r:ℝ)/y := div_le_div_of_nonneg_right h5 hy0.le
            linarith only [h6, h3, h4]
          have hlo : (1:ℝ)/2 ≤ (⌊w⌋₊:ℝ)*(r:ℝ)/y := by
            have h1 : y / (r:ℝ) < w := hTyw (by omega : 1 ≤ T)
            have h2 : (1:ℝ)/w < (r:ℝ)/y := by
              rw [div_lt_div_iff₀ hw0 hy0]
              have := (div_lt_iff₀ hr0).mp h1
              linarith only [this]
            have h3 := czFloorHalf w hw1
            have h4 : (w/2) * ((1:ℝ)/w) ≤ (⌊w⌋₊:ℝ) * (r:ℝ) / y := by
              have h := mul_le_mul h3 (le_of_lt h2) (by positivity) (by positivity)
              rwa [show (⌊w⌋₊:ℝ) * ((r:ℝ)/y) = (⌊w⌋₊:ℝ) * (r:ℝ) / y by ring] at h
            have h5 : (w/2) * ((1:ℝ)/w) = 1/2 := by field_simp <;> ring
            linarith only [h4, le_of_eq h5, h5]
          have hpos : 0 < (⌊w⌋₊:ℝ)*(r:ℝ)/y := by positivity
          rw [abs_le]
          constructor
          · have h := Real.log_le_log (by norm_num : (0:ℝ) < 1/2) hlo
            have h2 : Real.log (1/2) = -Real.log 2 := by rw [one_div, Real.log_inv]
            rw [h2] at h
            have h3 : Real.log 2 ≤ Real.log 4 := Real.log_le_log (by norm_num) (by norm_num)
            linarith only [h, h3]
          · have h := Real.log_le_log hpos hup
            linarith only [h]
        have hlog2le1 : Real.log 2 ≤ 1 := by
          have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2); linarith only [h]
        have hlog4le2 : Real.log 4 ≤ 2 := by
          have h : Real.log 4 = 2 * Real.log 2 := by
            rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; norm_num
          linarith only [hlog2le1, h]
        have hfii : |czFII w y r 1| ≤ 7 := by
          rw [czFII]
          simp only [div_one, Nat.cast_one, mul_one]
          have e1 : |Real.log ((⌊w⌋₊:ℝ)/w) - 1| ≤ Real.log 2 + 1 := by
            rw [sub_eq_add_neg]
            calc |Real.log ((⌊w⌋₊:ℝ)/w) + -1| ≤ |Real.log ((⌊w⌋₊:ℝ)/w)| + |-1| := abs_add_le _ _
              _ = |Real.log ((⌊w⌋₊:ℝ)/w)| + 1 := by rw [abs_neg, abs_one]
              _ ≤ Real.log 2 + 1 := by linarith only [ha]
          have e2 : |Real.log ((⌊w⌋₊:ℝ)*(r:ℝ)/y) - 1| ≤ Real.log 4 + 1 := by
            rw [sub_eq_add_neg]
            calc |Real.log ((⌊w⌋₊:ℝ)*(r:ℝ)/y) + -1| 
                ≤ |Real.log ((⌊w⌋₊:ℝ)*(r:ℝ)/y)| + |-1| := abs_add_le _ _
              _ = |Real.log ((⌊w⌋₊:ℝ)*(r:ℝ)/y)| + 1 := by rw [abs_neg, abs_one]
              _ ≤ Real.log 4 + 1 := by linarith only [hb]
          have e3 : |(Real.log ((⌊w⌋₊:ℝ)/w) - 1) * (Real.log ((⌊w⌋₊:ℝ)*(r:ℝ)/y) - 1) + 1|
              ≤ (Real.log 2 + 1) * (Real.log 4 + 1) + 1 := by
            have hm : |(Real.log ((⌊w⌋₊:ℝ)/w) - 1) * (Real.log ((⌊w⌋₊:ℝ)*(r:ℝ)/y) - 1)|
                ≤ (Real.log 2 + 1) * (Real.log 4 + 1) := by
              rw [abs_mul]
              exact mul_le_mul e1 e2 (abs_nonneg _) (by positivity)
            have h := abs_add_le ((Real.log ((⌊w⌋₊:ℝ)/w) - 1) * (Real.log ((⌊w⌋₊:ℝ)*(r:ℝ)/y) - 1)) 1
            rw [abs_one] at h
            linarith only [h, hm]
          have h21 : (0:ℝ) ≤ Real.log 2 + 1 := by linarith only [Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)]
          have h41 : (0:ℝ) ≤ Real.log 4 + 1 := by linarith only [Real.log_nonneg (by norm_num : (1:ℝ) ≤ 4)]
          have hmul : (Real.log 2 + 1) * (Real.log 4 + 1) ≤ 2 * 3 :=
            mul_le_mul (by linarith only [hlog2le1]) (by linarith only [hlog4le2]) h41 (by norm_num : (0:ℝ) ≤ 2)
          linarith only [e3, hmul]
        calc |(⌊w⌋₊ : ℝ) * czFII w y r 1| 
            = (⌊w⌋₊ : ℝ) * |czFII w y r 1| := by
              rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (⌊w⌋₊:ℝ))]
          _ ≤ w * 7 := mul_le_mul (Nat.floor_le (by positivity)) hfii (abs_nonneg _) (by positivity)
          _ = 7 * w := by ring
    have hks : Work.ZeroDensity.Jutila.kap r / (r:ℝ) ≤ σ := by
      rw [hσdef]; exact czKapDivLeSig r hsq
    have hπ : Real.pi^2/6 ≤ 3 := by nlinarith only [Real.pi_le_four, Real.pi_pos]
    have hC10 : (10:ℝ) ≤ (2 + Real.log 4) * C0 + 100 := by
      have h4 : (0:ℝ) < Real.log 4 := Real.log_pos (by norm_num); nlinarith only [hC0, h4]
    have hLHS : |czInSum w y N q r + w * (Real.pi^2/6) * (Work.ZeroDensity.Jutila.kap r / (r:ℝ))|
        ≤ 7 * w + w * (Real.pi^2/6) * σ := by
      calc |czInSum w y N q r + w * (Real.pi^2/6) * (Work.ZeroDensity.Jutila.kap r / (r:ℝ))|
          ≤ |czInSum w y N q r| + |w * (Real.pi^2/6) * (Work.ZeroDensity.Jutila.kap r / (r:ℝ))| := abs_add_le _ _
        _ ≤ 7 * w + w * (Real.pi^2/6) * σ := by
            have hknn : (0:ℝ) ≤ w * (Real.pi^2/6) * (Work.ZeroDensity.Jutila.kap r / (r:ℝ)) :=
              mul_nonneg (mul_nonneg hw0.le (by positivity))
                (div_nonneg (Work.ZeroDensity.Jutila.kap_pos r).le (by positivity))
            have hk : w * (Real.pi^2/6) * (Work.ZeroDensity.Jutila.kap r / (r:ℝ))
                = |w * (Real.pi^2/6) * (Work.ZeroDensity.Jutila.kap r / (r:ℝ))| := (abs_of_nonneg hknn).symm
            rw [← hk]
            have := mul_le_mul_of_nonneg_left hks (by positivity : (0:ℝ) ≤ w * (Real.pi^2/6))
            linarith only [hsmall, this]
    have hfin : 7 * w + w * (Real.pi^2/6) * σ ≤ ((2 + Real.log 4) * C0 + 100) * w * σ := by
      have h1 : 7 * w ≤ 7 * (w * σ) := by
        have := mul_le_mul_of_nonneg_left hσ1 (show (0:ℝ) ≤ 7 * w by positivity)
        linarith only [this]
      calc 7 * w + w * (Real.pi^2/6) * σ
          = 7 * w + (Real.pi^2/6) * (w * σ) := by ring
        _ ≤ 7 * (w * σ) + (Real.pi^2/6) * (w * σ) := by linarith only [h1]
        _ = (7 + Real.pi^2/6) * (w * σ) := by ring
        _ ≤ ((2 + Real.log 4) * C0 + 100) * (w * σ) :=
            mul_le_mul_of_nonneg_right (by linarith only [hπ, hC10]) (by positivity)
        _ = ((2 + Real.log 4) * C0 + 100) * w * σ := by ring
    have hRHSge : ((2 + Real.log 4) * C0 + 100) * w * σ
        ≤ ((2 + Real.log 4) * C0 + 100) * w * σ * (Work.ZeroDensity.Jutila.Dc c0 T + ((T:ℝ)/w)^2) := by
      have h1 : (1:ℝ) ≤ Work.ZeroDensity.Jutila.Dc c0 T + ((T:ℝ)/w)^2 := by
        rw [hDc1]; have := sq_nonneg ((T:ℝ)/w); linarith only [this]
      have h2 : (0:ℝ) ≤ ((2 + Real.log 4) * C0 + 100) * w * σ := by positivity
      nlinarith only [h1, h2, hDc1]
    linarith only [hLHS, hfin, hRHSge]
  · -- 2 ≤ T
    have hT1 : (1:ℝ) ≤ (T:ℝ) := by exact_mod_cast (by omega : 1 ≤ T)
    have hTpos : (0:ℝ) < (T:ℝ) := by exact_mod_cast (by omega : 0 < T)
    have hρle : ρ ≤ 4 * (T:ℝ) := hρle4T (by omega : 1 ≤ T)
    have hlogT0 : (0:ℝ) ≤ Real.log (ρ/(T:ℝ)) := by
      apply Real.log_nonneg
      rw [le_div_iff₀ hTpos]; linarith only [hTleρ]
    have hlogT1 : Real.log (ρ/(T:ℝ)) ≤ Real.log 4 := by
      refine Real.log_le_log (by positivity) ?_
      rw [div_le_iff₀ hTpos]; linarith only [hρle]
    set S0 : ℝ := ∑ k ∈ Finset.Icc 1 T, (if Nat.Coprime k r then (ArithmeticFunction.moebius k : ℝ)/kap k else 0) with hS0
    set S1 : ℝ := ∑ k ∈ Finset.Icc 1 T, (if Nat.Coprime k r then (ArithmeticFunction.moebius k : ℝ)/kap k * (czLL ρ k - 1) else 0) with hS1
    set R1 : ℝ := ∑ k ∈ Finset.Icc 1 T, (if Nat.Coprime k r then (ArithmeticFunction.moebius k : ℝ)/kap k * (czAA w k * (czLL ρ k - 1)) else 0) with hR1
    set R2 : ℝ := ∑ k ∈ Finset.Icc 1 T, (if Nat.Coprime k r then (ArithmeticFunction.moebius k : ℝ)/kap k * czGG w k else 0) with hR2
    set S2L : ℝ := ∑ k ∈ Finset.Icc 1 T, (if Nat.Coprime k r then (ArithmeticFunction.moebius k : ℝ)/kap k * (2 - czLL ρ k) else 0) with hS2Ldef
    set e1 : ℝ := S1 - (Real.pi^2/6) * (Work.ZeroDensity.Jutila.kap r / (r:ℝ)) - Real.log (ρ/(T:ℝ)) * S0 with he1def
    have hkk : ∀ k ∈ Finset.Icc 1 T, (1:ℝ) ≤ ρ/(k:ℝ) := by
      intro k hk
      rw [Finset.mem_Icc] at hk
      have hkpos : (0:ℝ) < (k:ℝ) := by exact_mod_cast (by omega : 0 < k)
      rw [le_div_iff₀ hkpos]
      have h2 : (k:ℝ) ≤ (T:ℝ) := by exact_mod_cast hk.2
      linarith only [hTleρ, h2]
    have hA0 : ∀ k ∈ Finset.Icc 1 T, (0:ℝ) < (⌊w/(k:ℝ)⌋₊:ℝ) := by
      intro k hk
      rw [Finset.mem_Icc] at hk
      have hkpos : (0:ℝ) < (k:ℝ) := by exact_mod_cast (by omega : 0 < k)
      have hkw : (k:ℝ) ≤ w/2 := le_trans (by exact_mod_cast hk.2) hTw2
      have h1 : 1 ≤ ⌊w/(k:ℝ)⌋₊ := by
        rw [Nat.one_le_floor_iff, le_div_iff₀ hkpos]; linarith only [hkw, hw0, hTw2, hT1]
      exact_mod_cast (by omega : 0 < ⌊w/(k:ℝ)⌋₊)
    have hthk : ∀ k ∈ Finset.Icc 1 T, czTh w k < w/2 := by
      intro k hk
      rw [Finset.mem_Icc] at hk
      have hkpos : (0:ℝ) < (k:ℝ) := by exact_mod_cast (by omega : 0 < k)
      have hkw : (k:ℝ) ≤ w/2 := le_trans (by exact_mod_cast hk.2) hTw2
      exact lt_of_lt_of_le (czTh_lt hkpos) hkw
    have hApos2 : ∀ k ∈ Finset.Icc 1 T, (0:ℝ) < (⌊w/(k:ℝ)⌋₊:ℝ)*(k:ℝ)/w := by
      intro k hk
      rw [Finset.mem_Icc] at hk
      have hkpos : (0:ℝ) < (k:ℝ) := by exact_mod_cast (by omega : 0 < k)
      have h1 : (0:ℝ) < (⌊w/(k:ℝ)⌋₊:ℝ) := by
        have h2 : 1 ≤ ⌊w/(k:ℝ)⌋₊ := by
          rw [Nat.one_le_floor_iff, le_div_iff₀ hkpos]
          have hkw : (k:ℝ) ≤ w/2 := le_trans (by exact_mod_cast hk.2) hTw2
          linarith only [hkw, hw0, hTw2, hT1]
        exact_mod_cast (by omega : 0 < ⌊w/(k:ℝ)⌋₊)
      positivity
    have hcz : czInSum w y N q r
        = w * ∑ k ∈ Finset.Icc 1 T, (if Nat.Coprime k r then (ArithmeticFunction.moebius k : ℝ)/kap k * (czEE w k * czFII w y r k) else 0) := by
      rw [czInSum, ← hTdef, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hA0k := hA0 k hk
      by_cases hc : Nat.Coprime r k
      · rw [if_pos hc, if_pos (Nat.coprime_comm.mpr hc)]
        rw [show czEE w k = (⌊w/(k:ℝ)⌋₊:ℝ)*(k:ℝ)/w from czEE_eq (hApos2 k hk)]
        have hwt : w * ((⌊w/(k:ℝ)⌋₊:ℝ)*(k:ℝ)/w) = (⌊w/(k:ℝ)⌋₊:ℝ)*(k:ℝ) := by
          rw [mul_comm, div_mul_cancel₀ _ hw0.ne']
        calc (ArithmeticFunction.moebius k : ℝ) * (k:ℝ) / kap k * ((⌊w/(k:ℝ)⌋₊:ℝ) * czFII w y r k)
            = (ArithmeticFunction.moebius k : ℝ) / kap k * ((⌊w/(k:ℝ)⌋₊:ℝ)*(k:ℝ) * czFII w y r k) := by ring
          _ = (ArithmeticFunction.moebius k : ℝ) / kap k * (w * ((⌊w/(k:ℝ)⌋₊:ℝ)*(k:ℝ)/w) * czFII w y r k) := by rw [hwt]
          _ = w * ((ArithmeticFunction.moebius k : ℝ) / kap k * ((⌊w/(k:ℝ)⌋₊:ℝ)*(k:ℝ)/w * czFII w y r k)) := by ring
      · rw [if_neg hc, if_neg (fun h => hc (Nat.coprime_comm.mp h)), mul_zero]
        ring
    have hinner : (∑ k ∈ Finset.Icc 1 T, (if Nat.Coprime k r then (ArithmeticFunction.moebius k : ℝ)/kap k * (czEE w k * czFII w y r k) else 0))
        = S2L + R1 + R2 := by
      rw [hS2Ldef, hR1, hR2, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [Finset.mem_Icc] at hk
      have hkpos : (0:ℝ) < (k:ℝ) := by exact_mod_cast (by omega : 0 < k)
      by_cases hc : Nat.Coprime k r
      · simp only [if_pos hc]
        rw [czPointwise w y r k ρ hρdef hw0 hy0 hkpos (hA0 k (by rw [Finset.mem_Icc]; exact hk)) hρpos]
        ring
      · simp only [if_neg hc]
        ring
    have hcz2 : czInSum w y N q r = w * (S2L + R1 + R2) := by rw [hcz, hinner]
    have hS2L' : S2L = -S1 + S0 := by
      rw [hS2Ldef, hS1, hS0, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k hk => ?_
      by_cases hc : Nat.Coprime k r
      · simp only [if_pos hc]; ring
      · simp only [if_neg hc]; ring
    have hS0b : |S0| ≤ C0 * σ * Work.ZeroDensity.Jutila.Dc c0 T := by
      rw [hS0, hσdef]
      exact hK2 r T hsq hT2
    have hS1c : (∑ k ∈ Finset.Icc 1 T, (if Nat.Coprime k r then (ArithmeticFunction.moebius k : ℝ)/kap k else 0) * (Real.log (ρ/(k:ℝ)) - 1)) = S1 := by
      rw [hS1]
      refine Finset.sum_congr rfl fun k hk => ?_
      by_cases hc : Nat.Coprime k r
      · rw [if_pos hc, if_pos hc]; simp only [czLL]
      · rw [if_neg hc, if_neg hc]; ring
    have he1b : |e1| ≤ C0 * σ * Work.ZeroDensity.Jutila.Dc c0 T := by
      have h := hK1 r T ρ hsq hT2 hTleρ
      rw [hS1c, ← hS0, ← hσdef] at h
      rw [he1def]
      exact h
    have hR1b : |R1| ≤ 48 * ((T:ℝ)/w)^2 := by
      rw [hR1]
      have hb : ∀ k ∈ Finset.Icc 1 T,
          |(if Nat.Coprime k r then (ArithmeticFunction.moebius k : ℝ)/kap k * (czAA w k * (czLL ρ k - 1)) else 0)|
            ≤ 12 * ρ / w^2 := by
        intro k hk
        rw [Finset.mem_Icc] at hk
        have hk1 : 1 ≤ k := hk.1
        have hkpos : (0:ℝ) < (k:ℝ) := by exact_mod_cast (by omega : 0 < k)
        by_cases hc : Nat.Coprime k r
        · rw [if_pos hc]
          have h1 : |(ArithmeticFunction.moebius k : ℝ)| / kap k ≤ 1/(k:ℝ) := czMuKapWeightLe k hk1
          have h2 : |czAA w k| ≤ 3 * (czU w k)^2 := by
            rw [czAA, czEE]
            exact (czExpDeviation (czU w k) (czU_abs_le_one hw0 hkpos (hthk k (by rw [Finset.mem_Icc]; exact hk)))).1
          have h3 : |czLL ρ k - 1| ≤ ρ/(k:ℝ) := czLL_abs_sub_one_le (hkk k (by rw [Finset.mem_Icc]; exact hk))
          have h4 : (czU w k)^2 ≤ 4 * (k:ℝ)^2 / w^2 := by
            refine le_trans (czU_sq_le hw0 hkpos (hthk k (by rw [Finset.mem_Icc]; exact hk))) ?_
            have hw2 : (0:ℝ) < w^2 := by positivity
            apply div_le_div_of_nonneg_right _ hw2.le
            linarith only [czTh_sq_le hw0.le hkpos, hw0, hkpos]
          have hnn1 : (0:ℝ) ≤ 1/(k:ℝ) := by positivity
          have hnn2 : (0:ℝ) ≤ ρ/(k:ℝ) := by positivity
          calc |(ArithmeticFunction.moebius k : ℝ)/kap k * (czAA w k * (czLL ρ k - 1))|
              = |(ArithmeticFunction.moebius k : ℝ)|/kap k * (|czAA w k| * |czLL ρ k - 1|) := by
                rw [abs_mul, abs_mul, abs_div,
                  abs_of_nonneg (Work.ZeroDensity.Jutila.kap_pos k).le]
            _ ≤ (1/(k:ℝ)) * ((3 * (czU w k)^2) * (ρ/(k:ℝ))) := by
                apply mul_le_mul h1 (mul_le_mul h2 h3 (abs_nonneg _) (by positivity)) (by positivity) hnn1
            _ ≤ (1/(k:ℝ)) * ((3 * (4*(k:ℝ)^2/w^2)) * (ρ/(k:ℝ))) := by
                apply mul_le_mul_of_nonneg_left _ hnn1
                exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h4 (by norm_num)) hnn2
            _ = 12 * ρ / w^2 := by field_simp <;> ring
        · rw [if_neg hc, abs_zero]; positivity
      calc |∑ k ∈ Finset.Icc 1 T, (if Nat.Coprime k r then (ArithmeticFunction.moebius k : ℝ)/kap k * (czAA w k * (czLL ρ k - 1)) else 0)|
          ≤ ∑ k ∈ Finset.Icc 1 T, |(if Nat.Coprime k r then (ArithmeticFunction.moebius k : ℝ)/kap k * (czAA w k * (czLL ρ k - 1)) else 0)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ k ∈ Finset.Icc 1 T, (12 * ρ / w^2) := Finset.sum_le_sum hb
        _ = (T:ℝ) * (12 * ρ / w^2) := by rw [Finset.sum_const]; simp [nsmul_eq_mul]
        _ = 12 * ρ * (T:ℝ) / w^2 := by ring
        _ ≤ 48 * ((T:ℝ)/w)^2 := by
            have h2 : (0:ℝ) ≤ (T:ℝ) := by positivity
            have h3a : ρ * (T:ℝ) ≤ (4*(T:ℝ)) * (T:ℝ) := mul_le_mul_of_nonneg_right hρle h2
            have h3b : 12 * (ρ * (T:ℝ)) ≤ 12 * ((4*(T:ℝ)) * (T:ℝ)) :=
              mul_le_mul_of_nonneg_left h3a (by norm_num)
            have hw2 : (0:ℝ) < w^2 := by positivity
            have h4 : 12 * ρ * (T:ℝ) / w^2 ≤ 12 * (4*(T:ℝ)) * (T:ℝ) / w^2 :=
              div_le_div_of_nonneg_right (by linarith only [h3b, h3a]) hw2.le
            have h5 : 12 * (4*(T:ℝ)) * (T:ℝ) / w^2 = 48 * ((T:ℝ)/w)^2 := by ring
            linarith only [h4, le_of_eq h5, h5]
    have hR2b : |R2| ≤ 16 * ((T:ℝ)/w)^2 := by
      rw [hR2]
      have hb : ∀ k ∈ Finset.Icc 1 T,
          |(if Nat.Coprime k r then (ArithmeticFunction.moebius k : ℝ)/kap k * czGG w k else 0)|
            ≤ 16 * (T:ℝ) / w^2 := by
        intro k hk
        rw [Finset.mem_Icc] at hk
        have hk1 : 1 ≤ k := hk.1
        have hkT : (k:ℝ) ≤ (T:ℝ) := by exact_mod_cast hk.2
        have hkpos : (0:ℝ) < (k:ℝ) := by exact_mod_cast (by omega : 0 < k)
        by_cases hc : Nat.Coprime k r
        · rw [if_pos hc, abs_mul]
          have h1 : |(ArithmeticFunction.moebius k : ℝ)| / kap k ≤ 1/(k:ℝ) := czMuKapWeightLe k hk1
          have h2 : |czGG w k| ≤ 4 * (czU w k)^2 := by
            rw [czGG, czEE]
            exact (czExpDeviation (czU w k) (czU_abs_le_one hw0 hkpos (hthk k (by rw [Finset.mem_Icc]; exact hk)))).2
          have h4 : (czU w k)^2 ≤ 4 * (k:ℝ)^2 / w^2 := by
            refine le_trans (czU_sq_le hw0 hkpos (hthk k (by rw [Finset.mem_Icc]; exact hk))) ?_
            have hw2 : (0:ℝ) < w^2 := by positivity
            apply div_le_div_of_nonneg_right _ hw2.le
            linarith only [czTh_sq_le hw0.le hkpos, hw0, hkpos]
          calc |(ArithmeticFunction.moebius k : ℝ)/kap k| * |czGG w k|
              = |(ArithmeticFunction.moebius k : ℝ)|/kap k * |czGG w k| := by
                rw [abs_div, abs_of_nonneg (Work.ZeroDensity.Jutila.kap_pos k).le]
            _ ≤ (1/(k:ℝ)) * (4 * (czU w k)^2) := mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
            _ ≤ (1/(k:ℝ)) * (4 * (4*(k:ℝ)^2/w^2)) := by
                apply mul_le_mul_of_nonneg_left _ (by positivity)
                exact mul_le_mul_of_nonneg_left h4 (by norm_num)
            _ = 16 * (k:ℝ) / w^2 := by field_simp <;> ring
            _ ≤ 16 * (T:ℝ) / w^2 := by
                have hw2 : (0:ℝ) < w^2 := by positivity
                apply div_le_div_of_nonneg_right _ hw2.le
                linarith only [hkT]
        · rw [if_neg hc, abs_zero]; positivity
      calc |∑ k ∈ Finset.Icc 1 T, (if Nat.Coprime k r then (ArithmeticFunction.moebius k : ℝ)/kap k * czGG w k else 0)|
          ≤ ∑ k ∈ Finset.Icc 1 T, |(if Nat.Coprime k r then (ArithmeticFunction.moebius k : ℝ)/kap k * czGG w k else 0)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ k ∈ Finset.Icc 1 T, (16 * (T:ℝ) / w^2) := Finset.sum_le_sum hb
        _ = (T:ℝ) * (16 * (T:ℝ) / w^2) := by rw [Finset.sum_const]; simp [nsmul_eq_mul]
        _ = 16 * ((T:ℝ)/w)^2 := by ring
    have hfinal : czInSum w y N q r + w*(Real.pi^2/6)*(Work.ZeroDensity.Jutila.kap r / (r:ℝ))
        = w * (S0 * (1 - Real.log (ρ/(T:ℝ))) - e1 + R1 + R2) := by
      rw [hcz2, hS2L', he1def]
      ring
    have h4b : |1 - Real.log (ρ/(T:ℝ))| ≤ 1 + Real.log 4 := by
      rw [abs_le]
      exact ⟨by linarith only [hlogT0, hlogT1], by linarith only [hlogT1, hlogT0]⟩
    have habs : |S0 * (1 - Real.log (ρ/(T:ℝ)))| ≤ |S0| * (1 + Real.log 4) := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left h4b (abs_nonneg _)
    have htri : |S0 * (1 - Real.log (ρ/(T:ℝ))) - e1 + R1 + R2|
        ≤ |S0| * (1 + Real.log 4) + |e1| + |R1| + |R2| := by
      have ha : |S0 * (1 - Real.log (ρ/(T:ℝ))) - e1| ≤ |S0 * (1 - Real.log (ρ/(T:ℝ)))| + |e1| := by
        rw [sub_eq_add_neg]
        calc |S0 * (1 - Real.log (ρ/(T:ℝ))) + -e1| 
            ≤ |S0 * (1 - Real.log (ρ/(T:ℝ)))| + |-e1| := abs_add_le _ _
          _ = |S0 * (1 - Real.log (ρ/(T:ℝ)))| + |e1| := by rw [abs_neg]
      have hb1 : |R1 + R2| ≤ |R1| + |R2| := abs_add_le _ _
      calc |S0 * (1 - Real.log (ρ/(T:ℝ))) - e1 + R1 + R2|
          = |(S0 * (1 - Real.log (ρ/(T:ℝ))) - e1) + (R1 + R2)| := by ring_nf
        _ ≤ |S0 * (1 - Real.log (ρ/(T:ℝ))) - e1| + |R1 + R2| := abs_add_le _ _
        _ ≤ (|S0| * (1 + Real.log 4) + |e1|) + (|R1| + |R2|) := by linarith only [ha, hb1, habs]
        _ = |S0| * (1 + Real.log 4) + |e1| + |R1| + |R2| := by ring
    have hmain : |S0 * (1 - Real.log (ρ/(T:ℝ))) - e1 + R1 + R2|
        ≤ C0 * σ * (2 + Real.log 4) * Work.ZeroDensity.Jutila.Dc c0 T + 64 * ((T:ℝ)/w)^2 := by
      have hlog4p : (0:ℝ) ≤ 1 + Real.log 4 := by
        have := Real.log_pos (by norm_num : (1:ℝ) < 4); linarith only [this]
      have hA : |S0| * (1 + Real.log 4) ≤ C0 * σ * Work.ZeroDensity.Jutila.Dc c0 T * (1 + Real.log 4) :=
        mul_le_mul_of_nonneg_right hS0b hlog4p
      have hB : |S0| * (1 + Real.log 4) + |e1| + |R1| + |R2|
          ≤ C0 * σ * Work.ZeroDensity.Jutila.Dc c0 T * (1 + Real.log 4)
            + C0 * σ * Work.ZeroDensity.Jutila.Dc c0 T + 48 * ((T:ℝ)/w)^2 + 16 * ((T:ℝ)/w)^2 := by
        linarith only [hA, he1b, hR1b, hR2b]
      have hC' : C0 * σ * Work.ZeroDensity.Jutila.Dc c0 T * (1 + Real.log 4)
            + C0 * σ * Work.ZeroDensity.Jutila.Dc c0 T + 48 * ((T:ℝ)/w)^2 + 16 * ((T:ℝ)/w)^2
          = C0 * σ * (2 + Real.log 4) * Work.ZeroDensity.Jutila.Dc c0 T + 64 * ((T:ℝ)/w)^2 := by ring
      linarith only [htri, hB, le_of_eq hC', he1b, hR1b, hR2b, hA]
    have hbound : |czInSum w y N q r + w*(Real.pi^2/6)*(Work.ZeroDensity.Jutila.kap r / (r:ℝ))|
        ≤ w * (C0 * σ * (2 + Real.log 4) * Work.ZeroDensity.Jutila.Dc c0 T + 64 * ((T:ℝ)/w)^2) := by
      rw [hfinal, abs_mul, abs_of_nonneg hw0.le]
      exact mul_le_mul_of_nonneg_left hmain hw0.le
    exact le_trans hbound (czFinalStep hC0 rfl hσ1 hw0 (Work.ZeroDensity.Jutila.Dc_pos c0 T).le (sq_nonneg _))

end Work.ZeroDensity.Jutila.BzCross
