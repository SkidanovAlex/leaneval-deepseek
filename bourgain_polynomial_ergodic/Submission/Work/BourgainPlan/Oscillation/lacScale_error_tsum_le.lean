import Mathlib
import Submission.Work.BourgainPlan.Oscillation.lacunary_defs

namespace Work.BourgainPlan.Oscillation

open Finset MeasureTheory
open scoped BigOperators ENNReal

/-!
# Summability and uniform boundedness of the lacunary profile-replacement error

For `ρ > 1`, `d ≥ 1`, the quantity

  `min( (|β| ⌊ρ^i⌋^d)^2 , (|β| ⌊ρ^i⌋^d)^{-2/d} )`

is the "profile-replacement error" at the lacunary scale `⌊ρ^i⌋`: it is the size of the gap between
the smooth profile `Φ` and the sharp window `|β N^d| ≤ 1` at the frequency offset `β`, and it enters
the oscillation argument with total weight `ℓ²`.

The content of this file is that this error is **summable in `i` with a bound uniform in `β ≠ 0`**.
Both regimes are uniformly controlled:

* on the *initial segment* `|β| ⌊ρ^i⌋^d ≤ 1` the terms are `(|β| ⌊ρ^i⌋^d)^2 ≤ |β| ⌊ρ^i⌋^d`, and
  `Σ_i ⌊ρ^i⌋^d ≤ C ρ^{i₀ d} ≤ C /|β|` because `ρ^i/2 ≤ ⌊ρ^i⌋`;
* on the *tail* `|β| ⌊ρ^i⌋^d > 1` the terms are `|β|^{-2/d} ⌊ρ^i⌋^{-2} ≤ 4 |β|^{-2/d} ρ^{-2i}`, a
  geometric series whose head `|β|^{-2/d} ρ^{-2 m}` (`m` the first index of the tail) is `≤ 1`
  since `⌊ρ^m⌋ ≤ ρ^m` and `|β| ⌊ρ^m⌋^d > 1` forces `|β| > ρ^{-md}`.
-/

noncomputable section

/-! ## Elementary estimates on the lacunary scale `⌊ρ^i⌋` -/

lemma one_le_lacScale (ρ : ℝ) (hρ : 1 ≤ ρ) (i : ℕ) : 1 ≤ lacScale ρ i := by
  rw [lacScale]; exact (Nat.one_le_floor_iff (ρ^i)).mpr (one_le_pow₀ hρ)

lemma lacScale_mono (ρ : ℝ) (hρ : 1 ≤ ρ) : Monotone (lacScale ρ) := by
  intro i j hij
  rw [lacScale]
  exact Nat.floor_mono (pow_le_pow_right₀ hρ hij)

lemma lacScale_le_pow (ρ : ℝ) (hρ : 0 ≤ ρ) (i : ℕ) : (lacScale ρ i : ℝ) ≤ ρ ^ i := by
  rw [lacScale]; exact Nat.floor_le (pow_nonneg hρ i)

lemma lacScale_ge_half (ρ : ℝ) (hρ : 1 < ρ) (i : ℕ) : ρ^i / 2 ≤ (lacScale ρ i : ℝ) := by
  rw [lacScale]
  rcases lt_or_ge (ρ^i) 2 with h2 | h2
  · have hx1 : (1:ℝ) ≤ ρ^i := one_le_pow₀ (le_of_lt hρ)
    have h3 : (1:ℝ) ≤ ((⌊ρ^i⌋₊ : ℕ) : ℝ) := by
      have h := (Nat.one_le_floor_iff (ρ^i)).mpr hx1; exact_mod_cast h
    linarith
  · have h4 : ρ^i - 1 < ((⌊ρ^i⌋₊ : ℕ) : ℝ) := by
      have := Nat.lt_floor_add_one (ρ^i); linarith
    linarith

/-! ## Geometric finite sums -/

lemma geom_range_le (r : ℝ) (hr : 1 < r) (n : ℕ) :
    ∑ i ∈ Finset.range n, r ^ i ≤ r ^ n / (r - 1) := by
  rw [geom_sum_eq (ne_of_gt hr) n]
  have hpos : 0 < r - 1 := by linarith
  have hle : r ^ n - 1 ≤ r ^ n := by
    have : (0:ℝ) < r^n := pow_pos (by linarith) n; linarith
  exact div_le_div_of_nonneg_right hle (le_of_lt hpos)

lemma sum_range_geom_le (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (n : ℕ) :
    ∑ i ∈ Finset.range n, r ^ i ≤ (1 - r)⁻¹ := by
  have h := Summable.sum_le_tsum (Finset.range n) (fun i _ => pow_nonneg hr0 i)
    (summable_geometric_of_lt_one hr0 hr1)
  rwa [tsum_geometric_of_lt_one hr0 hr1] at h

lemma sum_Ico_geom_le (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (m n : ℕ) :
    ∑ k ∈ Finset.Ico m n, r ^ k ≤ r ^ m * (1 - r)⁻¹ := by
  calc ∑ k ∈ Finset.Ico m n, r ^ k
      = ∑ k ∈ Finset.range (n - m), r ^ (m + k) := Finset.sum_Ico_eq_sum_range _ _ _
    _ = ∑ k ∈ Finset.range (n - m), r ^ m * r ^ k := by
        apply Finset.sum_congr rfl; intro k hk; rw [pow_add]
    _ = r ^ m * (∑ k ∈ Finset.range (n - m), r ^ k) := by rw [Finset.mul_sum]
    _ ≤ r ^ m * (1 - r)⁻¹ := by
        apply mul_le_mul_of_nonneg_left (sum_range_geom_le r hr0 hr1 (n - m))
        exact pow_nonneg hr0 m

/-! ## The initial-segment (`|β| ⌊ρ^i⌋^d ≤ 1`) contribution -/

lemma regionA_le (ρ : ℝ) (hρ : 1 < ρ) (d : ℕ) (hd : 1 ≤ d) (β : ℝ) (hβ : β ≠ 0)
    (s : Finset ℕ) :
    ∑ i ∈ s.filter (fun i => |β| * (lacScale ρ i : ℝ)^d ≤ 1),
        (|β| * (lacScale ρ i : ℝ)^d)^2 ≤ 2^d * ρ^d / (ρ^d - 1) := by
  have ha : 0 < |β| := abs_pos.mpr hβ
  have hρ0 : 0 < ρ := lt_trans zero_lt_one hρ
  have hρd1 : 1 < ρ^d := one_lt_pow₀ hρ (by omega)
  have hρd0 : 0 < ρ^d - 1 := by linarith
  set sA := s.filter (fun i => |β| * (lacScale ρ i : ℝ)^d ≤ 1) with hsA
  by_cases hne : sA.Nonempty
  · set M := sA.max' hne with hM
    have hMax : ∀ i ∈ sA, i ≤ M := fun i hi => Finset.le_max' sA i hi
    have hMmem : M ∈ sA := Finset.max'_mem _ hne
    have hPM : |β| * (lacScale ρ M : ℝ)^d ≤ 1 := (Finset.mem_filter.mp hMmem).2
    have hNMd : (lacScale ρ M : ℝ)^d ≤ 1/|β| := by rw [le_div_iff₀ ha]; linarith
    have hpow : (ρ^d)^M ≤ 2^d * (lacScale ρ M : ℝ)^d := by
      have h : (ρ^M)^d ≤ (2 * (lacScale ρ M : ℝ))^d :=
        pow_le_pow_left₀ (by positivity) (by linarith [lacScale_ge_half ρ hρ M]) d
      have hid : (ρ^M)^d = (ρ^d)^M := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
      rw [hid, mul_pow] at h; exact h
    calc ∑ i ∈ sA, (|β| * (lacScale ρ i : ℝ)^d)^2
        ≤ ∑ i ∈ sA, |β| * (lacScale ρ i : ℝ)^d := by
          apply Finset.sum_le_sum; intro i hi
          have hPi : |β| * (lacScale ρ i : ℝ)^d ≤ 1 := (Finset.mem_filter.mp hi).2
          have h0 : 0 ≤ |β| * (lacScale ρ i : ℝ)^d := by positivity
          have h := mul_le_mul_of_nonneg_left hPi h0
          simpa [pow_two] using h
      _ = |β| * ∑ i ∈ sA, (lacScale ρ i : ℝ)^d := by rw [Finset.mul_sum]
      _ ≤ |β| * ∑ i ∈ Finset.range (M+1), (ρ^d)^i := by
          apply mul_le_mul_of_nonneg_left _ (le_of_lt ha)
          apply le_trans (Finset.sum_le_sum (fun i hi => ?_))
            (Finset.sum_le_sum_of_subset_of_nonneg (fun i hi => ?_) (fun i hi _ => by positivity))
          · have := pow_le_pow_left₀ (by positivity) (lacScale_le_pow ρ (le_of_lt hρ0) i) d
            have hid : (ρ^i)^d = (ρ^d)^i := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
            rwa [hid] at this
          · exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hMax i hi))
      _ ≤ |β| * ((ρ^d)^M * ρ^d / (ρ^d - 1)) := by
          apply mul_le_mul_of_nonneg_left _ (le_of_lt ha)
          have hg := geom_range_le (ρ^d) hρd1 (M+1)
          rw [pow_succ] at hg; exact hg
      _ ≤ 2^d * ρ^d / (ρ^d - 1) := by
          have hnum : (ρ^d)^M * ρ^d ≤ (2^d * (1/|β|)) * ρ^d := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            calc (ρ^d)^M ≤ 2^d * (lacScale ρ M : ℝ)^d := hpow
              _ ≤ 2^d * (1/|β|) := mul_le_mul_of_nonneg_left hNMd (by positivity)
          have hdiv := div_le_div_of_nonneg_right hnum (le_of_lt hρd0)
          have hfinal : |β| * ((2^d * (1/|β|)) * ρ^d / (ρ^d -1)) = 2^d * ρ^d/(ρ^d -1) := by
            field_simp
          calc |β| * ((ρ^d)^M * ρ^d/(ρ^d-1))
              ≤ |β| * ((2^d * (1/|β|)) * ρ^d/(ρ^d-1)) := mul_le_mul_of_nonneg_left hdiv (le_of_lt ha)
            _ = 2^d * ρ^d/(ρ^d -1) := hfinal
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simp only [Finset.sum_empty]; positivity

/-! ## The tail (`|β| ⌊ρ^i⌋^d > 1`) contribution -/

/-- Pointwise control of the tail summand: for every index `i`,
`((|β| ⌊ρ^i⌋^d)^{-1/d})² ≤ 4 |β|^{-2/d} (ρ^{-2})^i`. -/
lemma term_bound (ρ : ℝ) (hρ : 1 < ρ) (d : ℕ) (hd : 1 ≤ d) (β : ℝ) (hβ : β ≠ 0) (i : ℕ) :
    ((|β| * (lacScale ρ i : ℝ)^d) ^ (-((1:ℝ)/(d:ℝ))))^2
      ≤ 4 * |β| ^ (-(2/(d:ℝ))) * ((ρ^2)⁻¹)^i := by
  have ha : 0 < |β| := abs_pos.mpr hβ
  have hd0 : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd
  have hρ0 : 0 < ρ := lt_trans zero_lt_one hρ
  have hNi : (0:ℝ) < (lacScale ρ i : ℝ) := by
    exact_mod_cast one_le_lacScale ρ (le_of_lt hρ) i
  have hNd : (0:ℝ) < (lacScale ρ i : ℝ)^d := pow_pos hNi d
  rw [Real.mul_rpow (le_of_lt ha) (le_of_lt hNd)]
  have hstep : ((lacScale ρ i : ℝ)^d) ^ (-(1/(d:ℝ))) = (lacScale ρ i : ℝ)^(-1:ℝ) := by
    rw [← Real.rpow_natCast (lacScale ρ i : ℝ) d, ← Real.rpow_mul (le_of_lt hNi)]
    congr 1
    field_simp
  rw [hstep, mul_pow]
  have hn : ((lacScale ρ i : ℝ)^(-1:ℝ))^2 = (lacScale ρ i : ℝ)^(-2:ℝ) := by
    rw [← Real.rpow_natCast ((lacScale ρ i : ℝ)^(-1:ℝ)) 2, ← Real.rpow_mul (le_of_lt hNi)]
    congr 1; norm_num
  have hb : (|β| ^ (-(1/(d:ℝ))))^2 = |β| ^ (-(2/(d:ℝ))) := by
    rw [← Real.rpow_natCast (|β| ^ (-(1/(d:ℝ)))) 2, ← Real.rpow_mul (le_of_lt ha)]
    congr 1; field_simp; ring
  rw [hn, hb]
  have hkey : 1 ≤ (lacScale ρ i : ℝ)^2 * (4 * ((ρ^2)⁻¹)^i) := by
    have hge := lacScale_ge_half ρ hρ i
    have hNi2 : (ρ^i/2)^2 ≤ (lacScale ρ i : ℝ)^2 := pow_le_pow_left₀ (by positivity) hge 2
    have hfour : (ρ^i/2)^2 * (4 * ((ρ^2)⁻¹)^i) = 1 := by
      have hpi2 : (ρ^i)^2 = (ρ^2)^i := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
      have hsq : (ρ^i/2)^2 = (ρ^2)^i / 4 := by rw [div_pow, hpi2]; norm_num
      have hcomb : (ρ^2)^i / 4 * (4 * ((ρ^2)⁻¹)^i) = (ρ^2)^i * ((ρ^2)⁻¹)^i := by ring
      rw [hsq, hcomb, ← mul_pow, mul_inv_cancel₀ (by positivity : ρ^2 ≠ 0), one_pow]
    calc (1:ℝ) = (ρ^i/2)^2 * (4 * ((ρ^2)⁻¹)^i) := hfour.symm
      _ ≤ (lacScale ρ i : ℝ)^2 * (4 * ((ρ^2)⁻¹)^i) :=
          mul_le_mul_of_nonneg_right hNi2 (by positivity)
  have hB : (lacScale ρ i : ℝ)^(-2:ℝ) ≤ 4 * ((ρ^2)⁻¹)^i := by
    have hsq : (lacScale ρ i : ℝ)^(-2:ℝ) = ((lacScale ρ i : ℝ)^2)⁻¹ := by
      rw [Real.rpow_neg hNi.le]; norm_num
    rw [hsq, inv_le_iff_one_le_mul₀ (by positivity : (0:ℝ) < (lacScale ρ i : ℝ)^2)]
    rw [mul_comm]; exact hkey
  calc |β| ^ (-(2/(d:ℝ))) * (lacScale ρ i : ℝ)^(-2:ℝ)
      ≤ |β| ^ (-(2/(d:ℝ))) * (4 * ((ρ^2)⁻¹)^i) :=
        mul_le_mul_of_nonneg_left hB (Real.rpow_nonneg (le_of_lt ha) _)
    _ = 4 * |β| ^ (-(2/(d:ℝ))) * ((ρ^2)⁻¹)^i := by ring

lemma regionB_le (ρ : ℝ) (hρ : 1 < ρ) (d : ℕ) (hd : 1 ≤ d) (β : ℝ) (hβ : β ≠ 0)
    (s : Finset ℕ) :
    ∑ i ∈ s.filter (fun i => ¬ (|β| * (lacScale ρ i : ℝ)^d ≤ 1)),
        ((|β| * (lacScale ρ i : ℝ)^d) ^ (-((1:ℝ)/(d:ℝ))))^2 ≤ 4/(1 - (ρ^2)⁻¹) := by
  have ha : 0 < |β| := abs_pos.mpr hβ
  have hρ0 : 0 < ρ := lt_trans zero_lt_one hρ
  have hr0 : 0 ≤ (ρ^2)⁻¹ := by positivity
  have hr1 : (ρ^2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (one_lt_pow₀ hρ (by norm_num))
  have h1mr : 0 < 1 - (ρ^2)⁻¹ := by linarith
  set sB := s.filter (fun i => ¬ (|β| * (lacScale ρ i : ℝ)^d ≤ 1)) with hsB
  by_cases hne : sB.Nonempty
  · set m := sB.min' hne with hm
    have hmmem : m ∈ sB := Finset.min'_mem _ hne
    have hmle : ∀ i ∈ sB, m ≤ i := fun i hi => Finset.min'_le sB i hi
    have ht : 1 < |β| * (lacScale ρ m : ℝ)^d :=
      lt_of_not_ge (Finset.mem_filter.mp hmmem).2
    have hcross : |β| ^ (-(2/(d:ℝ))) * ((ρ^2)⁻¹)^m ≤ 1 := by
      have hd0 : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd
      have hNm : (lacScale ρ m : ℝ) ≤ ρ^m := lacScale_le_pow ρ (le_of_lt hρ0) m
      have hNmpos : (0:ℝ) < (lacScale ρ m : ℝ) := by
        exact_mod_cast one_le_lacScale ρ (le_of_lt hρ) m
      have hbig : 1 < |β| * (ρ^m)^d := by
        have hpow : (lacScale ρ m : ℝ)^d ≤ (ρ^m)^d :=
          pow_le_pow_left₀ (le_of_lt hNmpos) hNm d
        nlinarith [ht, hpow, le_of_lt ha]
      have h2d : (0:ℝ) < 2/(d:ℝ) := by positivity
      have hraise : 1 < (|β| * (ρ^m)^d) ^ (2/(d:ℝ)) := by
        calc (1:ℝ) = 1 ^ (2/(d:ℝ)) := by rw [Real.one_rpow]
          _ < (|β| * (ρ^m)^d) ^ (2/(d:ℝ)) := Real.rpow_lt_rpow (by norm_num) hbig h2d
      have heq : (|β| * (ρ^m)^d) ^ (2/(d:ℝ))
          = |β| ^ (2/(d:ℝ)) * (((ρ^2)⁻¹)^m)⁻¹ := by
        rw [Real.mul_rpow (le_of_lt ha) (by positivity)]
        congr 1
        rw [← Real.rpow_natCast (ρ^m) d, ← Real.rpow_mul (by positivity : (0:ℝ) ≤ ρ^m)]
        have hexp : (d:ℝ) * (2/(d:ℝ)) = 2 := by field_simp
        rw [hexp]
        rw [show (ρ^m) ^ (2:ℝ) = (ρ^m)^2 from Real.rpow_natCast (ρ^m) 2]
        have h1 : (ρ^m)^2 = (ρ^2)^m := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
        have h2 : (((ρ^2)⁻¹)^m)⁻¹ = (ρ^2)^m := by rw [inv_pow, inv_inv]
        rw [h1, ← h2]
      rw [show |β| ^ (-(2/(d:ℝ))) = (|β| ^ (2/(d:ℝ)))⁻¹ by rw [Real.rpow_neg ha.le]]
      rw [show (|β| ^ (2/(d:ℝ)))⁻¹ * ((ρ^2)⁻¹)^m
              = (|β| ^ (2/(d:ℝ)) * (((ρ^2)⁻¹)^m)⁻¹)⁻¹ by rw [mul_inv, inv_inv]]
      rw [← heq]
      exact le_of_lt (inv_lt_one_of_one_lt₀ hraise)
    have hM : sB ⊆ Finset.Ico m (sB.max' hne + 1) := fun i hi =>
      Finset.mem_Ico.mpr ⟨hmle i hi, Nat.lt_succ_of_le (Finset.le_max' sB i hi)⟩
    have hgeom : ∑ i ∈ sB, ((ρ^2)⁻¹)^i ≤ ((ρ^2)⁻¹)^m * (1 - (ρ^2)⁻¹)⁻¹ := by
      calc ∑ i ∈ sB, ((ρ^2)⁻¹)^i
          ≤ ∑ i ∈ Finset.Ico m (sB.max' hne + 1), ((ρ^2)⁻¹)^i :=
            Finset.sum_le_sum_of_subset_of_nonneg hM (fun i _ _ => pow_nonneg hr0 i)
        _ ≤ ((ρ^2)⁻¹)^m * (1 - (ρ^2)⁻¹)⁻¹ := sum_Ico_geom_le _ hr0 hr1 m _
    calc ∑ i ∈ sB, ((|β| * (lacScale ρ i : ℝ)^d) ^ (-((1:ℝ)/(d:ℝ))))^2
        ≤ ∑ i ∈ sB, 4 * |β| ^ (-(2/(d:ℝ))) * ((ρ^2)⁻¹)^i :=
          Finset.sum_le_sum (fun i _ => term_bound ρ hρ d hd β hβ i)
      _ = 4 * |β| ^ (-(2/(d:ℝ))) * ∑ i ∈ sB, ((ρ^2)⁻¹)^i := by rw [Finset.mul_sum]
      _ ≤ 4 * |β| ^ (-(2/(d:ℝ))) * (((ρ^2)⁻¹)^m * (1 - (ρ^2)⁻¹)⁻¹) :=
          mul_le_mul_of_nonneg_left hgeom (by positivity)
      _ = (|β| ^ (-(2/(d:ℝ))) * ((ρ^2)⁻¹)^m) * (4 * (1 - (ρ^2)⁻¹)⁻¹) := by ring
      _ ≤ 1 * (4 * (1 - (ρ^2)⁻¹)⁻¹) := by
          apply mul_le_mul_of_nonneg_right hcross (by positivity)
      _ = 4/(1 - (ρ^2)⁻¹) := by rw [one_mul, div_eq_mul_inv]
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simp only [Finset.sum_empty]
    exact div_nonneg (by norm_num) (le_of_lt h1mr)

/-! ## The main statement -/

theorem lacScale_error_tsum_le (ρ : ℝ) (hρ : 1 < ρ) (d : ℕ) (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ β : ℝ, β ≠ 0 →
      Summable (fun i : ℕ => if |β| * (Work.BourgainPlan.Oscillation.lacScale ρ i : ℝ) ^ d ≤ 1
          then (|β| * (Work.BourgainPlan.Oscillation.lacScale ρ i : ℝ) ^ d) ^ 2
          else ((|β| * (Work.BourgainPlan.Oscillation.lacScale ρ i : ℝ) ^ d) ^ (-((1 : ℝ) / (d : ℝ)))) ^ 2)
      ∧ (∑' i : ℕ, if |β| * (Work.BourgainPlan.Oscillation.lacScale ρ i : ℝ) ^ d ≤ 1
          then (|β| * (Work.BourgainPlan.Oscillation.lacScale ρ i : ℝ) ^ d) ^ 2
          else ((|β| * (Work.BourgainPlan.Oscillation.lacScale ρ i : ℝ) ^ d) ^ (-((1 : ℝ) / (d : ℝ)))) ^ 2) ≤ C := by
  have hρ0 : 0 < ρ := lt_trans zero_lt_one hρ
  have hρd1 : 1 < ρ^d := one_lt_pow₀ hρ (by omega)
  have hr1 : (ρ^2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (one_lt_pow₀ hρ (by norm_num))
  refine ⟨2^d * ρ^d / (ρ^d - 1) + 4/(1 - (ρ^2)⁻¹), ?_, ?_⟩
  · have h1 : 0 < 2^d * ρ^d / (ρ^d - 1) :=
      div_pos (by positivity) (by linarith)
    have h2 : 0 < 4/(1 - (ρ^2)⁻¹) := div_pos (by norm_num) (by linarith)
    linarith
  · intro β hβ
    have key : ∀ s : Finset ℕ,
        ∑ i ∈ s, (if |β| * (lacScale ρ i : ℝ)^d ≤ 1
            then (|β| * (lacScale ρ i : ℝ)^d)^2
            else ((|β| * (lacScale ρ i : ℝ)^d) ^ (-((1:ℝ)/(d:ℝ))))^2)
          ≤ 2^d * ρ^d / (ρ^d - 1) + 4/(1 - (ρ^2)⁻¹) := by
      intro s
      rw [← Finset.sum_filter_add_sum_filter_not s
            (fun i => |β| * (lacScale ρ i : ℝ)^d ≤ 1)]
      have hA : ∑ i ∈ s.filter (fun i => |β| * (lacScale ρ i : ℝ)^d ≤ 1),
            (if |β| * (lacScale ρ i : ℝ)^d ≤ 1
              then (|β| * (lacScale ρ i : ℝ)^d)^2
              else ((|β| * (lacScale ρ i : ℝ)^d) ^ (-((1:ℝ)/(d:ℝ))))^2)
          ≤ 2^d * ρ^d / (ρ^d - 1) := by
        rw [Finset.sum_congr rfl (fun i hi => by
          rw [if_pos (Finset.mem_filter.mp hi).2])]
        exact regionA_le ρ hρ d hd β hβ s
      have hB : ∑ i ∈ s.filter (fun i => ¬ (|β| * (lacScale ρ i : ℝ)^d ≤ 1)),
            (if |β| * (lacScale ρ i : ℝ)^d ≤ 1
              then (|β| * (lacScale ρ i : ℝ)^d)^2
              else ((|β| * (lacScale ρ i : ℝ)^d) ^ (-((1:ℝ)/(d:ℝ))))^2)
          ≤ 4/(1 - (ρ^2)⁻¹) := by
        rw [Finset.sum_congr rfl (fun i hi => by
          rw [if_neg (Finset.mem_filter.mp hi).2])]
        exact regionB_le ρ hρ d hd β hβ s
      linarith [hA, hB]
    have hnn : 0 ≤ (fun i : ℕ => if |β| * (lacScale ρ i : ℝ)^d ≤ 1
            then (|β| * (lacScale ρ i : ℝ)^d)^2
            else ((|β| * (lacScale ρ i : ℝ)^d) ^ (-((1:ℝ)/(d:ℝ))))^2) := by
      intro i
      dsimp only
      split_ifs with h
      · exact sq_nonneg _
      · exact sq_nonneg _
    exact ⟨summable_of_sum_le hnn key, Real.tsum_le_of_sum_le hnn key⟩

end

end Work.BourgainPlan.Oscillation
