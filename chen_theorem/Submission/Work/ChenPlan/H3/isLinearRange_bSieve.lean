import Mathlib
import Submission.Work.ChenPlan.H3.Defs
import Submission.Work.ChenPlan.H3.isLinear_bSieve
import Submission.Work.NumberTheory.Chen.APSwitchUpper.Vsieve_log_ratio_sharp

/-!
# `IsLinearRange` for the `h3` sieve problem

The `h3` sieve problem `bSieve x M Y` (odd primes below `Y`, density `ν d = 1/φ(d)`) satisfies
the classical dimension-1 condition **uniformly on every sub-range** below `Y`:

`∏_{w ≤ p < z'} (1 - ν p)⁻¹ ≤ (log z' / log w) (1 + K / log w)`  for all `2 ≤ w < z' ≤ Y`.

This is `Submission.ChenPlan.IsLinearRange (bSieve …) (Y:ℝ) K` at `M = chenSiftLimitTenth x`,
`Y = chenWindowTop x`, with a constant `K` for which the single-range condition `IsLinear` also
holds (supplied by `isLinear_bSieve`); the `∃ K` of the statement carries both.

The product over `[w, z')` is `VsieveOdd ⌈w⌉₊ / VsieveOdd ⌈z'⌉₊`.  The proof splits on whether
`⌈w⌉₊ ≥ Y₀`, where `Y₀` is the sharp two-scale Mertens threshold of `Vsieve_log_ratio_sharp`:

* `⌈w⌉₊ ≥ Y₀`: the sharp ratio gives `VsieveOdd ⌈w⌉₊ log ⌈w⌉₊ ≤ VsieveOdd ⌈z'⌉₊ log ⌈z'⌉₊ (1+c/log²⌈w⌉₊)`
  and `log ⌈z'⌉₊ ≤ log z' + 1/z'` absorbs the step of the ceiling;
* `⌈w⌉₊ < Y₀`: then `w < T` is bounded, and the crude Mertens lower bound
  `cv/log Z ≤ VsieveOdd Z` is enough (`log ⌈z'⌉₊ ≤ log z' + 1/z'`);

with the `K` chosen generously (the maximum of the two constants) so that all the elementary
real inequalities go through.
-/

namespace Work.ChenPlan.H3

open Finset
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

open Commons.NumberTheory.Chen.ChenEight

/-! ## 0. Monotonicity in the constant `K` -/

private lemma isLinear_mono {s : BoundingSieve} {z K K' : ℝ}
    (h : Submission.ChenPlan.IsLinear s z K) (hKK : K ≤ K') :
    Submission.ChenPlan.IsLinear s z K' := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨h1, fun w hw2 hwz => ?_⟩
  have hlogw : 0 < Real.log w := Real.log_pos (by linarith)
  have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
  refine le_trans (h2 w hw2 hwz) ?_
  apply mul_le_mul_of_nonneg_left _ (div_nonneg hlogz.le hlogw.le)
  have : K / Real.log w ≤ K' / Real.log w := div_le_div_of_nonneg_right hKK hlogw.le
  linarith

private lemma isLinearRange_mono {s : BoundingSieve} {z K K' : ℝ}
    (h : Submission.ChenPlan.IsLinearRange s z K) (hKK : K ≤ K') :
    Submission.ChenPlan.IsLinearRange s z K' := by
  intro w z' hw2 hwz hz'z
  have hlogw : 0 < Real.log w := Real.log_pos (by linarith)
  have hlogz' : 0 < Real.log z' := Real.log_pos (by linarith)
  refine le_trans (h w z' hw2 hwz hz'z) ?_
  apply mul_le_mul_of_nonneg_left _ (div_nonneg hlogz'.le hlogw.le)
  have : K / Real.log w ≤ K' / Real.log w := div_le_div_of_nonneg_right hKK hlogw.le
  linarith

/-! ## 1. Elementary real comparisons -/

/-- `log ⌈z⌉₊ ≤ log z + 1/z`, the price of replacing the real upper limit `z` by its ceiling. -/
private lemma log_ceil_le (z : ℝ) (hz : 0 < z) :
    Real.log (⌈z⌉₊ : ℝ) ≤ Real.log z + 1/z := by
  have h1 : (⌈z⌉₊ : ℝ) < z + 1 := Nat.ceil_lt_add_one hz.le
  have h2 : Real.log (⌈z⌉₊ : ℝ) < Real.log (z + 1) :=
    Real.log_lt_log (by exact_mod_cast (Nat.ceil_pos.mpr hz)) h1
  have h3 : Real.log (z + 1) = Real.log z + Real.log (1 + 1/z) := by
    rw [show z + 1 = z * (1 + 1/z) by field_simp, Real.log_mul (ne_of_gt hz) (by positivity)]
  have h4 : Real.log (1 + 1/z) ≤ 1/z := by
    have := Real.log_le_sub_one_of_pos (by positivity : (0:ℝ) < 1 + 1/z)
    linarith
  linarith

/-- The sharp-ratio comparison:
`((A+δ)/B)(1+c/B²) ≤ (A/B)(1+K/B)` whenever `0 < B ≤ A`, `0 ≤ δ ≤ 1/2`,
`log 2 ≤ B` and `K ≥ c/log 2 + (1/2)(1 + c/log²2)`. -/
private lemma sharp_compare {A B δ c K : ℝ} (hA : 0 < A) (hB : 0 < B) (hBA : B ≤ A)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1/2) (hB2 : Real.log 2 ≤ B) (hc : 0 < c)
    (hK : c/Real.log 2 + (1/2)*(1 + c/(Real.log 2)^2) ≤ K) :
    ((A + δ)/B) * (1 + c/B^2) ≤ (A/B)*(1 + K/B) := by
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hkey : c/B + δ*(1+c/B^2) ≤ K := by
    have h1 : c/B ≤ c/Real.log 2 := div_le_div_of_nonneg_left hc.le hlog2pos hB2
    have h2 : δ*(1+c/B^2) ≤ (1/2)*(1 + c/(Real.log 2)^2) := by
      apply mul_le_mul hδ1 ?_ (by positivity) (by norm_num)
      have h3 : c/B^2 ≤ c/(Real.log 2)^2 :=
        div_le_div_of_nonneg_left hc.le (by positivity) (by nlinarith)
      linarith
    linarith
  have hX : c/B^2 + (δ/A)*(1+c/B^2) ≤ K/B := by
    have h1 : (δ/A)*(1+c/B^2) ≤ (δ/B)*(1+c/B^2) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      rw [div_le_div_iff₀ hA hB]
      nlinarith [hδ0, hBA]
    have h2 : c/B^2 + (δ/B)*(1+c/B^2) ≤ K/B := by
      rw [show c/B^2 + (δ/B)*(1+c/B^2) = (1/B)*(c/B + δ*(1+c/B^2)) by ring,
          show K/B = (1/B)*K by ring]
      exact mul_le_mul_of_nonneg_left hkey (by positivity)
    linarith
  have hmain : δ + A*c/B^2 + δ*c/B^2 ≤ A*(K/B) := by
    have hAX : A*(c/B^2 + (δ/A)*(1+c/B^2)) = δ + A*c/B^2 + δ*c/B^2 := by
      field_simp
      ring
    rw [← hAX]
    exact mul_le_mul_of_nonneg_left hX hA.le
  calc ((A+δ)/B)*(1+c/B^2) = (1/B)*((A+δ)*(1+c/B^2)) := by ring
    _ ≤ (1/B)*(A*(1+K/B)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have e1 : (A+δ)*(1+c/B^2) = A + (δ + A*c/B^2 + δ*c/B^2) := by ring
        have e2 : A*(1+K/B) = A + A*(K/B) := by ring
        rw [e1, e2]; linarith [hmain]
    _ = (A/B)*(1+K/B) := by ring

/-- The crude Mertens comparison:
`(A+δ)/cv ≤ (A/B)(1+K/B)` whenever `0 < B ≤ A`, `0 ≤ δ ≤ 1/2`, `cv > 0` and
`B²/cv + B/(2cv) - B ≤ K`. -/
private lemma crude_compare {A B δ cv K : ℝ} (hA : 0 < A) (hB : 0 < B) (hBA : B ≤ A)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1/2) (hcv : 0 < cv)
    (hK : B^2/cv + B/(2*cv) - B ≤ K) :
    (A + δ)/cv ≤ (A/B)*(1 + K/B) := by
  have hK' : B^2 + B/2 - cv*B ≤ cv*K := by
    have h := mul_le_mul_of_nonneg_left hK hcv.le
    have heq : cv*(B^2/cv + B/(2*cv) - B) = B^2 + B/2 - cv*B := by
      field_simp
    rw [heq] at h; exact h
  have h1 : (A+δ)*B^2 ≤ A*B^2 + A*B/2 := by
    have ha : δ*B^2 ≤ (1/2)*B^2 := mul_le_mul_of_nonneg_right hδ (by positivity)
    have hb : (1/2)*B^2 ≤ A*B/2 := by
      have := mul_le_mul_of_nonneg_right hBA (by positivity : (0:ℝ) ≤ B/2)
      nlinarith [this]
    nlinarith [ha, hb]
  have h2 : A*B^2 + A*B/2 ≤ A*cv*(B+K) := by
    have h := mul_le_mul_of_nonneg_left hK' hA.le
    nlinarith [h]
  have hgoal : (A+δ)*B^2 ≤ A*cv*(B+K) := le_trans h1 h2
  have hconv : (A+δ)*B^2/cv ≤ A*(B+K) := by
    rw [div_le_iff₀ hcv]; linarith [hgoal]
  calc (A+δ)/cv = (A+δ)*B^2/cv / B^2 := by field_simp
    _ ≤ A*(B+K)/B^2 := div_le_div_of_nonneg_right hconv (by positivity)
    _ = (A/B)*(1+K/B) := by field_simp

/-! ## 2. The range product identity -/

private lemma oddLt_eq_empty_of_le_three (M : ℕ) (h : M ≤ 3) : oddLt M = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro p hp
  rw [Submission.mem_oddLt] at hp
  omega

private lemma VsieveOdd_eq_one_of_le_three (M : ℕ) (h : M ≤ 3) : VsieveOdd M = 1 := by
  rw [VsieveOdd, oddLt_eq_empty_of_le_three M h, Finset.prod_empty]

/-- For `z' ≤ Y` the odd primes of `oddLt Y` in `[w, z')` are exactly `oddLt ⌈z'⌉₊ \ oddLt ⌈w⌉₊`. -/
private lemma oddLt_filter_range_eq_sdiff (Y : ℕ) (w z' : ℝ) (hzY : z' ≤ Y) :
    (oddLt Y).filter (fun p : ℕ => w ≤ (p:ℝ) ∧ (p:ℝ) < z')
      = oddLt ⌈z'⌉₊ \ oddLt ⌈w⌉₊ := by
  have hmY : ⌈z'⌉₊ ≤ Y := Nat.ceil_le.mpr hzY
  ext p
  simp only [Finset.mem_filter, Finset.mem_sdiff, Submission.mem_oddLt]
  constructor
  · rintro ⟨⟨hpp, hp3, hpY⟩, hwp, hpz⟩
    exact ⟨⟨hpp, hp3, Nat.lt_ceil.mpr hpz⟩, fun hpn => by
      obtain ⟨-, -, hlt⟩ := hpn
      have : (p:ℝ) < w := Nat.lt_ceil.mp hlt
      linarith⟩
  · rintro ⟨⟨hpp, hp3, hpm⟩, hpn⟩
    exact ⟨⟨hpp, hp3, by omega⟩, by
      by_contra h
      push Not at h
      exact hpn ⟨hpp, hp3, Nat.lt_ceil.mpr h⟩, Nat.lt_ceil.mp hpm⟩

private lemma prod_oddLt_filter_range_inv_eq (Y : ℕ) (w z' : ℝ) (hwz : w < z') (hzY : z' ≤ Y) :
    ∏ p ∈ (oddLt Y).filter (fun p : ℕ => w ≤ (p:ℝ) ∧ (p:ℝ) < z'), (1 - 1/((p:ℝ)-1))⁻¹
      = VsieveOdd ⌈w⌉₊ / VsieveOdd ⌈z'⌉₊ := by
  have hnm : ⌈w⌉₊ ≤ ⌈z'⌉₊ := Nat.ceil_mono hwz.le
  have hsub : oddLt ⌈w⌉₊ ⊆ oddLt ⌈z'⌉₊ := oddLt_mono hnm
  rw [oddLt_filter_range_eq_sdiff Y w z' hzY, Finset.prod_inv_distrib]
  have hsd := Finset.prod_sdiff hsub (f := fun p : ℕ => (1 - 1/((p:ℝ)-1)))
  have hVw : VsieveOdd ⌈w⌉₊ ≠ 0 := ne_of_gt (VsieveOdd_pos _)
  have hP : (∏ x ∈ oddLt ⌈z'⌉₊ \ oddLt ⌈w⌉₊, (1 - 1/((x:ℝ)-1)))
      = VsieveOdd ⌈z'⌉₊ / VsieveOdd ⌈w⌉₊ := by
    rw [eq_div_iff hVw]
    rw [show (∏ x ∈ oddLt ⌈w⌉₊, (1 - 1/((x:ℝ)-1))) = VsieveOdd ⌈w⌉₊ from rfl,
        show (∏ x ∈ oddLt ⌈z'⌉₊, (1 - 1/((x:ℝ)-1))) = VsieveOdd ⌈z'⌉₊ from rfl] at hsd
    exact hsd
  rw [hP, inv_div]

/-- The range product for `bSieve`: the inverse sieve factors over the odd primes in `[w, z')`
equal `VsieveOdd ⌈w⌉₊ / VsieveOdd ⌈z'⌉₊`. -/
private lemma bSieve_prod_range (x M Y : ℕ) (w z' : ℝ) (hwz : w < z') (hzY : z' ≤ Y) :
    ∏ p ∈ (bSieve x M Y).prodPrimes.primeFactors.filter
        (fun p : ℕ => w ≤ (p:ℝ) ∧ (p:ℝ) < z'), (1 - (bSieve x M Y).nu p)⁻¹
      = VsieveOdd ⌈w⌉₊ / VsieveOdd ⌈z'⌉₊ := by
  rw [show (bSieve x M Y).prodPrimes = oddPrimLt Y from rfl,
    Work.NumberTheory.Chen.BTermCount.primeFactors_oddPrimLt,
    ← prod_oddLt_filter_range_inv_eq Y w z' hwz hzY]
  refine Finset.prod_congr rfl (fun p hp => ?_)
  obtain ⟨hpodd, -⟩ := Finset.mem_filter.mp hp
  have hpp : p.Prime := (Finset.mem_filter.mp hpodd).2.1
  rw [show (bSieve x M Y).nu = invTotient from rfl, invTotient_apply,
      Nat.totient_prime hpp, Nat.cast_sub (by have := hpp.two_le; omega : 1 ≤ p)]
  push_cast
  ring

/-! ## 3. `IsLinearRange` for the sieve, given the two Mertens ingredients -/

private lemma isLinearRange_bSieve_aux (c cv : ℝ) (hc : 0 < c) (hcv : 0 < cv)
    (Y₀ T : ℕ) (K : ℝ) (hT4 : 4 ≤ T) (hTY₀ : Y₀ ≤ T)
    (hK1 : c/Real.log 2 + (1/2)*(1 + c/(Real.log 2)^2) ≤ K)
    (hK2 : (Real.log (T:ℝ))^2/cv + Real.log (T:ℝ)/(2*cv) ≤ K)
    (hVlow : ∀ Z : ℕ, 4 ≤ Z → cv / Real.log (Z:ℝ) ≤ VsieveOdd Z)
    (hsharp : ∀ u Z : ℕ, Y₀ ≤ u → u ≤ Z →
      VsieveOdd u * Real.log (u:ℝ) ≤ VsieveOdd Z * Real.log (Z:ℝ) *
        (1 + c / (Real.log (u:ℝ))^2))
    (x M Y : ℕ) (hYge : T ≤ Y) :
    Submission.ChenPlan.IsLinearRange (bSieve x M Y) (Y : ℝ) K := by
  intro w z' hw2 hwz hz'z
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hw2R : (2:ℝ) ≤ w := by exact_mod_cast hw2
  have hlogw : 0 < Real.log w := Real.log_pos (by linarith)
  have hlogz' : 0 < Real.log z' := Real.log_pos (by linarith)
  have hB2 : Real.log 2 ≤ Real.log w := Real.log_le_log (by norm_num) hw2R
  have hBA : Real.log w ≤ Real.log z' := Real.log_le_log (by linarith) hwz.le
  have hz'2 : (0:ℝ) < z' := by linarith
  have hδ2 : 1/z' ≤ 1/2 := by
    rw [div_le_div_iff₀ hz'2 (by norm_num)]
    linarith
  have hml : Real.log (⌈z'⌉₊ : ℝ) ≤ Real.log z' + 1/z' := log_ceil_le z' hz'2
  have hKnn : 0 ≤ K := by
    have : 0 ≤ c/Real.log 2 + (1/2)*(1 + c/(Real.log 2)^2) := by positivity
    linarith
  rw [bSieve_prod_range x M Y w z' hwz hz'z]
  have hnm : ⌈w⌉₊ ≤ ⌈z'⌉₊ := Nat.ceil_mono hwz.le
  by_cases hnY : Y₀ ≤ ⌈w⌉₊
  · -- ## sharp regime
    have hn2 : 2 ≤ ⌈w⌉₊ := by
      have : (2:ℝ) ≤ (⌈w⌉₊ : ℝ) := le_trans hw2R (Nat.le_ceil w)
      exact_mod_cast this
    have hlogn : 0 < Real.log (⌈w⌉₊ : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < ⌈w⌉₊))
    have hsh := hsharp ⌈w⌉₊ ⌈z'⌉₊ hnY hnm
    have hratio : VsieveOdd ⌈w⌉₊ / VsieveOdd ⌈z'⌉₊
        ≤ (Real.log (⌈z'⌉₊:ℝ)/Real.log (⌈w⌉₊:ℝ)) * (1 + c/(Real.log (⌈w⌉₊:ℝ))^2) := by
      rw [div_le_iff₀ (VsieveOdd_pos ⌈z'⌉₊)]
      rw [show ((Real.log (⌈z'⌉₊:ℝ) / Real.log (⌈w⌉₊:ℝ)) * (1 + c/(Real.log (⌈w⌉₊:ℝ))^2))
            * VsieveOdd ⌈z'⌉₊
          = (VsieveOdd ⌈z'⌉₊ * Real.log (⌈z'⌉₊:ℝ) * (1 + c/(Real.log (⌈w⌉₊:ℝ))^2))
            / Real.log (⌈w⌉₊:ℝ) from by field_simp]
      rw [le_div_iff₀ hlogn]
      exact hsh
    have hlnw : Real.log w ≤ Real.log (⌈w⌉₊ : ℝ) :=
      Real.log_le_log (by linarith : (0:ℝ) < w) (Nat.le_ceil w)
    have hbound : VsieveOdd ⌈w⌉₊ / VsieveOdd ⌈z'⌉₊
        ≤ ((Real.log z' + 1/z')/Real.log w) * (1 + c/(Real.log w)^2) := by
      refine le_trans hratio (mul_le_mul ?_ ?_ ?_ ?_)
      · have h1 : Real.log (⌈z'⌉₊:ℝ)/Real.log (⌈w⌉₊:ℝ)
            ≤ (Real.log z' + 1/z')/Real.log (⌈w⌉₊:ℝ) :=
          div_le_div_of_nonneg_right hml hlogn.le
        have h2 : (Real.log z' + 1/z')/Real.log (⌈w⌉₊:ℝ)
            ≤ (Real.log z' + 1/z')/Real.log w :=
          div_le_div_of_nonneg_left (by positivity) hlogw hlnw
        linarith
      · have h3 : Real.log w ^ 2 ≤ Real.log (⌈w⌉₊:ℝ)^2 := by nlinarith [hlnw, hlogw]
        have h4 : c/(Real.log (⌈w⌉₊:ℝ))^2 ≤ c/(Real.log w)^2 :=
          div_le_div_of_nonneg_left hc.le (by positivity) h3
        linarith
      · positivity
      · exact div_nonneg (by positivity) hlogw.le
    exact le_trans hbound (sharp_compare hlogz' hlogw hBA (by positivity) hδ2 hB2 hc hK1)
  · -- ## crude regime: `⌈w⌉₊ < Y₀`
    push Not at hnY
    have hwt : w < (T:ℝ) := by
      have h1 : w ≤ (⌈w⌉₊ : ℝ) := Nat.le_ceil w
      have h2 : ((⌈w⌉₊ : ℕ) : ℝ) < (Y₀ : ℝ) := by exact_mod_cast hnY
      have h3 : (Y₀ : ℝ) ≤ (T : ℝ) := by exact_mod_cast hTY₀
      linarith
    have hBT : Real.log w ≤ Real.log (T:ℝ) :=
      Real.log_le_log (by linarith : (0:ℝ) < w) hwt.le
    have hlogTnn : 0 ≤ Real.log (T:ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ T))
    by_cases hm4 : ⌈z'⌉₊ < 4
    · rw [VsieveOdd_eq_one_of_le_three ⌈w⌉₊ (by omega),
        VsieveOdd_eq_one_of_le_three ⌈z'⌉₊ (by omega), div_one]
      have h1 : 1 ≤ Real.log z' / Real.log w := by
        rw [le_div_iff₀ hlogw]; linarith
      have h2 : 1 ≤ 1 + K/Real.log w := by
        have : 0 ≤ K/Real.log w := div_nonneg hKnn hlogw.le
        linarith
      nlinarith [h1, h2, mul_nonneg (by linarith : (0:ℝ) ≤ Real.log z'/Real.log w) (by linarith : (0:ℝ) ≤ 1 + K/Real.log w)]
    · have hm4' : 4 ≤ ⌈z'⌉₊ := by omega
      have hVlowm := hVlow ⌈z'⌉₊ hm4'
      have hlogm : 0 < Real.log (⌈z'⌉₊:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < ⌈z'⌉₊))
      have hPle : VsieveOdd ⌈w⌉₊ / VsieveOdd ⌈z'⌉₊ ≤ Real.log (⌈z'⌉₊:ℝ) / cv := by
        have ha : VsieveOdd ⌈w⌉₊ / VsieveOdd ⌈z'⌉₊ ≤ 1 / VsieveOdd ⌈z'⌉₊ := by
          rw [div_le_div_iff_of_pos_right (VsieveOdd_pos ⌈z'⌉₊)]
          exact VsieveOdd_le_one ⌈w⌉₊
        have hb : 1 / VsieveOdd ⌈z'⌉₊ ≤ Real.log (⌈z'⌉₊:ℝ) / cv := by
          rw [div_le_div_iff₀ (VsieveOdd_pos ⌈z'⌉₊) hcv]
          have h5 : cv ≤ Real.log (⌈z'⌉₊:ℝ) * VsieveOdd ⌈z'⌉₊ := by
            have h := mul_le_mul_of_nonneg_left hVlowm hlogm.le
            have heq : Real.log (⌈z'⌉₊:ℝ) * (cv / Real.log (⌈z'⌉₊:ℝ)) = cv := by field_simp
            rwa [heq] at h
          linarith
        linarith
      have hPle2 : VsieveOdd ⌈w⌉₊ / VsieveOdd ⌈z'⌉₊ ≤ (Real.log z' + 1/z')/cv := by
        have : Real.log (⌈z'⌉₊:ℝ)/cv ≤ (Real.log z' + 1/z')/cv :=
          div_le_div_of_nonneg_right hml hcv.le
        linarith
      have hK2' : Real.log w^2/cv + Real.log w/(2*cv) - Real.log w ≤ K := by
        have h1 : Real.log w^2 ≤ (Real.log (T:ℝ))^2 := by nlinarith [hBT, hlogTnn]
        have h2 : Real.log w^2/cv ≤ (Real.log (T:ℝ))^2/cv := div_le_div_of_nonneg_right h1 hcv.le
        have h3 : Real.log w/(2*cv) ≤ Real.log (T:ℝ)/(2*cv) :=
          div_le_div_of_nonneg_right hBT (by positivity)
        linarith [hK2, h2, h3, hlogw.le]
      exact le_trans hPle2 (crude_compare hlogz' hlogw hBA (by positivity) hδ2 hcv hK2')

/-! ## 4. The sharp two-scale Mertens ratio in relative form -/

private lemma vsieveOdd_ratio_sharp_aux :
    ∃ c : ℝ, 0 < c ∧ ∃ Y₀ : ℕ, ∀ u Z : ℕ, Y₀ ≤ u → u ≤ Z →
      VsieveOdd u * Real.log (u:ℝ) ≤ VsieveOdd Z * Real.log (Z:ℝ) *
        (1 + c / (Real.log (u:ℝ))^2) := by
  obtain ⟨c, hc, Y₀, h⟩ :=
    Work.NumberTheory.Chen.APSwitchUpper.Vsieve_log_ratio_sharp 2 (by norm_num)
  refine ⟨c, hc, Y₀, fun u Z hu huZ => ?_⟩
  have hA : Real.log (u:ℝ) ^ (2:ℝ) = Real.log (u:ℝ) ^ (2:ℕ) := Real.rpow_natCast _ 2
  have h1 : VsieveOdd u * Real.log (u:ℝ) - VsieveOdd Z * Real.log (Z:ℝ)
      ≤ c * (VsieveOdd Z * Real.log (Z:ℝ)) / (Real.log (u:ℝ))^2 := by
    have h0 := (abs_le.mp (h u Z hu huZ)).2
    simp only [Work.NumberTheory.Chen.APSwitchUpper.Vsieve_eq_VsieveOdd, hA] at h0
    exact h0
  calc VsieveOdd u * Real.log (u:ℝ)
      ≤ VsieveOdd Z * Real.log (Z:ℝ)
          + c * (VsieveOdd Z * Real.log (Z:ℝ)) / (Real.log (u:ℝ))^2 :=
        sub_le_iff_le_add'.mp h1
    _ = VsieveOdd Z * Real.log (Z:ℝ) * (1 + c / (Real.log (u:ℝ))^2) := by ring

/-! ## 5. The theorem -/

theorem isLinearRange_bSieve :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ x : ℕ in Filter.atTop,
      Submission.ChenPlan.IsLinear
        (Work.ChenPlan.H3.bSieve x (Submission.chenSiftLimitTenth x) (Submission.chenWindowTop x))
        (Submission.chenWindowTop x : ℝ) K ∧
      Submission.ChenPlan.IsLinearRange
        (Work.ChenPlan.H3.bSieve x (Submission.chenSiftLimitTenth x) (Submission.chenWindowTop x))
        (Submission.chenWindowTop x : ℝ) K := by
  obtain ⟨Klin, hKlin, hLinEv⟩ := isLinear_bSieve
  obtain ⟨c, hc, Y₀, hsharp⟩ := vsieveOdd_ratio_sharp_aux
  obtain ⟨cv, Cv, hcvpos, hCvpos, hVb⟩ := Commons.NumberTheory.Chen.Vsieve_bounds
  have hVlow : ∀ Z : ℕ, 4 ≤ Z → cv / Real.log (Z:ℝ) ≤ VsieveOdd Z := by
    intro Z hZ
    have h := (hVb Z hZ).1
    rwa [Work.NumberTheory.Chen.APSwitchUpper.Vsieve_eq_VsieveOdd] at h
  set T : ℕ := max Y₀ 4 with hT
  have hT4 : 4 ≤ T := by rw [hT]; exact le_max_right _ _
  have hTY₀ : Y₀ ≤ T := by rw [hT]; exact le_max_left _ _
  set K1 : ℝ := c/Real.log 2 + (1/2)*(1 + c/(Real.log 2)^2) with hK1def
  set K2 : ℝ := (Real.log (T:ℝ))^2/cv + Real.log (T:ℝ)/(2*cv) with hK2def
  refine ⟨max Klin (max K1 K2), ?_, ?_⟩
  · exact le_trans hKlin (le_max_left _ _)
  · have hEv : ∀ᶠ x : ℕ in Filter.atTop, T ≤ Submission.chenWindowTop x := by
      have h1 : ∀ᶠ x : ℕ in Filter.atTop, (T:ℝ) ≤ Real.rpow (x:ℝ) (1/3) :=
        (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/3)).comp
          tendsto_natCast_atTop_atTop |>.eventually (Filter.eventually_ge_atTop (T:ℝ))
      filter_upwards [h1] with x hx
      unfold Submission.chenWindowTop
      have : T ≤ ⌊Real.rpow (x:ℝ) (1/3)⌋₊ := Nat.le_floor hx
      omega
    filter_upwards [hEv, hLinEv] with x hx hlin
    refine ⟨isLinear_mono hlin (le_max_left Klin (max K1 K2)), ?_⟩
    refine isLinearRange_bSieve_aux c cv hc hcvpos Y₀ T _ hT4 hTY₀ ?_ ?_ hVlow hsharp
      x (Submission.chenSiftLimitTenth x) (Submission.chenWindowTop x) hx
    · show K1 ≤ max Klin (max K1 K2)
      exact le_trans (le_max_left K1 K2) (le_max_right Klin (max K1 K2))
    · show K2 ≤ max Klin (max K1 K2)
      exact le_trans (le_max_right K1 K2) (le_max_right Klin (max K1 K2))

end

end Work.ChenPlan.H3
