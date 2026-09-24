import Mathlib
import Submission.Commons.NumberTheory.Mertens.primeProduct_oneSubInv_ge_sharp
import Submission.Commons.NumberTheory.Mertens.prime_euler_constant_identity
import Submission.Commons.NumberTheory.Mertens.second_mertens_converges
import Submission.Commons.NumberTheory.Mertens.corr_partial_sums_tendsto_tsum
import Submission.Commons.NumberTheory.Mertens.corr_sum_tail_bound
import Submission.Commons.NumberTheory.Mertens.eulerMascheroni_exp_neg_lower

open Finset Real Filter MeasureTheory
open scoped BigOperators Topology

namespace Commons.NumberTheory.Sieve

noncomputable section

set_option maxRecDepth 1000000
set_option maxHeartbeats 8000000

namespace Aux
open Commons.NumberTheory.Mertens

private lemma logDiv_le_log_sub_real' (t : ℝ) (ht : 100 ≤ t) :
    logDiv t ≤ Real.log t - 0.3 := by
  have hfloor : 100 ≤ ⌊t⌋₊ := by
    have h := Nat.floor_mono ht
    norm_num at h
    exact h
  have hle := logDiv_le_log_sub ⌊t⌋₊ hfloor
  have hlogle : Real.log ((⌊t⌋₊ : ℕ) : ℝ) ≤ Real.log t :=
    Real.log_le_log (by positivity) (Nat.floor_le (by linarith))
  have hlogdiv : logDiv t
      = ∑ p ∈ (⌊t⌋₊).primesLE, Real.log (p : ℝ) / (p : ℝ) := rfl
  rw [hlogdiv]; linarith

private lemma intble_inv_log {x X : ℝ} (hx : 2 ≤ x) (hxX : x ≤ X) :
    IntervalIntegrable (fun t : ℝ => t⁻¹ / Real.log t) volume x X := by
  refine ContinuousOn.intervalIntegrable ?_
  intro z hz
  rw [Set.uIcc_of_le hxX] at hz
  have hz2 : 2 ≤ z := le_trans hx hz.1
  have hz0 : z ≠ 0 := by linarith
  have hlogz : Real.log z ≠ 0 := by
    apply log_ne_zero_of_pos_of_ne_one <;> linarith
  exact ((continuousAt_id.inv₀ hz0).div (Real.continuousAt_log hz0) hlogz).continuousWithinAt

private lemma intble_inv_log_sq {x X : ℝ} (hx : 2 ≤ x) (hxX : x ≤ X) :
    IntervalIntegrable (fun t : ℝ => t⁻¹ / (Real.log t) ^ 2) volume x X := by
  refine ContinuousOn.intervalIntegrable ?_
  intro z hz
  rw [Set.uIcc_of_le hxX] at hz
  have hz2 : 2 ≤ z := le_trans hx hz.1
  have hz0 : z ≠ 0 := by linarith
  have hlogz : Real.log z ≠ 0 := by
    apply log_ne_zero_of_pos_of_ne_one <;> linarith
  exact ((continuousAt_id.inv₀ hz0).div ((Real.continuousAt_log hz0).pow 2)
    (pow_ne_zero 2 hlogz)).continuousWithinAt

private lemma e_diff_le (x X : ℝ) (hx : 100 ≤ x) (hxX : x ≤ X) :
    (primeRecips X - Real.log (Real.log X)) - (primeRecips x - Real.log (Real.log x))
      ≤ (73 / 50) / Real.log x := by
  set B : ℝ := -(3 / 10) with hB
  have hs_le : ∀ t : ℝ, 100 ≤ t → logDiv t - Real.log t - B ≤ 0 := by
    intro t ht
    have := logDiv_le_log_sub_real' t ht
    simp only [hB]; linarith
  have hs_ge : ∀ t : ℝ, 100 ≤ t → -(73 / 50) ≤ logDiv t - Real.log t - B := by
    intro t ht
    have := logDiv_ge_log_sub_sharp t (by linarith)
    simp only [hB]; linarith
  have hX100 : 100 ≤ X := le_trans hx hxX
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
  have hident := primeRecips_loglog_diff (x := x) (X := X) (B₁ := B) (by linarith) hxX
  have hF : IntervalIntegrable (fun t : ℝ => logDiv t / (t * (Real.log t) ^ 2))
      volume x X := intervalIntegrable_logDiv_div_id_log_sq_gen (by linarith) hxX
  have hU : IntervalIntegrable (fun t : ℝ => t⁻¹ / Real.log t) volume x X :=
    intble_inv_log (by linarith) hxX
  have hV : IntervalIntegrable (fun t : ℝ => t⁻¹ / (Real.log t) ^ 2) volume x X :=
    intble_inv_log_sq (by linarith) hxX
  have hg : IntervalIntegrable
      (fun t : ℝ => (logDiv t - Real.log t - B) / (t * (Real.log t) ^ 2))
      volume x X := by
    refine IntervalIntegrable.congr ?_ (hF.sub hU |>.sub (hV.const_mul B))
    intro t ht
    rw [Set.uIoc_of_le hxX] at ht
    have ht2 : 2 ≤ t := le_trans (by linarith) (le_of_lt ht.1)
    have ht0 : t ≠ 0 := by linarith
    have hlogt : Real.log t ≠ 0 := by
      apply log_ne_zero_of_pos_of_ne_one <;> linarith
    field_simp
  have hterm1 : (logDiv X - Real.log X - B) / Real.log X ≤ 0 :=
    div_nonpos_iff.mpr (Or.inr ⟨hs_le X hX100, hlogX.le⟩)
  have hterm2 : -((logDiv x - Real.log x - B) / Real.log x) ≤ (73 / 50) / Real.log x := by
    rw [← neg_div, div_le_div_iff_of_pos_right hlogx]
    have hs := hs_ge x hx
    linarith
  have hInt : (∫ t in x..X, (logDiv t - Real.log t - B) / (t * (Real.log t) ^ 2)) ≤ 0 := by
    have hzero : IntervalIntegrable (fun _ : ℝ => (0:ℝ)) volume x X := intervalIntegrable_const
    have hmono := intervalIntegral.integral_mono_on hxX hg hzero (fun t ht => ?_)
    · simpa using hmono
    · have ht100 : 100 ≤ t := le_trans hx ht.1
      have hlogt : 0 < Real.log t := Real.log_pos (by linarith : (1:ℝ) < t)
      have hden : 0 ≤ t * (Real.log t)^2 := by positivity
      exact div_nonpos_of_nonpos_of_nonneg (hs_le t ht100) hden
  rw [hident]
  linarith [hterm1, hterm2, hInt]

private lemma my_corr_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 100 ≤ x →
      |(∑' p : Nat.Primes, corrTerm p) - logRatioCorrSum x| ≤ C / x := by
  obtain ⟨C, hCpos, hC⟩ := corr_sum_tail_bound
  refine ⟨2 * C, by linarith, ?_⟩
  intro x hx
  have hxpos : (0:ℝ) < x := by linarith
  have hfloor1 : 1 ≤ ⌊x⌋₊ := by
    apply Nat.le_floor; push_cast; linarith
  have hbound := hC ⌊x⌋₊ hfloor1
  have hlog : logRatioCorrSum x = ∑ k ∈ Finset.range (⌊x⌋₊ + 1), corrExt k := by
    rw [logRatioCorrSum, partial_sum_eq_range]
  rw [tsum_corrExt_eq, hlog]
  have hfloorth : x / 2 ≤ (⌊x⌋₊ : ℝ) := by
    have hlt := Nat.lt_floor_add_one x; linarith
  have hhalfpos : (0:ℝ) < x / 2 := by linarith
  have h1 : (1:ℝ) / (⌊x⌋₊ : ℝ) ≤ 1 / (x / 2) :=
    one_div_le_one_div_of_le hhalfpos hfloorth
  have hmono : C / (⌊x⌋₊ : ℝ) ≤ C / (x / 2) := by
    rw [div_eq_mul_one_div, div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left (by simpa [one_div] using h1) hCpos.le
  have heq : C / (x / 2) = (2 * C) / x := by
    field_simp
  linarith [hbound, hmono, heq]

private lemma my_pw_eq (N m : ℕ) (hNm : N ≤ m) :
    (∑ k ∈ Finset.range (m + 1), corrExt k) - (∑ k ∈ Finset.range (N + 1), corrExt k)
      = ∑ k ∈ Finset.Icc (N + 1) m, corrExt k := by
  have hsub : Finset.range (N + 1) ⊆ Finset.range (m + 1) := by
    intro x hx
    exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) (by omega))
  have hsum := Finset.sum_sdiff (s₁ := Finset.range (N + 1)) (s₂ := Finset.range (m + 1))
    (f := corrExt) hsub
  have hset : Finset.range (m + 1) \ Finset.range (N + 1) = Finset.Icc (N + 1) m := by
    ext x; simp [Finset.mem_Icc]; omega
  calc (∑ k ∈ Finset.range (m + 1), corrExt k) - (∑ k ∈ Finset.range (N + 1), corrExt k)
      = (∑ k ∈ Finset.range (m + 1) \ Finset.range (N + 1), corrExt k) := by rw [← hsum]; ring
    _ = ∑ k ∈ Finset.Icc (N + 1) m, corrExt k := by rw [hset]

private lemma my_pw_bound (N m : ℕ) (hNm : N ≤ m) :
    |(∑ k ∈ Finset.range (m + 1), corrExt k) - (∑ k ∈ Finset.range (N + 1), corrExt k)|
      ≤ (4 : ℝ) / ((N : ℝ) + 1) := by
  have hIccIoo : Finset.Icc (N + 1) m = Finset.Ioo N (m + 1) := by
    ext x; simp [Finset.mem_Icc, Finset.mem_Ioo]
  calc |(∑ k ∈ Finset.range (m + 1), corrExt k) - (∑ k ∈ Finset.range (N + 1), corrExt k)|
      = |∑ k ∈ Finset.Icc (N + 1) m, corrExt k| := by rw [my_pw_eq N m hNm]
    _ ≤ ∑ k ∈ Finset.Icc (N + 1) m, |corrExt k| :=
        Finset.abs_sum_le_sum_abs corrExt (Finset.Icc (N + 1) m)
    _ ≤ ∑ k ∈ Finset.Icc (N + 1) m, (2 : ℝ) / (k : ℝ) ^ 2 := by
        refine Finset.sum_le_sum ?_; intro k hk
        simpa [Real.norm_eq_abs] using corrExt_bound k
    _ = ∑ k ∈ Finset.Icc (N + 1) m, (2 : ℝ) * (((k : ℝ) ^ 2)⁻¹) := by
        refine Finset.sum_congr rfl ?_; intro k hk; rw [div_eq_mul_inv]
    _ = (2 : ℝ) * ∑ k ∈ Finset.Icc (N + 1) m, (((k : ℝ) ^ 2)⁻¹) := by rw [Finset.mul_sum]
    _ = (2 : ℝ) * ∑ k ∈ Finset.Ioo N (m + 1), (((k : ℝ) ^ 2)⁻¹) := by rw [hIccIoo]
    _ ≤ (2 : ℝ) * (2 / ((N : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left (sum_Ioo_inv_sq_le (α := ℝ) N (m + 1)) (by norm_num)
    _ = (4 : ℝ) / ((N : ℝ) + 1) := by ring

private lemma my_corr_abs (N : ℕ) (hN : 1 ≤ N) :
    |(∑' n : ℕ, corrExt n) - (∑ k ∈ Finset.range (N + 1), corrExt k)| ≤ (4 : ℝ) / (N : ℝ) := by
  let S : ℕ → ℝ := fun m => ∑ k ∈ Finset.range (m + 1), corrExt k
  let T : ℝ := ∑' n : ℕ, corrExt n
  have hS : Tendsto S atTop (nhds T) := by dsimp [S, T]; exact tendsto_partial_range_add_one
  have hev : ∀ᶠ m : ℕ in atTop, |S m - S N| ≤ (4 : ℝ) / ((N : ℝ) + 1) := by
    filter_upwards [eventually_ge_atTop N] with m hm
    dsimp [S]; exact my_pw_bound N m hm
  have hsub : Tendsto (fun m : ℕ => S m - S N) atTop (nhds (T - S N)) := hS.sub tendsto_const_nhds
  have hlim : Tendsto (fun m : ℕ => |S m - S N|) atTop (nhds (|T - S N|)) :=
    (continuous_abs.tendsto (T - S N)).comp hsub
  have hb : |T - S N| ≤ (4 : ℝ) / ((N : ℝ) + 1) := le_of_tendsto hlim hev
  have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hlt : (4:ℝ) / ((N:ℝ)+1) ≤ 4 / (N:ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) hNpos (by linarith)
  exact le_trans hb hlt

private lemma my_corr_tail {x : ℝ} (hx : 100 ≤ x) :
    (∑' p : Nat.Primes, corrTerm p) - logRatioCorrSum x ≤ 8 / x := by
  have hN1 : 1 ≤ ⌊x⌋₊ := by apply Nat.le_floor; push_cast; linarith
  have hb := my_corr_abs ⌊x⌋₊ hN1
  have hlogCorr : logRatioCorrSum x = ∑ k ∈ Finset.range (⌊x⌋₊ + 1), corrExt k := by
    rw [logRatioCorrSum, partial_sum_eq_range]
  rw [tsum_corrExt_eq, hlogCorr]
  have h1 : (∑' n : ℕ, corrExt n) - (∑ k ∈ Finset.range (⌊x⌋₊ + 1), corrExt k)
      ≤ |(∑' n : ℕ, corrExt n) - (∑ k ∈ Finset.range (⌊x⌋₊ + 1), corrExt k)| := le_abs_self _
  have h3 : x / 2 ≤ (⌊x⌋₊ : ℝ) := by have := Nat.lt_floor_add_one x; linarith
  have h2 : (4:ℝ) / (⌊x⌋₊ : ℝ) ≤ 8 / x := by
    have h4 : (4:ℝ) / (⌊x⌋₊ : ℝ) ≤ 4 / (x/2) :=
      div_le_div_of_nonneg_left (by norm_num) (by linarith) h3
    have h5 : (4:ℝ)/(x/2) = 8/x := by field_simp; ring
    linarith [h4, h5.le, h5.ge]
  linarith [h1, hb, h2]

theorem my_logRatioSum_ge (x : ℝ) (hx : 100 ≤ x) :
    Real.log (Real.log x) + Real.eulerMascheroniConstant - (73/50) / Real.log x - 8 / x
      ≤ logRatioSum x := by
  obtain ⟨M, hM⟩ := second_mertens_converges
  have hγ := prime_euler_constant_identity (M := M) hM
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have he : M - (primeRecips x - Real.log (Real.log x)) ≤ (73 / 50) / Real.log x := by
    have hlim : Tendsto (fun X : ℝ =>
        (primeRecips X - Real.log (Real.log X)) - (primeRecips x - Real.log (Real.log x)))
        atTop (nhds (M - (primeRecips x - Real.log (Real.log x)))) :=
      hM.sub tendsto_const_nhds
    exact le_of_tendsto hlim (eventually_atTop.mpr ⟨x, fun X hxX => e_diff_le x X hx hxX⟩)
  have hcorr : (∑' p : Nat.Primes, corrTerm p) - logRatioCorrSum x ≤ 8 / x := my_corr_tail hx
  have hsum : logRatioSum x = primeRecips x + logRatioCorrSum x := by
    simp only [logRatioSum, primeRecips, logRatioCorrSum, corrTerm]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun p _ => by ring)
  have hγ' : Real.eulerMascheroniConstant = M + ∑' p : Nat.Primes, corrTerm p := by
    rw [← hγ]; congr 1
  have key : Real.eulerMascheroniConstant - (primeRecips x + logRatioCorrSum x - Real.log (Real.log x))
      = (M - (primeRecips x - Real.log (Real.log x)))
        + ((∑' p : Nat.Primes, corrTerm p) - logRatioCorrSum x) := by
    rw [hγ']; ring
  rw [hsum]
  linarith [he, hcorr, key]

end Aux

/-! ## The singular-series products over odd primes -/

/-- The odd factor `1 - 1/(q-1)`. -/
def oddFac (q : ℕ) : ℝ := 1 - (1 : ℝ) / ((q : ℝ) - 1)

/-- The squared odd factor `1 - 1/(q-1)^2`. -/
def oddSqFac (q : ℕ) : ℝ := 1 - (1 : ℝ) / ((q : ℝ) - 1) ^ 2

/-- `∏_{3 ≤ q ≤ n} (1 - 1/(q-1))` (product over odd primes). -/
def oddProd (n : ℕ) : ℝ :=
  ∏ q ∈ (Nat.primesLE n).filter (fun q : ℕ => q ≠ 2), oddFac q

/-- `∏_{3 ≤ q ≤ n} (1 - 1/(q-1)^2)` (product over odd primes). -/
def oddSqProd (n : ℕ) : ℝ :=
  ∏ q ∈ (Nat.primesLE n).filter (fun q : ℕ => q ≠ 2), oddSqFac q

/-- `∏_{p ≤ n} (1 - 1/p)` (product over all primes). -/
def primeProd (n : ℕ) : ℝ :=
  ∏ q ∈ Nat.primesLE n, (1 - (1 : ℝ) / (q : ℝ))

private lemma oddFac01 {m q : ℕ} (hq : q ∈ (Nat.primesLE m).filter (fun q : ℕ => q ≠ 2)) :
    0 ≤ oddFac q ∧ oddFac q ≤ 1 := by
  have hp : Nat.Prime q := (Nat.mem_primesLE.mp (Finset.mem_filter.mp hq).1).2
  have hqne : q ≠ 2 := (Finset.mem_filter.mp hq).2
  have h3 : 3 ≤ q := by have := hp.two_le; omega
  have h3' : (3:ℝ) ≤ (q:ℝ) := by exact_mod_cast h3
  have hpos : 0 < (q:ℝ) - 1 := by linarith
  have hle : (1:ℝ)/((q:ℝ)-1) ≤ 1 := by rw [div_le_one hpos]; linarith
  have hnn : 0 ≤ (1:ℝ)/((q:ℝ)-1) := div_nonneg (by norm_num) hpos.le
  unfold oddFac
  exact ⟨by linarith, by linarith⟩

private lemma oddSqFac01 {m q : ℕ} (hq : q ∈ (Nat.primesLE m).filter (fun q : ℕ => q ≠ 2)) :
    0 ≤ oddSqFac q ∧ oddSqFac q ≤ 1 := by
  have hp : Nat.Prime q := (Nat.mem_primesLE.mp (Finset.mem_filter.mp hq).1).2
  have hqne : q ≠ 2 := (Finset.mem_filter.mp hq).2
  have h3 : 3 ≤ q := by have := hp.two_le; omega
  have h3' : (3:ℝ) ≤ (q:ℝ) := by exact_mod_cast h3
  have hpos : 0 < ((q:ℝ) - 1)^2 := pow_pos (by linarith : (0:ℝ) < (q:ℝ)-1) 2
  have hle : (1:ℝ)/((q:ℝ)-1)^2 ≤ 1 := by rw [div_le_one hpos]; nlinarith
  have hnn : 0 ≤ (1:ℝ)/((q:ℝ)-1)^2 := div_nonneg (by norm_num) (by positivity)
  unfold oddSqFac
  exact ⟨by linarith, by linarith⟩

private lemma oddfilter_mono {a b : ℕ} (hab : a ≤ b) :
    (Nat.primesLE a).filter (fun q : ℕ => q ≠ 2)
      ⊆ (Nat.primesLE b).filter (fun q : ℕ => q ≠ 2) := by
  intro q hq
  rw [Finset.mem_filter] at hq ⊢
  exact ⟨Nat.mem_primesLE.mpr
    ⟨le_trans (Nat.mem_primesLE.mp hq.1).1 hab, (Nat.mem_primesLE.mp hq.1).2⟩, hq.2⟩

lemma oddProd_nonneg (n : ℕ) : 0 ≤ oddProd n := by
  unfold oddProd
  exact Finset.prod_nonneg (fun q hq => (oddFac01 hq).1)

lemma oddProd_le_one (n : ℕ) : oddProd n ≤ 1 := by
  unfold oddProd
  exact Finset.prod_le_one₀ (fun q hq => (oddFac01 hq).1) (fun q hq => (oddFac01 hq).2)

lemma oddSqProd_nonneg (n : ℕ) : 0 ≤ oddSqProd n := by
  unfold oddSqProd
  exact Finset.prod_nonneg (fun q hq => (oddSqFac01 hq).1)

lemma primeProd_nonneg (n : ℕ) : 0 ≤ primeProd n := by
  unfold primeProd
  refine Finset.prod_nonneg ?_
  intro q hq
  have hp : Nat.Prime q := (Nat.mem_primesLE.mp hq).2
  have hq2 : (2:ℝ) ≤ (q:ℝ) := by exact_mod_cast hp.two_le
  have hlt : (1:ℝ)/(q:ℝ) < 1 := by rw [div_lt_one (by linarith)]; linarith
  linarith

/-- `oddProd` is antitone. -/
lemma oddProd_anti : Antitone oddProd := by
  intro a b hab
  unfold oddProd
  rw [← Finset.prod_sdiff (oddfilter_mono hab)]
  have hnonneg : 0 ≤ ∏ q ∈ (Nat.primesLE a).filter (fun q : ℕ => q ≠ 2), oddFac q :=
    Finset.prod_nonneg (fun q hq => (oddFac01 hq).1)
  have h1 : (∏ q ∈ (Nat.primesLE b).filter (fun q : ℕ => q ≠ 2)
      \ (Nat.primesLE a).filter (fun q : ℕ => q ≠ 2), oddFac q) ≤ 1 :=
    Finset.prod_le_one₀ (fun q hq => (oddFac01 (Finset.mem_sdiff.mp hq).1).1)
      (fun q hq => (oddFac01 (Finset.mem_sdiff.mp hq).1).2)
  nlinarith [h1, hnonneg]

/-- `oddSqProd` is antitone. -/
lemma oddSqProd_anti : Antitone oddSqProd := by
  intro a b hab
  unfold oddSqProd
  rw [← Finset.prod_sdiff (oddfilter_mono hab)]
  have hnonneg : 0 ≤ ∏ q ∈ (Nat.primesLE a).filter (fun q : ℕ => q ≠ 2), oddSqFac q :=
    Finset.prod_nonneg (fun q hq => (oddSqFac01 hq).1)
  have h1 : (∏ q ∈ (Nat.primesLE b).filter (fun q : ℕ => q ≠ 2)
      \ (Nat.primesLE a).filter (fun q : ℕ => q ≠ 2), oddSqFac q) ≤ 1 :=
    Finset.prod_le_one₀ (fun q hq => (oddSqFac01 (Finset.mem_sdiff.mp hq).1).1)
      (fun q hq => (oddSqFac01 (Finset.mem_sdiff.mp hq).1).2)
  nlinarith [h1, hnonneg]

/-- Decomposition `oddProd n = 2 * primeProd n * oddSqProd n` for `n ≥ 2`. -/
lemma oddProd_decomp {n : ℕ} (hn : 2 ≤ n) :
    oddProd n = 2 * primeProd n * oddSqProd n := by
  have h2mem : 2 ∈ Nat.primesLE n := by rw [Nat.mem_primesLE]; exact ⟨hn, Nat.prime_two⟩
  have hfac : ∀ q ∈ (Nat.primesLE n).filter (fun q : ℕ => q ≠ 2),
      oddFac q = (1 - 1/(q:ℝ)) * oddSqFac q := by
    intro q hq
    have hp : Nat.Prime q := (Nat.mem_primesLE.mp (Finset.mem_filter.mp hq).1).2
    have hqne : q ≠ 2 := (Finset.mem_filter.mp hq).2
    have hq3 : 3 ≤ q := by have := hp.two_le; omega
    have hq3' : (3:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq3
    have hq0 : (q:ℝ) ≠ 0 := by positivity
    have hq1 : (q:ℝ) - 1 ≠ 0 := by linarith
    unfold oddFac oddSqFac
    field_simp
    ring
  unfold oddProd primeProd oddSqProd
  rw [Finset.prod_congr rfl hfac, Finset.prod_mul_distrib]
  have herase := Finset.mul_prod_erase (Nat.primesLE n) (fun q : ℕ => (1 - 1/(q:ℝ))) h2mem
  have h2val : (1 - 1/((2:ℕ):ℝ)) = (1/2 : ℝ) := by norm_num
  rw [h2val] at herase
  have hQ : (∏ q ∈ (Nat.primesLE n).erase 2, (1 - 1/(q:ℝ)))
      = 2 * ∏ q ∈ Nat.primesLE n, (1 - 1/(q:ℝ)) := by linarith [herase]
  have hset : (Nat.primesLE n).erase 2 = (Nat.primesLE n).filter (fun q : ℕ => q ≠ 2) := by
    ext q
    rw [Finset.mem_erase, Finset.mem_filter]
    exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  rw [hset] at hQ
  rw [hQ]

/-! ## Evaluation of products over explicit finsets -/

/-- `log m ≤ k log 2 - (2^k - m)/2^k` when `1 ≤ m ≤ 2^k`. -/
lemma log_le_klog2 (m k : ℕ) (hm : 1 ≤ m) (hk : m ≤ 2^k) :
    Real.log (m:ℝ) ≤ k * Real.log 2 - (((2:ℝ)^k - (m:ℝ)) / (2:ℝ)^k) := by
  have h2 : (0:ℝ) < (2:ℝ)^k := by positivity
  have hm0 : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
  have hr : (0:ℝ) < (m:ℝ)/(2:ℝ)^k := div_pos hm0 h2
  have h1 : Real.log ((m:ℝ)/(2:ℝ)^k) ≤ (m:ℝ)/(2:ℝ)^k - 1 := Real.log_le_sub_one_of_pos hr
  have h2log : Real.log ((2:ℝ)^k) = k * Real.log 2 := by rw [Real.log_pow]
  have hsplit : Real.log (m:ℝ) = Real.log ((2:ℝ)^k) + Real.log ((m:ℝ)/(2:ℝ)^k) := by
    rw [← Real.log_mul (ne_of_gt h2) (ne_of_gt hr)]
    congr 1; field_simp
  rw [hsplit, h2log]
  have hh : (((2:ℝ)^k - (m:ℝ)) / (2:ℝ)^k) = 1 - (m:ℝ)/(2:ℝ)^k := by field_simp
  rw [hh]; linarith

private lemma oddFac_eq {q : ℕ} (hq : 2 ≤ q) : oddFac q = ((q:ℝ)-2)/((q:ℝ)-1) := by
  have hq2 : (2:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
  have hne : (q:ℝ) - 1 ≠ 0 := by linarith
  unfold oddFac
  field_simp
  ring

private lemma oddSqFac_eq {q : ℕ} (hq : 2 ≤ q) :
    oddSqFac q = ((q:ℝ)*((q:ℝ)-2))/(((q:ℝ)-1)^2) := by
  have hq2 : (2:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
  have hne : (q:ℝ) - 1 ≠ 0 := by linarith
  unfold oddSqFac
  field_simp
  ring

/-- If `q * ∏(x-2) ≤ p * ∏(x-1)` then `∏ (1 - 1/(x-1)) ≤ p/q`. -/
private lemma lit_oddFac_le (L : Finset ℕ) (h2 : ∀ x ∈ L, 2 ≤ x) (p q : ℕ) (hq : 0 < q)
    (h : q * (∏ x ∈ L, (x - 2)) ≤ p * (∏ x ∈ L, (x - 1))) :
    (∏ x ∈ L, oddFac x) ≤ (p:ℝ)/(q:ℝ) := by
  set N : ℕ := ∏ x ∈ L, (x - 2) with hN
  set D : ℕ := ∏ x ∈ L, (x - 1) with hD
  have hND : q * N ≤ p * D := by rw [hN, hD]; exact h
  have e2 : (∏ x ∈ L, ((x:ℝ)-2)) = (N:ℝ) := by
    rw [hN, Finset.prod_natCast (s := L) (f := fun x => x - 2) (R := ℝ)]
    exact Finset.prod_congr rfl (fun x hx => by rw [Nat.cast_sub (h2 x hx)]; norm_num)
  have e1 : (∏ x ∈ L, ((x:ℝ)-1)) = (D:ℝ) := by
    rw [hD, Finset.prod_natCast (s := L) (f := fun x => x - 1) (R := ℝ)]
    exact Finset.prod_congr rfl (fun x hx => by
      rw [Nat.cast_sub (by have := h2 x hx; omega : 1 ≤ x)]; norm_num)
  have hfac : (∏ x ∈ L, oddFac x) = (∏ x ∈ L, ((x:ℝ)-2)) / (∏ x ∈ L, ((x:ℝ)-1)) := by
    have h1 : (∏ x ∈ L, oddFac x) = ∏ x ∈ L, ((x:ℝ)-2)/((x:ℝ)-1) :=
      Finset.prod_congr rfl (fun x hx => oddFac_eq (h2 x hx))
    rw [h1, Finset.prod_div_distrib]
  have hDpos : (0:ℝ) < (D:ℝ) := by
    rw [hD]; exact_mod_cast Finset.prod_pos (fun x hx => by have := h2 x hx; omega)
  have hqpos : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  rw [hfac, e2, e1]
  rw [div_le_div_iff₀ hDpos hqpos]
  have h' : ((q * N : ℕ) : ℝ) ≤ ((p * D : ℕ) : ℝ) := by exact_mod_cast hND
  push_cast at h'
  nlinarith [h']

/-- If `q * ∏(x*(x-2)) ≤ p * ∏(x-1)^2` then `∏ (1 - 1/(x-1)^2) ≤ p/q`. -/
private lemma lit_oddSqFac_le (L : Finset ℕ) (h2 : ∀ x ∈ L, 2 ≤ x) (p q : ℕ) (hq : 0 < q)
    (h : q * (∏ x ∈ L, (x * (x - 2))) ≤ p * (∏ x ∈ L, ((x - 1)^2))) :
    (∏ x ∈ L, oddSqFac x) ≤ (p:ℝ)/(q:ℝ) := by
  set N : ℕ := ∏ x ∈ L, (x * (x - 2)) with hN
  set D : ℕ := ∏ x ∈ L, ((x - 1)^2) with hD
  have hND : q * N ≤ p * D := by rw [hN, hD]; exact h
  have e2 : (∏ x ∈ L, ((x:ℝ)*((x:ℝ)-2))) = (N:ℝ) := by
    rw [hN, Finset.prod_natCast (s := L) (f := fun x => x * (x - 2)) (R := ℝ)]
    exact Finset.prod_congr rfl (fun x hx => by
      rw [Nat.cast_mul, Nat.cast_sub (h2 x hx)]; norm_num)
  have e1 : (∏ x ∈ L, (((x:ℝ)-1)^2)) = (D:ℝ) := by
    rw [hD, Finset.prod_natCast (s := L) (f := fun x => (x - 1)^2) (R := ℝ)]
    exact Finset.prod_congr rfl (fun x hx => by
      rw [Nat.cast_pow, Nat.cast_sub (by have := h2 x hx; omega : 1 ≤ x)]; norm_num)
  have hfac : (∏ x ∈ L, oddSqFac x)
      = (∏ x ∈ L, ((x:ℝ)*((x:ℝ)-2))) / (∏ x ∈ L, (((x:ℝ)-1)^2)) := by
    have h1 : (∏ x ∈ L, oddSqFac x) = ∏ x ∈ L, ((x:ℝ)*((x:ℝ)-2))/(((x:ℝ)-1)^2) :=
      Finset.prod_congr rfl (fun x hx => oddSqFac_eq (h2 x hx))
    rw [h1, Finset.prod_div_distrib]
  have hDpos : (0:ℝ) < (D:ℝ) := by
    rw [hD]; exact_mod_cast Finset.prod_pos (fun x hx =>
      pow_pos (Nat.sub_pos_of_lt (by have := h2 x hx; omega : 1 < x)) 2)
  have hqpos : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  rw [hfac, e2, e1]
  rw [div_le_div_iff₀ hDpos hqpos]
  have h' : ((q * N : ℕ) : ℝ) ≤ ((p * D : ℕ) : ℝ) := by exact_mod_cast hND
  push_cast at h'
  nlinarith [h']

/-- If `p * ∏(x-1)^2 ≤ q * ∏(x*(x-2))` then `p/q ≤ ∏ (1 - 1/(x-1)^2)`. -/
private lemma lit_oddSqFac_ge (L : Finset ℕ) (h2 : ∀ x ∈ L, 2 ≤ x) (p q : ℕ) (hq : 0 < q)
    (h : p * (∏ x ∈ L, ((x - 1)^2)) ≤ q * (∏ x ∈ L, (x * (x - 2)))) :
    (p:ℝ)/(q:ℝ) ≤ (∏ x ∈ L, oddSqFac x) := by
  set N : ℕ := ∏ x ∈ L, (x * (x - 2)) with hN
  set D : ℕ := ∏ x ∈ L, ((x - 1)^2) with hD
  have hND : p * D ≤ q * N := by rw [hN, hD]; exact h
  have e2 : (∏ x ∈ L, ((x:ℝ)*((x:ℝ)-2))) = (N:ℝ) := by
    rw [hN, Finset.prod_natCast (s := L) (f := fun x => x * (x - 2)) (R := ℝ)]
    exact Finset.prod_congr rfl (fun x hx => by
      rw [Nat.cast_mul, Nat.cast_sub (h2 x hx)]; norm_num)
  have e1 : (∏ x ∈ L, (((x:ℝ)-1)^2)) = (D:ℝ) := by
    rw [hD, Finset.prod_natCast (s := L) (f := fun x => (x - 1)^2) (R := ℝ)]
    exact Finset.prod_congr rfl (fun x hx => by
      rw [Nat.cast_pow, Nat.cast_sub (by have := h2 x hx; omega : 1 ≤ x)]; norm_num)
  have hfac : (∏ x ∈ L, oddSqFac x)
      = (∏ x ∈ L, ((x:ℝ)*((x:ℝ)-2))) / (∏ x ∈ L, (((x:ℝ)-1)^2)) := by
    have h1 : (∏ x ∈ L, oddSqFac x) = ∏ x ∈ L, ((x:ℝ)*((x:ℝ)-2))/(((x:ℝ)-1)^2) :=
      Finset.prod_congr rfl (fun x hx => oddSqFac_eq (h2 x hx))
    rw [h1, Finset.prod_div_distrib]
  have hDpos : (0:ℝ) < (D:ℝ) := by
    rw [hD]; exact_mod_cast Finset.prod_pos (fun x hx =>
      pow_pos (Nat.sub_pos_of_lt (by have := h2 x hx; omega : 1 < x)) 2)
  have hqpos : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  rw [hfac, e2, e1]
  rw [div_le_div_iff₀ hqpos hDpos]
  have h' : ((p * D : ℕ) : ℝ) ≤ ((q * N : ℕ) : ℝ) := by exact_mod_cast hND
  push_cast at h'
  nlinarith [h']

/-- A segment of the explicit product bound for `oddProd`. -/
private lemma oddProd_seg (B bmax : ℕ) (r : ℝ) (k : ℕ) (hr0 : 0 ≤ r)
    (hr : oddProd B ≤ r) (hk : bmax + 1 ≤ 2^k)
    (hb : r * (k * Real.log 2 - (((2:ℝ)^k - ((bmax:ℝ)+1)) / (2:ℝ)^k)) ≤ 0.879) :
    ∀ n : ℕ, B ≤ n → n ≤ bmax → oddProd n * Real.log ((n:ℝ)+1) ≤ 0.879 := by
  intro n hBn hnb
  have hop : oddProd n ≤ r := le_trans (oddProd_anti hBn) hr
  have hn1 : 1 ≤ n + 1 := by omega
  have hm : n + 1 ≤ 2^k := by omega
  have hlog : Real.log ((n:ℝ)+1) ≤ k * Real.log 2 - (((2:ℝ)^k - ((n:ℝ)+1)) / (2:ℝ)^k) := by
    have h := log_le_klog2 (n+1) k hn1 hm
    push_cast at h ⊢
    convert h using 3 <;> ring
  have hnb' : (n:ℝ) ≤ (bmax:ℝ) := by exact_mod_cast hnb
  have hmono : (((2:ℝ)^k - ((bmax:ℝ)+1)) / (2:ℝ)^k) ≤ (((2:ℝ)^k - ((n:ℝ)+1)) / (2:ℝ)^k) := by
    rw [div_le_div_iff_of_pos_right (by positivity : (0:ℝ) < (2:ℝ)^k)]
    push_cast
    linarith
  have hlog' : Real.log ((n:ℝ)+1) ≤ k * Real.log 2 - (((2:ℝ)^k - ((bmax:ℝ)+1)) / (2:ℝ)^k) := by
    linarith
  have hlogpos : 0 ≤ Real.log ((n:ℝ)+1) := Real.log_nonneg (by have : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n; linarith)
  calc oddProd n * Real.log ((n:ℝ)+1)
      ≤ r * (k * Real.log 2 - (((2:ℝ)^k - ((bmax:ℝ)+1)) / (2:ℝ)^k)) :=
        mul_le_mul hop hlog' hlogpos hr0
    _ ≤ 0.879 := hb

private def seg00L : Finset ℕ := ({3} : Finset ℕ)

private lemma seg00sub : seg00L ⊆ (Nat.primesLE 4).filter (fun q : ℕ => q ≠ 2) := by
  intro x hx
  fin_cases hx <;> simp only [Finset.mem_filter, Nat.mem_primesLE] <;> norm_num

private lemma seg00r : oddProd 4 ≤ ((1:ℕ):ℝ)/((2:ℕ):ℝ) := by
  have hle : oddProd 4 ≤ (∏ x ∈ seg00L, oddFac x) := by
    simp only [oddProd]
    exact Finset.prod_le_prod_of_subset_of_le_one₀ seg00sub
      (fun x hx => (oddFac01 hx).1) (fun x hx _ => (oddFac01 hx).2)
  exact le_trans hle (lit_oddFac_le seg00L (fun x hx => by fin_cases hx <;> norm_num) 1 2 (by norm_num) (by decide))

private lemma seg00 : ∀ n : ℕ, 4 ≤ n → n ≤ 4 →
    oddProd n * Real.log ((n:ℝ)+1) ≤ 0.879 := by
  have hpq : ((1:ℕ):ℝ)/((2:ℕ):ℝ) = (1:ℝ)/(2:ℝ) := by norm_num
  refine oddProd_seg 4 4 (((1:ℕ):ℝ)/((2:ℕ):ℝ)) 3 (by norm_num) seg00r (by norm_num) ?_
  rw [hpq]
  nlinarith [Real.log_two_lt_d9]

private def seg01L : Finset ℕ := ({3,5} : Finset ℕ)

private lemma seg01sub : seg01L ⊆ (Nat.primesLE 5).filter (fun q : ℕ => q ≠ 2) := by
  intro x hx
  fin_cases hx <;> simp only [Finset.mem_filter, Nat.mem_primesLE] <;> norm_num

private lemma seg01r : oddProd 5 ≤ ((3:ℕ):ℝ)/((8:ℕ):ℝ) := by
  have hle : oddProd 5 ≤ (∏ x ∈ seg01L, oddFac x) := by
    simp only [oddProd]
    exact Finset.prod_le_prod_of_subset_of_le_one₀ seg01sub
      (fun x hx => (oddFac01 hx).1) (fun x hx _ => (oddFac01 hx).2)
  exact le_trans hle (lit_oddFac_le seg01L (fun x hx => by fin_cases hx <;> norm_num) 3 8 (by norm_num) (by decide))

private lemma seg01 : ∀ n : ℕ, 5 ≤ n → n ≤ 8 →
    oddProd n * Real.log ((n:ℝ)+1) ≤ 0.879 := by
  have hpq : ((3:ℕ):ℝ)/((8:ℕ):ℝ) = (3:ℝ)/(8:ℝ) := by norm_num
  refine oddProd_seg 5 8 (((3:ℕ):ℝ)/((8:ℕ):ℝ)) 4 (by norm_num) seg01r (by norm_num) ?_
  rw [hpq]
  nlinarith [Real.log_two_lt_d9]

private def seg02L : Finset ℕ := ({3,5,7} : Finset ℕ)

private lemma seg02sub : seg02L ⊆ (Nat.primesLE 9).filter (fun q : ℕ => q ≠ 2) := by
  intro x hx
  fin_cases hx <;> simp only [Finset.mem_filter, Nat.mem_primesLE] <;> norm_num

private lemma seg02r : oddProd 9 ≤ ((5:ℕ):ℝ)/((16:ℕ):ℝ) := by
  have hle : oddProd 9 ≤ (∏ x ∈ seg02L, oddFac x) := by
    simp only [oddProd]
    exact Finset.prod_le_prod_of_subset_of_le_one₀ seg02sub
      (fun x hx => (oddFac01 hx).1) (fun x hx _ => (oddFac01 hx).2)
  exact le_trans hle (lit_oddFac_le seg02L (fun x hx => by fin_cases hx <;> norm_num) 5 16 (by norm_num) (by decide))

private lemma seg02 : ∀ n : ℕ, 9 ≤ n → n ≤ 15 →
    oddProd n * Real.log ((n:ℝ)+1) ≤ 0.879 := by
  have hpq : ((5:ℕ):ℝ)/((16:ℕ):ℝ) = (5:ℝ)/(16:ℝ) := by norm_num
  refine oddProd_seg 9 15 (((5:ℕ):ℝ)/((16:ℕ):ℝ)) 4 (by norm_num) seg02r (by norm_num) ?_
  rw [hpq]
  nlinarith [Real.log_two_lt_d9]

private def seg03L : Finset ℕ := ({3,5,7,11,13} : Finset ℕ)

private lemma seg03sub : seg03L ⊆ (Nat.primesLE 16).filter (fun q : ℕ => q ≠ 2) := by
  intro x hx
  fin_cases hx <;> simp only [Finset.mem_filter, Nat.mem_primesLE] <;> norm_num

private lemma seg03r : oddProd 16 ≤ ((257813:ℕ):ℝ)/((1000000:ℕ):ℝ) := by
  have hle : oddProd 16 ≤ (∏ x ∈ seg03L, oddFac x) := by
    simp only [oddProd]
    exact Finset.prod_le_prod_of_subset_of_le_one₀ seg03sub
      (fun x hx => (oddFac01 hx).1) (fun x hx _ => (oddFac01 hx).2)
  exact le_trans hle (lit_oddFac_le seg03L (fun x hx => by fin_cases hx <;> norm_num) 257813 1000000 (by norm_num) (by decide))

private lemma seg03 : ∀ n : ℕ, 16 ≤ n → n ≤ 29 →
    oddProd n * Real.log ((n:ℝ)+1) ≤ 0.879 := by
  have hpq : ((257813:ℕ):ℝ)/((1000000:ℕ):ℝ) = (257813:ℝ)/(1000000:ℝ) := by norm_num
  refine oddProd_seg 16 29 (((257813:ℕ):ℝ)/((1000000:ℕ):ℝ)) 5 (by norm_num) seg03r (by norm_num) ?_
  rw [hpq]
  nlinarith [Real.log_two_lt_d9]

private def seg04L : Finset ℕ := ({3,5,7,11,13,17,19,23,29} : Finset ℕ)

private lemma seg04sub : seg04L ⊆ (Nat.primesLE 30).filter (fun q : ℕ => q ≠ 2) := by
  intro x hx
  fin_cases hx <;> simp only [Finset.mem_filter, Nat.mem_primesLE] <;> norm_num

private lemma seg04r : oddProd 30 ≤ ((210114:ℕ):ℝ)/((1000000:ℕ):ℝ) := by
  have hle : oddProd 30 ≤ (∏ x ∈ seg04L, oddFac x) := by
    simp only [oddProd]
    exact Finset.prod_le_prod_of_subset_of_le_one₀ seg04sub
      (fun x hx => (oddFac01 hx).1) (fun x hx _ => (oddFac01 hx).2)
  exact le_trans hle (lit_oddFac_le seg04L (fun x hx => by fin_cases hx <;> norm_num) 210114 1000000 (by norm_num) (by decide))

private lemma seg04 : ∀ n : ℕ, 30 ≤ n → n ≤ 63 →
    oddProd n * Real.log ((n:ℝ)+1) ≤ 0.879 := by
  have hpq : ((210114:ℕ):ℝ)/((1000000:ℕ):ℝ) = (210114:ℝ)/(1000000:ℝ) := by norm_num
  refine oddProd_seg 30 63 (((210114:ℕ):ℝ)/((1000000:ℕ):ℝ)) 6 (by norm_num) seg04r (by norm_num) ?_
  rw [hpq]
  nlinarith [Real.log_two_lt_d9]

private def seg05L : Finset ℕ := ({3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61} : Finset ℕ)

private lemma seg05sub : seg05L ⊆ (Nat.primesLE 64).filter (fun q : ℕ => q ≠ 2) := by
  intro x hx
  fin_cases hx <;> simp only [Finset.mem_filter, Nat.mem_primesLE] <;> norm_num

private lemma seg05r : oddProd 64 ≤ ((174263:ℕ):ℝ)/((1000000:ℕ):ℝ) := by
  have hle : oddProd 64 ≤ (∏ x ∈ seg05L, oddFac x) := by
    simp only [oddProd]
    exact Finset.prod_le_prod_of_subset_of_le_one₀ seg05sub
      (fun x hx => (oddFac01 hx).1) (fun x hx _ => (oddFac01 hx).2)
  exact le_trans hle (lit_oddFac_le seg05L (fun x hx => by fin_cases hx <;> norm_num) 174263 1000000 (by norm_num) (by decide))

private lemma seg05 : ∀ n : ℕ, 64 ≤ n → n ≤ 127 →
    oddProd n * Real.log ((n:ℝ)+1) ≤ 0.879 := by
  have hpq : ((174263:ℕ):ℝ)/((1000000:ℕ):ℝ) = (174263:ℝ)/(1000000:ℝ) := by norm_num
  refine oddProd_seg 64 127 (((174263:ℕ):ℝ)/((1000000:ℕ):ℝ)) 7 (by norm_num) seg05r (by norm_num) ?_
  rw [hpq]
  nlinarith [Real.log_two_lt_d9]

private def seg06L : Finset ℕ := ({3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127} : Finset ℕ)

private lemma seg06sub : seg06L ⊆ (Nat.primesLE 128).filter (fun q : ℕ => q ≠ 2) := by
  intro x hx
  fin_cases hx <;> simp only [Finset.mem_filter, Nat.mem_primesLE] <;> norm_num

private lemma seg06r : oddProd 128 ≤ ((150540:ℕ):ℝ)/((1000000:ℕ):ℝ) := by
  have hle : oddProd 128 ≤ (∏ x ∈ seg06L, oddFac x) := by
    simp only [oddProd]
    exact Finset.prod_le_prod_of_subset_of_le_one₀ seg06sub
      (fun x hx => (oddFac01 hx).1) (fun x hx _ => (oddFac01 hx).2)
  exact le_trans hle (lit_oddFac_le seg06L (fun x hx => by fin_cases hx <;> norm_num) 150540 1000000 (by norm_num) (by decide))

private lemma seg06 : ∀ n : ℕ, 128 ≤ n → n ≤ 135 →
    oddProd n * Real.log ((n:ℝ)+1) ≤ 0.879 := by
  have hpq : ((150540:ℕ):ℝ)/((1000000:ℕ):ℝ) = (150540:ℝ)/(1000000:ℝ) := by norm_num
  refine oddProd_seg 128 135 (((150540:ℕ):ℝ)/((1000000:ℕ):ℝ)) 8 (by norm_num) seg06r (by norm_num) ?_
  rw [hpq]
  nlinarith [Real.log_two_lt_d9]

private def seg07L : Finset ℕ := ({3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127,131} : Finset ℕ)

private lemma seg07sub : seg07L ⊆ (Nat.primesLE 136).filter (fun q : ℕ => q ≠ 2) := by
  intro x hx
  fin_cases hx <;> simp only [Finset.mem_filter, Nat.mem_primesLE] <;> norm_num

private lemma seg07r : oddProd 136 ≤ ((149382:ℕ):ℝ)/((1000000:ℕ):ℝ) := by
  have hle : oddProd 136 ≤ (∏ x ∈ seg07L, oddFac x) := by
    simp only [oddProd]
    exact Finset.prod_le_prod_of_subset_of_le_one₀ seg07sub
      (fun x hx => (oddFac01 hx).1) (fun x hx _ => (oddFac01 hx).2)
  exact le_trans hle (lit_oddFac_le seg07L (fun x hx => by fin_cases hx <;> norm_num) 149382 1000000 (by norm_num) (by decide))

private lemma seg07 : ∀ n : ℕ, 136 ≤ n → n ≤ 255 →
    oddProd n * Real.log ((n:ℝ)+1) ≤ 0.879 := by
  have hpq : ((149382:ℕ):ℝ)/((1000000:ℕ):ℝ) = (149382:ℝ)/(1000000:ℝ) := by norm_num
  refine oddProd_seg 136 255 (((149382:ℕ):ℝ)/((1000000:ℕ):ℝ)) 8 (by norm_num) seg07r (by norm_num) ?_
  rw [hpq]
  nlinarith [Real.log_two_lt_d9]

private def seg08L : Finset ℕ := ({3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127,131,137,139,149,151,157,163,167,173,179,181,191,193,197,199,211,223,227,229,233,239,241,251} : Finset ℕ)

private lemma seg08sub : seg08L ⊆ (Nat.primesLE 256).filter (fun q : ℕ => q ≠ 2) := by
  intro x hx
  fin_cases hx <;> simp only [Finset.mem_filter, Nat.mem_primesLE] <;> norm_num

private lemma seg08r : oddProd 256 ≤ ((132579:ℕ):ℝ)/((1000000:ℕ):ℝ) := by
  have hle : oddProd 256 ≤ (∏ x ∈ seg08L, oddFac x) := by
    simp only [oddProd]
    exact Finset.prod_le_prod_of_subset_of_le_one₀ seg08sub
      (fun x hx => (oddFac01 hx).1) (fun x hx _ => (oddFac01 hx).2)
  exact le_trans hle (lit_oddFac_le seg08L (fun x hx => by fin_cases hx <;> norm_num) 132579 1000000 (by norm_num) (by decide))

private lemma seg08 : ∀ n : ℕ, 256 ≤ n → n ≤ 350 →
    oddProd n * Real.log ((n:ℝ)+1) ≤ 0.879 := by
  have hpq : ((132579:ℕ):ℝ)/((1000000:ℕ):ℝ) = (132579:ℝ)/(1000000:ℝ) := by norm_num
  refine oddProd_seg 256 350 (((132579:ℕ):ℝ)/((1000000:ℕ):ℝ)) 9 (by norm_num) seg08r (by norm_num) ?_
  rw [hpq]
  nlinarith [Real.log_two_lt_d9]

private def seg09L : Finset ℕ := ({3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127,131,137,139,149,151,157,163,167,173,179,181,191,193,197,199,211,223,227,229,233,239,241,251,257,263,269,271,277,281,283,293,307,311,313,317,331,337,347,349} : Finset ℕ)

private lemma seg09sub : seg09L ⊆ (Nat.primesLE 351).filter (fun q : ℕ => q ≠ 2) := by
  intro x hx
  fin_cases hx <;> simp only [Finset.mem_filter, Nat.mem_primesLE] <;> norm_num

private lemma seg09r : oddProd 351 ≤ ((125603:ℕ):ℝ)/((1000000:ℕ):ℝ) := by
  have hle : oddProd 351 ≤ (∏ x ∈ seg09L, oddFac x) := by
    simp only [oddProd]
    exact Finset.prod_le_prod_of_subset_of_le_one₀ seg09sub
      (fun x hx => (oddFac01 hx).1) (fun x hx _ => (oddFac01 hx).2)
  exact le_trans hle (lit_oddFac_le seg09L (fun x hx => by fin_cases hx <;> norm_num) 125603 1000000 (by norm_num) (by decide))

private lemma seg09 : ∀ n : ℕ, 351 ≤ n → n ≤ 1023 →
    oddProd n * Real.log ((n:ℝ)+1) ≤ 0.879 := by
  have hpq : ((125603:ℕ):ℝ)/((1000000:ℕ):ℝ) = (125603:ℝ)/(1000000:ℝ) := by norm_num
  refine oddProd_seg 351 1023 (((125603:ℕ):ℝ)/((1000000:ℕ):ℝ)) 10 (by norm_num) seg09r (by norm_num) ?_
  rw [hpq]
  nlinarith [Real.log_two_lt_d9]

private def seg10L : Finset ℕ := ({3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127,131,137,139,149,151,157,163,167,173,179,181,191,193,197,199,211,223,227,229,233,239,241,251,257,263,269,271,277,281,283,293,307,311,313,317,331,337,347,349,353,359,367,373,379,383,389,397,401,409,419,421,431,433,439,443,449,457,461,463,467,479,487,491,499,503,509,521,523,541,547,557,563,569,571,577,587,593,599,601,607,613,617,619,631,641,643,647,653,659,661,673,677,683,691,701,709,719,727,733,739,743,751,757,761,769,773,787,797,809,811,821,823,827,829,839,853,857,859,863,877,881,883,887,907,911,919,929,937,941,947,953,967,971,977,983,991,997,1009,1013,1019,1021} : Finset ℕ)

private lemma seg10sub : seg10L ⊆ (Nat.primesLE 1024).filter (fun q : ℕ => q ≠ 2) := by
  intro x hx
  fin_cases hx <;> simp only [Finset.mem_filter, Nat.mem_primesLE] <;> norm_num

private lemma seg10r : oddProd 1024 ≤ ((106494:ℕ):ℝ)/((1000000:ℕ):ℝ) := by
  have hle : oddProd 1024 ≤ (∏ x ∈ seg10L, oddFac x) := by
    simp only [oddProd]
    exact Finset.prod_le_prod_of_subset_of_le_one₀ seg10sub
      (fun x hx => (oddFac01 hx).1) (fun x hx _ => (oddFac01 hx).2)
  exact le_trans hle (lit_oddFac_le seg10L (fun x hx => by fin_cases hx <;> norm_num) 106494 1000000 (by norm_num) (by decide))

private lemma seg10 : ∀ n : ℕ, 1024 ≤ n → n ≤ 2047 →
    oddProd n * Real.log ((n:ℝ)+1) ≤ 0.879 := by
  have hpq : ((106494:ℕ):ℝ)/((1000000:ℕ):ℝ) = (106494:ℝ)/(1000000:ℝ) := by norm_num
  refine oddProd_seg 1024 2047 (((106494:ℕ):ℝ)/((1000000:ℕ):ℝ)) 11 (by norm_num) seg10r (by norm_num) ?_
  rw [hpq]
  nlinarith [Real.log_two_lt_d9]

private def seg11L : Finset ℕ := ({3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127,131,137,139,149,151,157,163,167,173,179,181,191,193,197,199,211,223,227,229,233,239,241,251,257,263,269,271,277,281,283,293,307,311,313,317,331,337,347,349,353,359,367,373,379,383,389,397,401,409,419,421,431,433,439,443,449,457,461,463,467,479,487,491,499,503,509,521,523,541,547,557,563,569,571,577,587,593,599,601,607,613,617,619,631,641,643,647,653,659,661,673,677,683,691,701,709,719,727,733,739,743,751,757,761,769,773,787,797,809,811,821,823,827,829,839,853,857,859,863,877,881,883,887,907,911,919,929,937,941,947,953,967,971,977,983,991,997,1009,1013,1019,1021,1031,1033,1039,1049,1051,1061,1063,1069,1087,1091,1093,1097,1103,1109,1117,1123,1129,1151,1153,1163,1171,1181,1187,1193,1201,1213,1217,1223,1229,1231,1237,1249,1259,1277,1279,1283,1289,1291,1297,1301,1303,1307,1319,1321,1327,1361,1367,1373,1381,1399,1409,1423,1427,1429,1433,1439,1447,1451,1453,1459,1471,1481,1483,1487,1489,1493,1499,1511,1523,1531,1543,1549,1553,1559,1567,1571,1579,1583,1597,1601,1607,1609,1613,1619,1621,1627,1637,1657,1663,1667,1669,1693,1697,1699,1709,1721,1723,1733,1741,1747,1753,1759,1777,1783,1787,1789,1801,1811,1823,1831,1847,1861,1867,1871,1873,1877,1879,1889,1901,1907,1913,1931,1933,1949,1951,1973,1979,1987,1993,1997,1999,2003,2011,2017,2027,2029,2039} : Finset ℕ)

private lemma seg11sub : seg11L ⊆ (Nat.primesLE 2048).filter (fun q : ℕ => q ≠ 2) := by
  intro x hx
  fin_cases hx <;> simp only [Finset.mem_filter, Nat.mem_primesLE] <;> norm_num

private lemma seg11r : oddProd 2048 ≤ ((975:ℕ):ℝ)/((10000:ℕ):ℝ) := by
  have hle : oddProd 2048 ≤ (∏ x ∈ seg11L, oddFac x) := by
    simp only [oddProd]
    exact Finset.prod_le_prod_of_subset_of_le_one₀ seg11sub
      (fun x hx => (oddFac01 hx).1) (fun x hx _ => (oddFac01 hx).2)
  exact le_trans hle (lit_oddFac_le seg11L (fun x hx => by fin_cases hx <;> norm_num) 975 10000 (by norm_num) (by decide))

private lemma seg11 : ∀ n : ℕ, 2048 ≤ n → n ≤ 8191 →
    oddProd n * Real.log ((n:ℝ)+1) ≤ 0.879 := by
  have hpq : ((975:ℕ):ℝ)/((10000:ℕ):ℝ) = (975:ℝ)/(10000:ℝ) := by norm_num
  refine oddProd_seg 2048 8191 (((975:ℕ):ℝ)/((10000:ℕ):ℝ)) 13 (by norm_num) seg11r (by norm_num) ?_
  rw [hpq]
  nlinarith [Real.log_two_lt_d9]

/-- `oddProd n * log (n+1) ≤ 0.879` for `4 ≤ n ≤ 8191`. -/
lemma oddProd_small (n : ℕ) (h4 : 4 ≤ n) (hn : n ≤ 8191) :
    oddProd n * Real.log ((n:ℝ)+1) ≤ 0.879 := by
  by_cases h : n ≤ 4; · exact seg00 n h4 h
  have h5 : 5 ≤ n := by omega
  by_cases h : n ≤ 8; · exact seg01 n h5 h
  have h9 : 9 ≤ n := by omega
  by_cases h : n ≤ 15; · exact seg02 n h9 h
  have h16 : 16 ≤ n := by omega
  by_cases h : n ≤ 29; · exact seg03 n h16 h
  have h30 : 30 ≤ n := by omega
  by_cases h : n ≤ 63; · exact seg04 n h30 h
  have h64 : 64 ≤ n := by omega
  by_cases h : n ≤ 127; · exact seg05 n h64 h
  have h128 : 128 ≤ n := by omega
  by_cases h : n ≤ 135; · exact seg06 n h128 h
  have h136 : 136 ≤ n := by omega
  by_cases h : n ≤ 255; · exact seg07 n h136 h
  have h256 : 256 ≤ n := by omega
  by_cases h : n ≤ 350; · exact seg08 n h256 h
  have h351 : 351 ≤ n := by omega
  by_cases h : n ≤ 1023; · exact seg09 n h351 h
  have h1024 : 1024 ≤ n := by omega
  by_cases h : n ≤ 2047; · exact seg10 n h1024 h
  have h2048 : 2048 ≤ n := by omega
  exact seg11 n h2048 hn

private def sqL : Finset ℕ := ({3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127,131,137,139,149,151,157,163,167,173,179,181,191,193,197,199} : Finset ℕ)

private lemma sqLeq : sqL = (Nat.primesLE 200).filter (fun q : ℕ => q ≠ 2) := by decide

private lemma sqF : oddSqProd 200 = ∏ x ∈ sqL, oddSqFac x := by
  rw [oddSqProd, ← sqLeq]

/-- `0.6606 ≤ oddSqProd 200`. -/
lemma oddSqProd_200_ge : (0.6606:ℝ) ≤ oddSqProd 200 := by
  have h := lit_oddSqFac_ge sqL (fun x hx => by fin_cases hx <;> norm_num) 6606 10000 (by norm_num) (by decide)
  have hc : ((6606:ℕ):ℝ)/((10000:ℕ):ℝ) = (0.6606:ℝ) := by norm_num
  rw [sqF]
  linarith [h, hc.le, hc.ge]

/-- `oddSqProd 200 ≤ 0.6607`. -/
lemma oddSqProd_200_le : oddSqProd 200 ≤ (0.6607:ℝ) := by
  have h := lit_oddSqFac_le sqL (fun x hx => by fin_cases hx <;> norm_num) 6607 10000 (by norm_num) (by decide)
  have hc : ((6607:ℕ):ℝ)/((10000:ℕ):ℝ) = (0.6607:ℝ) := by norm_num
  rw [sqF]
  linarith [h, hc.le, hc.ge]

/-- Product lower bound for `∏(1 - x_i)`. -/
private lemma prod_one_sub_ge_one_sub_sum {s : Finset ℕ} {f : ℕ → ℝ}
    (h0 : ∀ i ∈ s, 0 ≤ f i) (h1 : ∀ i ∈ s, f i ≤ 1) :
    1 - ∑ i ∈ s, f i ≤ ∏ i ∈ s, (1 - f i) := by
  classical
  revert h0 h1
  refine Finset.induction_on s ?_ ?_
  · intro _ _; simp
  · intro a s has ih h0 h1
    rw [Finset.sum_insert has, Finset.prod_insert has]
    have h0' : ∀ i ∈ s, 0 ≤ f i := fun i hi => h0 i (Finset.mem_insert_of_mem hi)
    have h1' : ∀ i ∈ s, f i ≤ 1 := fun i hi => h1 i (Finset.mem_insert_of_mem hi)
    have hs := ih h0' h1'
    have ha0 : 0 ≤ f a := h0 a (Finset.mem_insert_self a s)
    have hsum_nonneg : 0 ≤ ∑ i ∈ s, f i := Finset.sum_nonneg h0'
    have hfa : 0 ≤ 1 - f a := by have := h1 a (Finset.mem_insert_self a s); linarith
    calc 1 - (f a + ∑ i ∈ s, f i)
        = (1 - f a) * (1 - ∑ i ∈ s, f i) - f a * ∑ i ∈ s, f i := by ring
      _ ≤ (1 - f a) * (1 - ∑ i ∈ s, f i) := by
          have : 0 ≤ f a * ∑ i ∈ s, f i := mul_nonneg ha0 hsum_nonneg
          linarith
      _ ≤ (1 - f a) * ∏ i ∈ s, (1 - f i) := mul_le_mul_of_nonneg_left hs hfa

/-- Sharp tail bound `∑_{M<q≤n, q odd prime} 1/(q-1)² ≤ 1/(M-1)` for `M ≥ 2`. -/
private lemma sum_sdiff_pred_sq_le (n M : ℕ) (hM : 2 ≤ M) :
    (∑ q ∈ ((Nat.primesLE n).filter (fun q : ℕ => q ≠ 2)
        \ (Nat.primesLE M).filter (fun q : ℕ => q ≠ 2)), (1:ℝ)/((q:ℝ)-1)^2)
      ≤ 1 / (((M - 1 : ℕ)) : ℝ) := by
  set e := (Nat.primesLE n).filter (fun q : ℕ => q ≠ 2)
    \ (Nat.primesLE M).filter (fun q : ℕ => q ≠ 2) with he
  have hmem : ∀ q ∈ e, M < q ∧ q ≤ n ∧ Nat.Prime q ∧ q ≠ 2 := by
    intro q hq
    rw [he, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_filter] at hq
    obtain ⟨⟨hqn, hqne⟩, hMq⟩ := hq
    have hpn : Nat.Prime q := (Nat.mem_primesLE.mp hqn).2
    have hqlen : q ≤ n := (Nat.mem_primesLE.mp hqn).1
    have hMqq : ¬ (q ≤ M) := by
      intro hle
      exact hMq ⟨Nat.mem_primesLE.mpr ⟨hle, hpn⟩, hqne⟩
    exact ⟨by omega, hqlen, hpn, hqne⟩
  have hodd : ∀ q ∈ e, q = 2 * ((q - 1) / 2) + 1 := by
    intro q hq
    obtain ⟨-, -, hp, hne⟩ := hmem q hq
    obtain ⟨k, hk⟩ := hp.odd_of_ne_two hne
    omega
  have hinj : Set.InjOn (fun q : ℕ => (q - 1) / 2) (↑e : Set ℕ) := by
    intro x hx y hy hxy
    rw [Finset.mem_coe] at hx hy
    obtain ⟨-, -, hpx, hnex⟩ := hmem x hx
    obtain ⟨-, -, hpy, hney⟩ := hmem y hy
    obtain ⟨kx, hkx⟩ := hpx.odd_of_ne_two hnex
    obtain ⟨ky, hky⟩ := hpy.odd_of_ne_two hney
    have hxd : (x - 1) / 2 = kx := by omega
    have hyd : (y - 1) / 2 = ky := by omega
    change (x - 1) / 2 = (y - 1) / 2 at hxy
    rw [hxd, hyd] at hxy
    omega
  have hcongr : ∀ q ∈ e, (1:ℝ)/((q:ℝ)-1)^2 = 1 / ((2 * ((q-1)/2) : ℕ) : ℝ)^2 := by
    intro q hq
    have hq1 : 1 ≤ q := by have := (hmem q hq).1; omega
    have hoddq : q - 1 = 2 * ((q-1)/2) := by have := hodd q hq; omega
    have hcast : ((2 * ((q-1)/2) : ℕ) : ℝ) = (q:ℝ) - 1 := by
      have hmid : ((q:ℝ) - 1) = ((q - 1 : ℕ) : ℝ) := by rw [Nat.cast_sub hq1]; norm_num
      rw [hmid, ← hoddq]
    rw [hcast]
  rw [Finset.sum_congr rfl hcongr]
  rw [← Finset.sum_image (f := fun k : ℕ => 1 / ((2 * k : ℕ) : ℝ)^2) hinj]
  set t : Finset ℕ := e.image (fun q : ℕ => (q-1)/2) with ht
  have hsub : t ⊆ Finset.Ioo (M/2 - 1) n := by
    intro k hk
    rw [ht, Finset.mem_image] at hk
    obtain ⟨q, hq, rfl⟩ := hk
    rw [Finset.mem_Ioo]
    obtain ⟨hMq, hqn, -, -⟩ := hmem q hq
    have hoddq : q - 1 = 2 * ((q-1)/2) := by have := hodd q hq; omega
    constructor <;> omega
  have hstep : (∑ k ∈ t, 1 / ((2 * k : ℕ) : ℝ)^2)
      ≤ ∑ k ∈ Finset.Ioo (M/2 - 1) n, 1 / ((2 * k : ℕ) : ℝ)^2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => by positivity)
  have hsplit : ∀ k : ℕ, (1:ℝ) / ((2 * k : ℕ) : ℝ)^2 = (1/4) * (1/(k:ℝ)^2) := by
    intro k
    have hc : ((2 * k : ℕ) : ℝ) = 2 * (k:ℝ) := by push_cast; ring
    rw [hc]
    have hk4 : ((2:ℝ) * (k:ℝ))^2 = 4 * (k:ℝ)^2 := by ring
    rw [hk4]
    ring
  have hbound : (∑ k ∈ Finset.Ioo (M/2 - 1) n, 1 / ((2 * k : ℕ) : ℝ)^2) ≤ 1/(((M-1:ℕ)):ℝ) := by
    have h1 : (∑ k ∈ Finset.Ioo (M/2 - 1) n, 1 / ((2 * k : ℕ) : ℝ)^2)
        = (1/4) * ∑ k ∈ Finset.Ioo (M/2 - 1) n, 1/(k:ℝ)^2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun k _ => hsplit k)
    rw [h1]
    have h2 : (∑ k ∈ Finset.Ioo (M/2 - 1) n, 1/(k:ℝ)^2) ≤ 2 / (((M/2 - 1 : ℕ):ℝ) + 1) := by
      have h := sum_Ioo_inv_sq_le (α := ℝ) (M/2 - 1) n
      simpa [one_div] using h
    have hM2 : 1 ≤ M/2 := by omega
    have hcast : (((M/2 - 1 : ℕ):ℝ) + 1) = ((M/2 : ℕ):ℝ) := by
      rw [Nat.cast_sub hM2]; norm_num
    have hM1pos : (0:ℝ) < ((M-1 : ℕ):ℝ) := by
      have : (1:ℝ) ≤ ((M-1 : ℕ):ℝ) := by
        have h : 1 ≤ M-1 := by omega
        exact_mod_cast h
      linarith
    have hM2pos : (0:ℝ) < ((M/2 : ℕ):ℝ) := by
      have : (1:ℝ) ≤ ((M/2 : ℕ):ℝ) := by exact_mod_cast hM2
      linarith
    have hle : (2:ℝ) * ((M/2 : ℕ):ℝ) ≥ ((M-1 : ℕ):ℝ) := by
      have h1 : 2 * (M/2) ≥ M - 1 := by omega
      exact_mod_cast h1
    calc (1/4) * (∑ k ∈ Finset.Ioo (M/2 - 1) n, 1/(k:ℝ)^2)
        ≤ (1/4) * (2 / (((M/2 - 1 : ℕ):ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left h2 (by norm_num)
      _ = (1/4) * (2 / ((M/2 : ℕ):ℝ)) := by rw [hcast]
      _ ≤ 1/((M-1:ℕ):ℝ) := by
          have h2' : (2:ℝ) / ((M/2 : ℕ):ℝ) ≤ 4 / ((M-1:ℕ):ℝ) := by
            rw [div_le_div_iff₀ hM2pos hM1pos]
            nlinarith [hle]
          calc (1/4) * (2 / ((M/2 : ℕ):ℝ)) = (2 / ((M/2 : ℕ):ℝ)) / 4 := by ring
            _ ≤ (4 / ((M-1:ℕ):ℝ)) / 4 := div_le_div_of_nonneg_right h2' (by norm_num)
            _ = 1 / ((M-1:ℕ):ℝ) := by ring
  linarith [hstep, hbound]

/-- `oddSqProd n ≥ 0.6572` for all `n`. -/
lemma oddSqProd_ge (n : ℕ) : (0.6572:ℝ) ≤ oddSqProd n := by
  rcases lt_or_ge n 200 with hlt | hge
  · have h1 : oddSqProd 200 ≤ oddSqProd n := oddSqProd_anti (le_of_lt hlt)
    nlinarith [h1, oddSqProd_200_ge]
  · have hsub := oddfilter_mono hge
    have hsplit : oddSqProd n
        = (∏ q ∈ (Nat.primesLE n).filter (fun q : ℕ => q ≠ 2)
            \ (Nat.primesLE 200).filter (fun q : ℕ => q ≠ 2), oddSqFac q)
          * oddSqProd 200 := by
      simp only [oddSqProd]
      rw [← Finset.prod_sdiff hsub]
    rw [hsplit]
    set e := (Nat.primesLE n).filter (fun q : ℕ => q ≠ 2)
      \ (Nat.primesLE 200).filter (fun q : ℕ => q ≠ 2) with hed
    have hsub2 : e ⊆ (Nat.primesLE n).filter (fun q : ℕ => q ≠ 2) := by
      rw [hed]; exact Finset.sdiff_subset
    have h01 : ∀ q ∈ e, (0:ℝ) ≤ 1/((q:ℝ)-1)^2 ∧ (1:ℝ)/((q:ℝ)-1)^2 ≤ 1 := fun q hq => by
      have hsub' := hsub2 hq
      have hp : Nat.Prime q := (Nat.mem_primesLE.mp (Finset.mem_filter.mp hsub').1).2
      have hne : q ≠ 2 := (Finset.mem_filter.mp hsub').2
      have h3 : 3 ≤ q := by have := hp.two_le; omega
      have h3' : (3:ℝ) ≤ (q:ℝ) := by exact_mod_cast h3
      have hpos : 0 < (q:ℝ) - 1 := by linarith
      have h4 : (2:ℝ) ≤ (q:ℝ) - 1 := by linarith
      have hsq : (1:ℝ) ≤ ((q:ℝ)-1)^2 := by nlinarith
      exact ⟨by positivity, by rw [div_le_one (by positivity)]; nlinarith⟩
    have hprod := prod_one_sub_ge_one_sub_sum (s := e) (f := fun q => 1/((q:ℝ)-1)^2)
      (fun q hq => (h01 q hq).1) (fun q hq => (h01 q hq).2)
    have hsum : (∑ q ∈ e, 1/((q:ℝ)-1)^2) ≤ (1:ℝ)/199 := by
      rw [hed]
      have h := sum_sdiff_pred_sq_le n 200 (by norm_num)
      have hc : (1:ℝ)/(((199:ℕ)):ℝ) = (1:ℝ)/199 := by norm_num
      linarith [h, hc.le, hc.ge]
    have htail : (1:ℝ) - 1/199 ≤ ∏ q ∈ e, oddSqFac q := by
      have hcong : (∏ q ∈ e, oddSqFac q) = ∏ q ∈ e, (1 - 1/((q:ℝ)-1)^2) :=
        Finset.prod_congr rfl (fun q hq => rfl)
      rw [hcong]
      linarith [hprod, hsum]
    have hkey : (0.6572:ℝ) ≤ (∏ q ∈ e, oddSqFac q) * oddSqProd 200 := by
      have hb := oddSqProd_200_ge
      nlinarith [htail, hb]
    linarith [hkey]

/-- `oddSqProd n ≤ 0.6607` for `n ≥ 200`. -/
lemma oddSqProd_le (n : ℕ) (hn : 200 ≤ n) : oddSqProd n ≤ (0.6607:ℝ) :=
  le_trans (oddSqProd_anti hn) oddSqProd_200_le

/-! ## Sharp lower products and the rate bound -/

/-- Sharp Mertens lower bound for `primeProd`. -/
lemma primeProd_ge (n : ℕ) (hn : 100 ≤ n) :
    Real.exp (-Real.eulerMascheroniConstant) * Real.exp (-(3/2)/Real.log (n:ℝ)) / Real.log (n:ℝ)
      ≤ primeProd n := by
  have h := Commons.NumberTheory.Mertens.primeProduct_oneSubInv_ge_sharp n hn
  simpa only [primeProd, one_div] using h

lemma primeProd_pos (n : ℕ) : 0 < primeProd n := by
  unfold primeProd
  refine Finset.prod_pos ?_
  intro q hq
  have hp : Nat.Prime q := (Nat.mem_primesLE.mp hq).2
  have hq2 : (2:ℝ) ≤ (q:ℝ) := by exact_mod_cast hp.two_le
  have hlt : (1:ℝ)/(q:ℝ) < 1 := by rw [div_lt_one (by linarith)]; linarith
  linarith

/-- `primeProd n = exp (-logRatioSum n)`. -/
lemma primeProd_eq_exp (n : ℕ) :
    primeProd n = Real.exp (- Commons.NumberTheory.Mertens.logRatioSum (n:ℝ)) := by
  have hlog : Real.log (primeProd n) = - Commons.NumberTheory.Mertens.logRatioSum (n:ℝ) := by
    unfold primeProd Commons.NumberTheory.Mertens.logRatioSum
    rw [Nat.floor_natCast, Real.log_prod]
    · rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro q hq
      have hp : Nat.Prime q := (Nat.mem_primesLE.mp hq).2
      have hq2 : (2:ℝ) ≤ (q:ℝ) := by exact_mod_cast hp.two_le
      have h1 : 1 - 1/(q:ℝ) = (((q:ℝ)/((q:ℝ)-1))⁻¹) := by field_simp
      rw [h1, Real.log_inv]
    · intro q hq
      have hp : Nat.Prime q := (Nat.mem_primesLE.mp hq).2
      have hq2 : (2:ℝ) ≤ (q:ℝ) := by exact_mod_cast hp.two_le
      have hlt : (1:ℝ)/(q:ℝ) < 1 := by rw [div_lt_one (by linarith)]; linarith
      linarith
  rw [← hlog, Real.exp_log (primeProd_pos n)]

/-- Lower bound `oddProd z * log z ≥ 2 * 0.6572 * e^{-γ} * e^{-(3/2)/log z}`. -/
lemma oddProd_lower (z : ℕ) (hz : 100 ≤ z) :
    2 * (0.6572:ℝ) * Real.exp (-Real.eulerMascheroniConstant) * Real.exp (-(3/2)/Real.log (z:ℝ))
      ≤ oddProd z * Real.log (z:ℝ) := by
  have hz2 : 2 ≤ z := by omega
  have hlog : 0 < Real.log (z:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < z))
  have hp := primeProd_ge z hz
  have hs := oddSqProd_ge z
  have hspos : 0 ≤ oddSqProd z := oddSqProd_nonneg z
  have hprod : 2 * (Real.exp (-Real.eulerMascheroniConstant) * Real.exp (-(3/2)/Real.log (z:ℝ))
      / Real.log (z:ℝ)) * (0.6572:ℝ) ≤ 2 * primeProd z * oddSqProd z := by
    have h1 : (2:ℝ) * (Real.exp (-Real.eulerMascheroniConstant)
        * Real.exp (-(3/2)/Real.log (z:ℝ)) / Real.log (z:ℝ)) ≤ 2 * primeProd z :=
      mul_le_mul_of_nonneg_left hp (by norm_num)
    exact mul_le_mul h1 hs (by norm_num) (by have := primeProd_nonneg z; positivity)
  rw [oddProd_decomp hz2]
  have h2 := mul_le_mul_of_nonneg_right hprod hlog.le
  have heq : 2 * (Real.exp (-Real.eulerMascheroniConstant) * Real.exp (-(3/2)/Real.log (z:ℝ))
      / Real.log (z:ℝ)) * (0.6572:ℝ) * Real.log (z:ℝ)
      = 2 * (0.6572:ℝ) * Real.exp (-Real.eulerMascheroniConstant) * Real.exp (-(3/2)/Real.log (z:ℝ)) := by
    field_simp
  linarith [h2, heq.le, heq.ge]

/-- Rate bound for `oddProd`. -/
lemma oddProd_rate (n : ℕ) (hn : 2048 ≤ n) :
    oddProd n * Real.log ((n:ℝ)+1)
      ≤ (2 * (0.6607:ℝ) * Real.exp ((73/50)/Real.log (n:ℝ) + 8/(n:ℝ)) * (1 + 1/(n:ℝ)))
        * Real.exp (-Real.eulerMascheroniConstant) := by
  have h2 : 2 ≤ n := by omega
  have hn100 : 100 ≤ n := by omega
  have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hlog : 0 < Real.log (n:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hlog1 : (1:ℝ) < Real.log (n:ℝ) := by
    have h := Real.log_le_log (by norm_num : (0:ℝ) < 2048)
      (show (2048:ℝ) ≤ (n:ℝ) by exact_mod_cast (by omega : 2048 ≤ n))
    have h2' : Real.log (2048:ℝ) = 11 * Real.log 2 := by
      rw [show (2048:ℝ) = 2^11 by norm_num, Real.log_pow]; norm_num
    rw [h2'] at h
    linarith [h, Real.log_two_gt_d9]
  set E : ℝ := Real.exp (-Real.eulerMascheroniConstant) with hE
  set EA : ℝ := Real.exp ((73/50)/Real.log (n:ℝ) + 8/(n:ℝ)) with hEA
  have hp1 : primeProd n * Real.log (n:ℝ) ≤ E * EA := by
    rw [primeProd_eq_exp, show Real.log (n:ℝ) = Real.exp (Real.log (Real.log (n:ℝ)))
      by rw [Real.exp_log hlog]]
    rw [mul_comm, ← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
    have hG := Aux.my_logRatioSum_ge (n:ℝ) (by exact_mod_cast hn100)
    linarith [hG]
  have hlogn1 : Real.log ((n:ℝ)+1) ≤ Real.log (n:ℝ) * (1 + 1/(n:ℝ)) := by
    have hsplit : Real.log ((n:ℝ)+1) = Real.log (n:ℝ) + Real.log (1 + 1/(n:ℝ)) := by
      rw [show ((n:ℝ)+1) = (n:ℝ) * (1 + 1/(n:ℝ)) by field_simp]
      rw [Real.log_mul (ne_of_gt hnpos) (by positivity)]
    rw [hsplit]
    have hle : Real.log (1 + 1/(n:ℝ)) ≤ 1/(n:ℝ) := by
      have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 + 1/(n:ℝ) by positivity)
      linarith
    have hmul : (1:ℝ) * (1/(n:ℝ)) ≤ Real.log (n:ℝ) * (1/(n:ℝ)) :=
      mul_le_mul_of_nonneg_right hlog1.le (by positivity)
    nlinarith [hle, hmul]
  have hSp := oddSqProd_le n (by omega : 200 ≤ n)
  have hPP : 0 ≤ primeProd n := (primeProd_pos n).le
  have hSS : 0 ≤ oddSqProd n := oddSqProd_nonneg n
  have hpm : 0 ≤ 2 * primeProd n * oddSqProd n := by positivity
  have key : 2 * primeProd n * oddSqProd n * Real.log ((n:ℝ)+1)
      ≤ 2 * EA * (0.6607:ℝ) * (1 + 1/(n:ℝ)) * E := by
    have s1 : 2 * primeProd n * oddSqProd n * Real.log ((n:ℝ)+1)
        ≤ 2 * primeProd n * oddSqProd n * (Real.log (n:ℝ) * (1 + 1/(n:ℝ))) :=
      mul_le_mul_of_nonneg_left hlogn1 hpm
    have s2 : 2 * primeProd n * oddSqProd n * (Real.log (n:ℝ) * (1 + 1/(n:ℝ)))
        ≤ 2 * (E * EA) * (0.6607:ℝ) * (1 + 1/(n:ℝ)) := by
      have h2a : 2 * primeProd n * Real.log (n:ℝ) ≤ 2 * (E * EA) := by linarith [hp1]
      have hb : (2 * primeProd n * Real.log (n:ℝ)) * oddSqProd n
          ≤ (2 * (E * EA)) * (0.6607:ℝ) :=
        mul_le_mul h2a hSp hSS (by positivity)
      have := mul_le_mul_of_nonneg_right hb (by positivity : (0:ℝ) ≤ 1 + 1/(n:ℝ))
      nlinarith [this]
    have s3 : 2 * (E * EA) * (0.6607:ℝ) * (1 + 1/(n:ℝ))
        = 2 * EA * (0.6607:ℝ) * (1 + 1/(n:ℝ)) * E := by ring
    linarith [s1, s2, s3.le, s3.ge]
  rw [oddProd_decomp h2]
  refine le_trans key ?_
  rw [show (2 * (0.6607:ℝ) * Real.exp ((73/50)/Real.log (n:ℝ) + 8/(n:ℝ)) * (1 + 1/(n:ℝ)))
      * Real.exp (-Real.eulerMascheroniConstant)
      = 2 * EA * (0.6607:ℝ) * (1 + 1/(n:ℝ)) * E from by rw [hEA, hE]; ring]

/-! ## The target theorem -/

/-- **Chen's odd Euler product ratio bound.** -/
theorem oddEulerProduct_ratio_le_log_p5 :
    ∃ z₀ : ℕ, ∀ z : ℕ, z₀ ≤ z → ∀ p : ℕ, p.Prime → 5 ≤ p → p ≤ z →
      (∏ q ∈ (Nat.primesLE (p - 1)).filter (fun q : ℕ => q ≠ 2), (1 - (1 : ℝ) / ((q : ℝ) - 1)))
        ≤ (6 / 5) * (Real.log z / Real.log p) *
          (∏ q ∈ (Nat.primesLE z).filter (fun q : ℕ => q ≠ 2), (1 - (1 : ℝ) / ((q : ℝ) - 1))) := by
  refine ⟨2^10000, ?_⟩
  intro z hz p hpprime hp5 hpz
  have hz100 : 100 ≤ z := by
    have h1 : (100:ℕ) ≤ 2^10000 := by
      calc (100:ℕ) ≤ 2^7 := by norm_num
        _ ≤ 2^10000 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
    omega
  have hlogz : 0 < Real.log (z:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < z))
  have hlogzbig : (5000:ℝ) ≤ Real.log (z:ℝ) := by
    have h2 : Real.log (((2:ℕ)^10000 : ℕ):ℝ) ≤ Real.log (z:ℝ) :=
      Real.log_le_log (by positivity) (by exact_mod_cast hz)
    rw [show (((2:ℕ)^10000 : ℕ):ℝ) = (2:ℝ)^10000 by push_cast; ring, Real.log_pow] at h2
    push_cast at h2
    nlinarith [h2, Real.log_two_gt_d9]
  have hp1 : 1 ≤ p := by omega
  have hlogp : 0 < Real.log (p:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < p))
  change oddProd (p-1) ≤ (6/5) * (Real.log (z:ℝ) / Real.log (p:ℝ)) * oddProd z
  have hez : (0.9997:ℝ) ≤ Real.exp (-(3/2)/Real.log (z:ℝ)) := by
    have hle : (3/2)/Real.log (z:ℝ) ≤ (0.0003:ℝ) := by
      rw [div_le_iff₀ hlogz]; nlinarith
    rw [show -(3/2)/Real.log (z:ℝ) = -((3/2)/Real.log (z:ℝ)) by rw [neg_div]]
    have h1 : -(0.0003:ℝ) ≤ -((3/2)/Real.log (z:ℝ)) := by linarith
    have h2 := Real.exp_le_exp.mpr h1
    have h3 : (0.9997:ℝ) ≤ Real.exp (-(0.0003:ℝ)) := by
      have := Real.add_one_le_exp (-(0.0003:ℝ))
      linarith
    linarith [h2, h3]
  have hlow : 1.2 * 2 * (0.6572:ℝ) * Real.exp (-Real.eulerMascheroniConstant) * (0.9997:ℝ)
      ≤ (6/5) * (oddProd z * Real.log (z:ℝ)) := by
    have h := oddProd_lower z hz100
    have hEγ : 0 < Real.exp (-Real.eulerMascheroniConstant) := Real.exp_pos _
    nlinarith [h, hez, hEγ]
  rw [show (6/5) * (Real.log (z:ℝ) / Real.log (p:ℝ)) * oddProd z
      = (6/5) * (oddProd z * Real.log (z:ℝ)) / Real.log (p:ℝ) by field_simp]
  rw [le_div_iff₀ hlogp]
  rcases lt_or_ge (p-1) 8192 with hcase | hcase
  · have hn : p-1 ≤ 8191 := by omega
    have hsm := oddProd_small (p-1) (by omega) hn
    have hcast : (((p-1:ℕ):ℝ)+1) = (p:ℝ) := by rw [Nat.cast_sub hp1]; ring
    have hL : oddProd (p-1) * Real.log (p:ℝ) ≤ 0.879 := by
      have := hsm; rwa [hcast] at this
    have hγ : (0.56:ℝ) ≤ Real.exp (-Real.eulerMascheroniConstant) :=
      Commons.NumberTheory.Mertens.eulerMascheroni_exp_neg_lower
    have h872 : (0.879:ℝ) ≤ 1.2 * 2 * (0.6572:ℝ) * Real.exp (-Real.eulerMascheroniConstant) * (0.9997:ℝ) := by
      nlinarith [hγ]
    linarith [hL, h872, hlow]
  · have hn : 8192 ≤ p - 1 := hcase
    have hrate := oddProd_rate (p-1) (by omega : 2048 ≤ p-1)
    have hcast : (((p-1:ℕ):ℝ)+1) = (p:ℝ) := by rw [Nat.cast_sub hp1]; ring
    have hL : oddProd (p-1) * Real.log (p:ℝ)
        ≤ (2 * (0.6607:ℝ) * Real.exp ((73/50)/Real.log (((p-1:ℕ):ℝ)) + 8/(((p-1:ℕ):ℝ)))
            * (1 + 1/(((p-1:ℕ):ℝ))))
          * Real.exp (-Real.eulerMascheroniConstant) := by
      have := hrate; rwa [hcast] at this
    have hlogel : (9:ℝ) ≤ Real.log (((p-1:ℕ):ℝ)) := by
      have h2 : Real.log (8192:ℝ) ≤ Real.log (((p-1:ℕ):ℝ)) :=
        Real.log_le_log (by norm_num) (by exact_mod_cast (by omega : 8192 ≤ p-1))
      have h3 : Real.log (8192:ℝ) = 13 * Real.log 2 := by
        rw [show (8192:ℝ) = 2^13 by norm_num, Real.log_pow]; norm_num
      rw [h3] at h2
      nlinarith [h2, Real.log_two_gt_d9]
    have hA : Real.exp ((73/50)/Real.log (((p-1:ℕ):ℝ)) + 8/(((p-1:ℕ):ℝ))) ≤ 1.178 := by
      have h1 : (73/50)/Real.log (((p-1:ℕ):ℝ)) ≤ (73/50)/9 :=
        div_le_div_of_nonneg_left (by norm_num) (by norm_num) hlogel
      have h2 : 8/(((p-1:ℕ):ℝ)) ≤ 8/8192 :=
        div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by exact_mod_cast hn)
      have h3 : (73/50)/9 + 8/8192 ≤ Real.log 1.178 := by
        have h := Real.le_log_one_add_of_nonneg (x := (0.178:ℝ)) (by norm_num)
        norm_num at h ⊢
        linarith
      calc Real.exp ((73/50)/Real.log (((p-1:ℕ):ℝ)) + 8/(((p-1:ℕ):ℝ)))
          ≤ Real.exp (Real.log 1.178) := Real.exp_le_exp.mpr (by linarith)
        _ = 1.178 := Real.exp_log (by norm_num)
    have h1n : (1 + 1/(((p-1:ℕ):ℝ))) ≤ 1.00013 := by
      have : 1/(((p-1:ℕ):ℝ)) ≤ 1/8192 :=
        div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by exact_mod_cast hn)
      linarith
    have hEApos : 0 < Real.exp ((73/50)/Real.log (((p-1:ℕ):ℝ)) + 8/(((p-1:ℕ):ℝ))) := Real.exp_pos _
    have hcr : 2 * (0.6607:ℝ) * Real.exp ((73/50)/Real.log (((p-1:ℕ):ℝ)) + 8/(((p-1:ℕ):ℝ)))
        * (1 + 1/(((p-1:ℕ):ℝ))) ≤ 1.557 := by
      nlinarith [hA, h1n, hEApos]
    have hb1 : oddProd (p-1) * Real.log (p:ℝ)
        ≤ 1.557 * Real.exp (-Real.eulerMascheroniConstant) := by
      have hEpos : 0 < Real.exp (-Real.eulerMascheroniConstant) := Real.exp_pos _
      nlinarith [hL, hcr, hEpos]
    have hfin : 1.557 * Real.exp (-Real.eulerMascheroniConstant)
        ≤ 1.2 * 2 * (0.6572:ℝ) * Real.exp (-Real.eulerMascheroniConstant) * (0.9997:ℝ) := by
      have hEpos : 0 < Real.exp (-Real.eulerMascheroniConstant) := Real.exp_pos _
      nlinarith [hEpos]
    linarith [hb1, hfin, hlow]

end

end Commons.NumberTheory.Sieve
