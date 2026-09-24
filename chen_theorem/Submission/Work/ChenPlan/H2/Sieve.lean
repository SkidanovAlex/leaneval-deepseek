import Mathlib
import Submission.Work.ChenPlan.H2.Level
import Submission.Work.ChenPlan.H2.mertens_ratio_rate

/-!
# The upper linear sieve applied to the residue class `q`

Here we instantiate `Submission.ChenPlan.LinearSieveUpper` at the sieve problem `apSieve x M q`
of the residue class `q` (shifted primes `p ≤ x` with `q ∣ p+2`, sifting the odd primes `< M`,
density `ν = 1/φ`, total mass `x/φ(q)`, level `D/q` with `D = √x/(log x)^B`).
-/

open Finset Filter
open scoped BigOperators

namespace Work.ChenPlan.H2

noncomputable section

open Commons.NumberTheory.Chen.ChenEight

/-- Every prime factor of `oddPrimLt M` is `< M`. -/
lemma primeFactors_oddPrimLt_lt {p M : ℕ} (hp : p ∈ (oddPrimLt M).primeFactors) : p < M := by
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpd : p ∣ oddPrimLt M := Nat.dvd_of_mem_primeFactors hp
  exact primeFactor_lt_of_dvd_oddPrimLt (dvd_refl _) hpp hpd

/-- A divisor of `oddPrimLt M` is odd. -/
lemma odd_of_dvd_oddPrimLt {M d : ℕ} (h : d ∣ oddPrimLt M) : 2 ∣ d → False := by
  intro h2
  have h0 : oddPrimLt M % 2 = 0 := Nat.mod_eq_zero_of_dvd (dvd_trans h2 h)
  have h1 := oddPrimLt_odd M
  omega

/-- A divisor of `oddPrimLt M` is not even. -/
lemma not_two_dvd_oddPrimLt (M : ℕ) : ¬ (2 ∣ oddPrimLt M) := by
  intro h2
  have h0 : oddPrimLt M % 2 = 0 := Nat.mod_eq_zero_of_dvd h2
  have h1 := oddPrimLt_odd M
  omega

/-- The density factor at an odd prime. -/
lemma one_sub_invTotient_inv {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) :
    (1 - (Work.ChenPlan.H1.invTotient p))⁻¹ = ((p : ℝ) - 1) / ((p : ℝ) - 2) := by
  rw [Work.ChenPlan.H1.invTotient_apply, Nat.totient_prime hp,
    Nat.cast_sub (by have := hp.two_le; omega : 1 ≤ p)]
  push_cast
  have hp3 : 3 ≤ p := by
    have h2le : 2 ≤ p := hp.two_le
    rcases hp.eq_two_or_odd with h | h
    · exact absurd h h2
    · omega
  have hp3R : (3:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp3
  have h1 : (0:ℝ) < (p:ℝ) - 1 := by linarith
  have h2' : (0:ℝ) < (p:ℝ) - 2 := by linarith
  have hx : (1:ℝ) - ((p:ℝ) - 1)⁻¹ = ((p:ℝ) - 2) / ((p:ℝ) - 1) := by
    rw [inv_eq_one_div]
    field_simp
    ring
  rw [hx, inv_div]

/-- The sieve product is the product of `(p-1)/(p-2)` over the odd primes in `[w, M)`,
for `w ≥ 3`. -/
lemma prod_sieve_eq (M : ℕ) {w : ℝ} (hw : 3 ≤ w) :
    (∏ p ∈ (oddPrimLt M).primeFactors.filter (fun p : ℕ => w ≤ (p : ℝ)),
        (1 - (Work.ChenPlan.H1.invTotient p))⁻¹)
      = ∏ p ∈ (Finset.range M).filter (fun p : ℕ => p.Prime ∧ w ≤ (p : ℝ)),
          (((p : ℝ) - 1) / ((p : ℝ) - 2)) := by
  have hpf : (oddPrimLt M).primeFactors = oddLt M := by
    rw [oddPrimLt_eq_prod_oddLt]
    exact Nat.primeFactors_prod (fun p hp => (Submission.mem_oddLt.mp hp).1)
  rw [hpf]
  have hset : (oddLt M).filter (fun p : ℕ => w ≤ (p : ℝ))
      = (Finset.range M).filter (fun p : ℕ => p.Prime ∧ w ≤ (p : ℝ)) := by
    rw [show oddLt M = (Finset.range M).filter (fun p : ℕ => p.Prime ∧ 3 ≤ p) from rfl]
    rw [Finset.filter_filter]
    refine Finset.filter_congr (fun p _ => ?_)
    constructor
    · rintro ⟨⟨hp, h3p⟩, hwp⟩
      exact ⟨hp, hwp⟩
    · rintro ⟨hp, hwp⟩
      exact ⟨⟨hp, by exact_mod_cast (le_trans hw hwp)⟩, hwp⟩
  rw [hset]
  refine Finset.prod_congr rfl (fun p hp => ?_)
  rw [Finset.mem_filter] at hp
  obtain ⟨hpM, hpp, hwp⟩ := hp
  have hp2 : p ≠ 2 := by
    intro h
    have h2 : w ≤ (2:ℝ) := by
      calc w ≤ (p:ℝ) := hwp
        _ = 2 := by rw [h]; norm_num
    linarith
  exact one_sub_invTotient_inv hpp hp2

/-- For `2 ≤ w < 3` the sieve product is the full product over the odd primes `< M`. -/
lemma prod_sieve_eq_full (M : ℕ) {w : ℝ} (hw2 : 2 ≤ w) (hw3 : w < 3) :
    (∏ p ∈ (oddPrimLt M).primeFactors.filter (fun p : ℕ => w ≤ (p : ℝ)),
        (1 - (Work.ChenPlan.H1.invTotient p))⁻¹)
      = ∏ p ∈ (Finset.range M).filter (fun p : ℕ => p.Prime ∧ (3 : ℝ) ≤ (p : ℝ)),
          (((p : ℝ) - 1) / ((p : ℝ) - 2)) := by
  have h : (∏ p ∈ (oddPrimLt M).primeFactors.filter (fun p : ℕ => w ≤ (p : ℝ)),
        (1 - (Work.ChenPlan.H1.invTotient p))⁻¹)
      = ∏ p ∈ (oddPrimLt M).primeFactors.filter (fun p : ℕ => (3 : ℝ) ≤ (p : ℝ)),
          (1 - (Work.ChenPlan.H1.invTotient p))⁻¹ := by
    refine Finset.prod_congr ?_ (fun p _ => rfl)
    refine Finset.filter_congr (fun p hp => ?_)
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpd : p ∣ oddPrimLt M := Nat.dvd_of_mem_primeFactors hp
    constructor
    · intro hwp
      have hp2 : p ≠ 2 := by
        intro h; exact not_two_dvd_oddPrimLt M (by rw [← h]; exact hpd)
      have hp3 : 3 ≤ p := by
        have h2 : 2 ≤ p := hpp.two_le
        rcases hpp.eq_two_or_odd with h | h
        · exact absurd h hp2
        · omega
      exact_mod_cast hp3
    · intro h3p
      exact le_trans (le_of_lt hw3) h3p
  rw [h, prod_sieve_eq M (le_refl (3:ℝ))]

/-- **The Mertens ratio bound for the sieve product.** -/
lemma prod_ratio_le {K : ℝ} (hK : 0 ≤ K) {M : ℕ} (hM : 4 ≤ M) {w : ℝ} (hw : 2 ≤ w)
    (hwM : w < M)
    (hrate : ∀ (z : ℕ) (wt : ℝ), 2 ≤ wt → wt < z →
      (∏ p ∈ (Finset.range z).filter (fun p : ℕ => p.Prime ∧ wt ≤ (p : ℝ)),
          (((p : ℝ) - 1) / ((p : ℝ) - 2)))
        ≤ (Real.log (z : ℝ) / Real.log wt) * (1 + K / Real.log wt)) :
    (∏ p ∈ (oddPrimLt M).primeFactors.filter (fun p : ℕ => w ≤ (p : ℝ)),
        (1 - (Work.ChenPlan.H1.invTotient p))⁻¹)
      ≤ (Real.log (M : ℝ) / Real.log w) * (1 + K / Real.log w) := by
  rcases le_or_gt 3 w with h3 | h3
  · rw [prod_sieve_eq M h3]
    exact hrate M w hw hwM
  · rw [prod_sieve_eq_full M hw h3]
    have hM4 : (3 : ℝ) < (M : ℝ) := by
      have : 3 < M := by omega
      exact_mod_cast this
    have hr := hrate M 3 (by norm_num) hM4
    refine le_trans hr ?_
    have hlog3 : 0 < Real.log (3:ℝ) := Real.log_pos (by norm_num)
    have hwpos : 0 < w := by linarith
    have hlogw : 0 < Real.log w := Real.log_pos (by linarith : 1 < w)
    have hlogM : 0 < Real.log (M : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < M))
    have hlogw3 : Real.log w ≤ Real.log (3:ℝ) := Real.log_le_log hwpos (le_of_lt h3)
    have h1 : Real.log (M : ℝ) / Real.log 3 ≤ Real.log (M : ℝ) / Real.log w :=
      div_le_div_of_nonneg_left hlogM.le hlogw hlogw3
    have h2 : 1 + K / Real.log 3 ≤ 1 + K / Real.log w := by
      have h4 : 1 / Real.log (3:ℝ) ≤ 1 / Real.log w :=
        one_div_le_one_div_of_le hlogw hlogw3
      have h5 : K / Real.log 3 ≤ K / Real.log w := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left (by simpa [one_div] using h4) hK
      linarith
    exact mul_le_mul h1 h2 (by positivity) (by positivity)

/-- **`IsLinear` for the sieve problem of the residue class `q`.** -/
lemma isLinear_apSieve (x M q : ℕ) (hM : 4 ≤ M) {K : ℝ} (hK : 0 ≤ K)
    (hrate : ∀ (z : ℕ) (wt : ℝ), 2 ≤ wt → wt < z →
      (∏ p ∈ (Finset.range z).filter (fun p : ℕ => p.Prime ∧ wt ≤ (p : ℝ)),
          (((p : ℝ) - 1) / ((p : ℝ) - 2)))
        ≤ (Real.log (z : ℝ) / Real.log wt) * (1 + K / Real.log wt)) :
    Submission.ChenPlan.IsLinear (apSieve x M q) (M : ℝ) K := by
  refine ⟨?_, ?_⟩
  · intro p hp
    exact_mod_cast primeFactors_oddPrimLt_lt hp
  · intro w hw2 hwM
    exact prod_ratio_le hK hM hw2 hwM hrate

/-- Eventually the level `D` dominates `M · Y`. -/
lemma eventually_siftM_mul_winY_le_lvlD (B : ℝ) (hB : 0 < B) :
    ∀ᶠ x : ℕ in Filter.atTop, (siftM x : ℝ) * (winY x : ℝ) ≤ lvlD B x := by
  filter_upwards [eventually_const_mul_log_rpow_le (s := (1:ℝ)/15) (b := B) (by norm_num)
      (C := 6) (by norm_num), Filter.eventually_ge_atTop 2] with x hx hx2
  have hx0 : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 0 < x)
  have h1x : (1 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 1 < x)
  have hlogpos : 0 < Real.log (x : ℝ) := Real.log_pos h1x
  have hlogB : 0 < Real.log (x : ℝ) ^ B := Real.rpow_pos_of_pos hlogpos B
  have h6 : 6 * Real.log (x : ℝ) ^ B ≤ (x : ℝ) ^ ((1 : ℝ) / 15) := by simpa using hx
  have h0 : (1:ℝ) ≤ (x:ℝ) := by exact_mod_cast (by omega : 1 ≤ x)
  have hp10 : (1 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 10) := by
    have h := Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ 1) h0 (by norm_num : (0:ℝ) ≤ 1/10)
    rwa [Real.one_rpow] at h
  have hp13 : (1 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 3) := by
    have h := Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ 1) h0 (by norm_num : (0:ℝ) ≤ 1/3)
    rwa [Real.one_rpow] at h
  have hMle : (siftM x : ℝ) ≤ 2 * (x : ℝ) ^ ((1 : ℝ) / 10) := by
    have h := siftM_le_rpow_add_one x
    linarith
  have hYle : (winY x : ℝ) ≤ 3 * (x : ℝ) ^ ((1 : ℝ) / 3) := by
    have h2 := floor_rpow_three_le x
    rw [winY_eq]
    push_cast
    linarith
  have hprod_le : (siftM x : ℝ) * (winY x : ℝ) ≤ 6 * (x : ℝ) ^ ((13 : ℝ) / 30) := by
    have h1 : (siftM x : ℝ) * (winY x : ℝ)
        ≤ (2 * (x : ℝ) ^ ((1 : ℝ) / 10)) * (3 * (x : ℝ) ^ ((1 : ℝ) / 3)) :=
      mul_le_mul hMle hYle (by positivity) (by positivity)
    have h2 : (2 * (x : ℝ) ^ ((1 : ℝ) / 10)) * (3 * (x : ℝ) ^ ((1 : ℝ) / 3))
        = 6 * ((x : ℝ) ^ ((1 : ℝ) / 10) * (x : ℝ) ^ ((1 : ℝ) / 3)) := by ring
    have h3 : (x : ℝ) ^ ((1 : ℝ) / 10) * (x : ℝ) ^ ((1 : ℝ) / 3) = (x : ℝ) ^ ((13 : ℝ) / 30) := by
      rw [← Real.rpow_add hx0]; norm_num
    rw [h2, h3] at h1
    exact h1
  rw [lvlD, le_div_iff₀ hlogB]
  have hsplit : (x : ℝ) ^ ((1 : ℝ) / 2)
      = (x : ℝ) ^ ((1 : ℝ) / 15) * (x : ℝ) ^ ((13 : ℝ) / 30) := by
    rw [← Real.rpow_add hx0]; norm_num
  rw [Real.sqrt_eq_rpow, hsplit]
  have hx1330 : 0 < (x : ℝ) ^ ((13 : ℝ) / 30) := Real.rpow_pos_of_pos hx0 _
  calc (siftM x : ℝ) * (winY x : ℝ) * Real.log (x : ℝ) ^ B
      ≤ 6 * (x : ℝ) ^ ((13 : ℝ) / 30) * Real.log (x : ℝ) ^ B :=
        mul_le_mul_of_nonneg_right hprod_le hlogB.le
    _ = (6 * Real.log (x : ℝ) ^ B) * (x : ℝ) ^ ((13 : ℝ) / 30) := by ring
    _ ≤ (x : ℝ) ^ ((1 : ℝ) / 15) * (x : ℝ) ^ ((13 : ℝ) / 30) :=
        mul_le_mul_of_nonneg_right h6 hx1330.le

/-- For a window prime `q`, the sieve level ratio `s_q` is at least `1`. -/
lemma one_le_sVal {B : ℝ} {x M q : ℕ} (hqM : M ≤ q) (hqY : q < winY x) (hq2 : 2 ≤ q)
    (hMY : (siftM x : ℝ) * (winY x : ℝ) ≤ lvlD B x) (hx2 : 2 ≤ x) :
    1 ≤ sVal B x q := by
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hx0 : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 0 < x)
  have hlogpos : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < x))
  have hlogB : 0 < Real.log (x : ℝ) ^ B := Real.rpow_pos_of_pos hlogpos B
  have hlvlpos : 0 < lvlD B x := by
    rw [lvlD]; positivity
  have hMpos : 0 < (siftM x : ℝ) := by
    rw [siftM_eq]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) ⌊(x:ℝ)^((1:ℝ)/10)⌋₊]
  have hlogMpos : 0 < Real.log (siftM x : ℝ) := by
    apply Real.log_pos
    rw [siftM_eq]; push_cast
    have h0 : (1:ℝ) ≤ (x:ℝ) := by exact_mod_cast (by omega : 1 ≤ x)
    have h1 : (1:ℝ) ≤ (x:ℝ)^((1:ℝ)/10) := by
      have h := Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ 1) h0 (by norm_num : (0:ℝ) ≤ 1/10)
      rwa [Real.one_rpow] at h
    have h2 : 1 ≤ ⌊(x:ℝ)^((1:ℝ)/10)⌋₊ :=
      Nat.le_floor (show ((1:ℕ):ℝ) ≤ (x:ℝ)^((1:ℝ)/10) from by push_cast; exact h1)
    have h3 : (1:ℝ) ≤ ((⌊(x:ℝ)^((1:ℝ)/10)⌋₊ : ℕ) : ℝ) := by exact_mod_cast h2
    linarith
  have hqle : (q : ℝ) ≤ (winY x : ℝ) := by
    exact_mod_cast (le_of_lt hqY)
  -- `M ≤ D/q`
  have hMD : (siftM x : ℝ) ≤ lvlD B x / (q : ℝ) := by
    rw [le_div_iff₀ hqpos]
    calc (siftM x : ℝ) * (q : ℝ) ≤ (siftM x : ℝ) * (winY x : ℝ) :=
          mul_le_mul_of_nonneg_left hqle hMpos.le
      _ ≤ lvlD B x := hMY
  rw [sVal, le_div_iff₀ hlogMpos]
  rw [Real.log_div (ne_of_gt hlvlpos) (ne_of_gt hqpos)]
  have h := Real.log_le_log hMpos hMD
  rw [Real.log_div (ne_of_gt hlvlpos) (ne_of_gt hqpos)] at h
  simpa using h


/-! ## The per-`q` sieve bound -/

/-- The Mertens ratio hypothesis of `mertens_ratio_rate`, for the constant `K` it provides. -/
theorem exists_mertens_ratio :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (z : ℕ) (w : ℝ), 2 ≤ w → w < z →
      (∏ p ∈ (Finset.range z).filter (fun p : ℕ => p.Prime ∧ w ≤ (p : ℝ)),
          (((p : ℝ) - 1) / ((p : ℝ) - 2)))
        ≤ (Real.log (z : ℝ) / Real.log w) * (1 + K / Real.log w) :=
  Work.ChenPlan.H2.mertens_ratio_rate

/-- For every sieve limit `M ≥ 4` the sieve problem of the residue class `q` is linear with
the constant `K` of `mertens_ratio_rate`. -/
theorem isLinear_apSieve_of_ratio (x M q : ℕ) (hM : 4 ≤ M) {K : ℝ} (hK : 0 ≤ K)
    (hrate : ∀ (z : ℕ) (wt : ℝ), 2 ≤ wt → wt < z →
      (∏ p ∈ (Finset.range z).filter (fun p : ℕ => p.Prime ∧ wt ≤ (p : ℝ)),
          (((p : ℝ) - 1) / ((p : ℝ) - 2)))
        ≤ (Real.log (z : ℝ) / Real.log wt) * (1 + K / Real.log wt)) :
    Submission.ChenPlan.IsLinear (apSieve x M q) (M : ℝ) K :=
  isLinear_apSieve x M q hM hK hrate

/-- **The upper linear sieve at the residue class `q`.**  If the linear sieve `hU` is available
with the constant `K`, accuracy `η` and level threshold `D₀` (as an instantiated hypothesis),
then for a window prime `q` whose sieve level `Λ` exceeds `D₀`,

`apMass x M q ≤ (x/φ(q)) · VsieveOdd M · (Utab (s_Λ) + η) + remSumQ x M q Λ`. -/
theorem apMass_le_main_add_rem {x M q : ℕ} (hqp : q.Prime) (hqM : M ≤ q)
    {K η D₀ : ℝ} (hη : 0 < η)
    (hU : ∀ (s : BoundingSieve) (z D : ℝ),
      D₀ ≤ D → 2 ≤ z → Submission.ChenPlan.IsLinear s z K → 0 ≤ s.totalMass →
      1 ≤ Real.log D / Real.log z →
      s.siftedSum ≤ s.totalMass * Submission.ChenPlan.sieveV s
        * (Submission.ChenPlan.Utab (Real.log D / Real.log z) + η)
        + Submission.ChenPlan.remSum s D)
    {Λ : ℝ} (hΛ : D₀ ≤ Λ) (hM2 : 2 ≤ (M : ℝ))
    (hlin : Submission.ChenPlan.IsLinear (apSieve x M q) (M : ℝ) K)
    (hlog : 1 ≤ Real.log Λ / Real.log (M : ℝ)) :
    Submission.apMass x M q
      ≤ (x : ℝ) / (q.totient : ℝ) * VsieveOdd M
          * (Submission.ChenPlan.Utab (Real.log Λ / Real.log (M : ℝ)) + η)
        + remSumQ x M q Λ := by
  have htot : 0 ≤ (apSieve x M q).totalMass := by
    rw [apSieve_totalMass]
    positivity
  have h := hU (apSieve x M q) (M : ℝ) Λ hΛ hM2 hlin htot hlog
  rw [apSieve_siftedSum, apSieve_totalMass, apSieve_sieveV, apSieve_remSum hqp hqM Λ] at h
  exact h

end

end Work.ChenPlan.H2
