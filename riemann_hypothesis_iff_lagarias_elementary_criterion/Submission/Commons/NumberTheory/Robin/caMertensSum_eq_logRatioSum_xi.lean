import Mathlib
import Submission.Commons.NumberTheory.Robin.caMu_ge_iff_caF
import Submission.Commons.NumberTheory.Robin.caMu_pos
import Submission.Commons.Analysis.Real.log_one_add_inv_bounds
import Submission.Commons.NumberTheory.Mertens.sum_log_prime_ratio_real_tendsto

/-!
# The Mertens part of the U-decomposition equals `logRatioSum ξ(ε)`

For the colossally-abundant family with exponent parameter
`μ(p,ε) = log((p^{1+ε}−1)/(p^{1+ε}−p)) / log p` and support
`supp(ε) = {p prime, p < ⌈exp(2/ε)⌉+2 : 1 ≤ ⌊μ(p,ε)⌋₊}`, the prime support is
*downward closed*: `F(p,1) = log(1+1/p)/log p` is strictly decreasing in the prime `p`,
so `supp(ε) = {p prime : p ≤ ξ(ε)}` with `ξ(ε) := max supp(ε)`.  Consequently

  `Σ_{p ∈ supp(ε)} log(p/(p−1)) = logRatioSum ξ(ε)` .

All helpers are inlined and kept `private` so that nothing leaks into the shared
commons namespace (the file exports a single theorem).
-/

namespace Commons.NumberTheory.Robin

open scoped BigOperators

noncomputable section

/-- `μ(p,ε) = log((p^{1+ε}−1)/(p^{1+ε}−p))/log p`, the (4.11)-exponent parameter. -/
private def caMu (p : ℕ) (ε : ℝ) : ℝ :=
  Real.log (((p : ℝ) ^ (1 + ε) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) / Real.log (p : ℝ)

/-- The exponent of the prime `p` in the CA number `N_ε`: `⌊μ(p,ε)⌋₊`. -/
private def caExp (p : ℕ) (ε : ℝ) : ℕ := ⌊caMu p ε⌋₊

/-- `F(p,k) = log((p^{k+1}−1)/(p^{k+1}−p))/log p` for `k ≥ 1` (Nicolas (4.5)). -/
private def caF (p : ℕ) (k : ℕ) : ℝ :=
  Real.log (((p : ℝ) ^ (k + 1 : ℕ) - 1) / (((p : ℝ) ^ (k + 1 : ℕ)) - (p : ℝ))) / Real.log (p : ℝ)

/-- The support bound `⌈exp(2/ε)⌉+2` of `N_ε`. -/
private abbrev caBound (ε : ℝ) : ℕ := Nat.ceil (Real.exp (2 / ε)) + 2

/-- The prime support of `N_ε`: primes `p < caBound ε` with `1 ≤ ⌊μ(p,ε)⌋₊`. -/
private abbrev caSupp (ε : ℝ) : Finset ℕ :=
  ((Finset.range (caBound ε)).filter Nat.Prime).filter (fun p => 1 ≤ caExp p ε)

private lemma mem_caSupp {ε : ℝ} {p : ℕ} :
    p ∈ caSupp ε ↔ Nat.Prime p ∧ p < caBound ε ∧ 1 ≤ caExp p ε := by
  unfold caSupp caBound
  rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_range]
  exact ⟨fun h => ⟨h.1.2, h.1.1, h.2⟩, fun h => ⟨⟨h.2.1, h.1⟩, h.2.2⟩⟩

/-- `μ(p,ε) > 0` for `p ≥ 2`, `ε > 0`. -/
private lemma caMu_pos_local {p : ℕ} {ε : ℝ} (hp : 2 ≤ p) (hε : 0 < ε) : 0 < caMu p ε := by
  simpa [caMu] using Commons.NumberTheory.Robin.caMu_pos (p := p) (ε := ε) hp hε

/-- `p ≥ 2`, `ε > 0`: `1 ≤ ⌊μ(p,ε)⌋₊ ⟺ 1 ≤ μ(p,ε)`. -/
private lemma one_le_caExp_iff {p : ℕ} {ε : ℝ} (hp : 2 ≤ p) (hε : 0 < ε) :
    1 ≤ caExp p ε ↔ (1 : ℝ) ≤ caMu p ε := by
  constructor
  · intro h
    have hpos : 0 ≤ caMu p ε := le_of_lt (caMu_pos_local hp hε)
    have h' : (1 : ℝ) ≤ (⌊caMu p ε⌋₊ : ℝ) := by exact_mod_cast h
    exact le_trans h' (Nat.floor_le hpos)
  · intro h
    exact Nat.le_floor (show ((1 : ℕ) : ℝ) ≤ caMu p ε from by simpa using h)

/-- `p ≥ 2`, `ε > 0`: `μ(p,ε) ≥ 1 ⟺ ε ≤ F(p,1)` (Nicolas (4.11)/(4.5) at `k = 1`). -/
private lemma mu_ge_one_iff {p : ℕ} {ε : ℝ} (hp : 2 ≤ p) (hε : 0 < ε) :
    (1 : ℝ) ≤ caMu p ε ↔ ε ≤ caF p 1 := by
  have h := Commons.NumberTheory.Robin.caMu_ge_iff_caF p ε 1 hp hε (le_refl (1 : ℕ))
  simpa [caMu, caF] using h

/-- `F(p,1) = log(1 + 1/p)/log p` for `p ≥ 2`. -/
private lemma caF1_eq_log_one_add {p : ℕ} (hp : 2 ≤ p) :
    caF p 1 = Real.log (1 + 1 / (p : ℝ)) / Real.log (p : ℝ) := by
  unfold caF
  have hk : (1 + 1 : ℕ) = 2 := by norm_num
  rw [hk, pow_two]
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
  have hpm1 : (p : ℝ) - 1 ≠ 0 := by
    have hpne : (p : ℝ) ≠ 1 := by exact_mod_cast (by omega : p ≠ 1)
    exact sub_ne_zero.mpr hpne
  have hmain : ((p : ℝ) * (p : ℝ) - 1) / ((p : ℝ) * (p : ℝ) - (p : ℝ)) =
      1 + 1 / (p : ℝ) := by
    have hnum : (p : ℝ) * (p : ℝ) - 1 = ((p : ℝ) + 1) * ((p : ℝ) - 1) := by ring
    have hden : (p : ℝ) * (p : ℝ) - (p : ℝ) = (p : ℝ) * ((p : ℝ) - 1) := by ring
    rw [hnum, hden]
    field_simp [hp0, hpm1]
  rw [hmain]

/-- `F(·,1)` is strictly decreasing in the prime: `2 ≤ p < q ⟹ F(q,1) < F(p,1)`. -/
private lemma caF1_strict_anti {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (hlt : p < q) :
    caF q 1 < caF p 1 := by
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < p))
  have hlogq : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < q))
  have hbp := Commons.Analysis.Real.log_one_add_inv_bounds (t := (p : ℝ)) hppos
  have hq1ne : (1 : ℝ) + 1 / (q : ℝ) ≠ 1 := by
    have hq0r : (q : ℝ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
    have h : (1 : ℝ) / (q : ℝ) ≠ 0 := one_div_ne_zero hq0r
    intro hh
    apply h
    linarith
  have hq1pos : 0 < (1 : ℝ) + 1 / (q : ℝ) := by positivity
  have hqstrict : Real.log (1 + 1 / (q : ℝ)) < 1 / (q : ℝ) := by
    simpa using (Real.log_lt_sub_one_of_pos hq1pos hq1ne)
  have hrew1 : 1 / (((p : ℝ) + 1) * Real.log (p : ℝ)) =
      (1 / ((p : ℝ) + 1)) / Real.log (p : ℝ) := by
    field_simp [ne_of_gt hlogp]
  have h1 : 1 / (((p : ℝ) + 1) * Real.log (p : ℝ)) < caF p 1 := by
    rw [caF1_eq_log_one_add hp, hrew1]
    exact div_lt_div_of_pos_right hbp.1 hlogp
  have hrew2 : (1 / (q : ℝ)) / Real.log (q : ℝ) = 1 / ((q : ℝ) * Real.log (q : ℝ)) := by
    field_simp [ne_of_gt hlogq]
  have h2 : caF q 1 < 1 / ((q : ℝ) * Real.log (q : ℝ)) := by
    rw [caF1_eq_log_one_add hq, ← hrew2]
    exact div_lt_div_of_pos_right hqstrict hlogq
  have hpqcast : (p : ℝ) + 1 ≤ (q : ℝ) := by exact_mod_cast (by omega : p + 1 ≤ q)
  have hloglt : Real.log (p : ℝ) < Real.log (q : ℝ) :=
    Real.log_lt_log (by exact_mod_cast (by omega : 0 < p)) (by exact_mod_cast (by omega : p < q))
  have hmul1 : ((p : ℝ) + 1) * Real.log (p : ℝ) < (q : ℝ) * Real.log (q : ℝ) := by
    calc
      ((p : ℝ) + 1) * Real.log (p : ℝ) ≤ (q : ℝ) * Real.log (p : ℝ) :=
        mul_le_mul_of_nonneg_right hpqcast (le_of_lt hlogp)
      _ < (q : ℝ) * Real.log (q : ℝ) := mul_lt_mul_of_pos_left hloglt hqpos
  have h3 : 1 / ((q : ℝ) * Real.log (q : ℝ)) < 1 / (((p : ℝ) + 1) * Real.log (p : ℝ)) :=
    one_div_lt_one_div_of_lt (mul_pos (by linarith : 0 < (p : ℝ) + 1) hlogp) hmul1
  linarith

/-- the support is downward closed among primes: `p < q` primes with `1 ≤ ⌊μ(q,ε)⌋₊`
imply `1 ≤ ⌊μ(p,ε)⌋₊`. -/
private lemma caSupp_down_closed {ε : ℝ} (hε : 0 < ε) {p q : ℕ} (hp : Nat.Prime p)
    (hq : Nat.Prime q) (hlt : p < q) (hqge : 1 ≤ caExp q ε) : 1 ≤ caExp p ε := by
  have hqμ : (1 : ℝ) ≤ caMu q ε := (one_le_caExp_iff hq.two_le hε).mp hqge
  have hqF : ε ≤ caF q 1 := (mu_ge_one_iff hq.two_le hε).mp hqμ
  have hltF : caF q 1 < caF p 1 := caF1_strict_anti hp.two_le hq.two_le hlt
  have hpF : ε ≤ caF p 1 := le_of_lt (lt_of_le_of_lt hqF hltF)
  have hpμ : (1 : ℝ) ≤ caMu p ε := (mu_ge_one_iff hp.two_le hε).mpr hpF
  exact (one_le_caExp_iff hp.two_le hε).mpr hpμ

/-- characterization of the support as the primes `≤ max supp(ε)`. -/
private theorem caSupp_eq_primesLE_xi {ε : ℝ} (hε : 0 < ε) (hs : (caSupp ε).Nonempty) :
    caSupp ε = ((caSupp ε).max' hs).primesLE := by
  ext p
  rw [Nat.mem_primesLE]
  constructor
  · intro hp
    exact ⟨Finset.le_max' _ p hp, (mem_caSupp.mp hp).1⟩
  · rintro ⟨hple, hpprime⟩
    have hMmem : (caSupp ε).max' hs ∈ caSupp ε := Finset.max'_mem _ hs
    have hMspec := mem_caSupp.mp hMmem
    rw [mem_caSupp]
    refine ⟨hpprime, lt_of_le_of_lt hple hMspec.2.1, ?_⟩
    by_cases hpeq : p = (caSupp ε).max' hs
    · rw [hpeq]
      exact hMspec.2.2
    · exact caSupp_down_closed hε hpprime hMspec.1 (lt_of_le_of_ne hple hpeq) hMspec.2.2

/-- The Mertens part of the U-decomposition over the CA-support equals `logRatioSum ξ(ε)`
(Nicolas (5.4): the `−U5` main term matched to the Mertens `logRatioSum`). -/
theorem caMertensSum_eq_logRatioSum_xi {ε : ℝ} (hε : 0 < ε) (hs : (((Finset.range (Nat.ceil (Real.exp (2 / ε)) + 2)).filter Nat.Prime).filter (fun p : ℕ => 1 ≤ ⌊Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) / Real.log (p : ℝ)⌋₊)).Nonempty) :
    (Finset.sum (((Finset.range (Nat.ceil (Real.exp (2 / ε)) + 2)).filter Nat.Prime).filter (fun p : ℕ => 1 ≤ ⌊Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) / Real.log (p : ℝ)⌋₊)) (fun p : ℕ => Real.log ((p : ℝ) / ((p : ℝ) - 1)))) = Commons.NumberTheory.Mertens.logRatioSum (((((Finset.range (Nat.ceil (Real.exp (2 / ε)) + 2)).filter Nat.Prime).filter (fun p : ℕ => 1 ≤ ⌊Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) / Real.log (p : ℝ)⌋₊)).max' hs) : ℝ) := by
  show (Finset.sum (caSupp ε) (fun p : ℕ => Real.log ((p : ℝ) / ((p : ℝ) - 1)))) =
    Commons.NumberTheory.Mertens.logRatioSum (((caSupp ε).max' hs) : ℝ)
  unfold Commons.NumberTheory.Mertens.logRatioSum
  rw [Nat.floor_natCast]
  nth_rewrite 1 [caSupp_eq_primesLE_xi hε hs]
  rfl

end

end Commons.NumberTheory.Robin
