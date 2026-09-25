import Mathlib
import Submission.Work.RHContract.Corpus

/-!
# `Work.RHContract.A.ca_lcmUpto_dvd`

`lcm(1..ξ(ε))` divides the colossally abundant number `N_ε`, where `ξ(ε) = caXi ε` is the
largest prime factor of `N_ε` (hypothesis: `ξ ≥ 1530`).

This is (S1) of `ROUTE_LEAD.md` §2.3.  Write `a_p = ⌊μ(p,ε)⌋₊` for the exponent of `p` in
`N_ε` and `e_p = ⌊log ξ / log p⌋` for its exponent in `lcm(1..ξ)`.  Since

  `lcm(1..ξ) = ∏_{p ≤ ξ} p^{e_p}`,   `N_ε = ∏_{p prime, p < bound} p^{a_p}`,

it suffices that `e_p ≤ a_p` for every prime `p ≤ ξ`.

Both exponents are read off from the same threshold function
`F(q,k) = log(1 + 1/(q + q² + … + q^k))/log q = log((q^{k+1}-1)/(q^{k+1}-q))/log q`
(Nicolas (4.5)): `e_p ≥ k ⟺ p^k ≤ ξ`, while by
`Commons.NumberTheory.Robin.caMu_ge_iff_caF` we have `a_p ≥ k ⟺ ε ≤ F(p,k)`.  Hence it is
enough to prove

* `F(p,k) ≥ F(ξ,1)` whenever `p^k ≤ ξ`.

Indeed `F(ξ,1) = g(ξ)` with `g(t) = log(1+1/t)/log t`, which is strictly antitone on
`(1,∞)` (`Commons.Analysis.Real.log_one_add_inv_div_log_strictAntiOn`), so `g(ξ) ≤ g(p^k)`;
and `g(p^k) ≤ F(p,k)`: putting `S = p + … + p^k` we have `F(p,k) = log(1+1/S)/log p`,
`g(p^k) = log(1+1/p^k)/(k log p)`, `S ≤ k·p^k`, and Bernoulli's inequality gives
`(1+1/S)^k ≥ 1 + k/S ≥ 1 + 1/p^k`.

The hypothesis `ξ ≥ 1530` is only used to know that the support is non-empty.
-/

namespace Work.RHContract.A

open scoped BigOperators

noncomputable section

/-- `F(p,k) = log((p^{k+1}-1)/(p^{k+1}-p))/log p`, the corpus threshold `caF` (Nicolas (4.5)). -/
private def caFq (p k : ℕ) : ℝ :=
  Real.log (((p : ℝ) ^ (k + 1 : ℕ) - 1) / ((p : ℝ) ^ (k + 1 : ℕ) - (p : ℝ))) /
    Real.log (p : ℝ)

/-- `g(t) = log(1 + 1/t)/log t`. -/
private def caG (t : ℝ) : ℝ := Real.log (1 + 1 / t) / Real.log t

/-- `S(p,k) = p + p² + … + p^k`. -/
private def caS (p k : ℕ) : ℝ := ∑ i ∈ Finset.range k, (p : ℝ) ^ (i + 1)

private lemma caS_pos (p k : ℕ) (hp : 1 ≤ p) (hk : 1 ≤ k) : 0 < caS p k := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  unfold caS
  refine Finset.sum_pos (fun i _ => ?_) ⟨0, Finset.mem_range.mpr (by omega)⟩
  positivity

private lemma caS_geom (p k : ℕ) :
    ((p : ℝ) - 1) * caS p k = (p : ℝ) ^ (k + 1) - (p : ℝ) := by
  have h1 : caS p k = (p : ℝ) * ∑ i ∈ Finset.range k, (p : ℝ) ^ i := by
    unfold caS
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by rw [pow_succ'])
  have h2 := geom_sum_mul (p : ℝ) k
  rw [h1, pow_succ]
  nlinarith [h2]

/-- `F(p,k) = log(1 + 1/S(p,k))/log p`. -/
private lemma caFq_eq (p k : ℕ) (hp : 2 ≤ p) (hk : 1 ≤ k) :
    caFq p k = Real.log (1 + 1 / caS p k) / Real.log (p : ℝ) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hpm1 : ((p : ℝ) - 1) ≠ 0 := by
    have : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
    linarith
  have hSpos : 0 < caS p k := caS_pos p k (by omega) hk
  have hSne : caS p k ≠ 0 := ne_of_gt hSpos
  have h1 := caS_geom p k
  have h2 : ((p : ℝ) - 1) * (caS p k + 1) = (p : ℝ) ^ (k + 1) - 1 := by
    rw [mul_add, h1, mul_one]
    ring
  have hkey : (((p : ℝ) - 1) * (caS p k + 1)) / (((p : ℝ) - 1) * caS p k) =
      1 + 1 / caS p k := by
    rw [mul_comm ((p : ℝ) - 1) (caS p k + 1), mul_comm ((p : ℝ) - 1) (caS p k),
      mul_div_mul_right (caS p k + 1) (caS p k) hpm1]
    simp [add_div, div_self hSne]
  unfold caFq
  rw [← h2, ← h1, hkey]

/-- `F(p,1) = g(p)` for `p ≥ 2`. -/
private lemma caFq_one (p : ℕ) (hp : 2 ≤ p) : caFq p 1 = caG (p : ℝ) := by
  have hpne : (p : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
    exact ne_of_gt this
  have hpm1 : ((p : ℝ) - 1) ≠ 0 := by
    have : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
    linarith
  have hden : (p : ℝ) ^ 2 - (p : ℝ) ≠ 0 := by
    have : (p : ℝ) ^ 2 - (p : ℝ) = (p : ℝ) * ((p : ℝ) - 1) := by ring
    rw [this]
    exact mul_ne_zero hpne hpm1
  have h : (((p : ℝ) ^ (1 + 1 : ℕ) - 1) / ((p : ℝ) ^ (1 + 1 : ℕ) - (p : ℝ))) =
      1 + 1 / (p : ℝ) := by
    have h2 : (p : ℝ) ^ (1 + 1 : ℕ) = (p : ℝ) ^ 2 := by norm_num
    rw [h2, div_eq_iff hden]
    field_simp
    ring
  unfold caFq caG
  rw [h]

/-- `g(p^k) ≤ F(p,k)` for `p ≥ 2`, `k ≥ 1`. -/
private lemma caG_pow_le_caFq (p k : ℕ) (hp : 2 ≤ p) (hk : 1 ≤ k) :
    caG ((p : ℝ) ^ k) ≤ caFq p k := by
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
  have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos hp1
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hSpos : 0 < caS p k := caS_pos p k (by omega) hk
  have hpkpos : (0 : ℝ) < (p : ℝ) ^ k := by positivity
  have hSle : caS p k ≤ (k : ℝ) * (p : ℝ) ^ k := by
    unfold caS
    calc ∑ i ∈ Finset.range k, (p : ℝ) ^ (i + 1)
        ≤ ∑ _i ∈ Finset.range k, (p : ℝ) ^ k := by
          refine Finset.sum_le_sum (fun i hi => ?_)
          exact pow_le_pow_right₀ (le_of_lt hp1) (by have := Finset.mem_range.mp hi; omega)
      _ = (k : ℝ) * (p : ℝ) ^ k := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have h1 : 1 / (p : ℝ) ^ k ≤ (k : ℝ) / caS p k := by
    rw [div_le_div_iff₀ hpkpos hSpos]
    simpa using hSle
  have h2 : 1 + (k : ℝ) / caS p k ≤ (1 + 1 / caS p k) ^ k := by
    have hb := one_add_mul_le_pow (a := 1 / caS p k)
      (by have h := one_div_pos.mpr hSpos; linarith) k
    have heq : (k : ℝ) * (1 / caS p k) = (k : ℝ) / caS p k := by ring
    rwa [heq] at hb
  have h3 : 1 + 1 / (p : ℝ) ^ k ≤ (1 + 1 / caS p k) ^ k := by linarith
  have h4 : Real.log (1 + 1 / (p : ℝ) ^ k) ≤ (k : ℝ) * Real.log (1 + 1 / caS p k) := by
    have h5 := Real.log_le_log (by positivity : (0 : ℝ) < 1 + 1 / (p : ℝ) ^ k) h3
    rwa [Real.log_pow] at h5
  unfold caG
  rw [caFq_eq p k hp hk, Real.log_pow]
  rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < (k : ℝ) * Real.log (p : ℝ)) hlogp]
  calc Real.log (1 + 1 / (p : ℝ) ^ k) * Real.log (p : ℝ)
      ≤ ((k : ℝ) * Real.log (1 + 1 / caS p k)) * Real.log (p : ℝ) :=
        mul_le_mul_of_nonneg_right h4 (le_of_lt hlogp)
    _ = Real.log (1 + 1 / caS p k) * ((k : ℝ) * Real.log (p : ℝ)) := by ring

/-- `ε ≤ g(ξ)` and `p^k ≤ ξ` imply `ε ≤ F(p,k)` for `p ≥ 2`, `k ≥ 1`. -/
private lemma caG_le_caFq_of (ε : ℝ) {ξ p k : ℕ} (hp : 2 ≤ p) (hk : 1 ≤ k)
    (hpk : p ^ k ≤ ξ) (hεG : ε ≤ caG (ξ : ℝ)) : ε ≤ caFq p k := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
  have hpk' : ((p : ℝ) ^ k) ≤ (ξ : ℝ) := by exact_mod_cast hpk
  have hξ1 : (1 : ℝ) < (ξ : ℝ) := lt_of_lt_of_le (one_lt_pow₀ hp1 (by omega)) hpk'
  have hpk1 : (1 : ℝ) < (p : ℝ) ^ k := one_lt_pow₀ hp1 (by omega)
  have hanti : caG (ξ : ℝ) ≤ caG ((p : ℝ) ^ k) :=
    (Commons.Analysis.Real.log_one_add_inv_div_log_strictAntiOn.le_iff_ge
      (show (ξ : ℝ) ∈ Set.Ioi 1 from hξ1)
      (show ((p : ℝ) ^ k) ∈ Set.Ioi 1 from hpk1)).mpr hpk'
  exact le_trans hεG (le_trans hanti (caG_pow_le_caFq p k hp hk))

theorem ca_lcmUpto_dvd (ε : ℝ) (hε : 0 < ε) (hξ : 1530 ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Nat.lcmUpto ⌊(Work.RHPlan.caXi ε : ℝ)⌋₊ ∣ Work.RHPlan.caNumber ε := by
  rw [Nat.floor_natCast]
  have hξne : Work.RHPlan.caXi ε ≠ 0 := by
    intro h0
    rw [h0] at hξ
    norm_num at hξ
  -- the support of `N_ε` is non-empty, and `caXi ε` is its maximum
  have hne : (Work.RHPlan.caSupport ε).Nonempty := by
    by_contra hc
    rw [Finset.not_nonempty_iff_eq_empty] at hc
    have h0 : Work.RHPlan.caXi ε = 0 := by simp [Work.RHPlan.caXi, hc]
    rw [h0] at hξ
    norm_num at hξ
  have hmax : Work.RHPlan.caXi ε = (Work.RHPlan.caSupport ε).max' hne := by
    rw [Work.RHPlan.caXi, Finset.max'_eq_sup', Finset.sup'_eq_sup hne]
  have hmem : Work.RHPlan.caXi ε ∈ Work.RHPlan.caSupport ε := by
    rw [hmax]
    exact Finset.max'_mem _ hne
  have hmem' : Work.RHPlan.caXi ε ∈
      ((Finset.range (Nat.ceil (Real.exp (2 / ε)) + 2)).filter Nat.Prime).filter
        (fun p : ℕ => 1 ≤ ⌊Work.RHPlan.caMu p ε⌋₊) := by
    simpa [Work.RHPlan.caSupport, Work.RHPlan.caMu] using hmem
  obtain ⟨hmem2, hexp⟩ := Finset.mem_filter.mp hmem'
  obtain ⟨hrange, hprime⟩ := Finset.mem_filter.mp hmem2
  have hbound : Work.RHPlan.caXi ε < Nat.ceil (Real.exp (2 / ε)) + 2 :=
    Finset.mem_range.mp hrange
  -- `ε ≤ g (caXi ε)`
  have hμpos : 0 < Work.RHPlan.caMu (Work.RHPlan.caXi ε) ε := by
    have h := Commons.NumberTheory.Robin.caMu_pos (p := Work.RHPlan.caXi ε) (ε := ε)
      hprime.two_le hε
    simpa [Work.RHPlan.caMu] using h
  have hμ : (1 : ℝ) ≤ Work.RHPlan.caMu (Work.RHPlan.caXi ε) ε := by
    have h1 : (1 : ℝ) ≤ (⌊Work.RHPlan.caMu (Work.RHPlan.caXi ε) ε⌋₊ : ℝ) := by
      exact_mod_cast hexp
    exact le_trans h1 (Nat.floor_le (le_of_lt hμpos))
  have hεF : ε ≤ caFq (Work.RHPlan.caXi ε) 1 :=
    (Commons.NumberTheory.Robin.caMu_ge_iff_caF (Work.RHPlan.caXi ε) ε 1
      hprime.two_le hε le_rfl).mp (by simpa [Work.RHPlan.caMu] using hμ)
  have hεG : ε ≤ caG ((Work.RHPlan.caXi ε : ℕ) : ℝ) := by
    rw [← caFq_one (Work.RHPlan.caXi ε) hprime.two_le]
    exact hεF
  -- the primes of `N_ε`: `caNumber ε` is the product over them
  set S : Finset ℕ := (Finset.range (Nat.ceil (Real.exp (2 / ε)) + 2)).filter Nat.Prime with hSdef
  have hsub : Nat.primesLE (Work.RHPlan.caXi ε) ⊆ S := by
    intro p hp'
    rw [Nat.mem_primesLE] at hp'
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (lt_of_le_of_lt hp'.1 hbound), hp'.2⟩
  have htriv : ∀ p ∈ S, p ∉ Nat.primesLE (Work.RHPlan.caXi ε) →
      p ^ Nat.log p (Work.RHPlan.caXi ε) = 1 := by
    intro p hpS hpn
    have hpprime : Nat.Prime p := (Finset.mem_filter.mp hpS).2
    have hgt : Work.RHPlan.caXi ε < p := by
      by_contra hle
      exact hpn (Nat.mem_primesLE.mpr ⟨le_of_not_gt hle, hpprime⟩)
    rw [Nat.log_eq_zero_iff.mpr (Or.inl hgt), pow_zero]
  rw [Nat.lcmUpto_eq_prod_pow_log]
  calc ∏ p ∈ Nat.primesLE (Work.RHPlan.caXi ε), p ^ Nat.log p (Work.RHPlan.caXi ε)
      = ∏ p ∈ S, p ^ Nat.log p (Work.RHPlan.caXi ε) := Finset.prod_subset hsub htriv
    _ ∣ ∏ p ∈ S, p ^ ⌊Work.RHPlan.caMu p ε⌋₊ := by
        refine Finset.prod_dvd_prod_of_dvd _ _ (fun p hpS => ?_)
        by_cases hk0 : Nat.log p (Work.RHPlan.caXi ε) = 0
        · rw [hk0, pow_zero]
          exact one_dvd _
        · have hk1 : 1 ≤ Nat.log p (Work.RHPlan.caXi ε) :=
            Nat.succ_le_of_lt (Nat.pos_of_ne_zero hk0)
          have hpprime : Nat.Prime p := (Finset.mem_filter.mp hpS).2
          have hpkξ : p ^ Nat.log p (Work.RHPlan.caXi ε) ≤ Work.RHPlan.caXi ε :=
            Nat.pow_log_le_self p hξne
          have hle : ε ≤ caFq p (Nat.log p (Work.RHPlan.caXi ε)) :=
            caG_le_caFq_of ε hpprime.two_le hk1 hpkξ hεG
          have hmulog : (Nat.log p (Work.RHPlan.caXi ε) : ℝ) ≤ Work.RHPlan.caMu p ε :=
            (Commons.NumberTheory.Robin.caMu_ge_iff_caF p ε
              (Nat.log p (Work.RHPlan.caXi ε)) hpprime.two_le hε hk1).mpr
              (by simpa [caFq] using hle)
          exact pow_dvd_pow p (Nat.le_floor hmulog)
    _ = Work.RHPlan.caNumber ε := by
        rw [Work.RHPlan.caNumber, hSdef]
        refine Finset.prod_congr rfl (fun p _ => ?_)
        rw [Work.RHPlan.caMu]

end

end Work.RHContract.A
