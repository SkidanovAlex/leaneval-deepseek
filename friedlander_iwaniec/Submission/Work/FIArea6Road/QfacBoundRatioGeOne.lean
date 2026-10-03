/-
# `Submission.Work.FIArea6Road.QfacBoundRatioGeOne`

The bound on the §16 truncation sum

  `Q(s) = Σ_{c ≤ C, (c,Π)=1} λ(c)c^{-s}∏_{p|c}(1-λ(p)p^{-s})^{-1}`   (*FI* (16.34))

in the region **to the right of the line `re s = 1`**, i.e. on `1 ≤ re s ≤ 2`:

  `‖Q(s)‖ ≤ K·C^{re s - 1}·(1 + log(C+2)/log Pz)²`,  `K` absolute.

Since `C^{re s - 1} ≥ 1` for `C ≥ 1`, `re s ≥ 1`, it suffices to bound `Q(s)` by
`K(1 + log(C+2)/log Pz)²`: on `re s ≥ 1` every summand is dominated by its value at `re s = 1`,
namely `‖λ(c)‖c^{-1}∏_{p|c}(1+4p^{-3/4})`, because

* `c^{-re s} ≤ c^{-1}`, and every prime `p | c` for `c` in the sum exceeds `Pz ≥ e⁴` (the sum
  is restricted to `c` coprime to `Π = ∏_{p ≤ Pz} p`);
* `λ(c) = ∏_{p|c}λ(p)` for squarefree `c` (`zcub_heckeLam_prod_primeFactors`) and `‖λ(p)‖ ≤ 2`
  (`heckeLam_prime_norm_le_two`);
* the local factor is `≤ locBnd p ≤ 1 + 4p^{-3/4}` on `re s ≥ 3/4` (`locF_inv_bound`,
  `zcub_locBnd_le`).

The remaining sum is the Euler product `∏_{Pz < p ≤ C}(1 + 2(1+4p^{-3/4})/p) ≤ K(1 + log C/log Pz)²`
by the two-sided Mertens theorem (`zcub_Qfac_prod_le`) plus the expansion `QfacProdExpand`; the
factors `p ≤ Pz` are `1`, because their weight `QfacW` vanishes identically there.

The three steps are isolated below (`QfacTermNormLe`, `QfacSumBound`, `QfacRatioLogStep`); the
vocabulary (`QfacS`, `QfacTerm`, `QfacW`) lives in `Submission.Work.FIArea6Road.QfacRatioDefs`.
-/
import Mathlib
import Submission.Work.FIArea6Road.ZcontExistsBoundUniform
import Submission.Work.FIArea6Road.QfacRatioDefs
import Submission.Work.FIArea6Road.QfacProdExpand

namespace Work.FIArea6Road

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- **The per-summand bound at `re s ≥ 1`.**  For `c` in the index set `QfacS Pa` of (16.34) — so
`c` is squarefree and all its prime factors exceed `Pz ≥ e⁴ ≥ 7` — the summand
`λ(c)c^{-s}∏_{p|c}(1-λ(p)p^{-s})^{-1}` is dominated by the local majorant `∏_{p|c}QfacW Pa p`. -/
lemma QfacTermNormLe (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (m : ℤ)
    (hchi1 : chi 1 = 1) (hchimul : ∀ z w : GaussianInt, chi (z * w) = chi z * chi w)
    (hchi : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) (hlogPz : 4 ≤ Real.log (Pa.Pz : ℝ))
    {s : ℂ} (h1 : 1 ≤ s.re) {c : ℕ} (hc : c ∈ QfacS Pa) :
    ‖QfacTerm chi m s c‖ ≤ ∏ p ∈ c.primeFactors, QfacW Pa p := by
  have hcIcc : c ∈ Finset.Icc 1 ⌊Pa.C⌋₊ := (Finset.mem_filter.mp hc).1
  have hcsf : Squarefree c := (Finset.mem_filter.mp hc).2.1
  have hccop : Nat.Coprime c (∏ p ∈ Nat.primesBelow (Pa.Pz + 1), p) :=
    (Finset.mem_filter.mp hc).2.2
  have hc1 : 1 ≤ c := (Finset.mem_Icc.mp hcIcc).1
  have hc0 : 0 < c := by omega
  have hcR : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc0
  -- `Pz ≥ 7`, i.e. the local majorant `locBnd` is available at every prime `> Pz`
  have hPz7 : 7 ≤ Pa.Pz := by
    by_contra h
    have hle : (Pa.Pz : ℝ) ≤ 6 := by exact_mod_cast (by omega : Pa.Pz ≤ 6)
    have hlog6 : Real.log (Pa.Pz : ℝ) ≤ Real.log 6 := by
      rcases Nat.eq_zero_or_pos Pa.Pz with h0 | hpos
      · simp [h0]
        exact Real.log_nonneg (by norm_num)
      · exact Real.log_le_log (by exact_mod_cast hpos) hle
    have hlog68 : Real.log 6 ≤ Real.log 8 := Real.log_le_log (by norm_num) (by norm_num)
    have hlog8 : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
      norm_num
    have hlog2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
      linarith
    linarith
  -- the coprimality cut forces every prime factor of `c` to exceed `Pz`
  have hprime_gt : ∀ p ∈ c.primeFactors, Pa.Pz < p := by
    intro p hp
    have hpp : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
    have hpdvd : p ∣ c := (Nat.mem_primeFactors.mp hp).2.1
    by_contra hle
    have hple : p ≤ Pa.Pz := not_lt.mp hle
    have hmem : p ∈ Nat.primesBelow (Pa.Pz + 1) := by
      rw [Nat.mem_primesBelow]
      exact ⟨by omega, hpp⟩
    have hdvdPr : p ∣ ∏ q ∈ Nat.primesBelow (Pa.Pz + 1), q :=
      Finset.dvd_prod_of_mem (fun q : ℕ => q) hmem
    have hgcd : p ∣ Nat.gcd c (∏ q ∈ Nat.primesBelow (Pa.Pz + 1), q) :=
      Nat.dvd_gcd hpdvd hdvdPr
    rw [hccop.gcd_eq_one] at hgcd
    exact hpp.not_dvd_one hgcd
  -- split the norm of the summand
  have hnorm : ‖QfacTerm chi m s c‖
      = ‖Work.FIArea5.S16Hecke.heckeLam chi m c‖ * (c : ℝ) ^ (-s.re)
        * ∏ p ∈ c.primeFactors,
            ‖(1 - Work.FIArea5.S16Hecke.heckeLam chi m p * (p : ℂ) ^ (-s))⁻¹‖ := by
    rw [QfacTerm, norm_mul, norm_mul, norm_prod, Complex.norm_natCast_cpow_of_pos hc0]
    simp [Complex.neg_re]
  -- `‖λ(c)‖ ≤ ∏_{p|c} 2`
  have hlam : ‖Work.FIArea5.S16Hecke.heckeLam chi m c‖
      ≤ ∏ p ∈ c.primeFactors, (2 : ℝ) := by
    rw [zcub_heckeLam_prod_primeFactors chi m hchi1 hchimul hcsf, norm_prod]
    exact Finset.prod_le_prod₀ (fun p _ => norm_nonneg _)
      (fun p hp => heckeLam_prime_norm_le_two' chi m hchi
        ⟨p, Nat.prime_of_mem_primeFactors hp⟩)
  -- the local factors, bounded by `1 + 4p^{-3/4}`
  have hloc : ∏ p ∈ c.primeFactors,
        ‖(1 - Work.FIArea5.S16Hecke.heckeLam chi m p * (p : ℂ) ^ (-s))⁻¹‖
      ≤ ∏ p ∈ c.primeFactors, (1 + 4 * (p : ℝ) ^ (-(3 / 4 : ℝ))) := by
    refine Finset.prod_le_prod₀ (fun p _ => norm_nonneg _) ?_
    intro p hp
    have hpp : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
    have hp7 : 7 ≤ p := by have := hprime_gt p hp; omega
    have h34 : (3 : ℝ) / 4 ≤ s.re := by linarith
    exact le_trans (locF_inv_bound chi m hchi hpp h34) (zcub_locBnd_le hp7)
  -- `c^{-1} = ∏_{p|c} p^{-1}` and `c^{-re s} ≤ c^{-1}`
  have hcinv : ((c : ℝ))⁻¹ = ∏ p ∈ c.primeFactors, ((p : ℝ))⁻¹ := by
    rw [Finset.prod_inv_distrib, ← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hcsf]
  have hcv : (c : ℝ) ^ (-s.re) ≤ (c : ℝ)⁻¹ := by
    have hc1R : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc1
    have h' := Real.rpow_le_rpow_of_exponent_le hc1R (by linarith : -s.re ≤ (-1 : ℝ))
    rwa [Real.rpow_neg_one] at h'
  -- the per-prime weight is exactly `QfacW`
  have hW : ∀ p ∈ c.primeFactors,
      (2 : ℝ) * ((p : ℝ))⁻¹ * (1 + 4 * (p : ℝ) ^ (-(3 / 4 : ℝ))) = QfacW Pa p := by
    intro p hp
    rw [QfacW, if_pos (hprime_gt p hp), div_eq_mul_inv]
    ring
  calc ‖QfacTerm chi m s c‖
      = ‖Work.FIArea5.S16Hecke.heckeLam chi m c‖ * (c : ℝ) ^ (-s.re)
        * ∏ p ∈ c.primeFactors,
            ‖(1 - Work.FIArea5.S16Hecke.heckeLam chi m p * (p : ℂ) ^ (-s))⁻¹‖ := hnorm
    _ ≤ (∏ p ∈ c.primeFactors, (2 : ℝ)) * (∏ p ∈ c.primeFactors, ((p : ℝ))⁻¹)
        * ∏ p ∈ c.primeFactors, (1 + 4 * (p : ℝ) ^ (-(3 / 4 : ℝ))) := by
        refine mul_le_mul (mul_le_mul hlam (le_trans hcv (le_of_eq hcinv)) ?_ ?_) hloc
          (Finset.prod_nonneg (fun p _ => norm_nonneg _)) ?_
        · exact Real.rpow_nonneg (le_of_lt hcR) _
        · positivity
        · positivity
    _ = ∏ p ∈ c.primeFactors, QfacW Pa p := by
        rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
        exact Finset.prod_congr rfl hW

/-- **The summed bound at `re s ≥ 1`.**  The Euler product of the local weights
`QfacW Pa p = 2(1+4p^{-3/4})/p` over the primes `p > Pz` is `≪ (1 + log C/log Pz)²`, uniformly in
`Pa`: all the number theory is in `zcub_Qfac_prod_le`. -/
lemma QfacSumBound :
    ∃ K : ℝ, 0 < K ∧ ∀ Pa : Work.FITop.Params, 4 ≤ Real.log (Pa.Pz : ℝ) → 1 ≤ Pa.C →
      ∑ c ∈ QfacS Pa, ∏ p ∈ c.primeFactors, QfacW Pa p
        ≤ K * (1 + Real.log Pa.C / Real.log (Pa.Pz : ℝ)) ^ (2 : ℕ) := by
  obtain ⟨K₀, hK₀pos, hK₀⟩ := zcub_Qfac_prod_le
  refine ⟨K₀, hK₀pos, ?_⟩
  intro Pa hlogPz hC1
  set M : ℕ := ⌊Pa.C⌋₊ with hM
  have hCpos : (0 : ℝ) < Pa.C := lt_of_lt_of_le zero_lt_one hC1
  have hC1' : (1 : ℝ) ≤ Pa.C := hC1
  have hM1 : 1 ≤ M := Nat.le_floor (by exact_mod_cast hC1)
  have hMle : (M : ℝ) ≤ Pa.C := Nat.floor_le (le_of_lt hCpos)
  -- (1) enlarge the sum to all squarefree `c ≤ C`
  have hsub : QfacS Pa ⊆ (Finset.Icc 1 M).filter Squarefree := by
    intro c hc
    rw [QfacS, Finset.mem_filter] at hc
    exact Finset.mem_filter.mpr ⟨by rw [hM]; exact hc.1, hc.2.1⟩
  have hstep1 : ∑ c ∈ QfacS Pa, ∏ p ∈ c.primeFactors, QfacW Pa p
      ≤ ∑ c ∈ (Finset.Icc 1 M).filter Squarefree, ∏ p ∈ c.primeFactors, QfacW Pa p :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun c _ _ => Finset.prod_nonneg (fun p _ => QfacW_nonneg Pa p))
  -- (2) expand the Euler product
  have hstep2 : ∑ c ∈ (Finset.Icc 1 M).filter Squarefree, ∏ p ∈ c.primeFactors, QfacW Pa p
      ≤ ∏ p ∈ Nat.primesBelow (M + 1), (1 + QfacW Pa p) :=
    QfacProdExpand M (QfacW Pa) (QfacW_nonneg Pa)
  -- (3) drop the primes `p ≤ Pz`, where the weight vanishes
  have hstep3 : ∏ p ∈ Nat.primesBelow (M + 1), (1 + QfacW Pa p)
      = ∏ p ∈ (Nat.primesBelow (M + 1)).filter (fun p => Pa.Pz < p),
          (1 + 2 * (1 + 4 * (p : ℝ) ^ (-(3 / 4 : ℝ))) / (p : ℝ)) := by
    rw [← Finset.prod_filter_mul_prod_filter_not (s := Nat.primesBelow (M + 1))
      (p := fun p => Pa.Pz < p) (f := fun p => 1 + QfacW Pa p)]
    have h1 : ∏ p ∈ (Nat.primesBelow (M + 1)).filter (fun p => ¬ (Pa.Pz < p)),
        (1 + QfacW Pa p) = 1 := by
      apply Finset.prod_eq_one
      intro p hp
      rw [Finset.mem_filter] at hp
      rw [QfacW, if_neg hp.2, add_zero]
    rw [h1, mul_one]
    apply Finset.prod_congr rfl
    intro p hp
    rw [Finset.mem_filter] at hp
    rw [QfacW, if_pos hp.2]
  -- (4) the Mertens/Euler-product estimate
  have hstep4 := hK₀ Pa.Pz M hlogPz
  -- (5) replace `log M` by `log C`
  have hlogM : Real.log (M : ℝ) ≤ Real.log Pa.C := by
    refine Real.log_le_log ?_ hMle
    have : (0 : ℝ) < (M : ℝ) := by
      have : (0 : ℕ) < M := by omega
      exact_mod_cast this
    exact this
  have hlogPzpos : (0 : ℝ) < Real.log (Pa.Pz : ℝ) := by linarith
  have hlogMnn : 0 ≤ Real.log (M : ℝ) := Real.log_nonneg (by exact_mod_cast hM1)
  have hratio : Real.log (M : ℝ) / Real.log (Pa.Pz : ℝ)
      ≤ Real.log Pa.C / Real.log (Pa.Pz : ℝ) :=
    div_le_div_of_nonneg_right hlogM (le_of_lt hlogPzpos)
  have hbase : (1 : ℝ) ≤ 1 + Real.log (M : ℝ) / Real.log (Pa.Pz : ℝ) := by
    have := div_nonneg hlogMnn (le_of_lt hlogPzpos)
    linarith
  have hsq : (1 + Real.log (M : ℝ) / Real.log (Pa.Pz : ℝ)) ^ (2 : ℕ)
      ≤ (1 + Real.log Pa.C / Real.log (Pa.Pz : ℝ)) ^ (2 : ℕ) :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  calc ∑ c ∈ QfacS Pa, ∏ p ∈ c.primeFactors, QfacW Pa p
      ≤ ∑ c ∈ (Finset.Icc 1 M).filter Squarefree, ∏ p ∈ c.primeFactors, QfacW Pa p := hstep1
    _ ≤ ∏ p ∈ Nat.primesBelow (M + 1), (1 + QfacW Pa p) := hstep2
    _ = ∏ p ∈ (Nat.primesBelow (M + 1)).filter (fun p => Pa.Pz < p),
          (1 + 2 * (1 + 4 * (p : ℝ) ^ (-(3 / 4 : ℝ))) / (p : ℝ)) := hstep3
    _ ≤ K₀ * (1 + Real.log (M : ℝ) / Real.log (Pa.Pz : ℝ)) ^ (2 : ℕ) := hstep4
    _ ≤ K₀ * (1 + Real.log Pa.C / Real.log (Pa.Pz : ℝ)) ^ (2 : ℕ) :=
        mul_le_mul_of_nonneg_left hsq (le_of_lt hK₀pos)

/-- **The final bookkeeping step.**  `(1 + log C/log Pz)² ≤ C^{σ-1}(1 + log(C+2)/log Pz)²` for
`C ≥ 1`, `log Pz > 0` and `σ ≥ 1`: the factor `C^{σ-1}` is `≥ 1` and `log C ≤ log(C+2)`. -/
lemma QfacRatioLogStep (Pa : Work.FITop.Params) (s : ℂ) (hC : 1 ≤ Pa.C)
    (hlog : 0 < Real.log (Pa.Pz : ℝ)) (h1 : 1 ≤ s.re) :
    (1 + Real.log Pa.C / Real.log (Pa.Pz : ℝ)) ^ (2 : ℕ)
      ≤ Pa.C ^ (s.re - 1)
        * (1 + Real.log (Pa.C + 2) / Real.log (Pa.Pz : ℝ)) ^ (2 : ℕ) := by
  have hCpos : (0 : ℝ) < Pa.C := lt_of_lt_of_le zero_lt_one hC
  have hlogC : 0 ≤ Real.log Pa.C := Real.log_nonneg hC
  have hlogC2 : Real.log Pa.C ≤ Real.log (Pa.C + 2) :=
    Real.log_le_log hCpos (by linarith)
  have hlog2nn : 0 ≤ Real.log (Pa.C + 2) := le_trans hlogC hlogC2
  have hmono : Real.log Pa.C / Real.log (Pa.Pz : ℝ)
      ≤ Real.log (Pa.C + 2) / Real.log (Pa.Pz : ℝ) :=
    div_le_div_of_nonneg_right hlogC2 (le_of_lt hlog)
  have hbase : (1 : ℝ) ≤ 1 + Real.log Pa.C / Real.log (Pa.Pz : ℝ) := by
    have := div_nonneg hlogC (le_of_lt hlog)
    linarith
  have hsq : (1 + Real.log Pa.C / Real.log (Pa.Pz : ℝ)) ^ (2 : ℕ)
      ≤ (1 + Real.log (Pa.C + 2) / Real.log (Pa.Pz : ℝ)) ^ (2 : ℕ) :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  have hone : (1 : ℝ) ≤ Pa.C ^ (s.re - 1) :=
    Real.one_le_rpow hC (by linarith)
  calc (1 + Real.log Pa.C / Real.log (Pa.Pz : ℝ)) ^ (2 : ℕ)
      ≤ (1 + Real.log (Pa.C + 2) / Real.log (Pa.Pz : ℝ)) ^ (2 : ℕ) := hsq
    _ ≤ Pa.C ^ (s.re - 1)
        * (1 + Real.log (Pa.C + 2) / Real.log (Pa.Pz : ℝ)) ^ (2 : ℕ) :=
        le_mul_of_one_le_left (by positivity) hone

end

theorem QfacBoundRatioGeOne :
    ∃ K : ℝ, 0 < K ∧ ∀ (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (m : ℤ),
      chi 1 = 1 → (∀ z w : GaussianInt, chi (z * w) = chi z * chi w) →
      (∀ z : GaussianInt, ‖chi z‖ ≤ 1) → 1 ≤ Pa.C → 4 ≤ Real.log (Pa.Pz : ℝ) →
      ∀ s : ℂ, 1 ≤ s.re → 1 - 1 / Real.log (Pa.Pz : ℝ) ≤ s.re → s.re ≤ 2 →
        ‖Work.FIArea6.TauPieces.Qfac Pa chi m s‖
          ≤ K * Pa.C ^ (s.re - 1)
            * (1 + Real.log (Pa.C + 2) / Real.log (Pa.Pz : ℝ)) ^ (2 : ℕ) := by
  obtain ⟨K, hKpos, hK⟩ := QfacSumBound
  refine ⟨K, hKpos, ?_⟩
  intro Pa chi m hchi1 hchimul hchi hC1 hlogPz s h1re hr hle2
  have hlogpos : 0 < Real.log (Pa.Pz : ℝ) := by linarith
  rw [Qfac_eq_sum]
  calc ‖∑ c ∈ QfacS Pa, QfacTerm chi m s c‖
      ≤ ∑ c ∈ QfacS Pa, ‖QfacTerm chi m s c‖ := norm_sum_le _ _
    _ ≤ ∑ c ∈ QfacS Pa, ∏ p ∈ c.primeFactors, QfacW Pa p :=
        Finset.sum_le_sum
          (fun c hc => QfacTermNormLe Pa chi m hchi1 hchimul hchi hlogPz h1re hc)
    _ ≤ K * (1 + Real.log Pa.C / Real.log (Pa.Pz : ℝ)) ^ (2 : ℕ) := hK Pa hlogPz hC1
    _ ≤ K * (Pa.C ^ (s.re - 1)
          * (1 + Real.log (Pa.C + 2) / Real.log (Pa.Pz : ℝ)) ^ (2 : ℕ)) :=
        mul_le_mul_of_nonneg_left (QfacRatioLogStep Pa s hC1 hlogpos h1re) (le_of_lt hKpos)
    _ = K * Pa.C ^ (s.re - 1)
          * (1 + Real.log (Pa.C + 2) / Real.log (Pa.Pz : ℝ)) ^ (2 : ℕ) := by ring

end Work.FIArea6Road
