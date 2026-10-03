import Mathlib
import Submission.Work.FIArea6Road.ZcontAux
import Submission.Work.FIArea6Road.ZprodRegroup
import Submission.Work.FIArea6Road.PhifacIdent
import Submission.Work.FIArea6Road.PhifacAnalyticBound
import Submission.Work.FIArea6Road.PhifacBoundUniform
import Submission.Work.FIArea6Road.PfacSharpZT
import Submission.Work.FIArea6Road.ZcontPQBound
import Submission.Commons.NumberTheory.Chebyshev.sum_prime_inv_le_log_log_add
import Submission.Commons.NumberTheory.Chebyshev.sum_primes_rpow_tail_le
import Submission.Work.FIArea5.S16Hecke.Basic
import Submission.Work.FIArea5.S16Hecke.heckeLam_one
import Submission.Work.FIArea5.S16Hecke.heckeLam_prime_norm_le_two
import Submission.Work.FIArea5.S16Hecke.heckeLam_prime_eq_zero_of_ne_one_mod_four
import Submission.Commons.NumberTheory.Mertens.primeRecips_sub_loglog_bound_ge_three

namespace Work.FIArea6Road

open Finset
open scoped BigOperators Topology

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## The sharp, `Pa`-uniform bound for the truncation sum `Q(s)` (*FI* (16.34))

`Q(s) = Σ_{c ≤ C, (c,Π)=1} λ(c)c^{-s}∏_{p|c}(1-λ(p)p^{-s})^{-1}` with `Π = ∏_{p ≤ Pz}p`.
Every summand is supported on `c` all of whose prime factors exceed `Pz`, so only primes `≥ Pz`
occur; `‖λ(c)‖ = ∏_{p|c}‖λ(p)‖ ≤ 2^{ω(c)}` by multiplicativity of the Hecke eigenvalue, each local
inverse factor is `≤ locBnd p ≤ 1 + 4p^{-3/4}`, and `c^{-σ} ≤ c^{-1}C^{1-σ}`.  Hence
`‖Q(s)‖ ≤ C^{1-σ}∏_{Pz<p≤M}(1 + 2(1+4p^{-3/4})/p)`, `M = ⌊C⌋`, and that Euler product is
`≪ (1 + log M/log Pz)²` by the two-sided Mertens theorem. -/

/-- The sum over squarefree `c ≤ M` of `∏_{p | c} g p` is bounded by the full Euler product
`∏_{p ≤ M}(1 + g p)`, by expanding the latter and discarding the terms with `c > M`.  (Own copy of
this elementary expansion, so that the file does not depend on a module that may change.) -/
lemma zcub_prod_expand (M : ℕ) (g : ℕ → ℝ) (hg : ∀ p, 0 ≤ g p) :
    (∑ c ∈ (Finset.Icc 1 M).filter Squarefree, ∏ p ∈ c.primeFactors, g p)
      ≤ ∏ p ∈ Nat.primesBelow (M + 1), (1 + g p) := by
  classical
  rw [Finset.prod_one_add]
  set S : Finset ℕ := (Finset.Icc 1 M).filter Squarefree with hS
  have hinj : Set.InjOn Nat.primeFactors (↑S : Set ℕ) := by
    intro a ha b hb hab
    have haS : a ∈ S := Finset.mem_coe.mp ha
    have hbS : b ∈ S := Finset.mem_coe.mp hb
    rw [hS] at haS hbS
    have hsa : Squarefree a := (Finset.mem_filter.mp haS).2
    have hsb : Squarefree b := (Finset.mem_filter.mp hbS).2
    have h : (∏ p ∈ a.primeFactors, p) = (∏ p ∈ b.primeFactors, p) := by rw [hab]
    rwa [Nat.prod_primeFactors_of_squarefree hsa,
      Nat.prod_primeFactors_of_squarefree hsb] at h
  have hL : (∑ c ∈ S, ∏ p ∈ c.primeFactors, g p)
      = ∑ t ∈ S.image Nat.primeFactors, ∏ p ∈ t, g p :=
    (Finset.sum_image (s := S) (g := Nat.primeFactors)
      (f := fun t : Finset ℕ => ∏ p ∈ t, g p) hinj).symm
  rw [hL]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro t ht
    rw [hS, Finset.mem_image] at ht
    obtain ⟨c, hc, rfl⟩ := ht
    rw [Finset.mem_powerset]
    intro p hp
    have hcIcc : c ∈ Finset.Icc 1 M := (Finset.mem_filter.mp hc).1
    rw [Finset.mem_Icc] at hcIcc
    rw [Nat.mem_primesBelow]
    exact ⟨by have h := Nat.le_of_mem_primeFactors hp; omega,
      Nat.prime_of_mem_primeFactors hp⟩
  · intro t _ _
    exact Finset.prod_nonneg fun p _ => hg p

/-- `Nat.primesBelow (M+1) = Nat.primesLE M`. -/
lemma zcub_primesBelow_eq (M : ℕ) : Nat.primesBelow (M + 1) = Nat.primesLE M := by
  ext p
  rw [Nat.mem_primesBelow, Nat.mem_primesLE]
  exact ⟨fun h => ⟨by omega, h.2⟩, fun h => ⟨by omega, h.2⟩⟩

/-- Multiplicativity of the Hecke eigenvalue over the prime factors of a squarefree integer:
`λ(c) = ∏_{p | c} λ(p)`. -/
lemma zcub_heckeLam_prod_primeFactors (chi : GaussianInt → ℂ) (m : ℤ)
    (hchi1 : chi 1 = 1)
    (hchimul : ∀ z w : GaussianInt, chi (z * w) = chi z * chi w) {c : ℕ}
    (hsf : Squarefree c) :
    Work.FIArea5.S16Hecke.heckeLam chi m c
      = ∏ p ∈ c.primeFactors, Work.FIArea5.S16Hecke.heckeLam chi m p := by
  have hgen : ∀ s : Finset ℕ, (∀ p ∈ s, p.Prime) →
      Work.FIArea5.S16Hecke.heckeLam chi m (∏ p ∈ s, p)
        = ∏ p ∈ s, Work.FIArea5.S16Hecke.heckeLam chi m p := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [Work.FIArea5.S16Hecke.heckeLam_one, hchi1]
    | insert a s ha ih =>
        intro hP
        have haP : a.Prime := hP a (Finset.mem_insert_self a s)
        have hPs : ∀ p ∈ s, p.Prime := fun p hp => hP p (Finset.mem_insert_of_mem hp)
        have hcop : Nat.Coprime a (∏ p ∈ s, p) := by
          rw [Nat.coprime_prod_right_iff]
          intro p hp
          rw [haP.coprime_iff_not_dvd]
          intro hdvd
          have hpe : p = a := ((hPs p hp).dvd_iff_eq haP.ne_one).mp hdvd
          exact ha (hpe ▸ hp)
        rw [Finset.prod_insert ha, Finset.prod_insert ha,
          Work.FIArea5.S16Hecke.heckeLam_mul chi m hchimul haP.pos
            (Finset.prod_pos fun p hp => (hPs p hp).pos) hcop, ih hPs]
  have h := hgen c.primeFactors (fun p hp => Nat.prime_of_mem_primeFactors hp)
  rwa [Nat.prod_primeFactors_of_squarefree hsf] at h

/-- The Euler product `∏_{Pz < p ≤ M} (1 + 2(1+4p^{-3/4})/p) ≪ (1 + log M/log Pz)²`, uniformly in
`Pz ≥ e⁴` and `M`.  The two-sided Mertens theorem
(`Commons.NumberTheory.Mertens.primeRecips_sub_loglog_bound_ge_three`) gives
`Σ_{Pz<p≤M}1/p ≤ log log(M/Pz) + O(1)`. -/
lemma zcub_Qfac_prod_le :
    ∃ K : ℝ, 0 < K ∧ ∀ (Pz M : ℕ), 4 ≤ Real.log (Pz : ℝ) →
      (∏ p ∈ (Nat.primesBelow (M + 1)).filter (fun p => Pz < p),
          (1 + 2 * (1 + 4 * (p : ℝ) ^ (-(3 / 4 : ℝ))) / (p : ℝ)))
        ≤ K * (1 + Real.log (M : ℝ) / Real.log (Pz : ℝ)) ^ (2 : ℕ) := by
  obtain ⟨CM, hCMpos, hM⟩ :=
    Commons.NumberTheory.Mertens.primeRecips_sub_loglog_bound_ge_three
  set T : ℝ := (32 : ℝ) / ((3 / 4) * Real.log 2) with hTdef
  have hTpos : 0 < T := by
    rw [hTdef]
    exact div_pos (by norm_num)
      (mul_pos (by norm_num) (Real.log_pos (by norm_num : (1 : ℝ) < 2)))
  refine ⟨Real.exp (4 * CM + 8 * T) + 1, by positivity, ?_⟩
  intro Pz M hPz
  have hlogPz : (0 : ℝ) < Real.log (Pz : ℝ) := by linarith
  have hPz3 : 3 ≤ Pz := by
    by_contra h
    have hle : (Pz : ℝ) ≤ 3 := by exact_mod_cast (by omega : Pz ≤ 3)
    have hlog3 : Real.log (Pz : ℝ) ≤ Real.log 3 := by
      rcases Nat.eq_zero_or_pos Pz with h0 | hpos
      · simp [h0]
        exact Real.log_nonneg (by norm_num)
      · exact Real.log_le_log (by exact_mod_cast hpos) hle
    have h34 : Real.log 3 < 4 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num)
      linarith
    linarith
  by_cases hcase : M ≤ Pz
  · -- the product is empty
    have hemp : (Nat.primesBelow (M + 1)).filter (fun p => Pz < p) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro p hp
      rw [Nat.mem_primesBelow] at hp
      omega
    rw [hemp, Finset.prod_empty]
    have hMnn : (0 : ℝ) ≤ Real.log (M : ℝ) := by
      rcases Nat.eq_zero_or_pos M with h0 | hpos
      · simp [h0]
      · exact Real.log_nonneg (by exact_mod_cast hpos)
    have h1r : (1 : ℝ) ≤ 1 + Real.log (M : ℝ) / Real.log (Pz : ℝ) := by
      have := div_nonneg hMnn (le_of_lt hlogPz)
      linarith
    have h1 : (1 : ℝ) ≤ (1 + Real.log (M : ℝ) / Real.log (Pz : ℝ)) ^ (2 : ℕ) :=
      one_le_pow₀ h1r
    have hK1 : (1 : ℝ) ≤ Real.exp (4 * CM + 8 * T) + 1 := by
      linarith [Real.exp_pos (4 * CM + 8 * T)]
    nlinarith [h1, hK1]
  · have hPzM : Pz < M := not_le.mp hcase
    have hM3 : 3 ≤ M := by omega
    have hlogM : (0 : ℝ) < Real.log (M : ℝ) :=
      Real.log_pos (by exact_mod_cast (by omega : 1 < M))
    have hMertensM : (∑ p ∈ Nat.primesBelow (M + 1), (1 : ℝ) / (p : ℝ))
        ≤ Real.log (Real.log (M : ℝ)) + CM := by
      rw [zcub_primesBelow_eq M]
      have := (abs_le.mp (hM M hM3)).2
      linarith
    have hMertensPz : Real.log (Real.log (Pz : ℝ)) - CM
        ≤ ∑ p ∈ Nat.primesBelow (Pz + 1), (1 : ℝ) / (p : ℝ) := by
      rw [zcub_primesBelow_eq Pz]
      have := (abs_le.mp (hM Pz hPz3)).1
      linarith
    have hsub : Nat.primesBelow (Pz + 1) ⊆ Nat.primesBelow (M + 1) := by
      intro p hp
      rw [Nat.mem_primesBelow] at hp
      exact Nat.mem_primesBelow.mpr ⟨by omega, hp.2⟩
    have hset : (Nat.primesBelow (M + 1)).filter (fun p => Pz < p)
        = Nat.primesBelow (M + 1) \ Nat.primesBelow (Pz + 1) := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_sdiff, Nat.mem_primesBelow]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨⟨h1, h2⟩, fun h => by omega⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩
        have h4 : ¬ (p < Pz + 1) := fun h => h3 ⟨h, h2⟩
        exact ⟨⟨h1, h2⟩, by omega⟩
    have hsum1 : ∑ p ∈ (Nat.primesBelow (M + 1)).filter (fun p => Pz < p), (1 : ℝ) / (p : ℝ)
        = (∑ p ∈ Nat.primesBelow (M + 1), (1 : ℝ) / (p : ℝ))
          - ∑ p ∈ Nat.primesBelow (Pz + 1), (1 : ℝ) / (p : ℝ) := by
      rw [hset]
      have h := Finset.sum_sdiff hsub (f := fun p : ℕ => (1 : ℝ) / (p : ℝ))
      linarith
    have hlogdiv : Real.log (Real.log (M : ℝ)) - Real.log (Real.log (Pz : ℝ))
        = Real.log (Real.log (M : ℝ) / Real.log (Pz : ℝ)) :=
      (Real.log_div (ne_of_gt hlogM) (ne_of_gt hlogPz)).symm
    have hsum_inv : ∑ p ∈ (Nat.primesBelow (M + 1)).filter (fun p => Pz < p), (1 : ℝ) / (p : ℝ)
        ≤ Real.log (Real.log (M : ℝ) / Real.log (Pz : ℝ)) + 2 * CM := by
      rw [hsum1]
      have := sub_le_sub hMertensM hMertensPz
      linarith
    have hexp7 : ∀ p : ℕ, (p : ℝ) ^ (-(7 / 4 : ℝ)) = (p : ℝ) ^ (-(1 + (3 : ℝ) / 4)) := by
      intro p
      congr 1
      norm_num
    have hsum_tail : ∑ p ∈ (Nat.primesBelow (M + 1)).filter (fun p => Pz < p),
        (p : ℝ) ^ (-(7 / 4 : ℝ)) ≤ T := by
      rw [hTdef, Finset.sum_congr rfl (fun p _ => hexp7 p)]
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_)
        (Commons.NumberTheory.Chebyshev.sum_primes_rpow_tail_le (3 / 4) 2 M
          (by norm_num) (by norm_num) (by norm_num))
      · intro p hp
        rw [Finset.mem_filter, Nat.mem_primesBelow] at hp
        rw [Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨by omega, by omega⟩, hp.1.2⟩
      · intro p _ _
        positivity
    have hsum_tail' : ∑ p ∈ (Nat.primesBelow (M + 1)).filter (fun p => Pz < p),
        8 * (p : ℝ) ^ (-(7 / 4 : ℝ)) ≤ 8 * T := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left hsum_tail (by norm_num)
    have hsum_expo : ∑ p ∈ (Nat.primesBelow (M + 1)).filter (fun p => Pz < p),
        (2 * (1 + 4 * (p : ℝ) ^ (-(3 / 4 : ℝ))) / (p : ℝ))
        ≤ 2 * Real.log (Real.log (M : ℝ) / Real.log (Pz : ℝ)) + (4 * CM + 8 * T) := by
      have hpne : ∀ p ∈ (Nat.primesBelow (M + 1)).filter (fun p => Pz < p), (p : ℝ) ≠ 0 := by
        intro p hp
        rw [Finset.mem_filter, Nat.mem_primesBelow] at hp
        exact_mod_cast (by omega : p ≠ 0)
      have hterm : ∀ p ∈ (Nat.primesBelow (M + 1)).filter (fun p => Pz < p),
          (2 * (1 + 4 * (p : ℝ) ^ (-(3 / 4 : ℝ))) / (p : ℝ))
            = 2 * ((1 : ℝ) / (p : ℝ)) + 8 * (p : ℝ) ^ (-(7 / 4 : ℝ)) := by
        intro p hp
        have hp0 : (0 : ℝ) < (p : ℝ) := by
          have := hpne p hp
          positivity
        have hrw : (p : ℝ) ^ (-(7 / 4 : ℝ))
            = (p : ℝ) ^ (-(3 / 4 : ℝ)) * (p : ℝ)⁻¹ := by
          rw [← Real.rpow_neg_one (p : ℝ), ← Real.rpow_add hp0]
          congr 1
          norm_num
        rw [hrw]
        field_simp
        ring
      rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.mul_sum]
      have h2 : 2 * (∑ p ∈ (Nat.primesBelow (M + 1)).filter (fun p => Pz < p), (1 : ℝ) / (p : ℝ))
          ≤ 2 * (Real.log (Real.log (M : ℝ) / Real.log (Pz : ℝ)) + 2 * CM) :=
        mul_le_mul_of_nonneg_left hsum_inv (by norm_num)
      linarith [h2, hsum_tail']
    have hprod := Real.prod_one_add_le_exp_sum
      ((Nat.primesBelow (M + 1)).filter (fun p => Pz < p))
      (f := fun p : ℕ => 2 * (1 + 4 * (p : ℝ) ^ (-(3 / 4 : ℝ))) / (p : ℝ))
      (fun p => by positivity)
    have hEpos : 0 < Real.exp (4 * CM + 8 * T) := Real.exp_pos _
    have hr : (0 : ℝ) < Real.log (M : ℝ) / Real.log (Pz : ℝ) := div_pos hlogM hlogPz
    have hfinal : Real.exp (2 * Real.log (Real.log (M : ℝ) / Real.log (Pz : ℝ)) + (4 * CM + 8 * T))
        ≤ (Real.exp (4 * CM + 8 * T) + 1)
          * (1 + Real.log (M : ℝ) / Real.log (Pz : ℝ)) ^ (2 : ℕ) := by
      have hexp : Real.exp (2 * Real.log (Real.log (M : ℝ) / Real.log (Pz : ℝ)) + (4 * CM + 8 * T))
          = (Real.log (M : ℝ) / Real.log (Pz : ℝ)) ^ (2 : ℕ) * Real.exp (4 * CM + 8 * T) := by
        rw [Real.exp_add, show Real.exp (2 * Real.log (Real.log (M : ℝ) / Real.log (Pz : ℝ)))
            = (Real.log (M : ℝ) / Real.log (Pz : ℝ)) ^ (2 : ℕ) by
          rw [show (2 : ℝ) * Real.log (Real.log (M : ℝ) / Real.log (Pz : ℝ))
              = ((2 : ℕ) : ℝ) * Real.log (Real.log (M : ℝ) / Real.log (Pz : ℝ)) by norm_num,
            Real.exp_nat_mul, Real.exp_log hr]]
      rw [hexp]
      have hsq : (Real.log (M : ℝ) / Real.log (Pz : ℝ)) ^ (2 : ℕ)
          ≤ (1 + Real.log (M : ℝ) / Real.log (Pz : ℝ)) ^ (2 : ℕ) :=
        pow_le_pow_left₀ (le_of_lt hr) (by linarith) 2
      have hE : Real.exp (4 * CM + 8 * T) ≤ Real.exp (4 * CM + 8 * T) + 1 := by linarith
      have hbig : (0 : ℝ) ≤ (1 + Real.log (M : ℝ) / Real.log (Pz : ℝ)) ^ (2 : ℕ) :=
        pow_nonneg (by linarith) 2
      nlinarith [hsq, hE, hEpos, hbig, pow_nonneg (le_of_lt hr) 2]
    refine le_trans hprod ?_
    exact le_trans (Real.exp_le_exp.mpr hsum_expo) hfinal

/-- For a prime `p ≥ 7` the local majorant `locBnd p = (1-2p^{-3/4})^{-1}` is at most
`1 + 4p^{-3/4}`. -/
lemma zcub_locBnd_le {p : ℕ} (hp : 7 ≤ p) :
    Work.FIArea6Road.locBnd p ≤ 1 + 4 * (p : ℝ) ^ (-(3 / 4 : ℝ)) := by
  have hpR : (7 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp2 : ¬ p ≤ 2 := by omega
  have h4 : (4 : ℝ) ≤ (7 : ℝ) ^ ((3 : ℝ) / 4) := by
    have h : (4 : ℝ) ^ 4 ≤ ((7 : ℝ) ^ ((3 : ℝ) / 4)) ^ 4 := by
      rw [show ((7 : ℝ) ^ ((3 : ℝ) / 4)) ^ 4 = (7 : ℝ) ^ 3 by
        rw [← Real.rpow_natCast ((7 : ℝ) ^ ((3 : ℝ) / 4)) 4,
          ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 7)]
        norm_num]
      norm_num
    exact (pow_le_pow_iff_left₀ (by norm_num : (0 : ℝ) ≤ 4) (by positivity)
      (by norm_num : (4 : ℕ) ≠ 0)).mp h
  have hpw : (p : ℝ) ^ (-(3 / 4 : ℝ)) ≤ (7 : ℝ) ^ (-(3 / 4 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) hpR (by norm_num)
  have h7neg : (7 : ℝ) ^ (-(3 / 4 : ℝ)) = ((7 : ℝ) ^ ((3 : ℝ) / 4))⁻¹ := by
    rw [show -(3 / 4 : ℝ) = -((3 : ℝ) / 4) by norm_num,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 7)]
  have hu : (p : ℝ) ^ (-(3 / 4 : ℝ)) ≤ 1 / 4 := by
    rw [h7neg] at hpw
    have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4) h4
    have h' : ((7 : ℝ) ^ ((3 : ℝ) / 4))⁻¹ = 1 / ((7 : ℝ) ^ ((3 : ℝ) / 4)) := (one_div _).symm
    linarith [hpw, h, h']
  have hx2 : 2 * (p : ℝ) ^ (-(3 / 4 : ℝ)) ≤ 1 / 2 := by linarith
  have hpos : 0 < 1 - 2 * (p : ℝ) ^ (-(3 / 4 : ℝ)) := by linarith
  have hu0 : 0 ≤ (p : ℝ) ^ (-(3 / 4 : ℝ)) := Real.rpow_nonneg (by positivity) _
  rw [Work.FIArea6Road.locBnd, if_neg hp2, inv_le_iff_one_le_mul₀ hpos]
  nlinarith [hu, hx2, hu0, sq_nonneg ((p : ℝ) ^ (-(3 / 4 : ℝ)))]

/-- ***(FI)* (16.34) with a `Pa`-independent constant.**  On `3/4 ≤ σ ≤ 1` (together with the
region hypothesis `σ ≥ 1 - 1/log Pz`) the truncation sum
`Q(s) = Σ_{c ≤ C,(c,Π)=1}λ(c)c^{-s}∏_{p|c}(1-λ(p)p^{-s})^{-1}` satisfies
`‖Q(s)‖ ≤ K·C^{1-σ}·(1 + log(C+2)/log Pz)²`, `K` absolute. -/
theorem zcub_QfacBoundUniformRatio :
    ∃ K : ℝ, 0 < K ∧ ∀ (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (m : ℤ),
      chi 1 = 1 → (∀ z w : GaussianInt, chi (z * w) = chi z * chi w) →
      (∀ z : GaussianInt, ‖chi z‖ ≤ 1) → 1 ≤ Pa.C → 4 ≤ Real.log (Pa.Pz : ℝ) →
      ∀ s : ℂ, (3 : ℝ) / 4 ≤ s.re → 1 - 1 / Real.log (Pa.Pz : ℝ) ≤ s.re → s.re ≤ 1 →
        ‖Work.FIArea6.TauPieces.Qfac Pa chi m s‖
          ≤ K * Pa.C ^ (1 - s.re)
            * (1 + Real.log (Pa.C + 2) / Real.log (Pa.Pz : ℝ)) ^ (2 : ℕ) := by
  obtain ⟨K₁, hK₁pos, hK₁⟩ := zcub_Qfac_prod_le
  refine ⟨K₁, hK₁pos, ?_⟩
  intro Pa chi m hchi1 hchimul hchi hC1 hlogPz s h34 hr hle1
  set M : ℕ := ⌊Pa.C⌋₊ with hMdef
  set Pr : ℕ := ∏ p ∈ Nat.primesBelow (Pa.Pz + 1), p with hPrdef
  set g : ℕ → ℝ := fun p => if Pa.Pz < p then 2 * (1 + 4 * (p : ℝ) ^ (-(3 / 4 : ℝ))) / (p : ℝ) else 0
    with hgdef
  have hCpos : (0 : ℝ) < Pa.C := lt_of_lt_of_le zero_lt_one hC1
  have hMle : (M : ℝ) ≤ Pa.C := Nat.floor_le (le_of_lt hCpos)
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
  have hprime_gt : ∀ {c : ℕ}, c ∈ (Finset.Icc 1 M).filter
      (fun c => Squarefree c ∧ Nat.Coprime c Pr) → ∀ p ∈ c.primeFactors, Pa.Pz < p := by
    intro c hc p hp
    have hccop : Nat.Coprime c Pr := (Finset.mem_filter.mp hc).2.2
    have hpp : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
    have hpdvd : p ∣ c := (Nat.mem_primeFactors.mp hp).2.1
    by_contra hle
    have hple : p ≤ Pa.Pz := not_lt.mp hle
    have hmem : p ∈ Nat.primesBelow (Pa.Pz + 1) := by
      rw [Nat.mem_primesBelow]
      exact ⟨by omega, hpp⟩
    have hdvdPr : p ∣ Pr := by
      rw [hPrdef]
      exact Finset.dvd_prod_of_mem (fun q : ℕ => q) hmem
    have hgcd : p ∣ Nat.gcd c Pr := Nat.dvd_gcd hpdvd hdvdPr
    rw [hccop.gcd_eq_one] at hgcd
    exact hpp.not_dvd_one hgcd
  -- the pointwise bound for a summand
  have hterm : ∀ c ∈ (Finset.Icc 1 M).filter
      (fun c => Squarefree c ∧ Nat.Coprime c Pr),
      ‖Work.FIArea5.S16Hecke.heckeLam chi m c * (c : ℂ) ^ (-s)
        * ∏ p ∈ c.primeFactors,
            (1 - Work.FIArea5.S16Hecke.heckeLam chi m p * (p : ℂ) ^ (-s))⁻¹‖
        ≤ Pa.C ^ (1 - s.re) * ∏ p ∈ c.primeFactors, g p := by
    intro c hc
    have hcIcc : c ∈ Finset.Icc 1 M := (Finset.mem_filter.mp hc).1
    have hcsf : Squarefree c := (Finset.mem_filter.mp hc).2.1
    have hc1 : 1 ≤ c := (Finset.mem_Icc.mp hcIcc).1
    have hc0 : 0 < c := by omega
    have hcR : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc0
    have hnorm : ‖Work.FIArea5.S16Hecke.heckeLam chi m c * (c : ℂ) ^ (-s)
        * ∏ p ∈ c.primeFactors,
            (1 - Work.FIArea5.S16Hecke.heckeLam chi m p * (p : ℂ) ^ (-s))⁻¹‖
        = ‖Work.FIArea5.S16Hecke.heckeLam chi m c‖ * (c : ℝ) ^ (-s.re)
          * ∏ p ∈ c.primeFactors,
              ‖(1 - Work.FIArea5.S16Hecke.heckeLam chi m p * (p : ℂ) ^ (-s))⁻¹‖ := by
      rw [norm_mul, norm_mul, norm_prod, Complex.norm_natCast_cpow_of_pos hc0]
      simp [Complex.neg_re]
    have hlam : ‖Work.FIArea5.S16Hecke.heckeLam chi m c‖
        ≤ ∏ p ∈ c.primeFactors, ‖Work.FIArea5.S16Hecke.heckeLam chi m p‖ := by
      rw [zcub_heckeLam_prod_primeFactors chi m hchi1 hchimul hcsf, norm_prod]
    have hloc : ∏ p ∈ c.primeFactors,
          ‖(1 - Work.FIArea5.S16Hecke.heckeLam chi m p * (p : ℂ) ^ (-s))⁻¹‖
        ≤ ∏ p ∈ c.primeFactors, (1 + 4 * (p : ℝ) ^ (-(3 / 4 : ℝ))) := by
      refine Finset.prod_le_prod₀ (fun p _ => norm_nonneg _) ?_
      intro p hp
      have hpp : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
      have hloc1 := Work.FIArea6Road.locF_inv_bound chi m hchi hpp h34
      exact le_trans hloc1 (zcub_locBnd_le (by have := hprime_gt hc p hp; omega))
    have hcpow : (c : ℝ) ^ (-s.re) ≤ Pa.C ^ (1 - s.re) * ((c : ℝ))⁻¹ := by
      have hc1R : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc1
      have hcMe : (c : ℝ) ≤ Pa.C :=
        le_trans (by exact_mod_cast (Finset.mem_Icc.mp hcIcc).2) hMle
      rw [show -s.re = -1 + (1 - s.re) by ring, Real.rpow_add hcR, Real.rpow_neg_one]
      have h1 : (c : ℝ) ^ (1 - s.re) ≤ Pa.C ^ (1 - s.re) :=
        Real.rpow_le_rpow (le_of_lt hcR) hcMe (by linarith)
      have h2 : (0 : ℝ) ≤ ((c : ℝ))⁻¹ := by positivity
      calc ((c : ℝ))⁻¹ * (c : ℝ) ^ (1 - s.re)
          = (c : ℝ) ^ (1 - s.re) * ((c : ℝ))⁻¹ := by ring
        _ ≤ Pa.C ^ (1 - s.re) * ((c : ℝ))⁻¹ := mul_le_mul_of_nonneg_right h1 h2
    have hprodpc : (∏ p ∈ c.primeFactors, ((p : ℕ) : ℝ)) = (c : ℝ) := by
      rw [← Finset.prod_natCast, Nat.prod_primeFactors_of_squarefree hcsf]
    have hprodg : ((c : ℝ))⁻¹ * ∏ p ∈ c.primeFactors, (2 * (1 + 4 * (p : ℝ) ^ (-(3 / 4 : ℝ))))
        = ∏ p ∈ c.primeFactors, g p := by
      have hgw : ∀ p ∈ c.primeFactors, g p
          = 2 * (1 + 4 * (p : ℝ) ^ (-(3 / 4 : ℝ))) / (p : ℝ) := by
        intro p hp
        simp only [hgdef]
        rw [if_pos (hprime_gt hc p hp)]
      rw [Finset.prod_congr rfl hgw, Finset.prod_div_distrib, hprodpc]
      ring
    calc ‖Work.FIArea5.S16Hecke.heckeLam chi m c * (c : ℂ) ^ (-s)
          * ∏ p ∈ c.primeFactors,
              (1 - Work.FIArea5.S16Hecke.heckeLam chi m p * (p : ℂ) ^ (-s))⁻¹‖
        = ‖Work.FIArea5.S16Hecke.heckeLam chi m c‖ * (c : ℝ) ^ (-s.re)
          * ∏ p ∈ c.primeFactors,
              ‖(1 - Work.FIArea5.S16Hecke.heckeLam chi m p * (p : ℂ) ^ (-s))⁻¹‖ := hnorm
      _ ≤ (∏ p ∈ c.primeFactors, ‖Work.FIArea5.S16Hecke.heckeLam chi m p‖)
            * (c : ℝ) ^ (-s.re)
            * ∏ p ∈ c.primeFactors, (1 + 4 * (p : ℝ) ^ (-(3 / 4 : ℝ))) := by
          have hcσ : (0 : ℝ) ≤ (c : ℝ) ^ (-s.re) := Real.rpow_nonneg (le_of_lt hcR) _
          have h1 := mul_le_mul_of_nonneg_right hlam hcσ
          have h2 : (0 : ℝ) ≤ (∏ p ∈ c.primeFactors, ‖Work.FIArea5.S16Hecke.heckeLam chi m p‖)
              * (c : ℝ) ^ (-s.re) :=
            mul_nonneg (Finset.prod_nonneg fun p _ => norm_nonneg _) hcσ
          exact mul_le_mul h1 hloc (Finset.prod_nonneg fun p _ => norm_nonneg _) h2
      _ = (c : ℝ) ^ (-s.re)
            * ∏ p ∈ c.primeFactors,
                (‖Work.FIArea5.S16Hecke.heckeLam chi m p‖
                  * (1 + 4 * (p : ℝ) ^ (-(3 / 4 : ℝ)))) := by
          rw [Finset.prod_mul_distrib]
          ring
      _ ≤ (c : ℝ) ^ (-s.re)
            * ∏ p ∈ c.primeFactors, (2 * (1 + 4 * (p : ℝ) ^ (-(3 / 4 : ℝ)))) := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (le_of_lt hcR) _)
          refine Finset.prod_le_prod₀ (fun p _ => by positivity) ?_
          intro p hp
          have h2p : ‖Work.FIArea5.S16Hecke.heckeLam chi m p‖ ≤ 2 :=
            zcontHeckeLamPrimeNormLeTwo' chi m hchi (Nat.prime_of_mem_primeFactors hp)
          exact mul_le_mul_of_nonneg_right h2p (by positivity)
      _ ≤ Pa.C ^ (1 - s.re) * ((c : ℝ))⁻¹
            * ∏ p ∈ c.primeFactors, (2 * (1 + 4 * (p : ℝ) ^ (-(3 / 4 : ℝ)))) :=
          mul_le_mul_of_nonneg_right hcpow (Finset.prod_nonneg fun p _ => by positivity)
      _ = Pa.C ^ (1 - s.re) * ∏ p ∈ c.primeFactors, g p := by
          rw [← hprodg]
          ring
  -- sum over the squarefree `c` and use the Euler-product expansion
  rw [Work.FIArea6.TauPieces.Qfac]
  refine le_trans (norm_sum_le _ _) ?_
  have hSsub : (Finset.Icc 1 M).filter (fun c => Squarefree c ∧ Nat.Coprime c Pr)
      ⊆ (Finset.Icc 1 M).filter Squarefree := by
    intro c hc
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hc).1, (Finset.mem_filter.mp hc).2.1⟩
  have hge0 : ∀ c ∈ (Finset.Icc 1 M).filter Squarefree, 0 ≤ ∏ p ∈ c.primeFactors, g p :=
    fun c _ => Finset.prod_nonneg fun p _ => by simp only [hgdef]; split_ifs <;> positivity
  have hsum_le : ∑ c ∈ (Finset.Icc 1 M).filter (fun c => Squarefree c ∧ Nat.Coprime c Pr),
        ∏ p ∈ c.primeFactors, g p
      ≤ ∏ p ∈ (Nat.primesBelow (M + 1)).filter (fun p => Pa.Pz < p),
          (1 + 2 * (1 + 4 * (p : ℝ) ^ (-(3 / 4 : ℝ))) / (p : ℝ)) := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hSsub (fun c hc _ => hge0 c hc)) ?_
    refine le_trans (zcub_prod_expand M g
      (fun p => by simp only [hgdef]; split_ifs <;> positivity)) (le_of_eq ?_)
    rw [← Finset.prod_filter_mul_prod_filter_not (Nat.primesBelow (M + 1)) (fun p => Pa.Pz < p)]
    have hzero : (∏ p ∈ (Nat.primesBelow (M + 1)).filter (fun p => ¬ Pa.Pz < p),
        (1 + g p)) = 1 := by
      refine Finset.prod_eq_one ?_
      intro p hp
      rw [Finset.mem_filter] at hp
      simp only [hgdef]
      rw [if_neg hp.2, add_zero]
    rw [hzero, mul_one]
    refine Finset.prod_congr rfl ?_
    intro p hp
    rw [Finset.mem_filter] at hp
    simp only [hgdef]
    rw [if_pos hp.2]
  have hlogM1 : (1 : ℝ) ≤ (M : ℝ) := by
    have h1 : 1 ≤ M := Nat.succ_le_of_lt (Nat.floor_pos.mpr hC1)
    exact_mod_cast h1
  have hlogM_le : Real.log (M : ℝ) ≤ Real.log (Pa.C + 2) := by
    refine Real.log_le_log (by linarith) ?_
    linarith [hMle]
  have hnew : Pa.C ^ (1 - s.re) * ∑ c ∈ (Finset.Icc 1 M).filter
        (fun c => Squarefree c ∧ Nat.Coprime c Pr), ∏ p ∈ c.primeFactors, g p
      ≤ K₁ * Pa.C ^ (1 - s.re)
        * (1 + Real.log (Pa.C + 2) / Real.log (Pa.Pz : ℝ)) ^ (2 : ℕ) := by
    refine le_trans (mul_le_mul_of_nonneg_left hsum_le (Real.rpow_nonneg (le_of_lt hCpos) _)) ?_
    refine le_trans (mul_le_mul_of_nonneg_left (hK₁ Pa.Pz M hlogPz)
      (Real.rpow_nonneg (le_of_lt hCpos) _)) ?_
    have hx : (1 + Real.log (M : ℝ) / Real.log (Pa.Pz : ℝ)) ^ (2 : ℕ)
        ≤ (1 + Real.log (Pa.C + 2) / Real.log (Pa.Pz : ℝ)) ^ (2 : ℕ) := by
      refine pow_le_pow_left₀ (by positivity) ?_ 2
      have := div_le_div_of_nonneg_right hlogM_le (by linarith : (0 : ℝ) ≤ Real.log (Pa.Pz : ℝ))
      linarith
    calc Pa.C ^ (1 - s.re) * (K₁ * (1 + Real.log (M : ℝ) / Real.log (Pa.Pz : ℝ)) ^ (2 : ℕ))
        = K₁ * Pa.C ^ (1 - s.re)
            * (1 + Real.log (M : ℝ) / Real.log (Pa.Pz : ℝ)) ^ (2 : ℕ) := by ring
      _ ≤ K₁ * Pa.C ^ (1 - s.re)
            * (1 + Real.log (Pa.C + 2) / Real.log (Pa.Pz : ℝ)) ^ (2 : ℕ) := by
          refine mul_le_mul_of_nonneg_left hx ?_
          have := Real.rpow_nonneg (le_of_lt hCpos) (1 - s.re)
          nlinarith [hK₁pos]
  refine le_trans (le_trans (Finset.sum_le_sum hterm) ?_) hnew
  rw [← Finset.mul_sum]

/-! ## The `log`-bookkeeping

The three sharpened factors carry `log`-powers `2` (the `(Λ/arch)^{-1}` bound), `3` (the `P`-factor)
and `2` (the `Q`-factor).  Here they are absorbed into the single `log^6(N + |m| + |Im s| + 3)` of
the target.  The only arithmetic input from `Params` is `log Pz + 2 ≤ 900·L`, which comes from
`hPhi` (`log Pz ≤ log x/(loglog x)²`) together with `hNlo` (`N > x^{1/4+η}`), i.e. `log N > log x/4`,
and the crude `loglog x ≥ 0.07` valid for `x ≥ 3`. -/

/-- `log 3 ≥ 1.08`, from Mathlib's decimal bound `e < 2.7182818286`. -/
lemma zcub_log_three_ge : (1.08 : ℝ) ≤ Real.log 3 := by
  have he : Real.exp 1 < (2.7182818286 : ℝ) := Real.exp_one_lt_d9
  have h1 : (1.09 : ℝ) ≤ 3 / Real.exp 1 := by
    rw [le_div_iff₀ (Real.exp_pos 1)]
    nlinarith
  have h2 : Real.log (1.09 : ℝ) ≤ Real.log 3 - 1 := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 1.09) h1
    rw [Real.log_div (by norm_num) (ne_of_gt (Real.exp_pos 1)), Real.log_exp] at h
    linarith
  have h3 : 1 - (1.09 : ℝ)⁻¹ ≤ Real.log (1.09 : ℝ) :=
    Real.one_sub_inv_le_log_of_pos (by norm_num)
  linarith

/-- `log log x ≥ 0.07` for `x ≥ 3`. -/
lemma zcub_loglog_ge {x : ℝ} (hx : 3 ≤ x) : (0.07 : ℝ) ≤ Real.log (Real.log x) := by
  have hu : (1.08 : ℝ) ≤ Real.log x :=
    zcub_log_three_ge.trans (Real.log_le_log (by norm_num) hx)
  have hu0 : (0 : ℝ) < Real.log x := by linarith
  have h := Real.one_sub_inv_le_log_of_pos hu0
  have hinv : (Real.log x)⁻¹ ≤ 1 / 1.08 := by
    simpa [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1.08) hu
  linarith

/-- **`log Pz + 2 ≤ 900·log(N + |m| + |Im s| + 3)`**, uniformly in the set-up. -/
lemma zcub_logPz_add_two_le (Pa : Work.FITop.Params) (m : ℤ) (s : ℂ) :
    Real.log (Pa.Pz : ℝ) + 2
      ≤ 900 * Real.log (|(m : ℝ)| + |s.im| + (Pa.N : ℝ) + 3) := by
  have hx3 : (3 : ℝ) ≤ (Pa.x : ℝ) := by exact_mod_cast Pa.hx
  have hx0 : (0 : ℝ) < (Pa.x : ℝ) := by linarith
  have hu : (1.08 : ℝ) ≤ Real.log (Pa.x : ℝ) :=
    zcub_log_three_ge.trans (Real.log_le_log (by norm_num) hx3)
  have hu0 : (0 : ℝ) < Real.log (Pa.x : ℝ) := by linarith
  have hv : (0.07 : ℝ) ≤ Real.log (Real.log (Pa.x : ℝ)) := zcub_loglog_ge hx3
  have hv0 : (0 : ℝ) < Real.log (Real.log (Pa.x : ℝ)) := by linarith
  have hN0 : (0 : ℝ) < (Pa.N : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le zero_lt_one Pa.hN1)
  -- `log N > (1/4)·log x`
  have hlogN : Real.log (Pa.x : ℝ) / 4 < Real.log (Pa.N : ℝ) := by
    have h := Real.log_lt_log (Real.rpow_pos_of_pos hx0 ((1 : ℝ) / 4 + Pa.η)) Pa.hNlo
    rw [Real.log_rpow hx0] at h
    have hu_nn : (0 : ℝ) ≤ Real.log (Pa.x : ℝ) := by linarith
    nlinarith [Pa.hη]
  have hLlogN : Real.log (Pa.N : ℝ) ≤ Real.log (|(m : ℝ)| + |s.im| + (Pa.N : ℝ) + 3) := by
    refine Real.log_le_log hN0 ?_
    have h1 := abs_nonneg (m : ℝ)
    have h2 := abs_nonneg s.im
    linarith
  have hLbig : (0.27 : ℝ) < Real.log (|(m : ℝ)| + |s.im| + (Pa.N : ℝ) + 3) := by
    linarith
  -- the `Φ`-bound (4.4) rewritten as `log Pz ≤ log x / (loglog x)²`
  have hPhi' : Real.log (Pa.Pz : ℝ)
      ≤ Real.log (Pa.x : ℝ) * ((Real.log (Real.log (Pa.x : ℝ))) ^ 2)⁻¹ := by
    have hz : (Real.log (Real.log (Pa.x : ℝ))) ^ (-2 : ℤ)
        = ((Real.log (Real.log (Pa.x : ℝ))) ^ 2)⁻¹ := by
      rw [show (-2 : ℤ) = -((2 : ℕ) : ℤ) by norm_num, zpow_neg, zpow_natCast]
    have hh := Pa.hPhi
    rw [hz] at hh
    exact hh
  have hv2 : (0.0049 : ℝ) ≤ (Real.log (Real.log (Pa.x : ℝ))) ^ 2 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 0.07) hv 2
    norm_num at h
    linarith
  have hmain : Real.log (Pa.Pz : ℝ)
      ≤ 816.4 * Real.log (|(m : ℝ)| + |s.im| + (Pa.N : ℝ) + 3) := by
    have h1 : Real.log (Pa.x : ℝ) * ((Real.log (Real.log (Pa.x : ℝ))) ^ 2)⁻¹
        ≤ (4 * Real.log (|(m : ℝ)| + |s.im| + (Pa.N : ℝ) + 3)) * (0.0049 : ℝ)⁻¹ := by
      have hvinv : ((Real.log (Real.log (Pa.x : ℝ))) ^ 2)⁻¹ ≤ (0.0049 : ℝ)⁻¹ := by
        have h := one_div_le_one_div_of_le (show (0 : ℝ) < 0.0049 by norm_num) hv2
        rwa [one_div, one_div] at h
      have hu4L : Real.log (Pa.x : ℝ)
          ≤ 4 * Real.log (|(m : ℝ)| + |s.im| + (Pa.N : ℝ) + 3) := by linarith [hlogN, hLlogN]
      exact mul_le_mul hu4L hvinv (inv_nonneg.mpr (pow_pos hv0 2).le) (by linarith [hlogN, hLlogN])
    have h2 : (4 * Real.log (|(m : ℝ)| + |s.im| + (Pa.N : ℝ) + 3)) * (0.0049 : ℝ)⁻¹
        ≤ 816.4 * Real.log (|(m : ℝ)| + |s.im| + (Pa.N : ℝ) + 3) := by
      have hX : (0 : ℝ) ≤ Real.log (|(m : ℝ)| + |s.im| + (Pa.N : ℝ) + 3) := by linarith
      have hc : (4 : ℝ) * (0.0049 : ℝ)⁻¹ ≤ 816.4 := by norm_num
      calc (4 * Real.log (|(m : ℝ)| + |s.im| + (Pa.N : ℝ) + 3)) * (0.0049 : ℝ)⁻¹
          = (4 * (0.0049 : ℝ)⁻¹)
              * Real.log (|(m : ℝ)| + |s.im| + (Pa.N : ℝ) + 3) := by ring
        _ ≤ 816.4 * Real.log (|(m : ℝ)| + |s.im| + (Pa.N : ℝ) + 3) :=
            mul_le_mul_of_nonneg_right hc hX
    linarith [hPhi', h1]
  linarith [hmain, hLbig]

/-- **The `log`-bookkeeping of the target bound**: the `P`-factor's `(log Pz+2)³`, the `Q`-factor's
`(1 + log(C+2)/log Pz)²` and the `(Λ/arch)^{-1}`-factor's `log²(|m|+|Im s|+3)` all fit into the
single `log^6(|m|+|Im s|+N+3)`, with an absolute constant. -/
theorem ZcBoundArith_proved :
    ∃ C : ℝ, 0 < C ∧ ∀ (Pa : Work.FITop.Params) (m : ℤ) (s : ℂ),
      1 ≤ Pa.C → 4 ≤ Real.log (Pa.Pz : ℝ) →
      (Real.log (Pa.Pz : ℝ) + 2) ^ (3 : ℕ)
        * (1 + Real.log (Pa.C + 2) / Real.log (Pa.Pz : ℝ)) ^ (2 : ℕ)
        * (Real.log (|(m : ℝ)| + |s.im| + 3)) ^ (2 : ℕ)
      ≤ C * (Real.log (|(m : ℝ)| + |s.im| + (Pa.N : ℝ) + 3)) ^ (6 : ℕ) := by
  refine ⟨900 * (901.5 : ℝ) ^ 2, by norm_num, ?_⟩
  intro Pa m s hC1 hlogPz
  set p : ℝ := Real.log (Pa.Pz : ℝ) with hp_def
  set L : ℝ := Real.log (|(m : ℝ)| + |s.im| + (Pa.N : ℝ) + 3) with hL_def
  set b : ℝ := Real.log (|(m : ℝ)| + |s.im| + 3) with hb_def
  set c : ℝ := Real.log (Pa.C + 2) with hc_def
  have hp4 : (4 : ℝ) ≤ p := by rw [hp_def]; exact hlogPz
  have hp0 : (0 : ℝ) < p := by linarith
  have hL1 : (1 : ℝ) ≤ L := by
    rw [hL_def]
    have h5 : Real.exp 1 ≤ |(m : ℝ)| + |s.im| + (Pa.N : ℝ) + 3 := by
      have h1 := abs_nonneg (m : ℝ)
      have h2 := abs_nonneg s.im
      have h3 : (1 : ℝ) ≤ (Pa.N : ℝ) := by exact_mod_cast Pa.hN1
      linarith [Real.exp_one_lt_d9]
    exact (Real.log_exp 1).symm.trans_le (Real.log_le_log (Real.exp_pos 1) h5)
  have hb_le : b ≤ L := by
    rw [hb_def, hL_def]
    refine Real.log_le_log (by positivity) ?_
    have h1 := abs_nonneg (m : ℝ)
    have h2 := abs_nonneg s.im
    have h3 : (0 : ℝ) ≤ (Pa.N : ℝ) := by linarith [Pa.hN1]
    linarith
  have hb0 : (0 : ℝ) ≤ b := by
    rw [hb_def]
    apply Real.log_nonneg
    have h1 := abs_nonneg (m : ℝ)
    have h2 := abs_nonneg s.im
    linarith
  have hc_le : c ≤ L := by
    rw [hc_def, hL_def]
    refine Real.log_le_log (by positivity) ?_
    have hCN : Pa.C ≤ (Pa.N : ℝ) := by
      have hN1 : (1 : ℝ) ≤ (Pa.N : ℝ) := by exact_mod_cast Pa.hN1
      calc Pa.C ≤ (Pa.N : ℝ) ^ (1 - Pa.η) := Pa.hC2
        _ ≤ (Pa.N : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith [Pa.hη])
        _ = (Pa.N : ℝ) := Real.rpow_one _
    have h1 := abs_nonneg (m : ℝ)
    have h2 := abs_nonneg s.im
    linarith
  have hc0 : (0 : ℝ) ≤ c := by
    rw [hc_def]
    apply Real.log_nonneg
    linarith
  have hA_le : p + 2 ≤ 900 * L := by
    rw [hp_def, hL_def]
    exact zcub_logPz_add_two_le Pa m s
  have hone : (0 : ℝ) ≤ 1 + c / p := by positivity
  have hkey : (p + 2) * (1 + c / p) ≤ 901.5 * L := by
    have h1 : (p + 2) / p ≤ 1.5 := by
      rw [div_le_iff₀ hp0]
      linarith
    have h2 : (p + 2) * (1 + c / p) = (p + 2) + ((p + 2) / p) * c := by
      field_simp
    have h3 : ((p + 2) / p) * c ≤ 1.5 * L := mul_le_mul h1 hc_le hc0 (by norm_num)
    rw [h2]
    linarith
  calc (p + 2) ^ 3 * (1 + c / p) ^ 2 * b ^ 2
      = (p + 2) * ((p + 2) * (1 + c / p)) ^ 2 * b ^ 2 := by ring
    _ ≤ (p + 2) * (901.5 * L) ^ 2 * b ^ 2 := by
        gcongr
    _ ≤ (900 * L) * (901.5 * L) ^ 2 * L ^ 2 := by
        gcongr
    _ = 900 * 901.5 ^ 2 * L ^ 5 := by ring
    _ ≤ 900 * 901.5 ^ 2 * L ^ 6 := by
        have h56 : L ^ 5 ≤ L ^ 6 := by
          simpa using pow_le_pow_right₀ hL1 (by norm_num : (5 : ℕ) ≤ 6)
        have hnn : (0 : ℝ) ≤ 900 * 901.5 ^ 2 := by norm_num
        exact mul_le_mul_of_nonneg_left h56 hnn

/-- ***(FI)* (16.35) with a constant independent of the set-up `Pa`.**  The continuation `Zc` of the
Möbius-twisted Hecke series `Zsfun = M·P·Q` satisfies, on the region (16.24) ∩ (16.32),

  `‖Zc(s)‖ ≤ C_Z·d·C^{1-σ}·(log(N + |m| + |Im s| + 3))^6`

with `C_Z` depending only on `ε, c_h, C_h` — **not** on `Pa`, `χ`, `m`, `d`.  This is the form the
contour shift (16.36)–(16.38) needs: the `Pa`-dependent constant of the shelf's `ZcontExistsBound`
(`∏_{p ≤ Pz}(1-2p^{-3/4})^{-1}` from the `P`-factor and `Pa.C·A + 1` from the `Q`-factor) is absorbed
by the single `log^6(N + |m| + |Im s| + 3)`, which at the *shifted line* (`|Im s| ≤ T ≪ N`) is the
`log^6 N` that the target's right-hand side provides.

*Route.*  Rerun the construction of `ZcontExistsBound`
(`Zc = Φ·(Lam/heckeArch)^{-1}·P·Q`, agreeing with `Zsfun` for `re s > 1`) with the three sharpened
inputs: `Work.FIArea6Road.PhifacBoundUniform` (or the explicit constant
`exp((4/(1-2^{-3/4})²)Σ_p p^{-3/2})` read off the proof of `PhifacAnalyticBound`), the
`‖1/L‖ ≤ C_h d log²` inverse bound (a hypothesis here), the sharp `P`-bound `(log Pz + 2)³` of
`Work.FIArea6Road.PfacBoundSharp` (proved), and the sharp `Q`-bound `K·log(C+2)·C^{1-σ}` on
`1-1/logPz ≤ σ ≤ 1` (`Work.FIArea6Road.QfacBoundSharpOne`, delegated; it may also be proved
internally: at `σ = 1` the true size of `Q` is `≍ log C/log Pz`, so the first power of `log` is what
the proof gives once the local factors are bounded with the *region* `σ ≥ 1 - 1/log Pz` instead of
`σ ≥ 3/4`).  The product is `≤ K·(logPz+2)³·log(C+2)·log²(|m|+|Im s|+3)·d·C^{1-σ}`, and the fields of
`Params` give `logPz + 2 ≤ 6 log N` (`hNlo`, `hPhi`), `log(C+2) ≤ 2 log N` (`hC2`) and
`log(|m|+|Im s|+3) ≤ log(N+|m|+|Im s|+3)`, so `(logPz+2)³·log(C+2)·log²(|m|+|Im s|+3) ≤ 432 L^5`
with `L = log(N+|m|+|Im s|+3) ≥ 1`, which fits into the claimed `L^6`.  The analyticity conclusion is
the same open region as in `ZcontExistsBound`. -/
theorem ZcontExistsBoundUniform (ε c_h C_h : ℝ) (hε : 0 < ε) (hc_h : 0 < c_h) (hC_h : 0 < C_h) :
    ∃ C_Z : ℝ, 0 < C_Z ∧
    ∀ (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (m : ℤ) (d : ℕ) (Lam : ℂ → ℂ),
      1 ≤ d → chi 1 = 1 →
      (∀ z w : GaussianInt, chi (z * w) = chi z * chi w) →
      (∀ z : GaussianInt, ‖chi z‖ ≤ 1) →
      AnalyticOn ℂ Lam Set.univ →
      (∀ s : ℂ, 1 + |(m : ℝ)| / 2 < s.re →
        Lam s = Work.FITop4.Bridge.heckeArch d m s * Work.FIArea5.S16Hecke.heckeLSeries chi m s) →
      (∀ s : ℂ,
        1 - c_h / ((d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |s.im| + 3)) < s.re → s.re ≤ 2 →
        ‖(Lam s / Work.FITop4.Bridge.heckeArch d m s)⁻¹‖
          ≤ C_h * (d : ℝ) * (Real.log (|(m : ℝ)| + |s.im| + 3)) ^ (2 : ℕ)) →
      1 ≤ Pa.N → 1 ≤ Pa.C → 4 ≤ Real.log (Pa.Pz : ℝ) →
      ∃ Zc : ℂ → ℂ,
        (∀ s : ℂ, 1 < s.re → Zc s = Work.FIArea6.TauPieces.Zsfun Pa chi m s) ∧
        AnalyticOn ℂ Zc {s : ℂ | 1 / 2 < s.re ∧
          1 - c_h / (2 * (d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |s.im| + 3)) < s.re} ∧
        ∀ s : ℂ, 3 / 4 ≤ s.re →
          1 - 1 / Real.log (Pa.Pz : ℝ) ≤ s.re → s.re ≤ 1 →
          1 - c_h / (2 * (d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |s.im| + 3)) < s.re →
          ‖Zc s‖ ≤ C_Z * (d : ℝ) * Pa.C ^ (1 - s.re)
            * (Real.log (|(m : ℝ)| + |s.im| + (Pa.N : ℝ) + 3)) ^ (6 : ℕ) := by
  obtain ⟨KΦ, hKΦpos, hKΦbd⟩ := PhifacBoundUniform
  obtain ⟨KP, hKPpos, hKPbd⟩ := Work.FIArea6Road.ZT.PfacBoundSharpZT
  obtain ⟨KQ, hKQpos, hKQbd⟩ := zcub_QfacBoundUniformRatio
  obtain ⟨Cz, hCzpos, hArith⟩ := ZcBoundArith_proved
  refine ⟨KΦ * C_h * KP * KQ * Cz, by positivity, ?_⟩
  intro Pa chi m d Lam hd hchi1 hchimul hchibd hLam hag hinv hN1 hC1 hlogPz
  obtain ⟨hΦan, -⟩ := PhifacAnalyticBound chi m hchi1 hchimul hchibd
  refine ⟨Work.FIArea6.TauPieces.Zcand Pa chi m d Lam, ?_, ?_, ?_⟩
  · -- agreement with `Zsfun` for `re s > 1`
    intro s hs
    have hLval := zcontLval_eq hd chi m hchi1 hchimul hchibd hLam hag hs
    have hP2 := PhifacIdent chi m hchi1 hchimul hchibd hs
    have hLmul := zcontLSeries_mul_inv (m := m) hchi1 hchimul hchibd hs
    have hP1 := ZprodRegroup Pa chi m hchi1 hchimul hchibd hs
    have hLval' : Lam s / Work.FITop4.Bridge.heckeArch d m s
        = Work.FIArea5.S16Hecke.heckeLSeries chi m s := hLval
    rw [Work.FIArea6.TauPieces.Zcand_apply, hLval', hP2]
    have hstep : (Work.FIArea6.TauPieces.Mfac chi m s
        * Work.FIArea5.S16Hecke.heckeLSeries chi m s)
        * (Work.FIArea5.S16Hecke.heckeLSeries chi m s)⁻¹
        = Work.FIArea6.TauPieces.Mfac chi m s := by
      rw [mul_assoc, hLmul, mul_one]
    rw [hstep, ← hP1]
  · -- analyticity on the region (16.24)
    set U : Set ℂ := {s : ℂ | 1 / 2 < s.re ∧
        1 - c_h / (2 * (d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |s.im| + 3)) < s.re} with hU
    have hUopen : IsOpen U := by
      rw [hU]
      have hin : Continuous (fun w : ℂ => |(m : ℝ)| + |w.im| + 3) :=
        (continuous_const.add Complex.continuous_im.abs).add continuous_const
      have hlogc : Continuous (fun w : ℂ => Real.log (|(m : ℝ)| + |w.im| + 3)) :=
        Continuous.log hin (fun w => by
          have h1 := abs_nonneg (m : ℝ)
          have h2 := abs_nonneg w.im
          linarith)
      have hcont : Continuous (fun w : ℂ =>
          1 - c_h / (2 * (d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |w.im| + 3))) := by
        refine Continuous.sub continuous_const ?_
        refine Continuous.div continuous_const ?_ ?_
        · exact continuous_const.mul hlogc
        · intro w
          have h1 : 0 < (d : ℝ) ^ ε := Real.rpow_pos_of_pos (by exact_mod_cast hd) _
          have h2 : 0 < Real.log (|(m : ℝ)| + |w.im| + 3) := by
            apply Real.log_pos
            have h3 := abs_nonneg (m : ℝ)
            have h4 := abs_nonneg w.im
            linarith
          positivity
      exact IsOpen.and (isOpen_lt continuous_const Complex.continuous_re)
        (isOpen_lt hcont Complex.continuous_re)
    refine AnalyticOn.mul (AnalyticOn.mul (AnalyticOn.mul ?_ ?_) ?_) ?_
    · exact hΦan.mono (fun s hs => hs.1)
    · refine AnalyticOn.inv ?_ ?_
      · refine AnalyticOn.div ?_ ?_ ?_
        · exact hLam.mono (Set.subset_univ U)
        · refine DifferentiableOn.analyticOn ?_ hUopen
          intro w hw
          exact (zcontArch_diff hd m (by linarith [hw.1])).differentiableWithinAt
        · intro w hw
          exact zcontArch_ne_zero hd m (by linarith [hw.1])
      · intro w hw
        exact zcontLval_ne_zero hd chi m Lam ε c_h C_h hε hc_h hC_h hchi1 hchimul hchibd hLam hag
          hinv hw
    · refine DifferentiableOn.analyticOn ?_ hUopen
      exact (zcontPfac_diff Pa chi m hchibd).mono (fun s hs => hs.1)
    · refine DifferentiableOn.analyticOn ?_ hUopen
      exact (zcontQfac_diff Pa chi m hchibd).mono (fun s hs => hs.1)
  · -- the uniform bound
    intro s h34 hr hle1 hc
    have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    have hCpos : (0 : ℝ) < Pa.C := lt_of_lt_of_le zero_lt_one hC1
    have hlogPzpos : (0 : ℝ) < Real.log (Pa.Pz : ℝ) := by linarith
    have hlog3pos : (0 : ℝ) < Real.log (|(m : ℝ)| + |s.im| + 3) := by
      apply Real.log_pos
      have h1 := abs_nonneg (m : ℝ)
      have h2 := abs_nonneg s.im
      linarith
    have hhinv : 1 - c_h / ((d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |s.im| + 3)) < s.re := by
      have hX : 0 < (d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |s.im| + 3) :=
        mul_pos (Real.rpow_pos_of_pos hdR _) hlog3pos
      have hmul : 2 * (d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |s.im| + 3)
          = 2 * ((d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |s.im| + 3)) := by ring
      rw [hmul] at hc
      have hlt : c_h / (2 * ((d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |s.im| + 3)))
          < c_h / ((d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |s.im| + 3)) := by
        have hkey : c_h / (2 * ((d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |s.im| + 3)))
            = c_h / ((d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |s.im| + 3)) / 2 := by
          rw [mul_comm, div_mul_eq_div_div]
        rw [hkey]
        exact half_lt_self (div_pos hc_h hX)
      linarith
    have hΦ := hKΦbd chi m hchi1 hchimul hchibd s h34
    have hW := hinv s hhinv (by linarith)
    have hP := hKPbd Pa chi m hchi1 hchimul hchibd hlogPz s hr
    have hQ := hKQbd Pa chi m hchi1 hchimul hchibd hC1 hlogPz s h34 hr hle1
    have harith := hArith Pa m s hC1 hlogPz
    have hstep : ‖Work.FIArea6.TauPieces.Zcand Pa chi m d Lam s‖
        = ‖Work.FIArea6.TauPieces.Phifac chi m s‖
          * ‖(Lam s / Work.FITop4.Bridge.heckeArch d m s)⁻¹‖
          * ‖Work.FIArea6.TauPieces.Pfac Pa chi m s‖
          * ‖Work.FIArea6.TauPieces.Qfac Pa chi m s‖ := by
      rw [Work.FIArea6.TauPieces.Zcand_apply, norm_mul, norm_mul, norm_mul]
    rw [hstep]
    have hgc : ‖Work.FIArea6.TauPieces.Phifac chi m s‖
          * ‖(Lam s / Work.FITop4.Bridge.heckeArch d m s)⁻¹‖
          * ‖Work.FIArea6.TauPieces.Pfac Pa chi m s‖
          * ‖Work.FIArea6.TauPieces.Qfac Pa chi m s‖
        ≤ KΦ * (C_h * (d : ℝ) * (Real.log (|(m : ℝ)| + |s.im| + 3)) ^ (2 : ℕ))
          * (KP * (Real.log (Pa.Pz : ℝ) + 2) ^ (3 : ℕ))
          * (KQ * Pa.C ^ (1 - s.re)
              * (1 + Real.log (Pa.C + 2) / Real.log (Pa.Pz : ℝ)) ^ (2 : ℕ)) := by
      gcongr
    refine hgc.trans ?_
    have hrearr : KΦ * (C_h * (d : ℝ) * (Real.log (|(m : ℝ)| + |s.im| + 3)) ^ (2 : ℕ))
          * (KP * (Real.log (Pa.Pz : ℝ) + 2) ^ (3 : ℕ))
          * (KQ * Pa.C ^ (1 - s.re)
              * (1 + Real.log (Pa.C + 2) / Real.log (Pa.Pz : ℝ)) ^ (2 : ℕ))
        = (KΦ * C_h * KP * KQ) * (d : ℝ) * Pa.C ^ (1 - s.re)
          * ((Real.log (Pa.Pz : ℝ) + 2) ^ (3 : ℕ)
              * (1 + Real.log (Pa.C + 2) / Real.log (Pa.Pz : ℝ)) ^ (2 : ℕ)
              * (Real.log (|(m : ℝ)| + |s.im| + 3)) ^ (2 : ℕ)) := by
      ring
    rw [hrearr]
    have hnn : 0 ≤ (KΦ * C_h * KP * KQ) * (d : ℝ) * Pa.C ^ (1 - s.re) := by
      have hd0 : (0 : ℝ) < (d : ℝ) := hdR
      have hCnn : (0 : ℝ) ≤ Pa.C ^ (1 - s.re) := Real.rpow_nonneg (le_of_lt hCpos) _
      positivity
    refine (mul_le_mul_of_nonneg_left harith hnn).trans (le_of_eq ?_)
    ring

end

end Work.FIArea6Road
