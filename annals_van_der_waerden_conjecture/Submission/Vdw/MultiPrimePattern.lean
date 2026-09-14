import Mathlib
import Submission.Vdw.MultiPrimeFourier
import Submission.Commons.Data.ZMod.minrep_natCast_mul
import Submission.Commons.NumberTheory.Nat.prod_dvd_of_pairwise_coprime_dvd

open Finset
open scoped BigOperators

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-!
# Pattern decomposition of the multi-prime frequency sum (the `Dequi2` chapter)

This module provides the arithmetic core of the passage from the multi-prime
Fourier expansion (`MultiPrimeFourier.multiPrime_fourier_expansion`) to the
single-prime input `FourierPrime.MIndexBound`.

For a frequency vector `c : (ZMod C)^n`:

* `mof C n c` is the product of the primes `p | C` at which `c` does **not**
  vanish (`Qvan C n p c` is the vanishing predicate `∀ i, (c i).val % p = 0`);
* `mofC C n c = C / mof C n c` is the complementary product (for squarefree
  `C`), and it divides every coordinate value (`mofC_dvd_val`);
* `xforM C M n c` is the "scaled-down" frequency
  `i ↦ (c i).val / (C/M)` in `(ZMod M)^n`;
* `upM_xforM`: on the fibre `mof C n c = M`, the scaled frequency reconstructs
  `c` as `q * x` with `q = C/M` (`upM_xforM`), which gives injectivity of the
  scaling map on each fibre (`xforM_inj`) and shows that scaled frequencies of
  nonzero vectors are nonzero (`xforM_ne_zero`);
* `freqWeightZ_natCast_mul`: the frequency weight `freqWeightZ` is invariant
  under the scaling `y ↦ q*y` (modulus `q*M` ↦ modulus `M`), which is what
  makes each fibre contribute only through the scaled-down weight.

Axioms: propext / Classical.choice / Quot.sound only.
-/

namespace Submission.Vdw
noncomputable section

abbrev Qvan (C n : ℕ) (p : ℕ) (c : Fin n → ZMod C) : Prop := ∀ i, (c i).val % p = 0

def mof (C n : ℕ) (c : Fin n → ZMod C) : ℕ :=
  ∏ p ∈ C.primeFactors.filter (fun p => ¬ Qvan C n p c), p

def mofC (C n : ℕ) (c : Fin n → ZMod C) : ℕ :=
  ∏ p ∈ C.primeFactors.filter (fun p => Qvan C n p c), p

lemma mof_dvd (C n : ℕ) (c : Fin n → ZMod C) : mof C n c ∣ C := by
  classical
  exact (Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)).trans
    (Nat.prod_primeFactors_dvd C)

lemma mof_pos (C n : ℕ) (c : Fin n → ZMod C) : 0 < mof C n c := by
  classical
  refine Finset.prod_pos (fun p hp => ?_)
  exact (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_filter p hp)).pos

lemma mof_mul_mofC (C n : ℕ) (hC : C = ∏ p ∈ C.primeFactors, p) (c : Fin n → ZMod C) :
    mof C n c * mofC C n c = C := by
  classical
  rw [mof, mofC, mul_comm, Finset.prod_filter_mul_prod_filter_not, ← hC]

lemma mofC_eq_div (C n : ℕ) (hC : C = ∏ p ∈ C.primeFactors, p) (c : Fin n → ZMod C) :
    mofC C n c = C / mof C n c := by
  have h := mof_mul_mofC C n hC c
  have hpos := mof_pos C n c
  have h2 : mof C n c * (C / mof C n c) = C := Nat.mul_div_cancel' (mof_dvd C n c)
  have h3 : mof C n c * mofC C n c = mof C n c * (C / mof C n c) := by rw [h, h2]
  exact Nat.eq_of_mul_eq_mul_left hpos h3

lemma mofC_dvd_val (C n : ℕ) (c : Fin n → ZMod C) (i : Fin n) :
    mofC C n c ∣ (c i).val := by
  classical
  refine Commons.NumberTheory.Nat.prod_dvd_of_pairwise_coprime_dvd ?_ ?_
  · intro p hp q hq hpq
    exact (Nat.coprime_primes
      (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_filter p hp))
      (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_filter q hq))).mpr hpq
  · intro p hp
    exact Nat.dvd_of_mod_eq_zero ((Finset.mem_filter.mp hp).2 i)

def xforM (C M n : ℕ) (c : Fin n → ZMod C) : Fin n → ZMod M :=
  fun i => (((c i).val / (C / M) : ℕ) : ZMod M)

lemma xforM_val (C M n : ℕ) (c : Fin n → ZMod C) (hC : 0 < C) (hCsq : C = ∏ p ∈ C.primeFactors, p)
    (hcM : mof C n c = M) (i : Fin n) :
    (xforM C M n c i).val = (c i).val / (C / M) := by
  haveI : NeZero C := ⟨hC.ne'⟩
  have hMpos : 0 < M := by rw [← hcM]; exact mof_pos C n c
  have hMdiv : M ∣ C := by rw [← hcM]; exact mof_dvd C n c
  rw [xforM, ZMod.val_natCast, Nat.mod_eq_of_lt]
  have h1 : (c i).val < M * (C / M) := by
    calc (c i).val < C := ZMod.val_lt _
      _ = M * (C / M) := (Nat.mul_div_cancel' hMdiv).symm
  refine Nat.div_lt_of_lt_mul ?_
  rw [mul_comm]
  exact h1

lemma upM_xforM (C M n : ℕ) (c : Fin n → ZMod C) (hC : 0 < C) (hCsq : C = ∏ p ∈ C.primeFactors, p)
    (hcM : mof C n c = M) (i : Fin n) :
    ((C / M * (xforM C M n c i).val : ℕ) : ZMod C) = c i := by
  haveI : NeZero C := ⟨hC.ne'⟩
  have hMdiv : M ∣ C := by rw [← hcM]; exact mof_dvd C n c
  have hq : C / M = mofC C n c := by rw [mofC_eq_div C n hCsq c, hcM]
  have hdvd : C / M ∣ (c i).val := by rw [hq]; exact mofC_dvd_val C n c i
  have hval : (xforM C M n c i).val = (c i).val / (C / M) :=
    xforM_val C M n c hC hCsq hcM i
  have h3 : (C / M * (xforM C M n c i).val : ℕ) = (c i).val := by
    rw [hval, Nat.mul_div_cancel' hdvd]
  rw [h3, ZMod.natCast_zmod_val]

lemma xforM_inj (C M n : ℕ) (c₁ c₂ : Fin n → ZMod C) (hC : 0 < C)
    (hCsq : C = ∏ p ∈ C.primeFactors, p) (h1 : mof C n c₁ = M) (h2 : mof C n c₂ = M)
    (hx : xforM C M n c₁ = xforM C M n c₂) : c₁ = c₂ := by
  funext i
  rw [← upM_xforM C M n c₁ hC hCsq h1 i, ← upM_xforM C M n c₂ hC hCsq h2 i, hx]

lemma xforM_ne_zero (C M n : ℕ) (c : Fin n → ZMod C) (hC : 0 < C)
    (hCsq : C = ∏ p ∈ C.primeFactors, p) (hcM : mof C n c = M) (hc : c ≠ 0) :
    xforM C M n c ≠ 0 := by
  haveI : NeZero C := ⟨hC.ne'⟩
  rw [← hcM]
  intro hzero
  apply hc
  funext i
  have h1 := upM_xforM C (mof C n c) n c hC hCsq rfl i
  have h2 : xforM C (mof C n c) n c i = 0 := congrFun hzero i
  rw [h2] at h1
  simpa using h1.symm

lemma freqWeightZ_natCast_mul (H M q y : ℕ) [NeZero M] [NeZero (q * M)] (hM : 0 < M)
    (hq : 0 < q) :
    freqWeightZ (q * M) H (((q * y : ℕ)) : ZMod (q * M))
      = freqWeightZ M H (((y : ℕ)) : ZMod M) := by
  have hz : (((q * y : ℕ)) : ZMod (q * M)) = 0 ↔ (((y : ℕ)) : ZMod M) = 0 := by
    rw [ZMod.natCast_eq_zero_iff, ZMod.natCast_eq_zero_iff, Nat.mul_dvd_mul_iff_left hq]
  set d : ℕ := min (ZMod.val (((y : ℕ)) : ZMod M)) (M - ZMod.val (((y : ℕ)) : ZMod M)) with hd
  have hdd : min (ZMod.val (((q * y : ℕ)) : ZMod (q * M)))
        (q * M - ZMod.val (((q * y : ℕ)) : ZMod (q * M))) = q * d := by
    rw [hd]
    exact Commons.Data.ZMod.minrep_natCast_mul M q y hM hq
  have hdiv : (((q * M : ℕ)) : ℝ) / (2 * (((q * d : ℕ)) : ℝ))
      = ((M : ℕ) : ℝ) / (2 * ((d : ℕ) : ℝ)) := by
    rcases Nat.eq_zero_or_pos d with h | h
    · rw [h]; simp
    · have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast h.ne'
      have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
      push_cast
      field_simp
  rw [freqWeightZ, freqWeightZ, hdd]
  exact if_congr hz rfl (by rw [hdiv])


/-- The scaling identity with the modulus written as a product `C = q * M`. -/
lemma freqWeightZ_natCast_mul' (H M q y C : ℕ) [NeZero M] [NeZero C] (hM : 0 < M) (hq : 0 < q)
    (hC : C = q * M) :
    freqWeightZ C H (((q * y : ℕ)) : ZMod C) = freqWeightZ M H (((y : ℕ)) : ZMod M) := by
  subst hC
  exact freqWeightZ_natCast_mul H M q y hM hq

end
end Submission.Vdw
