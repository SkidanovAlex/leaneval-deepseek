import Mathlib
import Submission.Vdw.MultiPrimePattern

/-!
# The pattern (fibre) decomposition of the multi-prime frequency sum

This module assembles the pattern arithmetic of `MultiPrimePattern` into the
sum inequality that the multi-prime §4 chapter needs:

    `Σ_{c ≠ 0} (mof c)^{-1/2} · w_{mof c}(c)
        ≤ Σ_{M | C} M^{-1/2} · Σ_{x ≠ 0 ∈ (ZMod M)^n} ∏_i freqWeightZ M H (x i)`,

where `w_M(c) = ∏_i freqWeightZ M H ((c i).val / (C/M))` is the scaled-down
frequency weight of the fibre `mof C n c = M` (`wvec`), and the right-hand side
sums the "reduced weights" over all nonzero frequencies at each divisor.

The proof groups the frequencies `c ≠ 0` by the value `M = mof C n c`
(`Finset.sum_fiberwise_of_maps_to`), identifies each fibre sum with a sum over
the scaled-down frequencies via the injection `xforM` (`fiber_sum_le_Wsum`,
using `MultiPrimePattern.xforM_inj` and `φ xforM_ne_zero`), and bounds the
scaled-down sums by the full reduced sums.

Axioms: propext / Classical.choice / Quot.sound only.
-/

open Finset
open scoped BigOperators

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Submission.Vdw
noncomputable section

/-- Auxiliary: the product of the scaled-down frequency weights at the surviving
modulus. -/
def wvecAux (C n H : ℕ) (c : Fin n → ZMod C) [NeZero (mof C n c)] : ℝ :=
  ∏ i, freqWeightZ (mof C n c) H (xforM C (mof C n c) n c i)

/-- The fibre weight of a frequency `c : (ZMod C)^n`: the product of the
scaled-down frequency weights `freqWeightZ` at the surviving modulus
`mof C n c`. -/
def wvec (C n H : ℕ) (c : Fin n → ZMod C) : ℝ :=
  @wvecAux C n H c ⟨(mof_pos C n c).ne'⟩

/-- Auxiliary: the sum of the frequency product over the nonzero frequencies at
a modulus with a `NeZero` instance. -/
def WsumAux (n H M : ℕ) [NeZero M] : ℝ :=
  ∑ x ∈ (Finset.univ : Finset (Fin n → ZMod M)).erase 0, ∏ i, freqWeightZ M H (x i)

/-- `Wsum n H M` is the sum of the frequency product over the nonzero
frequencies at modulus `M` (and `0` at `M = 0`, where no frequency type is
available). -/
def Wsum (n H M : ℕ) : ℝ :=
  if h : M = 0 then 0 else @WsumAux n H M ⟨h⟩

lemma wvec_eq_of_mof (C n H M : ℕ) (c : Fin n → ZMod C) (h : mof C n c = M) [NeZero M] :
    wvec C n H c = ∏ i, freqWeightZ M H (xforM C M n c i) := by
  have key : wvec C n H c = @wvecAux C n H c ⟨(mof_pos C n c).ne'⟩ := rfl
  rw [key, wvecAux]
  subst h
  rfl

lemma wvec_nonneg (C n H : ℕ) (c : Fin n → ZMod C) : 0 ≤ wvec C n H c := by
  haveI : NeZero (mof C n c) := ⟨(mof_pos C n c).ne'⟩
  have key : wvec C n H c = wvecAux C n H c := rfl
  rw [key, wvecAux]
  exact Finset.prod_nonneg (fun i _ => freqWeightZ_nonneg _ H _)

lemma Wsum_nonneg (n H M : ℕ) : 0 ≤ Wsum n H M := by
  rw [Wsum]
  split_ifs with h
  · exact le_refl 0
  · haveI : NeZero M := ⟨h⟩
    rw [WsumAux]
    exact Finset.sum_nonneg (fun x _ => Finset.prod_nonneg (fun i _ => freqWeightZ_nonneg _ H _))

lemma Wsum_zero (n H : ℕ) : Wsum n H 0 = 0 := by
  rw [Wsum, dif_pos rfl]

lemma Wsum_of_ne_zero (n H M : ℕ) [NeZero M] (h : M ≠ 0) :
    Wsum n H M
      = ∑ x ∈ (Finset.univ : Finset (Fin n → ZMod M)).erase 0, ∏ i, freqWeightZ M H (x i) := by
  rw [Wsum, dif_neg h, WsumAux]

/-- **The fibre bound**: on each fibre of `mof`, the sum of the fibre weights is
at most the sum of the scaled-down weights over the nonzero frequencies at the
surviving modulus. -/
lemma fiber_sum_le_Wsum (C n H M : ℕ) [NeZero C] (hC : 0 < C)
    (hCsq : C = ∏ p ∈ C.primeFactors, p) (hMne : M ≠ 0) :
    ∑ c ∈ ((Finset.univ : Finset (Fin n → ZMod C)).erase 0).filter (fun c => mof C n c = M),
        wvec C n H c
      ≤ Wsum n H M := by
  classical
  haveI : NeZero M := ⟨hMne⟩
  set s : Finset (Fin n → ZMod C) :=
    ((Finset.univ : Finset (Fin n → ZMod C)).erase 0).filter (fun c => mof C n c = M) with hs
  have hinj : Set.InjOn (fun c : Fin n → ZMod C => xforM C M n c) ↑s := by
    intro c hc c' hc' hxy
    exact xforM_inj C M n c c' hC hCsq (Finset.mem_filter.mp hc).2 (Finset.mem_filter.mp hc').2 hxy
  have hsub : Finset.image (fun c : Fin n → ZMod C => xforM C M n c) s
      ⊆ (Finset.univ : Finset (Fin n → ZMod M)).erase 0 := by
    intro x hx
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hx
    rw [Finset.mem_erase]
    refine ⟨?_, Finset.mem_univ _⟩
    exact xforM_ne_zero C M n c hC hCsq (Finset.mem_filter.mp hc).2
      (Finset.mem_erase.mp (Finset.mem_filter.mp hc).1).1
  rw [Wsum_of_ne_zero n H M hMne]
  have hstep : ∑ c ∈ s, wvec C n H c
      = ∑ c ∈ s, ∏ i, freqWeightZ M H (xforM C M n c i) :=
    Finset.sum_congr rfl (fun c hc => wvec_eq_of_mof C n H M c (Finset.mem_filter.mp hc).2)
  rw [hstep]
  rw [← Finset.sum_image (f := fun y : Fin n → ZMod M => ∏ i, freqWeightZ M H (y i)) hinj]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun x _ _ => Finset.prod_nonneg (fun i _ => freqWeightZ_nonneg _ H _))

/-- **The pattern decomposition of the frequency sum**: the sum over nonzero
frequencies of the scaled fibre weight is at most the sum over the divisors of
`C` of `M^{-1/2}·Wsum M`. -/
theorem pattern_sum_le (C n H : ℕ) [NeZero C] (hC : 0 < C)
    (hCsq : C = ∏ p ∈ C.primeFactors, p) :
    ∑ c ∈ (Finset.univ : Finset (Fin n → ZMod C)).erase 0,
        ((mof C n c : ℝ) ^ (-(1/2) : ℝ)) * wvec C n H c
      ≤ ∑ M ∈ C.divisors, ((M : ℝ) ^ (-(1/2) : ℝ)) * Wsum n H M := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun c : Fin n → ZMod C => mof C n c)
    (t := C.divisors) (fun c _ => Nat.mem_divisors.mpr ⟨mof_dvd C n c, hC.ne'⟩)
    (fun c => ((mof C n c : ℝ) ^ (-(1/2) : ℝ)) * wvec C n H c)]
  refine Finset.sum_le_sum (fun M hM => ?_)
  have hMne : M ≠ 0 := fun h0 =>
    (Nat.mem_divisors.mp hM).2 (Nat.eq_zero_of_zero_dvd (h0 ▸ (Nat.mem_divisors.mp hM).1))
  have hsplit : ∑ c ∈ ((Finset.univ : Finset (Fin n → ZMod C)).erase 0).filter
        (fun c => mof C n c = M), ((mof C n c : ℝ) ^ (-(1/2) : ℝ)) * wvec C n H c
      = ((M : ℝ) ^ (-(1/2) : ℝ)) * ∑ c ∈ ((Finset.univ : Finset (Fin n → ZMod C)).erase 0).filter
        (fun c => mof C n c = M), wvec C n H c := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun c hc => ?_)
    rw [(Finset.mem_filter.mp hc).2]
  rw [hsplit]
  exact mul_le_mul_of_nonneg_left (fiber_sum_le_Wsum C n H M hC hCsq hMne)
    (Real.rpow_nonneg (Nat.cast_nonneg M) _)


/-- **The fibre weight is the full frequency weight**: for every frequency `c`,
`wvec C n H c = ∏ i, freqWeightZ C H (c i)` (the scaling identity
`MultiPrimePattern.freqWeightZ_natCast_mul'` applied coordinatewise). -/
lemma wvec_eq_prod (C n H : ℕ) [NeZero C] (c : Fin n → ZMod C) (hC0 : 0 < C)
    (hCsq : C = ∏ p ∈ C.primeFactors, p) :
    wvec C n H c = ∏ i, freqWeightZ C H (c i) := by
  haveI : NeZero (mof C n c) := ⟨(mof_pos C n c).ne'⟩
  have key : wvec C n H c = wvecAux C n H c := rfl
  rw [key, wvecAux]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  have h1 : ((C / mof C n c * (xforM C (mof C n c) n c i).val : ℕ) : ZMod C) = c i :=
    upM_xforM C (mof C n c) n c hC0 hCsq rfl i
  have h2 : (((xforM C (mof C n c) n c i).val : ℕ) : ZMod (mof C n c))
      = xforM C (mof C n c) n c i := ZMod.natCast_zmod_val _
  have hCq : C = (C / mof C n c) * mof C n c := (Nat.div_mul_cancel (mof_dvd C n c)).symm
  rw [← h2, ← h1]
  exact (freqWeightZ_natCast_mul' H (mof C n c) (C / mof C n c)
    (xforM C (mof C n c) n c i).val C (mof_pos C n c)
    (Nat.div_pos (Nat.le_of_dvd hC0 (mof_dvd C n c)) (mof_pos C n c)) hCq).symm


/-! ## θ-generic form -/

/-- **The pattern decomposition of the frequency sum**: the sum over nonzero
frequencies of the scaled fibre weight is at most the sum over the divisors of
`C` of `M^{-1/2}·Wsum M`. -/
theorem pattern_sum_le_saving (C n H : ℕ) (θ : ℝ) [NeZero C] (hC : 0 < C)
    (hCsq : C = ∏ p ∈ C.primeFactors, p) :
    ∑ c ∈ (Finset.univ : Finset (Fin n → ZMod C)).erase 0,
        ((mof C n c : ℝ) ^ ((-θ) : ℝ)) * wvec C n H c
      ≤ ∑ M ∈ C.divisors, ((M : ℝ) ^ ((-θ) : ℝ)) * Wsum n H M := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun c : Fin n → ZMod C => mof C n c)
    (t := C.divisors) (fun c _ => Nat.mem_divisors.mpr ⟨mof_dvd C n c, hC.ne'⟩)
    (fun c => ((mof C n c : ℝ) ^ ((-θ) : ℝ)) * wvec C n H c)]
  refine Finset.sum_le_sum (fun M hM => ?_)
  have hMne : M ≠ 0 := fun h0 =>
    (Nat.mem_divisors.mp hM).2 (Nat.eq_zero_of_zero_dvd (h0 ▸ (Nat.mem_divisors.mp hM).1))
  have hsplit : ∑ c ∈ ((Finset.univ : Finset (Fin n → ZMod C)).erase 0).filter
        (fun c => mof C n c = M), ((mof C n c : ℝ) ^ ((-θ) : ℝ)) * wvec C n H c
      = ((M : ℝ) ^ ((-θ) : ℝ)) * ∑ c ∈ ((Finset.univ : Finset (Fin n → ZMod C)).erase 0).filter
        (fun c => mof C n c = M), wvec C n H c := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun c hc => ?_)
    rw [(Finset.mem_filter.mp hc).2]
  rw [hsplit]
  exact mul_le_mul_of_nonneg_left (fiber_sum_le_Wsum C n H M hC hCsq hMne)
    (Real.rpow_nonneg (Nat.cast_nonneg M) _)



end
end Submission.Vdw
