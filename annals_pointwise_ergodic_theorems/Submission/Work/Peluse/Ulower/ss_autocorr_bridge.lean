/-
Copyright (c) 2026 The AnnalsChallenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AnnalsChallenge team.
-/
import Mathlib
import Submission.Work.Peluse.Basic

/-!
# The elementary bridge from the window sums of `f` to `progAvgSum`

For a `1`-bounded function `f` supported in `[-Ns,Ns]`, the progression average
`W x = progAvg N' q f x = (N')⁻¹ ∑_{m∈[1,N']} f (x + q m)` is again bounded by `1` in modulus, so
`‖W x‖² ≤ ‖W x‖` and therefore

`∑'_x ‖progAvg N' q f x‖² ≤ progAvgSum N' q f`.

Combined with `Work.Peluse.Ulower.ss_progAvg_normSq_eq_autocorrSum`
(`∑_x ‖W x‖² = (N')^{-2} ∑_{d=-(N'-1)}^{N'-1} (N'-|d|)·Re (∑_z f (z+qd) conj (f z))`) this shows
that a lower bound for the **autocorrelation sum of `f` at the multiples `q d` of the step** is
exactly a lower bound for `progAvgSum N' q f` — the target that the "split into progressions and
apply van der Corput" step of Peluse's §9 (arXiv:1909.00309) produces.

Everything here is elementary; the file exists to make the last step of §9 available as a lemma.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.Ulower

noncomputable section

open Work.Peluse

/-- The progression average is `1`-bounded for a `1`-bounded function. -/
theorem ss_progAvg_norm_le_one {f : ℤ → ℂ} {N' : ℕ} (hN' : 1 ≤ N') (q : ℤ)
    (hb : ∀ x : ℤ, ‖f x‖ ≤ 1) (x : ℤ) :
    ‖Work.Peluse.progAvg N' q f x‖ ≤ 1 := by
  have hN'pos : (0 : ℝ) < (N' : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN')
  have hcard : ((Finset.Icc 1 N').card : ℝ) = (N' : ℝ) := by
    rw [Nat.card_Icc]; simp
  calc ‖Work.Peluse.progAvg N' q f x‖
      = ‖((N' : ℂ))⁻¹ * ∑ m ∈ Finset.Icc 1 N', f (x + q * (m : ℤ))‖ := rfl
    _ = ‖((N' : ℂ))⁻¹‖ * ‖∑ m ∈ Finset.Icc 1 N', f (x + q * (m : ℤ))‖ := norm_mul _ _
    _ ≤ ‖((N' : ℂ))⁻¹‖ * ∑ m ∈ Finset.Icc 1 N', ‖f (x + q * (m : ℤ))‖ := by
        gcongr
        exact norm_sum_le _ _
    _ ≤ ‖((N' : ℂ))⁻¹‖ * ∑ _m ∈ Finset.Icc 1 N', (1 : ℝ) := by
        gcongr with m hm
        exact hb _
    _ = 1 := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one, norm_inv, Complex.norm_natCast]
        rw [hcard, inv_mul_cancel₀ (ne_of_gt hN'pos)]

/-- `progAvg` of a function supported in `[-Ns,Ns]` vanishes outside `[-L,L]`,
`L = Ns + |q| N'`. -/
theorem ss_progAvg_eq_zero_of_not_mem {f : ℤ → ℂ} {Ns N' : ℕ} (q : ℤ)
    (hsup : Work.Peluse.SupportIn f Ns) {x : ℤ} (hx : x ∉ symIcc (Ns + q.natAbs * N')) :
    Work.Peluse.progAvg N' q f x = 0 := by
  have hxabs : (((Ns + q.natAbs * N' : ℕ) : ℤ)) < |x| := by
    have h : ¬ (|x| ≤ (((Ns + q.natAbs * N' : ℕ) : ℤ))) := by
      intro hle
      exact hx (by rw [symIcc, Finset.mem_Icc]; exact abs_le.mp hle)
    exact not_le.mp h
  rw [Work.Peluse.progAvg]
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero (fun m hm => ?_))
  refine hsup _ ?_
  have hm' : m ≤ N' := (Finset.mem_Icc.mp hm).2
  have hqm : |q * (m : ℤ)| ≤ (((q.natAbs * N' : ℕ)) : ℤ) := by
    calc |q * (m : ℤ)| = |q| * |(m : ℤ)| := abs_mul _ _
      _ = |q| * (m : ℤ) := by rw [abs_of_nonneg (Int.natCast_nonneg m)]
      _ ≤ |q| * (N' : ℤ) := by
          exact mul_le_mul_of_nonneg_left (by exact_mod_cast hm') (abs_nonneg _)
      _ = (((q.natAbs * N' : ℕ)) : ℤ) := by push_cast; ring
  have hNscast : (((Ns + q.natAbs * N' : ℕ)) : ℤ)
      = (Ns : ℤ) + (((q.natAbs * N' : ℕ)) : ℤ) := by push_cast; ring
  have hmain : (Ns : ℤ) < |x + q * (m : ℤ)| := by
    have h := abs_sub_abs_le_abs_sub x (-(q * (m : ℤ)))
    rw [abs_neg, sub_neg_eq_add] at h
    rw [hNscast] at hxabs
    linarith
  have hfin : (Ns : ℤ) < (((x + q * (m : ℤ)).natAbs : ℕ) : ℤ) := by
    rw [Int.natCast_natAbs]; exact hmain
  exact_mod_cast hfin

/-- **The window-sum `ℓ²` bound is dominated by `progAvgSum`**: for `f` `1`-bounded,
`∑_x ‖progAvg N' q f x‖² ≤ progAvgSum N' q f`. -/
theorem ss_normSq_progAvg_le_progAvgSum {f : ℤ → ℂ} {Ns N' : ℕ} (hN' : 1 ≤ N') (q : ℤ)
    (hsup : Work.Peluse.SupportIn f Ns) (hb : ∀ x : ℤ, ‖f x‖ ≤ 1) :
    (∑' x : ℤ, ‖Work.Peluse.progAvg N' q f x‖ ^ 2) ≤ Work.Peluse.progAvgSum N' q f := by
  classical
  set L : ℕ := Ns + q.natAbs * N' with hL
  have hzero : ∀ x : ℤ, x ∉ symIcc L → ‖Work.Peluse.progAvg N' q f x‖ ^ 2 = 0 := by
    intro x hx
    rw [ss_progAvg_eq_zero_of_not_mem (Ns := Ns) q hsup (by rw [← hL]; exact hx)]
    simp
  have hzero' : ∀ x : ℤ, x ∉ symIcc L → ‖Work.Peluse.progAvg N' q f x‖ = 0 := by
    intro x hx
    rw [ss_progAvg_eq_zero_of_not_mem (Ns := Ns) q hsup (by rw [← hL]; exact hx)]
    simp
  rw [tsum_eq_sum (s := symIcc L) hzero, Work.Peluse.progAvgSum,
    tsum_eq_sum (s := symIcc L) hzero']
  refine Finset.sum_le_sum (fun x _ => ?_)
  have h1 : ‖Work.Peluse.progAvg N' q f x‖ ≤ 1 := ss_progAvg_norm_le_one hN' q hb x
  nlinarith [norm_nonneg (Work.Peluse.progAvg N' q f x)]

end

end Work.Peluse.Ulower
