/-
# `Submission.Work.FITop4.Red5.Aseq_tau_sq_le`

The divisor-sum bound for the sequence `ã` that the small-`m` region of the `§§4–5.2` reduction
consumes: `Σ_{k ≤ y} ã_k τ(k)² ≤ C·Ã(y)·(log y)^65536`, obtained from
`Work.FITop.AseqTauEightBound` (`Σ ã_k τ(k)^8 ≤ C·Ã(y)(log y)^262144`) by Hölder with the
conjugate exponents `(4, 4/3)`.
-/
import Mathlib
import Submission.Work.FITop4.Defs4
import Submission.Work.FITop.AseqTauEightBound

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.FITop4.Red5

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- Hölder's inequality with the conjugate exponents `4` and `4/3`. -/
private lemma holder_four {ι : Type*} (s : Finset ι) {f g : ι → ℝ}
    (hf : ∀ i ∈ s, 0 ≤ f i) (hg : ∀ i ∈ s, 0 ≤ g i) :
    (∑ i ∈ s, f i * g i)
      ≤ (∑ i ∈ s, f i ^ (4 : ℝ)) ^ ((1 : ℝ) / 4)
        * (∑ i ∈ s, g i ^ ((4 : ℝ) / 3)) ^ ((3 : ℝ) / 4) := by
  have hconj : (4 : ℝ).HolderConjugate ((4 : ℝ) / 3) := ⟨by norm_num, by norm_num, by norm_num⟩
  have h := Real.inner_le_Lp_mul_Lq_of_nonneg (s := s) (f := f) (g := g)
    (p := (4 : ℝ)) (q := (4 : ℝ) / 3) hconj hf hg
  simpa using h

/-- **The `τ²`-weighted divisor sum of `ã`.** -/
theorem Aseq_tau_sq_le :
    ∃ C x₀ : ℕ, 0 < C ∧ ∀ y : ℕ, x₀ ≤ y →
      (∑ k ∈ Finset.Icc 1 y, Work.FITop.atilFIa k * ((k.divisors.card : ℝ) ^ 2))
        ≤ C * Work.FITop.AcountAtil y * (Real.log (y : ℝ)) ^ (65536 : ℕ) := by
  obtain ⟨C8, X8, hC8, h8⟩ := Work.FITop.AseqTauEightBound
  refine ⟨max C8 1, max X8 3, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro y hy
  have hyX8 : X8 ≤ y := le_trans (le_max_left _ _) hy
  have hy3 : 3 ≤ y := le_trans (le_max_right _ _) hy
  have hlog1 : 1 ≤ Real.log (y : ℝ) := by
    rw [← Real.log_exp 1]
    apply Real.log_le_log (Real.exp_pos 1)
    calc Real.exp 1 ≤ 3 := le_of_lt Real.exp_one_lt_three
      _ ≤ (y : ℝ) := by exact_mod_cast hy3
  have hlog0 : 0 ≤ Real.log (y : ℝ) := le_trans zero_le_one hlog1
  have hã : ∀ k, 0 ≤ Work.FITop.atilFIa k := Work.FITop.atilFIa_nonneg
  have hÃ0 : 0 ≤ Work.FITop.AcountAtil y := by
    unfold Work.FITop.AcountAtil Submission.ASP.Acount
    exact Finset.sum_nonneg fun k _ => hã k
  -- the pointwise factorisation `ã τ² = (ã τ⁸)^{1/4} · ã^{3/4}`
  have hpt : ∀ k : ℕ, Work.FITop.atilFIa k * ((k.divisors.card : ℝ) ^ 2)
      = (Work.FITop.atilFIa k * ((k.divisors.card : ℝ) ^ 8)) ^ ((1 : ℝ) / 4)
        * (Work.FITop.atilFIa k) ^ ((3 : ℝ) / 4) := by
    intro k
    have hτ0 : (0 : ℝ) ≤ (k.divisors.card : ℝ) := by positivity
    have hτ8 : (0 : ℝ) ≤ (k.divisors.card : ℝ) ^ 8 := by positivity
    have h1 : (Work.FITop.atilFIa k * ((k.divisors.card : ℝ) ^ 8)) ^ ((1 : ℝ) / 4)
        = (Work.FITop.atilFIa k) ^ ((1 : ℝ) / 4) * (k.divisors.card : ℝ) ^ 2 := by
      rw [Real.mul_rpow (hã k) hτ8, ← Real.rpow_natCast (k.divisors.card : ℝ) 8,
        ← Real.rpow_mul hτ0]
      norm_num
    have h2 : (Work.FITop.atilFIa k) ^ ((1 : ℝ) / 4) * (Work.FITop.atilFIa k) ^ ((3 : ℝ) / 4)
        = Work.FITop.atilFIa k := by
      rw [← Real.rpow_add_of_nonneg (hã k) (by norm_num) (by norm_num)]
      norm_num
    rw [h1]
    rw [show (Work.FITop.atilFIa k) ^ ((1 : ℝ) / 4) * (k.divisors.card : ℝ) ^ 2
          * (Work.FITop.atilFIa k) ^ ((3 : ℝ) / 4)
        = ((Work.FITop.atilFIa k) ^ ((1 : ℝ) / 4) * (Work.FITop.atilFIa k) ^ ((3 : ℝ) / 4))
          * (k.divisors.card : ℝ) ^ 2 by ring]
    rw [h2]
  have hg0 : ∀ k : ℕ, (0 : ℝ) ≤ (Work.FITop.atilFIa k) ^ ((3 : ℝ) / 4) :=
    fun k => Real.rpow_nonneg (hã k) _
  have hf0 : ∀ k : ℕ,
      (0 : ℝ) ≤ (Work.FITop.atilFIa k * ((k.divisors.card : ℝ) ^ 8)) ^ ((1 : ℝ) / 4) :=
    fun k => Real.rpow_nonneg (mul_nonneg (hã k) (by positivity)) _
  have hHolder := holder_four (Finset.Icc 1 y) (f := fun k : ℕ =>
        (Work.FITop.atilFIa k * ((k.divisors.card : ℝ) ^ 8)) ^ ((1 : ℝ) / 4))
      (g := fun k : ℕ => (Work.FITop.atilFIa k) ^ ((3 : ℝ) / 4))
      (fun i _ => hf0 i) (fun i _ => hg0 i)
  -- normalise the exponents
  have hFsum : (∑ k ∈ Finset.Icc 1 y,
        ((Work.FITop.atilFIa k * ((k.divisors.card : ℝ) ^ 8)) ^ ((1 : ℝ) / 4)) ^ (4 : ℝ))
      = ∑ k ∈ Finset.Icc 1 y, Work.FITop.atilFIa k * ((k.divisors.card : ℝ) ^ 8) := by
    apply Finset.sum_congr rfl
    intro k _
    have hτ8 : (0 : ℝ) ≤ (k.divisors.card : ℝ) ^ 8 := by positivity
    rw [← Real.rpow_mul (mul_nonneg (hã k) hτ8) ((1 : ℝ) / 4) 4]
    norm_num
  have hGsum : (∑ k ∈ Finset.Icc 1 y,
        ((Work.FITop.atilFIa k) ^ ((3 : ℝ) / 4)) ^ ((4 : ℝ) / 3))
      = ∑ k ∈ Finset.Icc 1 y, Work.FITop.atilFIa k := by
    apply Finset.sum_congr rfl
    intro k _
    rw [← Real.rpow_mul (hã k)]
    norm_num
  have hGÃ : (∑ k ∈ Finset.Icc 1 y, Work.FITop.atilFIa k) = Work.FITop.AcountAtil y := by
    unfold Work.FITop.AcountAtil Submission.ASP.Acount
    rw [Nat.floor_natCast]
  rw [hFsum, hGsum, hGÃ] at hHolder
  -- the eight-bound and the exponent arithmetic
  have hstep : (∑ k ∈ Finset.Icc 1 y,
        (Work.FITop.atilFIa k * ((k.divisors.card : ℝ) ^ 8)) ^ ((1 : ℝ) / 4)
          * (Work.FITop.atilFIa k) ^ ((3 : ℝ) / 4))
      ≤ ((C8 : ℝ) * Work.FITop.AcountAtil y * (Real.log (y : ℝ)) ^ (262144 : ℕ)) ^ ((1 : ℝ) / 4)
        * (Work.FITop.AcountAtil y) ^ ((3 : ℝ) / 4) := by
    refine le_trans hHolder (mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hÃ0 _))
    exact Real.rpow_le_rpow
      (Finset.sum_nonneg fun k _ => mul_nonneg (hã k) (by positivity)) (h8 y hyX8) (by norm_num)
  have hC8r : ((C8 : ℝ) * Work.FITop.AcountAtil y * (Real.log (y : ℝ)) ^ (262144 : ℕ)) ^ ((1 : ℝ) / 4)
      = (C8 : ℝ) ^ ((1 : ℝ) / 4) * (Work.FITop.AcountAtil y) ^ ((1 : ℝ) / 4)
        * (Real.log (y : ℝ)) ^ (65536 : ℕ) := by
    rw [Real.mul_rpow (mul_nonneg (by positivity) hÃ0) (by positivity),
      Real.mul_rpow (by positivity) hÃ0, ← Real.rpow_natCast (Real.log (y : ℝ)) 262144,
      ← Real.rpow_mul hlog0]
    norm_num
  rw [hC8r] at hstep
  have hcastmax : ((max C8 1 : ℕ) : ℝ) = max (C8 : ℝ) 1 := by
    rw [Nat.cast_max]; norm_num
  have hC8le : (C8 : ℝ) ^ ((1 : ℝ) / 4) ≤ ((max C8 1 : ℕ) : ℝ) := by
    rw [hcastmax]
    by_cases h : (C8 : ℝ) ≤ 1
    · exact le_trans (Real.rpow_le_one (by positivity) h (by norm_num))
        (le_max_right (C8 : ℝ) 1)
    · exact le_trans (Real.rpow_le_self_of_one_le (not_le.mp h).le (by norm_num))
        (le_max_left (C8 : ℝ) 1)
  have hfac : (C8 : ℝ) ^ ((1 : ℝ) / 4) * (Work.FITop.AcountAtil y) ^ ((1 : ℝ) / 4)
        * (Real.log (y : ℝ)) ^ (65536 : ℕ) * (Work.FITop.AcountAtil y) ^ ((3 : ℝ) / 4)
      = (C8 : ℝ) ^ ((1 : ℝ) / 4) * Work.FITop.AcountAtil y
        * (Real.log (y : ℝ)) ^ (65536 : ℕ) := by
    have hcomb : (Work.FITop.AcountAtil y) ^ ((1 : ℝ) / 4)
        * (Work.FITop.AcountAtil y) ^ ((3 : ℝ) / 4) = Work.FITop.AcountAtil y := by
      rw [← Real.rpow_add_of_nonneg hÃ0 (by norm_num) (by norm_num)]
      norm_num
    rw [show (C8 : ℝ) ^ ((1 : ℝ) / 4) * (Work.FITop.AcountAtil y) ^ ((1 : ℝ) / 4)
          * (Real.log (y : ℝ)) ^ (65536 : ℕ) * (Work.FITop.AcountAtil y) ^ ((3 : ℝ) / 4)
        = (C8 : ℝ) ^ ((1 : ℝ) / 4) * (Real.log (y : ℝ)) ^ (65536 : ℕ)
          * ((Work.FITop.AcountAtil y) ^ ((1 : ℝ) / 4)
              * (Work.FITop.AcountAtil y) ^ ((3 : ℝ) / 4)) by ring, hcomb]
    ring
  rw [hfac] at hstep
  -- conclude
  rw [Finset.sum_congr rfl (fun k (_ : k ∈ Finset.Icc 1 y) => hpt k)]
  refine le_trans hstep ?_
  have hL0 : (0 : ℝ) ≤ (Real.log (y : ℝ)) ^ (65536 : ℕ) := by positivity
  calc (C8 : ℝ) ^ ((1 : ℝ) / 4) * Work.FITop.AcountAtil y * (Real.log (y : ℝ)) ^ (65536 : ℕ)
      ≤ ((max C8 1 : ℕ) : ℝ) * Work.FITop.AcountAtil y * (Real.log (y : ℝ)) ^ (65536 : ℕ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC8le hÃ0) hL0

/-- **The threshold-free form** of `Aseq_tau_sq_le`, in the shape the small-`m` region consumes:
for *every* `y`, `Σ_{k ≤ y} ã_k τ(k)² ≤ C·(Ã(y)+1)·(log (y+2))^65536`. -/
theorem Aseq_tau_sq_le_univ :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℕ,
      (∑ k ∈ Finset.Icc 1 y, Work.FITop.atilFIa k * ((k.divisors.card : ℝ) ^ 2))
        ≤ C * (Work.FITop.AcountAtil y + 1) * (Real.log ((y : ℝ) + 2)) ^ (65536 : ℕ) := by
  obtain ⟨C1, X1, hC1, h1⟩ := Aseq_tau_sq_le
  set C1R : ℝ := (C1 : ℝ) with hC1R
  have hC1R0 : 0 ≤ C1R := by rw [hC1R]; exact Nat.cast_nonneg C1
  have hC1Rpos : 0 < C1R := by rw [hC1R]; exact_mod_cast hC1
  have hã : ∀ k, 0 ≤ Work.FITop.atilFIa k := Work.FITop.atilFIa_nonneg
  have hÃnn : ∀ y : ℕ, 0 ≤ Work.FITop.AcountAtil y := by
    intro y
    unfold Work.FITop.AcountAtil Submission.ASP.Acount
    exact Finset.sum_nonneg fun k _ => hã k
  set C0 : ℝ := ∑ k ∈ Finset.Icc 1 X1, Work.FITop.atilFIa k * ((k.divisors.card : ℝ) ^ 2)
    with hC0
  have hC00 : 0 ≤ C0 := by
    rw [hC0]
    exact Finset.sum_nonneg fun k _ => mul_nonneg (hã k) (pow_nonneg (Nat.cast_nonneg _) 2)
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2p : 0 < (Real.log 2) ^ (65536 : ℕ) := pow_pos hlog2 _
  refine ⟨max C1R (C0 / (Real.log 2) ^ (65536 : ℕ)), lt_max_of_lt_left hC1Rpos, fun y => ?_⟩
  have hmaxleft : C1R ≤ max C1R (C0 / (Real.log 2) ^ (65536 : ℕ)) := le_max_left _ _
  have hmaxright : C0 / (Real.log 2) ^ (65536 : ℕ) ≤ max C1R (C0 / (Real.log 2) ^ (65536 : ℕ)) :=
    le_max_right _ _
  by_cases hy : X1 ≤ y
  · have h := h1 y hy
    by_cases hy0 : y = 0
    · have hL : (∑ k ∈ Finset.Icc 1 y, Work.FITop.atilFIa k * ((k.divisors.card : ℝ) ^ 2)) = 0 := by
        rw [hy0]; simp
      rw [hL]
      have hÃ0 : (0 : ℝ) ≤ Work.FITop.AcountAtil y := hÃnn y
      have hlg : (0 : ℝ) ≤ (Real.log ((y : ℝ) + 2)) ^ (65536 : ℕ) := by
        have hpos : (1 : ℝ) < (y : ℝ) + 2 := by
          have : (0 : ℝ) ≤ (y : ℝ) := Nat.cast_nonneg y
          linarith
        exact pow_nonneg (le_of_lt (Real.log_pos hpos)) 65536
      exact mul_nonneg (mul_nonneg (le_trans hC1R0 hmaxleft) (by linarith)) hlg
    · have hy1 : 1 ≤ y := by omega
      have hy1R : (1 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy1
      have hlogy0 : 0 ≤ Real.log (y : ℝ) := Real.log_nonneg hy1R
      have hlogyle : Real.log (y : ℝ) ≤ Real.log ((y : ℝ) + 2) :=
        Real.log_le_log (by linarith) (by linarith)
      have hpow : (Real.log (y : ℝ)) ^ (65536 : ℕ) ≤ (Real.log ((y : ℝ) + 2)) ^ (65536 : ℕ) :=
        pow_le_pow_left₀ hlogy0 hlogyle 65536
      have hlg0 : 0 ≤ (Real.log ((y : ℝ) + 2)) ^ (65536 : ℕ) :=
        pow_nonneg (le_of_lt (Real.log_pos (by linarith))) _
      have step1 : C1R * Work.FITop.AcountAtil y * (Real.log (y : ℝ)) ^ (65536 : ℕ)
          ≤ C1R * Work.FITop.AcountAtil y * (Real.log ((y : ℝ) + 2)) ^ (65536 : ℕ) :=
        mul_le_mul_of_nonneg_left hpow (mul_nonneg hC1R0 (hÃnn y))
      have step2 : C1R * Work.FITop.AcountAtil y * (Real.log ((y : ℝ) + 2)) ^ (65536 : ℕ)
          ≤ C1R * (Work.FITop.AcountAtil y + 1) * (Real.log ((y : ℝ) + 2)) ^ (65536 : ℕ) := by
        apply mul_le_mul_of_nonneg_right _ hlg0
        exact mul_le_mul_of_nonneg_left (by linarith [hÃnn y]) hC1R0
      have step3 : C1R * (Work.FITop.AcountAtil y + 1) * (Real.log ((y : ℝ) + 2)) ^ (65536 : ℕ)
          ≤ max C1R (C0 / (Real.log 2) ^ (65536 : ℕ)) * (Work.FITop.AcountAtil y + 1)
            * (Real.log ((y : ℝ) + 2)) ^ (65536 : ℕ) := by
        apply mul_le_mul_of_nonneg_right _ hlg0
        exact mul_le_mul_of_nonneg_right hmaxleft (by linarith [hÃnn y])
      have hh : (∑ k ∈ Finset.Icc 1 y, Work.FITop.atilFIa k * ((k.divisors.card : ℝ) ^ 2))
          ≤ C1R * Work.FITop.AcountAtil y * (Real.log (y : ℝ)) ^ (65536 : ℕ) := by
        rw [hC1R]; exact h
      exact le_trans hh (le_trans step1 (le_trans step2 step3))
  · have hyX1 : y ≤ X1 := by omega
    have hsub : Finset.Icc 1 y ⊆ Finset.Icc 1 X1 := by
      intro k hk
      obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.mp hk
      exact Finset.mem_Icc.mpr ⟨hk1, le_trans hk2 hyX1⟩
    have hC0' : (∑ k ∈ Finset.Icc 1 y, Work.FITop.atilFIa k * ((k.divisors.card : ℝ) ^ 2))
        ≤ C0 := by
      rw [hC0]
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun k _ _ => mul_nonneg (hã k) (pow_nonneg (Nat.cast_nonneg _) 2))
    have hlog2le : Real.log 2 ≤ Real.log ((y : ℝ) + 2) := by
      apply Real.log_le_log (by norm_num)
      have : (0 : ℝ) ≤ (y : ℝ) := Nat.cast_nonneg y
      linarith
    have hpow2 : (Real.log 2) ^ (65536 : ℕ) ≤ (Real.log ((y : ℝ) + 2)) ^ (65536 : ℕ) :=
      pow_le_pow_left₀ (le_of_lt hlog2) hlog2le 65536
    have hlg0 : 0 ≤ (Real.log ((y : ℝ) + 2)) ^ (65536 : ℕ) :=
      pow_nonneg (le_trans (le_of_lt hlog2) hlog2le) _
    have hstepA : C0 = (C0 / (Real.log 2) ^ (65536 : ℕ)) * (Real.log 2) ^ (65536 : ℕ) := by
      rw [div_mul_cancel₀]
      exact pow_ne_zero _ (ne_of_gt hlog2)
    have hstepB : (C0 / (Real.log 2) ^ (65536 : ℕ)) * (Real.log 2) ^ (65536 : ℕ)
        ≤ (C0 / (Real.log 2) ^ (65536 : ℕ)) * (Real.log ((y : ℝ) + 2)) ^ (65536 : ℕ) :=
      mul_le_mul_of_nonneg_left hpow2 (div_nonneg hC00 (le_of_lt hlog2p))
    have hstepC : (C0 / (Real.log 2) ^ (65536 : ℕ)) * (Real.log ((y : ℝ) + 2)) ^ (65536 : ℕ)
        ≤ max C1R (C0 / (Real.log 2) ^ (65536 : ℕ)) * (Work.FITop.AcountAtil y + 1)
          * (Real.log ((y : ℝ) + 2)) ^ (65536 : ℕ) := by
      have hmax0 : 0 ≤ max C1R (C0 / (Real.log 2) ^ (65536 : ℕ)) := le_trans hC1R0 hmaxleft
      calc (C0 / (Real.log 2) ^ (65536 : ℕ)) * (Real.log ((y : ℝ) + 2)) ^ (65536 : ℕ)
          ≤ max C1R (C0 / (Real.log 2) ^ (65536 : ℕ)) * (Real.log ((y : ℝ) + 2)) ^ (65536 : ℕ) :=
            mul_le_mul_of_nonneg_right hmaxright hlg0
        _ ≤ max C1R (C0 / (Real.log 2) ^ (65536 : ℕ)) * (Work.FITop.AcountAtil y + 1)
              * (Real.log ((y : ℝ) + 2)) ^ (65536 : ℕ) := by
            have h1le : (1 : ℝ) ≤ Work.FITop.AcountAtil y + 1 := by linarith [hÃnn y]
            apply mul_le_mul_of_nonneg_right _ hlg0
            simpa using mul_le_mul_of_nonneg_left h1le hmax0
    exact le_trans hC0' (le_trans (le_of_eq hstepA) (le_trans hstepB hstepC))

end

end Work.FITop4.Red5
