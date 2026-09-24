import Mathlib
import Submission.Work.ChenPlan.LinearSieve.FrameworkR

/-!
# The Rosser–Iwaniec tail bound `Σ_{y ≤ p < y'} ν(p) V(p)/V(y') ≤ log z/log y (1 + K/log y) - 1`

This is the "Buchstab telescoping" step of the Rosser–Iwaniec linear sieve: the total mass of the
first Buchstab layer between the two limits `y ≤ y'`, measured *relative to* `V(y')`, is bounded
by the reciprocal product `∏_{p ≥ y} (1 - ν p)⁻¹` minus `1`, and hence — by the linear sieve
axiom `IsLinear` at `w = y` — by `(log z/log y)(1 + K/log y) - 1`.

The proof is the exact telescoping of

`ν(p) · V(p) = V(p) - V(p⁺)`   (`p⁺` the next prime of `P` above `p`),

equivalently `ν(p) ∏_{q < p}(1 - ν q) = ∏_{q < p}(1 - ν q) - ∏_{q ≤ p}(1 - ν q)`, which for
natural arguments is the clean identity `V(t) - V(t+1) = ν(t) · V(t)` for `t ∈ P` and `0`
otherwise; summing over `t ∈ [⌈y⌉, ⌈y'⌉)` telescopes to `V(y) - V(y')`.

* `filter_lt_succ_eq` : `S.filter (· < t+1)` splits off the element `t` when `t ∈ S`.
* `Vf_succ` / `Vf_succ_of_notMem` : `Vf` is multiplied by `1 - ν t` exactly when `t` is a prime
  of `P`.
* `Vf_sub_Vf_succ` : `Vf t - Vf (t+1) = ν t · Vf t` for `t ∈ P`, and `0` otherwise.
* `sum_Ico_sub'` : the telescoping sum over `Ico m n`.
* `sum_nu_VfR_eq` : `Σ_{y ≤ p < y'} ν p · VfR p = VfR y - VfR y'`.
* `VfR_eq_VfR_mul_prod` : `VfR y' = VfR y · ∏_{y ≤ p < y'} (1 - ν p)`.
* `VfR_ratio_le` : `VfR y / VfR y' ≤ (log z/log y)(1 + K/log y)` from `IsLinear` at `w = y`.
* `tail_bound` : the requested statement.
-/

namespace Work.ChenPlan.LinearSieve.RI

open Finset
open scoped BigOperators

noncomputable section

/-- `S.filter (fun p => p < t + 1)` splits off the element `t` when `t ∈ S`. -/
lemma filter_lt_succ_eq (S : Finset ℕ) (t : ℕ) :
    S.filter (fun p => p < t + 1)
      = if t ∈ S then insert t (S.filter (fun p => p < t)) else S.filter (fun p => p < t) := by
  by_cases ht : t ∈ S
  · rw [if_pos ht]
    ext p
    rw [mem_filter, mem_insert, mem_filter]
    constructor
    · rintro ⟨hpS, hplt⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hplt with h | h
      · exact Or.inr ⟨hpS, h⟩
      · exact Or.inl h
    · rintro (h | ⟨hpS, hplt⟩)
      · rw [h]; exact ⟨ht, Nat.lt_succ_self t⟩
      · exact ⟨hpS, Nat.lt_succ_of_lt hplt⟩
  · rw [if_neg ht]
    ext p
    rw [mem_filter, mem_filter]
    constructor
    · rintro ⟨hpS, hplt⟩
      refine ⟨hpS, ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hplt with h | h
      · exact h
      · exact absurd (h ▸ hpS) ht
    · rintro ⟨hpS, hplt⟩
      exact ⟨hpS, Nat.lt_succ_of_lt hplt⟩

/-- Passing a prime of `P` multiplies `Vf` by the sieve factor `1 - ν p`. -/
lemma Vf_succ (A : BoundingSieve) {t : ℕ} (ht : t ∈ A.prodPrimes.primeFactors) :
    Vf A (t + 1) = (1 - A.nu t) * Vf A t := by
  unfold Vf
  rw [filter_lt_succ_eq, if_pos ht, Finset.prod_insert]
  simp

/-- A non-prime of `P` leaves `Vf` unchanged. -/
lemma Vf_succ_of_notMem (A : BoundingSieve) {t : ℕ} (ht : t ∉ A.prodPrimes.primeFactors) :
    Vf A (t + 1) = Vf A t := by
  unfold Vf
  rw [filter_lt_succ_eq, if_neg ht]

/-- **The telescoping increment**: `Vf t - Vf (t+1) = ν t · Vf t` for a prime `t` of `P`, and `0`
otherwise. -/
lemma Vf_sub_Vf_succ (A : BoundingSieve) (t : ℕ) :
    Vf A t - Vf A (t + 1)
      = if t ∈ A.prodPrimes.primeFactors then A.nu t * Vf A t else 0 := by
  by_cases ht : t ∈ A.prodPrimes.primeFactors
  · rw [Vf_succ A ht, if_pos ht]; ring
  · rw [Vf_succ_of_notMem A ht, if_neg ht]; ring

/-- The telescoping sum `Σ_{m ≤ i < n} (g i - g (i+1)) = g m - g n`. -/
lemma sum_Ico_sub' (g : ℕ → ℝ) {m n : ℕ} (h : m ≤ n) :
    ∑ i ∈ Finset.Ico m n, (g i - g (i + 1)) = g m - g n := by
  have hh : ∑ i ∈ Finset.Ico m n, (g i - g (i + 1))
      = ∑ i ∈ Finset.Ico m n, (-g (i + 1) - -g i) :=
    Finset.sum_congr rfl (fun i _ => by ring)
  rw [hh, Finset.sum_Ico_sub (fun i => -g i) h]
  ring

/-- **The telescoping identity** (real limits, `ν(p) · V(p)` measured absolutely):
`Σ_{y ≤ p < y'} ν p · VfR p = VfR y - VfR y'`. -/
theorem sum_nu_VfR_eq (A : BoundingSieve) {y y' : ℝ} (hyy' : y ≤ y') :
    ∑ p ∈ A.prodPrimes.primeFactors.filter (fun p : ℕ => y ≤ (p : ℝ) ∧ (p : ℝ) < y'),
        A.nu p * VfR A (p : ℝ) = VfR A y - VfR A y' := by
  have hceil : ⌈y⌉₊ ≤ ⌈y'⌉₊ := Nat.ceil_mono hyy'
  have hf1 : A.prodPrimes.primeFactors.filter (fun p : ℕ => y ≤ (p : ℝ) ∧ (p : ℝ) < y')
      = A.prodPrimes.primeFactors.filter (fun p : ℕ => ⌈y⌉₊ ≤ p ∧ p < ⌈y'⌉₊) := by
    apply Finset.filter_congr
    intro p _
    simp only [Nat.ceil_le, Nat.lt_ceil]
  have hf2 : A.prodPrimes.primeFactors.filter (fun p : ℕ => ⌈y⌉₊ ≤ p ∧ p < ⌈y'⌉₊)
      = (Finset.Ico ⌈y⌉₊ ⌈y'⌉₊).filter (fun p : ℕ => p ∈ A.prodPrimes.primeFactors) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Ico]
    tauto
  have hsum1 : ∑ p ∈ A.prodPrimes.primeFactors.filter (fun p : ℕ => y ≤ (p : ℝ) ∧ (p : ℝ) < y'),
        A.nu p * VfR A (p : ℝ)
      = ∑ p ∈ A.prodPrimes.primeFactors.filter (fun p : ℕ => y ≤ (p : ℝ) ∧ (p : ℝ) < y'),
        A.nu p * Vf A p := by
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [VfR_eq_Vf, Nat.ceil_natCast]
  have hsum2 : ∑ p ∈ (Finset.Ico ⌈y⌉₊ ⌈y'⌉₊).filter (fun p : ℕ => p ∈ A.prodPrimes.primeFactors),
        A.nu p * Vf A p = ∑ i ∈ Finset.Ico ⌈y⌉₊ ⌈y'⌉₊, (Vf A i - Vf A (i + 1)) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    exact (Vf_sub_Vf_succ A i).symm
  rw [hsum1, hf1, hf2, hsum2, sum_Ico_sub' (Vf A) hceil, VfR_eq_Vf, VfR_eq_Vf]

/-- **The product decomposition**: `VfR y' = VfR y · ∏_{y ≤ p < y'} (1 - ν p)`. -/
lemma VfR_eq_VfR_mul_prod (A : BoundingSieve) {y y' : ℝ} (hyy' : y ≤ y') :
    VfR A y' = VfR A y * ∏ p ∈ A.prodPrimes.primeFactors.filter
        (fun p : ℕ => y ≤ (p : ℝ) ∧ (p : ℝ) < y'), (1 - A.nu p) := by
  have h1 : A.prodPrimes.primeFactors.filter (fun p : ℕ => (p : ℝ) < y')
      = A.prodPrimes.primeFactors.filter (fun p : ℕ => (p : ℝ) < y)
        ∪ A.prodPrimes.primeFactors.filter (fun p : ℕ => y ≤ (p : ℝ) ∧ (p : ℝ) < y') := by
    rw [← Finset.filter_or]
    apply Finset.filter_congr
    intro p _
    constructor
    · intro h
      rcases lt_or_ge (p : ℝ) y with hlt | hge
      · exact Or.inl hlt
      · exact Or.inr ⟨hge, h⟩
    · rintro (h | ⟨h1, h2⟩)
      · linarith
      · exact h2
  have hdisj : Disjoint (A.prodPrimes.primeFactors.filter (fun p : ℕ => (p : ℝ) < y))
      (A.prodPrimes.primeFactors.filter (fun p : ℕ => y ≤ (p : ℝ) ∧ (p : ℝ) < y')) := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    rw [Finset.mem_filter] at hp1 hp2
    linarith [hp1.2, hp2.2.1]
  unfold VfR
  rw [h1, Finset.prod_union hdisj]

/-- **The `V`-ratio bound**: `VfR y / VfR y' ≤ (log z/log y)(1 + K/log y)`, which is the linear
sieve axiom `IsLinear A z K` at the sub-limit `w = y` (the tail `p ≥ y'` of the reciprocal product
is `≤ 1`). -/
lemma VfR_ratio_le (A : BoundingSieve) {z K y y' : ℝ} (hK : 0 ≤ K)
    (hlin : Submission.ChenPlan.IsLinear A z K) (hy : 2 ≤ y) (hyy' : y ≤ y') (hyz : y' ≤ z) :
    VfR A y / VfR A y' ≤ (Real.log z / Real.log y) * (1 + K / Real.log y) := by
  have hyz'' : y ≤ z := le_trans hyy' hyz
  have hlogy : 0 < Real.log y := Real.log_pos (by linarith)
  rcases lt_or_ge y z with hyltz | hzley
  · have hdecomp : VfR A y' = VfR A y * ∏ p ∈ A.prodPrimes.primeFactors.filter
        (fun p : ℕ => y ≤ (p : ℝ) ∧ (p : ℝ) < y'), (1 - A.nu p) := VfR_eq_VfR_mul_prod A hyy'
    have hdiv : VfR A y / VfR A y' = 1 / (∏ p ∈ A.prodPrimes.primeFactors.filter
        (fun p : ℕ => y ≤ (p : ℝ) ∧ (p : ℝ) < y'), (1 - A.nu p)) := by
      rw [hdecomp, div_mul_eq_div_div, div_self (ne_of_gt (VfR_pos A y))]
    rw [hdiv]
    have hTpos : 0 < ∏ p ∈ A.prodPrimes.primeFactors.filter
        (fun p : ℕ => y ≤ (p : ℝ) ∧ (p : ℝ) < y'), (1 - A.nu p) :=
      Finset.prod_pos (fun p hp => Vf_factor_pos A (Finset.mem_filter.mp hp).1)
    have hTbpos : 0 < ∏ p ∈ A.prodPrimes.primeFactors.filter
        (fun p : ℕ => y ≤ (p : ℝ)), (1 - A.nu p) :=
      Finset.prod_pos (fun p hp => Vf_factor_pos A (Finset.mem_filter.mp hp).1)
    have hsub : A.prodPrimes.primeFactors.filter (fun p : ℕ => y ≤ (p : ℝ) ∧ (p : ℝ) < y')
        ⊆ A.prodPrimes.primeFactors.filter (fun p : ℕ => y ≤ (p : ℝ)) := by
      intro p hp
      rw [Finset.mem_filter] at hp ⊢
      exact ⟨hp.1, hp.2.1⟩
    have hTb_le_T : (∏ p ∈ A.prodPrimes.primeFactors.filter (fun p : ℕ => y ≤ (p : ℝ)),
          (1 - A.nu p))
        ≤ ∏ p ∈ A.prodPrimes.primeFactors.filter (fun p : ℕ => y ≤ (p : ℝ) ∧ (p : ℝ) < y'),
          (1 - A.nu p) := by
      refine Finset.prod_le_prod_of_subset_of_le_one₀ hsub ?_ ?_
      · intro i hi
        exact Vf_factor_nonneg A (Finset.mem_filter.mp hi).1
      · intro i hi _
        exact Vf_factor_le_one A (Finset.mem_filter.mp hi).1
    have hinv : 1 / (∏ p ∈ A.prodPrimes.primeFactors.filter
          (fun p : ℕ => y ≤ (p : ℝ) ∧ (p : ℝ) < y'), (1 - A.nu p))
        ≤ 1 / (∏ p ∈ A.prodPrimes.primeFactors.filter (fun p : ℕ => y ≤ (p : ℝ)),
          (1 - A.nu p)) := one_div_le_one_div_of_le hTbpos hTb_le_T
    have hTb_inv : 1 / (∏ p ∈ A.prodPrimes.primeFactors.filter (fun p : ℕ => y ≤ (p : ℝ)),
          (1 - A.nu p))
        = ∏ p ∈ A.prodPrimes.primeFactors.filter (fun p : ℕ => y ≤ (p : ℝ)),
          (1 - A.nu p)⁻¹ := by
      rw [one_div, Finset.prod_inv_distrib]
    have hIsLin := hlin.2 y hy hyltz
    calc 1 / (∏ p ∈ A.prodPrimes.primeFactors.filter
            (fun p : ℕ => y ≤ (p : ℝ) ∧ (p : ℝ) < y'), (1 - A.nu p))
        ≤ 1 / (∏ p ∈ A.prodPrimes.primeFactors.filter (fun p : ℕ => y ≤ (p : ℝ)),
          (1 - A.nu p)) := hinv
      _ = ∏ p ∈ A.prodPrimes.primeFactors.filter (fun p : ℕ => y ≤ (p : ℝ)),
          (1 - A.nu p)⁻¹ := hTb_inv
      _ ≤ (Real.log z / Real.log y) * (1 + K / Real.log y) := hIsLin
  · -- `z ≤ y`: then `z = y' = y`, the filter is empty and the ratio is `1`
    have hzy : z = y := le_antisymm hzley hyz''
    have hy'y : y' = y := le_antisymm (hzy ▸ hyz) hyy'
    rw [hy'y, hzy, div_self (ne_of_gt (VfR_pos A y)), div_self (ne_of_gt hlogy), one_mul]
    have : 0 ≤ K / Real.log y := div_nonneg hK (le_of_lt hlogy)
    linarith

/-- The Rosser–Iwaniec tail sum, normalised by `VfR y'`, equals `VfR y / VfR y' - 1`. -/
lemma sum_nu_VfR_div_eq (A : BoundingSieve) {y y' : ℝ} (hyy' : y ≤ y') :
    ∑ p ∈ A.prodPrimes.primeFactors.filter (fun p : ℕ => y ≤ (p : ℝ) ∧ (p : ℝ) < y'),
        A.nu p * (VfR A (p : ℝ) / VfR A y')
      = VfR A y / VfR A y' - 1 := by
  have hVpos : 0 < VfR A y' := VfR_pos A y'
  have hL : ∑ p ∈ A.prodPrimes.primeFactors.filter (fun p : ℕ => y ≤ (p : ℝ) ∧ (p : ℝ) < y'),
        A.nu p * (VfR A (p : ℝ) / VfR A y')
      = (∑ p ∈ A.prodPrimes.primeFactors.filter (fun p : ℕ => y ≤ (p : ℝ) ∧ (p : ℝ) < y'),
          A.nu p * VfR A (p : ℝ)) / VfR A y' := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [mul_div_assoc]
  rw [hL, sum_nu_VfR_eq A hyy', sub_div, div_self (ne_of_gt hVpos)]

/-- **The tail bound** (the requested lemma): the mass of the first Buchstab layer between `y` and
`y'`, normalised by `V(y')`, is at most `(log z/log y)(1 + K/log y) - 1`. -/
theorem tail_bound (A : BoundingSieve) {z K y y' : ℝ} (hK : 0 ≤ K)
    (hlin : Submission.ChenPlan.IsLinear A z K) (hy : 2 ≤ y) (hyy' : y ≤ y') (hyz : y' ≤ z) :
    ∑ p ∈ A.prodPrimes.primeFactors.filter (fun p : ℕ => y ≤ (p:ℝ) ∧ (p:ℝ) < y'),
        A.nu p * (Work.ChenPlan.LinearSieve.VfR A (p:ℝ) / Work.ChenPlan.LinearSieve.VfR A y')
      ≤ (Real.log z / Real.log y) * (1 + K / Real.log y) - 1 := by
  rw [sum_nu_VfR_div_eq A hyy']
  have h := VfR_ratio_le A hK hlin hy hyy' hyz
  linarith

end

end Work.ChenPlan.LinearSieve.RI
