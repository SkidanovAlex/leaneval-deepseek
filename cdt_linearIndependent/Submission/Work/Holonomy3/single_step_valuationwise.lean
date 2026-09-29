import Mathlib
import Submission.Work.Holonomy3.defs
import Submission.Commons.NumberTheory.Chebyshev.lcmUpto_dvd_of_le

namespace Work.Holonomy3

open Submission.CDTPlan
open scoped BigOperators

/-- On a linearly ordered index type, two monotone real functions monovary. -/
private lemma monovary_of_monotone {N : ℕ} {f g : Fin N → ℝ} (hf : Monotone f) (hg : Monotone g) :
    Monovary f g := by
  intro i j hij
  have hlt : i < j := by
    by_contra h
    push_neg at h
    exact absurd (hg h) (not_le.mpr hij)
  exact hf hlt.le

theorem single_step_valuationwise (p : ℕ) (hp : p.Prime) {m k : ℕ} (u c : ℕ)
    (n : Fin (m * k) → ℕ) (hn : Monotone n) (π : Equiv.Perm (Fin (m * k))) :
    (∑ j : Fin (m * k),
      if u ≤ (j : ℕ) / k then ((Submission.CDTPlan.lcmUpto (c * n (π j))).factorization p) else 0)
      ≤ ∑ j : Fin (m * k),
        if u ≤ (j : ℕ) / k then ((Submission.CDTPlan.lcmUpto (c * n j)).factorization p) else 0 := by
  classical
  set f : Fin (m * k) → ℝ := fun j => if u ≤ (j : ℕ) / k then 1 else 0 with hf
  set g : Fin (m * k) → ℝ :=
    fun t => ((Submission.CDTPlan.lcmUpto (c * n t)).factorization p : ℝ) with hg
  have hfmono : Monotone f := by
    rw [hf]
    intro i j hij
    have hval : (i : ℕ) ≤ (j : ℕ) := Fin.le_iff_val_le_val.mp hij
    by_cases hi : u ≤ (i : ℕ) / k
    · by_cases hj : u ≤ (j : ℕ) / k
      · simp [hi, hj]
      · exfalso
        have h1 : (i : ℕ) / k ≤ (j : ℕ) / k := Nat.div_le_div_right hval
        omega
    · by_cases hj : u ≤ (j : ℕ) / k
      · simp [hi, hj]
      · simp [hi, hj]
  have hgmono : Monotone g := by
    rw [hg]
    intro s t hst
    refine Nat.cast_le.mpr ?_
    have hdvd : Submission.CDTPlan.lcmUpto (c * n s) ∣ Submission.CDTPlan.lcmUpto (c * n t) :=
      Commons.NumberTheory.Chebyshev.lcmUpto_dvd_of_le (Nat.mul_le_mul_left c (hn hst))
    have hs0 : (Submission.CDTPlan.lcmUpto (c * n s)) ≠ 0 := (Nat.lcmUpto_pos _).ne'
    have ht0 : (Submission.CDTPlan.lcmUpto (c * n t)) ≠ 0 := (Nat.lcmUpto_pos _).ne'
    have hfac := (Nat.factorization_le_iff_dvd hs0 ht0).mpr hdvd
    exact (Finsupp.le_def.mp hfac) p
  have hcast_π : ((∑ j : Fin (m * k),
      (if u ≤ (j : ℕ) / k then
        (Submission.CDTPlan.lcmUpto (c * n (π j))).factorization p else 0) : ℕ) : ℝ)
      = ∑ j, f j * g (π j) := by
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hf, hg]
    by_cases h : u ≤ (j : ℕ) / k <;> simp [h]
  have hcast_id : ((∑ j : Fin (m * k),
      (if u ≤ (j : ℕ) / k then
        (Submission.CDTPlan.lcmUpto (c * n j)).factorization p else 0) : ℕ) : ℝ)
      = ∑ j, f j * g j := by
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hf, hg]
    by_cases h : u ≤ (j : ℕ) / k <;> simp [h]
  have hmono : Monovary f g := monovary_of_monotone hfmono hgmono
  have hℝ : ∑ j, f j * g (π j) ≤ ∑ j, f j * g j := hmono.sum_mul_comp_perm_le_sum_mul
  rw [← hcast_π, ← hcast_id] at hℝ
  exact Nat.cast_le.mp hℝ

end Work.Holonomy3
