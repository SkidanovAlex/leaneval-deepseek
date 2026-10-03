import Mathlib
import Submission.Work.Peluse.UControl.HistDefs

/-!
# Basic lemmas for the history-indexed PET chain

* the general coefficient lemma `polyCoeffCompXAddC` for `p.comp (X + C c)`;
* `histShiftNeZero` (`shift h ≠ 0` for `h ≠ 0`) and `histSnocZeroFalse`.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.UControl

noncomputable section

open Polynomial

/-! ## The coefficient of `y^(d-1)` in `p(y + c)` -/

lemma polyCoeffCompXAddC {R : Type*} [CommSemiring R] (p : Polynomial R) (c : R) (d : ℕ)
    (hdeg : p.natDegree = d) :
    (p.comp (Polynomial.X + Polynomial.C c)).coeff (d - 1)
      = p.coeff (d - 1) + d • (p.coeff d * c) := by
  classical
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · -- `d = 0`: `p` is constant
    subst hd0
    rw [Polynomial.eq_C_of_natDegree_eq_zero hdeg, nsmul_eq_mul]
    simp
  have hexp : p.comp (Polynomial.X + Polynomial.C c)
      = p.sum (fun k a => Polynomial.C a * (Polynomial.X + Polynomial.C c) ^ k) := by
    conv_lhs => rw [← Polynomial.sum_C_mul_X_pow_eq p]
    rw [Polynomial.sum_def, Polynomial.sum_comp, Polynomial.sum_def]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Polynomial.C_mul_comp, Polynomial.pow_comp, Polynomial.X_comp]
  rw [hexp, Polynomial.coeff_sum, Polynomial.sum_def]
  have hterm : ∀ k : ℕ, (Polynomial.C (p.coeff k)
        * (Polynomial.X + Polynomial.C c) ^ k).coeff (d - 1)
      = p.coeff k * (c ^ (k - (d - 1)) * ↑(k.choose (d - 1))) := by
    intro k
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_add_C_pow]
  rw [Finset.sum_congr rfl (fun k _ => hterm k)]
  have hmain : ∀ k ∈ p.support, p.coeff k * (c ^ (k - (d - 1)) * ↑(k.choose (d - 1)))
      = (if k = d - 1 then p.coeff (d - 1) else 0)
        + (if k = d then p.coeff d * (↑d * c) else 0) := by
    intro k hk
    have hkd : k ≤ d := by
      simpa [hdeg] using Polynomial.le_natDegree_of_mem_supp k hk
    rcases lt_trichotomy k (d - 1) with hlt | heq | hgt
    · have hch : k.choose (d - 1) = 0 := Nat.choose_eq_zero_of_lt hlt
      have hne1 : ¬ (k = d - 1) := ne_of_lt hlt
      have hne2 : ¬ (k = d) := by
        exact ne_of_lt (lt_of_lt_of_le hlt (Nat.sub_le d 1))
      simp only [hch, Nat.cast_zero, mul_zero, if_neg hne1, if_neg hne2, add_zero]
    · have hne2 : ¬ (d - 1 = d) := by omega
      have hch : (d - 1).choose (d - 1) = 1 := Nat.choose_self _
      rw [heq, hch, Nat.cast_one, Nat.sub_self, pow_zero, mul_one, mul_one,
        if_pos rfl, if_neg hne2, add_zero]
    · have hkd' : k = d := by omega
      have hch : d.choose (d - 1) = d := by
        nth_rw 1 [show d = (d - 1) + 1 by omega]
        rw [Nat.choose_succ_self_right]
        omega
      have hsub : d - (d - 1) = 1 := by omega
      have hne1 : ¬ (d = d - 1) := by omega
      rw [hkd', hch, hsub, pow_one, if_pos rfl, if_neg hne1, zero_add]
      ring
  rw [Finset.sum_congr rfl hmain, Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.sum_ite_eq', nsmul_eq_mul]
  by_cases h1 : d - 1 ∈ p.support
  · rw [if_pos h1]
    by_cases h2 : d ∈ p.support
    · rw [if_pos h2]; ring
    · rw [if_neg h2]
      have hz2 : p.coeff d = 0 := by
        by_contra hc
        exact h2 (Polynomial.mem_support_iff.mpr hc)
      rw [hz2]
      ring
  · rw [if_neg h1]
    have hz1 : p.coeff (d - 1) = 0 := by
      by_contra hc
      exact h1 (Polynomial.mem_support_iff.mpr hc)
    rw [hz1]
    by_cases h2 : d ∈ p.support
    · rw [if_pos h2]
      ring
    · rw [if_neg h2]
      have hz2 : p.coeff d = 0 := by
        by_contra hc
        exact h2 (Polynomial.mem_support_iff.mpr hc)
      rw [hz2]
      ring

theorem histWeightEq {d n : ℕ} (X : HistData d n) (j : Fin (d + 1)) :
    X.weightH j = ((X.toSym).S.weight d j) := rfl

/-! ## The shift of a history -/

lemma histShiftNeZero {n : ℕ} {h : Fin n → Bool} (hh : h ≠ 0) : HistData.shift h ≠ 0 := by
  intro hzero
  apply hh
  funext i
  by_contra hi
  have htrue : h i = true := by
    cases hb : h i with
    | false => exact absurd hb hi
    | true => rfl
  have hshift' : HistData.shift h
      = ∑ j ∈ (Finset.univ.filter (fun j : Fin n => h j)), MvPolynomial.X j := by
    rw [HistData.shift]
    rw [Finset.sum_filter]
  have hval0 : MvPolynomial.eval (fun j : Fin n => if j = i then (1 : ℤ) else 0)
      (HistData.shift h) = 0 := by rw [hzero]; simp
  have hval1 : MvPolynomial.eval (fun j : Fin n => if j = i then (1 : ℤ) else 0)
      (HistData.shift h) = 1 := by
    rw [hshift', map_sum]
    simp only [MvPolynomial.eval_X]
    rw [Finset.sum_ite_eq']
    simp [htrue]
  rw [hval0] at hval1
  exact zero_ne_one hval1

lemma histSnocZeroFalse {n : ℕ} :
    (Fin.snoc (α := fun _ => Bool) (0 : Fin n → Bool) false : Fin (n + 1) → Bool) = 0 := by
  funext i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · rw [Fin.snoc_castSucc]; rfl
  · rw [Fin.snoc_last]; rfl

end

end Work.Peluse.UControl
