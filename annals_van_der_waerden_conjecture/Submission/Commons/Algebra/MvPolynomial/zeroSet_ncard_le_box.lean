import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Rat.Star
import Mathlib.RingTheory.SimpleRing.Principal

namespace Commons.Algebra.MvPolynomial

open scoped BigOperators
open Finset Fintype

/-- Schwartz-Zippel over a (uniform) finite subset of a field: a nonzero `m`-variable polynomial
over a field vanishes at at most `m · d · #S^(m-1)` points of `S^m` when each variable occurs with
degree at most `d`.  Useful with `S = Icc (-H) H ⊆ ℚ` to count integer zeros of a fixed integer
polynomial in a box, and with `S = ZMod p` for mod-`p` root counts. -/
theorem zeroSet_ncard_le_box {F : Type*} [Field F] [DecidableEq F] (m : ℕ)
    (h : MvPolynomial (Fin m) F) (hh : h ≠ 0) (S : Finset F) (d : ℕ)
    (hdeg : ∀ i : Fin m, h.degreeOf i ≤ d) :
    ({x : Fin m → F | (∀ i, x i ∈ S) ∧ MvPolynomial.eval x h = 0} : Set (Fin m → F)).ncard ≤
      m * d * S.card ^ (m - 1) := by
  -- Relate the set of zeros inside `S^m` to the corresponding `Finset` cardinality.
  have hlink :
      ({x : Fin m → F | (∀ i, x i ∈ S) ∧ MvPolynomial.eval x h = 0} : Set (Fin m → F)).ncard =
        ((Fintype.piFinset (fun _ : Fin m => S)).filter (fun x => MvPolynomial.eval x h = 0)).card := by
    have hset : ({x : Fin m → F | (∀ i, x i ∈ S) ∧ MvPolynomial.eval x h = 0} : Set (Fin m → F)) =
        ↑((Fintype.piFinset (fun _ : Fin m => S)).filter (fun x => MvPolynomial.eval x h = 0)) := by
      ext x
      simp only [Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_filter, Fintype.mem_piFinset]
    rw [hset, Set.ncard_coe_finset]
  rw [hlink]
  -- Two cases: no variables, or at least one variable.
  rcases m with _ | m
  · -- m = 0 : a nonzero constant polynomial has no zeros.
    have hSZ0 := MvPolynomial.schwartz_zippel_sum_degreeOf (R := F) hh (fun _ : Fin 0 => S)
    have hle :
        (((Fintype.piFinset (fun _ : Fin 0 => S)).filter
            (fun x : Fin 0 → F => MvPolynomial.eval x h = 0)).card : ℚ≥0) ≤ 0 := by
      simpa using hSZ0
    have hcard : ((Fintype.piFinset (fun _ : Fin 0 => S)).filter
        (fun x : Fin 0 → F => MvPolynomial.eval x h = 0)).card ≤ 0 := by
      exact_mod_cast hle
    simpa using hcard
  · -- m ≥ 1 : split into `S = ∅` and `S ≠ ∅`.
    by_cases hS : S.Nonempty
    · -- Nonempty case: the Schwartz-Zippel lemma of Mathlib gives the bound in terms of fractions.
      let Z : Finset (Fin (m + 1) → F) :=
        (Fintype.piFinset (fun _ : Fin (m + 1) => S)).filter (fun x => MvPolynomial.eval x h = 0)
      have hSZ := MvPolynomial.schwartz_zippel_sum_degreeOf (R := F) hh (fun _ : Fin (m + 1) => S)
      have hfrac :
          ((Z.card : ℕ) : ℚ≥0) / ((S.card : ℚ≥0) ^ (m + 1))
            ≤ ((((m + 1) * d : ℕ) : ℚ≥0) / (S.card : ℚ≥0)) := by
        calc
          ((Z.card : ℕ) : ℚ≥0) / ((S.card : ℚ≥0) ^ (m + 1))
              = (Z.card : ℚ≥0) / (∏ i : Fin (m + 1), (S.card : ℚ≥0)) := by
                  congr 1
                  rw [Finset.prod_const]
                  congr 1
                  simp
          _ ≤ ∑ i : Fin (m + 1), (h.degreeOf i : ℚ≥0) / (S.card : ℚ≥0) := by
                  simpa [Z] using hSZ
          _ ≤ ∑ i : Fin (m + 1), (d : ℚ≥0) / (S.card : ℚ≥0) := by
                  gcongr with i
                  exact_mod_cast hdeg i
          _ = (((m + 1) * d : ℕ) : ℚ≥0) / (S.card : ℚ≥0) := by
                  rw [Finset.sum_const]
                  simp
                  ring_nf
      have hk : S.card ≠ 0 := Finset.card_ne_zero.mpr hS
      have hk0 : (S.card : ℚ≥0) ≠ 0 := by exact_mod_cast hk
      have hpow : (S.card : ℚ≥0) ^ (m + 1) ≠ 0 := pow_ne_zero _ hk0
      have h2 : (Z.card : ℚ≥0) ≤ (((m + 1) * d : ℕ) : ℚ≥0) * (S.card : ℚ≥0) ^ m := by
        calc
          (Z.card : ℚ≥0)
              = (Z.card : ℚ≥0) / (S.card : ℚ≥0) ^ (m + 1) * (S.card : ℚ≥0) ^ (m + 1) := by
                  exact (div_mul_cancel₀ (Z.card : ℚ≥0) hpow).symm
          _ ≤ (((m + 1) * d : ℕ) : ℚ≥0) / (S.card : ℚ≥0) * (S.card : ℚ≥0) ^ (m + 1) := by
                  exact mul_le_mul_of_nonneg_right hfrac (by positivity)
          _ = (((m + 1) * d : ℕ) : ℚ≥0) * (S.card : ℚ≥0) ^ m := by
                  rw [pow_succ]
                  rw [mul_comm ((S.card : ℚ≥0) ^ m) (S.card : ℚ≥0)]
                  rw [← mul_assoc]
                  rw [div_mul_cancel₀ _ hk0]
      have hfin : Z.card ≤ (m + 1) * d * S.card ^ m := by
        exact_mod_cast h2
      simpa [Z] using hfin
    · -- Empty case: there are no points of `S^(m+1)` at all.
      have hpi : (Fintype.piFinset (fun _ : Fin (m + 1) => S)) = ∅ := by
        rw [← Finset.not_nonempty_iff_eq_empty]
        rintro ⟨x, hx⟩
        have hx0 : x (0 : Fin (m + 1)) ∈ S := (Fintype.mem_piFinset.mp hx) 0
        exact hS ⟨x (0 : Fin (m + 1)), hx0⟩
      have hc0 : ((Fintype.piFinset (fun _ : Fin (m + 1) => S)).filter
          (fun x : Fin (m + 1) → F => MvPolynomial.eval x h = 0)).card = 0 := by
        rw [hpi]
        simp
      rw [hc0]
      have hSempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
      rw [hSempty, Finset.card_empty]
      omega

end Commons.Algebra.MvPolynomial