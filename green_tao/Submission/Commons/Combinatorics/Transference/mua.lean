import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Submission.Commons.Algebra.BigOperators.prod_sub_const_expand

open Finset

namespace Commons.Combinatorics.Transference

/-- The alternating sum `∑_{S} (-1)^{n - |S|}` over all finsets `S` of a nonempty finite
type vanishes.  This is the `g ≡ 1` case of the multilinear expansion
`prod_sub_const_expand`. -/
lemma sum_neg_one_pow_card_sub {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] :
    ∑ S : Finset ι, (-1 : ℝ) ^ (Fintype.card ι - S.card) = 0 := by
  have h := Commons.Algebra.BigOperators.prod_sub_const_expand (fun _ : ι => (1 : ℝ)) (1 : ℝ)
  have hprod : (∏ _i : ι, ((1 : ℝ) - 1)) = 0 := by
    rw [Finset.prod_const, Finset.card_univ, sub_self]
    exact zero_pow (Fintype.card_ne_zero (α := ι))
  rw [hprod] at h
  simpa using h.symm

/-- Core transference step.  If the averaged products of `f` over every nonempty index set are
within `ε` of `1` (`|M⁻¹ ∑_x ∏_{ω∈A} f_ω(x) - 1| ≤ ε`), then the full multilinear (Möbius)
expansion `∏_ω (f_ω - 1)` is bounded by `2^{|ι|} · ε`.  The proof expands the product over the
powerset of `ι` (identified with all finsets), swaps the two finite sums and cancels the
constant term `∑_S (-1)^{n-|S|} = 0`. -/
lemma mua_core {ι X : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [Fintype X] [Nonempty X]
    (f : ι → X → ℝ) (M ε : ℝ) (hM : M = (Fintype.card X : ℝ))
    (h : ∀ A : Finset ι, A.Nonempty → |M⁻¹ * (∑ x, ∏ ω ∈ A, f ω x) - 1| ≤ ε) :
    |M⁻¹ * (∑ x, ∏ ω : ι, (f ω x - 1))| ≤ (2 : ℝ) ^ (Fintype.card ι) * ε := by
  classical
  have hcardX : (Fintype.card X : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero (α := X)
  have hM1 : M⁻¹ * (Fintype.card X : ℝ) = 1 := by
    rw [hM]; exact inv_mul_cancel₀ hcardX
  have hε : 0 ≤ ε := le_trans (abs_nonneg _) (h Finset.univ Finset.univ_nonempty)
  have hT0 : M⁻¹ * (∑ x : X, ∏ ω ∈ (∅ : Finset ι), f ω x) - 1 = 0 := by
    have hsum : (∑ x : X, ∏ ω ∈ (∅ : Finset ι), f ω x) = (Fintype.card X : ℝ) := by
      simp only [Finset.prod_empty, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    rw [hsum, hM1, sub_self]
  have hx : ∀ x : X, ∏ ω : ι, (f ω x - 1)
      = ∑ S : Finset ι, ((-1 : ℝ) ^ (Fintype.card ι - S.card)) * ∏ ω ∈ S, f ω x :=
    fun x => Commons.Algebra.BigOperators.prod_sub_const_expand (fun ω => f ω x) 1
  have hstep1 : (∑ x : X, ∏ ω : ι, (f ω x - 1))
      = ∑ x : X, ∑ S : Finset ι,
          ((-1 : ℝ) ^ (Fintype.card ι - S.card)) * ∏ ω ∈ S, f ω x :=
    Finset.sum_congr rfl (fun x _ => hx x)
  have hstep2 : (∑ x : X, ∑ S : Finset ι,
          ((-1 : ℝ) ^ (Fintype.card ι - S.card)) * ∏ ω ∈ S, f ω x)
      = ∑ S : Finset ι,
          ((-1 : ℝ) ^ (Fintype.card ι - S.card)) * ∑ x : X, ∏ ω ∈ S, f ω x := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro S _
    rw [← Finset.mul_sum]
  have key : M⁻¹ * (∑ x : X, ∏ ω : ι, (f ω x - 1))
      = ∑ S : Finset ι, ((-1 : ℝ) ^ (Fintype.card ι - S.card))
          * (M⁻¹ * (∑ x : X, ∏ ω ∈ S, f ω x) - 1) := by
    calc
      M⁻¹ * (∑ x : X, ∏ ω : ι, (f ω x - 1))
          = M⁻¹ * (∑ x : X, ∑ S : Finset ι,
              ((-1 : ℝ) ^ (Fintype.card ι - S.card)) * ∏ ω ∈ S, f ω x) := by rw [hstep1]
      _ = M⁻¹ * (∑ S : Finset ι,
              ((-1 : ℝ) ^ (Fintype.card ι - S.card)) * ∑ x : X, ∏ ω ∈ S, f ω x) := by rw [hstep2]
      _ = ∑ S : Finset ι, M⁻¹ * (((-1 : ℝ) ^ (Fintype.card ι - S.card))
              * ∑ x : X, ∏ ω ∈ S, f ω x) := by rw [Finset.mul_sum]
      _ = ∑ S : Finset ι, (((-1 : ℝ) ^ (Fintype.card ι - S.card))
              * (M⁻¹ * (∑ x : X, ∏ ω ∈ S, f ω x) - 1)
              + ((-1 : ℝ) ^ (Fintype.card ι - S.card))) := by
            apply Finset.sum_congr rfl; intro S _; ring
      _ = (∑ S : Finset ι, ((-1 : ℝ) ^ (Fintype.card ι - S.card))
              * (M⁻¹ * (∑ x : X, ∏ ω ∈ S, f ω x) - 1))
            + ∑ S : Finset ι, ((-1 : ℝ) ^ (Fintype.card ι - S.card)) := by
            rw [Finset.sum_add_distrib]
      _ = (∑ S : Finset ι, ((-1 : ℝ) ^ (Fintype.card ι - S.card))
              * (M⁻¹ * (∑ x : X, ∏ ω ∈ S, f ω x) - 1)) + 0 := by
            rw [sum_neg_one_pow_card_sub]
      _ = ∑ S : Finset ι, ((-1 : ℝ) ^ (Fintype.card ι - S.card))
              * (M⁻¹ * (∑ x : X, ∏ ω ∈ S, f ω x) - 1) := by
            rw [add_zero]
  have hT : ∀ S : Finset ι, |M⁻¹ * (∑ x : X, ∏ ω ∈ S, f ω x) - 1| ≤ ε := by
    intro S
    by_cases hSe : S = ∅
    · rw [hSe, hT0, abs_zero]; exact hε
    · exact h S (Finset.nonempty_iff_ne_empty.mpr hSe)
  calc
    |M⁻¹ * (∑ x : X, ∏ ω : ι, (f ω x - 1))|
        = |∑ S : Finset ι, ((-1 : ℝ) ^ (Fintype.card ι - S.card))
              * (M⁻¹ * (∑ x : X, ∏ ω ∈ S, f ω x) - 1)| := by rw [key]
    _ ≤ ∑ S : Finset ι, |((-1 : ℝ) ^ (Fintype.card ι - S.card))
              * (M⁻¹ * (∑ x : X, ∏ ω ∈ S, f ω x) - 1)| :=
          Finset.abs_sum_le_sum_abs _ _
    _ = ∑ S : Finset ι, |M⁻¹ * (∑ x : X, ∏ ω ∈ S, f ω x) - 1| := by
          apply Finset.sum_congr rfl; intro S _
          rw [abs_mul, abs_neg_one_pow, one_mul]
    _ ≤ ∑ S : Finset ι, ε := Finset.sum_le_sum (fun S _ => hT S)
    _ = (2 : ℝ) ^ (Fintype.card ι) * ε := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_finset, nsmul_eq_mul, Nat.cast_pow]
          norm_num

theorem mua {p : ℕ} [Fact p.Prime] {k : ℕ} (hk : 3 ≤ k) (ν : ZMod p → ℝ) {ε : ℝ}
    (hLFC : ∀ A : Finset (Fin (k - 1) → Bool), A.Nonempty →
      |((Fintype.card (ZMod p) : ℝ) ^ k)⁻¹ *
        (∑ z : ZMod p, ∑ h : Fin (k - 1) → ZMod p,
          ∏ ω ∈ A, ν (z + ∑ j, if ω j then h j else 0)) - 1| ≤ ε) :
    |((Fintype.card (ZMod p) : ℝ) ^ k)⁻¹ *
      (∑ z : ZMod p, ∑ h : Fin (k - 1) → ZMod p,
        ∏ ω : Fin (k - 1) → Bool, (ν (z + ∑ j, if ω j then h j else 0) - 1))|
      ≤ ((2 : ℝ) ^ (2 ^ (k - 1))) * ε := by
  classical
  let f : (Fin (k - 1) → Bool) → (ZMod p × (Fin (k - 1) → ZMod p)) → ℝ :=
    fun ω x => ν (x.1 + ∑ j, if ω j then x.2 j else 0)
  have hM : ((Fintype.card (ZMod p) : ℝ) ^ k)
      = (Fintype.card (ZMod p × (Fin (k - 1) → ZMod p)) : ℝ) := by
    have hc : Fintype.card (ZMod p × (Fin (k - 1) → ZMod p))
        = (Fintype.card (ZMod p)) ^ k := by
      rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
      have hk1 : 1 ≤ k := by omega
      rw [mul_comm, ← pow_succ, Nat.sub_add_cancel hk1]
    rw [hc, Nat.cast_pow]
  have h : ∀ A : Finset (Fin (k - 1) → Bool), A.Nonempty →
      |((Fintype.card (ZMod p) : ℝ) ^ k)⁻¹ *
        (∑ x : ZMod p × (Fin (k - 1) → ZMod p), ∏ ω ∈ A, f ω x) - 1| ≤ ε := by
    intro A hA
    have hsum : (∑ x : ZMod p × (Fin (k - 1) → ZMod p), ∏ ω ∈ A, f ω x)
        = ∑ z : ZMod p, ∑ hh : Fin (k - 1) → ZMod p,
            ∏ ω ∈ A, ν (z + ∑ j, if ω j then hh j else 0) := by
      rw [Fintype.sum_prod_type]
    rw [hsum]
    exact hLFC A hA
  have result := mua_core (ι := Fin (k - 1) → Bool)
    (X := ZMod p × (Fin (k - 1) → ZMod p)) f ((Fintype.card (ZMod p) : ℝ) ^ k) ε hM h
  have hsum2 : (∑ x : ZMod p × (Fin (k - 1) → ZMod p),
        ∏ ω : Fin (k - 1) → Bool, (f ω x - 1))
      = ∑ z : ZMod p, ∑ hh : Fin (k - 1) → ZMod p,
          ∏ ω : Fin (k - 1) → Bool, (ν (z + ∑ j, if ω j then hh j else 0) - 1) := by
    rw [Fintype.sum_prod_type]
  have hcard : Fintype.card (Fin (k - 1) → Bool) = 2 ^ (k - 1) := by
    rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  rw [hsum2, hcard] at result
  exact result

end Commons.Combinatorics.Transference