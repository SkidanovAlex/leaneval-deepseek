import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Submission.Commons.Lattice.Counting.card_matrix_mulVec_eq_zero

namespace Commons.Lattice.Counting

open Matrix

/-- Entrywise identification of `A.mulVec v` with a sum against the columns of `A`. -/
private lemma mulVec_cast_eq_sum {q m d : ℕ} (A : Matrix (Fin m) (Fin d) (ZMod q))
    (x : Fin d → ℤ) (i : Fin m) :
    A.mulVec (fun j => (x j : ZMod q)) i = ∑ j, (x j : ZMod q) * A i j := by
  rw [Matrix.mulVec_apply_eq_sum]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

private lemma mulVec_cast_eq_zero_iff {q m d : ℕ} (A : Matrix (Fin m) (Fin d) (ZMod q))
    (x : Fin d → ℤ) :
    A.mulVec (fun j => (x j : ZMod q)) = 0 ↔ ∀ i, ∑ j, (x j : ZMod q) * A i j = 0 := by
  constructor
  · intro hA i
    have hi : (A.mulVec (fun j => (x j : ZMod q))) i = 0 := by
      simpa using congrFun hA i
    rw [← mulVec_cast_eq_sum]
    exact hi
  · intro hA
    funext i
    rw [Pi.zero_apply, mulVec_cast_eq_sum, hA i]

/-- For a nonzero vector `x` in `(ZMod q)^d`, the weighted number of matrices `A` with `A x = 0`
equals `f x · q ^ (m * d - m)`. -/
private lemma sum_ite_mulVec_cast_eq_zero {q m d : ℕ} [Fact q.Prime]
    (f : (Fin d → ℤ) → ℝ) (x : Fin d → ℤ)
    (hvx : (fun j => (x j : ZMod q)) ≠ 0) :
    ∑ A : Matrix (Fin m) (Fin d) (ZMod q),
        (if A.mulVec (fun j => (x j : ZMod q)) = 0 then f x else 0)
      = f x * ((q ^ (m * d - m) : ℕ) : ℝ) := by
  classical
  have hcard : Nat.card
      {A : Matrix (Fin m) (Fin d) (ZMod q) // A.mulVec (fun j => (x j : ZMod q)) = 0}
      = q ^ (m * d - m) := by
    rw [card_matrix_mulVec_eq_zero (q := q) (m := m) (d := d) (fun j => (x j : ZMod q)),
      if_neg hvx]
  have hp : (Finset.univ.filter (fun A : Matrix (Fin m) (Fin d) (ZMod q) =>
      A.mulVec (fun j => (x j : ZMod q)) = 0)).card = q ^ (m * d - m) := by
    rw [← Fintype.card_subtype (fun A : Matrix (Fin m) (Fin d) (ZMod q) =>
      A.mulVec (fun j => (x j : ZMod q)) = 0), ← Nat.card_eq_fintype_card]
    exact hcard
  calc ∑ A : Matrix (Fin m) (Fin d) (ZMod q),
        (if A.mulVec (fun j => (x j : ZMod q)) = 0 then f x else 0)
      = ∑ A : Matrix (Fin m) (Fin d) (ZMod q),
        f x * (if A.mulVec (fun j => (x j : ZMod q)) = 0 then (1 : ℝ) else 0) := by
        refine Finset.sum_congr rfl fun A _ => ?_
        by_cases h : A.mulVec (fun j => (x j : ZMod q)) = 0 <;> simp [h]
    _ = f x * ∑ A : Matrix (Fin m) (Fin d) (ZMod q),
        (if A.mulVec (fun j => (x j : ZMod q)) = 0 then (1 : ℝ) else 0) :=
        (Finset.mul_sum _ _ _).symm
    _ = f x * ((Finset.univ.filter (fun A : Matrix (Fin m) (Fin d) (ZMod q) =>
        A.mulVec (fun j => (x j : ZMod q)) = 0)).card : ℝ) := by
        rw [Finset.sum_boole]
    _ = f x * ((q ^ (m * d - m) : ℕ) : ℝ) := by rw [hp]

theorem exists_qary_weighted_sum_le_ne_zero {q m d : ℕ} [Fact q.Prime]
    (S : Finset (Fin d → ℤ)) (f : (Fin d → ℤ) → ℝ) (hf : ∀ x, 0 ≤ f x)
    (h : ∀ x ∈ S, ∃ j, (x j : ZMod q) ≠ 0) :
    ∃ A : Matrix (Fin m) (Fin d) (ZMod q),
      (∑ x ∈ S, if (∀ i, ∑ j, (x j : ZMod q) * A i j = 0) then f x else 0)
        ≤ 2 * ((q : ℝ) ^ m)⁻¹ * (∑ x ∈ S, f x) := by
  classical
  rcases S.eq_empty_or_nonempty with hS | hS
  · rw [hS]
    refine ⟨0, ?_⟩
    simp
  · obtain ⟨x₀, hx₀⟩ := hS
    obtain ⟨j₀, hj₀⟩ := h x₀ hx₀
    have hd : 0 < d := by have := j₀.isLt; omega
    -- every `x ∈ S` is nonzero modulo `q`
    have hvS : ∀ x ∈ S, (fun j => (x j : ZMod q)) ≠ 0 := by
      intro x hx h0
      obtain ⟨j, hj⟩ := h x hx
      exact hj (by simpa using congrFun h0 j)
    have hF : 0 ≤ ∑ x ∈ S, f x := Finset.sum_nonneg fun x _ => hf x
    have hQ : (0 : ℝ) < (q : ℝ) := by
      have hq := (Fact.out : q.Prime).pos
      exact_mod_cast hq
    have hQne : (q : ℝ) ≠ 0 := ne_of_gt hQ
    have hm : m ≤ m * d := Nat.le_mul_of_pos_right m hd
    -- the average value of the weighted count
    have hkey : (∑ A : Matrix (Fin m) (Fin d) (ZMod q),
          (∑ x ∈ S, if A.mulVec (fun j => (x j : ZMod q)) = 0 then f x else 0))
        = ((q ^ (m * d - m) : ℕ) : ℝ) * (∑ x ∈ S, f x) := by
      rw [Finset.sum_comm]
      rw [Finset.sum_congr rfl fun x hx => sum_ite_mulVec_cast_eq_zero f x (hvS x hx)]
      rw [← Finset.sum_mul]
      exact mul_comm _ _
    -- the cardinality of the space of matrices
    have hcardM : (Fintype.card (Matrix (Fin m) (Fin d) (ZMod q)) : ℝ)
        = ((q ^ (m * d) : ℕ) : ℝ) := by
      rw [← Nat.card_eq_fintype_card, card_matrix_zmod]
    -- the total mass of the constant bound
    have hB : ((q ^ (m * d) : ℕ) : ℝ) * (2 * ((q : ℝ) ^ m)⁻¹ * (∑ x ∈ S, f x))
        = 2 * (((q ^ (m * d - m) : ℕ) : ℝ) * (∑ x ∈ S, f x)) := by
      rw [Nat.cast_pow, Nat.cast_pow]
      calc (q : ℝ) ^ (m * d) * (2 * ((q : ℝ) ^ m)⁻¹ * (∑ x ∈ S, f x))
          = 2 * ((q : ℝ) ^ (m * d) * ((q : ℝ) ^ m)⁻¹) * (∑ x ∈ S, f x) := by ring
        _ = 2 * ((q : ℝ) ^ (m * d - m)) * (∑ x ∈ S, f x) := by
              rw [pow_sub₀ (q : ℝ) hQne hm]
        _ = 2 * ((q : ℝ) ^ (m * d - m) * (∑ x ∈ S, f x)) := by ring
    have hsum_le : (∑ A : Matrix (Fin m) (Fin d) (ZMod q),
          (∑ x ∈ S, if A.mulVec (fun j => (x j : ZMod q)) = 0 then f x else 0))
        ≤ ∑ _A : Matrix (Fin m) (Fin d) (ZMod q),
          (2 * ((q : ℝ) ^ m)⁻¹ * (∑ x ∈ S, f x)) := by
      rw [hkey, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcardM, hB]
      have : (0 : ℝ) ≤ ((q ^ (m * d - m) : ℕ) : ℝ) * (∑ x ∈ S, f x) :=
        mul_nonneg (by positivity) hF
      linarith
    obtain ⟨A, -, hAle⟩ := Finset.exists_le_of_sum_le (s := Finset.univ)
      (f := fun A : Matrix (Fin m) (Fin d) (ZMod q) =>
        ∑ x ∈ S, if A.mulVec (fun j => (x j : ZMod q)) = 0 then f x else 0)
      (g := fun _ => 2 * ((q : ℝ) ^ m)⁻¹ * (∑ x ∈ S, f x))
      Finset.univ_nonempty hsum_le
    refine ⟨A, ?_⟩
    have hgA : (∑ x ∈ S, if (∀ i, ∑ j, (x j : ZMod q) * A i j = 0) then f x else 0)
        = ∑ x ∈ S, if A.mulVec (fun j => (x j : ZMod q)) = 0 then f x else 0 := by
      refine Finset.sum_congr rfl fun x _ => ?_
      by_cases hp : (∀ i, ∑ j, (x j : ZMod q) * A i j = 0)
      · rw [if_pos hp, if_pos ((mulVec_cast_eq_zero_iff A x).mpr hp)]
      · rw [if_neg hp, if_neg (fun hc => hp ((mulVec_cast_eq_zero_iff A x).mp hc))]
    rw [hgA]
    exact hAle

end Commons.Lattice.Counting