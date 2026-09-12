import Mathlib
import Submission.Commons.NumberTheory.DiophantineApproximation.BoundedDegree.p51_complete_family
import Submission.Commons.NumberTheory.DiophantineApproximation.BoundedDegree.p51_det_deriv_bound
import Submission.Commons.NumberTheory.DiophantineApproximation.BoundedDegree.root_height_bound
import Submission.Commons.NumberTheory.DiophantineApproximation.BoundedDegree.p51_prod_sum_bound3
import Submission.Commons.NumberTheory.DiophantineApproximation.BoundedDegree.p51_lift_pair_uniform2
import Submission.Commons.NumberTheory.DiophantineApproximation.BoundedDegree.root_close_deriv_bound
import Submission.Commons.NumberTheory.DiophantineApproximation.BoundedDegree.int_poly_supNorm_one_le
import Submission.Commons.NumberTheory.DiophantineApproximation.BoundedDegree.int_poly_natDegree_map_eq
import Submission.Commons.Analysis.Polynomial.supNorm_X_pow_mul

set_option maxHeartbeats 4000000
set_option autoImplicit true

namespace Commons.NumberTheory.DiophantineApproximation.BoundedDegree

open Polynomial
open scoped BigOperators

noncomputable section

/-! # p51_aux

Proposition 5.1 of Poëls (Annals 2025), in the version where the constant is allowed to
depend on `k` (in addition to `n` and `ξ`).  The proof follows the companion paper
arXiv:2405.07219 §6 (generalized resultants).  -/

/-- sup-norm of the real image of an integer polynomial. -/
private def p51H (P : Polynomial ℤ) : ℝ := (P.map (Int.castRingHom ℝ)).supNorm

/-- evaluation of an integer polynomial at a real point. -/
private def p51v (ξ : ℝ) (P : Polynomial ℤ) : ℝ :=
  Polynomial.eval ξ (P.map (Int.castRingHom ℝ))

private lemma p51H_nonneg (P : Polynomial ℤ) : 0 ≤ p51H P := by
  dsimp [p51H]
  exact supNorm_nonneg _

private lemma p51H_eq_zero_iff (P : Polynomial ℤ) : p51H P = 0 ↔ P = 0 := by
  dsimp [p51H]
  rw [supNorm_eq_zero_iff]
  constructor
  · intro h
    exact Polynomial.map_injective (Int.castRingHom ℝ) Int.cast_injective (by simpa using h)
  · intro h
    simp [h]

private lemma p51H_pos_of_ne (P : Polynomial ℤ) (hP : P ≠ 0) : 0 < p51H P := by
  have h1 : (1 : ℝ) ≤ p51H P := by
    dsimp [p51H]
    exact int_poly_supNorm_one_le P hP
  linarith

private lemma natDegree_map_real (P : Polynomial ℤ) :
    (P.map (Int.castRingHom ℝ)).natDegree = P.natDegree :=
  int_poly_natDegree_map_eq P

/-- P i ≠ 0 follows from linear independence of the real maps. -/
private lemma li_ne_zero (P : Fin k → Polynomial ℤ)
    (hLI : LinearIndependent ℝ (fun i : Fin k => (P i).map (Int.castRingHom ℝ))) (i : Fin k) :
    P i ≠ 0 := by
  intro hz
  have hv : (P i).map (Int.castRingHom ℝ) = 0 := by simp [hz]
  exact LinearIndependent.ne_zero i hLI hv

/-- Coprimality over ℤ survives the map to ℝ. -/
private lemma cop_map_real {P Q : Polynomial ℤ} (h : IsCoprime P Q) :
    IsCoprime (P.map (Int.castRingHom ℝ)) (Q.map (Int.castRingHom ℝ)) := by
  rcases h with ⟨U, V, hUV⟩
  refine ⟨U.map (Int.castRingHom ℝ), V.map (Int.castRingHom ℝ), ?_⟩
  rw [← Polynomial.map_mul, ← Polynomial.map_mul, ← Polynomial.map_add]
  simpa using congrArg (fun p : Polynomial ℤ => p.map (Int.castRingHom ℝ)) hUV

/-- Multiplying by `X^t` does not change the sup-norm of the real image. -/
private lemma supNorm_map_X_pow_mul (Q : Polynomial ℤ) (t : ℕ) :
    p51H (Polynomial.X ^ t * Q) = p51H Q := by
  dsimp [p51H]
  rw [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X]
  exact Commons.Analysis.Polynomial.supNorm_X_pow_mul (Q.map (Int.castRingHom ℝ)) t

private lemma supNorm_map_X_pow_mul' (Q : Polynomial ℤ) (t : ℕ) :
    ((((Polynomial.X ^ t * Q).map (Int.castRingHom ℝ))).supNorm) =
      ((Q.map (Int.castRingHom ℝ))).supNorm := by
  exact supNorm_map_X_pow_mul Q t

/-- evaluation of `X^t * Q` at ξ. -/
private lemma eval_map_X_pow_mul (ξ : ℝ) (Q : Polynomial ℤ) (t : ℕ) :
    Polynomial.eval ξ (((Polynomial.X ^ t * Q).map (Int.castRingHom ℝ))) =
      ξ ^ t * Polynomial.eval ξ (Q.map (Int.castRingHom ℝ)) := by
  rw [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X]
  rw [Polynomial.eval_mul, Polynomial.eval_pow]
  simp

/-- Norm bound for the evaluation of `X^t * Q` at ξ. -/
private lemma eval_X_pow_mul_norm_le (ξ : ℝ) (Q : Polynomial ℤ) (t N : ℕ) (ht : t ≤ N) :
    ‖Polynomial.eval ξ (((Polynomial.X ^ t * Q).map (Int.castRingHom ℝ)))‖ ≤
      (1 + |ξ|) ^ N * ‖Polynomial.eval ξ (Q.map (Int.castRingHom ℝ))‖ := by
  calc
    ‖Polynomial.eval ξ (((Polynomial.X ^ t * Q).map (Int.castRingHom ℝ)))‖
        = ‖ξ ^ t * Polynomial.eval ξ (Q.map (Int.castRingHom ℝ))‖ := by rw [eval_map_X_pow_mul]
    _ = |ξ| ^ t * ‖Polynomial.eval ξ (Q.map (Int.castRingHom ℝ))‖ := by
        rw [norm_mul, norm_pow, Real.norm_eq_abs]
    _ ≤ (1 + |ξ|) ^ N * ‖Polynomial.eval ξ (Q.map (Int.castRingHom ℝ))‖ := by
        have hξt : |ξ| ^ t ≤ (1 + |ξ|) ^ N := by
          have h1 : |ξ| ≤ 1 + |ξ| := by linarith
          have hp1 : |ξ| ^ t ≤ (1 + |ξ|) ^ t := pow_le_pow_left₀ (abs_nonneg ξ) h1 t
          have hb : (1 : ℝ) ≤ 1 + |ξ| := by have := abs_nonneg ξ; linarith
          have hp2 : (1 + |ξ|) ^ t ≤ (1 + |ξ|) ^ N := pow_le_pow_right₀ hb ht
          exact le_trans hp1 hp2
        exact mul_le_mul_of_nonneg_right hξt (norm_nonneg _)

/-- natDegree of `X^t * Q`. -/
private lemma natDegree_X_pow_mul_deg {Q : Polynomial ℤ} (hQ : Q ≠ 0) (t : ℕ) :
    ((Polynomial.X ^ t * Q).natDegree) = t + Q.natDegree := by
  rw [Polynomial.natDegree_mul (by exact pow_ne_zero t (by simp : (Polynomial.X : Polynomial ℤ) ≠ 0)) hQ]
  rw [Polynomial.natDegree_pow]
  simp

private lemma X_pow_mul_ne_zero {Q : Polynomial ℤ} (hQ : Q ≠ 0) (t : ℕ) :
    Polynomial.X ^ t * Q ≠ 0 := by
  exact mul_ne_zero (pow_ne_zero t (by simp : (Polynomial.X : Polynomial ℤ) ≠ 0)) hQ

/-- A multiplicative identity used for clearing denominators: `supNorm` of the real image of
the minimal polynomial height expression in `p51_aux` (the `Finset.sup ...` part). -/
private lemma supNorm_X_ne_zero : (Polynomial.X : Polynomial ℤ) ≠ 0 := by simp

/-! ## The complete family with integer coefficients and labels -/

/-- Integer version of the complete family. `p51_complete_family` produces a real linearly
independent family; here we reconstruct the same family inside `ℤ[X]` and record, for each
member, the underlying index `lab ℓ ∈ Fin k` and the exponent `exp ℓ` such that
`S ℓ = X^(exp ℓ) * Q (lab ℓ)`. -/
private lemma complete_family_int (n k : ℕ) (hn : 1 ≤ n) (hk2 : 2 ≤ k) (hkn : k ≤ n + 1)
    (Q : Fin k → Polynomial ℤ)
    (hQdeg : ∀ i : Fin k, (Q i).natDegree ≤ n)
    (hQdeg0 : (Q ⟨0, by omega⟩).natDegree = n)
    (hQdeg1 : (Q ⟨1, by omega⟩).natDegree = n)
    (hQcop : IsCoprime ((Q ⟨0, by omega⟩).map (Int.castRingHom ℝ))
        ((Q ⟨1, by omega⟩).map (Int.castRingHom ℝ)))
    (hQli : LinearIndependent ℝ (fun i : Fin k => (Q i).map (Int.castRingHom ℝ))) :
    ∃ (S : Fin (2 * n - k + 2) → Polynomial ℤ)
      (lab : Fin (2 * n - k + 2) → Fin k)
      (exp : Fin (2 * n - k + 2) → ℕ),
      (∀ ℓ : Fin (2 * n - k + 2), S ℓ = Polynomial.X ^ (exp ℓ) * Q (lab ℓ)) ∧
      (∀ ℓ : Fin (2 * n - k + 2), ℓ.val < n + 2 - k → lab ℓ = ⟨0, by omega⟩ ∧ exp ℓ = ℓ.val) ∧
      (∀ ℓ : Fin (2 * n - k + 2), n + 2 - k ≤ ℓ.val → ℓ.val < 2 * (n + 2 - k) →
          lab ℓ = ⟨1, by omega⟩ ∧ exp ℓ = ℓ.val - (n + 2 - k)) ∧
      (∀ ℓ : Fin (2 * n - k + 2), 2 * (n + 2 - k) ≤ ℓ.val →
          2 ≤ (lab ℓ).val ∧ (lab ℓ).val ≤ ℓ.val - 2 * (n + 2 - k) + 2) ∧
      (∀ ℓ : Fin (2 * n - k + 2), (Q (lab ℓ)).natDegree + exp ℓ ≤ 2 * n - k + 1) ∧
      LinearIndependent ℝ (fun ℓ : Fin (2 * n - k + 2) => (S ℓ).map (Int.castRingHom ℝ)) := by
  classical
  let q : Fin k → Polynomial ℝ := fun i => (Q i).map (Int.castRingHom ℝ)
  have hqdeg : ∀ i : Fin k, (q i).natDegree ≤ n := by
    intro i
    dsimp [q]
    rw [Polynomial.natDegree_map_eq_of_injective (f := Int.castRingHom ℝ) Int.cast_injective]
    exact hQdeg i
  have hqdeg0 : (q ⟨0, by omega⟩).natDegree = n := by
    dsimp [q]
    rw [Polynomial.natDegree_map_eq_of_injective (f := Int.castRingHom ℝ) Int.cast_injective]
    exact hQdeg0
  have hqdeg1 : (q ⟨1, by omega⟩).natDegree = n := by
    dsimp [q]
    rw [Polynomial.natDegree_map_eq_of_injective (f := Int.castRingHom ℝ) Int.cast_injective]
    exact hQdeg1
  rcases p51_complete_family n k hn hk2 hkn q hqdeg hqdeg0 hqdeg1 hQcop hQli with ⟨S, hS0, hS1, hS2, hSLI⟩
  let jOf (ℓ : Fin (2 * n - k + 2)) (hge : 2 * (n + 2 - k) ≤ ℓ.val) : Fin (k - 2) :=
    ⟨ℓ.val - 2 * (n + 2 - k), by have hltN : ℓ.val < 2 * n - k + 2 := ℓ.isLt; omega⟩
  let lab : Fin (2 * n - k + 2) → Fin k := fun ℓ =>
    if hlt : ℓ.val < n + 2 - k then ⟨0, by omega⟩
    else if hlt2 : ℓ.val < 2 * (n + 2 - k) then ⟨1, by omega⟩
    else Classical.choose (hS2 (jOf ℓ (by omega)))
  let exp : Fin (2 * n - k + 2) → ℕ := fun ℓ =>
    if hlt : ℓ.val < n + 2 - k then ℓ.val
    else if hlt2 : ℓ.val < 2 * (n + 2 - k) then ℓ.val - (n + 2 - k)
    else Classical.choose (Classical.choose_spec (hS2 (jOf ℓ (by omega)))).2.2
  let S' : Fin (2 * n - k + 2) → Polynomial ℤ := fun ℓ => Polynomial.X ^ (exp ℓ) * Q (lab ℓ)
  refine ⟨S', lab, exp, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ℓ; rfl
  · intro ℓ hlt
    constructor
    · apply Fin.ext
      dsimp [lab]
      simp [hlt]
    · dsimp [exp]
      simp [hlt]
  · intro ℓ hge hlt2
    have hnlt : ¬ ℓ.val < n + 2 - k := by omega
    constructor
    · apply Fin.ext
      dsimp [lab]
      simp [hnlt, hlt2]
    · dsimp [exp]
      simp [hnlt, hlt2]
  · intro ℓ hge
    have hnlt : ¬ ℓ.val < n + 2 - k := by omega
    have hnlt2 : ¬ ℓ.val < 2 * (n + 2 - k) := by omega
    let j : Fin (k - 2) := jOf ℓ (by omega)
    have hspec := Classical.choose_spec (hS2 j)
    have hlab : lab ℓ = Classical.choose (hS2 j) := by
      dsimp [lab]
      simp [hnlt, hnlt2]
    constructor
    · rw [hlab]
      exact hspec.1
    · rw [hlab]
      have hle : (Classical.choose (hS2 j)).val ≤ j.val + 2 := hspec.2.1
      dsimp [j] at hle
      omega
  · intro ℓ
    by_cases hlt : ℓ.val < n + 2 - k
    · have hlab : lab ℓ = ⟨0, by omega⟩ := by
        apply Fin.ext
        dsimp [lab]
        simp [hlt]
      have he : exp ℓ = ℓ.val := by dsimp [exp]; simp [hlt]
      rw [hlab, he]
      have hdegQ : (Q ⟨0, by omega⟩).natDegree ≤ n := hQdeg ⟨0, by omega⟩
      omega
    · by_cases hlt2 : ℓ.val < 2 * (n + 2 - k)
      · have hlab : lab ℓ = ⟨1, by omega⟩ := by
          apply Fin.ext
          dsimp [lab]
          simp [hlt, hlt2]
        have he : exp ℓ = ℓ.val - (n + 2 - k) := by
          dsimp [exp]
          simp [hlt, hlt2]
        rw [hlab, he]
        have hdegQ : (Q ⟨1, by omega⟩).natDegree ≤ n := hQdeg ⟨1, by omega⟩
        have h1 : ℓ.val - (n + 2 - k) ≤ n + 1 - k := by omega
        omega
      · let j : Fin (k - 2) := jOf ℓ (by omega)
        have hspec := Classical.choose_spec (hS2 j)
        have ht := Classical.choose_spec hspec.2.2
        have hlab : lab ℓ = Classical.choose (hS2 j) := by
          dsimp [lab]
          simp [hlt, hlt2]
        have he : exp ℓ = Classical.choose hspec.2.2 := by
          dsimp [exp]
          simp [hlt, hlt2]
        rw [hlab, he]
        have hqdeg_i : (q (Classical.choose (hS2 j))).natDegree =
            (Q (Classical.choose (hS2 j))).natDegree := by
          dsimp [q]
          exact Polynomial.natDegree_map_eq_of_injective (f := Int.castRingHom ℝ) Int.cast_injective
            (Q (Classical.choose (hS2 j)))
        have hsum : (q (Classical.choose (hS2 j))).natDegree +
            Classical.choose hspec.2.2 ≤ 2 * n - k + 1 := ht.1
        omega
  · have hS'_eq_S : (fun ℓ : Fin (2 * n - k + 2) => (S' ℓ).map (Int.castRingHom ℝ)) = S := by
      funext ℓ
      by_cases hlt : ℓ.val < n + 2 - k
      · have hleft : (S' ℓ).map (Int.castRingHom ℝ) = Polynomial.X ^ ℓ.val * q ⟨0, by omega⟩ := by
          simp [S', lab, exp, hlt, q, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X]
        have h1 := hS0 ℓ hlt
        calc
          (S' ℓ).map (Int.castRingHom ℝ) = Polynomial.X ^ ℓ.val * q ⟨0, by omega⟩ := hleft
          _ = S ℓ := h1.symm
      · by_cases hlt2 : ℓ.val < 2 * (n + 2 - k)
        · have hge : n + 2 - k ≤ ℓ.val := by omega
          have hleft : (S' ℓ).map (Int.castRingHom ℝ) =
              Polynomial.X ^ (ℓ.val - (n + 2 - k)) * q ⟨1, by omega⟩ := by
            simp [S', lab, exp, hlt, hlt2, q, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X]
          have h1 := hS1 ℓ hge hlt2
          calc
            (S' ℓ).map (Int.castRingHom ℝ) =
                Polynomial.X ^ (ℓ.val - (n + 2 - k)) * q ⟨1, by omega⟩ := hleft
            _ = S ℓ := h1.symm
        · let j : Fin (k - 2) := jOf ℓ (by omega)
          have hspec := Classical.choose_spec (hS2 j)
          have ht := Classical.choose_spec hspec.2.2
          have hleft : (S' ℓ).map (Int.castRingHom ℝ) =
              Polynomial.X ^ (Classical.choose hspec.2.2) *
                q (Classical.choose (hS2 j)) := by
            simp [S', lab, exp, hlt, hlt2, q, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X]
          have hSℓ : S ℓ = Polynomial.X ^ (Classical.choose hspec.2.2) *
                q (Classical.choose (hS2 j)) := by
            have hℓeq : ℓ = ⟨2 * (n + 2 - k) + j.val, by
                have hltN : ℓ.val < 2 * n - k + 2 := ℓ.isLt
                omega⟩ := by
              apply Fin.ext
              dsimp [j, jOf]
              omega
            simpa [hℓeq] using ht.2
          calc
            (S' ℓ).map (Int.castRingHom ℝ) =
                Polynomial.X ^ (Classical.choose hspec.2.2) *
                  q (Classical.choose (hS2 j)) := hleft
            _ = S ℓ := hSℓ.symm
    exact hS'_eq_S ▸ hSLI

private lemma H_nonneg_of_ge1 {H : Fin k → ℝ} (hHge : ∀ i : Fin k, 1 ≤ H i) (i : Fin k) : 0 ≤ H i := by
  have := hHge i
  linarith

private lemma card_B0 (n k : ℕ) (hk2 : 2 ≤ k) (hkn : k ≤ n + 1) :
    (Finset.univ.filter (fun ℓ : Fin (2 * n - k + 2) => ℓ.val < n + 2 - k)).card = n + 2 - k := by
  classical
  have h := Fin.card_filter_val_lt (n := 2 * n - k + 2) (m := n + 2 - k)
  have hmin : min (2 * n - k + 2) (n + 2 - k) = n + 2 - k := by
    apply min_eq_right
    omega
  simpa [hmin] using h

private lemma card_B1 (n k : ℕ) (hk2 : 2 ≤ k) (hkn : k ≤ n + 1) :
    (Finset.univ.filter (fun ℓ : Fin (2 * n - k + 2) =>
      n + 2 - k ≤ ℓ.val ∧ ℓ.val < 2 * (n + 2 - k))).card = n + 2 - k := by
  classical
  have hlt : (Finset.univ.filter (fun ℓ : Fin (2 * n - k + 2) => ℓ.val < 2 * (n + 2 - k))).card =
      2 * (n + 2 - k) := by
    have h' := Fin.card_filter_val_lt (n := 2 * n - k + 2) (m := 2 * (n + 2 - k))
    have hmin : min (2 * n - k + 2) (2 * (n + 2 - k)) = 2 * (n + 2 - k) := by
      apply min_eq_right
      omega
    simpa [hmin] using h'
  have hsd : (Finset.univ.filter (fun ℓ : Fin (2 * n - k + 2) =>
      n + 2 - k ≤ ℓ.val ∧ ℓ.val < 2 * (n + 2 - k))) =
      (Finset.univ.filter (fun ℓ : Fin (2 * n - k + 2) => ℓ.val < 2 * (n + 2 - k))) \
        (Finset.univ.filter (fun ℓ : Fin (2 * n - k + 2) => ℓ.val < n + 2 - k)) := by
    ext ℓ
    simp
    omega
  rw [hsd]
  have hsub : (Finset.univ.filter (fun ℓ : Fin (2 * n - k + 2) => ℓ.val < n + 2 - k)) ⊆
      (Finset.univ.filter (fun ℓ : Fin (2 * n - k + 2) => ℓ.val < 2 * (n + 2 - k))) := by
    intro ℓ hℓ
    simp at hℓ ⊢
    omega
  rw [Finset.card_sdiff_of_subset hsub]
  rw [hlt, card_B0 n k hk2 hkn]
  omega

private lemma card_BE (n k : ℕ) (hk2 : 2 ≤ k) (hkn : k ≤ n + 1) :
    (Finset.univ.filter (fun ℓ : Fin (2 * n - k + 2) => 2 * (n + 2 - k) ≤ ℓ.val)).card = k - 2 := by
  classical
  have hpart := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin (2 * n - k + 2))))
    (fun ℓ : Fin (2 * n - k + 2) => ℓ.val < 2 * (n + 2 - k))
  rw [Finset.card_univ, Fintype.card_fin] at hpart
  have h2 : (Finset.univ.filter (fun ℓ : Fin (2 * n - k + 2) =>
      ℓ.val < 2 * (n + 2 - k))).card = 2 * (n + 2 - k) := by
    have h' := Fin.card_filter_val_lt (n := 2 * n - k + 2) (m := 2 * (n + 2 - k))
    have hmin : min (2 * n - k + 2) (2 * (n + 2 - k)) = 2 * (n + 2 - k) := by
      apply min_eq_right
      omega
    simpa [hmin] using h'
  have heq : Finset.univ.filter (fun ℓ : Fin (2 * n - k + 2) => ¬ ℓ.val < 2 * (n + 2 - k)) =
      Finset.univ.filter (fun ℓ : Fin (2 * n - k + 2) => 2 * (n + 2 - k) ≤ ℓ.val) := by
    apply Finset.filter_congr
    intro ℓ hℓ
    by_cases hx : 2 * (n + 2 - k) ≤ ℓ.val
    · simp [hx]
    · have : ℓ.val < 2 * (n + 2 - k) := by omega
      simp [hx, this]
  rw [heq] at hpart
  rw [h2] at hpart
  omega

-- product over extras of H(L·) ≤ product over j : Fin(k-2) of H(j+2)
private lemma extras_prod_le (n k : ℕ) (hk2 : 2 ≤ k) (hkn : k ≤ n + 1)
    (H : Fin k → ℝ) (hmono : Monotone H) (hHge : ∀ i : Fin k, 1 ≤ H i)
    (L : Fin (2 * n - k + 2) → Fin k)
    (hLab : ∀ ℓ : Fin (2 * n - k + 2), 2 * (n + 2 - k) ≤ ℓ.val → (L ℓ).val ≤ (ℓ.val - 2 * (n + 2 - k)) + 2) :
    (∏ ℓ ∈ (Finset.univ.filter (fun ℓ : Fin (2 * n - k + 2) => 2 * (n + 2 - k) ≤ ℓ.val)),
        H (L ℓ)) ≤ ∏ j : Fin (k - 2), H ⟨j.val + 2, by omega⟩ := by
  classical
  let sh : Fin (2 * n - k + 2) → Fin k := fun ℓ =>
    if hx : 2 * (n + 2 - k) ≤ ℓ.val then
      ⟨(ℓ.val - 2 * (n + 2 - k)) + 2, by
        have hltN : ℓ.val < 2 * n - k + 2 := ℓ.isLt
        omega⟩
    else ⟨0, by omega⟩
  have hstep1 : (∏ ℓ ∈ (Finset.univ.filter (fun ℓ : Fin (2 * n - k + 2) => 2 * (n + 2 - k) ≤ ℓ.val)),
        H (L ℓ)) ≤ (∏ ℓ ∈ (Finset.univ.filter (fun ℓ : Fin (2 * n - k + 2) => 2 * (n + 2 - k) ≤ ℓ.val)),
        H (sh ℓ)) := by
    refine Finset.prod_le_prod ?h0 ?h1
    · intro ℓ hℓ
      exact H_nonneg_of_ge1 hHge (L ℓ)
    · intro ℓ hℓ
      have hge : 2 * (n + 2 - k) ≤ ℓ.val := (Finset.mem_filter.mp hℓ).2
      have hle := hLab ℓ hge
      have hsh : sh ℓ = ⟨(ℓ.val - 2 * (n + 2 - k)) + 2, by
          have hltN : ℓ.val < 2 * n - k + 2 := ℓ.isLt
          omega⟩ := by
        dsimp [sh]
        rw [dif_pos hge]
      rw [hsh]
      apply hmono
      rw [Fin.le_def]
      simpa using hle
  have hstep2 : (∏ ℓ ∈ (Finset.univ.filter (fun ℓ : Fin (2 * n - k + 2) => 2 * (n + 2 - k) ≤ ℓ.val)),
        H (sh ℓ)) = ∏ j : Fin (k - 2), H ⟨j.val + 2, by omega⟩ := by
    refine Finset.prod_bij
      (s := Finset.univ.filter (fun ℓ : Fin (2 * n - k + 2) => 2 * (n + 2 - k) ≤ ℓ.val))
      (t := Finset.univ)
      (f := fun ℓ => H (sh ℓ)) (g := fun j : Fin (k - 2) => H ⟨j.val + 2, by omega⟩)
      (i := fun ℓ hℓ => ⟨ℓ.val - 2 * (n + 2 - k), by
          have hge : 2 * (n + 2 - k) ≤ ℓ.val := (Finset.mem_filter.mp hℓ).2
          have hltN : ℓ.val < 2 * n - k + 2 := ℓ.isLt
          omega⟩)
      (hi := by intro a ha; simp)
      (i_inj := by
          intro a ha b hb h
          apply Fin.ext
          have hge_a : 2 * (n + 2 - k) ≤ a.val := (Finset.mem_filter.mp ha).2
          have hge_b : 2 * (n + 2 - k) ≤ b.val := (Finset.mem_filter.mp hb).2
          have hv : a.val - 2 * (n + 2 - k) = b.val - 2 * (n + 2 - k) := congrArg Fin.val h
          omega)
      (i_surj := by
          intro b hb
          have hbnd : 2 * (n + 2 - k) + b.val < 2 * n - k + 2 := by
            have hbv : b.val < k - 2 := b.isLt
            omega
          let a : Fin (2 * n - k + 2) := ⟨2 * (n + 2 - k) + b.val, hbnd⟩
          have hamem : a ∈ (Finset.univ.filter (fun ℓ : Fin (2 * n - k + 2) => 2 * (n + 2 - k) ≤ ℓ.val)) := by
            simp [a, hbnd]
          exact ⟨a, hamem, by
            apply Fin.ext
            dsimp [a]
            omega⟩)
      (h := by
          intro ℓ hℓ
          have hge : 2 * (n + 2 - k) ≤ ℓ.val := (Finset.mem_filter.mp hℓ).2
          have hsh : sh ℓ = ⟨(ℓ.val - 2 * (n + 2 - k)) + 2, by
              have hltN : ℓ.val < 2 * n - k + 2 := ℓ.isLt
              omega⟩ := by
            dsimp [sh]
            rw [dif_pos hge]
          rw [hsh])
  exact le_trans hstep1 (le_of_eq hstep2)

-- decompose the product over univ into the three blocks
private lemma prod_univ_block_decomp (n k : ℕ) (hk2 : 2 ≤ k) (hkn : k ≤ n + 1) (f : Fin (2 * n - k + 2) → ℝ) :
    (∏ ℓ ∈ (Finset.univ : Finset (Fin (2 * n - k + 2))), f ℓ) =
      (∏ ℓ ∈ (Finset.univ.filter (fun ℓ : Fin (2 * n - k + 2) => ℓ.val < n + 2 - k)), f ℓ) *
      (∏ ℓ ∈ (Finset.univ.filter (fun ℓ : Fin (2 * n - k + 2) =>
          n + 2 - k ≤ ℓ.val ∧ ℓ.val < 2 * (n + 2 - k))), f ℓ) *
      (∏ ℓ ∈ (Finset.univ.filter (fun ℓ : Fin (2 * n - k + 2) => 2 * (n + 2 - k) ≤ ℓ.val)), f ℓ) := by
  classical
  let A : Finset (Fin (2 * n - k + 2)) := Finset.univ.filter (fun ℓ => ℓ.val < n + 2 - k)
  let B : Finset (Fin (2 * n - k + 2)) := Finset.univ.filter (fun ℓ =>
      n + 2 - k ≤ ℓ.val ∧ ℓ.val < 2 * (n + 2 - k))
  let C : Finset (Fin (2 * n - k + 2)) := Finset.univ.filter (fun ℓ => 2 * (n + 2 - k) ≤ ℓ.val)
  have hdAB : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro ℓ hA hB
    simp [A] at hA
    simp [B] at hB
    omega
  have hdAB_C : Disjoint (A ∪ B) C := by
    rw [Finset.disjoint_left]
    intro ℓ h hC
    rcases Finset.mem_union.mp h with hA | hB
    · simp [A] at hA
      simp [C] at hC
      omega
    · simp [B] at hB
      simp [C] at hC
      omega
  have hcover : A ∪ B ∪ C = Finset.univ := by
    apply Finset.eq_univ_iff_forall.mpr
    intro ℓ
    by_cases h1 : ℓ.val < n + 2 - k
    · have hmem : ℓ ∈ A := by
        simp [A, h1]
      exact Finset.mem_union_left C (Finset.mem_union_left B hmem)
    · have hm_le : n + 2 - k ≤ ℓ.val := by omega
      by_cases h2 : ℓ.val < 2 * (n + 2 - k)
      · have hmem : ℓ ∈ B := by
          simp [B, h2]
          omega
        exact Finset.mem_union_left C (Finset.mem_union_right A hmem)
      · have hge : 2 * (n + 2 - k) ≤ ℓ.val := by omega
        have hmem : ℓ ∈ C := by
          simp [C, hge]
        exact Finset.mem_union_right (A ∪ B) hmem
  calc
    (∏ ℓ ∈ (Finset.univ : Finset (Fin (2 * n - k + 2))), f ℓ)
        = (∏ ℓ ∈ (A ∪ B ∪ C : Finset (Fin (2 * n - k + 2))), f ℓ) := by rw [hcover]
    _ = (∏ ℓ ∈ A, f ℓ) * (∏ ℓ ∈ B, f ℓ) * (∏ ℓ ∈ C, f ℓ) := by
        rw [Finset.prod_union hdAB_C]
        rw [Finset.prod_union hdAB]
    _ = (∏ ℓ ∈ (Finset.univ.filter (fun ℓ : Fin (2 * n - k + 2) => ℓ.val < n + 2 - k)), f ℓ) *
      (∏ ℓ ∈ (Finset.univ.filter (fun ℓ : Fin (2 * n - k + 2) =>
          n + 2 - k ≤ ℓ.val ∧ ℓ.val < 2 * (n + 2 - k))), f ℓ) *
      (∏ ℓ ∈ (Finset.univ.filter (fun ℓ : Fin (2 * n - k + 2) => 2 * (n + 2 - k) ≤ ℓ.val)), f ℓ) := by
        rfl

private lemma prod_univ_label_le (n k : ℕ) (hk2 : 2 ≤ k) (hkn : k ≤ n + 1)
    (H : Fin k → ℝ) (hmono : Monotone H) (hHge : ∀ i : Fin k, 1 ≤ H i)
    (L : Fin (2 * n - k + 2) → Fin k)
    (hLab0 : ∀ ℓ : Fin (2 * n - k + 2), ℓ.val < n + 2 - k → L ℓ = ⟨0, by omega⟩)
    (hLab1 : ∀ ℓ : Fin (2 * n - k + 2), n + 2 - k ≤ ℓ.val → ℓ.val < 2 * (n + 2 - k) →
        L ℓ = ⟨1, by omega⟩)
    (hLab2 : ∀ ℓ : Fin (2 * n - k + 2), 2 * (n + 2 - k) ≤ ℓ.val → (L ℓ).val ≤ (ℓ.val - 2 * (n + 2 - k)) + 2) :
    (∏ ℓ ∈ (Finset.univ : Finset (Fin (2 * n - k + 2))), H (L ℓ)) ≤
      (H ⟨0, by omega⟩) ^ (n + 2 - k) * (H ⟨1, by omega⟩) ^ (n + 2 - k) *
        ∏ j : Fin (k - 2), H ⟨j.val + 2, by omega⟩ := by
  classical
  let A : Finset (Fin (2 * n - k + 2)) := Finset.univ.filter (fun ℓ => ℓ.val < n + 2 - k)
  let B : Finset (Fin (2 * n - k + 2)) := Finset.univ.filter (fun ℓ =>
      n + 2 - k ≤ ℓ.val ∧ ℓ.val < 2 * (n + 2 - k))
  let C : Finset (Fin (2 * n - k + 2)) := Finset.univ.filter (fun ℓ => 2 * (n + 2 - k) ≤ ℓ.val)
  have hdecomp := prod_univ_block_decomp n k hk2 hkn (fun ℓ => H (L ℓ))
  -- block A: each factor H0
  have hA : (∏ ℓ ∈ A, H (L ℓ)) = (H ⟨0, by omega⟩) ^ (n + 2 - k) := by
    calc
      (∏ ℓ ∈ A, H (L ℓ)) = (∏ ℓ ∈ A, H ⟨0, by omega⟩) := by
        refine Finset.prod_congr rfl ?_
        intro ℓ hℓ
        have hlt : ℓ.val < n + 2 - k := by simpa [A] using hℓ
        exact congrArg H (hLab0 ℓ hlt)
      _ = (H ⟨0, by omega⟩) ^ (n + 2 - k) := by
        rw [Finset.prod_const]
        have hcard : A.card = n + 2 - k := by
          dsimp [A]
          exact card_B0 n k hk2 hkn
        rw [hcard]
  have hB : (∏ ℓ ∈ B, H (L ℓ)) = (H ⟨1, by omega⟩) ^ (n + 2 - k) := by
    calc
      (∏ ℓ ∈ B, H (L ℓ)) = (∏ ℓ ∈ B, H ⟨1, by omega⟩) := by
        refine Finset.prod_congr rfl ?_
        intro ℓ hℓ
        have hm : n + 2 - k ≤ ℓ.val ∧ ℓ.val < 2 * (n + 2 - k) := by simpa [B] using hℓ
        exact congrArg H (hLab1 ℓ hm.1 hm.2)
      _ = (H ⟨1, by omega⟩) ^ (n + 2 - k) := by
        rw [Finset.prod_const]
        have hcard : B.card = n + 2 - k := by
          dsimp [B]
          exact card_B1 n k hk2 hkn
        rw [hcard]
  have hC : (∏ ℓ ∈ C, H (L ℓ)) ≤ ∏ j : Fin (k - 2), H ⟨j.val + 2, by omega⟩ := by
    dsimp [C]
    exact extras_prod_le n k hk2 hkn H hmono hHge L hLab2
  calc
    (∏ ℓ ∈ (Finset.univ : Finset (Fin (2 * n - k + 2))), H (L ℓ))
        = (∏ ℓ ∈ A, H (L ℓ)) * (∏ ℓ ∈ B, H (L ℓ)) * (∏ ℓ ∈ C, H (L ℓ)) := hdecomp
    _ ≤ (H ⟨0, by omega⟩) ^ (n + 2 - k) * (H ⟨1, by omega⟩) ^ (n + 2 - k) *
        ∏ j : Fin (k - 2), H ⟨j.val + 2, by omega⟩ := by
        rw [hA, hB]
        -- (H0^m)*(H1^m)*ΠC ≤ (H0^m)(H1^m)Π
        have hC0 : 0 ≤ (H ⟨0, by omega⟩) ^ (n + 2 - k) :=
          pow_nonneg (H_nonneg_of_ge1 hHge ⟨0, by omega⟩) _
        have hC1 : 0 ≤ (H ⟨1, by omega⟩) ^ (n + 2 - k) :=
          pow_nonneg (H_nonneg_of_ge1 hHge ⟨1, by omega⟩) _
        have hnonnegC : ∀ ℓ ∈ C, 0 ≤ H (L ℓ) := by
          intro ℓ hℓ
          exact H_nonneg_of_ge1 hHge (L ℓ)
        have hle1 : (∏ ℓ ∈ C, H (L ℓ)) ≤ ∏ j : Fin (k - 2), H ⟨j.val + 2, by omega⟩ := hC
        calc
          (H ⟨0, by omega⟩) ^ (n + 2 - k) * (H ⟨1, by omega⟩) ^ (n + 2 - k) * (∏ ℓ ∈ C, H (L ℓ))
              ≤ (H ⟨0, by omega⟩) ^ (n + 2 - k) * (H ⟨1, by omega⟩) ^ (n + 2 - k) *
                  ∏ j : Fin (k - 2), H ⟨j.val + 2, by omega⟩ := by
                  have hle1' : (∏ ℓ ∈ C, H (L ℓ)) ≤
                      ∏ j : Fin (k - 2), H ⟨j.val + 2, by omega⟩ := hle1
                  have hprod0 : 0 ≤ (∏ ℓ ∈ C, H (L ℓ)) := by
                    exact Finset.prod_nonneg (fun ℓ hℓ => H_nonneg_of_ge1 hHge (L ℓ))
                  have hab0 : 0 ≤ (H ⟨0, by omega⟩) ^ (n + 2 - k) * (H ⟨1, by omega⟩) ^ (n + 2 - k) :=
                    mul_nonneg hC0 hC1
                  exact mul_le_mul_of_nonneg_left hle1' hab0

private lemma prod_erase_eq_div {ι : Type} [DecidableEq ι] (s : Finset ι) (f : ι → ℝ) (a : ι)
    (ha : a ∈ s) (hfa : f a ≠ 0) :
    (∏ x ∈ s.erase a, f x) = (∏ x ∈ s, f x) / f a := by
  classical
  have h := Finset.mul_prod_erase s f ha
  have htype : (∏ x ∈ s.erase a, f x) * f a = ∏ x ∈ s, f x := by simpa [mul_comm] using h
  calc
    (∏ x ∈ s.erase a, f x) = ((∏ x ∈ s.erase a, f x) * f a) / f a := by
      field_simp [hfa]
    _ = (∏ x ∈ s, f x) / f a := by rw [htype]

/-- Per-index erase product bound. -/
private lemma erase_label_prod_le (n k : ℕ) (hk2 : 2 ≤ k) (hkn : k ≤ n + 1)
    (H : Fin k → ℝ) (hmono : Monotone H) (hHge : ∀ i : Fin k, 1 ≤ H i)
    (L : Fin (2 * n - k + 2) → Fin k)
    (hLab0 : ∀ ℓ : Fin (2 * n - k + 2), ℓ.val < n + 2 - k → L ℓ = ⟨0, by omega⟩)
    (hLab1 : ∀ ℓ : Fin (2 * n - k + 2), n + 2 - k ≤ ℓ.val → ℓ.val < 2 * (n + 2 - k) →
        L ℓ = ⟨1, by omega⟩)
    (hLab2 : ∀ ℓ : Fin (2 * n - k + 2), 2 * (n + 2 - k) ≤ ℓ.val → (L ℓ).val ≤ (ℓ.val - 2 * (n + 2 - k)) + 2)
    (a : Fin (2 * n - k + 2)) :
    (∏ ℓ ∈ (Finset.univ.erase a), H (L ℓ)) ≤
      (H ⟨0, by omega⟩) ^ (n + 1 - k) * (H ⟨1, by omega⟩) ^ (n + 2 - k) *
        ∏ j : Fin (k - 2), H ⟨j.val + 2, by omega⟩ := by
  classical
  have hdiv : (∏ ℓ ∈ (Finset.univ.erase a), H (L ℓ)) =
      (∏ ℓ ∈ (Finset.univ : Finset (Fin (2 * n - k + 2))), H (L ℓ)) / H (L a) := by
    exact prod_erase_eq_div (s := (Finset.univ : Finset (Fin (2 * n - k + 2))))
      (fun ℓ => H (L ℓ)) a (by simp)
      (by have h1 : (1 : ℝ) ≤ H (L a) := hHge (L a); linarith)
  have hle := prod_univ_label_le n k hk2 hkn H hmono hHge L hLab0 hLab1 hLab2
  have hLa0 : 0 < H (L a) := by
    have h1 : (1 : ℝ) ≤ H (L a) := hHge (L a)
    linarith
  have hH00 : 0 < H ⟨0, by omega⟩ := by
    have h1 : (1 : ℝ) ≤ H ⟨0, by omega⟩ := hHge ⟨0, by omega⟩
    linarith
  have hH0leLa : H ⟨0, by omega⟩ ≤ H (L a) := by
    apply hmono
    rw [Fin.le_def]
    have hzero : (0 : ℕ) ≤ (L a).val := Nat.zero_le _
    simpa using hzero
  calc
    (∏ ℓ ∈ (Finset.univ.erase a), H (L ℓ))
        = (∏ ℓ ∈ (Finset.univ : Finset (Fin (2 * n - k + 2))), H (L ℓ)) / H (L a) := hdiv
    _ ≤ ((H ⟨0, by omega⟩) ^ (n + 2 - k) * (H ⟨1, by omega⟩) ^ (n + 2 - k) *
          ∏ j : Fin (k - 2), H ⟨j.val + 2, by omega⟩) / H (L a) := by
          exact div_le_div_of_nonneg_right hle (le_of_lt hLa0)
    _ ≤ ((H ⟨0, by omega⟩) ^ (n + 2 - k) * (H ⟨1, by omega⟩) ^ (n + 2 - k) *
          ∏ j : Fin (k - 2), H ⟨j.val + 2, by omega⟩) / H ⟨0, by omega⟩ := by
          have hH10 : 0 < H ⟨1, by omega⟩ := by
            have h1 : (1 : ℝ) ≤ H ⟨1, by omega⟩ := hHge ⟨1, by omega⟩
            linarith
          have hPj0 : 0 ≤ ∏ j : Fin (k - 2), H ⟨j.val + 2, by omega⟩ := by
            exact Finset.prod_nonneg (fun j hj => H_nonneg_of_ge1 hHge ⟨j.val + 2, by omega⟩)
          have hnum0 : 0 ≤ (H ⟨0, by omega⟩) ^ (n + 2 - k) * (H ⟨1, by omega⟩) ^ (n + 2 - k) *
              ∏ j : Fin (k - 2), H ⟨j.val + 2, by omega⟩ := by
            exact mul_nonneg (mul_nonneg (pow_nonneg (le_of_lt hH00) _)
              (pow_nonneg (le_of_lt hH10) _)) hPj0
          calc
            ((H ⟨0, by omega⟩) ^ (n + 2 - k) * (H ⟨1, by omega⟩) ^ (n + 2 - k) *
                ∏ j : Fin (k - 2), H ⟨j.val + 2, by omega⟩) / H (L a)
                = ((H ⟨0, by omega⟩) ^ (n + 2 - k) * (H ⟨1, by omega⟩) ^ (n + 2 - k) *
                    ∏ j : Fin (k - 2), H ⟨j.val + 2, by omega⟩) * (H (L a))⁻¹ := by
                    rw [div_eq_mul_inv]
            _ ≤ ((H ⟨0, by omega⟩) ^ (n + 2 - k) * (H ⟨1, by omega⟩) ^ (n + 2 - k) *
                    ∏ j : Fin (k - 2), H ⟨j.val + 2, by omega⟩) * (H ⟨0, by omega⟩)⁻¹ := by
                    have hinv : (H (L a))⁻¹ ≤ (H ⟨0, by omega⟩)⁻¹ :=
                      (inv_le_inv₀ hLa0 hH00).2 hH0leLa
                    exact mul_le_mul_of_nonneg_left hinv hnum0
            _ = ((H ⟨0, by omega⟩) ^ (n + 2 - k) * (H ⟨1, by omega⟩) ^ (n + 2 - k) *
                    ∏ j : Fin (k - 2), H ⟨j.val + 2, by omega⟩) / H ⟨0, by omega⟩ := by
                    rw [div_eq_mul_inv]
    _ = (H ⟨0, by omega⟩) ^ (n + 1 - k) * (H ⟨1, by omega⟩) ^ (n + 2 - k) *
          ∏ j : Fin (k - 2), H ⟨j.val + 2, by omega⟩ := by
          have hM0' : (n + 2 - k) = (n + 1 - k) + 1 := by omega
          rw [hM0']
          rw [pow_succ]
          field_simp [hH00.ne']

private lemma prod_filter_eq_prod_shift (k : ℕ) (hk2 : 2 ≤ k) (H : Fin k → ℝ) :
    (∏ j ∈ (Finset.univ.filter (fun j : Fin k => 2 ≤ j.val)), H j) =
      ∏ j : Fin (k - 2), H ⟨j.val + 2, by omega⟩ := by
  classical
  refine Finset.prod_bij (s := Finset.univ.filter (fun j : Fin k => 2 ≤ j.val))
    (t := Finset.univ) (f := H)
    (g := fun j : Fin (k - 2) => H ⟨j.val + 2, by omega⟩)
    (i := fun j hj => ⟨j.val - 2, by
        have hj2 : 2 ≤ j.val := (Finset.mem_filter.mp hj).2
        have hjv : j.val < k := j.isLt
        omega⟩)
    (hi := by intro a ha; simp)
    (i_inj := by
        intro a ha b hb h
        apply Fin.ext
        have hv : a.val - 2 = b.val - 2 := congrArg Fin.val h
        have ha2 : 2 ≤ a.val := (Finset.mem_filter.mp ha).2
        have hb2 : 2 ≤ b.val := (Finset.mem_filter.mp hb).2
        omega)
    (i_surj := by
        intro b hb
        have hbnd : b.val + 2 < k := by have hbv : b.val < k - 2 := b.isLt; omega
        let a : Fin k := ⟨b.val + 2, hbnd⟩
        have hamem : a ∈ (Finset.univ.filter (fun j : Fin k => 2 ≤ j.val)) := by
          simp [a, hbnd]
        exact ⟨a, hamem, by
          apply Fin.ext
          dsimp [a]
          omega⟩)
    (h := by
        intro a ha
        congr 1
        apply Fin.ext
        have ha2 : 2 ≤ a.val := (Finset.mem_filter.mp ha).2
        change a.val = (a.val - 2) + 2
        omega)
private lemma sum_erase_prod_le (n k : ℕ) (hk2 : 2 ≤ k) (hkn : k ≤ n + 1)
    (H : Fin k → ℝ) (hmono : Monotone H) (hHge : ∀ i : Fin k, 1 ≤ H i)
    (C : ℝ) (hC1 : 1 ≤ C)
    (A : Fin (2 * n - k + 2) → ℝ) (L : Fin (2 * n - k + 2) → Fin k)
    (hAnonneg : ∀ ℓ : Fin (2 * n - k + 2), 0 ≤ A ℓ)
    (hAub : ∀ ℓ : Fin (2 * n - k + 2), A ℓ ≤ C * H (L ℓ))
    (hLab0 : ∀ ℓ : Fin (2 * n - k + 2), ℓ.val < n + 2 - k → L ℓ = ⟨0, by omega⟩)
    (hLab1 : ∀ ℓ : Fin (2 * n - k + 2), n + 2 - k ≤ ℓ.val → ℓ.val < 2 * (n + 2 - k) →
        L ℓ = ⟨1, by omega⟩)
    (hLab2 : ∀ ℓ : Fin (2 * n - k + 2), 2 * (n + 2 - k) ≤ ℓ.val → (L ℓ).val ≤ (ℓ.val - 2 * (n + 2 - k)) + 2) :
    (∑ a : Fin (2 * n - k + 2), ∏ j ∈ (Finset.univ.erase a), A j) ≤
      (Fintype.card (Fin (2 * n - k + 2)) : ℝ) * C ^ (2 * n - k + 1) *
        (H ⟨0, by omega⟩) ^ (n + 1 - k) * (H ⟨1, by omega⟩) ^ (n + 2 - k) *
          ∏ j : Fin (k - 2), H ⟨j.val + 2, by omega⟩ := by
  classical
  let N : ℕ := 2 * n - k + 2
  have hC0 : 0 ≤ C := le_trans zero_le_one hC1
  have hper : ∀ a : Fin N, (∏ j ∈ (Finset.univ.erase a), A j) ≤
      C ^ (2 * n - k + 1) * ((H ⟨0, by omega⟩) ^ (n + 1 - k) *
        (H ⟨1, by omega⟩) ^ (n + 2 - k) * ∏ j : Fin (k - 2), H ⟨j.val + 2, by omega⟩) := by
    intro a
    have hprod1 : (∏ j ∈ (Finset.univ.erase a), A j) ≤
        ∏ j ∈ (Finset.univ.erase a), (C * H (L j)) := by
      refine Finset.prod_le_prod ?h0 ?h1
      · intro j hj
        exact hAnonneg j
      · intro j hj
        exact hAub j
    have hcard : (Finset.univ.erase a).card = 2 * n - k + 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ a)]
      simp [Fintype.card_fin]
      omega
    have hprod2 : (∏ j ∈ (Finset.univ.erase a), (C * H (L j))) =
        C ^ (2 * n - k + 1) * (∏ j ∈ (Finset.univ.erase a), H (L j)) := by
      calc
        (∏ j ∈ (Finset.univ.erase a), (C * H (L j))) = (∏ j ∈ (Finset.univ.erase a), C) *
            (∏ j ∈ (Finset.univ.erase a), H (L j)) := by
              rw [Finset.prod_mul_distrib]
        _ = C ^ (2 * n - k + 1) * (∏ j ∈ (Finset.univ.erase a), H (L j)) := by
              rw [Finset.prod_const, hcard]
    have hel : (∏ j ∈ (Finset.univ.erase a), A j) ≤
        C ^ (2 * n - k + 1) * (∏ j ∈ (Finset.univ.erase a), H (L j)) := by
      exact le_trans hprod1 (le_of_eq hprod2)
    have hel2 : (∏ j ∈ (Finset.univ.erase a), H (L j)) ≤
        (H ⟨0, by omega⟩) ^ (n + 1 - k) * (H ⟨1, by omega⟩) ^ (n + 2 - k) *
          ∏ j : Fin (k - 2), H ⟨j.val + 2, by omega⟩ :=
      erase_label_prod_le n k hk2 hkn H hmono hHge L hLab0 hLab1 hLab2 a
    have hpow0 : 0 ≤ C ^ (2 * n - k + 1) := pow_nonneg hC0 _
    exact le_trans hel (mul_le_mul_of_nonneg_left hel2 hpow0)
  calc
    (∑ a : Fin (2 * n - k + 2), ∏ j ∈ (Finset.univ.erase a), A j)
        = ∑ a : Fin N, ∏ j ∈ (Finset.univ.erase a), A j := by
            rfl
    _ ≤ ∑ a : Fin N, (C ^ (2 * n - k + 1) * ((H ⟨0, by omega⟩) ^ (n + 1 - k) *
        (H ⟨1, by omega⟩) ^ (n + 2 - k) * ∏ j : Fin (k - 2), H ⟨j.val + 2, by omega⟩)) := by
        refine Finset.sum_le_sum ?_
        intro a ha
        exact hper a
    _ = (Fintype.card (Fin N) : ℝ) * (C ^ (2 * n - k + 1) * ((H ⟨0, by omega⟩) ^ (n + 1 - k) *
        (H ⟨1, by omega⟩) ^ (n + 2 - k) * ∏ j : Fin (k - 2), H ⟨j.val + 2, by omega⟩)) := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    _ = (Fintype.card (Fin N) : ℝ) * C ^ (2 * n - k + 1) * (H ⟨0, by omega⟩) ^ (n + 1 - k) *
        (H ⟨1, by omega⟩) ^ (n + 2 - k) * ∏ j : Fin (k - 2), H ⟨j.val + 2, by omega⟩ := by
        ring

private lemma eval_map_real_complex (ξ : ℝ) (p : Polynomial ℝ) :
    Polynomial.eval ((ξ : ℂ)) (p.map (algebraMap ℝ ℂ)) = ((Polynomial.eval ξ p : ℝ) : ℂ) := by
  rw [Polynomial.eval_map]
  change Polynomial.eval₂ (algebraMap ℝ ℂ) (algebraMap ℝ ℂ ξ) p =
      ((Polynomial.eval ξ p : ℝ) : ℂ)
  exact Polynomial.eval₂_at_apply (f := algebraMap ℝ ℂ) (r := ξ) (p := p)

private lemma norm_eval_real_complex (ξ : ℝ) (p : Polynomial ℝ) :
    ‖Polynomial.eval ((ξ : ℂ)) (p.map (algebraMap ℝ ℂ))‖ = ‖Polynomial.eval ξ p‖ := by
  calc
    ‖Polynomial.eval ((ξ : ℂ)) (p.map (algebraMap ℝ ℂ))‖ = ‖((Polynomial.eval ξ p : ℝ) : ℂ)‖ := by
        rw [eval_map_real_complex]
    _ = ‖Polynomial.eval ξ p‖ := by rw [Complex.norm_real]

private lemma map_int_real_complex (S : Polynomial ℤ) :
    S.map (Int.castRingHom ℂ) = (S.map (Int.castRingHom ℝ)).map (algebraMap ℝ ℂ) := by
  rw [Polynomial.map_map]
  rfl

private lemma norm_eval_int_complex (ξ : ℝ) (S : Polynomial ℤ) :
    ‖Polynomial.eval (ξ : ℂ) (S.map (Int.castRingHom ℂ))‖ =
      ‖Polynomial.eval ξ (S.map (Int.castRingHom ℝ))‖ := by
  calc
    ‖Polynomial.eval (ξ : ℂ) (S.map (Int.castRingHom ℂ))‖
        = ‖Polynomial.eval (ξ : ℂ) ((S.map (Int.castRingHom ℝ)).map (algebraMap ℝ ℂ))‖ := by
            rw [map_int_real_complex]
    _ = ‖Polynomial.eval ξ (S.map (Int.castRingHom ℝ))‖ := by
            exact norm_eval_real_complex ξ (S.map (Int.castRingHom ℝ))

private lemma natDegree_map_complex (S : Polynomial ℤ) :
    (S.map (Int.castRingHom ℂ)).natDegree = S.natDegree := by
  exact Polynomial.natDegree_map_eq_of_injective (f := Int.castRingHom ℂ) Int.cast_injective S

private lemma derivative_map_complex (S : Polynomial ℤ) :
    ((S.map (Int.castRingHom ℂ)).derivative) = ((S.derivative).map (Int.castRingHom ℂ)) := by
  rw [Polynomial.derivative_map]

/-- Root-close for an integer polynomial evaluated at a real point, in terms of the real
evaluations. -/
private lemma root_close_int (S : Polynomial ℤ) (ξ : ℝ) (hS : 1 ≤ S.natDegree) :
    ∃ α : ℂ,
      Polynomial.IsRoot (S.map (Int.castRingHom ℂ)) α ∧
      ‖(ξ : ℂ) - α‖ * ‖Polynomial.eval ξ (((S.derivative).map (Int.castRingHom ℝ)))‖ ≤
        (S.natDegree : ℝ) * ‖Polynomial.eval ξ (S.map (Int.castRingHom ℝ))‖ := by
  have hSdegC : 1 ≤ (S.map (Int.castRingHom ℂ)).natDegree := by
    rw [natDegree_map_complex]
    exact hS
  rcases root_close_deriv_bound (S := S.map (Int.castRingHom ℂ)) hSdegC (ξ : ℂ) with ⟨α, hroot, hb⟩
  refine ⟨α, hroot, ?_⟩
  have hbA : ‖(ξ : ℂ) - α‖ *
      ‖Polynomial.eval (ξ : ℂ) (((S.map (Int.castRingHom ℂ)).derivative))‖ ≤
      (S.map (Int.castRingHom ℂ)).natDegree *
        ‖Polynomial.eval (ξ : ℂ) (S.map (Int.castRingHom ℂ))‖ := hb
  have hb1 : ‖(ξ : ℂ) - α‖ *
      ‖Polynomial.eval (ξ : ℂ) (((S.derivative).map (Int.castRingHom ℂ)))‖ ≤
      (S.natDegree : ℝ) * ‖Polynomial.eval ξ (S.map (Int.castRingHom ℝ))‖ := by
    have hdmap : ((S.map (Int.castRingHom ℂ)).derivative) =
        ((S.derivative).map (Int.castRingHom ℂ)) := derivative_map_complex S
    simpa [hdmap, natDegree_map_complex, norm_eval_int_complex] using hbA
  have hrc : ‖Polynomial.eval ξ (((S.derivative).map (Int.castRingHom ℝ)))‖ =
      ‖Polynomial.eval (ξ : ℂ) (((S.derivative).map (Int.castRingHom ℂ)))‖ :=
    (norm_eval_int_complex ξ (S.derivative)).symm
  rw [hrc]
  exact hb1

theorem p51_aux_real (n : ℕ) (hn : 2 ≤ n) (ξ : ℝ) :
    ∀ k : ℕ, ∀ hk2 : 2 ≤ k, ∀ hkn : k ≤ n + 1, ∃ c : ℝ, 0 < c ∧
    ∀ (P : Fin k → Polynomial ℤ) (δ : ℝ), 0 < δ →
      (∀ i : Fin k, (P i).natDegree ≤ n) →
      LinearIndependent ℝ (fun i : Fin k => (P i).map (Int.castRingHom ℝ)) →
      IsCoprime ((P ⟨0, by omega⟩).map (Int.castRingHom ℝ))
        ((P ⟨1, by omega⟩).map (Int.castRingHom ℝ)) →
      Monotone (fun i : Fin k => ((P i).map (Int.castRingHom ℝ)).supNorm) →
      (∀ i : Fin k,
        ‖Polynomial.eval ξ ((P i).map (Int.castRingHom ℝ))‖ ≤ δ) →
      ∃ m : Fin k, ∃ α : ℂ,
        IsAlgebraic ℚ α ∧
        Polynomial.natDegree (minpoly ℚ α) ≤ n ∧
        ((((let p := minpoly ℚ α;
            let D := Multiset.lcm (Multiset.map (fun i ↦ (p.coeff i).den) p.support.val);
            Finset.sup p.support (fun i ↦ (D * p.coeff i).num.natAbs) : ℕ) : ℝ)) ≤
          c * ((P m).map (Int.castRingHom ℝ)).supNorm) ∧
        ‖(ξ : ℂ) - α‖ ≤
          c * δ ^ 2 *
            (((P ⟨0, by omega⟩).map (Int.castRingHom ℝ)).supNorm) ^ (n + 1 - k) *
            (((P ⟨1, by omega⟩).map (Int.castRingHom ℝ)).supNorm) ^ (n + 2 - k) *
            (Finset.prod (Finset.univ.filter (fun j : Fin k => 2 ≤ j.val))
              (fun j : Fin k => (((P j).map (Int.castRingHom ℝ)).supNorm))) *
            (((P m).map (Int.castRingHom ℝ)).supNorm)⁻¹ := by
  intro k hk2 hkn
  have hn1 : 1 ≤ n := by omega
  let N0 : ℕ := 2 * n - k + 1
  have hN0ge1 : 1 ≤ N0 := by dsimp [N0]; omega
  let E : ℝ := (1 + |ξ|) ^ N0
  have hE1 : 1 ≤ E := by
    dsimp [E]
    apply one_le_pow₀
    have : (0 : ℝ) ≤ |ξ| := abs_nonneg ξ
    linarith
  have hEpos : 0 < E := by linarith
  rcases p51_lift_pair_uniform2 n k hn1 hk2 hkn ξ with ⟨C0, hC0pos, hC0main⟩
  let C : ℝ := max C0 1
  have hC1 : 1 ≤ C := le_max_right C0 1
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC1
  have hC0leC : C0 ≤ C := le_max_left C0 1
  rcases p51_det_deriv_bound N0 hN0ge1 ξ with ⟨c_det, hc_detpos, hc_detmain⟩
  rcases root_height_bound n with ⟨c_root, hc_rootpos, hc_rootmain⟩
  have hcardRpos : 0 < (Fintype.card (Fin (2 * n - k + 2)) : ℝ) := by
    have hc : 0 < Fintype.card (Fin (2 * n - k + 2)) := by
      rw [Fintype.card_fin]
      omega
    exact_mod_cast hc
  have hcardR0 : 0 ≤ (Fintype.card (Fin (2 * n - k + 2)) : ℝ) := le_of_lt hcardRpos
  have hN0posR : 0 < (N0 : ℝ) := by exact_mod_cast hN0ge1
  let cardR : ℝ := (Fintype.card (Fin (2 * n - k + 2)) : ℝ)
  let cSig : ℝ := cardR * C ^ (2 * n - k + 1)
  let c2 : ℝ := c_det * E * C0 * cSig * cardR
  let cProx : ℝ := (N0 : ℝ) * E * C0 * c2 * C
  let cFin : ℝ := cProx + c_root * C + 1
  have hcSigpos : 0 < cSig := by
    dsimp [cSig]
    exact mul_pos hcardRpos (pow_pos hCpos _)
  have hc2pos0 : 0 < c2 := by
    dsimp [c2]
    exact mul_pos (mul_pos (mul_pos (mul_pos hc_detpos hEpos) hC0pos) hcSigpos) hcardRpos
  have hcProxpos : 0 < cProx := by
    dsimp [cProx]
    exact mul_pos (mul_pos (mul_pos (mul_pos hN0posR hEpos) hC0pos) hc2pos0) hCpos
  have hcFinpos : 0 < cFin := by
    dsimp [cFin]
    positivity
  have hcFin_ge_prox : cProx ≤ cFin := by
    dsimp [cFin]
    have hnonneg : 0 ≤ c_root * C + 1 := by positivity
    linarith
  refine ⟨cFin, hcFinpos, ?_⟩
  intro P δ hδ hdeg hLI hcopR hmono heval
  have hPne : ∀ i : Fin k, P i ≠ 0 := fun i => li_ne_zero P hLI i
  have hHgeP : ∀ i : Fin k, (1 : ℝ) ≤ ((P i).map (Int.castRingHom ℝ)).supNorm := by
    intro i
    exact int_poly_supNorm_one_le (P i) (hPne i)
  rcases hC0main P hdeg hPne hLI hcopR with ⟨Q, hQdeg, hQdeg0, hQdeg1, hQcopR, hQli,
      hQfix, hQup, hQlo, hQeval⟩
  have hQne : ∀ i : Fin k, Q i ≠ 0 := by
    intro i
    intro hz
    have hv : (Q i).map (Int.castRingHom ℝ) = 0 := by simp [hz]
    exact LinearIndependent.ne_zero i hQli hv
  rcases complete_family_int n k hn1 hk2 hkn Q hQdeg hQdeg0 hQdeg1 hQcopR hQli with
    ⟨S, lab, exp, hSdef, hLab0, hLab1, hLab2c, hdegS, hSLI⟩
  -- constants derived
  let H : Fin k → ℝ := fun i => ((P i).map (Int.castRingHom ℝ)).supNorm
  have hHmono : Monotone H := by
    dsimp [H]
    exact hmono
  have hHge : ∀ i : Fin k, (1 : ℝ) ≤ H i := by
    intro i
    dsimp [H]
    exact hHgeP i
  have hQupC : ∀ i : Fin k, ((Q i).map (Int.castRingHom ℝ)).supNorm ≤ C * H i := by
    intro i
    calc
      ((Q i).map (Int.castRingHom ℝ)).supNorm ≤ C0 * H i := by
        dsimp [H]
        exact hQup i
      _ ≤ C * H i := by
        exact mul_le_mul_of_nonneg_right hC0leC (p51H_nonneg (P i))
  have hQloC : ∀ i : Fin k, H i ≤ C * ((Q i).map (Int.castRingHom ℝ)).supNorm := by
    intro i
    calc
      H i ≤ C0 * ((Q i).map (Int.castRingHom ℝ)).supNorm := by
        dsimp [H]
        exact hQlo i
      _ ≤ C * ((Q i).map (Int.castRingHom ℝ)).supNorm := by
        exact mul_le_mul_of_nonneg_right hC0leC ((Q i).map (Int.castRingHom ℝ)).supNorm_nonneg
  -- A-values
  let A : Fin (2 * n - k + 2) → ℝ := fun ℓ => ((S ℓ).map (Int.castRingHom ℝ)).supNorm
  have hAnonneg : ∀ ℓ : Fin (2 * n - k + 2), 0 ≤ A ℓ := by
    intro ℓ
    dsimp [A]
    exact ((S ℓ).map (Int.castRingHom ℝ)).supNorm_nonneg
  have hLab0p : ∀ ℓ : Fin (2 * n - k + 2), ℓ.val < n + 2 - k → lab ℓ = ⟨0, by omega⟩ := by
    intro ℓ hlt
    exact (hLab0 ℓ hlt).1
  have hLab1p : ∀ ℓ : Fin (2 * n - k + 2), n + 2 - k ≤ ℓ.val → ℓ.val < 2 * (n + 2 - k) →
      lab ℓ = ⟨1, by omega⟩ := by
    intro ℓ hge hlt2
    exact (hLab1 ℓ hge hlt2).1
  have hLab2 : ∀ ℓ : Fin (2 * n - k + 2), 2 * (n + 2 - k) ≤ ℓ.val →
      (lab ℓ).val ≤ (ℓ.val - 2 * (n + 2 - k)) + 2 := by
    intro ℓ hge
    exact (hLab2c ℓ hge).2
  have hLab2ge2 : ∀ ℓ : Fin (2 * n - k + 2), 2 * (n + 2 - k) ≤ ℓ.val → 2 ≤ (lab ℓ).val := by
    intro ℓ hge
    exact (hLab2c ℓ hge).1
  have hAeqQ : ∀ ℓ : Fin (2 * n - k + 2), A ℓ = ((Q (lab ℓ)).map (Int.castRingHom ℝ)).supNorm := by
    intro ℓ
    dsimp [A]
    rw [hSdef ℓ]
    exact supNorm_map_X_pow_mul (Q (lab ℓ)) (exp ℓ)
  have hAub : ∀ ℓ : Fin (2 * n - k + 2), A ℓ ≤ C * H (lab ℓ) := by
    intro ℓ
    rw [hAeqQ ℓ]
    exact hQupC (lab ℓ)
  -- evaluation bounds
  have hδQ : ∀ i : Fin k, ‖Polynomial.eval ξ ((Q i).map (Int.castRingHom ℝ))‖ ≤ C0 * δ := by
    intro i
    calc
      ‖Polynomial.eval ξ ((Q i).map (Int.castRingHom ℝ))‖ ≤ C0 * ‖Polynomial.eval ξ ((P i).map (Int.castRingHom ℝ))‖ := hQeval i
      _ ≤ C0 * δ := by
        exact mul_le_mul_of_nonneg_left (heval i) (le_of_lt hC0pos)
  have hexp_le_N0 : ∀ ℓ : Fin (2 * n - k + 2), exp ℓ ≤ N0 := by
    intro ℓ
    have hdeg0 : (0 : ℕ) ≤ (Q (lab ℓ)).natDegree := Nat.zero_le _
    have h := hdegS ℓ
    change exp ℓ ≤ 2 * n - k + 1
    omega
  have hevalS : ∀ ℓ : Fin (2 * n - k + 2),
      ‖Polynomial.eval ξ ((S ℓ).map (Int.castRingHom ℝ))‖ ≤ E * (C0 * δ) := by
    intro ℓ
    have h1 := eval_X_pow_mul_norm_le ξ (Q (lab ℓ)) (exp ℓ) N0 (hexp_le_N0 ℓ)
    calc
      ‖Polynomial.eval ξ ((S ℓ).map (Int.castRingHom ℝ))‖
          = ‖Polynomial.eval ξ ((((Polynomial.X ^ (exp ℓ) * Q (lab ℓ))).map (Int.castRingHom ℝ)))‖ := by
              rw [hSdef ℓ]
      _ ≤ (1 + |ξ|) ^ N0 * ‖Polynomial.eval ξ ((Q (lab ℓ)).map (Int.castRingHom ℝ))‖ := h1
      _ ≤ (1 + |ξ|) ^ N0 * (C0 * δ) := by
          exact mul_le_mul_of_nonneg_left (hδQ (lab ℓ)) (by positivity : 0 ≤ (1 + |ξ|) ^ N0)
      _ = E * (C0 * δ) := by rfl
  -- degree bound of S
  have hdegS' : ∀ ℓ : Fin (2 * n - k + 2), (S ℓ).natDegree ≤ N0 := by
    intro ℓ
    rw [hSdef ℓ]
    have heq : ((Polynomial.X ^ (exp ℓ) * Q (lab ℓ)).natDegree) = exp ℓ + (Q (lab ℓ)).natDegree :=
      natDegree_X_pow_mul_deg (hQne (lab ℓ)) (exp ℓ)
    rw [heq]
    have h := hdegS ℓ
    change exp ℓ + (Q (lab ℓ)).natDegree ≤ 2 * n - k + 1
    omega
  have hSne : ∀ ℓ : Fin (2 * n - k + 2), S ℓ ≠ 0 := by
    intro ℓ
    rw [hSdef ℓ]
    exact X_pow_mul_ne_zero (hQne (lab ℓ)) (exp ℓ)

  -- (2) determinant lemma on the complete family S
  have hδev : 0 < E * (C0 * δ) := by positivity
  have hdet := hc_detmain S (E * (C0 * δ)) hδev hdegS' hSne hSLI hevalS
  let SA : ℝ := ∑ a : Fin (2 * n - k + 2), ∏ j ∈ (Finset.univ.erase a), A j
  let SB : ℝ := ∑ b : Fin (2 * n - k + 2),
      ‖Polynomial.eval ξ (((S b).derivative).map (Int.castRingHom ℝ))‖ / A b
  have hdet' : 1 ≤ c_det * (E * (C0 * δ)) * SA * SB := by
    dsimp [SA, SB, A]
    simpa [mul_assoc] using hdet
  -- product-sum bound
  have hsumA := sum_erase_prod_le n k hk2 hkn H hHmono hHge C hC1 A lab hAnonneg hAub hLab0p hLab1p hLab2
  have hSA0 : SA ≤ cSig * (H ⟨0, by omega⟩) ^ (n + 1 - k) * (H ⟨1, by omega⟩) ^ (n + 2 - k) *
      ∏ j : Fin (k - 2), H ⟨j.val + 2, by omega⟩ := by
    dsimp [SA, cSig]
    exact hsumA
  let T0F : ℝ := (H ⟨0, by omega⟩) ^ (n + 1 - k) * (H ⟨1, by omega⟩) ^ (n + 2 - k) *
      Finset.prod (Finset.univ.filter (fun j : Fin k => 2 ≤ j.val)) H
  have hprodF_eq : (∏ j : Fin (k - 2), H ⟨j.val + 2, by omega⟩) =
      Finset.prod (Finset.univ.filter (fun j : Fin k => 2 ≤ j.val)) H := by
    exact (prod_filter_eq_prod_shift k hk2 H).symm
  have hSA : SA ≤ cSig * T0F := by
    calc
      SA ≤ cSig * (H ⟨0, by omega⟩) ^ (n + 1 - k) * (H ⟨1, by omega⟩) ^ (n + 2 - k) *
          ∏ j : Fin (k - 2), H ⟨j.val + 2, by omega⟩ := hSA0
      _ = cSig * ((H ⟨0, by omega⟩) ^ (n + 1 - k) * (H ⟨1, by omega⟩) ^ (n + 2 - k) *
          ∏ j : Fin (k - 2), H ⟨j.val + 2, by omega⟩) := by ring
      _ = cSig * T0F := by
          rw [hprodF_eq]
  -- f and maximising index
  let f : Fin (2 * n - k + 2) → ℝ := fun b =>
      ‖Polynomial.eval ξ (((S b).derivative).map (Int.castRingHom ℝ))‖ / A b
  have hApos : ∀ b : Fin (2 * n - k + 2), 0 < A b := by
    intro b
    have hge1 : (1 : ℝ) ≤ A b := by
      dsimp [A]
      exact int_poly_supNorm_one_le (S b) (hSne b)
    linarith
  have hfnonneg : ∀ b : Fin (2 * n - k + 2), 0 ≤ f b := by
    intro b
    dsimp [f]
    exact div_nonneg (by positivity : 0 ≤ ‖Polynomial.eval ξ (((S b).derivative).map (Int.castRingHom ℝ))‖) (le_of_lt (hApos b))
  have hnonempty : (Finset.univ : Finset (Fin (2 * n - k + 2))).Nonempty := by
    refine ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  rcases Finset.exists_max_image (Finset.univ : Finset (Fin (2 * n - k + 2))) f hnonempty with
    ⟨b0, hb0mem, hb0max⟩
  have hf0 : SB ≤ (Fintype.card (Fin (2 * n - k + 2)) : ℝ) * f b0 := by
    have hle1 : SB ≤ ∑ b : Fin (2 * n - k + 2), f b := by
      dsimp [SB, f]
      rfl
    have hle2 : (∑ b : Fin (2 * n - k + 2), f b) ≤ (Fintype.card (Fin (2 * n - k + 2)) : ℝ) * f b0 := by
      calc
        (∑ b : Fin (2 * n - k + 2), f b) ≤ ∑ b : Fin (2 * n - k + 2), f b0 := by
          exact Finset.sum_le_sum (fun b hb => hb0max b hb)
        _ = (Fintype.card (Fin (2 * n - k + 2)) : ℝ) * f b0 := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    exact le_trans hle1 hle2
  -- 1 ≤ c2 * δ * T0F * f b0
  have hc2pos : 0 < c2 := hc2pos0
  have hmain1 : 1 ≤ c2 * δ * T0F * f b0 := by
    have hT0F0 : 0 ≤ T0F := by
      dsimp [T0F]
      have hH0p : 0 ≤ H ⟨0, by omega⟩ := by have h := hHge ⟨0, by omega⟩; linarith
      have hH1p : 0 ≤ H ⟨1, by omega⟩ := by have h := hHge ⟨1, by omega⟩; linarith
      have hprod : 0 ≤ ∏ j ∈ (Finset.univ.filter (fun j : Fin k => 2 ≤ j.val)), H j := by
        exact Finset.prod_nonneg (fun j hj => H_nonneg_of_ge1 hHge j)
      exact mul_nonneg (mul_nonneg (pow_nonneg hH0p _) (pow_nonneg hH1p _)) hprod
    have hSA0' : 0 ≤ SA := by
      dsimp [SA]
      exact Finset.sum_nonneg (fun a ha =>
        Finset.prod_nonneg (fun j hj => hAnonneg j))
    have hSB0 : 0 ≤ SB := by
      dsimp [SB]
      exact Finset.sum_nonneg (fun b hb => div_nonneg (by positivity : 0 ≤ ‖Polynomial.eval ξ (((S b).derivative).map (Int.castRingHom ℝ))‖) (le_of_lt (hApos b)))
    have hc0 : 0 ≤ c_det * (E * (C0 * δ)) := by positivity
    have hstep1 : c_det * (E * (C0 * δ)) * SA * SB ≤
        c_det * (E * (C0 * δ)) * (cSig * T0F) * ((Fintype.card (Fin (2 * n - k + 2)) : ℝ) * f b0) := by
      have hcSig0 : 0 ≤ cSig := by
        dsimp [cSig]
        have hC0 : 0 ≤ C := le_trans zero_le_one hC1
        exact mul_nonneg hcardR0 (pow_nonneg hC0 _)
      have hconc : 0 ≤ cSig * T0F := mul_nonneg hcSig0 hT0F0
      have h12 : SA * SB ≤ (cSig * T0F) * ((Fintype.card (Fin (2 * n - k + 2)) : ℝ) * f b0) := by
        exact mul_le_mul hSA hf0 hSB0 hconc
      calc
        c_det * (E * (C0 * δ)) * SA * SB = (c_det * (E * (C0 * δ))) * (SA * SB) := by ring
        _ ≤ (c_det * (E * (C0 * δ))) * ((cSig * T0F) *
            ((Fintype.card (Fin (2 * n - k + 2)) : ℝ) * f b0)) :=
              mul_le_mul_of_nonneg_left h12 hc0
        _ = c_det * (E * (C0 * δ)) * (cSig * T0F) *
            ((Fintype.card (Fin (2 * n - k + 2)) : ℝ) * f b0) := by ring
    have hle2 : c_det * (E * (C0 * δ)) * (cSig * T0F) *
        ((Fintype.card (Fin (2 * n - k + 2)) : ℝ) * f b0) = c2 * δ * T0F * f b0 := by
      dsimp [c2]
      ring
    calc
      1 ≤ c_det * (E * (C0 * δ)) * SA * SB := hdet'
      _ ≤ c_det * (E * (C0 * δ)) * (cSig * T0F) *
          ((Fintype.card (Fin (2 * n - k + 2)) : ℝ) * f b0) := hstep1
      _ = c2 * δ * T0F * f b0 := hle2

  -- (3) positivity of f b0 and degree of S b0
  have hT0Fpos : 0 < T0F := by
    dsimp [T0F]
    have hH0pos : 0 < H ⟨0, by omega⟩ := lt_of_lt_of_le zero_lt_one (hHge ⟨0, by omega⟩)
    have hH1pos : 0 < H ⟨1, by omega⟩ := lt_of_lt_of_le zero_lt_one (hHge ⟨1, by omega⟩)
    have hpf : 0 < ∏ j ∈ (Finset.univ.filter (fun j : Fin k => 2 ≤ j.val)), H j := by
      exact Finset.prod_pos (fun j hj => lt_of_lt_of_le zero_lt_one (hHge j))
    exact mul_pos (mul_pos (pow_pos hH0pos (n + 1 - k)) (pow_pos hH1pos (n + 2 - k))) hpf
  have hc2δT0Fpos : 0 < c2 * δ * T0F := by
    exact mul_pos (mul_pos hc2pos hδ) hT0Fpos
  have hmain2 : 0 < f b0 := by
    by_contra hf
    have hle0 : f b0 ≤ 0 := le_of_not_gt hf
    have hnonneg : 0 ≤ c2 * δ * T0F := le_of_lt hc2δT0Fpos
    have hnonpos : c2 * δ * T0F * f b0 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hnonneg hle0
    linarith
  let d0 : ℝ := ‖Polynomial.eval ξ (((S b0).derivative).map (Int.castRingHom ℝ))‖
  have hd0pos : 0 < d0 := by
    have hfpos : 0 < d0 / A b0 := by
      simpa [f, d0] using hmain2
    have hne : d0 ≠ 0 := by
      intro hz
      have hfz : d0 / A b0 = 0 := by
        rw [hz]
        simp
      linarith
    exact lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
  have hderiv_ne : (S b0).derivative ≠ 0 := by
    intro hd
    have hd0zero : d0 = 0 := by
      dsimp [d0]
      simp [hd]
    exact (ne_of_gt hd0pos) hd0zero
  have hdegS_b0 : 1 ≤ (S b0).natDegree := by
    by_contra hdeg
    have hd0nat : (S b0).natDegree = 0 := by omega
    have hderiv0 : (S b0).derivative = 0 := by
      have hconst : S b0 = Polynomial.C ((S b0).coeff 0) :=
        Polynomial.eq_C_of_natDegree_eq_zero hd0nat
      rw [hconst]
      simp
    exact hderiv_ne hderiv0
  -- (4) root of S b0 close to ξ
  rcases root_close_int (S b0) ξ hdegS_b0 with ⟨α, hαroot, hαclose⟩
  have hclose2 : ‖(ξ : ℂ) - α‖ * d0 ≤ N0 * (E * (C0 * δ)) := by
    calc
      ‖(ξ : ℂ) - α‖ * d0 ≤ (S b0).natDegree * ‖Polynomial.eval ξ ((S b0).map (Int.castRingHom ℝ))‖ := by
          simpa [d0] using hαclose
      _ ≤ N0 * ‖Polynomial.eval ξ ((S b0).map (Int.castRingHom ℝ))‖ := by
          have hN0deg : ((S b0).natDegree : ℝ) ≤ (N0 : ℝ) := by
            have hh := hdegS' b0
            exact_mod_cast hh
          exact mul_le_mul_of_nonneg_right hN0deg (norm_nonneg _)
      _ ≤ N0 * (E * (C0 * δ)) := by
          exact mul_le_mul_of_nonneg_left (hevalS b0) (le_of_lt (by positivity : 0 < (N0 : ℝ)))
  -- bound A0 / d0 from hmain1
  let A0 : ℝ := A b0
  have hA0pos : 0 < A0 := by
    dsimp [A0]
    exact hApos b0
  have hmainA0 : A0 / d0 ≤ c2 * δ * T0F := by
    have hypos : 0 < d0 / A0 := by
      dsimp [f, d0, A0]
      exact hmain2
    have h1' : 1 ≤ c2 * δ * T0F * (d0 / A0) := by
      dsimp [f, d0, A0]
      exact hmain1
    -- multiply h1' by (d0/A0)⁻¹
    have hyinv : 1 ≤ c2 * δ * T0F * (d0 / A0) := h1'
    have hmul := mul_le_mul_of_nonneg_right hyinv (le_of_lt (inv_pos.mpr hypos))
    -- (1) * (d0/A0)⁻¹ ≤ (c2δT0F*(d0/A0))*(d0/A0)⁻¹ ; simplify both sides
    have hleft : (1 : ℝ) * (d0 / A0)⁻¹ = A0 / d0 := by
      field_simp [ne_of_gt hd0pos, ne_of_gt hA0pos]
    have hright : (c2 * δ * T0F * (d0 / A0)) * (d0 / A0)⁻¹ = c2 * δ * T0F := by
      field_simp [ne_of_gt hd0pos, ne_of_gt hA0pos]
    rwa [hleft, hright] at hmul
  have hclose2' : ‖(ξ : ℂ) - α‖ ≤ (N0 * (E * (C0 * δ))) / d0 := by
    exact (le_div_iff₀ hd0pos).mpr hclose2
  have h1d : (1 : ℝ) / d0 ≤ (c2 * δ * T0F) / A0 := by
    have hmul := mul_le_mul_of_nonneg_right hmainA0 (le_of_lt (inv_pos.mpr hA0pos))
    have hleft : (A0 / d0) * (A0)⁻¹ = (1 : ℝ) / d0 := by
      field_simp [ne_of_gt hA0pos, ne_of_gt hd0pos]
    have hright : (c2 * δ * T0F) * (A0)⁻¹ = (c2 * δ * T0F) / A0 := by
      rw [div_eq_mul_inv]
    rwa [hleft, hright] at hmul
  have hclose3 : ‖(ξ : ℂ) - α‖ ≤ (N0 * (E * (C0 * δ)) * (c2 * δ * T0F)) / A0 := by
    calc
      ‖(ξ : ℂ) - α‖ ≤ (N0 * (E * (C0 * δ))) / d0 := hclose2'
      _ = (N0 * (E * (C0 * δ))) * (1 / d0) := by ring
      _ ≤ (N0 * (E * (C0 * δ))) * ((c2 * δ * T0F) / A0) := by
          exact mul_le_mul_of_nonneg_left h1d
            (le_of_lt (by positivity : 0 < (N0 : ℝ) * (E * (C0 * δ))))
      _ = (N0 * (E * (C0 * δ)) * (c2 * δ * T0F)) / A0 := by ring
  let m : Fin k := lab b0
  -- S b0 = X^t * Q m
  have hSb0 : S b0 = Polynomial.X ^ (exp b0) * Q m := by
    dsimp [m]
    exact hSdef b0
  have hAm : A0 = ((Q m).map (Int.castRingHom ℝ)).supNorm := by
    dsimp [A0, m]
    exact hAeqQ b0
  have hHm_le_A0C : H m ≤ C * A0 := by
    rw [hAm]
    dsimp [H, m]
    exact hQloC (lab b0)
  have hHmpos : 0 < H m := by
    have h1 : (1 : ℝ) ≤ H m := hHge m
    linarith
  have hA0inv_le : A0⁻¹ ≤ C * (H m)⁻¹ := by
    have hCA0pos : 0 < C * A0 := mul_pos hCpos hA0pos
    have h1 : (C * A0)⁻¹ ≤ (H m)⁻¹ := (inv_le_inv₀ hCA0pos hHmpos).2 hHm_le_A0C
    calc
      A0⁻¹ = C * (C * A0)⁻¹ := by field_simp [ne_of_gt hCpos]
      _ ≤ C * (H m)⁻¹ := by exact mul_le_mul_of_nonneg_left h1 (le_of_lt hCpos)
  have hclose4 : ‖(ξ : ℂ) - α‖ ≤
      (N0 * (E * (C0 * δ)) * (c2 * δ * T0F) * C) * (H m)⁻¹ := by
    have h1 := hclose3
    have h2 : (N0 * (E * (C0 * δ)) * (c2 * δ * T0F)) / A0 ≤
        (N0 * (E * (C0 * δ)) * (c2 * δ * T0F) * C) * (H m)⁻¹ := by
      -- 1/A0 ≤ C/Hm from hA0inv_le and positive multiplier
      have hposM : 0 ≤ N0 * (E * (C0 * δ)) * (c2 * δ * T0F) := by positivity
      calc
        (N0 * (E * (C0 * δ)) * (c2 * δ * T0F)) / A0
            = (N0 * (E * (C0 * δ)) * (c2 * δ * T0F)) * A0⁻¹ := by rw [div_eq_mul_inv]
        _ ≤ (N0 * (E * (C0 * δ)) * (c2 * δ * T0F)) * (C * (H m)⁻¹) := by
              exact mul_le_mul_of_nonneg_left hA0inv_le hposM
        _ = (N0 * (E * (C0 * δ)) * (c2 * δ * T0F) * C) * (H m)⁻¹ := by ring
    exact le_trans h1 h2

  -- (5) height bound and final conclusion
  -- proximity in the target form
  have hprox : ‖(ξ : ℂ) - α‖ ≤ cFin * δ ^ 2 * (H ⟨0, by omega⟩) ^ (n + 1 - k) *
      (H ⟨1, by omega⟩) ^ (n + 2 - k) *
      (Finset.prod (Finset.univ.filter (fun j : Fin k => 2 ≤ j.val)) H) * (H m)⁻¹ := by
    have h1' : ‖(ξ : ℂ) - α‖ ≤ cProx * δ ^ 2 * T0F * (H m)⁻¹ := by
      calc
        ‖(ξ : ℂ) - α‖ ≤ (N0 * (E * (C0 * δ)) * (c2 * δ * T0F) * C) * (H m)⁻¹ := hclose4
        _ = cProx * δ ^ 2 * T0F * (H m)⁻¹ := by
            dsimp [cProx, c2]
            ring_nf
    have hT0F : T0F = (H ⟨0, by omega⟩) ^ (n + 1 - k) * (H ⟨1, by omega⟩) ^ (n + 2 - k) *
        (Finset.prod (Finset.univ.filter (fun j : Fin k => 2 ≤ j.val)) H) := rfl
    have hstep : cProx * δ ^ 2 * T0F * (H m)⁻¹ ≤
        cFin * δ ^ 2 * T0F * (H m)⁻¹ := by
      have h1 := mul_le_mul_of_nonneg_right hcFin_ge_prox (by positivity : 0 ≤ δ ^ 2)
      have h2 := mul_le_mul_of_nonneg_right h1 (by positivity : 0 ≤ T0F * (H m)⁻¹)
      simpa [mul_assoc] using h2
    calc
      ‖(ξ : ℂ) - α‖ ≤ cProx * δ ^ 2 * T0F * (H m)⁻¹ := h1'
      _ ≤ cFin * δ ^ 2 * T0F * (H m)⁻¹ := hstep
      _ = cFin * δ ^ 2 * (H ⟨0, by omega⟩) ^ (n + 1 - k) * (H ⟨1, by omega⟩) ^ (n + 2 - k) *
          (Finset.prod (Finset.univ.filter (fun j : Fin k => 2 ≤ j.val)) H) * (H m)⁻¹ := by
          rw [hT0F]
          ring_nf
  -- height bound
  by_cases hα0 : α = 0
  · -- α = 0 : witness α' := 0, use the polynomial X
    have hXne : (Polynomial.X : Polynomial ℤ) ≠ 0 := by simp
    have hdegX : (Polynomial.X : Polynomial ℤ).natDegree ≤ n := by
      rw [Polynomial.natDegree_X]
      omega
    have hrootX : Polynomial.IsRoot ((Polynomial.X : Polynomial ℤ).map (Int.castRingHom ℂ)) (0 : ℂ) := by
      rw [Polynomial.IsRoot.def]
      simp
    rcases hc_rootmain (Polynomial.X : Polynomial ℤ) (0 : ℂ) hXne hdegX hrootX with ⟨hAlg0, hdegmin0, hgt0⟩
    have hsupX : ((((Polynomial.X : Polynomial ℤ).map (Int.castRingHom ℝ))).supNorm) = (1 : ℝ) := by
      have hxm : ((Polynomial.X : Polynomial ℤ).map (Int.castRingHom ℝ)) = (Polynomial.X : Polynomial ℝ) := by
        simp
      rw [hxm]
      exact Polynomial.supNorm_X
    have hgtX : ((((let p := minpoly ℚ (0 : ℂ);
            let D := Multiset.lcm (Multiset.map (fun i ↦ (p.coeff i).den) p.support.val);
            Finset.sup p.support (fun i ↦ (D * p.coeff i).num.natAbs) : ℕ) : ℝ))) ≤ c_root := by
      calc
        ((((let p := minpoly ℚ (0 : ℂ);
            let D := Multiset.lcm (Multiset.map (fun i ↦ (p.coeff i).den) p.support.val);
            Finset.sup p.support (fun i ↦ (D * p.coeff i).num.natAbs) : ℕ) : ℝ)))
            ≤ c_root * ((((Polynomial.X : Polynomial ℤ).map (Int.castRingHom ℝ))).supNorm) := hgt0
        _ = c_root * 1 := by rw [hsupX]
        _ = c_root := by ring
    -- height of 0 ≤ c_root * C * H m ≤ cFin * H m
    have hHmge1 : (1 : ℝ) ≤ H m := hHge m
    have hC1ge : (1 : ℝ) ≤ C := hC1
    have hCHge : (1 : ℝ) ≤ C * H m := one_le_mul_of_one_le_of_one_le hC1ge hHmge1
    have hrootC_le : c_root ≤ c_root * (C * H m) := by
      have hcroot0 : 0 ≤ c_root := le_of_lt hc_rootpos
      simpa using (mul_le_mul_of_nonneg_left hCHge hcroot0)
    have hgtFin0 : ((((let p := minpoly ℚ (0 : ℂ);
            let D := Multiset.lcm (Multiset.map (fun i ↦ (p.coeff i).den) p.support.val);
            Finset.sup p.support (fun i ↦ (D * p.coeff i).num.natAbs) : ℕ) : ℝ))) ≤
        cFin * H m := by
      calc
        ((((let p := minpoly ℚ (0 : ℂ);
            let D := Multiset.lcm (Multiset.map (fun i ↦ (p.coeff i).den) p.support.val);
            Finset.sup p.support (fun i ↦ (D * p.coeff i).num.natAbs) : ℕ) : ℝ)))
            ≤ c_root := hgtX
        _ ≤ c_root * (C * H m) := hrootC_le
        _ = (c_root * C) * H m := by ring
        _ ≤ cFin * H m := by
            have hcc : c_root * C ≤ cFin := by
              dsimp [cFin]
              have hp0 : 0 ≤ cProx := le_of_lt hcProxpos
              linarith
            exact mul_le_mul_of_nonneg_right hcc (le_of_lt hHmpos)
    -- the witness: m, 0 : ℂ
    refine ⟨m, (0 : ℂ), hAlg0, hdegmin0, ?_, ?_⟩
    · -- height ≤ cFin * supNorm((P m).map)
      -- H m = ((P m).mapℝ).supNorm
      change ((((let p := minpoly ℚ (0 : ℂ);
            let D := Multiset.lcm (Multiset.map (fun i ↦ (p.coeff i).den) p.support.val);
            Finset.sup p.support (fun i ↦ (D * p.coeff i).num.natAbs) : ℕ) : ℝ))) ≤
        cFin * ((P m).map (Int.castRingHom ℝ)).supNorm
      have hHm : H m = ((P m).map (Int.castRingHom ℝ)).supNorm := rfl
      rw [← hHm]
      exact hgtFin0
    · -- proximity for α' = 0
      have hpx : ‖(ξ : ℂ) - (0 : ℂ)‖ ≤
          cFin * δ ^ 2 * (H ⟨0, by omega⟩) ^ (n + 1 - k) * (H ⟨1, by omega⟩) ^ (n + 2 - k) *
          (Finset.prod (Finset.univ.filter (fun j : Fin k => 2 ≤ j.val)) H) * (H m)⁻¹ := by
        simpa [hα0] using hprox
      simpa [H, m] using hpx
  · -- α ≠ 0 : α is a root of Q m
    have hαne0 : α ≠ 0 := hα0
    have hpow_ne : α ^ (exp b0) ≠ 0 := pow_ne_zero (exp b0) hαne0
    have heq0 : Polynomial.eval α (((S b0).map (Int.castRingHom ℂ))) = 0 :=
      (Polynomial.IsRoot.def).mp hαroot
    have hSb0C : (S b0).map (Int.castRingHom ℂ) =
        ((Polynomial.X ^ (exp b0) * Q m).map (Int.castRingHom ℂ)) := by
      rw [hSb0]
    have hrootQ : Polynomial.IsRoot ((Q m).map (Int.castRingHom ℂ)) α := by
      rw [Polynomial.IsRoot.def]
      have heval : Polynomial.eval α (((Polynomial.X ^ (exp b0) * Q m).map (Int.castRingHom ℂ))) =
          α ^ (exp b0) * Polynomial.eval α ((Q m).map (Int.castRingHom ℂ)) := by
        rw [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X]
        rw [Polynomial.eval_mul, Polynomial.eval_pow]
        simp
      have hzero : α ^ (exp b0) * Polynomial.eval α ((Q m).map (Int.castRingHom ℂ)) = 0 := by
        rw [← heval, ← hSb0C]
        exact heq0
      exact mul_eq_zero.mp hzero |>.resolve_left hpow_ne
    rcases hc_rootmain (Q m) α (hQne m) (hQdeg m) hrootQ with ⟨hAlgα, hdegminα, hgtα⟩
    have hgtα1 : ((((let p := minpoly ℚ α;
            let D := Multiset.lcm (Multiset.map (fun i ↦ (p.coeff i).den) p.support.val);
            Finset.sup p.support (fun i ↦ (D * p.coeff i).num.natAbs) : ℕ) : ℝ))) ≤
        c_root * (C0 * H m) := by
      calc
        ((((let p := minpoly ℚ α;
            let D := Multiset.lcm (Multiset.map (fun i ↦ (p.coeff i).den) p.support.val);
            Finset.sup p.support (fun i ↦ (D * p.coeff i).num.natAbs) : ℕ) : ℝ)))
            ≤ c_root * (((Q m).map (Int.castRingHom ℝ)).supNorm) := hgtα
        _ ≤ c_root * (C0 * H m) := by
            have hup : ((Q m).map (Int.castRingHom ℝ)).supNorm ≤ C0 * H m := by
              dsimp [H]
              exact hQup m
            exact mul_le_mul_of_nonneg_left hup (le_of_lt hc_rootpos)
    have hgtFin1 : ((((let p := minpoly ℚ α;
            let D := Multiset.lcm (Multiset.map (fun i ↦ (p.coeff i).den) p.support.val);
            Finset.sup p.support (fun i ↦ (D * p.coeff i).num.natAbs) : ℕ) : ℝ))) ≤
        cFin * H m := by
      calc
        ((((let p := minpoly ℚ α;
            let D := Multiset.lcm (Multiset.map (fun i ↦ (p.coeff i).den) p.support.val);
            Finset.sup p.support (fun i ↦ (D * p.coeff i).num.natAbs) : ℕ) : ℝ)))
            ≤ c_root * (C0 * H m) := hgtα1
        _ = (c_root * C0) * H m := by ring
        _ ≤ (c_root * C) * H m := by
            have hC0C : C0 ≤ C := hC0leC
            have hHm0 : 0 ≤ H m := le_of_lt hHmpos
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hC0C (le_of_lt hc_rootpos)) hHm0
        _ ≤ cFin * H m := by
            have hcc : c_root * C ≤ cFin := by
              dsimp [cFin]
              have hp0 : 0 ≤ cProx := le_of_lt hcProxpos
              linarith
            exact mul_le_mul_of_nonneg_right hcc (le_of_lt hHmpos)
    refine ⟨m, α, hAlgα, hdegminα, ?_, ?_⟩
    · change ((((let p := minpoly ℚ α;
            let D := Multiset.lcm (Multiset.map (fun i ↦ (p.coeff i).den) p.support.val);
            Finset.sup p.support (fun i ↦ (D * p.coeff i).num.natAbs) : ℕ) : ℝ))) ≤
          cFin * ((P m).map (Int.castRingHom ℝ)).supNorm
      have hHm : H m = ((P m).map (Int.castRingHom ℝ)).supNorm := rfl
      rw [← hHm]
      exact hgtFin1
    · simpa [H, m] using hprox


/-- Proposition 5.1 of A. Poels, Annals of Math 201 (2025), arXiv:2405.08341, in the
version whose coprimality hypothesis is taken on the REAL maps of the first two
polynomials: `IsCoprime ((P 0).map RR) ((P 1).map RR)` over RR[X] (i.e. gcd 1 over
RR[X], equivalently no common complex root) instead of Bezout over ZZ[X].  This is
the form actually needed downstream: families built by Lemma 4.1-type constructions
only provide gcd-1 over QQ (hence over RR) and generally NOT a ZZ[X] Bezout
identity (ZZ[X] is not Bezout; e.g. Q1 = 7X-4, P = 67X-38 have QQ-gcd 1 but no
ZZ-Bezout identity).  Conclusion identical to commons poels_prop51: from k in
[2,n+1], integer P_1..P_k of degree <= n, RR-linearly independent, first two
RR-coprime, monotone RR-supNorms, |P_i(xi)| <= delta, one obtains m and an
algebraic alpha of degree <= n with naive height <= c*||P_m|| and
|xi-alpha| <= c*delta^2*||P_1||^(n+1-k)*||P_2||^(n+2-k)*(prod over j>=2 of
||P_j||)*||P_m||^(-1), c depending on n and xi only. -/
theorem poels_prop51_real (n : ℕ) (hn : 2 ≤ n) (ξ : ℝ) :
    ∃ c : ℝ, 0 < c ∧
    ∀ (k : ℕ) (hk2 : 2 ≤ k) (hkn : k ≤ n + 1)
      (P : Fin k → Polynomial ℤ) (δ : ℝ) (hδ : 0 < δ),
      (∀ i : Fin k, (P i).natDegree ≤ n) →
      LinearIndependent ℝ (fun i : Fin k => (P i).map (Int.castRingHom ℝ)) →
      IsCoprime (((P ⟨0, lt_of_lt_of_le (by norm_num) hk2⟩).map (Int.castRingHom ℝ)))
        (((P ⟨1, lt_of_lt_of_le (by norm_num) hk2⟩).map (Int.castRingHom ℝ))) →
      Monotone (fun i : Fin k => ((P i).map (Int.castRingHom ℝ)).supNorm) →
      (∀ i : Fin k,
        ‖Polynomial.eval ξ ((P i).map (Int.castRingHom ℝ))‖ ≤ δ) →
      ∃ m : Fin k, ∃ α : ℂ,
        IsAlgebraic ℚ α ∧
        Polynomial.natDegree (minpoly ℚ α) ≤ n ∧
        ((((let p := minpoly ℚ α;
            let D := Multiset.lcm (Multiset.map (fun i ↦ (p.coeff i).den) p.support.val);
            Finset.sup p.support (fun i ↦ (D * p.coeff i).num.natAbs) : ℕ) : ℝ)) ≤
          c * ((P m).map (Int.castRingHom ℝ)).supNorm) ∧
        ‖(ξ : ℂ) - α‖ ≤
          c * δ ^ 2 *
            (((P ⟨0, lt_of_lt_of_le (by norm_num) hk2⟩).map (Int.castRingHom ℝ)).supNorm) ^ (n + 1 - k) *
            (((P ⟨1, lt_of_lt_of_le (by norm_num) hk2⟩).map (Int.castRingHom ℝ)).supNorm) ^ (n + 2 - k) *
            (Finset.prod (Finset.univ.filter (fun j : Fin k => 2 ≤ j.val))
              (fun j : Fin k => (((P j).map (Int.castRingHom ℝ)).supNorm))) *
            (((P m).map (Int.castRingHom ℝ)).supNorm)⁻¹ := by
  let ks : Finset ℕ := Finset.Icc 2 (n + 1)
  have hks_ne : ks.Nonempty := by
    refine ⟨2, ?_⟩
    rw [Finset.mem_Icc]
    omega
  let cfun : ℕ → ℝ := fun k =>
    if hk : k ∈ ks then
      Classical.choose (p51_aux_real n hn ξ k (Finset.mem_Icc.mp hk).1 (Finset.mem_Icc.mp hk).2)
    else 1
  let c : ℝ := ks.sup' hks_ne cfun
  refine ⟨c, ?_, ?_⟩
  · -- 0 < c
    have h2mem : (2 : ℕ) ∈ ks := by
      rw [Finset.mem_Icc]
      omega
    have hc2 : cfun 2 = Classical.choose (p51_aux_real n hn ξ 2 (Finset.mem_Icc.mp h2mem).1 (Finset.mem_Icc.mp h2mem).2) := by
      dsimp [cfun]
      rw [dif_pos h2mem]
    have hs := Classical.choose_spec (p51_aux_real n hn ξ 2 (Finset.mem_Icc.mp h2mem).1 (Finset.mem_Icc.mp h2mem).2)
    have hpos : 0 < cfun 2 := by
      rw [hc2]
      exact hs.1
    have hle2 : cfun 2 ≤ c := by
      dsimp [c]
      exact Finset.le_sup' cfun h2mem
    linarith
  · -- main universal
    intro k hk2 hkn P δ hδ hdeg hlin hcop hmono hsmall
    have hk : k ∈ ks := by
      rw [Finset.mem_Icc]
      exact ⟨hk2, hkn⟩
    have hcfun : cfun k = Classical.choose
        (p51_aux_real n hn ξ k (Finset.mem_Icc.mp hk).1 (Finset.mem_Icc.mp hk).2) := by
      dsimp [cfun]
      rw [dif_pos hk]
    have hspec := Classical.choose_spec
      (p51_aux_real n hn ξ k (Finset.mem_Icc.mp hk).1 (Finset.mem_Icc.mp hk).2)
    have hmain := hspec.2 P δ hδ hdeg hlin hcop hmono hsmall
    rcases hmain with ⟨m, α, hα⟩
    have hck : cfun k ≤ c := by
      dsimp [c]
      exact Finset.le_sup' cfun hk
    refine ⟨m, α, ?_⟩
    rcases hα with ⟨hαalg, hdegα, hh, hd⟩
    refine ⟨hαalg, hdegα, ?_, ?_⟩
    · have hh' : ((((let p := minpoly ℚ α;
          let D := Multiset.lcm (Multiset.map (fun i ↦ (p.coeff i).den) p.support.val);
          Finset.sup p.support (fun i ↦ (D * p.coeff i).num.natAbs) : ℕ) : ℝ)) ≤
          cfun k * ((P m).map (Int.castRingHom ℝ)).supNorm) := by
          rw [← hcfun] at hh
          exact hh
      have hmnonneg : 0 ≤ ((P m).map (Int.castRingHom ℝ)).supNorm := by
        exact supNorm_nonneg _
      have hmult : cfun k * ((P m).map (Int.castRingHom ℝ)).supNorm ≤
          c * ((P m).map (Int.castRingHom ℝ)).supNorm := by
        exact mul_le_mul_of_nonneg_right hck hmnonneg
      exact le_trans hh' hmult
    · have hd' : ‖(ξ : ℂ) - α‖ ≤
          cfun k * δ ^ 2 *
            (((P ⟨0, lt_of_lt_of_le (by norm_num) hk2⟩).map (Int.castRingHom ℝ)).supNorm) ^ (n + 1 - k) *
            (((P ⟨1, lt_of_lt_of_le (by norm_num) hk2⟩).map (Int.castRingHom ℝ)).supNorm) ^ (n + 2 - k) *
            (Finset.prod (Finset.univ.filter (fun j : Fin k => 2 ≤ j.val))
              (fun j : Fin k => (((P j).map (Int.castRingHom ℝ)).supNorm))) *
            (((P m).map (Int.castRingHom ℝ)).supNorm)⁻¹ := by
          rw [← hcfun] at hd
          exact hd
      have hA0n : 0 ≤ (((P ⟨0, lt_of_lt_of_le (by norm_num) hk2⟩).map (Int.castRingHom ℝ)).supNorm) ^ (n + 1 - k) := by
        exact pow_nonneg (supNorm_nonneg _) _
      have hA1n : 0 ≤ (((P ⟨1, lt_of_lt_of_le (by norm_num) hk2⟩).map (Int.castRingHom ℝ)).supNorm) ^ (n + 2 - k) := by
        exact pow_nonneg (supNorm_nonneg _) _
      have hCPn : 0 ≤ Finset.prod (Finset.univ.filter (fun j : Fin k => 2 ≤ j.val))
              (fun j : Fin k => (((P j).map (Int.castRingHom ℝ)).supNorm)) := by
        exact Finset.prod_nonneg (by intro x hx; exact supNorm_nonneg _)
      have hIn : 0 ≤ (((P m).map (Int.castRingHom ℝ)).supNorm)⁻¹ := by
        exact inv_nonneg.mpr (supNorm_nonneg _)
      have hX0 : 0 ≤ δ ^ 2 *
            (((P ⟨0, lt_of_lt_of_le (by norm_num) hk2⟩).map (Int.castRingHom ℝ)).supNorm) ^ (n + 1 - k) *
            (((P ⟨1, lt_of_lt_of_le (by norm_num) hk2⟩).map (Int.castRingHom ℝ)).supNorm) ^ (n + 2 - k) *
            (Finset.prod (Finset.univ.filter (fun j : Fin k => 2 ≤ j.val))
              (fun j : Fin k => (((P j).map (Int.castRingHom ℝ)).supNorm))) *
            (((P m).map (Int.castRingHom ℝ)).supNorm)⁻¹ := by
        exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg δ) hA0n) hA1n) hCPn) hIn
      calc
        ‖(ξ : ℂ) - α‖ ≤
            cfun k * δ ^ 2 *
              (((P ⟨0, lt_of_lt_of_le (by norm_num) hk2⟩).map (Int.castRingHom ℝ)).supNorm) ^ (n + 1 - k) *
              (((P ⟨1, lt_of_lt_of_le (by norm_num) hk2⟩).map (Int.castRingHom ℝ)).supNorm) ^ (n + 2 - k) *
              (Finset.prod (Finset.univ.filter (fun j : Fin k => 2 ≤ j.val))
                (fun j : Fin k => (((P j).map (Int.castRingHom ℝ)).supNorm))) *
              (((P m).map (Int.castRingHom ℝ)).supNorm)⁻¹ := hd'
        _ = cfun k * (δ ^ 2 *
              (((P ⟨0, lt_of_lt_of_le (by norm_num) hk2⟩).map (Int.castRingHom ℝ)).supNorm) ^ (n + 1 - k) *
              (((P ⟨1, lt_of_lt_of_le (by norm_num) hk2⟩).map (Int.castRingHom ℝ)).supNorm) ^ (n + 2 - k) *
              (Finset.prod (Finset.univ.filter (fun j : Fin k => 2 ≤ j.val))
                (fun j : Fin k => (((P j).map (Int.castRingHom ℝ)).supNorm))) *
              (((P m).map (Int.castRingHom ℝ)).supNorm)⁻¹) := by ring
        _ ≤ c * (δ ^ 2 *
              (((P ⟨0, lt_of_lt_of_le (by norm_num) hk2⟩).map (Int.castRingHom ℝ)).supNorm) ^ (n + 1 - k) *
              (((P ⟨1, lt_of_lt_of_le (by norm_num) hk2⟩).map (Int.castRingHom ℝ)).supNorm) ^ (n + 2 - k) *
              (Finset.prod (Finset.univ.filter (fun j : Fin k => 2 ≤ j.val))
                (fun j : Fin k => (((P j).map (Int.castRingHom ℝ)).supNorm))) *
              (((P m).map (Int.castRingHom ℝ)).supNorm)⁻¹) := by
          exact mul_le_mul_of_nonneg_right hck hX0
        _ = c * δ ^ 2 *
              (((P ⟨0, lt_of_lt_of_le (by norm_num) hk2⟩).map (Int.castRingHom ℝ)).supNorm) ^ (n + 1 - k) *
              (((P ⟨1, lt_of_lt_of_le (by norm_num) hk2⟩).map (Int.castRingHom ℝ)).supNorm) ^ (n + 2 - k) *
              (Finset.prod (Finset.univ.filter (fun j : Fin k => 2 ≤ j.val))
                (fun j : Fin k => (((P j).map (Int.castRingHom ℝ)).supNorm))) *
              (((P m).map (Int.castRingHom ℝ)).supNorm)⁻¹ := by ring

end
end Commons.NumberTheory.DiophantineApproximation.BoundedDegree
