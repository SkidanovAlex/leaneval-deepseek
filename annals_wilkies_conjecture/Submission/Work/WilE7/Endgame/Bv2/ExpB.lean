/-
  Area E7 / the `CoreLT_succ` endgame, node **E2S** (module `Work.WilE7.Endgame.Bv2.ExpB`).

  The elementary helpers and the *bounding toolkit* of the `cellRefine_of_nodesBv2` assembly:

  * `nullDimLT_of_lt`: a set in `ℝ^N` is `K`-null-dimensional once `K > N`;
  * `ExpB`: the class of functions `ℕ → ℕ → ℕ` of `(D, k)` bounded by `M * (1 + D + k) ^ N`, with
    closure under `+`, `*`, multiplication by a constant, evaluation of a polynomial in `D`, and
    evaluation of a (2- or 3-variable) `MvPolynomial` at arguments which are themselves `ExpB`
    functions;
  * `exists_mvpoly3_le`: the consumer, an `ExpB` function is dominated by a three-variable
    `MvPolynomial (Fin 3) ℕ` evaluated at `![D, k, l]` (`l` unused).
-/
import Mathlib
import Submission.Work.WilE7.MainDesignDefs
import Submission.Work.WilE7.poly_dominate
import Submission.Work.WilE7.poly_dominate3

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilE7.Endgame.Bv2

/-! ## 0. Elementary helpers -/

/-- A set in `ℝ^N` is `K`-null-dimensional as soon as `K > N` (no embedding `Fin K ↪ Fin N`
exists). -/
theorem nullDimLT_of_lt {N K : ℕ} (h : N < K)
    (X : Set (Fin N → ℝ)) : Work.WilE7.MainDesign.NullDimLT X K := by
  cases K with
  | zero => omega
  | succ K' =>
      intro e
      exact absurd (Fintype.card_le_of_embedding e) (by simp; omega)

/-! ## 1. The bounding toolkit -/

/-- The class of functions of `(D,k)` bounded by `M * (1 + D + k) ^ N`. -/
def ExpB (L : ℕ → ℕ → ℕ) : Prop := ∃ M N : ℕ, ∀ D k, L D k ≤ M * (1 + D + k) ^ N

theorem expB_of_le {L L' : ℕ → ℕ → ℕ} (h : ExpB L') (hle : ∀ D k, L D k ≤ L' D k) : ExpB L :=
  ⟨h.choose, h.choose_spec.choose,
    fun D k => le_trans (hle D k) (h.choose_spec.choose_spec D k)⟩

theorem expB_const (C : ℕ) : ExpB (fun _ _ => C) :=
  ⟨C, 0, fun D k => by simp⟩

theorem expB_const_mul {L : ℕ → ℕ → ℕ} (h : ExpB L) (c : ℕ) :
    ExpB (fun D k => c * L D k) := by
  obtain ⟨M, N, hM⟩ := h
  refine ⟨c * M, N, fun D k => ?_⟩
  calc c * L D k ≤ c * (M * (1 + D + k) ^ N) := Nat.mul_le_mul_left c (hM D k)
    _ = c * M * (1 + D + k) ^ N := by ring

theorem expB_add {L L' : ℕ → ℕ → ℕ} (h : ExpB L) (h' : ExpB L') :
    ExpB (fun D k => L D k + L' D k) := by
  obtain ⟨M, N, hM⟩ := h
  obtain ⟨M', N', hM'⟩ := h'
  refine ⟨M + M', max N N', fun D k => ?_⟩
  have hx : 0 < 1 + D + k := by positivity
  have hN : (1 + D + k) ^ N ≤ (1 + D + k) ^ max N N' :=
    Nat.pow_le_pow_right hx (le_max_left _ _)
  have hN' : (1 + D + k) ^ N' ≤ (1 + D + k) ^ max N N' :=
    Nat.pow_le_pow_right hx (le_max_right _ _)
  have hA : L D k ≤ M * (1 + D + k) ^ max N N' := le_trans (hM D k) (Nat.mul_le_mul_left M hN)
  have hB : L' D k ≤ M' * (1 + D + k) ^ max N N' :=
    le_trans (hM' D k) (Nat.mul_le_mul_left M' hN')
  have hsum : M * (1 + D + k) ^ max N N' + M' * (1 + D + k) ^ max N N'
      = (M + M') * (1 + D + k) ^ max N N' := by ring
  exact le_trans (Nat.add_le_add hA hB) (le_of_eq hsum)

theorem expB_mul {L L' : ℕ → ℕ → ℕ} (h : ExpB L) (h' : ExpB L') :
    ExpB (fun D k => L D k * L' D k) := by
  obtain ⟨M, N, hM⟩ := h
  obtain ⟨M', N', hM'⟩ := h'
  refine ⟨M * M', 2 * max N N', fun D k => ?_⟩
  have hx : 0 < 1 + D + k := by positivity
  have hN : (1 + D + k) ^ N ≤ (1 + D + k) ^ max N N' :=
    Nat.pow_le_pow_right hx (le_max_left _ _)
  have hN' : (1 + D + k) ^ N' ≤ (1 + D + k) ^ max N N' :=
    Nat.pow_le_pow_right hx (le_max_right _ _)
  have hA : L D k ≤ M * (1 + D + k) ^ max N N' := le_trans (hM D k) (Nat.mul_le_mul_left M hN)
  have hB : L' D k ≤ M' * (1 + D + k) ^ max N N' :=
    le_trans (hM' D k) (Nat.mul_le_mul_left M' hN')
  calc L D k * L' D k
      ≤ (M * (1 + D + k) ^ max N N') * (M' * (1 + D + k) ^ max N N') := Nat.mul_le_mul hA hB
    _ = M * M' * (1 + D + k) ^ (2 * max N N') := by
        rw [show (M * (1 + D + k) ^ max N N') * (M' * (1 + D + k) ^ max N N')
              = M * M' * ((1 + D + k) ^ max N N' * (1 + D + k) ^ max N N') from by ring,
            ← pow_add]
        rw [show max N N' + max N N' = 2 * max N N' from by ring]

theorem expB_poly1 (q : Polynomial ℕ) : ExpB (fun D _ => q.eval D) := by
  obtain ⟨C, N, h⟩ := Work.WilE7.poly_eval_le q
  refine ⟨C, N, fun D k => ?_⟩
  have h1 : (1 + D) ^ N ≤ (1 + D + k) ^ N := Nat.pow_le_pow_left (by omega) N
  calc q.eval D ≤ C * (1 + D) ^ N := h D
    _ ≤ C * (1 + D + k) ^ N := Nat.mul_le_mul_left _ h1

theorem expB_poly2 (b : MvPolynomial (Fin 2) ℕ) : ExpB (fun D k => b.eval ![D, k]) := by
  obtain ⟨M, N, h⟩ := Work.WilE7.poly_le_pow b
  refine ⟨M, 2 * N, fun D k => ?_⟩
  have hD : (1 + D) ^ N ≤ (1 + D + k) ^ N := Nat.pow_le_pow_left (by omega) N
  have hk : (1 + k) ^ N ≤ (1 + D + k) ^ N := Nat.pow_le_pow_left (by omega) N
  calc b.eval ![D, k] ≤ M * (1 + D) ^ N * (1 + k) ^ N := h D k
    _ ≤ M * (1 + D + k) ^ N * (1 + D + k) ^ N :=
        Nat.mul_le_mul (Nat.mul_le_mul_left M hD) hk
    _ = M * (1 + D + k) ^ (2 * N) := by
        rw [show M * (1 + D + k) ^ N * (1 + D + k) ^ N
              = M * ((1 + D + k) ^ N * (1 + D + k) ^ N) from by ring, ← pow_add]
        rw [show N + N = 2 * N from by ring]

theorem expB_shift {L : ℕ → ℕ → ℕ} (h : ExpB L) : ExpB (fun D k => L D k + 1) :=
  expB_add h (expB_const 1)

theorem expB_pow {L : ℕ → ℕ → ℕ} (h : ExpB L) (N : ℕ) :
    ExpB (fun D k => (L D k + 1) ^ N) := by
  obtain ⟨M0, N0, h0⟩ := expB_shift h
  refine ⟨M0 ^ N, N0 * N, fun D k => ?_⟩
  have h1 : L D k + 1 ≤ M0 * (1 + D + k) ^ N0 := h0 D k
  calc (L D k + 1) ^ N ≤ (M0 * (1 + D + k) ^ N0) ^ N := Nat.pow_le_pow_left h1 N
    _ = M0 ^ N * (1 + D + k) ^ (N0 * N) := by rw [mul_pow, ← pow_mul]

/-- A two-variable polynomial evaluated at two `ExpB` functions is `ExpB`. -/
theorem expB_mvpoly2 {L L' : ℕ → ℕ → ℕ} (h : ExpB L) (h' : ExpB L')
    (b : MvPolynomial (Fin 2) ℕ) : ExpB (fun D k => b.eval ![L D k, L' D k]) := by
  obtain ⟨M, N, hM⟩ := Work.WilE7.poly_le_pow b
  obtain ⟨M1, N1, h1⟩ := expB_pow h N
  obtain ⟨M2, N2, h2⟩ := expB_pow h' N
  refine ⟨M * M1 * M2, N1 + N2 + N, fun D k => ?_⟩
  have hX : 1 ≤ 1 + D + k := by omega
  have e1 : 1 + L D k = L D k + 1 := by ring
  have e2 : 1 + L' D k = L' D k + 1 := by ring
  calc b.eval ![L D k, L' D k] ≤ M * (1 + L D k) ^ N * (1 + L' D k) ^ N := hM (L D k) (L' D k)
    _ = M * (L D k + 1) ^ N * (L' D k + 1) ^ N := by rw [e1, e2]
    _ ≤ M * (M1 * (1 + D + k) ^ N1) * (M2 * (1 + D + k) ^ N2) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left M (h1 D k)) (h2 D k)
    _ = M * M1 * M2 * ((1 + D + k) ^ N1 * (1 + D + k) ^ N2) := by ring
    _ = M * M1 * M2 * (1 + D + k) ^ (N1 + N2) := by rw [← pow_add]
    _ ≤ M * M1 * M2 * (1 + D + k) ^ (N1 + N2 + N) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hX (Nat.le_add_right _ _))

/-- A three-variable polynomial evaluated at three `ExpB` functions is `ExpB`. -/
theorem expB_mvpoly3 {L L' L'' : ℕ → ℕ → ℕ} (h : ExpB L) (h' : ExpB L') (h'' : ExpB L'')
    (b : MvPolynomial (Fin 3) ℕ) : ExpB (fun D k => b.eval ![L D k, L' D k, L'' D k]) := by
  obtain ⟨M, N, hM⟩ := Work.WilE7.poly_le_pow3 b
  obtain ⟨M1, N1, h1⟩ := expB_pow h N
  obtain ⟨M2, N2, h2⟩ := expB_pow h' N
  obtain ⟨M3, N3, h3⟩ := expB_pow h'' N
  refine ⟨M * M1 * M2 * M3, N1 + N2 + (N3 + N), fun D k => ?_⟩
  have hX : 1 ≤ 1 + D + k := by omega
  have e1 : 1 + L D k = L D k + 1 := by ring
  have e2 : 1 + L' D k = L' D k + 1 := by ring
  have e3 : 1 + L'' D k = L'' D k + 1 := by ring
  have hb := hM ![L D k, L' D k, L'' D k]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons] at hb
  calc b.eval ![L D k, L' D k, L'' D k]
      ≤ M * (1 + L D k) ^ N * (1 + L' D k) ^ N * (1 + L'' D k) ^ N := hb
    _ = M * (L D k + 1) ^ N * (L' D k + 1) ^ N * (L'' D k + 1) ^ N := by rw [e1, e2, e3]
    _ ≤ M * (M1 * (1 + D + k) ^ N1) * (M2 * (1 + D + k) ^ N2) * (M3 * (1 + D + k) ^ N3) :=
        Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left M (h1 D k)) (h2 D k)) (h3 D k)
    _ = M * M1 * M2 * M3 *
          ((1 + D + k) ^ N1 * ((1 + D + k) ^ N2 * (1 + D + k) ^ N3)) := by ring
    _ = M * M1 * M2 * M3 * (1 + D + k) ^ (N1 + (N2 + N3)) := by rw [← pow_add, ← pow_add]
    _ ≤ M * M1 * M2 * M3 * (1 + D + k) ^ (N1 + N2 + (N3 + N)) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hX (by omega))

/-- Substitution of a polynomial into a polynomial preserves `ExpB`. -/
theorem expB_poly_comp (q p : Polynomial ℕ) : ExpB (fun D _ => q.eval (p.eval D)) := by
  obtain ⟨Cq, Nq, hq⟩ := Work.WilE7.poly_eval_le q
  obtain ⟨Cp, Np, hp⟩ := Work.WilE7.poly_eval_le p
  have hpD : ∀ D : ℕ, 1 + p.eval D ≤ (Cp + 1) * (1 + D) ^ Np := by
    intro D
    have h1 : (1 : ℕ) ≤ (1 + D) ^ Np := Nat.one_le_pow _ _ (by omega)
    have h2 := hp D
    calc 1 + p.eval D ≤ 1 + Cp * (1 + D) ^ Np := by omega
      _ ≤ (Cp + 1) * (1 + D) ^ Np := by
          have : Cp * (1 + D) ^ Np + (1 + D) ^ Np = (Cp + 1) * (1 + D) ^ Np := by ring
          omega
  refine ⟨Cq * (Cp + 1) ^ Nq, Np * Nq, fun D k => ?_⟩
  have hX : (1 + D) ≤ 1 + D + k := by omega
  calc q.eval (p.eval D) ≤ Cq * (1 + p.eval D) ^ Nq := hq _
    _ ≤ Cq * ((Cp + 1) * (1 + D) ^ Np) ^ Nq :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (hpD D) Nq)
    _ = Cq * ((Cp + 1) ^ Nq * ((1 + D) ^ Np) ^ Nq) := by rw [mul_pow]
    _ = Cq * (Cp + 1) ^ Nq * (1 + D) ^ (Np * Nq) := by rw [← pow_mul]; ring
    _ ≤ Cq * (Cp + 1) ^ Nq * (1 + D + k) ^ (Np * Nq) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hX (Np * Nq))

/-- The consumer: an `ExpB` function is dominated by a polynomial in three variables (evaluated at
`![D,k,l]`, `l` unused). -/
theorem exists_mvpoly3_le {L : ℕ → ℕ → ℕ} (h : ExpB L) :
    ∃ Ng : MvPolynomial (Fin 3) ℕ, ∀ D k l : ℕ, L D k ≤ MvPolynomial.eval ![D, k, l] Ng := by
  obtain ⟨M, N, hM⟩ := h
  refine ⟨MvPolynomial.C M * (MvPolynomial.X (0 : Fin 3) + MvPolynomial.X (1 : Fin 3) + 1) ^ N,
    fun D k l => ?_⟩
  have he : MvPolynomial.eval ![D, k, l]
      (MvPolynomial.C M * (MvPolynomial.X (0 : Fin 3) + MvPolynomial.X (1 : Fin 3) + 1) ^ N)
      = M * (D + k + 1) ^ N := by
    simp [MvPolynomial.eval_mul, MvPolynomial.eval_pow, MvPolynomial.eval_add, MvPolynomial.eval_X]
  rw [he]
  calc L D k ≤ M * (1 + D + k) ^ N := hM D k
    _ = M * (D + k + 1) ^ N := by ring_nf

end Work.WilE7.Endgame.Bv2
