import Submission.ZagierHoffmanProof.StepK5
import Submission.ZagierHoffmanProof.StepK4

set_option autoImplicit false
set_option maxHeartbeats 8000000

open Polynomial
open scoped BigOperators

/-!
# Step K6: R1(0) — the level-1 power-sum evaluation `P F 1 ⟨1⟩ = −D1⁻¹`

R1 (paper (2.8)) at level d = 0 reads `P_0(q) + D1·S_1(1, q−1) = 0`; since
`P_0(n) = 1` and `S_1(1, q−1) = P_1(1)·S_<1(q−1) = P_1(1)`, the base case is exactly
`P F 1 ⟨1⟩ = −D1⁻¹` (D1 = the completion class of `carlitzOne F = X^q − X`).

Using `P_one_eq_sum_translate`, `P F 1 ⟨1⟩ = Σ_c (X + C c)^{-1}`; per `c`, in `RatFunc F`
`(X + C c)^{-1} = (qPoly F c)·carlitzOne^{-1}` (from `carlitzOne = (X + C c)·qPoly F c`),
so the sum is `(A F 1)·carlitzOne^{-1} = −1·carlitzOne^{-1}` by StepK5's `A F 1 = −1`.
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- The completion cast `RatFunc F → CompletionAtInfty F` is the algebra map. -/
lemma rat_cast_eq_algebraMap (x : RatFunc F) :
    (x : RatFunc.CompletionAtInfty F) =
      algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F) x := by
  rfl

/-- The `RatFunc F`-cast of a polynomial is the algebra map from `F[X]`. -/
lemma poly_cast_eq_algebraMap (p : F[X]) :
    (p : RatFunc F) = algebraMap (F[X]) (RatFunc F) p := by
  rfl

/-- The linear factor `X + C c` is nonzero in `F[X]`. -/
lemma X_add_C_ne_zero (c : F) : (X + C c : F[X]) ≠ 0 := by
  intro hz
  have hc := congrArg (fun p : F[X] => p.coeff 1) hz
  simp at hc

/-- `qPoly F c` is nonzero in `F[X]` (it is monic of degree `q − 1 ≥ 1`). -/
lemma qPoly_ne_zero (c : F) : qPoly F c ≠ 0 := by
  intro hz
  have hn := qPoly_natDegree F c
  rw [hz, Polynomial.natDegree_zero] at hn
  have hq : 2 ≤ Nat.card F := card_ge_two F
  omega

/-- Per-`c` RatFunc identity: `(X + C c)^{-1} = (qPoly F c)·carlitzOne^{-1}` in `RatFunc F`. -/
lemma rat_inv_X_add_C (c : F) :
    ((X + C c : F[X]) : RatFunc F)⁻¹ =
      ((qPoly F c : F[X]) : RatFunc F) *
        (((carlitzOne F : F[X]) : RatFunc F)⁻¹) := by
  classical
  let x : RatFunc F := ((X + C c : F[X]) : RatFunc F)
  let q : RatFunc F := ((qPoly F c : F[X]) : RatFunc F)
  let y : RatFunc F := ((carlitzOne F : F[X]) : RatFunc F)
  change x⁻¹ = q * y⁻¹
  have hy : y = x * q := by
    dsimp [x, q, y]
    calc
      ((carlitzOne F : F[X]) : RatFunc F)
          = (((X + C c) * qPoly F c : F[X]) : RatFunc F) := by
            exact congrArg (fun p : F[X] => (p : RatFunc F)) (carlitzOne_eq_mul_qPoly F c)
      _ = ((X + C c : F[X]) : RatFunc F) * ((qPoly F c : F[X]) : RatFunc F) := by
            exact map_mul (algebraMap (F[X]) (RatFunc F)) (X + C c : F[X]) (qPoly F c)
  have hx0 : x ≠ 0 := by
    dsimp [x]
    intro hz
    exact X_add_C_ne_zero F c (RatFunc.algebraMap_injective F (by simpa using hz))
  have hq0 : q ≠ 0 := by
    dsimp [q]
    intro hz
    exact qPoly_ne_zero F c (RatFunc.algebraMap_injective F (by simpa using hz))
  have hy0 : y ≠ 0 := by
    rw [hy]
    exact mul_ne_zero hx0 hq0
  have hxq : x⁻¹ * y = q := by
    rw [hy]
    rw [← mul_assoc, inv_mul_cancel₀ hx0, one_mul]
  calc
    x⁻¹ = x⁻¹ * (y * y⁻¹) := by
          rw [mul_inv_cancel₀ hy0, mul_one]
    _ = (x⁻¹ * y) * y⁻¹ := by
          rw [mul_assoc]
    _ = q * y⁻¹ := by
          rw [hxq]

/-- Completion-level per-`c` identity (image of `rat_inv_X_add_C` under the
`RatFunc F → K∞` embedding). -/
lemma inv_X_add_C_K (c : F) :
    letI : Fintype F := Fintype.ofFinite F
    ((((X + C c : F[X]) : RatFunc F) : RatFunc.CompletionAtInfty F) ^ (1 : ℕ))⁻¹ =
      (((qPoly F c : F[X]) : RatFunc F) : RatFunc.CompletionAtInfty F) *
        ((((carlitzOne F : F[X]) : RatFunc F) : RatFunc.CompletionAtInfty F)⁻¹) := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  have hpow : ((((X + C c : F[X]) : RatFunc F) : RatFunc.CompletionAtInfty F) ^ (1 : ℕ))⁻¹ =
      ((((X + C c : F[X]) : RatFunc F) : RatFunc.CompletionAtInfty F))⁻¹ := by
    simp
  rw [hpow]
  let x : RatFunc F := ((X + C c : F[X]) : RatFunc F)
  let q : RatFunc F := ((qPoly F c : F[X]) : RatFunc F)
  let y : RatFunc F := ((carlitzOne F : F[X]) : RatFunc F)
  change (x : RatFunc.CompletionAtInfty F)⁻¹ =
      (q : RatFunc.CompletionAtInfty F) * ((y : RatFunc.CompletionAtInfty F)⁻¹)
  have hr := rat_inv_X_add_C F c
  have hembed := congrArg (algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F)) hr
  calc
    (x : RatFunc.CompletionAtInfty F)⁻¹
        = (algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F)) (x⁻¹) := by
          rw [rat_cast_eq_algebraMap F]
          exact (map_inv₀ (algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F)) x).symm
    _ = (algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F)) (q * y⁻¹) := by
          exact hembed
    _ = (algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F)) q *
          (algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F)) (y⁻¹) := by
          rw [map_mul]
    _ = (q : RatFunc.CompletionAtInfty F) * ((y : RatFunc.CompletionAtInfty F)⁻¹) := by
          rw [map_inv₀]
          rw [rat_cast_eq_algebraMap F, rat_cast_eq_algebraMap F]

/-- `Σ_c qPoly F c = A F 1` in `F[X]`. -/
lemma sum_qPoly_eq_A_one :
    letI : Fintype F := Fintype.ofFinite F
    (∑ c : F, qPoly F c : F[X]) = A F 1 := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  calc
    (∑ c : F, qPoly F c : F[X]) = (∑ c : F, (qPoly F c) ^ 1 : F[X]) := by
          apply Finset.sum_congr rfl
          intro c hc
          simp
    _ = A F 1 := by
          rfl

/-- Sum of the embedded `qPoly`'s equals the embedded `A F 1`. -/
lemma sum_qPoly_embed_eq_A_one :
    letI : Fintype F := Fintype.ofFinite F
    (∑ c : F, (((qPoly F c : F[X]) : RatFunc F) : RatFunc.CompletionAtInfty F)) =
      (((A F 1 : F[X]) : RatFunc F) : RatFunc.CompletionAtInfty F) := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  have h1 : (∑ c : F, ((qPoly F c : F[X]) : RatFunc F)) =
      (((∑ c : F, qPoly F c : F[X]) : RatFunc F)) := by
    exact (map_sum (algebraMap (F[X]) (RatFunc F)) (fun c : F => qPoly F c)
      (Finset.univ : Finset F)).symm
  have h2 : (∑ c : F, (((qPoly F c : F[X]) : RatFunc F) : RatFunc.CompletionAtInfty F)) =
      (((∑ c : F, ((qPoly F c : F[X]) : RatFunc F)) : RatFunc F) : RatFunc.CompletionAtInfty F) := by
    exact (map_sum (algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F))
      (fun c : F => ((qPoly F c : F[X]) : RatFunc F)) (Finset.univ : Finset F)).symm
  calc
    (∑ c : F, (((qPoly F c : F[X]) : RatFunc F) : RatFunc.CompletionAtInfty F))
        = (((∑ c : F, ((qPoly F c : F[X]) : RatFunc F)) : RatFunc F) : RatFunc.CompletionAtInfty F) := h2
    _ = (((∑ c : F, qPoly F c : F[X]) : RatFunc F) : RatFunc.CompletionAtInfty F) := by
          rw [h1]
    _ = (((A F 1 : F[X]) : RatFunc F) : RatFunc.CompletionAtInfty F) := by
          rw [sum_qPoly_eq_A_one F]

/-- ★ `P F 1 ⟨1⟩ = −D1⁻¹` where `D1` is the completion class of `X^q − X`. -/
lemma P_one_one_eq_neg_inv_carlitz :
    letI : Fintype F := Fintype.ofFinite F
    P F 1 ⟨1, by omega⟩ =
      -(((carlitzOne F : F[X]) : RatFunc F) : RatFunc.CompletionAtInfty F)⁻¹ := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  have hA1 : (((A F 1 : F[X]) : RatFunc F) : RatFunc.CompletionAtInfty F) = (-1 : RatFunc.CompletionAtInfty F) := by
    let φ : F[X] →+* RatFunc.CompletionAtInfty F :=
      (algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F)).comp (algebraMap (F[X]) (RatFunc F))
    have hc := congrArg φ (A_one_eq_neg_one F)
    have hneg : φ (-1 : F[X]) = (-1 : RatFunc.CompletionAtInfty F) := by
      calc
        φ (-1 : F[X]) = -(φ (1 : F[X])) := by
              exact map_neg φ (1 : F[X])
        _ = -1 := by
              rw [map_one]
    rw [hneg] at hc
    rw [rat_cast_eq_algebraMap F, poly_cast_eq_algebraMap F]
    exact hc
  calc
    P F 1 ⟨1, by omega⟩
        = ∑ c : F, ((((X + C c : F[X]) : RatFunc F) : RatFunc.CompletionAtInfty F) ^ (1 : ℕ))⁻¹ := by
          rw [P_one_eq_sum_translate F ⟨1, by omega⟩]
          apply Finset.sum_congr rfl
          intro c hc
          simp
    _ = ∑ c : F, ((((qPoly F c : F[X]) : RatFunc F) : RatFunc.CompletionAtInfty F) *
          (((carlitzOne F : F[X]) : RatFunc F) : RatFunc.CompletionAtInfty F)⁻¹) := by
          apply Finset.sum_congr rfl
          intro c hc
          change ((((X + C c : F[X]) : RatFunc F) : RatFunc.CompletionAtInfty F) ^ (1 : ℕ))⁻¹ =
              (((qPoly F c : F[X]) : RatFunc F) : RatFunc.CompletionAtInfty F) *
                (((carlitzOne F : F[X]) : RatFunc F) : RatFunc.CompletionAtInfty F)⁻¹
          rw [inv_X_add_C_K F c]
    _ = (∑ c : F, (((qPoly F c : F[X]) : RatFunc F) : RatFunc.CompletionAtInfty F)) *
          (((carlitzOne F : F[X]) : RatFunc F) : RatFunc.CompletionAtInfty F)⁻¹ := by
          rw [Finset.sum_mul]
    _ = (((A F 1 : F[X]) : RatFunc F) : RatFunc.CompletionAtInfty F) *
          (((carlitzOne F : F[X]) : RatFunc F) : RatFunc.CompletionAtInfty F)⁻¹ := by
          rw [sum_qPoly_embed_eq_A_one F]
    _ = (-1 : RatFunc.CompletionAtInfty F) *
          (((carlitzOne F : F[X]) : RatFunc F) : RatFunc.CompletionAtInfty F)⁻¹ := by
          rw [hA1]
    _ = -(((carlitzOne F : F[X]) : RatFunc F) : RatFunc.CompletionAtInfty F)⁻¹ := by
          simp




variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- `S_<1(m) = 1` at level one (only the constant monic polynomial contributes). -/
lemma S_lt_one_one (m : ℕ+) :
    letI : Fintype F := Fintype.ofFinite F
    S_lt F 1 (by omega : 0 < 1) (single m) 1 = 1 := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  rw [S_lt_eq_sum_levels F 1 (by omega : 0 < 1) (single m) 1]
  have h01 : (Finset.range 1) = {0} := by
    ext i
    simp
  rw [h01]
  simp
  rw [S_one_eq_P F 0 (by omega : 0 < 1) (single m)]
  change P F 0 m = 1
  exact P_zero_eq_one F m

/-- The embedding `RatFunc F → CompletionAtInfty F` is injective (source is a field). -/
lemma rat_embed_injective :
    Function.Injective (algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F)) := by
  let K := RatFunc.CompletionAtInfty F
  let f : RatFunc F →+* K := algebraMap (RatFunc F) K
  intro a b hab
  by_contra h
  have hc : a - b ≠ 0 := sub_ne_zero.mpr h
  have hzero : f (a - b) = 0 := by
    rw [map_sub]
    rw [hab]
    rw [sub_self]
  have hone : (1 : K) = 0 := by
    calc
      (1 : K) = f (1 : RatFunc F) := by
            exact (map_one f).symm
      _ = f ((a - b) * (a - b)⁻¹) := by
            rw [mul_inv_cancel₀ hc]
      _ = f (a - b) * f ((a - b)⁻¹) := by
            rw [map_mul]
      _ = 0 := by
            rw [hzero]
            simp
  exact one_ne_zero hone

/-- `D1 := X^q − X` is nonzero in the completion. -/
lemma carlitz_class_ne_zero :
    (((carlitzOne F : F[X]) : RatFunc F) : RatFunc.CompletionAtInfty F) ≠ 0 := by
  classical
  have hcar0 : carlitzOne F ≠ 0 := by
    intro hz
    have hn := carlitzOne_natDegree F
    rw [hz, Polynomial.natDegree_zero] at hn
    have hq : 2 ≤ Nat.card F := card_ge_two F
    omega
  have hrat0 : ((carlitzOne F : F[X]) : RatFunc F) ≠ 0 := by
    intro h
    apply hcar0
    exact RatFunc.algebraMap_injective F (by simpa using h)
  -- D1 = f(rat) with f injective
  rw [rat_cast_eq_algebraMap F]
  intro hz
  apply hrat0
  exact rat_embed_injective F hz

/-- ★ `S F 2 (pair 1 (q−1)) 1 = P F 1 ⟨1⟩`. -/
lemma S_two_one_qminus :
    letI : Fintype F := Fintype.ofFinite F
    S F 2 (by omega : 0 < 2)
        (pair ⟨1, by omega⟩ ⟨Nat.card F - 1, by have hq : 2 ≤ Nat.card F := card_ge_two F; omega⟩)
        1 = P F 1 ⟨1, by omega⟩ := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  let qm : ℕ+ := ⟨Nat.card F - 1, by have hq : 2 ≤ Nat.card F := card_ge_two F; omega⟩
  change S F 2 (by omega : 0 < 2) (pair ⟨1, by omega⟩ qm) 1 = P F 1 ⟨1, by omega⟩
  rw [S_d_recursion F 2 (by omega : 1 < 2) (by omega : 0 < 2) (by omega : 0 < 2 - 1)
      (pair ⟨1, by omega⟩ qm) 1]
  have htail : (fun j : Fin 1 => pair ⟨1, by omega⟩ qm ⟨j.1 + 1, by omega⟩) = single qm := by
    funext j
    fin_cases j
    simp [single, pair]
  rw [htail]
  rw [S_lt_one_one F qm]
  simp [pair]

/-- ★ R1 at level 0: `P_0(q) + D1·S_1(1, q−1) = 0`. -/
theorem R1_zero :
    P F 0 ⟨Nat.card F, by have hq : 2 ≤ Nat.card F := card_ge_two F; omega⟩ +
      (((carlitzOne F : F[X]) : RatFunc F) : RatFunc.CompletionAtInfty F) *
      S F 2 (by omega : 0 < 2)
        (pair ⟨1, by omega⟩ ⟨Nat.card F - 1, by have hq : 2 ≤ Nat.card F := card_ge_two F; omega⟩)
        1 = 0 := by
  classical
  let K := RatFunc.CompletionAtInfty F
  let D1 : K := (((carlitzOne F : F[X]) : RatFunc F) : K)
  let qm : ℕ+ := ⟨Nat.card F - 1, by have hq : 2 ≤ Nat.card F := card_ge_two F; omega⟩
  have hD0 : D1 ≠ 0 := by
    dsimp [D1]
    exact carlitz_class_ne_zero F
  calc
    P F 0 ⟨Nat.card F, by have hq : 2 ≤ Nat.card F := card_ge_two F; omega⟩ +
        D1 * S F 2 (by omega : 0 < 2) (pair ⟨1, by omega⟩ qm) 1
        = P F 0 ⟨Nat.card F, by have hq : 2 ≤ Nat.card F := card_ge_two F; omega⟩ +
            D1 * P F 1 ⟨1, by omega⟩ := by
          rw [S_two_one_qminus F]
    _ = 1 + D1 * P F 1 ⟨1, by omega⟩ := by
          rw [P_zero_eq_one F ⟨Nat.card F, by have hq : 2 ≤ Nat.card F := card_ge_two F; omega⟩]
    _ = 0 := by
          rw [P_one_one_eq_neg_inv_carlitz F]
          rw [mul_neg]
          rw [mul_inv_cancel₀ hD0]
          ring


end ZagierHoffmanPositiveChar

