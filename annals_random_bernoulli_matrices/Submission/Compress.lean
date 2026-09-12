/-
Deterministic core of Proposition `l: compress` (Tikhomirov 2020, arXiv:1812.09016).

Vector convention (matching `AuxOfLKR.aux_single_vector`): vectors are
`x : Fin n → ℝ`, squared Euclidean norm `sqNorm x := ∑ i, (x i)^2`, and the
action of an (m × n) matrix family has squared length
`actSq A x := ∑ k : Fin m, (∑ j : Fin n, A k j * x j)^2`.

All probability-free facts live here:
  * `sqrt_sum_sq_add_le` / `sqrtAct_triangle` / `sqrtAct_shift_le` — the ℓ₂
    triangle machinery for the row action (Minkowski for Finset sums);
  * `sqrtAct_le_of_spectral`    — spectral-event bound on the centered part;
  * `event_reduction`           — on the spectral event, a small ball of `x`
    at scale (γ/2)·√n gives a small ball of the net point `y` at scale γ·√n;
  * `act_ge_of_sum_ge`          — on the spectral event a large |Σ x| forces
    ‖(A + c·11ᵀ) x‖ ≥ γ·√n (the ℓ-truncation principle).
-/
import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 400000

namespace Submission.Compress

noncomputable section

open scoped BigOperators

/-! ## Squared norms and row actions on coordinate vectors -/

/-- Squared Euclidean norm of a coordinate vector. -/
noncomputable def sqNorm {n : ℕ} (x : Fin n → ℝ) : ℝ := ∑ i, (x i)^2

/-- Coordinate sum. -/
noncomputable def vecSum {n : ℕ} (x : Fin n → ℝ) : ℝ := ∑ i, x i

/-- Row action of a matrix family on a vector. -/
noncomputable def rowAct {m n : ℕ} (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ) : Fin m → ℝ :=
  fun k => ∑ j : Fin n, A k j * x j

/-- Squared ℓ₂ norm of the image vector. -/
noncomputable def actSq {m n : ℕ} (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ k : Fin m, (rowAct A x k)^2

/-- ℓ₂ norm of the image vector. -/
noncomputable def sqrtAct {m n : ℕ} (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ) : ℝ :=
  Real.sqrt (actSq A x)

/-- Adding a constant `c` to every entry. -/
noncomputable def shiftRows {m n : ℕ} (A : Fin m → Fin n → ℝ) (c : ℝ) : Fin m → Fin n → ℝ :=
  fun k j => A k j + c

lemma actSq_nonneg {m n : ℕ} (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ) : 0 ≤ actSq A x := by
  unfold actSq
  positivity

lemma sqNorm_nonneg {n : ℕ} (x : Fin n → ℝ) : 0 ≤ sqNorm x := by
  unfold sqNorm
  positivity

lemma rowAct_add {m n : ℕ} (A : Fin m → Fin n → ℝ) (x y : Fin n → ℝ) :
    rowAct A (x + y) = rowAct A x + rowAct A y := by
  funext k
  calc
    (∑ j : Fin n, A k j * (x j + y j)) = ∑ j : Fin n, (A k j * x j + A k j * y j) := by
      apply Finset.sum_congr rfl; intro j hj; ring
    _ = (∑ j : Fin n, A k j * x j) + (∑ j : Fin n, A k j * y j) := by
      rw [Finset.sum_add_distrib]

lemma rowAct_sub {m n : ℕ} (A : Fin m → Fin n → ℝ) (x y : Fin n → ℝ) :
    rowAct A (x - y) = rowAct A x - rowAct A y := by
  funext k
  calc
    (∑ j : Fin n, A k j * (x j - y j)) = ∑ j : Fin n, (A k j * x j - A k j * y j) := by
      apply Finset.sum_congr rfl; intro j hj; ring
    _ = (∑ j : Fin n, A k j * x j) - (∑ j : Fin n, A k j * y j) := by
      rw [Finset.sum_sub_distrib]

lemma vecSum_add {n : ℕ} (x y : Fin n → ℝ) : vecSum (x + y) = vecSum x + vecSum y := by
  simp [vecSum, Finset.sum_add_distrib]

lemma vecSum_sub {n : ℕ} (x y : Fin n → ℝ) : vecSum (x - y) = vecSum x - vecSum y := by
  simp [vecSum, Finset.sum_sub_distrib]

lemma sqNorm_eq_sqrt : ∀ {n : ℕ} (x : Fin n → ℝ), sqNorm x = (Real.sqrt (sqNorm x))^2 := by
  intro n x
  rw [Real.sq_sqrt (sqNorm_nonneg x)]

/-! ## ℓ₂ triangle machinery for the row action -/

/-- Minkowski: √(∑ (a+b)²) ≤ √(∑ a²) + √(∑ b²) on `Fin m`. -/
lemma sqrt_sum_sq_add_le {m : ℕ} (a b : Fin m → ℝ) :
    Real.sqrt (∑ k : Fin m, (a k + b k)^2) ≤
      Real.sqrt (∑ k : Fin m, (a k)^2) + Real.sqrt (∑ k : Fin m, (b k)^2) := by
  have hcs : |∑ k : Fin m, a k * b k| ≤
      Real.sqrt (∑ k : Fin m, (a k)^2) * Real.sqrt (∑ k : Fin m, (b k)^2) := by
    have h1 : (∑ k : Fin m, a k * b k)^2 ≤ (∑ k : Fin m, (a k)^2) * (∑ k : Fin m, (b k)^2) := by
      simpa using (Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin m)) a b)
    have hsa : 0 ≤ ∑ k : Fin m, (a k)^2 := by positivity
    have hsb : 0 ≤ ∑ k : Fin m, (b k)^2 := by positivity
    have h2 : Real.sqrt ((∑ k : Fin m, (a k)^2) * (∑ k : Fin m, (b k)^2)) =
        Real.sqrt (∑ k : Fin m, (a k)^2) * Real.sqrt (∑ k : Fin m, (b k)^2) := by
      rw [Real.sqrt_mul hsa (∑ k : Fin m, (b k)^2)]
    calc
      |∑ k : Fin m, a k * b k| = Real.sqrt ((∑ k : Fin m, a k * b k)^2) := by
        rw [Real.sqrt_sq_eq_abs]
      _ ≤ Real.sqrt ((∑ k : Fin m, (a k)^2) * (∑ k : Fin m, (b k)^2)) := Real.sqrt_le_sqrt h1
      _ = Real.sqrt (∑ k : Fin m, (a k)^2) * Real.sqrt (∑ k : Fin m, (b k)^2) := h2
  let sa : ℝ := Real.sqrt (∑ k : Fin m, (a k)^2)
  let sb : ℝ := Real.sqrt (∑ k : Fin m, (b k)^2)
  have hs : (∑ k : Fin m, (a k + b k)^2) ≤ (sa + sb)^2 := by
    have hsum : (∑ k : Fin m, (a k + b k)^2) =
        (∑ k : Fin m, (a k)^2) + 2 * (∑ k : Fin m, a k * b k) + (∑ k : Fin m, (b k)^2) := by
      calc
        (∑ k : Fin m, (a k + b k)^2) = ∑ k : Fin m, ((a k)^2 + 2 * (a k) * (b k) + (b k)^2) := by
          apply Finset.sum_congr rfl; intro k hk; ring
        _ = (∑ k : Fin m, (a k)^2) + 2 * (∑ k : Fin m, (a k) * (b k)) + (∑ k : Fin m, (b k)^2) := by
          simp [Finset.sum_add_distrib, mul_assoc, Finset.mul_sum, add_comm, add_left_comm]
    rw [hsum]
    have hcs' : 2 * (∑ k : Fin m, a k * b k) ≤ 2 * (sa * sb) := by
      exact mul_le_mul_of_nonneg_left (by simpa [sa, sb] using (le_abs_self _).trans hcs) (by norm_num)
    have hm : (∑ k : Fin m, (a k)^2) + (∑ k : Fin m, (b k)^2) ≤ sa^2 + sb^2 := by
      have h1 : (∑ k : Fin m, (a k)^2) = sa^2 := by simp [sa]; rw [Real.sq_sqrt (by positivity)]
      have h2 : (∑ k : Fin m, (b k)^2) = sb^2 := by simp [sb]; rw [Real.sq_sqrt (by positivity)]
      rw [h1, h2]
    nlinarith
  calc
    Real.sqrt (∑ k : Fin m, (a k + b k)^2) ≤ Real.sqrt ((sa + sb)^2) := Real.sqrt_le_sqrt hs
    _ = sa + sb := by
      rw [Real.sqrt_sq_eq_abs]
      have : 0 ≤ sa + sb := add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      rw [abs_of_nonneg this]

/-- Triangle inequality for `sqrtAct` (linearity of the row action). -/
lemma sqrtAct_triangle {m n : ℕ} (A : Fin m → Fin n → ℝ) (x y : Fin n → ℝ) :
    sqrtAct A (x + y) ≤ sqrtAct A x + sqrtAct A y := by
  unfold sqrtAct actSq
  rw [rowAct_add A x y]
  exact sqrt_sum_sq_add_le (fun k : Fin m => rowAct A x k) (fun k : Fin m => rowAct A y k)

/-- Bound on ‖(A + c·11ᵀ) w‖ in terms of ‖A w‖ and the coordinate sum of `w`. -/
lemma sqrtAct_shift_le {m n : ℕ} (A : Fin m → Fin n → ℝ) (c : ℝ) (w : Fin n → ℝ) :
    sqrtAct (shiftRows A c) w ≤ sqrtAct A w + Real.sqrt (m : ℝ) * |c| * |vecSum w| := by
  let B : Fin m → Fin n → ℝ := fun _ _ => c
  have hBrow : rowAct B w = fun k : Fin m => c * vecSum w := by
    funext k
    simp [rowAct, B, vecSum]
    rw [Finset.mul_sum]
  have hlin : rowAct (shiftRows A c) w = rowAct A w + rowAct B w := by
    funext k
    simp [shiftRows, rowAct]
    calc
      (∑ j : Fin n, (A k j + c) * w j) = ∑ j : Fin n, (A k j * w j + c * w j) := by
        apply Finset.sum_congr rfl; intro j hj; ring
      _ = (∑ j : Fin n, A k j * w j) + (∑ j : Fin n, c * w j) := by
        rw [Finset.sum_add_distrib]
      _ = (∑ j : Fin n, A k j * w j) + (∑ j : Fin n, B k j * w j) := by
        apply congrArg (fun t => (∑ j : Fin n, A k j * w j) + t)
        apply Finset.sum_congr rfl; intro j hj; simp [B]
  have htri : sqrtAct (shiftRows A c) w ≤ sqrtAct A w + sqrtAct B w := by
    unfold sqrtAct actSq
    rw [hlin]
    rw [hBrow]
    exact sqrt_sum_sq_add_le (fun k : Fin m => rowAct A w k) (fun k : Fin m => c * vecSum w)
  have hconst : sqrtAct B w = Real.sqrt (m : ℝ) * |c| * |vecSum w| := by
    unfold sqrtAct actSq
    rw [hBrow]
    calc
      Real.sqrt (∑ k : Fin m, (c * vecSum w)^2) = Real.sqrt ((m : ℝ) * (c * vecSum w)^2) := by
        congr 1
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        simp
      _ = Real.sqrt (m : ℝ) * |c * vecSum w| := by
        rw [Real.sqrt_mul (by exact_mod_cast (Nat.zero_le m : 0 ≤ m)) ((c * vecSum w)^2)]
        rw [Real.sqrt_sq_eq_abs]
      _ = Real.sqrt (m : ℝ) * |c| * |vecSum w| := by
        rw [abs_mul]
        ring
  calc
    sqrtAct (shiftRows A c) w ≤ sqrtAct A w + sqrtAct B w := htri
    _ = sqrtAct A w + Real.sqrt (m : ℝ) * |c| * |vecSum w| := by rw [hconst]

/-! ## Spectral-event bounds on the centered part -/

/-- Spectral hypothesis gives the bound ‖A w‖ ≤ L·√n·‖w‖. -/
lemma sqrtAct_le_of_spectral {m n : ℕ} (A : Fin m → Fin n → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hE : ∀ v : Fin n → ℝ, actSq A v ≤ L ^ 2 * (n : ℝ) * sqNorm v) (w : Fin n → ℝ) :
    sqrtAct A w ≤ L * Real.sqrt (n : ℝ) * Real.sqrt (sqNorm w) := by
  have hsqw : 0 ≤ sqNorm w := sqNorm_nonneg w
  have hn : 0 ≤ (n : ℝ) := by positivity
  have h1 : Real.sqrt (L ^ 2 * ((n : ℝ) * sqNorm w)) = L * Real.sqrt ((n : ℝ) * sqNorm w) := by
    rw [Real.sqrt_mul (sq_nonneg L) ((n : ℝ) * sqNorm w)]
    rw [Real.sqrt_sq_eq_abs]
    rw [abs_of_nonneg hL]
  have h2 : Real.sqrt ((n : ℝ) * sqNorm w) = Real.sqrt (n : ℝ) * Real.sqrt (sqNorm w) := by
    rw [Real.sqrt_mul hn (sqNorm w)]
  have hs1 : Real.sqrt (L ^ 2 * (n : ℝ) * sqNorm w) =
      L * Real.sqrt (n : ℝ) * Real.sqrt (sqNorm w) := by
    calc
      Real.sqrt (L ^ 2 * (n : ℝ) * sqNorm w) = Real.sqrt (L ^ 2 * ((n : ℝ) * sqNorm w)) := by rw [← mul_assoc]
      _ = L * Real.sqrt ((n : ℝ) * sqNorm w) := h1
      _ = L * (Real.sqrt (n : ℝ) * Real.sqrt (sqNorm w)) := by rw [h2]
      _ = L * Real.sqrt (n : ℝ) * Real.sqrt (sqNorm w) := by ring
  calc
    sqrtAct A w = Real.sqrt (actSq A w) := rfl
    _ ≤ Real.sqrt (L ^ 2 * (n : ℝ) * sqNorm w) := Real.sqrt_le_sqrt (hE w)
    _ = L * Real.sqrt (n : ℝ) * Real.sqrt (sqNorm w) := hs1

/-- Reverse triangle inequality for the concrete ℓ₂ sums. -/
lemma sqrt_sum_sq_add_ge_sub {m : ℕ} (a b : Fin m → ℝ) :
    Real.sqrt (∑ k : Fin m, (b k)^2) - Real.sqrt (∑ k : Fin m, (a k)^2) ≤
      Real.sqrt (∑ k : Fin m, (a k + b k)^2) := by
  have htri := sqrt_sum_sq_add_le (fun k : Fin m => a k + b k) (fun k : Fin m => -a k)
  have hid : (∑ k : Fin m, ((a k + b k) + -a k)^2) = (∑ k : Fin m, (b k)^2) := by
    apply Finset.sum_congr rfl; intro k hk; ring
  have hn : (∑ k : Fin m, (-a k)^2) = (∑ k : Fin m, (a k)^2) := by
    apply Finset.sum_congr rfl; intro k hk; ring
  have h1 : Real.sqrt (∑ k : Fin m, (b k)^2) ≤
      Real.sqrt (∑ k : Fin m, (a k + b k)^2) + Real.sqrt (∑ k : Fin m, (a k)^2) := by
    calc
      Real.sqrt (∑ k : Fin m, (b k)^2) = Real.sqrt (∑ k : Fin m, ((a k + b k) + -a k)^2) := by rw [hid]
      _ ≤ Real.sqrt (∑ k : Fin m, (a k + b k)^2) + Real.sqrt (∑ k : Fin m, (-a k)^2) := by
        simpa using htri
      _ = Real.sqrt (∑ k : Fin m, (a k + b k)^2) + Real.sqrt (∑ k : Fin m, (a k)^2) := by rw [hn]
  linarith

/-- Row action after a constant shift: rowAct (shiftRows A c) x = rowAct A x + c·Σx. -/
lemma rowAct_shift {m n : ℕ} (A : Fin m → Fin n → ℝ) (c : ℝ) (x : Fin n → ℝ) :
    rowAct (shiftRows A c) x = fun k => rowAct A x k + c * vecSum x := by
  funext k
  calc
    (∑ j : Fin n, (A k j + c) * x j) = ∑ j : Fin n, (A k j * x j + c * x j) := by
      apply Finset.sum_congr rfl; intro j hj; ring
    _ = (∑ j : Fin n, A k j * x j) + (∑ j : Fin n, c * x j) := by
      rw [Finset.sum_add_distrib]
    _ = (∑ j : Fin n, A k j * x j) + c * (∑ j : Fin n, x j) := by
      rw [Finset.mul_sum]

/-- On the spectral event a large |Σ x| forces ‖(A + c·11ᵀ) x‖ ≥ γ·√n. -/
lemma act_ge_of_sum_ge {n : ℕ} (hn2 : 2 ≤ n) (A : Fin (n - 1) → Fin n → ℝ) (c L γ : ℝ)
    (hL : 0 < L) (hγ : 0 < γ) (hc : c ≠ 0)
    (hE : ∀ v : Fin n → ℝ, actSq A v ≤ L ^ 2 * (n : ℝ) * sqNorm v)
    {x : Fin n → ℝ} (hunit : sqNorm x = 1)
    (hsum : (2 * L + 2 * γ) / |c| ≤ |vecSum x|) :
    γ * Real.sqrt (n : ℝ) ≤ sqrtAct (shiftRows A c) x := by
  classical
  let M : Fin (n - 1) → Fin n → ℝ := shiftRows A c
  let b : Fin (n - 1) → ℝ := fun _ => c * vecSum x
  have hlin : rowAct M x = rowAct A x + b := by
    funext k
    have hk := congrFun (rowAct_shift A c x) k
    simpa [M, b] using hk
  have hsp : sqrtAct A x ≤ L * Real.sqrt (n : ℝ) := by
    have h1 := sqrtAct_le_of_spectral A L (le_of_lt hL) hE x
    calc
      sqrtAct A x ≤ L * Real.sqrt (n : ℝ) * Real.sqrt (sqNorm x) := h1
      _ = L * Real.sqrt (n : ℝ) := by
        rw [hunit, Real.sqrt_one, mul_one]
  have hb : Real.sqrt (∑ k : Fin (n - 1), (b k)^2) ≥
      Real.sqrt (((n - 1 : ℕ) : ℝ)) * (2 * L + 2 * γ) := by
    have hc0 : 0 < |c| := abs_pos.mpr hc
    have hnorm : Real.sqrt (∑ k : Fin (n - 1), (b k)^2) =
        Real.sqrt (((n - 1 : ℕ) : ℝ)) * (|c| * |vecSum x|) := by
      unfold b
      have hsumc : (∑ k : Fin (n - 1), (c * vecSum x)^2) =
          (((n - 1 : ℕ) : ℝ)) * (c * vecSum x)^2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        simp
      rw [hsumc]
      have h0 : 0 ≤ (((n - 1 : ℕ) : ℝ)) := by exact_mod_cast Nat.zero_le _
      rw [Real.sqrt_mul h0 ((c * vecSum x)^2)]
      rw [Real.sqrt_sq_eq_abs]
      rw [abs_mul]
    have hmul : |c| * |vecSum x| ≥ 2 * L + 2 * γ := by
      calc
        2 * L + 2 * γ = |c| * ((2 * L + 2 * γ) / |c|) := by field_simp [hc0.ne']
        _ ≤ |c| * |vecSum x| := by
          exact mul_le_mul_of_nonneg_left hsum (le_of_lt hc0)
    rw [hnorm]
    exact mul_le_mul_of_nonneg_left hmul (Real.sqrt_nonneg _)
  have hsub1 : Real.sqrt (∑ k : Fin (n - 1), (b k)^2) - sqrtAct A x ≤ sqrtAct M x := by
    have hg := sqrt_sum_sq_add_ge_sub (rowAct A x) b
    unfold sqrtAct
    have hrew : (∑ k : Fin (n - 1), (rowAct A x k + b k)^2) = actSq M x := by
      unfold actSq
      apply Finset.sum_congr rfl
      intro k hk
      have hk' : rowAct M x k = rowAct A x k + b k := by
        simpa using congrFun hlin k
      rw [← hk']
    calc
      Real.sqrt (∑ k : Fin (n - 1), (b k)^2) - Real.sqrt (∑ k : Fin (n - 1), (rowAct A x k)^2)
          ≤ Real.sqrt (∑ k : Fin (n - 1), (rowAct A x k + b k)^2) := hg
      _ = sqrtAct M x := by
        unfold sqrtAct
        rw [hrew]
  have hsub2 : Real.sqrt (∑ k : Fin (n - 1), (b k)^2) - sqrtAct A x ≥
      Real.sqrt (((n - 1 : ℕ) : ℝ)) * (2 * L + 2 * γ) - L * Real.sqrt (n : ℝ) := by
    linarith [hb, hsp]
  have hnum : γ * Real.sqrt (n : ℝ) ≤
      Real.sqrt (((n - 1 : ℕ) : ℝ)) * (2 * L + 2 * γ) - L * Real.sqrt (n : ℝ) := by
    have h4 : (4 : ℝ) * ((n - 1 : ℕ) : ℝ) ≥ (n : ℝ) := by
      have hn2r : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
      have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ n)]
        norm_num
      rw [hcast]
      nlinarith
    have h2sqrt : (2 : ℝ) * Real.sqrt (((n - 1 : ℕ) : ℝ)) ≥ Real.sqrt (n : ℝ) := by
      have hsqrtmul : Real.sqrt (4 * ((n - 1 : ℕ) : ℝ)) = 2 * Real.sqrt (((n - 1 : ℕ) : ℝ)) := by
        rw [Real.sqrt_mul (by norm_num : 0 ≤ (4 : ℝ)) (((n - 1 : ℕ) : ℝ))]
        norm_num
      calc
        (2 : ℝ) * Real.sqrt (((n - 1 : ℕ) : ℝ)) = Real.sqrt (4 * ((n - 1 : ℕ) : ℝ)) := by rw [hsqrtmul]
        _ ≥ Real.sqrt (n : ℝ) := Real.sqrt_le_sqrt h4
    have hLg : 0 ≤ L + γ := add_nonneg (le_of_lt hL) (le_of_lt hγ)
    have hmain : (2 * L + 2 * γ) * Real.sqrt (((n - 1 : ℕ) : ℝ)) ≥ (L + γ) * Real.sqrt (n : ℝ) := by
      calc
        (2 * L + 2 * γ) * Real.sqrt (((n - 1 : ℕ) : ℝ))
            = (L + γ) * (2 * Real.sqrt (((n - 1 : ℕ) : ℝ))) := by ring
        _ ≥ (L + γ) * Real.sqrt (n : ℝ) := by
          exact mul_le_mul_of_nonneg_left h2sqrt hLg
    nlinarith
  calc
    γ * Real.sqrt (n : ℝ) ≤ Real.sqrt (((n - 1 : ℕ) : ℝ)) * (2 * L + 2 * γ) - L * Real.sqrt (n : ℝ) := hnum
    _ ≤ Real.sqrt (∑ k : Fin (n - 1), (b k)^2) - sqrtAct A x := by linarith
    _ ≤ sqrtAct M x := hsub1

/-- From a squared-distance hypothesis to the Euclidean bound ‖y−x‖ ≤ γ/(8L). -/
lemma sqrt_sqNorm_le_of_sq_le {n : ℕ} {γ L : ℝ} (hL : 0 < L) (hγ : 0 < γ)
    {w : Fin n → ℝ} (h : sqNorm w ≤ (γ / (8 * L))^2) :
    Real.sqrt (sqNorm w) ≤ γ / (8 * L) := by
  have hpos : 0 ≤ γ / (8 * L) := div_nonneg (le_of_lt hγ) (by positivity)
  calc
    Real.sqrt (sqNorm w) ≤ Real.sqrt ((γ / (8 * L))^2) := Real.sqrt_le_sqrt h
    _ = |γ / (8 * L)| := Real.sqrt_sq_eq_abs (γ / (8 * L))
    _ = γ / (8 * L) := abs_of_nonneg hpos

/-- On the spectral event, small ball of `x` at scale (γ/2)·√n propagates to
scale γ·√n at a net point `y` with ‖y−x‖ ≤ γ/(8L) and matching coordinate sum. -/
lemma event_reduction {n : ℕ} (A : Fin (n - 1) → Fin n → ℝ) (c L γ : ℝ)
    (hL : 0 < L) (hγ : 0 < γ) (hc : c ≠ 0)
    (hE : ∀ v : Fin n → ℝ, actSq A v ≤ L ^ 2 * (n : ℝ) * sqNorm v)
    {x y : Fin n → ℝ}
    (hball : sqrtAct (shiftRows A c) x ≤ (γ / 2) * Real.sqrt (n : ℝ))
    (hd : sqNorm (y - x) ≤ (γ / (8 * L))^2)
    (hs : |vecSum (y - x)| ≤ γ / (4 * |c|)) :
    sqrtAct (shiftRows A c) y ≤ γ * Real.sqrt (n : ℝ) := by
  classical
  let M : Fin (n - 1) → Fin n → ℝ := shiftRows A c
  have htri := sqrtAct_triangle M x (y - x)
  have hy : x + (y - x) = y := by
    funext i
    simp
  rw [hy] at htri
  -- htri : sqrtAct M y ≤ sqrtAct M x + sqrtAct M (y - x)
  have hshift := sqrtAct_shift_le A c (y - x)
  -- hshift : sqrtAct (shiftRows A c) (y - x) ≤ sqrtAct A (y - x) + √(n−1)·|c|·|Σ|
  have hspec := sqrtAct_le_of_spectral A L (le_of_lt hL) hE (y - x)
  -- hspec : sqrtAct A (y−x) ≤ L·√n·√(sqNorm (y−x))
  have hd' : Real.sqrt (sqNorm (y - x)) ≤ γ / (8 * L) := sqrt_sqNorm_le_of_sq_le hL hγ hd
  have hpart1 : sqrtAct A (y - x) ≤ γ * Real.sqrt (n : ℝ) / 8 := by
    calc
      sqrtAct A (y - x) ≤ L * Real.sqrt (n : ℝ) * Real.sqrt (sqNorm (y - x)) := hspec
      _ ≤ L * Real.sqrt (n : ℝ) * (γ / (8 * L)) := by
        exact mul_le_mul_of_nonneg_left hd' (mul_nonneg (le_of_lt hL) (Real.sqrt_nonneg _))
      _ = γ * Real.sqrt (n : ℝ) / 8 := by
        field_simp [hL.ne']
  have hpart2 : Real.sqrt (((n - 1 : ℕ) : ℝ)) * |c| * |vecSum (y - x)| ≤ γ * Real.sqrt (n : ℝ) / 4 := by
    have hc0 : 0 < |c| := abs_pos.mpr hc
    have hstep : |c| * |vecSum (y - x)| ≤ γ / 4 := by
      calc
        |c| * |vecSum (y - x)| ≤ |c| * (γ / (4 * |c|)) := by
          exact mul_le_mul_of_nonneg_left hs (le_of_lt hc0)
        _ = γ / 4 := by field_simp [hc0.ne']
    have hrows : Real.sqrt (((n - 1 : ℕ) : ℝ)) ≤ Real.sqrt (n : ℝ) := by
      apply Real.sqrt_le_sqrt
      exact_mod_cast (Nat.sub_le n 1 : n - 1 ≤ n)
    have hA : Real.sqrt (n : ℝ) * |c| * |vecSum (y - x)| ≤ Real.sqrt (n : ℝ) * (γ / 4) := by
      have hm := mul_le_mul_of_nonneg_left hstep (Real.sqrt_nonneg (n : ℝ))
      calc
        Real.sqrt (n : ℝ) * |c| * |vecSum (y - x)| = Real.sqrt (n : ℝ) * (|c| * |vecSum (y - x)|) := by ring
        _ ≤ Real.sqrt (n : ℝ) * (γ / 4) := hm
    calc
      Real.sqrt (((n - 1 : ℕ) : ℝ)) * |c| * |vecSum (y - x)| ≤ Real.sqrt (n : ℝ) * |c| * |vecSum (y - x)| := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hrows (abs_nonneg c)) (abs_nonneg _)
      _ ≤ Real.sqrt (n : ℝ) * (γ / 4) := hA
      _ = γ * Real.sqrt (n : ℝ) / 4 := by ring
  have hM : sqrtAct M (y - x) ≤ γ * Real.sqrt (n : ℝ) / 8 + γ * Real.sqrt (n : ℝ) / 4 := by
    calc
      sqrtAct M (y - x) ≤ sqrtAct A (y - x) + Real.sqrt (((n - 1 : ℕ) : ℝ)) * |c| * |vecSum (y - x)| := by
        simpa [M] using hshift
      _ ≤ γ * Real.sqrt (n : ℝ) / 8 + γ * Real.sqrt (n : ℝ) / 4 := by
        linarith [hpart1, hpart2]
  have hM' : sqrtAct M (y - x) ≤ γ * Real.sqrt (n : ℝ) / 2 := by
    have hg : 0 ≤ γ * Real.sqrt (n : ℝ) := mul_nonneg (le_of_lt hγ) (Real.sqrt_nonneg _)
    linarith
  have hmain : sqrtAct M y ≤ (γ / 2) * Real.sqrt (n : ℝ) + (γ / 2) * Real.sqrt (n : ℝ) := by
    calc
      sqrtAct M y ≤ sqrtAct M x + sqrtAct M (y - x) := htri
      _ ≤ (γ / 2) * Real.sqrt (n : ℝ) + γ * Real.sqrt (n : ℝ) / 2 := by
        linarith [hball, hM']
      _ = (γ / 2) * Real.sqrt (n : ℝ) + (γ / 2) * Real.sqrt (n : ℝ) := by ring_nf
  calc
    sqrtAct M y ≤ (γ / 2) * Real.sqrt (n : ℝ) + (γ / 2) * Real.sqrt (n : ℝ) := hmain
    _ = γ * Real.sqrt (n : ℝ) := by ring

/-- Contrapositive of `act_ge_of_sum_ge`: a small ball forces a bounded |Σ x|. -/
lemma sum_lt_of_ball_lt {n : ℕ} (hn2 : 2 ≤ n) (A : Fin (n - 1) → Fin n → ℝ) (c L γ : ℝ)
    (hL : 0 < L) (hγ : 0 < γ) (hc : c ≠ 0)
    (hE : ∀ v : Fin n → ℝ, actSq A v ≤ L ^ 2 * (n : ℝ) * sqNorm v)
    {x : Fin n → ℝ} (hunit : sqNorm x = 1)
    (hball : sqrtAct (shiftRows A c) x < γ * Real.sqrt (n : ℝ)) :
    |vecSum x| < (2 * L + 2 * γ) / |c| := by
  by_contra hnot
  have hge : (2 * L + 2 * γ) / |c| ≤ |vecSum x| := le_of_not_gt hnot
  have h1 := act_ge_of_sum_ge hn2 A c L γ hL hγ hc hE hunit hge
  -- h1 : γ * √n ≤ sqrtAct (shiftRows A c) x
  linarith

/-! ## Slice windows -/

/-- Two numbers in the same half-open window `[w·ℓ, w·(ℓ+1))` differ by less than `w`. -/
lemma abs_sub_lt_of_same_window {w : ℝ} (hw : 0 < w) (ℓ : ℤ) {a b : ℝ}
    (ha₁ : w * (ℓ : ℝ) ≤ a) (ha₂ : a < w * ((ℓ : ℝ) + 1))
    (hb₁ : w * (ℓ : ℝ) ≤ b) (hb₂ : b < w * ((ℓ : ℝ) + 1)) :
    |a - b| < w := by
  have h1 : a - b < w := by
    have ha2' : a - w * (ℓ : ℝ) < w := by
      have hℓ : w * ((ℓ : ℝ) + 1) = w * (ℓ : ℝ) + w := by ring
      linarith
    have hb1' : w * (ℓ : ℝ) ≤ b := hb₁
    nlinarith
  have h2 : b - a < w := by
    have hb2' : b - w * (ℓ : ℝ) < w := by
      have hℓ : w * ((ℓ : ℝ) + 1) = w * (ℓ : ℝ) + w := by ring
      linarith
    have ha1' : w * (ℓ : ℝ) ≤ a := ha₁
    nlinarith
  rw [abs_lt]
  constructor <;> linarith


end

end Submission.Compress
