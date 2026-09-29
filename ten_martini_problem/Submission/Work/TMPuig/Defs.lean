/-
# Puig's argument (C12 of the Ten Martini contract): shared definitions and basic lemmas
-/
import Submission.Work.TMContract.Components

open Matrix
open scoped Matrix

noncomputable section

namespace Work.TMPuig

open Work.TMContract

/-! ## 1. Rotations (angles in turns) -/

/-- `rot` is `1`-periodic. -/
theorem rot_add_one (c : ℝ) : rot (c + 1) = rot c := by
  have h : 2 * Real.pi * (c + 1) = 2 * Real.pi * c + 2 * Real.pi := by ring
  have hc : Real.cos (2 * Real.pi * (c + 1)) = Real.cos (2 * Real.pi * c) := by
    rw [h, Real.cos_add, Real.cos_two_pi, Real.sin_two_pi]; ring
  have hs : Real.sin (2 * Real.pi * (c + 1)) = Real.sin (2 * Real.pi * c) := by
    rw [h, Real.sin_add, Real.cos_two_pi, Real.sin_two_pi]; ring
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [rot, hc, hs]

/-- `rot n = 1` for an integer number of turns. -/
theorem rot_int (n : ℤ) : rot (n : ℝ) = 1 := by
  have hc : Real.cos (2 * Real.pi * (n : ℝ)) = 1 := by
    rw [show 2 * Real.pi * (n : ℝ) = (n : ℝ) * (2 * Real.pi) by ring, Real.cos_int_mul_two_pi]
  have hs : Real.sin (2 * Real.pi * (n : ℝ)) = 0 := by
    rw [Real.sin_eq_zero_iff]; exact ⟨2 * n, by push_cast; ring⟩
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [rot, hc, hs]

/-- `rot` is a homomorphism `ℝ → SL(2,ℝ)`. -/
theorem rot_add (a b : ℝ) : rot (a + b) = rot a * rot b := by
  have hc : Real.cos (2 * Real.pi * (a + b))
      = Real.cos (2 * Real.pi * a) * Real.cos (2 * Real.pi * b)
        - Real.sin (2 * Real.pi * a) * Real.sin (2 * Real.pi * b) := by
    rw [show 2 * Real.pi * (a+b) = 2 * Real.pi * a + 2 * Real.pi * b by ring, Real.cos_add]
  have hs : Real.sin (2 * Real.pi * (a + b))
      = Real.sin (2 * Real.pi * a) * Real.cos (2 * Real.pi * b)
        + Real.cos (2 * Real.pi * a) * Real.sin (2 * Real.pi * b) := by
    rw [show 2 * Real.pi * (a+b) = 2 * Real.pi * a + 2 * Real.pi * b by ring, Real.sin_add]
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [rot, Matrix.mul_apply, Fin.sum_univ_two, hc, hs] <;> ring

theorem det_rot (a : ℝ) : (rot a).det = 1 := by
  rw [Matrix.det_fin_two]
  simp [rot]
  nlinarith [Real.cos_sq_add_sin_sq (2 * Real.pi * a)]

/-! ## 2. The real transfer matrix -/

/-- The transfer matrix is affine in the energy. -/
theorem tmR_sub_tmR (lam E₁ E₂ x : ℝ) :
    tmR lam E₂ x - tmR lam E₁ x = (E₂ - E₁) • (!![(1 : ℝ), 0; 0, 0]) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [tmR]

/-- The free transfer matrix at phase `0` is the quarter-turn. -/
theorem tmR_zero_zero_zero : tmR 0 0 0 = rot (1 / 4) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp only [tmR, rot] <;>
    rw [show 2 * Real.pi * (1/4) = Real.pi / 2 by ring] <;>
    simp [Real.cos_pi_div_two, Real.sin_pi_div_two]

/-- The `(0,0)` entry of the transfer matrix. -/
theorem tmR_apply_zero_zero (lam E x : ℝ) :
    tmR lam E x 0 0 = E - 2 * lam * Real.cos (2 * Real.pi * x) := by
  simp [tmR]

/-- The `n`-th iterate of the real transfer matrix (real version of `iterC`). -/
def iterR (α lam E : ℝ) : ℕ → ℝ → Matrix (Fin 2) (Fin 2) ℝ
  | 0, _ => 1
  | n + 1, x => tmR lam E (x + (n : ℝ) * α) * iterR α lam E n x

@[simp] theorem iterR_zero (α lam E : ℝ) (x : ℝ) : iterR α lam E 0 x = 1 := rfl

theorem iterR_succ (α lam E : ℝ) (n : ℕ) (x : ℝ) :
    iterR α lam E (n + 1) x = tmR lam E (x + (n : ℝ) * α) * iterR α lam E n x := rfl

/-! ## 3. Conjugacy of the cocycle -/

/-- The one-step consequence of a conjugacy `B(x+α) S(x) = R B(x)`. -/
theorem tmR_conj_step {α lam E : ℝ} {B : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    {R : Matrix (Fin 2) (Fin 2) ℝ} (hinv : ∀ x, IsUnit (B x).det)
    (hconj : ∀ x, B (x + α) * tmR lam E x = R * B x) (x : ℝ) :
    tmR lam E x * (B x)⁻¹ = (B (x + α))⁻¹ * R := by
  have h1 : B (x + α) * tmR lam E x * (B x)⁻¹ = R * (B x * (B x)⁻¹) := by
    rw [hconj x]; simp only [mul_assoc]
  rw [Matrix.mul_nonsing_inv _ (hinv x), mul_one] at h1
  have h2 : B (x + α) * (tmR lam E x * (B x)⁻¹) = R := by rw [← mul_assoc]; exact h1
  calc tmR lam E x * (B x)⁻¹
      = (B (x + α))⁻¹ * (B (x + α) * (tmR lam E x * (B x)⁻¹)) := by
        rw [Matrix.nonsing_inv_mul_cancel_left _ _ (hinv (x + α))]
    _ = (B (x + α))⁻¹ * R := by rw [h2]

/-- **Conjugacy of the cocycle.**  If `B(x+α) S_E(x) = R B(x)` with `B(x)` invertible, then
the `n`-th iterate of the cocycle is `B(x+nα)⁻¹ Rⁿ B(x)`. -/
theorem iterR_conj (α lam E : ℝ) (B : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (R : Matrix (Fin 2) (Fin 2) ℝ) (hinv : ∀ x, IsUnit (B x).det)
    (hconj : ∀ x, B (x + α) * tmR lam E x = R * B x) (n : ℕ) (x : ℝ) :
    iterR α lam E n x = (B (x + n * α))⁻¹ * R ^ n * B x := by
  induction n with
  | zero =>
      simp only [iterR_zero, Nat.cast_zero, zero_mul, add_zero, pow_zero, mul_one]
      rw [Matrix.nonsing_inv_mul _ (hinv x)]
  | succ n ih =>
      have hB : x + (n : ℝ) * α + α = x + (n + 1 : ℕ) * α := by push_cast; ring
      rw [iterR_succ, ih]
      rw [← mul_assoc (tmR lam E (x + (n:ℝ)*α)) ((B (x + (n:ℝ)*α))⁻¹ * R^n) (B x)]
      rw [← mul_assoc, tmR_conj_step hinv hconj (x + (n:ℝ)*α), mul_assoc, hB, pow_succ']
      simp only [mul_assoc]

/-! ## 4. The reducibility datum -/

/-- The reducibility datum appearing in `RedSet`: an analytic `1`-periodic
`SL(2,ℝ)`-valued function `B` conjugating the cocycle at energy `E` to the constant
rotation by `c` (angles in turns). -/
def HasRedDatum (α lam E c : ℝ) : Prop :=
  ∃ B : ℝ → Matrix (Fin 2) (Fin 2) ℝ,
    (∀ i j, AnalyticOnNhd ℝ (fun x => B x i j) Set.univ) ∧ (∀ x, B (x + 1) = B x) ∧
    (∀ x, (B x).det = 1) ∧ (∀ x, B (x + α) * tmR lam E x = rot c * B x)

end Work.TMPuig

