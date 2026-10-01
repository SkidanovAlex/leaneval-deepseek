/-
# ZeroFreeTables/P9/Defs — the auxiliary notions of the `P9` (HB §9) engine
-/
import Mathlib
import Submission.Work.ZeroFreeTables.P3.DefsL
import Submission.Work.ZeroFreeTables.P3.P3Bounds

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables.P9

/-- The indicator of the near set `‖1 + i·Im s - u‖ ≤ δ`, as a real number. -/
def nearInd (s : ℂ) (δ : ℝ) (u : ℂ) : ℝ :=
  if ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ then 1 else 0

lemma nearInd_nonneg (s : ℂ) (δ : ℝ) (u : ℂ) : 0 ≤ nearInd s δ u := by
  unfold nearInd; split <;> norm_num

lemma nearInd_le_one (s : ℂ) (δ : ℝ) (u : ℂ) : nearInd s δ u ≤ 1 := by
  unfold nearInd; split <;> norm_num

lemma nearInd_eq_ite (s : ℂ) (δ : ℝ) (u : ℂ) :
    nearInd s δ u = if ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ then 1 else 0 := rfl

lemma ite_nearInd (s : ℂ) (δ : ℝ) (u : ℂ) (x : ℝ) :
    (if ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ then x else 0) = nearInd s δ u * x := by
  unfold nearInd
  by_cases h : ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ <;> simp [h]

/-- The near-zero sum of `Re P₃(α/((s-u)L))` over the zeros of `L(·,χ)`, `α = a + λ₁`, written
through the three terms of `P₃`. -/
def nearP3sum (N : ℕ) [NeZero N] (L : ℝ) (χ : DirichletCharacter ℂ N) (s : ℂ)
    (a lam₁ δ : ℝ) : ℝ :=
  ∑' u : ℂ, (Work.LinnikContract.zeroMult χ u : ℝ) * nearInd s δ u *
    ( ((a + lam₁) / L) * ((1 / (s - u))).re
      + ((a + lam₁) / L) ^ 2 * ((1 / (s - u)) ^ 2).re
      + (2 / 3) * ((a + lam₁) / L) ^ 3 * ((1 / (s - u)) ^ 3).re)

/-- The near-zero sum of `Re (1/(s-u))` (the `k = 1` term of the `P₃` sum). -/
def nearInvSum (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ) (δ : ℝ) : ℝ :=
  ∑' u : ℂ, (Work.LinnikContract.zeroMult χ u : ℝ) * nearInd s δ u * ((1 / (s - u)).re)

/-- The multiplicity-weighted inverse-square zero sum. -/
def invSqSum (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ) : ℝ :=
  ∑' u : ℂ, (Work.LinnikContract.zeroMult χ u : ℝ) * (1 / (1 + ‖s - u‖ ^ 2))

lemma ofReal_mul_re' (r : ℝ) (z : ℂ) : ((r : ℂ) * z).re = r * z.re := by
  simp [Complex.mul_re]

/-- The real part of `P₃(A·w)` as a combination of `Re (w^k)`, `k = 1,2,3`. -/
lemma P3_re_mul_inv (A : ℝ) (w : ℂ) :
    (Work.ZeroFreeTables.P3 ((A : ℂ) * w)).re
      = A * w.re + A ^ 2 * (w ^ 2).re + (2 / 3) * A ^ 3 * (w ^ 3).re := by
  have h : Work.ZeroFreeTables.P3 ((A : ℂ) * w)
      = (A : ℂ) * w + (((A ^ 2 : ℝ)) : ℂ) * w ^ 2
        + ((((2 : ℝ) / 3) * A ^ 3 : ℝ) : ℂ) * w ^ 3 := by
    unfold Work.ZeroFreeTables.P3
    push_cast
    ring
  rw [h, Complex.add_re, Complex.add_re, ofReal_mul_re', ofReal_mul_re', ofReal_mul_re']

/-- The argument identity `(a+λ₁)/((s-u)L) = ((a+λ₁)/L)·(1/(s-u))`. -/
lemma P3_arg_eq (a lam₁ L : ℝ) (s u : ℂ) :
    (a + lam₁) / ((s - u) * (L : ℂ)) = (((a + lam₁) / L : ℝ) : ℂ) * (1 / (s - u)) := by
  have h : (((a + lam₁) / L : ℝ) : ℂ) = (a + lam₁) / (L : ℂ) := by push_cast; ring
  rw [h, div_eq_mul_inv, div_eq_mul_inv, one_div, mul_inv_rev]
  ring

/-- `Re P₃(α/((s-u)L))` in the three-term form. -/
lemma P3_re_div_eq (a lam₁ L : ℝ) (s u : ℂ) :
    (Work.ZeroFreeTables.P3 ((a + lam₁) / ((s - u) * (L : ℂ)))).re
      = ((a + lam₁) / L) * ((1 / (s - u))).re
        + ((a + lam₁) / L) ^ 2 * ((1 / (s - u)) ^ 2).re
        + (2 / 3) * ((a + lam₁) / L) ^ 3 * ((1 / (s - u)) ^ 3).re := by
  rw [P3_arg_eq, P3_re_mul_inv]

/-- `Φ(x,y,t) = Re P₃(x/(y+it))`. -/
def PhiG (x y t : ℝ) : ℝ :=
  (Work.ZeroFreeTables.P3 (((x : ℂ)) / ((y : ℂ) + (t : ℂ) * Complex.I))).re

/-- `0 ≤ Φ(x,y,t)` for `0 < x ≤ y`. -/
lemma PhiG_nonneg {x y t : ℝ} (hx : 0 < x) (hxy : x ≤ y) : 0 ≤ PhiG x y t :=
  Work.ZeroFreeTables.P3.P3Bounds.1 x y t hx hxy

end Work.ZeroFreeTables.P9
