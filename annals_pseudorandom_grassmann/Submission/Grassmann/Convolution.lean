import Submission.Grassmann.XNormSum

/-!
# The convolution formula for the Fourier transform on `L(V,W)`

The starting point of the §4 analysis of arXiv:2209.04243 (`lem:hyp inductive step`) is the
Parseval identity `E[f⁴] = Σ_X |\widehat{f²}(X)|²`, together with the convolution formula

  `\widehat{f·g}(X) = q^{-mn} Σ_Y f̂(Y) ĝ(X + Y)`.

Both are proved here:

* `mchar_orthogonal_left` — the *dual* orthogonality of the characters,
  `Σ_X u_X(A) u_X(B) = q^{mn}[A = B]` (summing over the indices, with the group elements fixed);
* **`fhat_mul_fun`** — the convolution formula (proved without any triple-sum bookkeeping, by
  writing `f̂ g (X + Y) = f̂ (fun B => g B · u_X(B)) Y` and applying Parseval `fhat_parseval`);
* `sum_normSq_fhat_sq_mul` — `Σ_X ‖\widehat{f²}(X)‖² = q^{2mn} ‖f‖₄⁴`;
* **`l4q_eq_sum_conv`** — the form used in the F₁/F₂ analysis:
  `‖f‖₄⁴ = q^{-4mn} Σ_X ‖Σ_Y f̂(Y) f̂(X+Y)‖²`.
-/

open Finset BigOperators Matrix
open Classical

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Submission.Grassmann

noncomputable section

local notation "𝔽₂" => ZMod 2

/-! ## Elementary facts about matrices over `𝔽₂` -/

lemma mtx_add_self {m n : ℕ} (A : Matrix (Fin m) (Fin n) 𝔽₂) : A + A = 0 := by
  ext i j; exact CharTwo.add_self_eq_zero (A i j)

lemma mtx_neg_eq {m n : ℕ} (A : Matrix (Fin m) (Fin n) 𝔽₂) : -A = A := by
  ext i j; exact CharTwo.neg_eq (A i j)

lemma mtx_add_eq_zero {m n : ℕ} {A B : Matrix (Fin m) (Fin n) 𝔽₂} (h : A + B = 0) :
    A = B := by
  have h1 : A = -B := (add_eq_zero_iff_eq_neg).mp h
  rw [h1, mtx_neg_eq]

/-- **Dual orthogonality of the characters** (summing over the indices). -/
lemma mchar_orthogonal_left {m n : ℕ} (A B : Matrix (Fin m) (Fin n) 𝔽₂) :
    (∑ X : Matrix (Fin n) (Fin m) 𝔽₂, mchar X A * mchar X B) =
      if A = B then (2 : ℂ) ^ (m * n) else 0 := by
  have h : ∀ X : Matrix (Fin n) (Fin m) 𝔽₂, mchar X A * mchar X B = mchar X (A + B) :=
    fun X => (mchar_add_right X A B).symm
  rw [Finset.sum_congr rfl (fun X _ => h X), mchar_sum_left]
  by_cases hAB : A = B
  · subst hAB
    rw [mtx_add_self, if_pos rfl, if_pos rfl]
  · rw [if_neg hAB, if_neg]
    intro hc
    exact hAB (mtx_add_eq_zero hc)

/-- **Convolution of Fourier coefficients**: the Fourier transform of a product is the
(dual) convolution of the Fourier transforms. -/
theorem fhat_mul_fun {m n : ℕ} (f g : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ)
    (X : Matrix (Fin n) (Fin m) 𝔽₂) :
    fhat (fun A => f A * g A) X =
      ((2 : ℂ) ^ (m * n))⁻¹ *
        ∑ Y : Matrix (Fin n) (Fin m) 𝔽₂, fhat f Y * fhat g (X + Y) := by
  have h1 : ∀ Y : Matrix (Fin n) (Fin m) 𝔽₂,
      fhat (fun B => g B * mchar X B) Y = fhat g (X + Y) := by
    intro Y
    rw [fhat, fhat]
    refine Finset.sum_congr rfl fun B _ => ?_
    rw [← mchar_mul]
    ring
  have h2 := fhat_parseval f (fun B => g B * mchar X B)
  have h3 : (∑ Y : Matrix (Fin n) (Fin m) 𝔽₂,
        fhat f Y * fhat (fun B => g B * mchar X B) Y)
      = ∑ Y : Matrix (Fin n) (Fin m) 𝔽₂, fhat f Y * fhat g (X + Y) :=
    Finset.sum_congr rfl fun Y _ => by rw [h1 Y]
  rw [h3] at h2
  calc fhat (fun A => f A * g A) X
      = ∑ A : Matrix (Fin m) (Fin n) 𝔽₂, (f A * g A) * mchar X A := by rw [fhat]
    _ = ∑ A : Matrix (Fin m) (Fin n) 𝔽₂, f A * (g A * mchar X A) :=
        Finset.sum_congr rfl fun A _ => by ring
    _ = ((2 : ℂ) ^ (m * n))⁻¹ *
          ((2 : ℂ) ^ (m * n) * ∑ A : Matrix (Fin m) (Fin n) 𝔽₂, f A * (g A * mchar X A)) := by
        rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ (by norm_num : (2:ℂ) ≠ 0)), one_mul]
    _ = ((2 : ℂ) ^ (m * n))⁻¹ *
          ∑ Y : Matrix (Fin n) (Fin m) 𝔽₂, fhat f Y * fhat g (X + Y) := by rw [h2]

/-- `Σ_X ‖fhat (f·f) X‖² = 2^{2mn} l4q f`. -/
theorem sum_normSq_fhat_sq_mul {m n : ℕ} (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    (∑ X : Matrix (Fin n) (Fin m) 𝔽₂, ‖fhat (fun A => f A * f A) X‖ ^ 2) =
      ((2 : ℝ) ^ (m * n)) ^ 2 * l4q f := by
  rw [fhat_parseval_normSq]
  have hA : ∀ A : Matrix (Fin m) (Fin n) 𝔽₂, ‖f A * f A‖ ^ 2 = ‖f A‖ ^ 4 := by
    intro A
    rw [norm_mul, mul_pow]
    ring
  rw [Finset.sum_congr rfl (fun A _ => hA A), l4q]
  field_simp

/-- **The `l4q` form used in the F₁/F₂ analysis**: the fourth-power norm of `f` is the sum over
characters of the squared modulus of the convolution of the Fourier coefficients. -/
theorem l4q_eq_sum_conv {m n : ℕ} (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    l4q f = (((2 : ℝ) ^ (m * n)) ^ 4)⁻¹ *
      ∑ X : Matrix (Fin n) (Fin m) 𝔽₂,
        ‖∑ Y : Matrix (Fin n) (Fin m) 𝔽₂, fhat f Y * fhat f (X + Y)‖ ^ 2 := by
  set c : ℝ := ((2 : ℝ) ^ (m * n)) ^ 2 with hcdef
  have hc : ‖((2 : ℂ) ^ (m * n))⁻¹‖ ^ 2 = c⁻¹ := by
    rw [norm_inv, norm_pow, show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num, inv_pow, hcdef]
  have hstep : ∀ X : Matrix (Fin n) (Fin m) 𝔽₂,
      ‖fhat (fun A => f A * f A) X‖ ^ 2 =
        c⁻¹ * ‖∑ Y : Matrix (Fin n) (Fin m) 𝔽₂, fhat f Y * fhat f (X + Y)‖ ^ 2 := by
    intro X
    rw [fhat_mul_fun f f X, norm_mul, mul_pow, hc]
  have h1 : l4q f = c⁻¹ * ∑ X : Matrix (Fin n) (Fin m) 𝔽₂,
      ‖fhat (fun A => f A * f A) X‖ ^ 2 := by
    rw [sum_normSq_fhat_sq_mul, hcdef]
    field_simp
  rw [h1, Finset.sum_congr rfl (fun X _ => hstep X), ← Finset.mul_sum]
  have hkey : c⁻¹ * (c⁻¹ * ∑ X : Matrix (Fin n) (Fin m) 𝔽₂,
        ‖∑ Y : Matrix (Fin n) (Fin m) 𝔽₂, fhat f Y * fhat f (X + Y)‖ ^ 2) =
      (((2 : ℝ) ^ (m * n)) ^ 4)⁻¹ * ∑ X : Matrix (Fin n) (Fin m) 𝔽₂,
        ‖∑ Y : Matrix (Fin n) (Fin m) 𝔽₂, fhat f Y * fhat f (X + Y)‖ ^ 2 := by
    rw [hcdef]
    field_simp
  exact hkey



/-- **The Fourier coefficients of the square of a Fourier multiplier.**  The coefficient of
`X` in `(L_P f)²` receives a contribution from the pair `(Y, X + Y)` exactly when both `Y` and
`X + Y` are kept by `P` (this is the algebraic content of the paper's classification of the
pairs `(Y,Z)` into `𝓕₁(X)` and `𝓕₂(X)`). -/
theorem fhat_sq_lapMulN {m n : ℕ} (P : Matrix (Fin n) (Fin m) 𝔽₂ → Prop)
    (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) (X : Matrix (Fin n) (Fin m) 𝔽₂) :
    fhat (fun A => lapMulN P f A * lapMulN P f A) X =
      ((2 : ℂ) ^ (m * n))⁻¹ *
        ∑ Y : Matrix (Fin n) (Fin m) 𝔽₂,
          ((if P Y then (1 : ℂ) else 0) * fhat f Y) *
            ((if P (X + Y) then (1 : ℂ) else 0) * fhat f (X + Y)) := by
  rw [fhat_mul_fun]
  congr 1
  refine Finset.sum_congr rfl fun Y _ => ?_
  rw [fhat_lapMulN, fhat_lapMulN]

end

end Submission.Grassmann
