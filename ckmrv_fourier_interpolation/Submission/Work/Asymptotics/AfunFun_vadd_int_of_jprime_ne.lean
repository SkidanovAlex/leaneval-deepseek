/-
# The value of the cleared kernel at the translate `z + n` of its first variable

The cleared kernel `AfunFun ℓ d τ z = (K_+^{cl}(τ,z) + K_-^{cl}(τ,z)) / (2 Δ(τ) Δ(z)^e)` of
CKMRV is holomorphic in `(τ,z)` and off the divisor `j(τ) = j(z)` equals
`K^{(d)}(τ,z)·(j(τ) - j(z))`.  Its values at the points of the orbit (`z = γτ`) are the
"residue values" of the kernel: at the translate `z = τ - n` one has

  `AfunFun ℓ d τ (τ - n) = -(n/2π)·j'(τ - n)`

(`AfunFun_vadd_one` for `n = 1`, `AfunMinus_neg_one` for `n = -1`).  This file proves the
statement for every `n : ℤ`, in the equivalent form

  `AfunFun ℓ d (((n : ℤ) : ℝ) +ᵥ τ) τ = (n/2π)·j'(τ)`

(or, renaming `τ ↦ z + n`, `AfunFun ℓ d τ (((n : ℤ) : ℝ) +ᵥ τ) = (n/2π)·j'(((n : ℤ) : ℝ) +ᵥ τ)`),
which is the value identity used in Section 5 of the paper.

## Method

The proof uses the *functional equation* `K^{(d)}(·,z) |^τ_{d/2} (T - I)² = 0` of
Theorem 4.9(2) in its cleared form

  `F(τ+2) - 2F(τ+1) + F(τ) = 0` for `F = K_±^{cl}(·,z)`

(`KPlusClear_T2_aux`, `KMinusClear_T2`).  Dividing by the `T`-periodic factor
`2Δ(τ)Δ(z)^e` shows that `τ ↦ AfunFun ℓ d τ z` satisfies the same second-order difference
equation; a sequence on `ℤ` with vanishing second difference is affine, so for fixed `z` the
sequence `m ↦ AfunFun ℓ d (z+m) z` is affine, and its two initial values
`AfunFun ℓ d z z = 0` (`KPlusClear_diag`, `KMinusClear_diag`) and
`AfunFun ℓ d (z+1) z = -(1/2π)j'(z)` (`AfunFun_vadd_one`) give the formula for all `m : ℤ`.
No hypothesis on `j'` is needed; in particular the elliptic points cause no difficulty.
-/
import Mathlib
import Submission.Work.Asymptotics.KfunAuxDefs
import Submission.Work.Asymptotics.bad_line_slice_simple_zero
import Submission.Work.Residues.AfunMinus_neg_one

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups Manifold

namespace Work.Asymptotics

open Work.Kernels Work.Residues

/-! ## A sequence on `ℤ` with vanishing second difference is affine -/

/-- If `f : ℤ → ℂ` satisfies the second-order recurrence `f (m+2) - 2 f (m+1) + f m = 0`
for all `m`, then `f` is affine: `f m = f 0 + m (f 1 - f 0)`. -/
lemma eq_affine_of_secondDifference {f : ℤ → ℂ}
    (h : ∀ m : ℤ, f (m + 2) - 2 * f (m + 1) + f m = 0) :
    ∀ m : ℤ, f m = f 0 + (m : ℂ) * (f 1 - f 0) := by
  have key : ∀ m : ℤ, f m = f 0 + (m : ℂ) * (f 1 - f 0)
      ∧ f (m + 1) = f 0 + ((m + 1 : ℤ) : ℂ) * (f 1 - f 0) := by
    intro m
    induction m using Int.induction_on with
    | zero =>
        refine ⟨by simp, ?_⟩
        push_cast
        ring
    | succ n ih =>
        obtain ⟨h1, h2⟩ := ih
        refine ⟨h2, ?_⟩
        have hh := h (n : ℤ)
        rw [show (n : ℤ) + 1 + 1 = (n : ℤ) + 2 from by ring] at ⊢
        have hval : f ((n : ℤ) + 2) = f 0 + (((n : ℤ) + 2 : ℤ) : ℂ) * (f 1 - f 0) := by
          rw [show f ((n : ℤ) + 2) = 2 * f ((n : ℤ) + 1) - f (n : ℤ) from by
                linear_combination hh,
            h2, h1]
          push_cast
          ring
        exact hval
    | pred n ih =>
        obtain ⟨h1, h2⟩ := ih
        refine ⟨?_, ?_⟩
        · have hh := h (-(n : ℤ) - 1)
          rw [show (-(n : ℤ) - 1) + 2 = -(n : ℤ) + 1 from by ring,
            show (-(n : ℤ) - 1) + 1 = -(n : ℤ) from by ring] at hh
          have hval : f (-(n : ℤ) - 1) = f 0 + ((-(n : ℤ) - 1 : ℤ) : ℂ) * (f 1 - f 0) := by
            rw [show f (-(n : ℤ) - 1) = 2 * f (-(n : ℤ)) - f (-(n : ℤ) + 1) from by
                  linear_combination hh,
              h1, h2]
            push_cast
            ring
          exact hval
        · rw [show (-(n : ℤ) - 1) + 1 = -(n : ℤ) from by ring]
          exact h1
  intro m
  exact (key m).1

/-! ## The cleared kernel as a product with a `T`-periodic factor -/

/-- If `N` is killed by `(T-I)²` and `G` is `T`-periodic, then so is `N/G`. -/
lemma T2op_div_of {N G : ℍ → ℂ} (hN : T2op N = 0)
    (hG : ∀ τ : ℍ, G ((1 : ℝ) +ᵥ τ) = G τ) :
    T2op (fun τ : ℍ => N τ / G τ) = 0 := by
  funext τ
  have h0 := congr_fun hN τ
  have h2 : G ((2 : ℝ) +ᵥ τ) = G τ := by
    rw [vadd_one_add_one, hG ((1 : ℝ) +ᵥ τ), hG τ]
  simp only [T2op, Pi.zero_apply] at h0
  simp only [T2op, Pi.zero_apply, h2, hG τ, div_eq_mul_inv]
  linear_combination (G τ)⁻¹ * h0

/-- **`(T-I)²` annihilates `AfunFun` in its first variable.** -/
lemma T2op_AfunFun_fst (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (z : ℍ) :
    T2op (fun τ : ℍ => AfunFun ℓ d τ z) = 0 := by
  have hN : T2op (fun τ : ℍ => KPlusClear d τ z + KMinusClear ℓ d τ z) = 0 :=
    T2op_add (KPlusClear_T2_aux d hd z)
      (Work.Residues.AfunMinusNegOne.KMinusClear_T2 ℓ d hd z)
  set G : ℍ → ℂ := fun τ => 2 * (DeltaFun τ * DeltaFun z ^ dpow d) with hGdef
  have hG : ∀ τ : ℍ, G ((1 : ℝ) +ᵥ τ) = G τ := by
    intro τ
    simp only [hGdef, KernelFacts.DeltaFun_vadd_one]
  have h := T2op_div_of hN hG
  rw [show (fun τ : ℍ => AfunFun ℓ d τ z)
      = (fun τ : ℍ => (KPlusClear d τ z + KMinusClear ℓ d τ z) / G τ) from by
        funext τ
        rw [AfunFun, AfunPlus, AfunMinus]
        ring]
  exact h

/-- `AfunFun` vanishes on the diagonal `τ = z`. -/
lemma AfunFun_diag (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (z : ℍ) :
    AfunFun ℓ d z z = 0 := by
  rw [AfunFun, AfunPlus, AfunMinus, KPlusClear_diag d hd z, KMinusClear_diag ℓ d hd z]
  simp

/-! ## The translate identity -/

lemma vadd_int_add_one (m : ℤ) (z : ℍ) :
    (1 : ℝ) +ᵥ (((m : ℤ) : ℝ) +ᵥ z) = (((m + 1 : ℤ)) : ℝ) +ᵥ z := by
  apply UpperHalfPlane.ext
  simp only [UpperHalfPlane.coe_vadd]
  push_cast
  ring

lemma vadd_int_add_two (m : ℤ) (z : ℍ) :
    (2 : ℝ) +ᵥ (((m : ℤ) : ℝ) +ᵥ z) = (((m + 2 : ℤ)) : ℝ) +ᵥ z := by
  apply UpperHalfPlane.ext
  simp only [UpperHalfPlane.coe_vadd]
  push_cast
  ring

/-- **The value identity at every translate of the first variable.**
For every `z ∈ ℍ` and `m : ℤ`, `AfunFun ℓ d (z + m) z = m·(-(1/2π))·j'(z)`. -/
lemma AfunFun_vadd_int (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (z : ℍ) (m : ℤ) :
    AfunFun ℓ d (((m : ℤ) : ℝ) +ᵥ z) z
      = (m : ℂ) * (-(1 / (2 * Real.pi))) * jprime z := by
  have hrec : ∀ k : ℤ,
      AfunFun ℓ d (((k + 2 : ℤ) : ℝ) +ᵥ z) z
        - 2 * AfunFun ℓ d (((k + 1 : ℤ) : ℝ) +ᵥ z) z
        + AfunFun ℓ d (((k : ℤ) : ℝ) +ᵥ z) z = 0 := by
    intro k
    have hT2 := congr_fun (T2op_AfunFun_fst ℓ d hd z) (((k : ℤ) : ℝ) +ᵥ z)
    simp only [T2op, Pi.zero_apply] at hT2
    rw [vadd_int_add_two k z, vadd_int_add_one k z] at hT2
    exact hT2
  have hmain := eq_affine_of_secondDifference
    (f := fun k : ℤ => AfunFun ℓ d (((k : ℤ) : ℝ) +ᵥ z) z) hrec m
  have h0 : AfunFun ℓ d (((0 : ℤ) : ℝ) +ᵥ z) z = 0 := by
    rw [show ((0 : ℤ) : ℝ) = 0 from by norm_num, zero_vadd]
    exact AfunFun_diag ℓ d hd z
  have h1 : AfunFun ℓ d (((1 : ℤ) : ℝ) +ᵥ z) z = -(1 / (2 * Real.pi)) * jprime z := by
    rw [show ((1 : ℤ) : ℝ) = 1 from by norm_num]
    exact AfunFun_vadd_one ℓ d hd z
  rw [hmain, h0, h1]
  ring

/-- **The value identity at the translate `τ + n` of the kernel variable.**
For `d ∈ {8,24}`, `τ ∈ ℍ`, `n : ℤ`,

  `AfunFun ℓ d τ (τ + n) = (n/2π)·j'(τ + n).` -/
theorem AfunFun_vadd_int_of_jprime_ne (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) (τ : UpperHalfPlane) (n : ℤ)
    (hne : Work.Residues.jprime τ ≠ 0) :
    Work.Asymptotics.AfunFun ℓ d τ (((n : ℤ) : ℝ) +ᵥ τ)
      = ((n : ℂ) / (2 * (Real.pi : ℂ))) * Work.Residues.jprime ((((n : ℤ) : ℝ) +ᵥ τ)) := by
  have _ := hne
  have h := AfunFun_vadd_int ℓ d hd (((n : ℤ) : ℝ) +ᵥ τ) (-n)
  have hpt : (((-n : ℤ) : ℝ) +ᵥ (((n : ℤ) : ℝ) +ᵥ τ)) = τ := by
    rw [← add_vadd]
    have hsum : ((-n : ℤ) : ℝ) + ((n : ℤ) : ℝ) = 0 := by push_cast; ring
    rw [hsum, zero_vadd]
  rw [hpt] at h
  rw [h]
  push_cast
  ring

end Work.Asymptotics
