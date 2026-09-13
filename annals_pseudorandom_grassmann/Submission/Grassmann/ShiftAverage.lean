import Submission.Grassmann.SmallInfl
import Submission.Grassmann.EOp

/-!
# The average of the influence over the shift `T`

For a fixed pair of subspaces `(V₁,W₁) = (ker Q, range ι)`, the paper's derivative
`D_{V₁,W₁,T}[f] = (L_{V₁,W₁}[f])_{(V₁,W₁)→T}` is the `T`-restriction of the hybrid Laplacian
of `f`.  Averaging its squared `L²` norm over the shift `T` gives back the squared `L²` norm
of the hybrid Laplacian:

  `E_T ‖D_{V₁,W₁,T}[f]‖₂² = ‖L_{V₁,W₁}[f]‖₂²`,

which is the step

  `E_T ‖D_T f‖₂² = ‖L_{V₁,W₁}[f]‖₂²`

in the proof of the paper's `cor:Corollary of hypercontractivity` (`ShiftAverage.sum_l2sq_restr_shift`,
`sum_inflBS2_eq`).  Combining it with the small-influence hypothesis bounds the averaged *fourth*
power by `ε` times the averaged square (`sum_sq_inflBS2_le_of_smallInfl`), which is the only place
the generalised influences enter the derivation of `cor:atmostd`/`HypCor4`.

The argument for the shift average is elementary: both `restr` and `shift` just evaluate `g`
at `ι * A * Q + T`, so averaging over `A` (a bijection onto the coset of `T`) and then over `T`
(a translation invariant average on `L(V,W)`) recovers the total mass of `g`.
-/

open Finset BigOperators Matrix
open Classical

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Submission.Grassmann

noncomputable section

local notation "𝔽₂" => ZMod 2

/-! ## Elementary counting lemmas -/

/-- The number of `m × n` matrices over `𝔽₂` is `2^{mn}` (as a `Fintype.card`). -/
lemma fintype_card_matrix_zmod_two (m n : ℕ) :
    Fintype.card (Matrix (Fin m) (Fin n) 𝔽₂) = 2 ^ (m * n) := by
  rw [← Nat.card_eq_fintype_card, natCard_matrix_zmod_two]

/-- **Total mass.** The sum of the pointwise squared norms of `g` over the whole space is
`2^{mn}` times its normalised squared `L²` norm. -/
lemma sum_normSq_eq {m n : ℕ} (g : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    (∑ T : Matrix (Fin m) (Fin n) 𝔽₂, ‖g T‖ ^ 2) = (2 : ℝ) ^ (m * n) * l2sq g := by
  rw [l2sq, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ (by norm_num : (2:ℝ) ≠ 0)), one_mul]

/-- **Translation invariance of the total mass.** -/
lemma sum_normSq_shift_comp {m n : ℕ} (g : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ)
    (B : Matrix (Fin m) (Fin n) 𝔽₂) :
    (∑ T : Matrix (Fin m) (Fin n) 𝔽₂, ‖g (B + T)‖ ^ 2) =
      ∑ T : Matrix (Fin m) (Fin n) 𝔽₂, ‖g T‖ ^ 2 := by
  refine Fintype.sum_equiv (Equiv.addLeft B) (fun T => ‖g (B + T)‖ ^ 2)
    (fun T => ‖g T‖ ^ 2) fun T => ?_
  simp [Equiv.addLeft]

/-! ## The shift average of a restriction -/

/-- `restr` followed by `shift` evaluates `g` at `ι * A * Q + T`. -/
lemma restr_shift_apply {m n m' n' : ℕ} (Q : Matrix (Fin n') (Fin n) 𝔽₂)
    (ι : Matrix (Fin m) (Fin m') 𝔽₂) (T : Matrix (Fin m) (Fin n) 𝔽₂)
    (g : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) (A : Matrix (Fin m') (Fin n') 𝔽₂) :
    restr Q ι (shift T g) A = g (ι * A * Q + T) := rfl

/-- **The shift average of the squared norm of a restriction.**  Averaging
`‖g_{(V₁,W₁)→T}‖₂²` over the shift `T ∈ L(V,W)` recovers the total mass of `g`. -/
theorem sum_l2sq_restr_shift {m n m' n' : ℕ} (Q : Matrix (Fin n') (Fin n) 𝔽₂)
    (ι : Matrix (Fin m) (Fin m') 𝔽₂) (g : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    (∑ T : Matrix (Fin m) (Fin n) 𝔽₂, l2sq (restr Q ι (shift T g))) =
      (2 : ℝ) ^ (m * n) * l2sq g := by
  have h1 : ∀ T : Matrix (Fin m) (Fin n) 𝔽₂,
      l2sq (restr Q ι (shift T g)) =
        ((2 : ℝ) ^ (m' * n'))⁻¹ * ∑ A : Matrix (Fin m') (Fin n') 𝔽₂,
          ‖g (ι * A * Q + T)‖ ^ 2 := by
    intro T
    simp only [l2sq, restr, shift]
  have h2 : (∑ T : Matrix (Fin m) (Fin n) 𝔽₂,
        ((2 : ℝ) ^ (m' * n'))⁻¹ * ∑ A : Matrix (Fin m') (Fin n') 𝔽₂,
          ‖g (ι * A * Q + T)‖ ^ 2)
      = ((2 : ℝ) ^ (m' * n'))⁻¹ *
        ∑ T : Matrix (Fin m) (Fin n) 𝔽₂, ∑ A : Matrix (Fin m') (Fin n') 𝔽₂,
          ‖g (ι * A * Q + T)‖ ^ 2 := by
    simp only [Finset.mul_sum]
  have h3 : (∑ A : Matrix (Fin m') (Fin n') 𝔽₂, ∑ T : Matrix (Fin m) (Fin n) 𝔽₂,
        ‖g (ι * A * Q + T)‖ ^ 2)
      = ∑ _A : Matrix (Fin m') (Fin n') 𝔽₂, (2 : ℝ) ^ (m * n) * l2sq g := by
    refine Finset.sum_congr rfl fun A _ => ?_
    rw [sum_normSq_shift_comp g (ι * A * Q), sum_normSq_eq]
  calc (∑ T : Matrix (Fin m) (Fin n) 𝔽₂, l2sq (restr Q ι (shift T g)))
      = ∑ T : Matrix (Fin m) (Fin n) 𝔽₂,
          ((2 : ℝ) ^ (m' * n'))⁻¹ * ∑ A : Matrix (Fin m') (Fin n') 𝔽₂,
            ‖g (ι * A * Q + T)‖ ^ 2 := Finset.sum_congr rfl fun T _ => h1 T
    _ = ((2 : ℝ) ^ (m' * n'))⁻¹ *
          ∑ T : Matrix (Fin m) (Fin n) 𝔽₂, ∑ A : Matrix (Fin m') (Fin n') 𝔽₂,
            ‖g (ι * A * Q + T)‖ ^ 2 := h2
    _ = ((2 : ℝ) ^ (m' * n'))⁻¹ *
          ∑ A : Matrix (Fin m') (Fin n') 𝔽₂, ∑ T : Matrix (Fin m) (Fin n) 𝔽₂,
            ‖g (ι * A * Q + T)‖ ^ 2 := by rw [Finset.sum_comm]
    _ = ((2 : ℝ) ^ (m' * n'))⁻¹ *
          ∑ _A : Matrix (Fin m') (Fin n') 𝔽₂, (2 : ℝ) ^ (m * n) * l2sq g := by rw [h3]
    _ = (2 : ℝ) ^ (m * n) * l2sq g := by
        rw [Finset.sum_const, Finset.card_univ, fintype_card_matrix_zmod_two, nsmul_eq_mul]
        push_cast
        rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ (by norm_num : (2:ℝ) ≠ 0)), one_mul]

/-! ## The averaged influence is the squared norm of the hybrid Laplacian -/

/-- **`E_T ‖D_{V₁,W₁,T}[f]‖₂² = ‖L_{V₁,W₁}[f]‖₂²`.** -/
theorem sum_inflBS2_eq {m n : ℕ} {m' n' : ℕ} (Q : Matrix (Fin n') (Fin n) 𝔽₂)
    (ι : Matrix (Fin m) (Fin m') 𝔽₂) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    (∑ T : Matrix (Fin m) (Fin n) 𝔽₂,
        l2sq (restr Q ι (shift T (lapMulN (hybridPred Q ι) f)))) =
      (2 : ℝ) ^ (m * n) * l2sq (lapMulN (hybridPred Q ι) f) :=
  sum_l2sq_restr_shift Q ι _

/-- **The small-influence hypothesis bounds the averaged fourth power by `ε` times the
averaged square**: the pointwise bound `inflBS2 ≤ ε` and nonnegativity give
`E_T (inflBS2)² ≤ ε · E_T (inflBS2)`. -/
theorem sum_sq_inflBS2_le_of_smallInfl {m n : ℕ} {m' n' : ℕ}
    (Q : Matrix (Fin n') (Fin n) 𝔽₂) (ι : Matrix (Fin m) (Fin m') 𝔽₂)
    (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) {d : ℕ} {ε : ℝ} (hε : 0 ≤ ε)
    (h : SmallInfl d ε f) (hord : hybridOrder Q ι ≤ d) :
    (∑ T : Matrix (Fin m) (Fin n) 𝔽₂, (inflBS2 Q ι T f) ^ 2) ≤
      ε * ∑ T : Matrix (Fin m) (Fin n) 𝔽₂, inflBS2 Q ι T f := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun T _ => ?_
  have h1 : inflBS2 Q ι T f ≤ ε := h Q ι T hord
  have h2 : 0 ≤ inflBS2 Q ι T f := by
    rw [inflBS2]; exact l2sq_nonneg _
  nlinarith [h1, h2]

end

end Submission.Grassmann
