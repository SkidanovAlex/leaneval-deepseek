import Mathlib
import Submission.Work.Diff.Alg.Pinch.Defs
import Submission.Work.Diff.Alg.Pinch.Linv
import Submission.Work.Diff.Alg.Pinch.ell_isAlgCurv

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg

-- The hypothesis `p ≤ 1` of the target statement is redundant: `p > 1` together with `scal > 0`
-- already contradicts `RicPinch p S`.  Silence the linter for the unused binder.
set_option linter.unusedVariables false

variable {n : ℕ}

/-!
# The traceless Ricci tensor of a Ricci-pinched algebraic curvature tensor

`Work.Diff.Alg.Pinch.ric0Frob2_le` bounds the squared Frobenius norm of the traceless Ricci
tensor `Ric₀ = Ric − (scal/n)·id` of an algebraic curvature tensor `S` whose Ricci tensor is
`p`-pinched (`RicPinch p S`, i.e. `Ric ≥ (p · scal/n)·id`) and whose scalar curvature is
positive.

The bound `|Ric₀|² ≤ n(n−1)(1−p)² (scal/n)²` is exactly the sharp one: writing `σ = scal/n`
and `M = Ric − pσ·id` (positive semidefinite by `RicPinch`) and `c = (1−p)σ`, one has
`Ric₀ = M − c·id`, hence

* `Σᵢⱼ (Mᵢⱼ)² ≤ (Σᵢ Mᵢᵢ)² = (n c)²` for the positive semidefinite `M`
  (`Work.Diff.Alg.Pinch.sum_sq_le_trace_sq`), and
* `Σᵢⱼ (Ric₀)ᵢⱼ² = Σᵢⱼ Mᵢⱼ² − n c²` (`Work.Diff.Alg.Pinch.sum_sq_sub_id2`),

so that `|Ric₀|² ≤ n²c² − nc² = n(n−1)c²`.  The extremal case (all but one eigenvalue of `Ric`
equal to `pσ`) shows that equality can occur.  (Note that `p ≤ 1` is in fact redundant: `p > 1`
together with `scal > 0` contradicts `RicPinch p S`.)
-/

/-! ## Sums involving the Kronecker delta `id2` -/

/-- The `id2` matrix contracts double sums to the diagonal. -/
private lemma id2_mul (M : Fin n → Fin n → ℝ) :
    ∑ i, ∑ j, id2 n i j * M i j = ∑ i, M i i := by
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.sum_eq_single i]
  · simp [id2]
  · intro j _ hj
    have hne : ¬ (i = j) := fun h => hj h.symm
    simp [id2, hne]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- `∑ᵢⱼ δᵢⱼ = n`. -/
private lemma id2_card : ∑ i : Fin n, ∑ j, id2 n i j = (n : ℝ) := by
  simpa using id2_mul (n := n) (fun _ _ : Fin n => (1 : ℝ))

/-- Constants can be pulled out of a double sum. -/
private lemma pull_sum (a : ℝ) (f : Fin n → Fin n → ℝ) :
    ∑ i, ∑ j, a * f i j = a * ∑ i, ∑ j, f i j := by
  simp only [Finset.mul_sum]

/-- Expansion of `∑ᵢⱼ (Mᵢⱼ − c δᵢⱼ)²`. -/
private lemma sum_sq_sub_id2 (M : Fin n → Fin n → ℝ) (c : ℝ) :
    ∑ i, ∑ j, (M i j - c * id2 n i j) * (M i j - c * id2 n i j)
      = ∑ i, ∑ j, M i j * M i j - 2 * c * (∑ i, M i i) + (n : ℝ) * c ^ 2 := by
  have hpt : ∀ i j, (M i j - c * id2 n i j) * (M i j - c * id2 n i j)
      = M i j * M i j - 2 * c * (id2 n i j * M i j) + c ^ 2 * id2 n i j := by
    intro i j
    simp only [id2]
    split <;> ring
  simp only [hpt, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [pull_sum, pull_sum, id2_mul, id2_card]
  ring

/-- The scalar curvature is the trace of the Ricci tensor, `scal R = ∑ᵢ Ricᵢᵢ`. -/
private lemma scalAlg_eq_sum_ric (R : Curv4 n) : scalAlg R = ∑ i, ric R i i := by
  simp only [scalAlg, ric]
  rw [Finset.sum_comm]

/-! ## The positive semidefinite bound -/

/-- The shift of a `(0,2)`-tensor by `c · id`: `shiftDiag A c = A + c·id`. -/
noncomputable def shiftDiag (A : Fin n → Fin n → ℝ) (c : ℝ) : Fin n → Fin n → ℝ :=
  fun i j => A i j + c * id2 n i j

/-- For a symmetric `(0,2)`-tensor `M` with nonnegative quadratic form, the sum of the squares of
all entries is at most the square of the trace: `‖M‖_F² ≤ (tr M)²`.

The proof uses that `M` is positive semidefinite, hence `Mᵢⱼ² ≤ Mᵢᵢ Mⱼⱼ` — obtained by applying
`Matrix.PosSemidef.det_nonneg` to the 2×2 principal submatrix on `{i, j}`, whose determinant is
`Mᵢᵢ Mⱼⱼ − Mᵢⱼ²` — and then summing,
`∑ᵢⱼ Mᵢⱼ² ≤ ∑ᵢⱼ Mᵢᵢ Mⱼⱼ = (∑ᵢ Mᵢᵢ)²`. -/
theorem sum_sq_le_trace_sq {n : ℕ} {M : Fin n → Fin n → ℝ}
    (hsym : ∀ i j, M i j = M j i)
    (hpsd : ∀ v : Fin n → ℝ, 0 ≤ ∑ i, ∑ j, M i j * v i * v j) :
    ∑ i, ∑ j, M i j * M i j ≤ (∑ i, M i i) ^ 2 := by
  have hentry : ∀ i j, M i j * M i j ≤ M i i * M j j := by
    intro i j
    have hM : Matrix.PosSemidef (Matrix.of M) := by
      refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
      · exact Matrix.IsHermitian.ext (fun i j => by
          simp only [star_trivial, Matrix.of_apply]; exact hsym j i)
      · intro x
        have hx := hpsd x
        simpa [dotProduct, Matrix.mulVec, Matrix.of_apply, Finset.mul_sum, mul_assoc,
          mul_left_comm, mul_comm] using hx
    by_cases hij : i = j
    · subst hij; exact le_of_eq (by ring)
    · let e : Fin 2 → Fin n := ![i, j]
      have hsub : (Matrix.submatrix (Matrix.of M) e e).PosSemidef :=
        Matrix.PosSemidef.submatrix hM e
      have hdet := hsub.det_nonneg
      rw [Matrix.det_fin_two] at hdet
      simp only [Matrix.submatrix_apply, e, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.of_apply] at hdet
      rw [hsym j i] at hdet
      linarith
  calc ∑ i, ∑ j, M i j * M i j
      ≤ ∑ i, ∑ j, M i i * M j j := by
        apply Finset.sum_le_sum; intro i _
        apply Finset.sum_le_sum; intro j _
        exact hentry i j
    _ = (∑ i, M i i) ^ 2 := by
        rw [pow_two, Finset.sum_mul_sum]

/-- Frob–trace bound for a traceless symmetric `(0,2)`-tensor `A` such that the shifted tensor
`A + c·id` has nonnegative quadratic form: `∑ᵢⱼ Aᵢⱼ² ≤ n(n−1)c²`. -/
theorem frob_sq_le_of_psd {n : ℕ} {A : Fin n → Fin n → ℝ} {c : ℝ}
    (hsym : ∀ i j, A i j = A j i)
    (hpsd : ∀ v : Fin n → ℝ, 0 ≤ ∑ i, ∑ j, shiftDiag A c i j * v i * v j)
    (htrace : ∑ i, A i i = 0) :
    ∑ i, ∑ j, A i j * A i j ≤ (n : ℝ) * ((n : ℝ) - 1) * c ^ 2 := by
  have hMsym : ∀ i j, shiftDiag A c i j = shiftDiag A c j i := by
    intro i j
    simp only [shiftDiag, hsym i j, id2_symm i j]
  have hb := sum_sq_le_trace_sq (M := shiftDiag A c) hMsym hpsd
  have htr : ∑ i, shiftDiag A c i i = (n : ℝ) * c := by
    have hpt : ∀ i : Fin n, shiftDiag A c i i = A i i + c := by
      intro i; simp [shiftDiag, id2]
    rw [Finset.sum_congr rfl (fun i _ => hpt i)]
    rw [Finset.sum_add_distrib, htrace]
    simp [Finset.sum_const, nsmul_eq_mul]
  rw [htr] at hb
  have hexp := sum_sq_sub_id2 (n := n) (shiftDiag A c) c
  rw [htr] at hexp
  have hAq : ∑ i, ∑ j, A i j * A i j
      = ∑ i, ∑ j, (shiftDiag A c i j - c * id2 n i j)
          * (shiftDiag A c i j - c * id2 n i j) := by
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    simp only [shiftDiag]
    ring
  rw [hAq, hexp]
  nlinarith [hb]

theorem ric0Frob2_le (n : ℕ) {p : ℝ} (hp : p ≤ 1) {S : Submission.Diff.Alg.Curv4 n}
    (hS : Submission.Diff.Alg.IsAlgCurv S) (hric : Work.Diff.Alg.Pinch.RicPinch p S)
    (hscal : 0 < Submission.Diff.Alg.scalAlg S / (n : ℝ)) :
    Work.Diff.Alg.Pinch.ric0Frob2 S
      ≤ (n : ℝ) * ((n : ℝ) - 1) * (1 - p) ^ 2
          * (Submission.Diff.Alg.scalAlg S / (n : ℝ)) ^ 2 := by
  have hn : (n : ℝ) ≠ 0 := by
    intro h; rw [h] at hscal; simp at hscal
  set σ : ℝ := scalAlg S / (n : ℝ) with hσ
  set c : ℝ := (1 - p) * σ with hc
  have hsym : ∀ i j, ric0 S i j = ric0 S j i := fun i j => ric0_symm hS i j
  have htr : ∑ i, ric0 S i i = 0 := by
    have hpt : ∀ i : Fin n, ric0 S i i = ric S i i - scalAlg S / (n : ℝ) := by
      intro i; simp [ric0, id2]
    rw [Finset.sum_congr rfl (fun i _ => hpt i)]
    rw [Finset.sum_sub_distrib, ← scalAlg_eq_sum_ric S]
    have hconst : ∑ i : Fin n, (scalAlg S / (n : ℝ)) = (n : ℝ) * (scalAlg S / (n : ℝ)) := by
      simp [Finset.sum_const, nsmul_eq_mul]
    rw [hconst, mul_comm, div_mul_cancel₀ _ hn]
    ring
  have hpsd : ∀ v : Fin n → ℝ, 0 ≤ ∑ i, ∑ j, shiftDiag (ric0 S) c i j * v i * v j := by
    intro v
    have hv := hric v
    have hcoef : p * scalAlg S / (n : ℝ) = p * σ := by rw [hσ]; ring
    rw [hcoef] at hv
    have hsum : ∑ i, ∑ j, shiftDiag (ric0 S) c i j * v i * v j
        = ∑ i, ∑ j, ric S i j * v i * v j - (p * σ) * (∑ i, v i * v i) := by
      have hpt : ∀ i j, shiftDiag (ric0 S) c i j * v i * v j
          = ric S i j * v i * v j - (p * σ) * (id2 n i j * (v i * v j)) := by
        intro i j
        simp only [shiftDiag, ric0, hc, hσ]
        ring
      simp only [hpt, Finset.sum_sub_distrib]
      rw [pull_sum, id2_mul]
    rw [hsum]
    linarith
  have hkey := frob_sq_le_of_psd (n := n) hsym hpsd htr
  have hcval : (n : ℝ) * ((n : ℝ) - 1) * c ^ 2
      = (n : ℝ) * ((n : ℝ) - 1) * (1 - p) ^ 2 * (scalAlg S / (n : ℝ)) ^ 2 := by
    rw [hc, hσ]; ring
  calc ric0Frob2 S = ∑ i, ∑ j, ric0 S i j * ric0 S i j := rfl
    _ ≤ (n : ℝ) * ((n : ℝ) - 1) * c ^ 2 := hkey
    _ = (n : ℝ) * ((n : ℝ) - 1) * (1 - p) ^ 2 * (scalAlg S / (n : ℝ)) ^ 2 := hcval

end Work.Diff.Alg.Pinch
