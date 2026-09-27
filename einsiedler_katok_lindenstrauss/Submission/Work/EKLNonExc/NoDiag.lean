import Mathlib
import Submission.Work.EKLNonExc.Defs
import Submission.Work.EKLContract.Lemmas.Gamma3Facts
import Submission.Work.EKLContract.Lemmas.mkX_mul
import Submission.Work.EKLNonExc.rat_of_int_traces
import Submission.Work.EKLNonExc.int_of_rat_root

/-!
# EKL L9.3: no diagonal element of `SL₃(ℝ)` fixes a point of `X₃ = SL₃(ℝ)/SL₃(ℤ)`

`Work.EKLNonExc.NoDiag`: if `h ∈ SL₃(ℝ)` has matrix `diag(λ, λ, λ⁻²)` with `λ > 0`, `λ ≠ 1`
(the `λ⁻²` sitting in an arbitrary slot `c`), then `h` has no fixed point on `X₃`.

Proof (ROUTE_LEAD L9.3).  Suppose `h • x = x` and write `x = mkX k`.  Then `mkX (h * k) = mkX k`,
i.e. `(h*k)⁻¹ * k ∈ Γ₃ = SL₃(ℤ)`; equivalently `γ := k⁻¹ h k ∈ Γ₃`.  Since `γ` is conjugate to
`h`, and both `γ` and `γ⁻¹` lie in `Γ₃` (so have integer entries), the two traces
`tr γ = 2λ + λ⁻²` and `tr γ⁻¹ = λ² + 2λ⁻¹` are integers: the first is `tr (toMat h)`, the second
`tr (toMat h⁻¹) = tr ((toMat h).adjugate)` (valid since `det h = 1`), and the adjugate of a
diagonal matrix is diagonal with the products of the remaining entries.

The arithmetic (Einsiedler–Katok–Lindenstrauss, §5) then rules this out:
* `Work.EKLNonExc.rat_of_int_traces`: `λ ∈ ℚ`;
* `Work.EKLNonExc.int_of_rat_root`: a rational root of the monic integer polynomial `X³ - bX + 2`
  is an integer, and here `b = tr γ⁻¹` with `λ³ = b λ - 2`;
* `Work.EKLNonExc.no_int_lam` (below): `λ ∈ ℤ`, `λ > 0`, `λ ≠ 1` forces `λ ≥ 2`, so
  `0 < λ⁻² ≤ 1/4 < 1`, while `λ⁻² = a - 2λ` with `a = 2λ + λ⁻² ∈ ℤ`.
-/

set_option linter.unusedVariables false

namespace Work.EKLNonExc

open Work.EKLContract

noncomputable section

open Matrix

/-! ## Traces -/

/-- The trace of a conjugated element: `tr (k⁻¹ h k) = tr h`. -/
lemma trace_conj (k h : SL3) : Matrix.trace (toMat (k⁻¹ * h * k)) = Matrix.trace (toMat h) := by
  have hkey : k⁻¹ * h * k = k⁻¹ * (h * k) := by group
  calc Matrix.trace (toMat (k⁻¹ * h * k))
      = Matrix.trace (toMat k⁻¹ * toMat (h * k)) := by rw [hkey, toMat_mul]
    _ = Matrix.trace (toMat (h * k) * toMat k⁻¹) := Matrix.trace_mul_comm _ _
    _ = Matrix.trace (toMat ((h * k) * k⁻¹)) := by rw [← toMat_mul]
    _ = Matrix.trace (toMat h) := by congr 1; group

/-- The trace of an element of `Γ₃ = SL₃(ℤ)` is an integer. -/
lemma trace_Γ3_int (γ : SL3) (hγ : γ ∈ Γ3) :
    ∃ n : ℤ, Matrix.trace (toMat γ) = (n : ℝ) := by
  have h : ∀ i : Fin 3, ∃ m : ℤ, toMat γ i i = (m : ℝ) :=
    fun i => Lemmas.Γ3_integral_entries γ hγ i i
  choose f hf using h
  refine ⟨∑ i : Fin 3, f i, ?_⟩
  push_cast
  rw [Matrix.trace, Fin.sum_univ_three, Fin.sum_univ_three]
  simp only [Matrix.diag_apply, hf]

/-- The trace of `diag(λ,λ,λ⁻²)` with `λ⁻²` in slot `c`. -/
lemma trace_diag_h (lam : ℝ) (c : Fin 3) :
    Matrix.trace (Matrix.diagonal (fun i : Fin 3 => if i = c then (lam ^ 2)⁻¹ else lam))
      = 2 * lam + (lam ^ 2)⁻¹ := by
  rw [Matrix.trace_diagonal, Fin.sum_univ_three]
  fin_cases c <;> simp <;> ring

/-! ### The adjugate of `diag(λ,λ,λ⁻²)`

The adjugate of a diagonal matrix is diagonal with the products of the others, so
`tr ((diag(λ,λ,λ⁻²))⁻¹) = λ² + 2λ⁻¹`.  The finitely many `prod_erase_univ_*` evaluations below
turn `∏ j ∈ univ.erase i, v j` into the product of the remaining two entries. -/

lemma prod_erase_univ_zero (v : Fin 3 → ℝ) :
    (∏ j ∈ Finset.univ.erase (0 : Fin 3), v j) = v 1 * v 2 := by
  have h : (Finset.univ.erase (0 : Fin 3)) = ({1, 2} : Finset (Fin 3)) := by decide
  rw [h]
  simp [Finset.prod_insert, Finset.prod_singleton]

lemma prod_erase_univ_one (v : Fin 3 → ℝ) :
    (∏ j ∈ Finset.univ.erase (1 : Fin 3), v j) = v 0 * v 2 := by
  have h : (Finset.univ.erase (1 : Fin 3)) = ({0, 2} : Finset (Fin 3)) := by decide
  rw [h]
  simp [Finset.prod_insert, Finset.prod_singleton]

lemma prod_erase_univ_two (v : Fin 3 → ℝ) :
    (∏ j ∈ Finset.univ.erase (2 : Fin 3), v j) = v 0 * v 1 := by
  have h : (Finset.univ.erase (2 : Fin 3)) = ({0, 1} : Finset (Fin 3)) := by decide
  rw [h]
  simp [Finset.prod_insert, Finset.prod_singleton]

/-- `tr (adjugate (diag(λ,λ,λ⁻²))) = λ² + 2λ⁻¹`; since `det = 1`, the adjugate is the inverse. -/
lemma trace_adjugate_diag_aux (lam : ℝ) (c : Fin 3) :
    Matrix.trace (Matrix.adjugate
      (Matrix.diagonal (fun i : Fin 3 => if i = c then (lam ^ 2)⁻¹ else lam)))
      = lam ^ 2 + 2 * lam⁻¹ := by
  rw [Matrix.adjugate_diagonal, Matrix.trace_diagonal, Fin.sum_univ_three]
  fin_cases c <;>
    simp only [prod_erase_univ_zero, prod_erase_univ_one, prod_erase_univ_two] <;>
    simp <;> field_simp <;> ring

/-! ## The arithmetic: `λ` cannot be an integer -/

/-- If `λ ∈ ℤ`, `λ > 0`, `λ ≠ 1` and `2λ + λ⁻²` is an integer, we reach a contradiction: `λ ≥ 2`,
so `0 < λ⁻² ≤ 1/4 < 1`, while `λ⁻² = a - 2λ` is an integer. -/
lemma no_int_lam (lam : ℝ) (hlam : 0 < lam) (hlam1 : lam ≠ 1) (a : ℤ)
    (ha : 2 * lam + (lam^2)⁻¹ = (a : ℝ)) (hm : ∃ m : ℤ, (m : ℝ) = lam) : False := by
  obtain ⟨m, hm⟩ := hm
  have hm0 : 0 < m := by
    have : (0 : ℝ) < (m : ℝ) := by rw [hm]; exact hlam
    exact_mod_cast this
  have hm1 : m ≠ 1 := by
    rintro rfl
    exact hlam1 (by rw [← hm]; norm_num)
  have hm2 : (2 : ℤ) ≤ m := by omega
  have hcast : (((a - 2 * m : ℤ)) : ℝ) = (lam ^ 2)⁻¹ := by
    rw [← hm] at ha ⊢
    push_cast
    linarith [ha]
  have h0 : (0 : ℝ) < (((a - 2 * m : ℤ)) : ℝ) := by rw [hcast]; positivity
  have h1 : (((a - 2 * m : ℤ)) : ℝ) < 1 := by
    rw [hcast]
    have h2 : (1 : ℝ) < lam ^ 2 := by
      have h3 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm2
      rw [hm] at h3
      nlinarith
    exact inv_lt_one_of_one_lt₀ h2
  have e1 : (0 : ℤ) < a - 2 * m := by exact_mod_cast h0
  have e2 : a - 2 * m < 1 := by exact_mod_cast h1
  omega

/-- **Arithmetic core of EKL L9.3**: `2λ + λ⁻²` and `λ² + 2λ⁻¹` cannot both be integers when
`λ > 0` and `λ ≠ 1`. -/
lemma lam_false (lam : ℝ) (hlam : 0 < lam) (hlam1 : lam ≠ 1) (a b : ℤ)
    (ha : 2 * lam + (lam^2)⁻¹ = (a : ℝ)) (hb : lam^2 + 2 * lam⁻¹ = (b : ℝ)) : False := by
  obtain ⟨q, hq⟩ := rat_of_int_traces lam hlam a b ha hb
  have hroot : lam ^ 3 = (b : ℝ) * lam - 2 := by
    rw [hb.symm]
    field_simp
    ring
  obtain ⟨m, hm⟩ := int_of_rat_root lam b ⟨q, hq⟩ hroot
  exact no_int_lam lam hlam hlam1 a ha ⟨m, hm⟩

/-! ## The main statement -/

/-- **EKL L9.3.**  No element of `SL₃(ℝ)` whose matrix is `diag(λ,λ,λ⁻²)` (`λ > 0`, `λ ≠ 1`)
fixes a point of `X₃ = SL₃(ℝ)/SL₃(ℤ)`. -/
theorem NoDiag (a b c : Fin 3) (hab : a ≠ b) (hac : a ≠ c) (hcb : c ≠ b)
    (lam : ℝ) (hlam : 0 < lam) (hlam1 : lam ≠ 1) (x : Work.EKLContract.X3)
    (h : Work.EKLContract.SL3)
    (hmat : Work.EKLContract.toMat h =
      Matrix.diagonal (fun i => if i = c then (lam^2)⁻¹ else lam)) :
    h • x ≠ x := by
  intro hfix
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective x
  have h2 : mkX (h * k) = mkX k := by
    rw [Lemmas.mkX_mul]; exact hfix
  have h3 : (h * k)⁻¹ * k ∈ Γ3 := QuotientGroup.eq.mp h2
  set γ : SL3 := k⁻¹ * h * k with hγdef
  have hγ : γ ∈ Γ3 := by
    have he : γ = ((h * k)⁻¹ * k)⁻¹ := by rw [hγdef]; group
    rw [he]; exact inv_mem h3
  obtain ⟨A, hA⟩ := trace_Γ3_int γ hγ
  obtain ⟨B, hB⟩ := trace_Γ3_int γ⁻¹ (inv_mem hγ)
  have e1 : (A : ℝ) = 2 * lam + (lam ^ 2)⁻¹ := by
    rw [← hA, hγdef, trace_conj k h, hmat, trace_diag_h]
  have e2 : (B : ℝ) = lam ^ 2 + 2 * lam⁻¹ := by
    rw [← hB]
    have hginv : γ⁻¹ = k⁻¹ * h⁻¹ * k := by rw [hγdef]; group
    rw [hginv, trace_conj k h⁻¹]
    have hcoe : toMat h⁻¹ = (toMat h).adjugate := Matrix.SpecialLinearGroup.coe_inv h
    rw [hcoe, hmat, trace_adjugate_diag_aux]
  exact lam_false lam hlam hlam1 A B e1.symm e2.symm

end

end Work.EKLNonExc
