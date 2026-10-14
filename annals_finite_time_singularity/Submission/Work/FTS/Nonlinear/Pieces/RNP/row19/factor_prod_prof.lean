import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row19.Vs0_interval_lower
import Submission.Work.Spaces.dthU_Gam
import Submission.Work.Spaces.sq_mul_div_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.Pieces.RNP.row19

open scoped Real Topology

/-!
# `factor_prod_prof`: the mixed derivatives of a product `proff(z)·U(θ)`

The radial profile `proff z θ = 2z(1−z)/(1+z)³` does not depend on `θ`.  Consequently the
product `F(z,θ) = proff z θ · U θ` behaves exactly like separated variables under the
weighted operators:

* `D_z` differentiates only the `z`-variable, so the `θ`-factor `U θ` is a (pointwise)
  constant for `D_z^j`;
* for fixed `z`, the map `θ ↦ proff z θ` is a *constant* `c = proff z θ'`, so `D_θ^i` acts on
  the `θ`-slice as the iterate of the one-variable operator `Lop`, i.e.
  `D_θ^i F z θ = proff z θ · Lop^[i] U θ`.

Combining the two, `D_z^j D_θ^i F = (D_z^j proff) · (Lop^[i] U)`.

Everything here is unconditional: no smoothness of `U` or of `proff` is assumed, and no
hypothesis on `(z,θ)` is needed.  The only input beyond the definitions is the fact that
`deriv` of a pointwise constant multiple is the constant times the derivative, which holds
without differentiability hypotheses since `deriv` is `0` on non-differentiable functions.
-/

/-! ## Unconditional constant-multiple rules for `deriv` -/

private lemma deriv_const_mul_any (c : ℝ) (u : ℝ → ℝ) (x : ℝ) :
    deriv (fun y => c * u y) x = c * deriv u x := by
  rcases eq_or_ne c 0 with h | h
  · subst h; simp
  · rcases em (DifferentiableAt ℝ u x) with hd | hd
    · exact deriv_const_mul c hd
    · have h2 : ¬ DifferentiableAt ℝ (fun y => c * u y) x := by
        intro hh
        apply hd
        have he : u = fun y => c⁻¹ * (c * u y) := by
          funext y; rw [← mul_assoc, inv_mul_cancel₀ h, one_mul]
        rw [he]
        exact hh.const_mul c⁻¹
      rw [deriv_zero_of_not_differentiableAt hd,
        deriv_zero_of_not_differentiableAt h2, mul_zero]

private lemma deriv_mul_const_any (c : ℝ) (u : ℝ → ℝ) (x : ℝ) :
    deriv (fun y => u y * c) x = deriv u x * c := by
  rcases eq_or_ne c 0 with h | h
  · subst h; simp
  · rcases em (DifferentiableAt ℝ u x) with hd | hd
    · exact deriv_mul_const hd c
    · have h2 : ¬ DifferentiableAt ℝ (fun y => u y * c) x := by
        intro hh
        apply hd
        have he : u = fun y => (u y * c) * c⁻¹ := by
          funext y; rw [mul_assoc, mul_inv_cancel₀ h, mul_one]
        rw [he]
        exact hh.mul_const c⁻¹
      rw [deriv_zero_of_not_differentiableAt hd,
        deriv_zero_of_not_differentiableAt h2, zero_mul]

/-! ## `D_z^j` on a product with a function of `θ` alone -/

/-- `D_z^j (f · V) = (D_z^j f) · V` for a factor `V = V(θ)` depending only on the angle:
the operator `D_z` does not see `θ`. -/
lemma DzIter_mul_snd (j : ℕ) (f : ℝ → ℝ → ℝ) (V : ℝ → ℝ) :
    ∀ z θ, Work.Spaces.DzIter j (fun z θ => f z θ * V θ) z θ
      = Work.Spaces.DzIter j f z θ * V θ := by
  induction j with
  | zero => intro z θ; rfl
  | succ j ih =>
      intro z θ
      show z * deriv (fun z' => Work.Spaces.DzIter j (fun z θ => f z θ * V θ) z' θ) z
        = (z * deriv (fun z' => Work.Spaces.DzIter j f z' θ) z) * V θ
      have h1 : (fun z' => Work.Spaces.DzIter j (fun z θ => f z θ * V θ) z' θ)
          = fun z' => Work.Spaces.DzIter j f z' θ * V θ := by
        funext z'; exact ih z' θ
      rw [h1, deriv_mul_const_any (V θ) (fun z' => Work.Spaces.DzIter j f z' θ) z]
      ring

/-! ## `D_θ^i` on a slice which is a constant multiple -/

/-- If the slice of `F` at `z` is a constant multiple `c · U` of a one-variable function,
then every `D_θ`-iterate of `F` at `z` is the corresponding iterate of `Lop`:
`D_θ^i F z θ = c · Lop^[i] U θ`. -/
lemma DthIter_mul_const_slice (i : ℕ) (F : ℝ → ℝ → ℝ) (c : ℝ) (U : ℝ → ℝ) {z : ℝ}
    (hz : ∀ θ', F z θ' = c * U θ') :
    ∀ θ, Work.Spaces.DthIter i F z θ = c * Work.Spaces.Lop^[i] U θ := by
  induction i with
  | zero => exact hz
  | succ i ih =>
      intro θ
      show Real.sin (2 * θ) * deriv (fun θ' => Work.Spaces.DthIter i F z θ') θ
        = c * Work.Spaces.Lop^[i + 1] U θ
      have h1 : (fun θ' => Work.Spaces.DthIter i F z θ')
          = fun θ' => c * Work.Spaces.Lop^[i] U θ' := by
        funext θ'; exact ih θ'
      rw [h1, deriv_const_mul_any c (Work.Spaces.Lop^[i] U) θ,
        Function.iterate_succ_apply']
      simp only [Work.Spaces.Lop]
      ring

/-! ## The factorisation of the mixed derivatives -/

/-- **`factor_prod_prof`.**  For `F(z,θ) = proff(z)·U(θ)` the weighted derivatives
factorise: `D_z^i F = (D_z^i proff)·U`, `D_θ^i F = proff·Lop^[i] U` and
`D_z^j D_θ^i F = (D_z^j proff)·(Lop^[i] U)` — with no hypotheses whatsoever. -/
theorem factor_prod_prof (U : ℝ → ℝ) (i j : ℕ) (z θ : ℝ) :
    Work.Spaces.DzIter i (fun z θ => Work.FTS.Nonlinear.Pieces.RNP.row19.proff z θ * U θ) z θ
        = (Work.Spaces.DzIter i Work.FTS.Nonlinear.Pieces.RNP.row19.proff) z θ * U θ ∧
    Work.Spaces.DthIter i (fun z θ => Work.FTS.Nonlinear.Pieces.RNP.row19.proff z θ * U θ) z θ
        = Work.FTS.Nonlinear.Pieces.RNP.row19.proff z θ * Work.Spaces.Lop^[i] U θ ∧
    Work.Spaces.mixed j i (fun z θ => Work.FTS.Nonlinear.Pieces.RNP.row19.proff z θ * U θ) z θ
        = (Work.Spaces.DzIter j Work.FTS.Nonlinear.Pieces.RNP.row19.proff) z θ * Work.Spaces.Lop^[i] U θ := by
  refine ⟨?_, ?_, ?_⟩
  · exact DzIter_mul_snd i proff U z θ
  · refine DthIter_mul_const_slice i (fun z θ => proff z θ * U θ) (proff z θ) U
      (z := z) (fun θ' => ?_) θ
    rw [show proff z θ' = proff z θ from rfl]
  · have hDth : Work.Spaces.DthIter i (fun z θ => proff z θ * U θ)
        = fun z θ => proff z θ * Work.Spaces.Lop^[i] U θ := by
      funext z' θ'
      refine DthIter_mul_const_slice i (fun z θ => proff z θ * U θ) (proff z' θ') U
        (z := z') (fun θ'' => ?_) θ'
      rw [show proff z' θ'' = proff z' θ' from rfl]
    rw [Work.Spaces.mixed, hDth]
    exact DzIter_mul_snd j proff (Work.Spaces.Lop^[i] U) z θ

end Work.FTS.Nonlinear.Pieces.RNP.row19
