import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst

/-! ## Elementary facts about `L = sin(2θ) ∂_θ` used below

The operator `Work.Spaces.Lop` is the one-dimensional angular operator `L u θ = sin(2θ) u'(θ)`,
whose iterates are `LopIter i u = (L^[i]) u`.  What the proof of `Lop_iter_cos_eq` needs is
(i) that `L` is `ℝ`-homogeneous (unconditionally, via `deriv_const_mul_field`), so that its
iterates are too, and (ii) the explicit value `L (2 cos 2θ) = -4 sin²(2θ)`. -/

/-- `L = sin(2θ) ∂_θ` commutes with multiplication by a constant: this holds for *every*
`f` (no differentiability needed), by the unconditional `deriv_const_mul_field`. -/
theorem Lop_const_mul (c : ℝ) (f : ℝ → ℝ) :
    Work.Spaces.Lop (fun θ : ℝ => c * f θ) = fun θ : ℝ => c * Work.Spaces.Lop f θ := by
  funext θ
  simp only [Work.Spaces.Lop]
  rw [deriv_const_mul_field]
  ring

/-- The iterate `LopIter (j+1) = L^[j] ∘ L` (the successor step applied at the front rather
than at the back, complementing `LopIter_succ`). -/
theorem LopIter_succ_apply (j : ℕ) (u : ℝ → ℝ) :
    LopIter (j + 1) u = LopIter j (Work.Spaces.Lop u) := by
  simp only [LopIter, Function.iterate_succ_apply]

/-- The iterates of `L` are `ℝ`-homogeneous. -/
theorem LopIter_const_mul (i : ℕ) (c : ℝ) :
    ∀ f : ℝ → ℝ, LopIter i (fun θ : ℝ => c * f θ) = fun θ : ℝ => c * LopIter i f θ := by
  induction i with
  | zero => intro f; rfl
  | succ n ih =>
      intro f
      rw [LopIter_succ_apply, Lop_const_mul, ih, LopIter_succ_apply]

/-- `L (2 cos 2θ) = -4 sin²(2θ)`: the first iterate of `2 cos(2θ)`. -/
theorem Lop_two_cos :
    Work.Spaces.Lop (fun θ : ℝ => 2 * Real.cos (2 * θ))
      = fun θ : ℝ => -4 * (Real.sin (2 * θ)) ^ 2 := by
  funext θ
  simp only [Work.Spaces.Lop]
  rw [deriv_const_mul_field]
  rw [show (fun θ : ℝ => Real.cos (2 * θ)) = Real.cos ∘ (fun θ : ℝ => 2 * θ) from rfl]
  rw [deriv_comp] <;> try fun_prop
  rw [Real.deriv_cos]
  have h2 : deriv (fun θ : ℝ => 2 * θ) θ = 2 := by
    rw [deriv_const_mul_field]; simp
  rw [h2]
  ring

/-- The iterates of `2 cos(2θ)` under `L = sin(2θ) ∂_θ` are the `L`-iterates of `sin(2θ)²`:
`L^i (2 cos 2θ) = -4 · L^{i-1}(sin²(2θ))` for `i ≥ 1`.

Proof route: `L (2 cos 2θ) = sin(2θ) · deriv (2 cos 2θ) = sin(2θ) · (-4 sin 2θ) = -4 sin²(2θ)`,
and `L^{i} = L^{i-1} ∘ L` together with the linearity of the iterates of `L`
(`L (fun θ => c * f θ) = fun θ => c * L f θ` by `deriv_const_mul_field`); a direct induction on
`i` using `Function.iterate_succ_apply` is enough. -/
theorem Lop_iter_cos_eq (i : ℕ) (hi : 1 ≤ i) :
    Work.FTS.EllipticEst.LopIter i (fun θ : ℝ => 2 * Real.cos (2 * θ))
      = fun θ : ℝ => -4 * Work.FTS.EllipticEst.LopIter (i - 1)
          (fun θ : ℝ => (Real.sin (2 * θ)) ^ 2) θ := by
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.one_le_iff_ne_zero.mp hi) with ⟨j, rfl⟩
  rw [LopIter_succ_apply]
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel]
  rw [Lop_two_cos, LopIter_const_mul]

end Work.FTS.EllipticEst
