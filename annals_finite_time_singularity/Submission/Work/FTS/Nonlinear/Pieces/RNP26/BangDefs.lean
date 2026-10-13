/-
Copyright: work module for the Elgindi finite-time singularity project.

# Auxiliary polynomials for the `D_θ`-bound on `ψ = sin²θ·Γ`

The target `Work.FTS.Nonlinear.Pieces.RNP26.psiB_Lop_bound` states that the iterates
`D_θ^i ψ`, `1 ≤ i ≤ 4`, of the angular factor `ψ(θ) = sin²θ · Γ(θ)` are bounded by
`D·Γ(θ)·(sin²(2θ) + α)`, uniformly in `0 < α ≤ 1`.

On the open quadrant `D_θ = sin(2θ)∂_θ` acts, after writing `x = cos²θ`, as

  `D_θ (Γ(θ)·a(cos²θ)) = Γ(θ)·(-4x(1-x)·a'(x) + (α/3)(6x-4)·a(x))`

(this is `Work.Construction.glop_step`, together with
`D_θ(Γ) = (α/3)(6cos²θ - 4)·Γ`).  Since `sin²θ = 1 - cos²θ`, the identity

  `D_θ^i (ψ) = Γ(θ)·Bᵢ(cos²θ, α)`

holds with `B₀ = 1-x` and `Bᵢ₊₁ = -4x(1-x)Bᵢ' + (2α/3)(3x-2)Bᵢ`, which is the recurrence
realised below (`bang_succ`, stated in the `(α/3)(6x-4)` form produced by `glop_step`).

Each `Bᵢ` is written in the split form

  `Bᵢ = 4x(1-x)·Vᵢ(x) + ∑_{k=1}^{i} (α/3)^k P_{i,k}(x)`

(so that the `k = 0` part automatically carries the factor `sin²(2θ) = 4cos²θ sin²θ` and
the remaining parts carry a factor `α`), which makes the pointwise bound on `[0,1]`
elementary (`Work.FTS.Nonlinear.Pieces.RNP26.Bang_bound`).

The file also isolates `bang_iter`, the iterate identity
`D_θ^i ψ = Γ·Bᵢ(cos², α)`, and the differentiability of the `Bᵢ`.
-/
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.IntervalCases
import Submission.Work.Spaces.DthIter_mul
import Submission.Work.Spaces.Gam_bounds
import Submission.Work.Construction.GLop_Aux
import Submission.Work.Construction.H4N_GammaTerm_Lop_bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open Filter

namespace Work.FTS.Nonlinear.Pieces.RNP26

set_option autoImplicit false

/-- The `i`-th angular polynomial `Bᵢ(x,α)` of the `θ`-calculation for `ψ = sin²θ·Γ`,
`i ≤ 4` (written in the split form `4x(1-x)Vᵢ + ∑_{k≥1}(α/3)^k P_{i,k}`). -/
def Bang (i : ℕ) : ℝ → ℝ → ℝ := fun x α =>
  match i with
  | 0 => 1 - x
  | 1 => 4 * x * (1 - x) * 1
      + (α / 3) * (-4 + 10 * x - 6 * x ^ 2)
  | 2 => 4 * x * (1 - x) * (-4 + 8 * x)
      + (α / 3) * (-56 * x + 128 * x ^ 2 - 72 * x ^ 3)
      + (α / 3) ^ 2 * (16 - 64 * x + 84 * x ^ 2 - 36 * x ^ 3)
  | 3 => 4 * x * (1 - x) * (16 - 96 * x + 96 * x ^ 2)
      + (α / 3) * (288 * x - 1536 * x ^ 2 + 2304 * x ^ 3 - 1056 * x ^ 4)
      + (α / 3) ^ 2 * (480 * x - 1776 * x ^ 2 + 2160 * x ^ 3 - 864 * x ^ 4)
      + (α / 3) ^ 3 * (-64 + 352 * x - 720 * x ^ 2 + 648 * x ^ 3 - 216 * x ^ 4)
  | 4 => 4 * x * (1 - x) * (-64 + 896 * x - 2304 * x ^ 2 + 1536 * x ^ 3)
      + (α / 3) * (-1408 * x + 15616 * x ^ 2 - 45696 * x ^ 3 + 50688 * x ^ 4 - 19200 * x ^ 5)
      + (α / 3) ^ 2 * (-3072 * x + 24000 * x ^ 2 - 58560 * x ^ 3 + 57792 * x ^ 4 - 20160 * x ^ 5)
      + (α / 3) ^ 3 * (-3328 * x + 17152 * x ^ 2 - 32832 * x ^ 3 + 27648 * x ^ 4 - 8640 * x ^ 5)
      + (α / 3) ^ 4 * (256 - 1792 * x + 4992 * x ^ 2 - 6912 * x ^ 3 + 4752 * x ^ 4 - 1296 * x ^ 5)
  | _ => 0

@[simp] theorem Bang_zero (x α : ℝ) : Bang 0 x α = 1 - x := rfl

@[simp] theorem Bang_one (x α : ℝ) : Bang 1 x α =
    4 * x * (1 - x) * 1 + (α / 3) * (-4 + 10 * x - 6 * x ^ 2) := rfl

@[simp] theorem Bang_two (x α : ℝ) : Bang 2 x α =
    4 * x * (1 - x) * (-4 + 8 * x)
      + (α / 3) * (-56 * x + 128 * x ^ 2 - 72 * x ^ 3)
      + (α / 3) ^ 2 * (16 - 64 * x + 84 * x ^ 2 - 36 * x ^ 3) := rfl

@[simp] theorem Bang_three (x α : ℝ) : Bang 3 x α =
    4 * x * (1 - x) * (16 - 96 * x + 96 * x ^ 2)
      + (α / 3) * (288 * x - 1536 * x ^ 2 + 2304 * x ^ 3 - 1056 * x ^ 4)
      + (α / 3) ^ 2 * (480 * x - 1776 * x ^ 2 + 2160 * x ^ 3 - 864 * x ^ 4)
      + (α / 3) ^ 3 * (-64 + 352 * x - 720 * x ^ 2 + 648 * x ^ 3 - 216 * x ^ 4) := rfl

@[simp] theorem Bang_four (x α : ℝ) : Bang 4 x α =
    4 * x * (1 - x) * (-64 + 896 * x - 2304 * x ^ 2 + 1536 * x ^ 3)
      + (α / 3) * (-1408 * x + 15616 * x ^ 2 - 45696 * x ^ 3 + 50688 * x ^ 4 - 19200 * x ^ 5)
      + (α / 3) ^ 2 * (-3072 * x + 24000 * x ^ 2 - 58560 * x ^ 3 + 57792 * x ^ 4 - 20160 * x ^ 5)
      + (α / 3) ^ 3 * (-3328 * x + 17152 * x ^ 2 - 32832 * x ^ 3 + 27648 * x ^ 4 - 8640 * x ^ 5)
      + (α / 3) ^ 4 * (256 - 1792 * x + 4992 * x ^ 2 - 6912 * x ^ 3 + 4752 * x ^ 4
          - 1296 * x ^ 5) := rfl

/-- The polynomials `Bᵢ` (`i ≤ 4`) are differentiable. -/
theorem differentiable_Bang (j : ℕ) (hj : j ≤ 4) (α : ℝ) :
    Differentiable ℝ (fun y : ℝ => Bang j y α) := by
  interval_cases j
  · simp only [Bang_zero]; fun_prop
  · simp only [Bang_one]; fun_prop
  · simp only [Bang_two]; fun_prop
  · simp only [Bang_three]; fun_prop
  · simp only [Bang_four]; fun_prop

/-- The recurrence `Bᵢ₊₁ = -4x(1-x)Bᵢ' + (α/3)(6x-4)Bᵢ` for `i ≤ 3`, in the exact shape
produced by `Work.Construction.glop_step`. -/
theorem bang_succ (j : ℕ) (hj : j ≤ 3) (x α : ℝ) :
    -4 * x * (1 - x) * deriv (fun y : ℝ => Bang j y α) x
      + (α / 3) * (6 * x - 4) * Bang j x α = Bang (j + 1) x α := by
  interval_cases j
  · have h : (fun y : ℝ => Bang 0 y α)
        = fun y : ℝ => 1 + (-1) * y + 0 * y ^ 2 + 0 * y ^ 3 + 0 * y ^ 4 + 0 * y ^ 5 := by
      funext y
      simp only [Bang_zero]
      ring
    rw [h, Work.Construction.deriv_mono5, Bang_one, Bang_zero]
    ring
  · have h : (fun y : ℝ => Bang 1 y α)
        = fun y : ℝ => (-(4 : ℝ) * α / 3) + (4 + 10 * α / 3) * y
            + (-4 - 2 * α) * y ^ 2 + 0 * y ^ 3 + 0 * y ^ 4 + 0 * y ^ 5 := by
      funext y
      simp only [Bang_one]
      ring
    rw [h, Work.Construction.deriv_mono5, Bang_two, Bang_one]
    ring
  · have h : (fun y : ℝ => Bang 2 y α)
        = fun y : ℝ => (16 * α ^ 2 / 9) + (-16 - 56 * α / 3 - 64 * α ^ 2 / 9) * y
            + (48 + 128 * α / 3 + 28 * α ^ 2 / 3) * y ^ 2
            + (-32 - 24 * α - 4 * α ^ 2) * y ^ 3 + 0 * y ^ 4 + 0 * y ^ 5 := by
      funext y
      simp only [Bang_two]
      ring
    rw [h, Work.Construction.deriv_mono5, Bang_three, Bang_two]
    ring
  · have h : (fun y : ℝ => Bang 3 y α)
        = fun y : ℝ => (-(64 : ℝ) * α ^ 3 / 27)
            + (64 + 96 * α + 160 * α ^ 2 / 3 + 352 * α ^ 3 / 27) * y
            + (-448 - 512 * α - 592 * α ^ 2 / 3 - 80 * α ^ 3 / 3) * y ^ 2
            + (768 + 768 * α + 240 * α ^ 2 + 24 * α ^ 3) * y ^ 3
            + (-384 - 352 * α - 96 * α ^ 2 - 8 * α ^ 3) * y ^ 4 + 0 * y ^ 5 := by
      funext y
      simp only [Bang_three]
      ring
    rw [h, Work.Construction.deriv_mono5, Bang_four, Bang_three]
    ring

/-- `D_θ^i ψ(θ) = Γ(θ)·Bᵢ(cos²θ, α)` for `i ≤ 4` and `θ ∈ (0,π/2)`, where
`ψ(θ) = sin²θ·Γ(θ)`. -/
theorem bang_iter (α : ℝ) (hα : 0 < α) (i : ℕ) (hi : i ≤ 4) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      (Work.Spaces.Lop^[i] (fun θ : ℝ => Real.sin θ ^ 2 * Work.Spaces.Gam α θ)) θ
        = Work.Spaces.Gam α θ * Bang i (Real.cos θ ^ 2) α := by
  induction i with
  | zero =>
      intro θ hθ
      simp only [Function.iterate_zero, id_eq, Bang_zero]
      rw [Real.sin_sq]
      ring
  | succ j ih =>
      intro θ hθ
      have hj : j ≤ 4 := le_trans (Nat.le_succ j) hi
      have hev : (Work.Spaces.Lop^[j] (fun θ : ℝ => Real.sin θ ^ 2 * Work.Spaces.Gam α θ))
          =ᶠ[𝓝 θ] (fun y => Work.Spaces.Gam α y * Bang j (Real.cos y ^ 2) α) := by
        filter_upwards [Ioo_mem_nhds hθ.1 hθ.2] with y hy
        exact ih hj y hy
      rw [Function.iterate_succ_apply']
      rw [show Work.Spaces.Lop
            (Work.Spaces.Lop^[j] (fun θ : ℝ => Real.sin θ ^ 2 * Work.Spaces.Gam α θ)) θ
          = Work.Spaces.Lop
              (fun y => Work.Spaces.Gam α y * Bang j (Real.cos y ^ 2) α) θ from by
        show Real.sin (2 * θ)
              * deriv (Work.Spaces.Lop^[j]
                  (fun θ : ℝ => Real.sin θ ^ 2 * Work.Spaces.Gam α θ)) θ
            = Real.sin (2 * θ)
              * deriv (fun y => Work.Spaces.Gam α y * Bang j (Real.cos y ^ 2) α) θ
        rw [hev.deriv_eq]]
      rw [Work.Construction.glop_step α hα (fun y : ℝ => Bang j y α)
        (differentiable_Bang j hj α) θ hθ]
      rw [bang_succ j (by omega) (Real.cos θ ^ 2) α]

end Work.FTS.Nonlinear.Pieces.RNP26
