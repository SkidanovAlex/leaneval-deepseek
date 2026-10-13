import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.EllipticEst.InteriorRegularity.Strip

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.InteriorRegularity

/-! ### Coordinates of `E2 = EuclideanSpace ℝ (Fin 2)` along the `e₀`/`e₁` lines -/

lemma coords_apply_zero (s θ : ℝ) : (coords s θ) 0 = s := by simp [coords]

lemma coords_apply_one (s θ : ℝ) : (coords s θ) 1 = θ := by simp [coords]

lemma add_smul_e0_coords (x : E2) (t : ℝ) : x + t • e0 = coords (x 0 + t) (x 1) := by
  ext i
  fin_cases i <;> simp [coords, e0, EuclideanSpace.basisFun_apply]

lemma add_smul_e1_coords (x : E2) (t : ℝ) : x + t • e1 = coords (x 0) (x 1 + t) := by
  ext i
  fin_cases i <;> simp [coords, e1, EuclideanSpace.basisFun_apply]

/-! ### The line derivatives of a function on `E2` pulled back from `ℝ × ℝ`

These are the two "coordinate bridge" identities, in the form in which the
second-order identity needs them: they hold for *any* `Q`, differentiability is
irrelevant, because a line derivative along `e₀` is by definition the derivative of
the `e₀`-slice, i.e. of `t ↦ Q (x₀ + t, x₁)`, and shifting the variable only relabels
the point at which the one-variable derivative is taken. -/

lemma lineDeriv_e0_curry_prod (Q : ℝ × ℝ → ℂ) (x : E2) :
    lineDeriv ℝ (fun y : E2 => Q (y 0, y 1)) x e0 = deriv (fun s => Q (s, x 1)) (x 0) := by
  rw [lineDeriv]
  have h1 : (fun t : ℝ => (fun y : E2 => Q (y 0, y 1)) (x + t • e0))
      = fun t : ℝ => Q (x 0 + t, x 1) := by
    funext t
    rw [add_smul_e0_coords x t]
    simp [coords]
  rw [h1, deriv_comp_const_add (fun s => Q (s, x 1)) (x 0) (0 : ℝ)]
  simp

lemma lineDeriv_e1_curry_prod (Q : ℝ × ℝ → ℂ) (x : E2) :
    lineDeriv ℝ (fun y : E2 => Q (y 0, y 1)) x e1 = deriv (fun θ => Q (x 0, θ)) (x 1) := by
  rw [lineDeriv]
  have h1 : (fun t : ℝ => (fun y : E2 => Q (y 0, y 1)) (x + t • e1))
      = fun t : ℝ => Q (x 0, x 1 + t) := by
    funext t
    rw [add_smul_e1_coords x t]
    simp [coords]
  rw [h1, deriv_comp_const_add (fun θ => Q (x 0, θ)) (x 1) (0 : ℝ)]
  simp

theorem curryC_bridge {F : ℝ → ℝ → ℂ}
    (hF : ∀ n : ℕ, ContDiff ℝ n (Function.uncurry F)) :
    (∀ n : ℕ, ContDiff ℝ n (curryC F)) ∧
    (∀ x : E2, lineDeriv ℝ (curryC F) x e0 = deriv (fun s => F s (x 1)) (x 0)) ∧
    (∀ x : E2, lineDeriv ℝ (curryC F) x e1 = deriv (fun θ => F (x 0) θ) (x 1)) ∧
    (∀ x : E2, d0 (d0 (curryC F)) x + d1 (d1 (curryC F)) x
      = deriv (fun s => deriv (fun s' => F s' (x 1)) s) (x 0)
        + deriv (fun θ => deriv (fun θ' => F (x 0) θ') θ) (x 1)) := by
  -- The two first-order identities: both sides are the derivative of the corresponding
  -- slice of `F`, after transporting along the `e₀`- (resp. `e₁`-) line.
  have hd0 : ∀ x : E2, lineDeriv ℝ (curryC F) x e0 = deriv (fun s => F s (x 1)) (x 0) := by
    intro x
    rw [lineDeriv]
    have h1 : (fun t : ℝ => curryC F (x + t • e0)) = fun t : ℝ => F (x 0 + t) (x 1) := by
      funext t
      rw [add_smul_e0_coords x t]
      exact curryC_curry'_apply F (x 0 + t) (x 1)
    rw [h1, deriv_comp_const_add (fun s => F s (x 1)) (x 0) (0 : ℝ)]
    simp
  have hd1 : ∀ x : E2, lineDeriv ℝ (curryC F) x e1 = deriv (fun θ => F (x 0) θ) (x 1) := by
    intro x
    rw [lineDeriv]
    have h1 : (fun t : ℝ => curryC F (x + t • e1)) = fun t : ℝ => F (x 0) (x 1 + t) := by
      funext t
      rw [add_smul_e1_coords x t]
      exact curryC_curry'_apply F (x 0) (x 1 + t)
    rw [h1, deriv_comp_const_add (fun θ => F (x 0) θ) (x 1) (0 : ℝ)]
    simp
  refine ⟨?_, hd0, hd1, ?_⟩
  · -- Smoothness: `curryC F` is `uncurry F` composed with the linear coordinate map.
    intro n
    have hphi : ContDiff ℝ n (fun x : E2 => (x 0, x 1)) := by
      have h : (fun x : E2 => (x 0, x 1))
          = fun x : E2 => ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)) x,
                            (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)) x) := rfl
      rw [h]
      exact (ContinuousLinearMap.prod (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2))
        (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2))).contDiff
    exact (hF n).comp hphi
  · -- Second order: replace `d0 (curryC F)` and `d1 (curryC F)` by their slice forms
    -- (the first-order identities), then apply the bridge again.
    intro x
    have hG0 : d0 (curryC F) = fun y : E2 => deriv (fun s => F s (y 1)) (y 0) := by
      funext y
      rw [show d0 (curryC F) y = lineDeriv ℝ (curryC F) y e0 from rfl, hd0 y]
    have hG1 : d1 (curryC F) = fun y : E2 => deriv (fun θ => F (y 0) θ) (y 1) := by
      funext y
      rw [show d1 (curryC F) y = lineDeriv ℝ (curryC F) y e1 from rfl, hd1 y]
    have e0' : lineDeriv ℝ (fun y : E2 => deriv (fun s => F s (y 1)) (y 0)) x e0
        = deriv (fun s => deriv (fun s' => F s' (x 1)) s) (x 0) :=
      lineDeriv_e0_curry_prod (fun p : ℝ × ℝ => deriv (fun s => F s p.2) p.1) x
    have e1' : lineDeriv ℝ (fun y : E2 => deriv (fun θ => F (y 0) θ) (y 1)) x e1
        = deriv (fun θ => deriv (fun θ' => F (x 0) θ') θ) (x 1) :=
      lineDeriv_e1_curry_prod (fun p : ℝ × ℝ => deriv (fun θ => F p.1 θ) p.2) x
    rw [show d0 (d0 (curryC F)) x + d1 (d1 (curryC F)) x
          = lineDeriv ℝ (d0 (curryC F)) x e0 + lineDeriv ℝ (d1 (curryC F)) x e1 from rfl]
    rw [hG0, hG1, e0', e1']

end Work.EllipticEst.InteriorRegularity
