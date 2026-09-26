import Mathlib
import Submission.Work.TorusCover.Basic

/-!
# Pulling a `TorusParam` back along a diffeomorphism

Given a parametrised torus `P : TorusParam` (periodic, injective modulo `2π`, with a
uniform positive lower bound `P.c` for its derivative) and a `C¹`-diffeomorphism
`Ψ : ℝ³ → ℝ³` with inverse `Ψinv`, the composite parametrisation

  `fun x y => Ψinv (P.psi x y)`

is again a parametrised torus, provided the derivative of `Ψ` is bounded by `C` on the
image of that composite.  Its constant is `P.c / C`: the derivative of `Ψinv` expands by
at least the reciprocal of `‖fderiv ℝ Ψ‖` wherever `Ψ` and `Ψinv` are inverse, and the
uniform lower bound `P.c` of `P` is transported through.

The single analytic ingredient is the chain-rule identity
`fderiv Ψ (Ψinv z) ∘ fderiv Ψinv z = 1` (`fderiv_comp_inv`), which turns
`‖v‖ = ‖fderiv Ψ (Ψinv z) (fderiv Ψinv z v)‖ ≤ ‖fderiv Ψ (Ψinv z)‖ * ‖fderiv Ψinv z v‖`
into the expansion estimate for `Ψinv`.
-/

namespace Work.TorusCover

open LeanEval.KnotTheory.PardonDistortion Set

/-- **Chain rule identity for an inverse pair.**  If `Ψ` and `Ψinv` are `C¹` and
`Ψ ∘ Ψinv = id`, then the derivative of `Ψ` at `Ψinv y` is a left inverse of the
derivative of `Ψinv` at `y`. -/
lemma fderiv_comp_inv {Ψ Ψinv : R3 → R3}
    (hΨ : ContDiff ℝ (1 : ℕ∞) Ψ) (hΨinv : ContDiff ℝ (1 : ℕ∞) Ψinv)
    (hright : ∀ x, Ψ (Ψinv x) = x) (y : R3) :
    (fderiv ℝ Ψ (Ψinv y)).comp (fderiv ℝ Ψinv y) = 1 := by
  have h := fderiv_comp (𝕜 := ℝ) y (f := Ψinv) (g := Ψ)
    (hΨ.differentiable (by norm_num) (Ψinv y)) (hΨinv.differentiable (by norm_num) y)
  rw [show (Ψ ∘ Ψinv) = id from funext hright, fderiv_id] at h
  exact h.symm

theorem exists_torusParam_comp (P : Work.TorusCover.TorusParam)
    (Ψ Ψinv : LeanEval.KnotTheory.PardonDistortion.R3 → LeanEval.KnotTheory.PardonDistortion.R3)
    (hΨ : ContDiff ℝ (1 : ℕ∞) Ψ) (hΨinv : ContDiff ℝ (1 : ℕ∞) Ψinv)
    (hleft : ∀ x, Ψinv (Ψ x) = x) (hright : ∀ x, Ψ (Ψinv x) = x)
    (C : ℝ) (hC : 0 < C)
    (hbound : ∀ z ∈ Set.range (fun p : ℝ × ℝ => Ψinv (P.psi p.1 p.2)),
      ‖fderiv ℝ Ψ z‖ ≤ C) :
    ∃ P' : Work.TorusCover.TorusParam,
      P'.psi = (fun x y => Ψinv (P.psi x y)) ∧ P'.c = P.c / C := by
  have hΨinv_inj : Function.Injective Ψinv := fun x y h => by
    have h2 := congrArg Ψ h
    rwa [hright, hright] at h2
  have hderiv : ∀ x y (u : ℝ × ℝ),
      (P.c / C) * ‖u‖ ≤ ‖fderiv ℝ (psiMap (fun x y => Ψinv (P.psi x y))) (x, y) u‖ := by
    intro x y u
    -- chain rule for the composite parametrisation
    have hchain : fderiv ℝ (psiMap (fun x y => Ψinv (P.psi x y))) (x, y)
        = (fderiv ℝ Ψinv (P.psi x y)).comp (fderiv ℝ (psiMap P.psi) (x, y)) := by
      have h := fderiv_comp (𝕜 := ℝ) (x, y) (f := psiMap P.psi) (g := Ψinv)
        (hΨinv.differentiable (by norm_num) (P.psi x y))
        (P.contDiff.differentiable (by norm_num) (x, y))
      rw [show psiMap (fun x y => Ψinv (P.psi x y)) = Ψinv ∘ psiMap P.psi from rfl]
      exact h
    -- the two derivatives are inverse to each other at the relevant point
    have hcomp := fderiv_comp_inv hΨ hΨinv hright (P.psi x y)
    have hbnd : ‖fderiv ℝ Ψ (Ψinv (P.psi x y))‖ ≤ C :=
      hbound _ ⟨(x, y), rfl⟩
    have hBD : (fderiv ℝ Ψinv (P.psi x y))
          ((fderiv ℝ (psiMap P.psi) (x, y)) u)
        = (fderiv ℝ (psiMap (fun x y => Ψinv (P.psi x y))) (x, y)) u := by
      rw [hchain]
      rfl
    -- `fderiv Ψ` inverts `fderiv Ψinv`, so `fderiv Ψinv` expands
    have hstep1 : ‖(fderiv ℝ (psiMap P.psi) (x, y)) u‖
        ≤ ‖fderiv ℝ Ψ (Ψinv (P.psi x y))‖ *
          ‖(fderiv ℝ Ψinv (P.psi x y)) ((fderiv ℝ (psiMap P.psi) (x, y)) u)‖ := by
      have h1 : (fderiv ℝ Ψ (Ψinv (P.psi x y)))
          ((fderiv ℝ Ψinv (P.psi x y)) ((fderiv ℝ (psiMap P.psi) (x, y)) u))
          = (fderiv ℝ (psiMap P.psi) (x, y)) u := by
        have h3 := congrFun (congrArg DFunLike.coe hcomp) ((fderiv ℝ (psiMap P.psi) (x, y)) u)
        simpa using h3
      have h2 := ContinuousLinearMap.le_opNorm (fderiv ℝ Ψ (Ψinv (P.psi x y)))
        ((fderiv ℝ Ψinv (P.psi x y)) ((fderiv ℝ (psiMap P.psi) (x, y)) u))
      rwa [h1] at h2
    have hstep2 : ‖(fderiv ℝ (psiMap P.psi) (x, y)) u‖
        ≤ C * ‖(fderiv ℝ (psiMap (fun x y => Ψinv (P.psi x y))) (x, y)) u‖ := by
      have hstep2' : ‖(fderiv ℝ (psiMap P.psi) (x, y)) u‖
          ≤ C * ‖(fderiv ℝ Ψinv (P.psi x y)) ((fderiv ℝ (psiMap P.psi) (x, y)) u)‖ :=
        le_trans hstep1 (mul_le_mul_of_nonneg_right hbnd (norm_nonneg _))
      rwa [hBD] at hstep2'
    -- combine with the uniform lower bound of `P` and divide by `C > 0`
    have hD := P.deriv_lower x y u
    have hone : (P.c / C) * ‖u‖ = (P.c * ‖u‖) / C := by ring
    rw [hone]
    refine (div_le_iff₀ hC).mpr ?_
    rw [mul_comm ‖(fderiv ℝ (psiMap (fun x y => Ψinv (P.psi x y))) (x, y)) u‖ C]
    exact le_trans hD hstep2
  refine ⟨{ psi := fun x y => Ψinv (P.psi x y),
            periodic_fst := fun x y => by rw [P.periodic_fst],
            periodic_snd := fun x y => by rw [P.periodic_snd],
            inj_mod := fun x y x' y' => by rw [hΨinv_inj.eq_iff, P.inj_mod],
            c := P.c / C,
            c_pos := div_pos P.c_pos hC,
            deriv_lower := hderiv,
            contDiff := ?_ }, rfl, rfl⟩
  show ContDiff ℝ (1 : ℕ∞) (fun p : ℝ × ℝ => Ψinv (P.psi p.1 p.2))
  exact hΨinv.comp P.contDiff

end Work.TorusCover
