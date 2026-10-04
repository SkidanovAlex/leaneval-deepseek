import Mathlib
import Submission.Work.Diff.STE.B3.VarCoef.pdAux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Adjointness of the second-order variable-coefficient operator `f ↦ m · ∂ₐ∂_b f`

The `L²`-adjoint of the operator `f ↦ m · ∂ₐ∂_b f` (with `m` a real, smooth, `1`-periodic
multiplier) is again `w ↦ ∂ₐ∂_b (m · w)`, i.e. (multiplying by `star` and integrating by parts
twice)

`∫ (m ∂ₐ∂_b f) · conj g = ∫ f · conj (∂ₐ∂_b (m g))`  on the unit torus.

The sign is the one of a *double* integration by parts (two sign flips), and the two resulting
"intermediate" derivative factors are periodic by periodicity of `f`, `g`, `m`.  Note that
`conj` commutes with `pd` unconditionally (`star_pd`), so the conjugation produces no side
conditions.
-/

open MeasureTheory BigOperators
open scoped ComplexConjugate

namespace Work.Diff.STE.B3.VarCoef

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Two-fold integration by parts on the unit torus.**  For smooth `1`-periodic functions `F`,
`W` and any two coordinates `a`, `b`,

`∫ F · ∂ₐ∂_b W = ∫ (∂ₐ∂_b F) · W`.

This is `ga_ibp_pd_unitCube` applied twice, with `pd_pd_swap` (Clairaut) identifying the two mixed
second derivatives. -/
theorem integral_pd_pd_swap (a b : ι) (F W : (ι → ℝ) → ℂ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hW : ContDiff ℝ (⊤ : ℕ∞) W)
    (hFp : Work.Diff.STE.Periodic1 F) (hWp : Work.Diff.STE.Periodic1 W) :
    ∫ x in Work.Diff.STE.unitCube, F x * Work.Diff.STE.pd a (Work.Diff.STE.pd b W) x
      = ∫ x in Work.Diff.STE.unitCube, Work.Diff.STE.pd a (Work.Diff.STE.pd b F) x * W x := by
  have hpdW : ContDiff ℝ 1 (Work.Diff.STE.pd b W) :=
    Work.Diff.STE.ga_contDiff_pd 1 (hW.of_le (by simp)) b
  have hpdF : ContDiff ℝ 1 (Work.Diff.STE.pd a F) :=
    Work.Diff.STE.ga_contDiff_pd 1 (hF.of_le (by simp)) a
  have hdF : Differentiable ℝ F := hF.differentiable (by simp)
  have hdW : Differentiable ℝ W := hW.differentiable (by simp)
  -- first integration by parts: `∂ₐ` on the factor `∂_b W`
  have h1 := Work.Diff.STE.ga_ibp_pd_unitCube a F (Work.Diff.STE.pd b W)
    (hF.of_le (by simp)) hpdW (hFp a) (Work.Diff.STE.ga_periodicIn_pd a b hWp hdW)
  -- second integration by parts: `∂_b` on the factor `W`
  have h2 := Work.Diff.STE.ga_ibp_pd_unitCube b (Work.Diff.STE.pd a F) W hpdF
    (hW.of_le (by simp)) (Work.Diff.STE.ga_periodicIn_pd b a hFp hdF) (hWp b)
  calc ∫ x in Work.Diff.STE.unitCube, F x * Work.Diff.STE.pd a (Work.Diff.STE.pd b W) x
      = - ∫ x in Work.Diff.STE.unitCube, Work.Diff.STE.pd a F x * Work.Diff.STE.pd b W x := h1
    _ = - (- ∫ x in Work.Diff.STE.unitCube,
            Work.Diff.STE.pd b (Work.Diff.STE.pd a F) x * W x) := by rw [h2]
    _ = ∫ x in Work.Diff.STE.unitCube, Work.Diff.STE.pd a (Work.Diff.STE.pd b F) x * W x := by
          rw [neg_neg, pd_pd_swap hF b a]

theorem cm_pd_pd_L2re_adjoint {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : (ι → ℝ) → ℝ) (a b : ι) (f g : (ι → ℝ) → ℂ)
    (hm : ContDiff ℝ (⊤ : ℕ∞) m) (hmp : Work.Diff.STE.Periodic1 m)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfp : Work.Diff.STE.Periodic1 f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgp : Work.Diff.STE.Periodic1 g) :
    Work.Diff.STE.L2re (fun x => ((m x : ℝ) : ℂ) * Work.Diff.STE.pd a (Work.Diff.STE.pd b f) x) g
      = Work.Diff.STE.L2re f
          (fun x => Work.Diff.STE.pd a (Work.Diff.STE.pd b
            (fun y => ((m y : ℝ) : ℂ) * g y)) x) := by
  have hM : ContDiff ℝ (⊤ : ℕ∞) (fun y => ((m y : ℝ) : ℂ)) :=
    Work.Diff.STE.ga_contDiff_ofReal hm
  have hstar : ContDiff ℝ (⊤ : ℕ∞) (fun y => star (g y)) :=
    Work.Diff.STE.ga_contDiff_star hg
  -- `w := m · conj g` is smooth and periodic
  have hMg : ContDiff ℝ (⊤ : ℕ∞) (fun y => ((m y : ℝ) : ℂ) * star (g y)) := hM.mul hstar
  have hMgp : Work.Diff.STE.Periodic1 (fun y => ((m y : ℝ) : ℂ) * star (g y)) := fun i =>
    Work.Diff.STE.ga_periodicIn_mul i (Work.Diff.STE.ga_periodicIn_ofReal i hmp)
      (Work.Diff.STE.ga_periodicIn_star i hgp)
  -- move the multiplier on the left integrand
  have e1 : (fun x : ι → ℝ =>
        (((m x : ℝ) : ℂ) * Work.Diff.STE.pd a (Work.Diff.STE.pd b f) x) * star (g x))
      = fun x : ι → ℝ =>
        Work.Diff.STE.pd a (Work.Diff.STE.pd b f) x * (((m x : ℝ) : ℂ) * star (g x)) := by
    funext x; ring
  -- `star ∘ pd^2 = pd^2 ∘ star`, and `conj (m · g) = m · conj g`
  have e2 : (fun x : ι → ℝ =>
        f x * star (Work.Diff.STE.pd a (Work.Diff.STE.pd b (fun y => ((m y : ℝ) : ℂ) * g y)) x))
      = fun x : ι → ℝ =>
        f x * Work.Diff.STE.pd a
          (Work.Diff.STE.pd b (fun y => ((m y : ℝ) : ℂ) * star (g y))) x := by
    funext x
    simp only [star_pd, star_cm_mul]
  show Complex.re (∫ x in Work.Diff.STE.unitCube,
        (((m x : ℝ) : ℂ) * Work.Diff.STE.pd a (Work.Diff.STE.pd b f) x) * star (g x))
      = Complex.re (∫ x in Work.Diff.STE.unitCube,
        f x * star (Work.Diff.STE.pd a (Work.Diff.STE.pd b
          (fun y => ((m y : ℝ) : ℂ) * g y)) x))
  rw [e1, e2]
  exact congrArg Complex.re
    (integral_pd_pd_swap a b f (fun y => ((m y : ℝ) : ℂ) * star (g y))
      hf hMg hfp hMgp).symm

end Work.Diff.STE.B3.VarCoef
