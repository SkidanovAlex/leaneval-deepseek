/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FlowerGlue2 team
-/
import Mathlib
import Submission.Work.FlowerGlue2.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `Work.FlowerGlue2.SymmDeriv_tricorn`

Two structural facts about the antiholomorphic fifth iterate `gtc c = (T̄_c)^[5]` of the
mandelbar map `T̄_c(z) = z̄² + c`:

* `gtc c = star ∘ Q c` for a **holomorphic** polynomial map `Q c`
  (so `gtc c` is antiholomorphic);
* at a 2-cycle `p ↦ q ↦ p` of `gtc c`, the holomorphic return map `Ft c = gtc c ∘ gtc c`
  has derivatives that are complex conjugates at the conjugate points:
  `deriv (Ft c) q = star (deriv (Ft c) p)`.

The second statement is the "symmetry of the multiplier" used in the flower glue; it is a
formal consequence of `gtc c = star ∘ Q c` together with the two cycle relations.
-/

open scoped Topology
open Filter Set Metric

set_option linter.unusedVariables false

namespace Work.FlowerGlue2

open Work.PARIMPL (ParNormal Ft gtc)
open LeanEval.ComplexAnalysis (Tantibar)

noncomputable section

/-! ## 1. The holomorphic polynomial `Q c` with `gtc c = star ∘ Q c` -/

/-- The holomorphic quadratic `z ↦ z² + conj c`. -/
def polyS (c : ℂ) : ℂ → ℂ := fun z => z ^ 2 + star c

/-- The holomorphic quartic `z ↦ (z² + conj c)² + c`, which is `(T̄_c)^[2]`. -/
def polyTSq (c : ℂ) : ℂ → ℂ := fun z => (z ^ 2 + star c) ^ 2 + c

/-- The holomorphic polynomial `Q c = polyS c ∘ (polyTSq c)^[2]`, satisfying
`gtc c = star ∘ Q c`. -/
def Qtc (c : ℂ) : ℂ → ℂ := polyS c ∘ (polyTSq c)^[2]

theorem star_polyS (c z : ℂ) : star (polyS c z) = Tantibar c z := by
  simp [polyS, Tantibar]

theorem tantibar_iterate_two (c : ℂ) : (Tantibar c)^[2] = polyTSq c := by
  funext z
  rw [show (2 : ℕ) = 1 + 1 from rfl, Function.iterate_add_apply, Function.iterate_one]
  simp [polyTSq, Tantibar]

theorem gtc_eq_star_Qtc (c : ℂ) : ∀ z : ℂ, gtc c z = star (Qtc c z) := by
  intro z
  have h4 : (Tantibar c)^[4] = (polyTSq c)^[2] := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, Function.iterate_mul, tantibar_iterate_two]
  calc gtc c z = (Tantibar c)^[5] z := rfl
    _ = Tantibar c ((Tantibar c)^[4] z) := Function.iterate_succ_apply' (Tantibar c) 4 z
    _ = Tantibar c ((polyTSq c)^[2] z) := by rw [h4]
    _ = star (polyS c ((polyTSq c)^[2] z)) := (star_polyS c _).symm
    _ = star (Qtc c z) := rfl

/-! ## 2. Differentiability of `Qtc c` -/

theorem differentiable_polyS (c : ℂ) : Differentiable ℂ (polyS c) := by
  unfold polyS; fun_prop

theorem differentiable_polyTSq (c : ℂ) : Differentiable ℂ (polyTSq c) := by
  unfold polyTSq; fun_prop

theorem differentiable_Qtc (c : ℂ) : Differentiable ℂ (Qtc c) := by
  have h : Differentiable ℂ ((polyTSq c)^[2]) := (differentiable_polyTSq c).iterate 2
  unfold Qtc
  exact (differentiable_polyS c).comp h

/-! ## 3. The conjugated map `star ∘ Qtc c ∘ star` -/

/-- `Qbar c = star ∘ Qtc c ∘ star`; it is holomorphic and `Ft c = Qbar c ∘ Qtc c`. -/
def Qbar (c : ℂ) : ℂ → ℂ := star ∘ Qtc c ∘ ⇑(starRingEnd ℂ)

theorem differentiable_Qbar (c : ℂ) : Differentiable ℂ (Qbar c) := by
  intro w
  have h := ((differentiable_Qtc c).differentiableAt (x := (starRingEnd ℂ) w)).star_conj
  rw [starRingEnd_self_apply] at h
  exact h

theorem deriv_Qbar (c : ℂ) :
    deriv (Qbar c) = star ∘ deriv (Qtc c) ∘ ⇑(starRingEnd ℂ) :=
  deriv_star_conj

theorem Ft_eq_Qbar_comp_Qtc (c : ℂ) : Ft c = Qbar c ∘ Qtc c := by
  have hQ : gtc c = star ∘ Qtc c := by
    funext z; rw [Function.comp_apply]; exact gtc_eq_star_Qtc c z
  rw [Work.PARIMPL.Ft_eq_g_comp, hQ]
  funext z
  simp only [Qbar, Function.comp_apply, starRingEnd_apply]

/-! ## 4. The main statement -/

theorem SymmDeriv_tricorn :
    (∀ c : ℂ, ∃ Q : ℂ → ℂ, Differentiable ℂ Q ∧ ∀ z : ℂ, gtc c z = star (Q z)) ∧
    ∀ (c p q : ℂ), gtc c p = q → gtc c q = p →
      deriv (Ft c) q = star (deriv (Ft c) p) := by
  refine ⟨?_, ?_⟩
  · intro c
    exact ⟨Qtc c, differentiable_Qtc c, gtc_eq_star_Qtc c⟩
  · intro c p q h1 h2
    have hQ : gtc c = star ∘ Qtc c := by
      funext z; rw [Function.comp_apply]; exact gtc_eq_star_Qtc c z
    have h1' : star (Qtc c p) = q := by
      have h := h1; rw [hQ] at h; simpa [Function.comp_apply] using h
    have h2' : star (Qtc c q) = p := by
      have h := h2; rw [hQ] at h; simpa [Function.comp_apply] using h
    have hFt : Ft c = Qbar c ∘ Qtc c := Ft_eq_Qbar_comp_Qtc c
    have hdQ : Differentiable ℂ (Qtc c) := differentiable_Qtc c
    have hdU : Differentiable ℂ (Qbar c) := differentiable_Qbar c
    have hderU : deriv (Qbar c) (Qtc c p) = star (deriv (Qtc c) q) := by
      rw [deriv_Qbar]
      simp only [Function.comp_apply]
      rw [starRingEnd_apply, h1']
    have hderU' : deriv (Qbar c) (Qtc c q) = star (deriv (Qtc c) p) := by
      rw [deriv_Qbar]
      simp only [Function.comp_apply]
      rw [starRingEnd_apply, h2']
    have hcp : deriv (Ft c) p
        = deriv (Qbar c) (Qtc c p) * deriv (Qtc c) p := by
      rw [hFt]
      exact deriv_comp p hdU.differentiableAt hdQ.differentiableAt
    have hcq : deriv (Ft c) q
        = deriv (Qbar c) (Qtc c q) * deriv (Qtc c) q := by
      rw [hFt]
      exact deriv_comp q hdU.differentiableAt hdQ.differentiableAt
    rw [hcp, hcq, hderU, hderU', star_mul, star_star, mul_comm]

end

end Work.FlowerGlue2
