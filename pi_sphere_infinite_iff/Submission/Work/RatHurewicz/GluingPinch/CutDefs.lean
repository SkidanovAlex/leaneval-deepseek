import Mathlib
import Submission.Work.RatHurewicz.GluingPinch.CoordGen
import Submission.Work.Stems.Hur2.Psi

/-!
# Cutting a based `n`-cube along a coordinate hyperplane: the two readings

Let `p : Ω^n(X,x₀)` be a based cube which is `x₀` on the hyperplane `{u i = a}`.  The two *affine
readings*

* `cutL i a p h` — `u ↦ p (update u i (clamp (a * u i)))` (the "left" half, rescaled),
* `cutR i a p h` — `u ↦ p (update u i (clamp (a + (1-a) * u i)))` (the "right" half, rescaled)

are again based cubes, and (the main content, `Work.RatHurewicz.cl_cut_gen`)

  `cl p = cl (cutL i a p h) * cl (cutR i a p h)`,

the general-`n`, general-coordinate form of `Work.Stems.Hur2b.cl_cut_vertical`.
-/

open scoped unitInterval Topology
open Work.Stems.Cubical
open Work.Stems.Hur2

namespace Work.RatHurewicz

noncomputable section

variable {X : Type} [TopologicalSpace X] {x₀ : X}

/-- The piecewise-linear map `I → I` with `0 ↦ 0`, `1/2 ↦ a`, `1 ↦ 1`, written with `min`/`max`
inside a `clamp` so that continuity is automatic.  (Copy of `Work.Stems.Hur2b.stretch`.) -/
def stretchI (a : unitInterval) : C(unitInterval, unitInterval) :=
  ⟨fun s => clamp (min (1:ℝ) (2 * (s : ℝ)) * (a : ℝ)
      + max (0:ℝ) (2 * (s : ℝ) - 1) * (1 - (a : ℝ))),
    continuous_clamp.comp (by fun_prop)⟩

theorem stretchI_zero_val (a : unitInterval) : stretchI a 0 = 0 := by
  show clamp (min (1:ℝ) (2 * ((0 : unitInterval) : ℝ)) * (a : ℝ)
    + max (0:ℝ) (2 * ((0 : unitInterval) : ℝ) - 1) * (1 - (a : ℝ))) = 0
  simp

theorem stretchI_one_val (a : unitInterval) : stretchI a 1 = 1 := by
  show clamp (min (1:ℝ) (2 * ((1 : unitInterval) : ℝ)) * (a : ℝ)
    + max (0:ℝ) (2 * ((1 : unitInterval) : ℝ) - 1) * (1 - (a : ℝ))) = 1
  have h : ((a:ℝ)) + (1 - (a:ℝ)) = 1 := by ring
  rw [show ((1 : unitInterval) : ℝ) = 1 from rfl]
  rw [show min (1:ℝ) (2 * (1:ℝ)) = 1 from by norm_num,
    show max (0:ℝ) (2 * (1:ℝ) - 1) = 1 from by norm_num, one_mul, one_mul, h, clamp_one]

/-- The reading of the left half `{u i ≤ a}` of the cube, rescaled by `a`. -/
def cutL {n : ℕ} (i : Fin n) (a : unitInterval) (p : GenLoop (Fin n) X x₀)
    (h : ∀ u : IC n, u i = a → p.1 u = x₀) : GenLoop (Fin n) X x₀ where
  val := p.1.comp ⟨fun u => Function.update u i (clamp ((a : ℝ) * ((u i : unitInterval) : ℝ))),
    continuous_id.update i (continuous_clamp.comp (continuous_const.mul
      (continuous_subtype_val.comp (continuous_apply i))))⟩
  property := by
    intro u hu
    show p.1 (Function.update u i (clamp ((a : ℝ) * ((u i : unitInterval) : ℝ)))) = x₀
    by_cases h1 : u i = 1
    · refine h _ ?_
      rw [Function.update_apply, if_pos rfl, h1]
      norm_num
      exact (clamp_of_mem a.2).trans rfl
    · by_cases h0 : u i = 0
      · refine p.2 _ ⟨i, Or.inl ?_⟩
        rw [Function.update_apply, if_pos rfl, h0]
        norm_num
      · obtain ⟨j, hj⟩ := hu
        have hji : j ≠ i := by
          rintro rfl
          rcases hj with hj | hj
          · exact h0 hj
          · exact h1 hj
        refine p.2 _ ⟨j, ?_⟩
        rw [Function.update_apply, if_neg hji]
        exact hj

/-- The reading of the right half `{u i ≥ a}` of the cube, rescaled by `1 - a`. -/
def cutR {n : ℕ} (i : Fin n) (a : unitInterval) (p : GenLoop (Fin n) X x₀)
    (h : ∀ u : IC n, u i = a → p.1 u = x₀) : GenLoop (Fin n) X x₀ where
  val := p.1.comp ⟨fun u => Function.update u i
      (clamp ((a : ℝ) + (1 - (a : ℝ)) * ((u i : unitInterval) : ℝ))),
    continuous_id.update i (continuous_clamp.comp (continuous_const.add
      ((continuous_const.sub continuous_const).mul
        (continuous_subtype_val.comp (continuous_apply i)))))⟩
  property := by
    intro u hu
    show p.1 (Function.update u i (clamp ((a : ℝ) + (1 - (a : ℝ)) *
      ((u i : unitInterval) : ℝ)))) = x₀
    by_cases h0 : u i = 0
    · refine h _ ?_
      rw [Function.update_apply, if_pos rfl, h0]
      norm_num
      exact (clamp_of_mem a.2).trans rfl
    · by_cases h1 : u i = 1
      · refine p.2 _ ⟨i, Or.inr ?_⟩
        rw [Function.update_apply, if_pos rfl, h1]
        norm_num
      · obtain ⟨j, hj⟩ := hu
        have hji : j ≠ i := by
          rintro rfl
          rcases hj with hj | hj
          · exact h0 hj
          · exact h1 hj
        refine p.2 _ ⟨j, ?_⟩
        rw [Function.update_apply, if_neg hji]
        exact hj

end

end Work.RatHurewicz
