import Mathlib
import Submission.Work.NN.Core.Defs

namespace Work.NN.Core

open LeanEval.Geometry.NewlanderNirenberg
open Submission
open Set
open scoped ContDiff

/-- Perturbing a bijective real-linear continuous map by a map small enough (measured after
composing with the inverse) keeps it bijective.  Applied to `T₀ = tupleDeriv T` and
`S =` the differential of the correction, this is the invertibility step of the argument. -/
lemma bijective_add_of_norm_comp_lt_one {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (T₀ : X →L[ℝ] Y) (T₀inv : Y →L[ℝ] X) (h1 : T₀inv.comp T₀ = 1) (h2 : T₀.comp T₀inv = 1)
    (S : X →L[ℝ] Y) (hS : ‖T₀inv.comp S‖ < 1) : Function.Bijective (T₀ + S) := by
  -- Write `T₀ + S = T₀ ∘ (1 + T₀inv ∘ S)`; it suffices to know that both factors are bijective.
  set A : X →L[ℝ] X := T₀inv.comp S with hA
  have hA' : ‖A‖ < 1 := by rw [hA]; exact hS
  -- `1 + A = 1 - (-A)` is a unit of the Banach algebra `X →L[ℝ] X` by the Neumann series,
  -- and on a Banach space a continuous linear endomorphism is a unit iff it is bijective.
  have hunit : IsUnit ((1 : X →L[ℝ] X) + A) := by
    have h : ‖(-A : X →L[ℝ] X)‖ < 1 := by simpa using hA'
    have := isUnit_one_sub_of_norm_lt_one (R := X →L[ℝ] X) h
    simpa using this
  have hU : Function.Bijective ((1 : X →L[ℝ] X) + A) :=
    ContinuousLinearMap.isUnit_iff_bijective.mp hunit
  -- `T₀` is bijective, with the two-sided inverse `T₀inv`.
  have hT : Function.Bijective (T₀ : X → Y) := by
    constructor
    · intro x y hxy
      have hx : T₀inv (T₀ x) = x := by rw [← ContinuousLinearMap.comp_apply, h1]; rfl
      have hy : T₀inv (T₀ y) = y := by rw [← ContinuousLinearMap.comp_apply, h1]; rfl
      rw [hxy] at hx
      exact hx.symm.trans hy
    · intro y
      exact ⟨T₀inv y, by rw [← ContinuousLinearMap.comp_apply, h2]; rfl⟩
  -- Identify `T₀ + S` with the composition `T₀ ∘ (1 + A)`.
  have hfactor : (T₀ + S) = T₀.comp ((1 : X →L[ℝ] X) + A) := by
    ext x
    simp only [ContinuousLinearMap.comp_apply, add_apply]
    rw [show (1 : X →L[ℝ] X) x = x by rfl, map_add]
    have hTA : T₀ (A x) = S x := by
      rw [hA, ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.comp_apply, h2]
      rfl
    rw [hTA]
  rw [hfactor, ContinuousLinearMap.coe_comp]
  exact hT.comp hU

end Work.NN.Core
