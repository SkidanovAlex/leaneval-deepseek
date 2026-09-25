import Mathlib
import Submission.Work.Core.Defs
import Submission.Work.Core.Solvable

namespace Work.Translate

open LeanEval.Geometry.NewlanderNirenberg
open Submission
open Set
open scoped ContDiff

/-- `zcoord T j` is linear, hence `zcoord T j (y - x) + zcoord T j x = zcoord T j y`. -/
lemma zcoord_sub_add {n : ℕ} (T : E n ≃L[ℝ] F n) (j : Fin n) (y x : E n) :
    zcoord T j (y - x) + zcoord T j x = zcoord T j y := by
  simp only [zcoord, map_sub, Pi.sub_apply]
  ring

/-- Translation of `∂̄`: composing the unknown with `y ↦ y - x` corresponds to translating the
structure by `x`. -/
lemma dbar_comp_sub {n : ℕ} (J : E n → E n →L[ℝ] E n) (u : E n → ℂ) (x y : E n) :
    dbar J (fun z => u (z - x)) y = dbar (fun z => J (x + z)) u (y - x) := by
  have h1 : fderiv ℝ (fun z => u (z - x)) y = fderiv ℝ u (y - x) := fderiv_comp_sub x
  have h2 : x + (y - x) = y := add_sub_cancel x y
  simp only [dbar, h1, h2]

/-- Differential of the translated tuple of coordinates: the coordinate functions are linear
(so their derivatives are translation invariant) and adding the constant `(zcoord T j x)_j`
does not change the derivative. -/
lemma fderiv_translate_tuple {n : ℕ} (T : E n ≃L[ℝ] F n) (v : Fin n → E n → ℂ)
    (x y : E n) :
    fderiv ℝ (fun y' => fun j => zcoord T j y' - v j (y' - x)) y
      = fderiv ℝ (fun z => fun j => zcoord T j z - v j z) (y - x) := by
  set Ψ : E n → (Fin n → ℂ) := fun z => fun j => zcoord T j z - v j z with hΨ
  set c : Fin n → ℂ := fun j => zcoord T j x with hc
  have hfun : (fun y' => fun j => zcoord T j y' - v j (y' - x))
      = fun y' => Ψ (y' - x) + c := by
    funext y' j
    simp only [hΨ, hc, Pi.add_apply]
    rw [← zcoord_sub_add T j y' x]
    ring
  rw [hfun, fderiv_add_const c, fderiv_comp_sub (f := Ψ) x]

/-- **Translation of the analytic input to a general point.**  Everything in the workspace
(`Submission/DbarSolvable` and the solvers built by the subprojects) is stated at the origin.  If
the analytic input holds for the translation `y ↦ x + y` of the structure `J` at `0`, then it
holds for `J` at `x`: the correcting functions are translated back, the standard coordinates
`zcoord T j` are linear so their differentials are translation invariant, and translations do not
change derivatives.

This is the glue needed to apply a solver proved at `0` (e.g. `Work.NN.Core.dbarSolvable_of_pert`)
at an arbitrary point of `U`. -/
theorem ofTranslate {n : ℕ} {U : Set (E n)} (hU : IsOpen U) (x : E n)
    {J : E n → E n →L[ℝ] E n} {T : E n ≃L[ℝ] F n}
    (h : DbarSolvable (fun y => J (x + y)) {y | x + y ∈ U} 0 T) :
    DbarSolvable J U x T := by
  obtain ⟨V₀, hV₀, h0V₀, hV₀U, v₀, hv₀, hv₀eq, hv₀inv⟩ := h
  refine ⟨{y | y - x ∈ V₀}, ?_, ?_, ?_, ?_⟩
  · exact IsOpen.preimage (continuous_id.sub continuous_const) hV₀
  · simpa using h0V₀
  · intro y hy
    simpa [add_sub_cancel] using hV₀U hy
  · refine ⟨fun j y => v₀ j (y - x), ?_, ?_, ?_⟩
    · intro j
      exact (hv₀ j).comp ((contDiff_id.sub contDiff_const).contDiffOn (s := {y | y - x ∈ V₀}))
        (fun y hy => hy)
    · intro j y hy
      rw [dbar_comp_sub J (v₀ j) x y, hv₀eq j (y - x) hy]
      simp only [fderiv_zcoord, stdOf, add_sub_cancel]
    · intro y hy
      rw [fderiv_translate_tuple T v₀ x y]
      exact hv₀inv (y - x) hy

end Work.Translate
