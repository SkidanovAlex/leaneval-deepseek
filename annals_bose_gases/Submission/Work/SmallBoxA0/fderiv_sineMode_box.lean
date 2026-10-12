import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.SmallBoxModeParseval
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The directional derivative of the mixed Neumann/`sin` box mode along `ê_m`

(`Work.SmallBoxA0.fderiv_sineMode_box`.)

The function

  `y ↦ (∏_{i ≠ m} boxNeumann s (k i) (y i)) * sin (((k m)π/s) (y_m + s/2))`

is the product of the excited coordinates of the box Neumann mode `k` in the two
coordinates `i ≠ m` with the *other* branch of the same one-dimensional mode in
coordinate `m`: as `cos θ ' = -sin θ` and `sin θ ' = cos θ`, the sine branch is
the "conjugate" (Bogoliubov `b`-type) coordinate of the cosine mode.  Its
derivative in the direction `ê_m = kcStdBasis m` is the cosine factor times
`(k m)π/s`, giving `((k m)π/s) · boxNeumann3 s k z`.

The proof is the standard line computation

  `fderiv ℝ F z v = deriv (fun t ↦ F (z + t•v)) 0`

(`DifferentiableAt.deriv_comp_add_smul`), the product over `i ≠ m` being
constant along the line because `(z + t•ê_m) i = z i` there.
-/

namespace Work.SmallBoxA0

open Submission BoseGases
open scoped Real

set_option linter.unusedVariables false

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- Directional derivative of `(∏_{i ≠ m} u_{k i}(y_i)) · sin(a (y_m + s/2))`
along `ê_m`, with the `sin` left in its general linear-phase form `a`. -/
private lemma fderiv_eraseProd_sin {s a : ℝ} (k : Fin 3 → ℕ) (m : Fin 3) (z : ℝ³) :
    fderiv ℝ (fun y : ℝ³ => (∏ i ∈ Finset.univ.erase m, boxNeumann s (k i) (y i)) *
        Real.sin (a * (y m + s / 2))) z (kcStdBasis m)
      = a * ((∏ i ∈ Finset.univ.erase m, boxNeumann s (k i) (z i)) * Real.cos (a * (z m + s / 2))) := by
  let F : ℝ³ → ℝ := fun y => (∏ i ∈ Finset.univ.erase m, boxNeumann s (k i) (y i)) *
      Real.sin (a * (y m + s / 2))
  change fderiv ℝ F z (kcStdBasis m)
      = a * ((∏ i ∈ Finset.univ.erase m, boxNeumann s (k i) (z i)) * Real.cos (a * (z m + s / 2)))
  have hdiff : DifferentiableAt ℝ F z := by
    dsimp only [F]
    apply DifferentiableAt.mul
    · unfold boxNeumann; fun_prop
    · fun_prop
  have hdiff' : DifferentiableAt ℝ F (z + (0 : ℝ) • kcStdBasis m) := by simpa using hdiff
  have hlin : deriv (fun u : ℝ => F (z + u • kcStdBasis m)) 0 = fderiv ℝ F z (kcStdBasis m) := by
    have h := DifferentiableAt.deriv_comp_add_smul (𝕜 := ℝ) (f := F) (x := z)
      (y := kcStdBasis m) (t := (0 : ℝ)) hdiff'
    simpa using h
  rw [← hlin]
  have hfun : (fun u : ℝ => F (z + u • kcStdBasis m))
      = fun u : ℝ => (∏ i ∈ Finset.univ.erase m, boxNeumann s (k i) (z i)) *
          Real.sin (a * (z m + u + s / 2)) := by
    funext u
    dsimp only [F]
    have hprod : (∏ i ∈ Finset.univ.erase m, boxNeumann s (k i) ((z + u • kcStdBasis m) i))
        = (∏ i ∈ Finset.univ.erase m, boxNeumann s (k i) (z i)) := by
      apply Finset.prod_congr rfl
      intro i hi
      have hne : i ≠ m := Finset.ne_of_mem_erase hi
      simp [kcStdBasis, hne]
    have hm : (z + u • kcStdBasis m) m = z m + u := by simp [kcStdBasis]
    rw [hprod, hm]
  rw [hfun]
  have h1 : HasDerivAt (fun u : ℝ => a * (z m + u + s / 2)) a 0 := by
    have h : HasDerivAt (fun u : ℝ => (z m + s / 2) + u) 1 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_add (z m + s / 2)
    have he : (fun u : ℝ => a * (z m + u + s / 2)) = fun u : ℝ => a * ((z m + s / 2) + u) := by
      funext u; ring
    rw [he]
    simpa using h.const_mul a
  have hsin : HasDerivAt (fun u : ℝ => Real.sin (a * (z m + u + s / 2)))
      (Real.cos (a * (z m + 0 + s / 2)) * a) 0 := by
    have h := (Real.hasDerivAt_sin (a * (z m + 0 + s / 2))).comp 0 h1
    simpa only [Function.comp_def, add_zero] using h
  have hderiv := (hsin.const_mul (∏ i ∈ Finset.univ.erase m, boxNeumann s (k i) (z i))).deriv
  rw [hderiv]
  simp only [add_zero]
  ring

lemma fderiv_sineMode_box {s : ℝ} (hs : 0 < s) (m : Fin 3) (k : Fin 3 → ℕ)
    (z : EuclideanSpace ℝ (Fin 3)) :
    fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 3) =>
        (∏ i ∈ Finset.univ.erase m, Submission.BoseGases.boxNeumann s (k i) (y i)) *
          Real.sin (((k m : ℝ) * Real.pi / s) * (y m + s / 2))) z
        (Submission.BoseGases.kcStdBasis m)
      = ((k m : ℝ) * Real.pi / s) * Submission.BoseGases.boxNeumann3 s k z := by
  rw [fderiv_eraseProd_sin (s := s) (a := (k m : ℝ) * Real.pi / s) (k := k) (m := m) (z := z)]
  congr 1
  rw [boxNeumann3, ← Finset.prod_erase_mul Finset.univ (fun j => boxNeumann s (k j) (z j))
        (Finset.mem_univ m)]
  simp only [boxNeumann]

end Work.SmallBoxA0
