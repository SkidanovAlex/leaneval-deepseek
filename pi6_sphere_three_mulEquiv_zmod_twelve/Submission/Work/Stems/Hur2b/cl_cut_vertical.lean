import Mathlib
import Submission.Work.Stems.Hur2b.CutLemma
import Submission.Work.Stems.WedgePinch

/-!
# The vertical cut lemma for based `2`-cubes

Let `p : Ω²(X,x₀)` be a based `2`-cube which is `x₀` on the straight line `{y₀ = a}`.  Then its
class in `π₂(X,x₀)` is the product of the classes of the two *affine column readings*
`cutL a p h` and `cutR a p h` (the restrictions of `p` to the columns `[0,a] × I` and `[a,1] × I`,
read via the affine parametrisations `(a·y₀, y₁)` and `(a + (1-a)·y₀, y₁)`).

The proof is the one described in `Submission/Work/Stems/Hur2b/CutLemma.lean`: the piecewise-linear
stretch `stretch a` (with `stretch a 0 = 0`, `stretch a (1/2) = a`, `stretch a 1 = 1`) moves the
line `{y₀ = a}` to the midline, which does not change the class (`cl_reparam_coord`); on the two
halves of the square the stretched reading is *definitionally* the concatenation
`GenLoop.transAt 0 (cutL a p h) (cutR a p h)` of the two affine column readings, whose class splits
by `HomotopyGroup.mul_spec` (`cl_transAt_zero`).  The two halves meet along the line `{y₀ = 1/2}`,
where both give `x₀` because `stretch a (1/2) = a` and `p` vanishes on `{y₀ = a}`.
-/

open scoped unitInterval Topology

namespace Work.Stems.Hur2b

open Work.Stems.Cubical
open Work.Stems.Hur2

variable {X : Type} [TopologicalSpace X] {x₀ : X}

/-- The defining formula of the piecewise-linear stretch, exposed for rewriting. -/
theorem stretch_apply (a : unitInterval) (s : unitInterval) :
    stretch a s = clamp (min 1 (2 * (s : ℝ)) * (a : ℝ)
      + max 0 (2 * (s : ℝ) - 1) * (1 - (a : ℝ))) := rfl

/-- In the left half of the square (`y₀ ≤ 1/2`), the column reading `colMap a` of the rescaled
point `sigmaA 0 y` is the strided reading `coordMap (stretch a) y`. -/
theorem colMap_sigmaA (a : unitInterval) (t : IC 2) (ht : (t 0 : ℝ) ≤ 1 / 2) :
    colMap a (Work.Stems.sigmaA (n := 2) 0 t) = coordMap (stretch a) t := by
  have ht0 : (0 : ℝ) ≤ (t 0 : ℝ) := (t 0).2.1
  have ht1 : (t 0 : ℝ) ≤ 1 := (t 0).2.2
  have h1 : ((Work.Stems.sigmaA (n := 2) 0 t) 0 : ℝ) = 2 * (t 0 : ℝ) := by
    rw [Work.Stems.sigmaA_apply_self, Set.coe_projIcc,
      min_eq_right (show (2 : ℝ) * (t 0 : ℝ) ≤ 1 by linarith),
      max_eq_right (show (0 : ℝ) ≤ 2 * (t 0 : ℝ) by linarith)]
  have h2 : Work.Stems.sigmaA (n := 2) 0 t 1 = t 1 :=
    Work.Stems.sigmaA_apply_of_ne 0 t (show (1 : Fin 2) ≠ 0 by decide)
  funext j
  fin_cases j
  · show clamp ((a : ℝ) * ((Work.Stems.sigmaA (n := 2) 0 t) 0 : ℝ)) = stretch a (t 0)
    rw [h1, stretch_apply,
      min_eq_right (show (2 : ℝ) * (t 0 : ℝ) ≤ 1 by linarith),
      max_eq_left (show (2 : ℝ) * (t 0 : ℝ) - 1 ≤ 0 by linarith), zero_mul, add_zero]
    exact congrArg clamp (by ring)
  · show ((Work.Stems.sigmaA (n := 2) 0 t) 1) = t 1
    exact h2

/-- In the right half of the square (`1/2 < y₀`), the column reading `colMapR a` of the rescaled
point `sigmaB 0 y` is the strided reading `coordMap (stretch a) y`. -/
theorem colMapR_sigmaB (a : unitInterval) (t : IC 2) (ht : 1 / 2 < (t 0 : ℝ)) :
    colMapR a (Work.Stems.sigmaB (n := 2) 0 t) = coordMap (stretch a) t := by
  have ht0 : (0 : ℝ) ≤ (t 0 : ℝ) := (t 0).2.1
  have ht1 : (t 0 : ℝ) ≤ 1 := (t 0).2.2
  have h1 : ((Work.Stems.sigmaB (n := 2) 0 t) 0 : ℝ) = 2 * (t 0 : ℝ) - 1 := by
    rw [Work.Stems.sigmaB_apply_self, Set.coe_projIcc,
      min_eq_right (show (2 : ℝ) * (t 0 : ℝ) - 1 ≤ 1 by linarith),
      max_eq_right (show (0 : ℝ) ≤ 2 * (t 0 : ℝ) - 1 by linarith)]
  have h2 : Work.Stems.sigmaB (n := 2) 0 t 1 = t 1 :=
    Work.Stems.sigmaB_apply_of_ne 0 t (show (1 : Fin 2) ≠ 0 by decide)
  funext j
  fin_cases j
  · show clamp ((a : ℝ) + (1 - (a : ℝ)) * ((Work.Stems.sigmaB (n := 2) 0 t) 0 : ℝ))
      = stretch a (t 0)
    rw [h1, stretch_apply,
      min_eq_left (show (1 : ℝ) ≤ 2 * (t 0 : ℝ) by linarith),
      max_eq_right (show (0 : ℝ) ≤ 2 * (t 0 : ℝ) - 1 by linarith), one_mul]
    exact congrArg clamp (by ring)
  · show ((Work.Stems.sigmaB (n := 2) 0 t) 1) = t 1
    exact h2

/-- **The vertical cut lemma.**  A based `2`-cube which is `x₀` on the straight line `{y₀ = a}`
splits, in `π₂(X,x₀)`, as the product of the classes of its two affine column readings. -/
theorem cl_cut_vertical {X : Type} [TopologicalSpace X] {x₀ : X} (p : GenLoop (Fin 2) X x₀)
    (a : unitInterval) (h : ∀ s : unitInterval, p.1 (Work.Stems.Hur2.pair2 a s) = x₀) :
    Work.Stems.Hur2b.cl x₀ p = Work.Stems.Hur2b.cl x₀ (Work.Stems.Hur2b.cutL a p h) *
      Work.Stems.Hur2b.cl x₀ (Work.Stems.Hur2b.cutR a p h) := by
  -- the stretched cube `p ∘ (stretch a)`, whose class is that of `p`
  let qq : GenLoop (Fin 2) X x₀ := compGenLoop (c := p) (φ := coordMap (stretch a))
    (fun y hy => p.2 _ (coordMap_mem_boundary (stretch_zero_val a) (stretch_one_val a) hy))
  have hσ : cl x₀ qq = cl x₀ p :=
    cl_reparam_coord p (stretch a) (stretch_zero_val a) (stretch_one_val a)
  -- the stretched cube is the concatenation of the two affine column readings
  have heq : GenLoop.transAt 0 (cutL a p h) (cutR a p h) = qq := by
    apply Subtype.ext
    apply ContinuousMap.ext
    intro t
    show (if (t 0 : ℝ) ≤ 1 / 2 then (cutL a p h) (Work.Stems.sigmaA (n := 2) 0 t)
      else (cutR a p h) (Work.Stems.sigmaB (n := 2) 0 t)) = qq t
    by_cases ht : (t 0 : ℝ) ≤ 1 / 2
    · rw [if_pos ht]
      show p.1 (colMap a (Work.Stems.sigmaA (n := 2) 0 t)) = p.1 (coordMap (stretch a) t)
      rw [colMap_sigmaA a t ht]
    · rw [if_neg ht]
      show p.1 (colMapR a (Work.Stems.sigmaB (n := 2) 0 t)) = p.1 (coordMap (stretch a) t)
      rw [colMapR_sigmaB a t (not_le.mp ht)]
  calc cl x₀ p = cl x₀ qq := hσ.symm
    _ = cl x₀ (GenLoop.transAt 0 (cutL a p h) (cutR a p h)) := by rw [heq]
    _ = cl x₀ (cutR a p h) * cl x₀ (cutL a p h) := cl_transAt_zero (cutR a p h) (cutL a p h)
    _ = cl x₀ (cutL a p h) * cl x₀ (cutR a p h) := mul_comm _ _

end Work.Stems.Hur2b
