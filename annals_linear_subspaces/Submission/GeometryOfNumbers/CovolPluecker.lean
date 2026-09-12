import Mathlib
import Submission.GeometryOfNumbers.SubLatticeCovol
import Submission.Commons.Analysis.InnerProductSpace.exteriorPower_norm_intersection_le
import Submission.Commons.LinearAlgebra.ExteriorPower.iMulti_ne_zero_of_linearIndependent

/-!
# The P1 engine: covolume (Euclidean) Plücker inequality for aligned sublattice bases

de Saxcé Lemma 3 (paper §3) is the submodularity of the Grayson data
`φ(W) = log‖W‖ + A·(dim W)(d − dim W)` over the discrete subgroups of a lattice, proved
from the Euclidean Plücker inequality `‖V‖₂·‖W‖₂ ≥ ‖V∩W‖₂·‖V+W‖₂` on wedge norms
(plus norm-equivalence, absorbed by the quadratic term).  In the Euclidean model we use
`‖W‖ := covolume of `W` inside its own real span`, which by
`SubLatticeCovol.covol_saturated_wedge` equals the **ambient wedge norm** `‖ιMulti b‖` of a
`ℤ`-basis `b` of `W`.  With `ℤ`-bases of two saturated sublattices aligned as
`u ++ x` (of `V`), `u ++ y` (of `W`) over a common `ℤ`-basis `u` of `V ∩ W`
(possible by the pure-basis-extension theorems of the Commons), the Plücker inequality is
exactly the pure exterior-power statement of the Commons
(`exteriorPower_norm_intersection_le`), and the covolume vocabulary is transported by
`covol_saturated_wedge`.

This module records the resulting **aligned-family engine** — covolume form and
log-submodularity form — over the standard space `E = EuclideanSpace ℝ (Fin d)`:

    covol(u++x)·covol(u++y) ≥ covol(u)·covol((u++x)++y)
    log covol(u++x) + log covol(u++y) ≥ log covol(u) + log covol((u++x)++y)

for `ℝ`-independent families `u : Fin m → E`, `x : Fin a → E`, `y : Fin b → E`
(`0 < m`; degenerate rank-0 terms contribute `log 1 = 0` at consumers).  Here
`covol w` is the covolume of the `ℤ`-span of `w` inside its own real span
`span ℝ (range w)`.  Consumers (the Grayson-polygon data over saturated subgroups of the
model flow lattice, ROADMAP session-78 next item) instantiate `u, x, y` as the aligned
`ℤ`-bases obtained from the basis-extension theorems, and combine the second form with the
quadratic-submodularity inequality `Commons.Lattice.Counting.grassmann_codim_incomparable`
for the `A·rank(d−rank)` term.
-/

noncomputable section

open Set Filter Metric MeasureTheory Module Real BigOperators exteriorPower
open scoped ENNReal
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace Submission.CovolPluecker

/-- Covolume of the `ℤ`-span of the family `u` inside its own real span
`span ℝ (range u)`: `covolFamily u = covol(span ℤ u ; span ℝ u)`. -/
noncomputable def covolFamily {d r : ℕ} (u : Fin r → EuclideanSpace ℝ (Fin d)) : ℝ :=
  ZLattice.covolume (Submodule.span ℤ (Set.range (fun i : Fin r =>
      (⟨u i, Submodule.subset_span (by simp)⟩ : Submodule.span ℝ (Set.range u)))))

/-- The covolume of the lattice of an independent family is strictly positive
(equals the positive wedge norm). -/
lemma covolFamily_pos_of_linearIndependent {d r : ℕ} (hr : 0 < r)
    (u : Fin r → EuclideanSpace ℝ (Fin d)) (hu : LinearIndependent ℝ u) :
    0 < covolFamily u := by
  have hw : exteriorPower.ιMulti ℝ r u ≠ 0 :=
    Commons.LinearAlgebra.ExteriorPower.iMulti_ne_zero_of_linearIndependent (K := ℝ) (k := r) u hu
  rw [covolFamily]
  rw [Submission.SubLatticeCovol.covol_saturated_wedge hr u hu]
  exact norm_pos_iff.mpr hw

/-- The covolume of the lattice of an independent family is non-zero. -/
lemma covolFamily_ne_zero_of_linearIndependent {d r : ℕ} (hr : 0 < r)
    (u : Fin r → EuclideanSpace ℝ (Fin d)) (hu : LinearIndependent ℝ u) :
    covolFamily u ≠ 0 :=
  ne_of_gt (covolFamily_pos_of_linearIndependent hr u hu)

/-- **P1 engine, covolume form.**  For `ℝ`-independent aligned families
(`u` a common basis of the intersection, `u++x` of one subspace, `u++y` of the other,
`(u++x)++y` of the sum), the covolume Plücker inequality holds:

`covol(u++x)·covol(u++y) ≥ covol(u)·covol((u++x)++y)`. -/
theorem covolPluecker_aligned {d m a b : ℕ} (hm : 0 < m)
    (u : Fin m → EuclideanSpace ℝ (Fin d)) (x : Fin a → EuclideanSpace ℝ (Fin d))
    (y : Fin b → EuclideanSpace ℝ (Fin d)) (hu : LinearIndependent ℝ u)
    (hux : LinearIndependent ℝ (Fin.append u x))
    (huy : LinearIndependent ℝ (Fin.append u y))
    (huxy : LinearIndependent ℝ (Fin.append (Fin.append u x) y)) :
    covolFamily (Fin.append u x) * covolFamily (Fin.append u y) ≥
      covolFamily u * covolFamily (Fin.append (Fin.append u x) y) := by
  rw [covolFamily, covolFamily, covolFamily, covolFamily]
  rw [Submission.SubLatticeCovol.covol_saturated_wedge (hr := (by omega : 0 < m + a))
    (u := Fin.append u x) hux]
  rw [Submission.SubLatticeCovol.covol_saturated_wedge (hr := (by omega : 0 < m + b))
    (u := Fin.append u y) huy]
  rw [Submission.SubLatticeCovol.covol_saturated_wedge hm u hu]
  rw [Submission.SubLatticeCovol.covol_saturated_wedge (hr := (by omega : 0 < m + a + b))
    (u := Fin.append (Fin.append u x) y) huxy]
  exact Commons.Analysis.InnerProductSpace.exteriorPower_norm_intersection_le (u := u) (x := x) (y := y)

/-- **P1 engine, log form** (the Euclidean Lemma-3 core, `A = 0`): for aligned independent
families, the log-covolumes are submodular:

`log covol(u++x) + log covol(u++y) ≥ log covol(u) + log covol((u++x)++y)`. -/
theorem covolPluecker_aligned_log {d m a b : ℕ} (hm : 0 < m)
    (u : Fin m → EuclideanSpace ℝ (Fin d)) (x : Fin a → EuclideanSpace ℝ (Fin d))
    (y : Fin b → EuclideanSpace ℝ (Fin d)) (hu : LinearIndependent ℝ u)
    (hux : LinearIndependent ℝ (Fin.append u x))
    (huy : LinearIndependent ℝ (Fin.append u y))
    (huxy : LinearIndependent ℝ (Fin.append (Fin.append u x) y)) :
    Real.log (covolFamily (Fin.append u x)) + Real.log (covolFamily (Fin.append u y)) ≥
      Real.log (covolFamily u) + Real.log (covolFamily (Fin.append (Fin.append u x) y)) := by
  have hx1 := covolFamily_ne_zero_of_linearIndependent (hr := (by omega : 0 < m + a))
    (u := Fin.append u x) hux
  have hx2 := covolFamily_ne_zero_of_linearIndependent (hr := (by omega : 0 < m + b))
    (u := Fin.append u y) huy
  have hx3 := covolFamily_ne_zero_of_linearIndependent hm u hu
  have hx4 := covolFamily_ne_zero_of_linearIndependent (hr := (by omega : 0 < m + a + b))
    (u := Fin.append (Fin.append u x) y) huxy
  have hpos : 0 < covolFamily u * covolFamily (Fin.append (Fin.append u x) y) :=
    mul_pos (covolFamily_pos_of_linearIndependent hm u hu)
      (covolFamily_pos_of_linearIndependent (hr := (by omega : 0 < m + a + b))
        (u := Fin.append (Fin.append u x) y) huxy)
  calc
    Real.log (covolFamily (Fin.append u x)) + Real.log (covolFamily (Fin.append u y))
        = Real.log (covolFamily (Fin.append u x) * covolFamily (Fin.append u y)) := by
          rw [Real.log_mul hx1 hx2]
    _ ≥ Real.log (covolFamily u * covolFamily (Fin.append (Fin.append u x) y)) := by
          exact Real.log_le_log hpos (covolPluecker_aligned hm u x y hu hux huy huxy)
    _ = Real.log (covolFamily u) + Real.log (covolFamily (Fin.append (Fin.append u x) y)) := by
          rw [Real.log_mul hx3 hx4]

end Submission.CovolPluecker
