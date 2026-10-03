import Mathlib
import Submission.Work.Pert.tSat_glue
import Submission.Work.Pert.RBlock

/-!
# `Work.Pert.pert2v2.glue_window` — the two-piece glue, with *vacuous* compatibilities

`Work.Pert.tSat_glue` glues a family of local charts `(U i, R i)` into one `T`-equivariant
holomorphic map `R'` on the `ℤ`-saturation `D = ⋃ i ⋃ n (U i + n)`, the compatibility hypothesis
being

  `hcompat : w ∈ U i → w + n ∈ U j → R j (w + n) = R i w + n`.

For the §4.2 design the family is `ι = Bool` with

* `U false` = the low piece (crux formula `RlowPiece`, inside `{|Re| < 1/2} ∩ {|Im| ≤ Hband}`), and
* `U true`  = the high piece (`retOf`/`retP` on the waist image, inside `{|Re| < 1/2} ∩ {Hband < |Im|}`),

and the compatibility hypothesis — the one thing that would otherwise need a genuine
overlap computation — is **vacuous**, for two independent reasons:

* **the open window `|Re| < 1/2`** kills the same-chart case `i = j`, `n ≠ 0`: if
  `|Re w| < 1/2` and `|Re (w + n)| < 1/2` with `n ≠ 0`, then `1 ≤ |n| ≤ |Re w| + |Re (w+n)| < 1`,
  a contradiction;
* **pairwise disjoint `Im`-ranges** kill the mixed case `i ≠ j`: `(w + n).im = w.im`, so a point of
  `U i` and a point of `U j` with the same imaginary part cannot coexist.

So it suffices to provide openness, holomorphy and *disjoint imaginary parts* for the pieces; the
gluing then produces `R'`, and the design's `R` is `R'` (`R` is determined by its values on the
window pieces through the equivariance).

This file contains the glue core; the two concrete pieces (`Ulow`/`RlowPiece` and
`Uhigh`/`retOf`) are `Work.Pert.pert2v2.low_piece_data` and `Work.Pert.pert2v2.high_piece_data`.
-/

namespace Work.Pert.pert2v2

open Set

/-- **The two-piece glue with vacuous compatibilities.**  If every chart lives in the open window
`{|Re| < 1/2}` and the charts have pairwise disjoint imaginary parts, then `Work.Pert.tSat_glue`
applies, and the glued map is the `T`-equivariant extension of the given local maps. -/
theorem tSat_glue_window {ι : Type*} (U : ι → Set ℂ) (R : ι → ℂ → ℂ)
    (hU : ∀ i, IsOpen (U i)) (hR : ∀ i, DifferentiableOn ℂ (R i) (U i))
    (hwindow : ∀ i, U i ⊆ {w : ℂ | |w.re| < 1 / 2})
    (himdisj : ∀ i j, i ≠ j → ∀ a b : ℂ, a ∈ U i → b ∈ U j → a.im ≠ b.im) :
    ∃ R' : ℂ → ℂ, IsOpen (⋃ i, ⋃ n : ℤ, (fun w => w + (n : ℂ)) '' U i) ∧
      MandelDim.IsTEquivariantOn R' (⋃ i, ⋃ n : ℤ, (fun w => w + (n : ℂ)) '' U i) ∧
      DifferentiableOn ℂ R' (⋃ i, ⋃ n : ℤ, (fun w => w + (n : ℂ)) '' U i) ∧
      ∀ i, ∀ w ∈ U i, R' w = R i w := by
  classical
  refine tSat_glue U R hU hR ?_
  intro i j n w hwi hwj
  rcases eq_or_ne i j with rfl | hij
  · -- same chart: `n ≠ 0` cannot happen inside the open window `|Re| < 1/2`
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · exfalso
      have h1 : |w.re| < 1 / 2 := hwindow i hwi
      have h2 : |(w + (n : ℂ)).re| < 1 / 2 := hwindow i hwj
      have hre : (w + (n : ℂ)).re = w.re + ((n : ℤ) : ℝ) := by simp
      have h1' : -(1 / 2 : ℝ) < w.re := (abs_lt.mp h1).1
      have h1'' : w.re < 1 / 2 := (abs_lt.mp h1).2
      have h2' : -(1 / 2 : ℝ) < w.re + ((n : ℤ) : ℝ) := by
        rw [← hre]; exact (abs_lt.mp h2).1
      have h2'' : w.re + ((n : ℤ) : ℝ) < 1 / 2 := by
        rw [← hre]; exact (abs_lt.mp h2).2
      have hnlt : |((n : ℤ) : ℝ)| < 1 := by
        rw [abs_lt]
        constructor <;> linarith
      have hge : (1 : ℝ) ≤ |((n : ℤ) : ℝ)| := by
        have := Int.one_le_abs hn
        exact_mod_cast this
      linarith
  · -- different charts: the imaginary parts cannot agree
    exfalso
    exact himdisj i j hij w (w + (n : ℂ)) hwi hwj (by simp)

/- **DONE (session 25):** the `ι = Bool` packaging is
`Work.Pert.pert2v2.glue_window_bool` in `Submission/Work/Pert/pert2v2/glue_window_bool.lean`
(proved, axiom-clean).  Together with `tSat_glue_window` above, the two chart inputs
(`Work.Pert.pert2v2.low_piece_data`, `Work.Pert.pert2v2.high_piece_data`) and this packaging, the
`tSat_glue` row of the §4.2 design is **complete**: `R` is produced on the `ℤ`-saturation of the two
window pieces with *vacuous* compatibility conditions. -/

end Work.Pert.pert2v2
