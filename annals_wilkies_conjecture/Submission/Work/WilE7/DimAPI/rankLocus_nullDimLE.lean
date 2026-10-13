/-
  `Work.WilE7.DimAPI.rankLocus_nullDimLE` — the Sard node C1 of the E7 main design
  (`Submission/Work/WilE7/E7main_DESIGN.md`): the locus of an absolute `Good` stratum where the
  projection rank is `≤ r` projects to a `NullDimLE r` set.

  The route is the one recorded in the design:

  * `sardOnLevelSet` (the level-set form of the general Sard lemma for analytic maps,
    `Submission/Work/WilE9G/Sard/sardOnLevelSet.lean`) applied at each point `z₀` of the stratum
    to the equation family `h := fun z a => eaEval S.X.c (S.h a) z` and the coordinate projection
    `F := coordMap n m (r+1) e`: the points of the rank-`≤ r` locus are exactly the points where
    the restriction of `dF` to `ker (jac S z) = ker (dh z)` is *not* surjective onto `ℝ^{r+1}`,
    which is the criticality condition of Sard;
  * the countable-cover lemma `glueNull` turns the pointwise information into the global
    `volume (F '' locus) = 0`;
  * `image_coordMap` identifies the set of `NullDimLE` with the image of the coordinate map.
-/
import Mathlib
import Submission.Work.WilE7.MainDesignDefs
import Submission.Work.WilE7.DimAPI.rankLocusAux
import Submission.Work.WilE7.DimAPI.finrank_range_mulVecLin_submatrix_natAdd
import Submission.Work.WilE7.DimAPI.rankLocusLocal
import Submission.Work.WilE9G.Sard.sardOnLevelSet
import Submission.Work.WilE9G.Sard.glueNull

set_option autoImplicit false
noncomputable section
open Classical Filter Topology
namespace Work.WilE7.DimAPI
open WilkiesDesign WilkiesDesign.E
open Work.WilE7.MainDesign

/-- The Jacobian of the equations of an absolute `Good` stratum has full row rank: its range has
dimension `S.j`.  (`Good` gives the rank of the equations' Jacobian with the columns indexed by
`Fin N` through `Fin.natAdd 0`; `jac` indexes them by `Fin (0 + N)`, and the two indexings differ
by the relabelling `Fin.natAdd 0 : Fin N ≃ Fin (0 + N)`, which is the delegated lemma
`finrank_range_mulVecLin_submatrix_natAdd`.) -/
theorem jacRankGood {N : ℕ} (S : Stratum 0 N) (hS : S.Good) {z : Fin (0 + N) → ℝ}
    (hz : z ∈ S.X.set) :
    Module.finrank ℝ (LinearMap.range (jac S z)) = S.j := by
  rw [MainDesign.jac]
  rw [← finrank_range_mulVecLin_submatrix_natAdd
    (Matrix.of fun (a : Fin S.j) (l : Fin (0 + N)) => eaEval S.X.c (eaD S.X.c l (S.h a)) z)]
  exact (hS z hz).2.1

/-- At a point `z` of an absolute `Good` stratum the equation family is a submersion: its
Fréchet derivative is surjective onto `ℝ^{S.j}`. -/
theorem eaFamily_surj_of_good {N : ℕ} (S : Stratum 0 N) (hS : S.Good) {z : Fin (0 + N) → ℝ}
    (hz : z ∈ S.X.set) :
    Function.Surjective (fderiv ℝ (fun w : Fin (0 + N) → ℝ => fun a : Fin S.j =>
      eaEval S.X.c (S.h a) w) z) := by
  have hfun : ⇑(fderiv ℝ (fun w : Fin (0 + N) → ℝ => fun a : Fin S.j =>
        eaEval S.X.c (S.h a) w) z) = ⇑(jac S z) := by
    funext v
    rw [fderiv_eaFamily_apply_jac, jac_apply]
  rw [hfun, ← LinearMap.range_eq_top, Submodule.eq_top_iff_finrank_eq, jacRankGood S hS hz,
    Module.finrank_fin_fun]

/-- **C1 of the E7 design (BV Prop. 9's Sard input).**  The projection to `ℝ^n` of the locus of
an absolute `Good` stratum on which the restricted projection rank is `≤ r` is a `NullDimLE r`
set: each of its `(r+1)`-coordinate projections is Lebesgue-null.

At each point `z₀` of the stratum the local Sard step is `rankLocusLocal` (the delegated local
statement, in the vocabulary of the equation family of `S.X`), with the surjectivity of the
equation family supplied by `eaFamily_surj_of_good` (the full-row-rank part of `Good`); the
countable cover of the locus by these local pieces is provided by `glueNull`, and
`image_coordMap` identifies the measured set with the coordinate projection used there. -/
theorem rankLocus_nullDimLE {n m : ℕ} (S : WilkiesDesign.E.Stratum 0 (n + m))
    (hS : S.Good) (r : ℕ) :
    Work.WilE7.MainDesign.NullDimLE
      (WilkiesDesign.E.projFirst n m ''
        (Work.WilE7.MainDesign.absPt '' {z ∈ S.X.set | Work.WilE7.MainDesign.projRank S z ≤ r})) r := by
  intro e
  have hA : (fun x : Fin n → ℝ => x ∘ e) ''
        (projFirst n m '' (absPt '' {z ∈ S.X.set | projRank S z ≤ r}))
      = coordMap n m (r + 1) e '' {z ∈ S.X.set | projRank S z ≤ r} :=
    image_coordMap n m (r + 1) e _
  rw [hA]
  refine Work.WilE9G.Sard.glueNull (coordMap n m (r + 1) e)
    {z ∈ S.X.set | projRank S z ≤ r} ?_
  rintro z₀ ⟨hz₀S, _⟩
  exact rankLocusLocal S hS r e hz₀S (eaFamily_surj_of_good S hS hz₀S)

end Work.WilE7.DimAPI
