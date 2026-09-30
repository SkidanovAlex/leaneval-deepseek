/-
# `H_*(S¹ × T²; ℤ)` — the homology of the three-torus

This file computes the integral singular homology of the cusp cross-section `T³ = S¹ × T²` in the
ranks of `Work.HomologyIso.rankT = (1,3,3,1)`.

The input is the "Künneth with a circle" theorem `Work.PieceHomology.prod_circle`
(`H_{n+1}(X × S¹) ≅ H_{n+1}(X) ⊕ H_n(X)`, proved by Mayer–Vietoris along the two-arc cover of the
circle), applied step by step:

* `singHomology_circ` — `H_k(S¹) ≅ ℤ^{rankCirc k}` (`rankCirc = (1,1)`),
* `singHomology_torus2` — `H_k(T²) ≅ ℤ^{rankT2 k}` (`rankT2 = (1,2,1)`),
* `singHomology_torus3` — `H_k(T³) ≅ ℤ^{rankT k}` (`rankT = (1,3,3,1)`),

with the degree-zero cases from path-connectedness and the rank arithmetic from
`Work.PieceHomology.freeMod_rank_arith`.
-/
import Mathlib
import Submission.Work.PieceHomology.Basic
import Submission.Work.Homology.Basic
import Submission.Work.Homology.Pairs
import Submission.Work.Homology.Point
import Submission.Work.Homology.RelChainMap
import Submission.Work.Homology.Corollaries
import Submission.Work.Homology.SingHomologyHomeomorph
import Submission.Work.Homology.HomologyBiprod
import Submission.Work.Homology.SingHomologyClopen
import Submission.Work.Homology.ContractibleHomology
import Submission.Work.Homology.BallHomology
import Submission.Work.Homology.StdSimplexHomology
import Submission.Work.Homology.HomotopyEquivHomology
import Submission.Work.Homology.DeformationRetractHomology
import Submission.Work.Homology.SimplexShim
import Submission.Work.Cohomology.Chains
import Submission.Work.Cohomology.HomologyPairSequence
import Submission.Work.Homology.Spheres
import Submission.Work.Homology.MayerVietoris
import Submission.Work.PieceHomology.CircCover
import Submission.Work.PieceHomology.prod_circle
import Submission.Work.PieceHomology.freeMod_rank_arith

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.PieceHomology

open CategoryTheory CategoryTheory.Limits

noncomputable section

/-- `ℤ^{1} ≅ ℤ`, the free model of rank one. -/
def freeModOneIso : Work.HomologyMV.freeMod 1 ≅ Work.Homology.ZMod :=
  (LinearEquiv.funUnique (Fin 1) ℤ ℤ).toModuleIso

/-- The free model of rank zero is the trivial module. -/
def freeModZeroIso : Work.HomologyMV.freeMod 0 ≅ ModuleCat.of ℤ PUnit :=
  (Work.HomologyMV.isZero_freeMod_zero).iso (Work.Homology.isZero_moduleCat_of_subsingleton _)

/-- Homology is invariant under homeomorphism of the underlying types. -/
theorem singHomology_homeo {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (k : ℕ) :
    Nonempty (Work.Homology.singHomology Work.Homology.ZMod k (TopCat.of X)
      ≅ Work.Homology.singHomology Work.Homology.ZMod k (TopCat.of Y)) :=
  Work.Homology.SingHomologyHomeomorph Work.Homology.ZMod k
    (X := TopCat.of X) (Y := TopCat.of Y) e

/-- `H_k` of a point, in the free models of the ranks `rankPt`. -/
def singHomologyPointFreeMod (k : ℕ) :
    Work.Homology.singHomology Work.Homology.ZMod k (TopCat.of PUnit)
      ≅ Work.HomologyMV.freeMod (rankPt (k : ℤ)) := by
  rcases k with _ | j
  · simpa using (Work.Homology.singHomologyPoint Work.Homology.ZMod 0).trans freeModOneIso.symm
  · have h0 : ¬ ((j + 1 : ℕ) = 0) := by omega
    have hz : rankPt ((j : ℤ) + 1) = 0 := rankPt_eq_zero _ (by omega)
    simpa [if_neg h0, hz] using
      (Work.Homology.singHomologyPoint Work.Homology.ZMod (j + 1)).trans freeModZeroIso.symm

/-- **The homology of the circle**: `H_k(S¹) ≅ ℤ^{rankCirc k}`, `rankCirc = (1,1)`. -/
theorem singHomology_circ (k : ℕ) :
    Nonempty (Work.Homology.singHomology Work.Homology.ZMod k (TopCat.of Circ)
      ≅ Work.HomologyMV.freeMod (rankCirc (k : ℤ))) := by
  rcases k with _ | j
  · have h : rankCirc (((0 : ℕ)) : ℤ) = 1 := by simp
    exact ⟨(Work.Homology.singHomologyZeroIsoOfPathConnected Work.Homology.ZMod
      (TopCat.of Circ)).trans (freeModOneIso.symm.trans
        (Work.HomologyIso.freeModCast h))⟩
  · obtain ⟨e1⟩ := prod_circle (X := PUnit) j
    obtain ⟨e2⟩ := singHomology_homeo (Homeomorph.uniqueProd PUnit Circ).symm (j + 1)
    have e3 := singHomologyPointFreeMod (j + 1)
    have e4 := singHomologyPointFreeMod j
    obtain ⟨e5⟩ := freeMod_rank_arith.2.2.2.2.2.1
      (rankPt (((j + 1 : ℕ)) : ℤ)) (rankPt ((j : ℕ) : ℤ))
    have h1 : ((j + 1 : ℕ) : ℤ) = (j : ℤ) + 1 := by push_cast; ring
    have key : rankPt (((j + 1 : ℕ)) : ℤ) + rankPt ((j : ℕ) : ℤ)
        = rankCirc (((j + 1 : ℕ)) : ℤ) := by
      rw [h1]; exact (freeMod_rank_arith.1 j).symm
    exact ⟨e2.trans (e1.trans ((biprod.mapIso e3 e4).trans
      (e5.trans (Work.HomologyIso.freeModCast key))))⟩

/-- **The homology of the two-torus**: `H_k(T²) ≅ ℤ^{rankT2 k}`, `rankT2 = (1,2,1)`. -/
theorem singHomology_torus2 (k : ℕ) :
    Nonempty (Work.Homology.singHomology Work.Homology.ZMod k
        (TopCat.of (Fin 2 → Circ))
      ≅ Work.HomologyMV.freeMod (Work.HomologyIso.rankT2 (k : ℤ))) := by
  rcases k with _ | j
  · have h : Work.HomologyIso.rankT2 (((0 : ℕ)) : ℤ) = 1 := by simp
    exact ⟨(Work.Homology.singHomologyZeroIsoOfPathConnected Work.Homology.ZMod
      (TopCat.of (Fin 2 → Circ))).trans (freeModOneIso.symm.trans
        (Work.HomologyIso.freeModCast h))⟩
  · obtain ⟨h1⟩ := singHomology_homeo (Homeomorph.piFinTwo (fun _ : Fin 2 => Circ)) (j + 1)
    obtain ⟨h2⟩ := prod_circle (X := Circ) j
    obtain ⟨h3⟩ := singHomology_circ (j + 1)
    obtain ⟨h4⟩ := singHomology_circ j
    obtain ⟨h5⟩ := freeMod_rank_arith.2.2.2.2.2.1
      (rankCirc (((j + 1 : ℕ)) : ℤ)) (rankCirc ((j : ℕ) : ℤ))
    have h6 : ((j + 1 : ℕ) : ℤ) = (j : ℤ) + 1 := by push_cast; ring
    have key : rankCirc (((j + 1 : ℕ)) : ℤ) + rankCirc ((j : ℕ) : ℤ)
        = Work.HomologyIso.rankT2 (((j + 1 : ℕ)) : ℤ) := by
      rw [h6]; exact (freeMod_rank_arith.2.1 j).symm
    exact ⟨h1.trans (h2.trans ((biprod.mapIso h3 h4).trans
      (h5.trans (Work.HomologyIso.freeModCast key))))⟩

/-- **The homology of the three-torus**: `H_k(S¹ × T²) ≅ ℤ^{rankT k}`, `rankT = (1,3,3,1)`. -/
theorem singHomology_torus3 (k : ℕ) :
    Nonempty (Work.Homology.singHomology Work.Homology.ZMod k
        (TopCat.of (Circ × (Fin 2 → Circ)))
      ≅ Work.HomologyMV.freeMod (Work.HomologyIso.rankT (k : ℤ))) := by
  rcases k with _ | j
  · have h : Work.HomologyIso.rankT (((0 : ℕ)) : ℤ) = 1 := by simp
    exact ⟨(Work.Homology.singHomologyZeroIsoOfPathConnected Work.Homology.ZMod
      (TopCat.of (Circ × (Fin 2 → Circ)))).trans (freeModOneIso.symm.trans
        (Work.HomologyIso.freeModCast h))⟩
  · obtain ⟨h0⟩ := singHomology_homeo
      (Homeomorph.prodComm Circ (Fin 2 → Circ)) (j + 1)
    obtain ⟨h1⟩ := prod_circle (X := Fin 2 → Circ) j
    obtain ⟨h2⟩ := singHomology_torus2 (j + 1)
    obtain ⟨h3⟩ := singHomology_torus2 j
    obtain ⟨h4⟩ := freeMod_rank_arith.2.2.2.2.2.1
      (Work.HomologyIso.rankT2 (((j + 1 : ℕ)) : ℤ))
      (Work.HomologyIso.rankT2 ((j : ℕ) : ℤ))
    have h5 : ((j + 1 : ℕ) : ℤ) = (j : ℤ) + 1 := by push_cast; ring
    have key : Work.HomologyIso.rankT2 (((j + 1 : ℕ)) : ℤ)
          + Work.HomologyIso.rankT2 ((j : ℕ) : ℤ)
        = Work.HomologyIso.rankT (((j + 1 : ℕ)) : ℤ) := by
      rw [h5]; exact (freeMod_rank_arith.2.2.1 j).symm
    exact ⟨h0.trans (h1.trans ((biprod.mapIso h2 h3).trans
      (h4.trans (Work.HomologyIso.freeModCast key))))⟩

theorem intHomology_torus3 (k : ℕ) :
    Nonempty (LeanEval.Topology.intHomology k
      (TopCat.of (AddCircle (1 : ℝ) × (Fin 2 → AddCircle (1 : ℝ))))
      ≅ Work.HomologyMV.freeMod (Work.HomologyIso.rankT (k : ℤ))) := by
  obtain ⟨e⟩ := singHomology_torus3 k
  exact ⟨(eqToIso (Work.Homology.intHomology_eq k
    (TopCat.of (Circ × (Fin 2 → Circ))))).trans e⟩

end

end Work.PieceHomology
