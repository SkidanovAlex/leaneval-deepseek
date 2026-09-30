import Submission.Work.Homology.Basic
import Submission.Work.Homology.Point
import Submission.Work.Homology.Corollaries
import Submission.Work.Homology.Pairs
import Submission.Work.Cohomology.Chains
import Submission.Work.Cohomology.HomologyPairSequence
import Submission.Work.Cohomology.sphereHomologyTop
import Submission.Work.Cohomology.sphereHomologyZero
import Submission.Work.Cohomology.diskPairHomologyTop
import Submission.Work.Cohomology.diskPairHomologyZero
import Submission.Work.Cohomology.excision
import Submission.Work.Cohomology.localHomology

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The homology of spheres and of disc pairs

This file specialises the ported subdivision/excision chapter to the statements the rest of the
project needs:

* `Work.Homology.Sph n` — the unit `n`-sphere;
* `Work.Homology.singHomology_sphere_top`, `Work.Homology.isZero_singHomology_sphere` —
  `H_n(Sⁿ) ≅ ℤ` and `H_k(Sⁿ) = 0` for `k ≠ 0, n`;
* `Work.Homology.singHomology_sphere` — the combined statement;
* `Work.Homology.intHomology_sphere_four` — the `n = 4` case in the challenge's exact form;
* `Work.Homology.relHomology_disc_sphere` — `H_k(Dⁿ, Sⁿ⁻¹)`;
* `Work.Homology.relHomology_excision` — the excision isomorphism.
-/

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Homology

noncomputable section

/-- The unit `n`-sphere, as a topological space. -/
abbrev Sph (n : ℕ) : TopCat := TopCat.of (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)

/-- The unit `n`-sphere is path connected for `n ≥ 1`. -/
instance instPathConnectedSpaceSph (n : ℕ) [NeZero n] : PathConnectedSpace (Sph n) := by
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (NeZero.out (n := n))
  rw [← isPathConnected_iff_pathConnectedSpace]
  refine isPathConnected_sphere ?_ 0 (by norm_num)
  rw [show Module.rank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = ((n + 1 : ℕ) : Cardinal) from by
    have h2 := LinearEquiv.rank_eq (EuclideanSpace.equiv (Fin (n + 1)) ℝ).toLinearEquiv
    rw [h2]; exact rank_fin_fun (n + 1)]
  norm_num
  omega

/-- `H_n(Sⁿ; ℤ) ≅ ℤ` for `n ≥ 1`. -/
theorem singHomology_sphere_top (n : ℕ) (hn : 1 ≤ n) :
    Nonempty (singHomology ZMod n (Sph n) ≅ ZMod) :=
  Work.Cohomology.sphereHomologyTop n hn

/-- `H_k(Sⁿ; ℤ) = 0` for `k ≠ 0, n` (`n ≥ 1`). -/
theorem isZero_singHomology_sphere (n k : ℕ) (hn : 1 ≤ n) (h0 : k ≠ 0) (hk : k ≠ n) :
    IsZero (singHomology ZMod k (Sph n)) :=
  Work.Cohomology.sphereHomologyZero n k hn h0 hk

/-- **The homology of the `n`-sphere**: `ℤ` in degrees `0` and `n`, zero otherwise (`n ≥ 1`). -/
theorem singHomology_sphere (n k : ℕ) (hn : 1 ≤ n) :
    Nonempty (singHomology ZMod k (Sph n) ≅
      (if k = 0 ∨ k = n then ZMod else ModuleCat.of ℤ PUnit)) := by
  haveI : NeZero n := ⟨by omega⟩
  by_cases h : k = 0 ∨ k = n
  · rw [if_pos h]
    rcases h with h0 | hk
    · rw [h0]
      exact ⟨singHomologyZeroIsoOfPathConnected ZMod (Sph n)⟩
    · rw [hk]
      exact ⟨(Work.Cohomology.sphereHomologyTop n hn).some⟩
  · rw [if_neg h]
    push_neg at h
    exact ⟨(Work.Cohomology.sphereHomologyZero n k hn h.1 h.2).iso
      (isZero_moduleCat_of_subsingleton _)⟩

/-- **The `n = 4` case in the challenge's exact form.** -/
theorem intHomology_sphere_four (k : ℕ) :
    Nonempty (LeanEval.Topology.intHomology k
        (TopCat.of (Metric.sphere (0 : EuclideanSpace ℝ (Fin 5)) 1)) ≅
      (if k = 0 ∨ k = 4 then ModuleCat.of ℤ ℤ else ModuleCat.of ℤ PUnit)) := by
  rw [intHomology_eq]
  exact singHomology_sphere 4 k (by norm_num)

/-- **Relative homology of the disc pair** `(Dⁿ, Sⁿ⁻¹)`: `ℤ` in degree `n`, zero otherwise. -/
theorem relHomology_disc_sphere (n k : ℕ) (hn : 1 ≤ n) :
    Nonempty (relHomology ZMod k (Work.Cohomology.diskUnit n)
        (Work.Cohomology.sphereInUnit n) ≅
      (if k = n then ZMod else ModuleCat.of ℤ PUnit)) := by
  by_cases h : k = n
  · rw [h, if_pos rfl]
    exact Work.Cohomology.diskPairHomologyTop n hn
  · rw [if_neg h]
    exact ⟨(Work.Cohomology.diskPairHomologyZero n k hn h).iso
      (isZero_moduleCat_of_subsingleton _)⟩

/-- **Excision** (closure form): if `closure Z ⊆ interior A` then `H_n(X, A) ≅ H_n(X ∖ Z, A ∖ Z)`. -/
theorem relHomology_excision (X : TopCat) (A Z : Set X) (h : closure Z ⊆ interior A) (n : ℕ) :
    Nonempty (relHomology ZMod n X A ≅
      relHomology ZMod n (TopCat.of {x : X | x ∉ Z}) {x : {x : X | x ∉ Z} | (x : X) ∈ A}) :=
  Work.Cohomology.excision X A Z h n

end

end Work.Homology
