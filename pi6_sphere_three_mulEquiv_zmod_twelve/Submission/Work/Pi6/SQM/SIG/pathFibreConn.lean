import Mathlib
import Submission.Work.StemsB.Fibrations
import Submission.Work.StemsB.homotopyGroup_loopSpace
import Submission.Work.StemsB.pi_homeo_invariance
import Submission.Work.Serre.subsingleton_pi0_loopSpace_of_pi1
import Submission.Work.Serre.ZeroCase.Bridge
import Submission.Work.Cohomology.isZero_homology_of_homotopyEquiv
import Submission.Work.RatHurewicz.ConnectivityBridge
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option linter.style.haveILetI false

open scoped Topology

namespace Work.Pi6.SQM.SIG

noncomputable section

/-! ## Two elementary helpers

* `π₀` of a path connected space is trivial at every base point;
* the fibre of the path–loop fibration inherits path connectedness from its loop space. -/

/-- **`π₀` of a path connected space is trivial** (at any base point).  The `0`-cube model of the
homotopy group is `ZerothHomotopy X` (`HomotopyGroup.pi0EquivZerothHomotopy`), which is a
subsingleton as soon as `X` is path connected. -/
theorem subsingleton_homotopyGroup_zero_of_pathConnectedSpace {X : Type} [TopologicalSpace X]
    (x : X) [PathConnectedSpace X] : Subsingleton (HomotopyGroup (Fin 0) X x) :=
  ⟨fun _ _ => (HomotopyGroup.pi0EquivZerothHomotopy (X := X) (x := x)).injective
      (Subsingleton.elim _ _)⟩

/-- The fibre of the path–loop fibration `evalOne : PK → K` over `k₀` is path connected whenever
the loop space `ΩK = Path k₀ k₀` is (they are homeomorphic). -/
theorem pathConnectedSpace_fibre_evalOne {K : Type} [TopologicalSpace K] (k₀ : K)
    [PathConnectedSpace (Path k₀ k₀)] :
    PathConnectedSpace (Work.StemsB.fibre (Work.StemsB.evalOne K k₀) k₀) :=
  (Work.StemsB.fibreEvalOneHomeo K k₀).symm.pathConnectedSpace

/-- **The loop-space connectivity shift.**  If `π_i(K) = 0` for all `i < f + 1`, then
`π_i(ΩK) = 0` for all `i < f`: the currying isomorphism `Work.StemsB.homotopyGroup_loopSpace`
shifts `π_{k+2}(K)` to `π_{k+1}(ΩK)`, and `π₀(ΩK) = 0` because `π₁(K) = 0`
(`Work.Serre.subsingleton_pi0_loopSpace_of_pi1`). -/
theorem subsingleton_homotopyGroup_loopSpace_of_lt {K : Type} [TopologicalSpace K] (k₀ : K)
    (f : ℕ) (hconn : ∀ i : ℕ, i < f + 1 → Subsingleton (HomotopyGroup (Fin i) K k₀)) :
    ∀ i : ℕ, i < f → Subsingleton (HomotopyGroup (Fin i) (Path k₀ k₀) (Path.refl k₀)) := by
  intro i hi
  rcases i with _ | k
  · exact Work.Serre.subsingleton_pi0_loopSpace_of_pi1 k₀ (hconn 1 (by omega))
  · obtain ⟨e⟩ := Work.StemsB.homotopyGroup_loopSpace k k₀
    haveI : Subsingleton (HomotopyGroup (Fin (k + 2)) K k₀) := hconn (k + 2) (by omega)
    exact e.symm.injective.subsingleton

/-- **The fibre of the path–loop fibration `evalOne : PK → K` over `k₀` is `(b-2)`-connected**
when `K` is `(b-1)`-connected (`b ≥ 2`), based at the constant loop: `π₀` of the fibre is trivial
and `H_j(fibre; ℤ) = 0` for `0 < j < b - 1`.

Route: the fibre is homeomorphic to `ΩK = Path k₀ k₀` (`Work.StemsB.fibreEvalOneHomeo`), whose
homotopy groups are those of `K` shifted by one (`Work.StemsB.homotopyGroup_loopSpace`,
`Work.StemsB.pi_homeo_invariance`), with `π₀` of the loop space trivial because `π₁K = 0`
(`Work.Serre.subsingleton_pi0_loopSpace_of_pi1`); Hurewicz:
`Work.Serre.isZero_singularChains_homology_of_pi_subsingleton`. -/
theorem pathFibreConn (K : Type) [TopologicalSpace K] (k₀ : K) (b : ℕ) (hb : 2 ≤ b)
    (hconn : ∀ i : ℕ, i < b → Subsingleton (HomotopyGroup (Fin i) K k₀)) :
    Subsingleton (HomotopyGroup (Fin 0)
        (Work.StemsB.fibre (Work.StemsB.evalOne K k₀) k₀)
        ((Work.StemsB.fibreEvalOneHomeo K k₀).symm (Path.refl k₀))) ∧
      (∀ j : ℕ, 0 < j → j < b - 1 →
        CategoryTheory.Limits.IsZero ((Work.Cohomology.singularChains ℤ
          (TopCat.of (Work.StemsB.fibre (Work.StemsB.evalOne K k₀) k₀))).homology j)) := by
  -- `π₁K = 0`, so the loop space is path connected (`π₀(ΩK) = 0`), and so is the fibre
  have hpi1 : Subsingleton (HomotopyGroup (Fin 1) K k₀) := hconn 1 (by omega)
  haveI hpcL : PathConnectedSpace (Path k₀ k₀) :=
    Work.RatHurewicz.pathConnectedSpace_of_subsingleton_pi_zero (Path.refl k₀)
      (Work.Serre.subsingleton_pi0_loopSpace_of_pi1 k₀ hpi1)
  haveI hpcF : PathConnectedSpace (Work.StemsB.fibre (Work.StemsB.evalOne K k₀) k₀) :=
    pathConnectedSpace_fibre_evalOne k₀
  refine ⟨subsingleton_homotopyGroup_zero_of_pathConnectedSpace _, fun j hj hjlt => ?_⟩
  -- the loop space has vanishing homotopy groups below `b - 1`, hence vanishing homology there
  have hloop : ∀ i : ℕ, i < b - 1 →
      Subsingleton (HomotopyGroup (Fin i) (Path k₀ k₀) (Path.refl k₀)) :=
    subsingleton_homotopyGroup_loopSpace_of_lt k₀ (b - 1)
      (fun i hi => hconn i (by omega))
  have hZ : CategoryTheory.Limits.IsZero ((Work.Cohomology.singularChains ℤ
      (TopCat.of (Path k₀ k₀))).homology j) :=
    Work.Serre.isZero_singularChains_homology_of_pi_subsingleton (Path.refl k₀) (b - 1)
      hloop j hj hjlt
  -- and homology is a homeomorphism invariant, so the fibre inherits the vanishing
  exact Work.Cohomology.isZero_homology_of_homotopyEquiv
    (X := TopCat.of (Work.StemsB.fibre (Work.StemsB.evalOne K k₀) k₀))
    (Y := TopCat.of (Path k₀ k₀))
    (Work.StemsB.fibreEvalOneHomeo K k₀).toHomotopyEquiv j hZ

end

end Work.Pi6.SQM.SIG
