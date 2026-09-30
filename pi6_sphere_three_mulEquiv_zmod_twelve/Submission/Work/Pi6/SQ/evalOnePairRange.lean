import Mathlib
import Submission.Work.StemsB.serreStableExactTwo
import Submission.Work.StemsB.homotopyGroup_loopSpace
import Submission.Work.StemsB.pi_homeo_invariance
import Submission.Work.StemsB.isSerreFibration_evalOne
import Submission.Work.Serre.ZeroCase.Bridge
import Submission.Work.Serre.pathConnectedSpace_fibre_of_isSerreFibration
import Submission.Work.Pi6.SQM.SIG.pathFibreConn
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The Serre pair comparison for the path–loop fibration, in the range `2b - 1`

`Work.StemsB.serrePairComparisonTwo` gives, for a Serre fibration `p : E → B` over a **simply
connected** base `B` (`2 ≤ b`), with `B` `(b-1)`-connected and fibre `(f-1)`-connected, that the map
of pairs `(E, p⁻¹b₀) → (B, {b₀})` is an isomorphism on integral homology in degrees `< b + f` and an
epimorphism in degree `b + f`.

This file instantiates it for the **path–loop fibration** `evalOne K k₀ : PK → K` with
`f = b - 1`: the fibre is the loop space `ΩK = Path k₀ k₀`, whose homotopy groups are those of `K`
shifted by one, so `K` `(b-1)`-connected makes `ΩK` `(b-2)`-connected
(`Work.Pi6.SQM.SIG.pathFibreConn`).  Hence

* `H_i(PK, ΩK; ℤ) → H_i(K, {k₀}; ℤ)` is an isomorphism for `i < b + (b-1) = 2b-1`, and
* surjective in degree `b + (b-1)`.

This is the integral input of `Work.Pi6.SQ.sigmaRange`.
-/

set_option linter.style.haveILetI false

open scoped Topology unitInterval

namespace Work.Pi6.SQ

theorem evalOnePairRange (K : Type) [TopologicalSpace K] (k₀ : K) (b : ℕ) (hb : 2 ≤ b)
    (hconn : ∀ i : ℕ, i < b → Subsingleton (HomotopyGroup (Fin i) K k₀)) :
    (∀ i : ℕ, i < b + (b - 1) → CategoryTheory.IsIso (HomologicalComplex.homologyMap
        (Work.StemsB.relPairMap (Work.StemsB.evalOne K k₀) k₀) i)) ∧
    Function.Surjective (HomologicalComplex.homologyMap
        (Work.StemsB.relPairMap (Work.StemsB.evalOne K k₀) k₀) (b + (b - 1))).hom := by
  classical
  -- the path–loop fibration is a Hurewicz fibration, hence a Serre fibration
  have hserre : Work.StemsB.IsSerreFibration (Work.StemsB.evalOne K k₀) :=
    Work.StemsB.IsHurewiczFibration.isSerreFibration
      (Work.StemsB.isHurewiczFibration_evalOne K k₀)
  -- the constant path at `k₀`, as a point of the path space, lies over `k₀`
  let e₀ : Work.StemsB.PathSpace K k₀ := ⟨ContinuousMap.const I k₀, rfl⟩
  have he₀ : Work.StemsB.evalOne K k₀ e₀ = k₀ := rfl
  -- `π₁(K) = 0` makes the loop space `ΩK` path connected, hence so is the fibre
  haveI hpc : PathConnectedSpace (Work.StemsB.fibre (Work.StemsB.evalOne K k₀) k₀) := by
    haveI : PathConnectedSpace (Path k₀ k₀) :=
      Work.RatHurewicz.pathConnectedSpace_of_subsingleton_pi_zero (Path.refl k₀)
        (Work.Serre.subsingleton_pi0_loopSpace_of_pi1 k₀ (hconn 1 (by omega)))
    exact Work.Pi6.SQM.SIG.pathConnectedSpace_fibre_evalOne k₀
  -- the two connectivity inputs of the comparison, with `f = b - 1`
  let f₀ : Work.StemsB.fibre (Work.StemsB.evalOne K k₀) k₀ := ⟨e₀, he₀⟩
  have hfib0 : Subsingleton (HomotopyGroup (Fin 0)
      (Work.StemsB.fibre (Work.StemsB.evalOne K k₀) k₀) f₀) :=
    Work.Pi6.SQM.SIG.subsingleton_homotopyGroup_zero_of_pathConnectedSpace
      (X := Work.StemsB.fibre (Work.StemsB.evalOne K k₀) k₀) f₀
  have hfibH : ∀ j : ℕ, 0 < j → j < b - 1 → CategoryTheory.Limits.IsZero
      ((Work.Cohomology.singularChains ℤ
        (TopCat.of (Work.StemsB.fibre (Work.StemsB.evalOne K k₀) k₀))).homology j) :=
    (Work.Pi6.SQM.SIG.pathFibreConn K k₀ b hb hconn).2
  exact Work.StemsB.serrePairComparisonTwo (Work.StemsB.evalOne K k₀) hserre k₀ e₀ he₀
    b (b - 1) hb hconn hfib0 hfibH

end Work.Pi6.SQ
