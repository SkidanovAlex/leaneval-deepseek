import Mathlib
import Submission.Work.Stems.RankOneClauses
import Submission.Work.Stems.rankOne_hurewicz_torsion
import Submission.Work.RatHurewicz.fibreRangeVanishing

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The rank-one Hurewicz input: an infinite-order class and the loop space generator

For a `(k-1)`-connected space `X` (`k ≥ 2`) with `H_k(X;ℚ) ≅ ℚ` we prove the two facts that the
rank-one Eilenberg--MacLane computation consumes in its even step
(`Work.Stems.EvenClauseR`, `Submission/Work/Stems/rankOne_evenStep.lean`):

* `π_k(X,x₀)` contains a class of **infinite order** — the contradiction of the torsion criterion
  `Work.Stems.rankOne_hurewicz_torsion` with `H_k(X;ℚ) ≅ ℚ ≠ 0`;
* **`H_{k-1}(ΩX;ℚ) ≅ ℚ`** for the loop space `ΩX = Path x₀ x₀` — the transgression isomorphism
  `H_{k-1}(ΩX;ℚ) ≅ H_k(X;ℚ)` of the path--loop fibration `ΩX → PX → X`
  (`Work.Stems.ratH_loopSpace_iso` below).

The second statement is what lets the odd clause `Work.Stems.OddClauseR (k-1)` be applied to `ΩX`
in the even step: `ΩX` inherits the `π`-vanishing of `X` one degree down, and `ratH_loopSpace_iso`
supplies the missing rank-one generator in degree `k-1`.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology

set_option linter.style.haveILetI false

namespace Work.Stems

noncomputable section

/-- **The transgression isomorphism for the path--loop fibration, in rational homology.**
For a `(k-1)`-connected space `X` (`k ≥ 2`) the loop space `ΩX = Path x₀ x₀` has
`H_{k-1}(ΩX;ℚ) ≅ H_k(X;ℚ)`.

The proof is the classical one: the path--loop fibration `ΩX → PX → X` has contractible total space
`PX`, so the connecting map of the pair `(PX, ΩX)` gives `H_{k-1}(ΩX;ℚ) ≅ H_k(PX, ΩX;ℚ)`; the
Serre exact sequence in the stable range (`Work.RatHurewicz.ratPairComparison_proof`, the proved
rational pair comparison, applied with base connectivity `b = k` and fibre parameter `f = 1`)
identifies `H_k(PX, ΩX;ℚ) ≅ H_k(X, {x₀};ℚ)`; and `H_k(X, {x₀};ℚ) ≅ H_k(X;ℚ)`, the one-point space
having no positive-degree rational homology.  Finally the strict fibre of the endpoint evaluation
is the loop space (`Work.StemsB.fibreEvalOneHomeo`). -/
theorem ratH_loopSpace_iso {X : Type} [TopologicalSpace X] (x₀ : X) (k : ℕ) (hk : 2 ≤ k)
    (hconn : ∀ i : ℕ, i < k → Subsingleton (HomotopyGroup (Fin i) X x₀)) :
    Nonempty (Work.Serre.ratH (TopCat.of (Path x₀ x₀)) (k - 1) ≅
      Work.Serre.ratH (TopCat.of X) k) := by
  -- the total space `PX` is contractible, hence rationally acyclic
  haveI hcontrPX : ContractibleSpace (Work.StemsB.PathSpace X x₀) :=
    Work.StemsB.contractible_pathSpace X x₀
  haveI hpcPX : PathConnectedSpace (Work.StemsB.PathSpace X x₀) := inferInstance
  have hacPX : Work.Serre.RatAcyclic (Work.StemsB.PathSpace X x₀) :=
    Work.Serre.ratAcyclic_of_contractible (Work.StemsB.PathSpace X x₀)
  -- the base is path connected and the fibre of `evalOne` is path connected (`π₁(X) = 0`)
  haveI hpcX : PathConnectedSpace X :=
    Work.RatHurewicz.pathConnectedSpace_of_subsingleton_pi_zero x₀ (hconn 0 (by omega))
  have hfib0 : PathConnectedSpace (Work.StemsB.fibre (Work.StemsB.evalOne X x₀) x₀) :=
    Work.Serre.pathConnectedSpace_fibre_of_isSerreFibration (Work.StemsB.evalOne X x₀)
      (Work.StemsB.isSerreFibration_evalOne X x₀) x₀ hpcPX hpcX (hconn 1 (by omega))
  -- (1) `H_{k-1}(ΩX;ℚ) ≅ H_{k-1}(fibre;ℚ)`: the strict fibre of the endpoint evaluation is `ΩX`
  have h1 : Nonempty
      (Work.Serre.ratH
          (TopCat.of (Work.StemsB.fibre (Work.StemsB.evalOne X x₀) x₀)) (k - 1) ≅
        Work.Serre.ratH (TopCat.of (Path x₀ x₀)) (k - 1)) := by
    haveI : IsIso (Work.Serre.ratHomologyMap
        ((Work.StemsB.fibreEvalOneHomeo X x₀).toHomotopyEquiv).toFun (k - 1)) :=
      Work.Serre.IsRatHomologyIso.of_homotopyEquiv
        (Work.StemsB.fibreEvalOneHomeo X x₀).toHomotopyEquiv (k - 1)
    exact ⟨asIso (Work.Serre.ratHomologyMap
      ((Work.StemsB.fibreEvalOneHomeo X x₀).toHomotopyEquiv).toFun (k - 1))⟩
  -- (2) the pair `(PX, ΩX)`: `H_k(PX, ΩX;ℚ) ≅ H_{k-1}(ΩX;ℚ)` (`PX` acyclic in degrees `k-1`, `k`)
  have h2 : Nonempty
      (Work.RatHurewicz.relHRat (TopCat.of (Work.StemsB.PathSpace X x₀))
          ((Work.StemsB.evalOne X x₀) ⁻¹' {x₀}) k ≅
        Work.Serre.ratH
          (TopCat.of (Work.StemsB.fibre (Work.StemsB.evalOne X x₀) x₀)) (k - 1)) :=
    Work.RatHurewicz.nonempty_iso_of_eq
      (congrArg (fun n => Work.RatHurewicz.relHRat (TopCat.of (Work.StemsB.PathSpace X x₀))
        ((Work.StemsB.evalOne X x₀) ⁻¹' {x₀}) n) (Nat.sub_add_cancel (by omega : 1 ≤ k)))
      rfl
      (Work.RatHurewicz.nonempty_iso_relChainsRδ_of_isZero
        (TopCat.of (Work.StemsB.PathSpace X x₀)) ((Work.StemsB.evalOne X x₀) ⁻¹' {x₀}) (k - 1)
        (by
          rw [Nat.sub_add_cancel (by omega : 1 ≤ k)]
          exact hacPX.isZero_ratH (by omega))
        (hacPX.isZero_ratH (by omega)))
  -- (3) the Serre exact sequence (`b = k`, `f = 1`): `H_k(PX, ΩX;ℚ) ≅ H_k(X, {x₀};ℚ)`
  have h3 : Nonempty
      (Work.RatHurewicz.relHRat (TopCat.of (Work.StemsB.PathSpace X x₀))
          ((Work.StemsB.evalOne X x₀) ⁻¹' {x₀}) k ≅
        Work.RatHurewicz.relHRat (TopCat.of X) ({x₀} : Set X) k) :=
    (Work.RatHurewicz.ratPairComparison_proof (Work.StemsB.evalOne X x₀)
      (Work.StemsB.isSerreFibration_evalOne X x₀) x₀ k 1 hk le_rfl hpcPX hpcX hconn hfib0
      (fun j hj hj1 => by omega)).1 k (by omega)
  -- (4) `H_k(X, {x₀};ℚ) ≅ H_k(X;ℚ)`, the one-point space being acyclic in positive degrees
  have h4 : Nonempty
      (Work.Serre.ratH (TopCat.of X) k ≅
        Work.RatHurewicz.relHRat (TopCat.of X) ({x₀} : Set X) k) :=
    Work.RatHurewicz.nonempty_iso_of_eq
      (congrArg (fun n => Work.Serre.ratH (TopCat.of X) n) (Nat.sub_add_cancel (by omega : 1 ≤ k)))
      (congrArg (fun n => Work.RatHurewicz.relHRat (TopCat.of X) ({x₀} : Set X) n)
        (Nat.sub_add_cancel (by omega : 1 ≤ k)))
      (Work.RatHurewicz.nonempty_iso_cokernelπ_of_isZero (TopCat.of X) ({x₀} : Set X) (k - 1)
        (by
          rw [Nat.sub_add_cancel (by omega : 1 ≤ k)]
          exact Work.RatHurewicz.isZero_ratH_singleton x₀ (by omega))
        (Work.RatHurewicz.isZero_ratH_singleton x₀ (by omega)))
  exact ⟨h1.some.symm ≪≫ h2.some.symm ≪≫ h3.some ≪≫ h4.some.symm⟩

theorem rankOne_hurewicz_rank {k : ℕ} (hk : 2 ≤ k) [Nonempty (Fin k)] {X : Type} [TopologicalSpace X] (x₀ : X)
    (hconn : ∀ i : ℕ, i < k → Subsingleton (HomotopyGroup (Fin i) X x₀))
    (hH : Nonempty (Work.Serre.ratH (TopCat.of X) k ≅ ModuleCat.of ℚ ℚ)) :
    (∃ x : HomotopyGroup (Fin k) X x₀, ∀ m : ℕ, 0 < m → x ^ m ≠ 1) ∧
    Nonempty (Work.Serre.ratH (TopCat.of (Path x₀ x₀)) (k - 1) ≅ ModuleCat.of ℚ ℚ) := by
  constructor
  · -- an element of infinite order: otherwise `H_k(X;ℚ) = 0`, contradicting `H_k(X;ℚ) ≅ ℚ`
    by_contra h
    have htors : ∀ α : HomotopyGroup (Fin k) X x₀, ∃ m : ℕ, 0 < m ∧ α ^ m = 1 := by
      intro α
      by_contra hc
      exact h ⟨α, fun m hm => by
        by_contra hne
        exact hc ⟨m, hm, hne⟩⟩
    have hz : CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of X) k) :=
      Work.Stems.rankOne_hurewicz_torsion hk x₀ hconn htors
    obtain ⟨e⟩ := hH
    have hzQ : CategoryTheory.Limits.IsZero (ModuleCat.of ℚ ℚ) :=
      CategoryTheory.Limits.IsZero.of_iso hz e.symm
    haveI : Subsingleton ℚ := ModuleCat.isZero_iff_subsingleton.mp hzQ
    exact one_ne_zero (Subsingleton.elim (1 : ℚ) 0)
  · -- the loop space generator: the transgression isomorphism, then `H_k(X;ℚ) ≅ ℚ`
    obtain ⟨e⟩ := ratH_loopSpace_iso x₀ k hk hconn
    exact ⟨e ≪≫ hH.some⟩

end

end Work.Stems
