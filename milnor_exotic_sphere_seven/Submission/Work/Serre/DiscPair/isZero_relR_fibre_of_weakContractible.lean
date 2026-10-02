import Mathlib
import Submission.Work.Serre.ratSerrePairComparison
import Submission.Work.RatHurewicz.Cofibre.piMap_cofibreCollapse_bijective
import Submission.Work.Serre.serreE0Range
import Submission.Work.Serre.Csr.Base
import Submission.Work.RatHurewicz.Cofibre.isIso_beta_of_contractible_subspace

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Serre.DiscPair

open CategoryTheory CategoryTheory.Limits

/-!
# The relative homology of a fibre over a weakly contractible base

Let `q : X → B` be a Serre fibration with `B` path connected and weakly contractible
(`πᵢ(B,b₀) = 0` for all `i`), and with all fibres path connected.  Then for **every** base point
`w : B` the relative rational homology `H_k(X, q⁻¹{w};ℚ)` vanishes for `1 ≤ k ≤ N + 1`.

The proof does not need the hypotheses on the rational homology of the fibre (`hvan`, `hgen`): a
weakly contractible base forces the base side of the Serre pair comparison to vanish.  Concretely:

* `Work.RatHurewicz.Cofibre.subsingleton_homotopyGroup_of_pathConnected` transfers the vanishing of
  the homotopy groups of `B` from `b₀` to the point `w` of the conclusion;
* `Work.Serre.ratSerrePairComparison` at the base point `w` (with `b = N + 2`, `f = 1`, so that the
  hypotheses on the rational homology of the fibre are vacuous) gives
  `H_i(X, q⁻¹{w}) ≅ H_i(B, {w})` for `i < N + 3`;
* `Work.Serre.serreE0Range` gives `H_k(B;ℚ) = 0` for `k ≥ 1` from the weak contractibility of `B`,
  and `isZero_relChainsR_point_rat` below turns this into the vanishing of the reduced homology
  `H_k(B, {w};ℚ)` — a rational form of the pair sequence computation for a point, which avoids the
  integral base-change lemma `Work.StemsB.homologyBaseChangeRat` (that one lives in a module of the
  `WangCoh` chain, whose import graph currently carries a cycle);
* the two are combined by `IsZero.of_iso`.
-/

/-- **The reduced rational homology of a point of a path connected space vanishes in positive
degrees.**  For `k ≠ 0`, `H_k(X, {b};ℚ) ≅ H_k(X;ℚ)`: the inclusion `{b} ↪ X` induces an
isomorphism `β_k : H_k(X;ℤ) ≅ H_k(X,{b};ℤ)` because `{b}` is contractible
(`Work.RatHurewicz.Cofibre.isIso_beta_of_contractible_subspace`), and base change to `ℚ`
(`Work.Serre.Csr.relChainsRHomologyIsoRat`) preserves isomorphisms and vanishing.

This is the rational-coefficient counterpart of `Work.Serre.DiscPair.isZero_relChainsR_point_zero`;
it is stated here (rather than imported from `Work.Serre.DiscPair.isZero_conePairRelCoh`, whose
import graph is currently cyclic) so that this file builds on acycle-free imports. -/
theorem isZero_relChainsR_point_rat {X : Type} [TopologicalSpace X] [PathConnectedSpace X]
    (b : X) (k : ℕ) (hk : k ≠ 0) (h : IsZero (Work.Serre.ratH (TopCat.of X) k)) :
    IsZero ((Work.StemsB.relChainsR ℚ (TopCat.of X) ({b} : Set X)).homology k) := by
  -- the integral absolute homology vanishes in degree `k`
  have hZ : IsZero (Work.StemsB.IntRatF.obj
      ((Work.Cohomology.singularChains ℤ (TopCat.of X)).homology k)) :=
    IsZero.of_iso h (Work.Serre.Csr.absHomologyIsoRat (TopCat.of X) k).some.symm
  -- the middle map of the integral pair sequence is an isomorphism
  haveI : IsIso (HomologicalComplex.homologyMap
      (cokernel.π (Work.Cohomology.inclChains (TopCat.of X) ({b} : Set X))) k) :=
    Work.RatHurewicz.Cofibre.isIso_beta_of_contractible_subspace
      (TopCat.of X) ({b} : Set X) k hk
  -- hence so is its base change, so the integral relative homology vanishes in degree `k`
  have h2 : IsZero (Work.StemsB.IntRatF.obj
      ((Work.Cohomology.relChains (TopCat.of X) ({b} : Set X)).homology k)) :=
    IsZero.of_iso hZ (Work.StemsB.IntRatF.mapIso (asIso (HomologicalComplex.homologyMap
      (cokernel.π (Work.Cohomology.inclChains (TopCat.of X) ({b} : Set X))) k))).symm
  -- and base change back to `ℚ`
  obtain ⟨eR⟩ := Work.Serre.Csr.relChainsRHomologyIsoRat (TopCat.of X) ({b} : Set X) k
  exact IsZero.of_iso h2 eR

theorem isZero_relR_fibre_of_weakContractible {B : Type} [TopologicalSpace B] {X : Type}
    [TopologicalSpace X] (q : C(X, B)) (b₀ : B) (r N : ℕ) (hr : 1 ≤ r) (hrN : r ≤ N)
    (hq : Work.StemsB.IsSerreFibration q) (hB : PathConnectedSpace B)
    (hBc : ∀ i : ℕ, Subsingleton (HomotopyGroup (Fin i) B b₀))
    (hX : PathConnectedSpace X)
    (hpc : ∀ b : B, PathConnectedSpace (Work.StemsB.fibre q b))
    (hvan : ∀ b : B, ∀ t : ℕ, 0 < t → t ≠ r → t ≤ N →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q b)) t))
    (hgen : ∀ b : B, Nonempty (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q b)) r
      ≅ ModuleCat.of ℚ ℚ))
    (w : B) (k : ℕ) (hk : 1 ≤ k) (hkN : k ≤ N + 1) :
    CategoryTheory.Limits.IsZero
      ((Work.StemsB.relChainsR ℚ (TopCat.of X) (q ⁻¹' ({w} : Set B))).homology k) := by
  classical
  -- (1) `B` is weakly contractible at *every* base point, by path connectedness.
  have hconn_w : ∀ i : ℕ, i < N + 2 → Subsingleton (HomotopyGroup (Fin i) B w) :=
    fun i hi =>
      Work.RatHurewicz.Cofibre.subsingleton_homotopyGroup_of_pathConnected b₀ hB (N + 1)
        (fun j _ => hBc j) i (by omega) w
  -- (2) The Serre pair comparison at the base point `w`, with `b = N + 2` and `f = 1` (so that
  -- the hypotheses on the rational homology of the fibre are vacuous).
  have hcmp := (Work.Serre.ratSerrePairComparison q hq w (N + 2) 1 (by omega) (by omega) hX hB
    hconn_w (hpc w) (fun j hj hj1 => by omega)).1
  -- (3) The base side vanishes in positive degrees.
  have hBk : IsZero (Work.Serre.ratH (TopCat.of B) k) :=
    Work.Serre.serreE0Range B b₀ k (fun i _ => hBc i) k hk (by omega)
  have hbase : IsZero ((Work.StemsB.relChainsR ℚ (TopCat.of B) ({w} : Set B)).homology k) :=
    isZero_relChainsR_point_rat w k (by omega) hBk
  -- (4) Transport the vanishing of the base side to the total space.
  obtain ⟨e⟩ := hcmp k (by omega)
  exact IsZero.of_iso hbase e

end Work.Serre.DiscPair
