import Mathlib
import Submission.Work.Serre.ThomCylDefs
import Submission.Work.Serre.CWModelThomAux
import Submission.Work.Serre.DiscPair.cellStepPairKernel
import Submission.Work.Serre.DiscPair.cellStepVanishing
import Submission.Work.Serre.DiscPair.centreConePair
import Submission.Work.Serre.DiscPair.centreConePairZero
import Submission.Work.Serre.DiscPair.cylPairCofibre
import Submission.Work.Serre.DiscPair.lesSplitPair
import Submission.Work.Serre.DiscPair.relPairFiveRat
import Submission.Work.Serre.TripleCohDefs
import Submission.Work.Serre.cellStepAssembly
import Submission.Work.RatHurewicz.cellStepShell

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Serre



/-- **The vacuous case of the cellular step**: if `N < r` there is no degree in the range, so any
class (here `0`) witnesses the conclusion. -/
theorem thomCylCellStepAlt_of_lt (r N : ℕ) (h : N < r)
    {Γ : Type} [TopologicalSpace Γ] {X : Type} [TopologicalSpace X] (q : C(X, Γ)) :
    Work.Serre.ThomCylAt r N q := by
  refine ⟨0, fun m hm => ?_⟩
  exfalso
  omega

/-- **The cellular step of the CW-model Thom case (independent second proof).**

This is a deliberate second proof of the single open step `Work.Serre.thomCylCellStep` in
`Submission/Work/Serre/cwModelThomCase.lean`, with the same statement (do NOT import that module:
its `thomCylCellStep` is still unproved and would pollute `#print axioms`).  The whole rest of the
project's E3(b) node is already assembled on top of that one statement, so proving this one
statement here finishes the node through `Submission/Work/Serre/eulerFibreRange.lean`.

Content: attaching cells of dimension `D ≥ 2` to a path connected base `Γ` (maps `f` out of
`S^{D-2}`), a Serre fibration `q` over the attachment whose fibres are path connected and have the
rational homology of `S^r` through degree `N` (`H^t(fibre) = 0` for `0 < t ≤ N`, `t ≠ r`, and
`H^r(fibre) ≅ ℚ`), and the conclusion known for the restriction to the preimage of the old part,
imply the conclusion for `q`.

### The earlier reduction plan (kept for the record)

Write `n = D-2`, `Γ' = attachCells n Γ ι f`, `S = Set.range (attachIncl n Γ ι f)`,
`M = cyl q`, `A = Set.range (cylIncl q)`,
`N = (cylRetract q) ⁻¹' S ∪ A` (so that `A ⊆ N ⊆ M` is a triple).

* **Vacuous case.**  If `N < r` there is no `m` with `m + r + 1 ≤ N + 1`, so any class
  (e.g. `0`) works: `thomCylCellStepAlt_of_lt` below.  Hence we may assume `r ≤ N`.

* **The vanishing of the new-cell groups** (`Work.Serre.discPairCellVanishing`, delegated this
  session): for `j ≤ N+1`, `j ≠ D+r+1`, `H^j(M,N) = 0`.  This is the cohomological cell step
  `Work.Serre.DiscPair.discCellStepCoh` (`H^m(M,N) ≅ ∏_i H^{m-D}` of the disc pair over the
  cell centre) combined with the per-cell concentration of the fibre pair (the fibre at a centre
  is a rational `S^r` through degree `N`, `hvan` + `hpc`), and with the vanishing below the cell
  dimension (`cellStepVanishing`).

* **The vanishing below the cell dimension for the base pair**
  (`Work.Serre.attachRelCohVanishing`, PROVED this session): `H^m(Γ',S) = 0` for `m ≤ D-1`.

* **The extension of the old class.**  `IH` gives a class `U₀ ∈ H^{r+1}(N,A)` with the cup
  isomorphism over the old part (transported along the pair identification
  `cylPreimageHomeo`/`cylPreimageRelChainsIso` and `Work.Serre.cylRestrictHomeo`).
  Because `H^{r+1}(M,N) = 0` and `H^{r+2}(M,N) = 0`, `U₀` has a *unique* preimage
  `U ∈ H^{r+1}(M,A)` (the long exact sequence of the triple `A ⊆ N ⊆ M`); the transfer to
  cohomology is `Work.Serre.DiscPair.isIso_triple_f_of_isZero` (dualised).

* **The ladder.**  Let `n₀ = r+1`.  The base pair `(Γ',S)` and the triple `A ⊆ N ⊆ M` give two
  long exact sequences of `ℚ`-modules, and the vertical maps
  `TM k : H^k(Γ',S) ⟶ H^{k+n₀}(M,N)`,
  `TP k : H^k(Γ') ⟶ H^{k+n₀}(M,A)`  (the target: `x ↦ retract^*(x) ⌣ U`),
  `TQ k : H^k(S) ⟶ H^{k+n₀}(N,A)`  (the `IH` isomorphism, transported)
  form a ladder.  The three squares are
  (i) `i ≫ TP = TM ≫ i'` (the restriction to `N` of the cup map with `U` — true by construction of
  `U` as the extension of `U₀` together with the naturality of the mixed cup product under the
  map of pairs `(N,A) → (M,A)`),
  (ii) `j ≫ TQ = TP ≫ j'` (naturality of the mixed cup product — a general statement),
  (iii) `δ ≫ TM = TQ ≫ ∂` (the Leibniz / transgression compatibility of the cell comparison with
  the connecting maps — this is the classical "the cross product with the fibre fundamental class
  commutes with the connecting maps").
  `Work.Serre.boundedFiveLemmaLES` (delegated this session) then gives
  `IsIso (TP (k+1))` for `k+1 ≤ N-r`, i.e. the conclusion for all `m ≥ 1`, from `TM`, `TQ`
  isomorphisms in the range `k ≤ N-r+1`; degree `m = 0` is `H^0(Γ') ≅ ℚ ≅ H^{n₀}(M,A)` and is
  handled separately.

* **The remaining gap** is the cell comparison `TM`: it is an isomorphism in every degree `≠ D`
  (both sides vanish, by the two vanishing statements above) and in degree `D` it is the
  comparison `H^D(Γ',S) → H^{D+r+1}(M,N)` between the two "cell groups" — the per-cell
  identification of the disc class with the fundamental class of the fibre, transported along the
  fibre-homotopy triviality of the disc-pair bundle over each cell (`Work.StemsB.FibrewiseTrivial`,
  `fibrewiseTrivial_of_contraction`) and computed by the *proved* local models
  `Work.Serre.modelThomRatPairQ`, `Work.StemsB.modelThomRatAll`, `Work.Serre.cubePairRelCohomology`
  / `Work.Serre.relCoh_cube_prod_concentrated`.  In the range `k ≤ N-r+1` this is exactly the
  classical "cross product with the fibre fundamental class is an isomorphism on the new cells".

### Proof (final, this session)

The statement is proved as `Work.RatHurewicz.thomCylCellStepAlt_free`
(`Submission/Work/RatHurewicz/cellStepShell.lean`), i.e. by the *shell / orthant-cover* route:
`Work.RatHurewicz.sphereThom_of_nonzeroClass` (the sphere case from a non-zero class),
`Work.RatHurewicz.cellShellThom_of_nonzeroClass`, `Work.Serre.cellStepU_ne_zero` (the extension
class `Work.Serre.cellStepU` is non-zero) and `Work.Serre.thomCylCellStep_of_shellsBall`, giving
`Work.RatHurewicz.CellStepAt D` for every `D ≥ 2` and hence the statement.  This route is
independent of `Work.Serre.thomCylCellStep` of `cwModelThomCase.lean` (which is still unproved)
and is axiom-clean, so the import of `Submission.Work.RatHurewicz.cellStepShell` below does *not*
pollute `#print axioms`.  The reduction plan recorded above (the ladder between the pair `(Γ',S)`
and the triple `A ⊆ N ⊆ M`, and the three critical facts `(F1)`, `(F2)`, `(F3)` for the cup map
`TP`) was the route taken in earlier sessions; it is superseded by the proof below and is kept only
for the record (its bookkeeping, `Work.Serre.cellStepAssembly`, is imported above).

**Dependency note.**  `RatHurewicz.cellStepShell` reaches this module indirectly through
`Work.Serre.SphereAssembly → Work.Serre.DiscPair.existsNonzeroRelCohTower →
Work.Serre.DiscPair.thomCylAt_of_contractible → Work.Serre.relCoh_concentrated_of_ratAcyclic`,
which used to import `Work.Serre.serreE3b` (and hence `thomIsoCylFibreRange`, which imports *this*
module) — a cycle.  That import was redundant (the two lemmas it used,
`isZero_coh_of_ratAcyclic` and `isZero_ratCoh_of_isZero_ratH`, are declared upstream in
`Work.Serre.EulerFibreRoot`), and it has been redirected there, which is what allows this module to
import the proof.

-/
theorem thomCylCellStepAlt (r N : ℕ) (hr : 1 ≤ r) (D : ℕ) (hD : 2 ≤ D)
    {Γ : Type} [TopologicalSpace Γ] (hΓ : PathConnectedSpace Γ) (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere (D - 2), Γ))
    {X : Type} [TopologicalSpace X] (q : C(X, Work.RatHurewicz.attachCells (D - 2) Γ ι f))
    (hq : Work.StemsB.IsSerreFibration q)
    (hvan : ∀ γ : Work.RatHurewicz.attachCells (D - 2) Γ ι f, ∀ t : ℕ, 0 < t → t ≠ r → t ≤ N →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q γ)) t))
    (hgen : ∀ γ : Work.RatHurewicz.attachCells (D - 2) Γ ι f,
      Nonempty (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q γ)) r ≅ ModuleCat.of ℚ ℚ))
    (hpc : ∀ γ : Work.RatHurewicz.attachCells (D - 2) Γ ι f,
      PathConnectedSpace (Work.StemsB.fibre q γ))
    (IH : Work.Serre.ThomCylAt r N (Work.Serre.restrictFibre q
      (Set.range (Work.RatHurewicz.attachIncl (D - 2) Γ ι f)))) :
    Work.Serre.ThomCylAt r N q := by
  exact Work.RatHurewicz.thomCylCellStepAlt_free r N hr D hD hΓ ι f q hq hvan hgen hpc IH

end Work.Serre