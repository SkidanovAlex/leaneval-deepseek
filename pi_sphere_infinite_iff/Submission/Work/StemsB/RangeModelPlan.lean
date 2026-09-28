import Mathlib
import Submission.Work.Serre.Models
import Submission.Work.RatHurewicz.S3Inputs
import Submission.Work.RatHurewicz.S3Inputs
import Submission.Work.RatHurewicz.AttachPush.CellInterior
import Submission.Work.AttachPush.exists_homotopy_avoids_cellOrigins

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Route to `Work.RatHurewicz.RangeModelRatAcyclic` (SERRE blueprint ADDENDUM 3 (A))

This area's contract `Work.Drive.StableStemsTorsion` is closed by the transfer
`Work.RatHurewicz.TruncationHomologyTransfer`, which is assembled (in
`Submission/Work/RatHurewicz/S3Corr.lean`) from Serre's exact sequence in the stable range and the
rational acyclicity of the range models of a `K(A,k)` **below `2k`**
(`Work.RatHurewicz.RangeModelRatAcyclic`).  This file records the decomposition of that statement,
which `SERRE_BLUEPRINT.md` ADDENDUM 3 (A) gives:

* **the compactness lemma** (`attachCells_finite_cells`, below): a compact subset of an iterated
  cell attachment meets only finitely many open cells — this is what lets one replace an arbitrary
  (possibly infinite) range model by a *finitely generated* one.
* **the finitely generated case**: `A` finitely generated; writing `A ≅ ℤ^r ⊕ F` with `F` finite
  (`Module.Finite`), a range model of `K(A,k)` is, in the range, a product of range models of
  `K(ℤ,k)` and `K(F,k)`, and rational Künneth reduces the claim to the two classical
  Eilenberg–MacLane computations:

  * `C2RatSphere k` — `K(ℤ,k)` is rationally `S^k` through degree `2k-1` (the periodicity
    `H_i(K(ℤ,k);ℚ) ≅ H_{i-k}(K(ℤ,1);ℚ)` of the loop shift, C2 of the blueprint);
  * `C3Finite` — `K(F,k)` is rationally acyclic for finite `F` (C3 of the blueprint).

The definitions `C2RatSphere`/`C3Finite` below are the exact interfaces; the reductions are the
work of this file.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.StemsB

noncomputable section

/-- **C2 of the blueprint, in the form the range model consumes.**  For `k ≥ 1`, a range model of
`K(ℤ,k)` through degree `N` is a rational `k`-sphere through degree `2k-1`: `H_k ≅ ℚ` and
`H_i = 0` for `0 < i ≤ 2k-1`, `i ≠ k`.

(`2k-1` is exactly the range in which the rational homology of `K(ℤ,k)` has no product classes:
the first multiple of `k` above `k` is `2k`.)

**WARNING (this form is too strong, and false).**  `Work.Serre.IsEMSpaceUpTo A m _ N X pt` does
**not** require `m ≤ N`; for `N < m` it only says `π_m ≅ A` and `π_i = 0` for `i < m`.  With
`N < k` the statement above therefore claims things about a space which is *not* a range model at
all: for `k = 2`, `N = 0` and `X = S² × S³` (which has `π_2 ≅ ℤ`, `π_1 = 0` and no constraint in
degree `3`), the hypothesis
`Work.Serre.IsEMSpaceUpTo ℤ 2 (by omega) 0 X pt` holds while `H_3(X;ℚ) = ℚ ≠ 0`, contradicting the
conclusion at `i = 3 ≤ 2·2−1`.  **The correct statement carries the hypothesis
`2*k - 1 ≤ N`** and is `C2RatSphereRange` below; `C2RatSphere` implies it
(`C2RatSphere.toRange`), and every consumer in this area uses the range form.  Nobody should try to
prove `C2RatSphere` as stated. -/
def C2RatSphere : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k) (N : ℕ) (X : Type) [TopologicalSpace X] (pt : X),
    Work.Serre.IsEMSpaceUpTo ℤ k (by omega) N X pt →
    Nonempty ((Work.Serre.ratH (TopCat.of X) k) ≅ ModuleCat.of ℚ ℚ) ∧
      ∀ i : ℕ, 0 < i → i ≤ 2 * k - 1 → i ≠ k →
        CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of X) i)

/-- **C2 of the blueprint, restricted to the range in which it is true.**  For `k ≥ 1` and a range
model `X` of `K(ℤ,k)` through a degree `N ≥ 2k-1`, one has `H_k(X;ℚ) ≅ ℚ` and `H_i(X;ℚ) = 0` for
`0 < i ≤ 2k-1`, `i ≠ k`.

This is `C2RatSphere` with the hypothesis `2*k - 1 ≤ N`, and it is **this** statement — not the
unrestricted one — that the range-model route consumes and that the Eilenberg–MacLane computation
can supply; see the warning at `C2RatSphere`. -/
def C2RatSphereRange : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k) (N : ℕ) (hN : 2 * k - 1 ≤ N) (X : Type) [TopologicalSpace X] (pt : X),
    Work.Serre.IsEMSpaceUpTo ℤ k (by omega) N X pt →
    Nonempty ((Work.Serre.ratH (TopCat.of X) k) ≅ ModuleCat.of ℚ ℚ) ∧
      ∀ i : ℕ, 0 < i → i ≤ 2 * k - 1 → i ≠ k →
        CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of X) i)

/-- The unrestricted (false as stated — see the warning at `C2RatSphere`) form implies the range
form. -/
theorem C2RatSphere.toRange (h : C2RatSphere) : C2RatSphereRange :=
  fun k hk N _ X _ pt hX => h k hk N X pt hX

/-- **C3 of the blueprint for finite `A`.**  A range model of `K(A,k)` with `A` finite abelian is
rationally acyclic in the range. -/
def C3Finite : Prop :=
  ∀ (A : Type) [AddCommGroup A] [Finite A] (k : ℕ) (hk : 1 ≤ k) (N : ℕ)
    (X : Type) [TopologicalSpace X] (pt : X),
    Work.Serre.IsEMSpaceUpTo A k (by omega) N X pt →
    ∀ i : ℕ, 0 < i → i ≤ N → CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of X) i)

/-- **C3 of the blueprint for finite `A`, restricted to `k ≥ 2`.**  This is the part of
`C3Finite` that the range-model route actually consumes (`Work.RatHurewicz.RangeModelRatAcyclic` is
stated for `k ≥ 2`), and it *is* reachable from subproject SERRE's genuine statements
(`Work.StemsB.C3Finite_of_serre_two`), whereas the `k = 1` instance is not: the comparison
`Work.StemsB.rangeModel_ratH_iso` requires `2 ≤ k`, and the workspace's `k = 1` range statement
(`Work.Serre.RangeEMVanOne`) loses one degree. -/
def C3FiniteTwo : Prop :=
  ∀ (A : Type) [AddCommGroup A] [Finite A] (k : ℕ) (hk : 2 ≤ k) (N : ℕ)
    (X : Type) [TopologicalSpace X] (pt : X),
    Work.Serre.IsEMSpaceUpTo A k (by omega) N X pt →
    ∀ i : ℕ, 0 < i → i ≤ N → CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of X) i)

/-- The `k ≥ 2` restriction of `C3Finite`. -/
theorem C3Finite.toTwo (h : C3Finite) : C3FiniteTwo :=
  fun A _ _ k hk N X _ pt hX i hi hiN => h A k (by omega) N X pt hX i hi hiN

/-- **The compactness lemma** (ADDENDUM 3 (A), step (2)): a compact subset of `attachCells n Y ι f`
meets only finitely many *open* cells.  Consequently it lies in the image of `Y` together with
finitely many closed cells, i.e. in a "finite subcomplex".  This is the lemma that lets one replace
an arbitrary range model by a finitely generated one, and it is already in the workspace
(`Work.AttachPush.finite_meets_cellInterior`, in `Submission/Work/AttachPush/`). -/
theorem attachCells_finite_cells {n : ℕ} {Y : Type} [TopologicalSpace Y] {ι : Type}
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y))
    {K : Set (Work.RatHurewicz.attachCells n Y ι f)} (hK : IsCompact K) :
    {i : ι | (Work.RatHurewicz.cellInterior n Y ι f i ∩ K).Nonempty}.Finite := by
  simpa only [Set.inter_comm] using Work.AttachPush.finite_meets_cellInterior n Y ι f hK

/-! ## The two delegated pieces

The two statements below are *delegated* (their proofs live in their own modules, so that this file
stays sorry-free); this file records only the interfaces `C2RatSphere`/`C3Finite` they are phrased
against.

* `Work.StemsB.serreC3_of_two_le` (module `Submission.Work.StemsB.serreC3_of_two_le`):
  `Work.RatHurewicz.TorsionHomotopyVanishing → C3Finite` for `n ≥ 2`.
* `Work.StemsB.rangeModelRatAcyclic_of_C2C3` (module
  `Submission.Work.StemsB.rangeModelRatAcyclic_of_C2C3`): the assembly of ADDENDUM 3 (A),
  `C2RatSphere → C3Finite → Work.RatHurewicz.RangeModelRatAcyclic`.
-/

end

end Work.StemsB
