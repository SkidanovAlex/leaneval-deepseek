import Mathlib
import Submission.Work.RatHurewicz.RelHomotopy
import Submission.Work.RatHurewicz.exists_killed_tower
import Submission.Work.Cohomology.Chains
import Submission.Work.Cohomology.Pullback

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The two inputs of the stem induction for the rational Hurewicz theorem (area RATHUREWICZ)

This module isolates the **two statements outside this chapter** that the assembly
`Work.RatHurewicz.hurewiczModTorsionRange_of_inputs` (`S3Assembly.lean`) consumes, together with
the reduction `TruncationHomologyTransfer` of the hypothesis a tower produces.

## The mathematics

The rational Hurewicz theorem in the stable range for a `(k-1)`-connected space `X` is proved here
by the classical **stem induction**, whose step replaces `X` by the homotopy fibre `F` of a map
`inc : X → Z` which kills `π_{>k}` — the truncation tower
`Work.RatHurewicz.exists_killed_tower` of this area.  Two facts are needed about this step, and
both belong to the surrounding chapter (area SERRE's blueprint
`Submission/Work/Drive/SERRE_BLUEPRINT.md`, C2/C3 and E3(a)/E3(b)):

* `Work.RatHurewicz.TruncationHomologyTransfer` — **the homology transfer**: for a map `inc : X → Z`
  whose homotopy fibre `F` is `k`-connected and where `Z` is a *range model of `K(π_k X, k)`*
  (`π_j(Z) = 0` for `j ≤ 2k-1`, `j ≠ k`), the fibre inclusion `F → X` induces, in degrees
  `k < n+1 ≤ 2k-2`, a map `H_{n+1}(F;ℤ) → H_{n+1}(X;ℤ)` whose kernel is torsion.

  Its proof is Serre's exact sequence in the stable range together with the vanishing of the
  rational homology of a `K(A,k)` below `2k`:
  the long exact sequence of the pair `(X, F)` gives
  `H_{n+2}(X,F) → H_{n+1}(F) → H_{n+1}(X)` with `ker = im`;
  `H_j(X,F) ≅ H̃_j(Z)` for `j < b + f = k + (k+1) = 2k+1` (Serre's exact sequence, since the base
  `Z` is `(k-1)`-connected and the fibre `F` is `k`-connected), and `H̃_{n+2}(Z;ℚ) = 0` because
  `k < n+2 ≤ 2k-1` and `Z` is a range model of `K(π_kX,k)` (the classical computation of the
  rational homology of an Eilenberg–MacLane space below `2k`: `C2`/`C3` of the blueprint together
  with the comparison of a range model with the genuine `K(A,k)`).

* `Work.RatHurewicz.TowerStepData` — **the tower data**, which is *this area's* obligation and is
  produced from `Work.RatHurewicz.exists_killed_tower`: the tower's truncation `Z` is a range model
  of `K(π_kX,k)` (the low degrees from the compression property, the high ones from the killing),
  the fibre is `k`-connected, and the fibre inclusion is *surjective* on `π_{n+1}`
  (`k < n+1`), so that a class of `π_{n+1}(X)` can be transported to the fibre — where it is
  handled by the induction hypothesis, which applies at connectivity one higher.

The two together give `Work.Drive.RationalHurewiczStable` (and hence `...Stable3`), by
`S3Assembly.lean`.
-/

open scoped Topology
open CategoryTheory CategoryTheory.Limits

namespace Work.RatHurewicz

noncomputable section

/-! ## The range model condition -/

/-- **`Z` is a range model of `K(A,k)` up to degree `M`**: `π_j(Z) = 0` for `j ≤ M`, `j ≠ k`, and
`π_k(Z) = A`.  In the truncation tower `M = 2k-1` is what the transfer needs. -/
def IsRangeKModel (k M : ℕ) {Z : Type} [TopologicalSpace Z] (z₀ : Z) : Prop :=
  ∀ j : ℕ, j ≤ M → j ≠ k → Subsingleton (HomotopyGroup (Fin j) Z z₀)

/-! ## The rational homology of a range model (the Eilenberg–MacLane computation) -/

/-- **The rational homology of a range model of `K(A,k)` vanishes below `2k`.**

For `k ≥ 2` and a space `Z` with `π_j(Z) = 0` for `j ≤ 2k-1`, `j ≠ k` (`IsRangeKModel k (2k-1) z₀`),
the rational homology of `Z` vanishes in the degrees `k < j ≤ 2k-1`.

This is the classical computation of the rational homology of an Eilenberg–MacLane space below the
doubled degree — `C2` (for free `A`: rationally `K(A,k)` is a wedge of `k`-spheres below `2k`) and
`C3` (for torsion `A`) of `Submission/Work/Drive/SERRE_BLUEPRINT.md`, together with the comparison
of a range model with the genuine space.  It is the second half of the input
`TruncationHomologyTransfer` below. -/
def RangeModelRatAcyclic : Prop :=
  ∀ (k : ℕ), 2 ≤ k → ∀ (Z : Type) [TopologicalSpace Z] (z₀ : Z),
    IsRangeKModel k (2 * k - 1) z₀ →
    ∀ j : ℕ, k < j → j ≤ 2 * k - 1 →
      IsZero ((Work.Cohomology.singularChains ℚ (TopCat.of Z)).homology j)

/-! ## The two inputs -/

/-- **The homology transfer of the truncation step** (Serre's exact sequence in the stable range and
the rational homology of a `K(A,k)` below `2k`).

Let `k ≥ 2`, let `inc : X → Z` and let `F := homotopyFibre inc x₀`.
Assume

* `F` is `k`-connected (`π_j(F) = 0` for `j ≤ k`), and
* `Z` is a range model of `K(π_kX,k)` up to degree `2k-1` (`π_j(Z) = 0` for `j ≤ 2k-1`, `j ≠ k`).

Then for `k < n+1 ≤ 2k-2`, every element of `H_{n+1}(F;ℤ)` whose image in `H_{n+1}(X;ℤ)` under the
fibre inclusion is of finite order is itself of finite order.

This is the statement the consumers of this chapter must obtain from the neighbouring chapter: see
the module docstring.  It is *not* a shortcut — the long exact sequence of the pair gives
`ker(H_{n+1}(F) → H_{n+1}(X)) = im(H_{n+2}(X,F) → H_{n+1}(F))`, and the whole content is that
`H_{n+2}(X,F;ℚ) ≅ H̃_{n+2}(Z;ℚ) = 0` in the displayed range. -/
def TruncationHomologyTransfer : Prop :=
  ∀ (k : ℕ), 2 ≤ k → ∀ (X Z : Type) [TopologicalSpace X] [TopologicalSpace Z]
    (inc : C(X, Z)) (x₀ : X),
    (∀ j : ℕ, j ≤ k → Subsingleton (HomotopyGroup (Fin j) (homotopyFibre inc x₀)
      (homotopyFibreBasepoint inc x₀))) →
    IsRangeKModel k (2 * k - 1) (inc x₀) →
    ∀ n : ℕ, k < n + 1 → n + 1 ≤ 2 * k - 2 →
      ∀ y : (Work.Cohomology.singularChains ℤ (TopCat.of (homotopyFibre inc x₀))).homology (n + 1),
        (∃ M : ℕ, 0 < M ∧ M • HomologicalComplex.homologyMap
            (Work.Cohomology.chainMap ℤ (TopCat.of (homotopyFibre inc x₀)) (TopCat.of X)
              (TopCat.ofHom (homotopyFibreFst inc x₀))) (n + 1) y = 0) →
        ∃ M : ℕ, 0 < M ∧ M • y = 0

/-- **The tower data of the truncation step.**  For `k ≥ 2`, a `(k-1)`-connected `X` and a degree
`n+1 > k`, the truncation tower of `Work.RatHurewicz.exists_killed_tower` produces a map
`inc : X → Z` whose target is a range model of `K(π_kX,k)` up to degree `2k-1`, whose homotopy fibre
is `k`-connected, and on whose homotopy fibre *every* class of `π_{n+1}(X)` is hit:

the two vanishing statements are the two halves of the construction of the tower (the low degrees
`j < k` come from the compression property — the tower's cubes can be pushed into the range of the
inclusion, which is `X` — and the high degrees `k < j ≤ 2k-1` from the killing), and the
surjectivity is exactness of the long exact sequence of the pair at `π_{n+1}(X)`
(`Work.RatHurewicz.pair_les`), since `π_{n+1}(Z) = 0`. -/
def TowerStepData : Prop :=
  ∀ (k n : ℕ), 2 ≤ k → k < n + 1 → n + 1 ≤ 2 * k - 2 → ∀ (X : Type) [TopologicalSpace X] (x₀ : X),
    (∀ j < k, Subsingleton (HomotopyGroup (Fin j) X x₀)) →
    ∃ (Z : Type) (_ : TopologicalSpace Z) (inc : C(X, Z)),
      IsRangeKModel k (2 * k - 1) (inc x₀) ∧
      (∀ j : ℕ, j ≤ k → Subsingleton (HomotopyGroup (Fin j) (homotopyFibre inc x₀)
        (homotopyFibreBasepoint inc x₀))) ∧
      Function.Surjective (Work.StemsB.πmap (homotopyFibreFst inc x₀) n
        (homotopyFibreBasepoint inc x₀))

end

end Work.RatHurewicz
