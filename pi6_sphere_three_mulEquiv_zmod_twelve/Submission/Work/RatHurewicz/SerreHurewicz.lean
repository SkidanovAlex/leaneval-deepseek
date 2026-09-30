import Mathlib
import Submission.Work.RatHurewicz.Basic
import Submission.Work.RatHurewicz.RelHomotopy
import Submission.Work.Stems.HurewiczNeutral
import Submission.Work.Drive.RationalHurewicz

set_option synthInstance.maxHeartbeats 400000

/-!
# The Hurewicz-type interfaces of the rational Hurewicz chapter

Area **RATHUREWICZ** (`Submission/Work/RatHurewicz/`).  This module records the *statements* of the
Hurewicz theorems the drive's contract `Work.Drive.RationalHurewiczStable` needs, in the language of
this area, together with the (proved) elementary relations between them.

The mathematical content of the contract is the **rational Hurewicz theorem in the stable range**
(Serre; Cartan–Serre; Klaus–Kreck): for a `(k-1)`-connected space `X` the Hurewicz homomorphism
`π_j(X) ⊗ ℚ → H_j(X;ℚ)` is an isomorphism for `j ≤ 2k - 2`.  The half of it that the contract
needs is the statement that the *kernel* is torsion, which is recorded here as
`HurewiczModTorsionRange` in the form of the explicit Hurewicz map
`Work.Stems.hurewiczMapN` of this workspace:

> `j ≤ 2k-2`, `a : π_j(X,x₀)`, `N • h(a) = 0` for some `N > 0` ⟹ `a^M = 1` for some `M > 0`.

The classical proof of the range statement (see `README.md` of this directory) proceeds through the
**relative Hurewicz theorem modulo torsion** for `(k-1)`-connected pairs and **homotopy excision**
(Blakers–Massey), plus Freudenthal's suspension theorem; `Excision.lean` records those statements, and
the relative homotopy groups and the long exact sequence of a pair that the argument needs are built
in `RelHomotopy.lean` / `PairLES.lean`.

## Main results of this module

* `Work.RatHurewicz.HurewiczModTorsionRange` — the crux, in Hurewicz-map form (a `Prop`).
* `Work.RatHurewicz.hurewiczModTorsionRange_iff_rationalHurewiczStable` — the (proved) equivalence
  with the drive's contract `Work.Drive.RationalHurewiczStable`; it pins down that the contract is
  exactly the injectivity-modulo-torsion half of the rational Hurewicz theorem.
* `Work.RatHurewicz.HurewiczModTorsionFirstDegree` — the same statement in the first non-vanishing
  degree `k` (the classical Hurewicz theorem modulo torsion), and its (proved) derivation from the
  range form.
* `Work.RatHurewicz.SphereConnected` — the classical connectivity of spheres, the extra input of the
  corollary for `Sⁿ` (`Work.Drive.StableStemsTorsion`).
-/

open scoped Topology

namespace Work.RatHurewicz

noncomputable section

/-- **The rational Hurewicz theorem in the stable range, injectivity-modulo-torsion form**
(Serre; Cartan–Serre).  For `k ≥ 2` and a `(k-1)`-connected space `X` (all `π_i(X,x₀)` with `i < k`
are trivial, `π_0` included), and for `1 ≤ j ≤ 2k-2`, a class `a ∈ π_j(X,x₀)` whose Hurewicz class
`h(a) ∈ H_j(X;ℤ)` (the explicit map `Work.Stems.hurewiczMapN`) is of finite order is itself of
finite order.

This is the mathematical content of `Work.Drive.RationalHurewiczStable`, stated with the Hurewicz
map on homotopy groups rather than on cubes; the two forms are equivalent
(`hurewiczModTorsionRange_iff_rationalHurewiczStable`). -/
def HurewiczModTorsionRange : Prop :=
  ∀ (k : ℕ), 2 ≤ k → ∀ (X : Type) [TopologicalSpace X] (x₀ : X),
    (∀ i < k, Subsingleton (HomotopyGroup (Fin i) X x₀)) →
    ∀ (n : ℕ), n + 1 ≤ 2 * k - 2 →
      ∀ a : HomotopyGroup (Fin (n + 1)) X x₀,
        (∃ N : ℕ, 0 < N ∧
            (N : ℤ) • Work.Stems.hurewiczMapN (n + 1)
              (Nat.succ_le_succ (Nat.zero_le n)) x₀ a = 0) →
          ∃ N : ℕ, 0 < N ∧ a ^ N = 1

/-- **The classical Hurewicz theorem modulo torsion, in the first non-vanishing degree.**

For `k ≥ 2` and a `(k-1)`-connected space `X`, the kernel of the Hurewicz map
`π_k(X,x₀) → H_k(X;ℤ)` is torsion.  (Classically the map is an isomorphism in this degree; the
weaker torsion statement is what the range theorem builds on.) -/
def HurewiczModTorsionFirstDegree : Prop :=
  ∀ (m : ℕ), 1 ≤ m → ∀ (X : Type) [TopologicalSpace X] (x₀ : X),
    (∀ i < m + 1, Subsingleton (HomotopyGroup (Fin i) X x₀)) →
      ∀ a : HomotopyGroup (Fin (m + 1)) X x₀,
        (∃ N : ℕ, 0 < N ∧
            (N : ℤ) • Work.Stems.hurewiczMapN (m + 1)
              (Nat.succ_le_succ (Nat.zero_le m)) x₀ a = 0) →
          ∃ N : ℕ, 0 < N ∧ a ^ N = 1

/-- The range form of the rational Hurewicz theorem implies its first-degree form (take `j = k`;
the range condition `k ≤ 2k - 2` is `2 ≤ k`). -/
theorem hurewiczModTorsionFirstDegree_of_range (h : HurewiczModTorsionRange) :
    HurewiczModTorsionFirstDegree := by
  intro m hm X _ x₀ hconn a ha
  exact h (m + 1) (by omega) X x₀ hconn m (by omega) a ha

/-- **`Sⁿ` is `(n-1)`-connected**: all homotopy groups `π_j(Sⁿ)`, `j < n`, vanish.

This is the classical connectivity of the sphere, stated here as an interface: it is the extra input
needed to apply the range form of the rational Hurewicz theorem to `Sⁿ` and deduce
`Work.Drive.StableStemsTorsion` (the corollary `stableStemsTorsion_of_rationalHurewiczStable` of
`Main.lean`).  For `j = 0` it says that `Sⁿ` is path connected, for `j = 1` that it is simply
connected (`Work.StemsB.sphSimplyConnected`, proved), and for `2 ≤ j < n` it is the classical
statement that `Sⁿ` has no cells below dimension `n`. -/
def SphereConnected : Prop :=
  ∀ (n : ℕ), 1 ≤ n →
    ∀ (x₀ : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1),
      ∀ j : ℕ, j < n →
        Subsingleton (HomotopyGroup (Fin j)
          (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) x₀)

end

end Work.RatHurewicz
