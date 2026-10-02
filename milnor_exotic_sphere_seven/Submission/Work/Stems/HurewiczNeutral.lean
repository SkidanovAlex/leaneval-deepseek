import Submission.Work.Stems.hurewiczChain_eq_of_homotopic

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# A fork-neutral Hurewicz map

The workspace declares the name `Work.Cohomology.chainMap_comp'` in two different files
(`Submission/Work/Cohomology/localCohomology.lean` and
`Submission/Work/Cohomology/prodSphereAux.lean`), so a module whose import closure contains *both*
fails to build.  In particular `Work.Stems.HurewiczMapNatural` (via the wedge/pinch machinery used
for the additivity of the Hurewicz map, `Stems/WedgeFstSndAux.lean` →
`Work.Cohomology.proj_pair_injective` → `prodSphereAux`) cannot be imported together with
`Work.Drive.Interfaces` (→ `localCohomology`) or with the `Work.StemsB` fork (→
`Cohomology.Compat*.prodSphereAux`).

This file provides the **definition** of the Hurewicz map `πₙ(X,x₀) → Hₙ(X;ℤ)` (its
well-definedness on homotopy classes only) with a *fork-neutral* import closure: it imports only
`Submission.Work.Stems.hurewiczChain_eq_of_homotopic`, whose closure contains no module declaring
`chainMap_comp'` (checked).  It can therefore be used to *state* Hurewicz-type theorems on either
side of the workspace.

The additivity (`hurewiczMap_mul`) and naturality are *not* available here — they live in
`Work.Stems.HurewiczMap`/`HurewiczMapNatural`, whose closure contains `prodSphereAux`.  Only the
following two facts are recorded, and both are immediate from the definition:

* `Work.Stems.hurewiczMapN_mk` — the value on the class of a cube;
* `Work.Stems.hurewiczMapN_out` — the value on `Quotient.out` of a class.

The agreement with `Work.Stems.hurewiczMap` is in `Stems/HurewiczNeutralAgree.lean` (a file that
*does* import the non-neutral `HurewiczMapNatural`, and hence cannot be imported on the StemsB
side).
-/

open CategoryTheory AlgebraicTopology
open scoped Topology Topology.Homotopy unitInterval

namespace Work.Stems

noncomputable section

/-- **The Hurewicz map** `πₙ(X,x₀) → Hₙ(X;ℤ)`, in a fork-neutral module: the descent of
`hurewiczChain` to the homotopy group. -/
def hurewiczMapN (n : ℕ) (hn : 1 ≤ n) {X : Type} [TopologicalSpace X] (x₀ : X) :
    HomotopyGroup (Fin n) X x₀ → (chains (TopCat.of X)).homology n :=
  Quotient.lift (fun p => hurewiczChain n hn x₀ p)
    (fun _ _ h => hurewiczChain_eq_of_homotopic n hn h)

/-- `hurewiczMapN` of the class of a cube is the Hurewicz class of that cube. -/
theorem hurewiczMapN_mk (n : ℕ) (hn : 1 ≤ n) {X : Type} [TopologicalSpace X] {x₀ : X}
    (p : Ω^ (Fin n) X x₀) :
    hurewiczMapN n hn x₀ ⟦p⟧ = hurewiczChain n hn x₀ p := rfl

/-- The value of `hurewiczMapN` on a representative `Quotient.out`. -/
theorem hurewiczMapN_out (n : ℕ) (hn : 1 ≤ n) {X : Type} [TopologicalSpace X] (x₀ : X)
    (a : HomotopyGroup (Fin n) X x₀) :
    hurewiczMapN n hn x₀ a = hurewiczChain n hn x₀ (Quotient.out a) := by
  conv_lhs => rw [← Quotient.out_eq a]
  exact hurewiczMapN_mk (x₀ := x₀) n hn (Quotient.out a)

end

end Work.Stems
