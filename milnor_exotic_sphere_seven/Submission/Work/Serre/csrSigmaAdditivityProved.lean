import Mathlib
import Submission.Work.Serre.csrSigmaAdditivity

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Additivity of relative homology over a disjoint union (wrapper)

The proof lives in `Submission/Work/Serre/csrSigmaAdditivity.lean`; this file only records the
statement under its original name for the consumers of the cell-step argument.
-/

open scoped Topology
open CategoryTheory CategoryTheory.Limits

namespace Work.Serre

noncomputable section

/-- **Restatement in a fresh module of `Work.Serre.csrSigmaAdditivity`** (whose own file is still a stub), so that `Work.Serre.csrUnionIso` can import a *proved* version.  Additivity of relative singular homology with `ℚ`-coefficients over a disjoint union of pairs: if for every `i` the map of pairs `(X i, A i) → (Y i, B i)` induces an isomorphism on relative `ℚ`-homology in degree `m`, then so does the map of pairs `(Σ i, X i, Σ i, A i) → (Σ i, Y i, Σ i, B i)`.  The decomposition of the relative chains of a disjoint union into the coproduct of those of the pieces, naturally in a family of maps of pairs, is `Work.Serre.relChainsCoproductSquareRat` (`Submission/Work/Serre/sigmaPairIso.lean`), and the homology of a coproduct of chain complexes of `ℚ`-modules is the coproduct of the homologies (naturally so) by `Work.Serre.isIso_homologyMap_sigma` (`Submission/Work/Serre/sigmaHomologyRat.lean`). -/
theorem csrSigmaAdditivityProved {ι : Type} {X Y : ι → Type}
    [∀ i, TopologicalSpace (X i)] [∀ i, TopologicalSpace (Y i)]
    (A : ∀ i, Set (X i)) (B : ∀ i, Set (Y i)) (g : ∀ i, C(X i, Y i))
    (hg : ∀ i, Set.MapsTo (g i) (A i) (B i)) (m : ℕ)
    (h : ∀ i, CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Serre.relChainsRPairMap (A i) (B i) (g i) (hg i)) m)) :
    CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Serre.relChainsRPairMap {x : (Σ i, X i) | x.2 ∈ A x.1}
        {x : (Σ i, Y i) | x.2 ∈ B x.1}
        ⟨Sigma.map id (fun i => g i), by fun_prop⟩
        (by rintro ⟨i, x⟩ hx; exact hg i hx)) m) :=
  csrSigmaAdditivity A B g hg m h

end

end Work.Serre
