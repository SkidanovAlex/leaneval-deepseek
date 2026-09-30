import Mathlib
import ChallengeDeps
import Submission.Work.HomologyMV.Model

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `HomologyMV/`: from a quasi-isomorphism and a certificate to `H_k(X) ≅ ℤ^n`

The identifications `eM`, `eN` of the Mayer–Vietoris computation
(`Work.HomologyMV.MVLES` / `Work.HomologyMV.intHomology_of_concrete`) are produced by composing

* a *quasi-isomorphism* from the chain complex `C` on which a certificate lives (the cellular
  or `Δ`-complex chain complex of `M̄`, of a cuspidal `T³`, or of a filling `T²`) to the singular
  chain complex of the space — this is the `HS2`/`HS3`/`G0` realisation step; with
* an isomorphism `H_k(C) ≅ ℤ^n` — this is `CERT`'s `SDR.sound`.

This file provides that composition, in both the singular-chain form and the
`LeanEval.Topology.intHomology` form used by the target statement.
-/

namespace Work.HomologyMV

open CategoryTheory AlgebraicTopology

noncomputable section

/-- The singular chain complex of `X` with coefficients in `ℤ`, as an object of
`ChainComplex (ModuleCat ℤ) ℕ`.  (This is the complex whose homology is
`LeanEval.Topology.intHomology k X`.) -/
abbrev singCx (X : TopCat) : ChainComplex (ModuleCat ℤ) ℕ :=
  ((singularChainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).obj X

/-- `LeanEval.Topology.intHomology k X` is the `k`-th homology of `singCx X`. -/
theorem intHomology_eq_singCx (k : ℕ) (X : TopCat) :
    LeanEval.Topology.intHomology k X = (singCx X).homology k := rfl

/-- A quasi-isomorphism `C ⟶ C_*(X)` transports an isomorphism `H_k(C) ≅ ℤ^n` to
`H_k(X) ≅ ℤ^n`. -/
theorem homology_iso_of_quasiIso {C : ChainComplex (ModuleCat ℤ) ℕ} (X : TopCat)
    (φ : C ⟶ singCx X) (hφ : QuasiIso φ) {k n : ℕ} (e : C.homology k ≅ freeMod n) :
    Nonempty ((singCx X).homology k ≅ freeMod n) :=
  ⟨(asIso (HomologicalComplex.homologyMap φ k)).symm ≪≫ e⟩

/-- The same in the `intHomology` form used by the target statement. -/
theorem intHomology_iso_of_quasiIso {C : ChainComplex (ModuleCat ℤ) ℕ} (X : TopCat)
    (φ : C ⟶ singCx X) (hφ : QuasiIso φ) {k n : ℕ} (e : C.homology k ≅ freeMod n) :
    Nonempty (LeanEval.Topology.intHomology k X ≅ freeMod n) :=
  ⟨(asIso (HomologicalComplex.homologyMap φ k)).symm ≪≫ e⟩

end

end Work.HomologyMV
