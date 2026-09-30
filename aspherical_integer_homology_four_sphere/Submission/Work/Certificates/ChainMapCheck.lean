/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `Certificates/`: chain maps and boundary witnesses between `FinChainCx`s

`chainMapCheck` decides that a family of sparse maps is a chain map up to a degree bound, and
`boundaryWitnessCheck` decides the chain identity `φ y − ψ z = ∂ w` in a single degree.  The
second is the form in which the polyhedral torus bridge of the Ratcliffe–Tschantz construction
supplies its witnesses (`sd_B z_B − sd_A z_A = ∂w`).
-/

import Mathlib
import Submission.Work.Certificates.ChainCx

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open CategoryTheory

namespace Work.Certificates

/-- The check that `φ k : D_k → C_k` is a chain map in degrees `< N`. -/
def chainMapCheck (C D : FinChainCx) (φ : ∀ k, SOp (D.dim k) (C.dim k)) (N : ℕ) : Bool :=
  (List.range N).all (fun k => ((φ k).mul (C.bd k)).eqb ((D.bd k).mul (φ (k+1))))

/-- The check of the chain identity `φ y − ψ z = ∂ w` in degree `k`, all maps applied sparsely.
`y` is a chain of `C` in degree `k`, `z` a chain of `D` in degree `k`, `w` a chain of `E` in
degree `k+1`, and `φ`, `ψ` map the chains of `C`, `D` into the chains of `E`. -/
def boundaryWitnessCheck (C D E : FinChainCx) (φ : ∀ k, SOp (E.dim k) (C.dim k))
    (ψ : ∀ k, SOp (E.dim k) (D.dim k)) (k : ℕ) (y : SVec (C.dim k))
    (z : SVec (D.dim k)) (w : SVec (E.dim (k+1))) : Bool :=
  (((φ k).apply y).sub ((ψ k).apply z)).eqb ((E.bd k).apply w)

/-- The specialization of `boundaryWitnessCheck` to `ψ` the identity (`φ y − z = ∂w`), with `z`
a chain of `E` itself. -/
def boundaryWitnessCheckId (C E : FinChainCx) (φ : ∀ k, SOp (E.dim k) (C.dim k)) (k : ℕ)
    (y : SVec (C.dim k)) (z : SVec (E.dim k)) (w : SVec (E.dim (k+1))) : Bool :=
  (((φ k).apply y).sub z).eqb ((E.bd k).apply w)

/-- The check that `y` is a cycle of `C` in degree `k+1`. -/
def cyclesCheck (C : FinChainCx) (k : ℕ) (y : SVec (C.dim (k+1))) : Bool :=
  ((C.bd k).apply y).eqb []

end Work.Certificates
