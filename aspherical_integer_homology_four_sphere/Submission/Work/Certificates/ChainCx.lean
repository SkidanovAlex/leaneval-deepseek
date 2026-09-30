/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `Certificates/`: finite chain complexes of free `ℤ`-modules

A `FinChainCx` is a chain complex of finitely generated free `ℤ`-modules, presented by
*sparse* boundary operators: `C_k = ℤ^{(dim k)}` and `bd k : C_{k+1} → C_k` is an `SOp`,
with the relation `∂_{k+1} ∘ ∂_{k+2} = 0` as a matrix identity.

`toChainComplex` is the resulting object of `ChainComplex (ModuleCat ℤ) ℕ`, and `homology k`
is its `k`-th homology -- the same object the areas `DeltaHomology`/`Subdivision` compute by
other means, so certificates proved here compose with quasi-isomorphisms proved there.
-/

import Mathlib
import Submission.Work.Certificates.Sparse

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open CategoryTheory

namespace Work.Certificates

/-- A finite chain complex of free `ℤ`-modules: `ℤ^{(dim k)}` in degree `k`, with sparse
boundary maps `bd k : C_{k+1} → C_k` satisfying `∂ ∘ ∂ = 0`. -/
structure FinChainCx where
  /-- The number of cells (free generators) in degree `k`. -/
  dim : ℕ → ℕ
  /-- `bd k` is the boundary `∂_{k+1} : C_{k+1} → C_k`, as the matrix
  `Matrix (Fin (dim k)) (Fin (dim (k+1))) ℤ`. -/
  bd : ∀ k, SOp (dim k) (dim (k+1))
  /-- The chain condition `∂_{k+1} ∘ ∂_{k+2} = 0`. -/
  bd_comp : ∀ k, (bd k).toMatrix * (bd (k+1)).toMatrix = 0

namespace FinChainCx

variable (C : FinChainCx)

/-- The chain complex of `ℤ`-modules underlying a `FinChainCx`. -/
noncomputable def toChainComplex : ChainComplex (ModuleCat ℤ) ℕ :=
  ChainComplex.of (fun k => ModuleCat.of ℤ (Fin (C.dim k) → ℤ))
    (fun k => ModuleCat.ofHom (Matrix.toLin' ((C.bd k).toMatrix)))
    (fun k => by
      rw [← ModuleCat.ofHom_comp, ← Matrix.toLin'_mul, C.bd_comp k]
      simp)

/-- The `k`-th homology `H_k(C)` of a `FinChainCx`, as an object of `ModuleCat ℤ`. -/
noncomputable abbrev homology (k : ℕ) : ModuleCat ℤ := (C.toChainComplex).homology k

/-- The complex with `b k` free generators in degree `k` and zero boundary maps; its homology
is `ℤ^{(b k)}` in degree `k` and zero elsewhere. -/
def zeroDiff (b : ℕ → ℕ) : FinChainCx where
  dim := b
  bd := fun _ => SOp.zero _ _
  bd_comp := fun k => by rw [SOp.toMatrix_zero, SOp.toMatrix_zero, Matrix.zero_mul]

/-- The sparse check that `bd` is a boundary operator on degrees `< N` (all data beyond `N`
is required to be zero by the caller). -/
def bdCheck (dim : ℕ → ℕ) (bd : ∀ k, SOp (dim k) (dim (k+1))) (N : ℕ) : Bool :=
  (List.range N).all fun k => ((bd k).mul (bd (k+1))).eqb (SOp.zero (dim k) (dim (k+2)))

/-- One degree of `bdCheck`, for verifying the boundary condition one degree at a time. -/
def bdCheckDeg (dim : ℕ → ℕ) (bd : ∀ k, SOp (dim k) (dim (k+1))) (k : ℕ) : Bool :=
  ((bd k).mul (bd (k+1))).eqb (SOp.zero (dim k) (dim (k+2)))

/-- `bdCheck` is the conjunction of its per-degree pieces. -/
theorem bdCheck_eq (dim : ℕ → ℕ) (bd : ∀ k, SOp (dim k) (dim (k+1))) (N : ℕ) :
    bdCheck dim bd N = (List.range N).all (bdCheckDeg dim bd) := rfl

end FinChainCx

/-! ### Notation-free names for the categorical API

The scoped notations `≫` and `𝟙` are not active in a statement that is elaborated outside
`open CategoryTheory`, so the certificates below refer to these names instead. -/

/-- Hom-sets of chain complexes of `ℤ`-modules, without the scoped notation `⟶`. -/
abbrev ChainHom (K L : ChainComplex (ModuleCat ℤ) ℕ) : Type := K ⟶ L

/-- Composition of chain maps, without the scoped notation `≫`. -/
def chainComp {K L M : ChainComplex (ModuleCat ℤ) ℕ} (f : ChainHom K L) (g : ChainHom L M) :
    ChainHom K M := f ≫ g

/-- The identity chain map, without the scoped notation `𝟙`. -/
def chainId (K : ChainComplex (ModuleCat ℤ) ℕ) : ChainHom K K := 𝟙 K

/-- Chain homotopies, exposed without the scoped notations. -/
abbrev ChainHomotopy {K L : ChainComplex (ModuleCat ℤ) ℕ} (f g : ChainHom K L) : Type :=
  Homotopy f g

/-- Homotopy equivalences of chain complexes. -/
abbrev ChainHomotopyEquiv (K L : ChainComplex (ModuleCat ℤ) ℕ) : Type := HomotopyEquiv K L

end Work.Certificates
