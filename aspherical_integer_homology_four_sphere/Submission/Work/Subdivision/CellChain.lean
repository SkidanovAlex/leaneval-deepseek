/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import Submission.Work.Subdivision.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The cellular chain complex of a `PolyCW`

The cellular chain complex of a polyhedral CW complex `P` with ℤ coefficients is
free in degree `k` on the cells of dimension `k`, with differential
`∂e = ∑_{f ⋖ e} inc(e,f) • f` (`f ⋖ e` meaning `f ∈ P.facets e`).

The cocycle condition `∂ ∘ ∂ = 0` (`PolyCW.HasDdZero`) is *not* built into the
definition of `PolyCW`: it is a hypothesis, supplied by the certificate data
(`∂² = 0` for the incidence numbers of a cell decomposition).  This mirrors the
blueprint, where `subdiv_chainMap` takes `h∂∂ : ∂ ∘ ∂ = 0` as a hypothesis.
-/

namespace Work.Subdivision

universe u

namespace PolyCW

variable (P : PolyCW.{u})

/-- The free ℤ-module on the cells of dimension `k`. -/
noncomputable abbrev cellMod (k : ℕ) : Type u := {e : P.Cell // P.dim e = k} →₀ ℤ

/-- The image of a single `(k+1)`-cell under the incidence differential. -/
noncomputable def cellDval (k : ℕ) (e : {e : P.Cell // P.dim e = k + 1}) : cellMod P k :=
  ∑ x ∈ (P.facets e.1).attach,
    P.inc e.1 x.1 • Finsupp.single ⟨x.1, by
      have h := (P.mem_facets e.1 x.1).1 x.2
      have he := e.2
      omega⟩ 1

/-- The incidence differential `∂e = ∑_{f ⋖ e} inc(e,f) • f` as a linear map. -/
noncomputable def cellD (k : ℕ) : cellMod P (k + 1) →ₗ[ℤ] cellMod P k :=
  Finsupp.linearCombination ℤ fun e : {e : P.Cell // P.dim e = k + 1} => cellDval P k e

@[simp] theorem cellD_single (k : ℕ) (e : {e : P.Cell // P.dim e = k + 1}) :
    cellD P k (Finsupp.single e 1) = cellDval P k e := by
  simp [cellD]

/-- The cocycle condition: `∂ ∘ ∂ = 0`. -/
def HasDdZero : Prop := ∀ k, (cellD P k).comp (cellD P (k + 1)) = 0

/-- The augmentation condition on 1-cells: the incidence coefficients of the two
endpoints of every edge sum to zero.  This is needed for the subdivision to
respect boundaries in degree one, and it is a consequence of the sphere/generator
condition on the local complexes (`subdiv_quasiIso` only assumes the latter). -/
def HasAugZero : Prop := ∀ e : P.Cell, P.dim e = 1 → ∑ f ∈ P.facets e, P.inc e f = 0

/-- The cellular chain complex, given the cocycle condition. -/
noncomputable def cellChain (h : P.HasDdZero) : ChainComplex (ModuleCat ℤ) ℕ :=
  ChainComplex.of (fun k => ModuleCat.of ℤ (cellMod P k))
    (fun k => ModuleCat.ofHom (cellD P k))
    (fun k => ModuleCat.hom_ext (by simpa using h k))

@[simp] theorem cellChain_X (h : P.HasDdZero) (k : ℕ) :
    (cellChain P h).X k = ModuleCat.of ℤ (cellMod P k) := rfl

@[simp] theorem cellChain_d (h : P.HasDdZero) (k : ℕ) :
    (cellChain P h).d (k + 1) k = ModuleCat.ofHom (cellD P k) := by
  simp only [cellChain, ChainComplex.of_d]

end PolyCW

end Work.Subdivision
