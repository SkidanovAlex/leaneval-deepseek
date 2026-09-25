/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Submission.NK.GlobalCFTdeep.Herbrand.SIdeles
import Submission.NK.GlobalCFT.Inclusion.globalCFT_exists_smul_eq_of_liesOver

/-!
# The idèles supported on the places above a fixed place

Milne's Proposition 2.7 computes the Herbrand quotient of the `T`-idèles `𝕀_{L,T}` by decomposing
them over the places `v` of `K`:

  `𝕀_{L,T} = ∏_{v ∈ S} (∏_{w | v} L_wˣ)`,

and computing each *fibre* `∏_{w | v} L_wˣ` by Shapiro's lemma from the local units `L_wˣ` at a
single `w | v`.  This file provides the `ℤ[Gal(L/K)]`-module `∏_{w | v} L_wˣ` — realised as the
subgroup of `𝕀 L` supported on the places above `v`, so that the Galois action is the ambient one
on idèles (`Idele.smul_apply`) and no dependent-product transport is needed:

* `NK.GlobalCFTdeep.fiberIdeles v` — the idèles whose components vanish outside the places above
  `v`;
* `NK.GlobalCFTdeep.smul_mem_fiberIdeles` — `Gal(L/K)` preserves it (the action permutes the
  places above `v`: `Place.liesOver_smul_iff`);
* `NK.GlobalCFTdeep.fiberIdelesRep v` — the fibre as a `Rep ℤ (L ≃ₐ[K] L)`.

The remaining step of Proposition 2.7 is the identification of this module with the *coinduced*
module `Coind_{D_w}^{G} L_wˣ` of the decomposition group `D_w = {σ | σ • w = w}`
(`NK.GlobalCFT.Inclusion.globalCFT_exists_smul_eq_of_liesOver` gives the transitivity of the
`G`-action on the fibre, i.e. the fibre is a single orbit).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace NK.GlobalCFTdeep

open NK.GlobalCFT

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- **The idèles supported on the places above `v`**: the subgroup of `𝕀 L` whose components
outside the fibre of `v` are trivial.  This is Milne's `∏_{w | v} L_wˣ` (the fibre is finite, so
the restricted-product condition is automatic). -/
def fiberIdeles (v : Place K) : Subgroup (Idele L) where
  carrier := {x | ∀ w : Place L, ¬ Place.LiesOver w v → x w = 1}
  one_mem' := by intro w _; exact Idele.one_apply w
  mul_mem' := by
    intro x y hx hy w hw
    rw [Idele.mul_apply, hx w hw, hy w hw, one_mul]
  inv_mem' := by
    intro x hx w hw
    rw [Idele.inv_apply, hx w hw, inv_one]

@[simp] theorem mem_fiberIdeles {v : Place K} {x : Idele L} :
    x ∈ fiberIdeles v ↔ ∀ w : Place L, ¬ Place.LiesOver w v → x w = 1 := Iff.rfl

/-- The fibre of `v` is preserved by `Gal(L/K)`: the action permutes the places above `v`. -/
theorem smul_mem_fiberIdeles (v : Place K) {σ : L ≃ₐ[K] L} {x : Idele L}
    (hx : x ∈ fiberIdeles (K := K) v) : σ • x ∈ fiberIdeles (K := K) v := by
  intro w hw
  rw [Idele.smul_apply]
  have h1 : ¬ Place.LiesOver (σ⁻¹ • w) v := fun h =>
    hw ((Place.liesOver_smul_iff (σ := σ⁻¹)).mp h)
  rw [hx (σ⁻¹ • w) h1, map_one]

/-- **The fibre of `v` as a `ℤ[Gal(L/K)]`-module** (Milne's `∏_{w | v} L_wˣ`). -/
def fiberIdelesRep (v : Place K) : Rep ℤ (L ≃ₐ[K] L) :=
  letI : MulDistribMulAction (L ≃ₐ[K] L) (fiberIdeles (K := K) (L := L) v) :=
    stableMulDistribMulAction (L ≃ₐ[K] L) (fiberIdeles (K := K) (L := L) v)
      (fun σ x hx => smul_mem_fiberIdeles v hx)
  Rep.ofMulDistribMulAction (L ≃ₐ[K] L) (fiberIdeles (K := K) (L := L) v)

/-- **The idèles supported on `T`**: the subgroup of `𝕀 L` whose components outside `T` are
trivial.  For `T` the union of the fibres over a finite set `S` of places of `K` this is the
internal direct product `∏_{v ∈ S} (∏_{w | v} L_wˣ)` — the module whose Herbrand quotient is the
product `∏_{v ∈ S} n_v` of Milne's Proposition 2.7.  (Note that `𝕀_{L,T}`, which asks for *local
units* outside `T` rather than triviality, is a different subgroup: no fibre splits off from
`𝕀_{L,T}` as a direct factor at an archimedean place, because there the local units are everything.
The correct decomposition of the `T`-idèles is
`𝕀_{L,T} = (∏_{v ∈ S} ∏_{w|v} L_wˣ) × (∏_{w ∉ T, w finite} U_w)`, the second factor having Herbrand
quotient `1`.) -/
def supportedIdeles (T : Set (Place L)) : Subgroup (Idele L) where
  carrier := {x | ∀ w : Place L, w ∉ T → x w = 1}
  one_mem' := by intro w _; exact Idele.one_apply w
  mul_mem' := by
    intro x y hx hy w hw
    rw [Idele.mul_apply, hx w hw, hy w hw, one_mul]
  inv_mem' := by
    intro x hx w hw
    rw [Idele.inv_apply, hx w hw, inv_one]

@[simp] theorem mem_supportedIdeles {T : Set (Place L)} {x : Idele L} :
    x ∈ supportedIdeles T ↔ ∀ w : Place L, w ∉ T → x w = 1 := Iff.rfl

/-- The idèles supported on `T` are `T`-idèles. -/
theorem supportedIdeles_le_TIdeles (T : Set (Place L)) :
    supportedIdeles T ≤ TIdeles T := by
  intro x hx w hw
  rw [hx w hw]
  exact one_mem _

/-- The supported idèles are stable under `Gal(L/K)` when `T` is. -/
theorem smul_mem_supportedIdeles {T : Set (Place L)}
    (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : Place L⦄, w ∈ T → σ • w ∈ T)
    {σ : L ≃ₐ[K] L} {x : Idele L} (hx : x ∈ supportedIdeles T) :
    σ • x ∈ supportedIdeles T := by
  intro w hw
  rw [Idele.smul_apply]
  have h1 : ¬ (σ⁻¹ • w) ∈ T := by
    intro h
    exact hw (by simpa using hT (σ := σ) h)
  rw [hx (σ⁻¹ • w) h1, map_one]

/-- **The idèles supported on `T` as a `ℤ[Gal(L/K)]`-module.** -/
def supportedIdelesRep (T : Set (Place L))
    (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : Place L⦄, w ∈ T → σ • w ∈ T) : Rep ℤ (L ≃ₐ[K] L) :=
  letI : MulDistribMulAction (L ≃ₐ[K] L) (supportedIdeles (L := L) T) :=
    stableMulDistribMulAction (L ≃ₐ[K] L) (supportedIdeles (L := L) T)
      (fun σ x hx => smul_mem_supportedIdeles hT hx)
  Rep.ofMulDistribMulAction (L ≃ₐ[K] L) (supportedIdeles (L := L) T)

/-- **The decomposition group of a place** `w` of `L`: the subgroup of `Gal(L/K)` fixing `w`.
For `L/K` Galois it is isomorphic to `Gal(L_w/K_v)`, and for cyclic `L/K` it is cyclic. -/
def decompositionSubgroup (w : Place L) : Subgroup (L ≃ₐ[K] L) where
  carrier := {σ | σ • w = w}
  one_mem' := by simp
  mul_mem' := by
    intro σ τ hσ hτ
    show (σ * τ) • w = w
    rw [mul_smul, hτ, hσ]
  inv_mem' := by
    intro σ hσ
    calc σ⁻¹ • w = σ⁻¹ • (σ • w) := by rw [hσ]
      _ = w := by rw [← mul_smul, inv_mul_cancel, one_smul]

@[simp] theorem mem_decompositionSubgroup {w : Place L} {σ : L ≃ₐ[K] L} :
    σ ∈ decompositionSubgroup (K := K) w ↔ σ • w = w := Iff.rfl

end NK.GlobalCFTdeep
