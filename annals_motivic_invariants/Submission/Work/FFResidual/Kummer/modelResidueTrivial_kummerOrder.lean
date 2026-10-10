/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE file.
Authors: Work.FFResidual
-/
import Mathlib
import Submission.Work.FFResidual.Kummer.modelPreserves_kummerOrder
import Submission.Work.ClassA.Model

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The Kummer automorphism acts trivially on the residue field of the Eisenstein order `R[s]`

Let `P : FunctionFieldPlace 𝔽 𝕜` be a place of a function field over its constants, `Top P = 𝕜(s)`,
`s ^ 5 = π` the Kummer extension (`Submission/Work/FFResidual/Kummer/Basic`) and
`KummerOrder P = R[s] = R[X]/(X ^ 5 - π)` its Eisenstein order
(`Submission/Work/FFResidual/Kummer/Order`). Let `σ = P.kummerEquiv ζ hζ` be the Kummer
automorphism `s ↦ ζ s`.

This file proves `Work.ClassA.ModelResidueTrivial`, i.e. that `σ` acts **trivially on the residue
field** of the local model `R[s]`: for `r r' ∈ R[s]` with `algebraMap r' = σ (algebraMap r)` we have
`residue r' = residue r`.

The mathematical content is the observation of the paper that `σ x - x` is divisible by the
uniformizer `s` of the model: explicitly `kummerOrderHom r - r ∈ (s)` for every `r ∈ R[s]`, where
`kummerOrderHom` is the endomorphism `s ↦ ζ s` of `R[s]` (`Submission/Work/FFResidual/Kummer/Model`).
Since `s` generates the maximal ideal of `R[s]`, the residue map kills `(s)`. Finally, a residue-level
algebraic remark: an element of `R[s]` killed by the map `kummerOrderMap : R[s] → 𝕜(s)` is a
non-unit, hence also killed by `residue`.

## Main results

* `FunctionFieldPlace.kummerOrderResidue` — the ring hom `R[s] → R/𝔪 = ResidueField R` with
  `s ↦ 0`, i.e. the residue map of the model seen through the base.
* `FunctionFieldPlace.kummerOrderHom_sub_mem_span_root` — `kummerOrderHom r - r ∈ (s)`.
* `Work.FFResidual.Kummer.modelResidueTrivial_kummerOrder` — `σ` is residue-trivial on `R[s]`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false


namespace Work.FFResidual

noncomputable section

open Polynomial

namespace FunctionFieldPlace

variable {𝔽 : Type} [Field 𝔽] {𝕜 : Type} [Field 𝕜] [Algebra 𝔽 𝕜]

/-- The defining polynomial of the Eisenstein order, as a polynomial over `R`. -/
abbrev kummerOrderPoly (P : FunctionFieldPlace 𝔽 𝕜) : P.R[X] := X ^ 5 - C P.π

/-- **The residue map of the model through the base.** The ring hom `R[s] → R/𝔪` which is the
residue map `residue R` on the base `R` and sends the uniformizer `s` to `0`.  It exists because
`X ^ 5 - π ↦ 0 ^ 5 - residue π = 0` (`π ∈ 𝔪`). -/
noncomputable def kummerOrderResidue (P : FunctionFieldPlace 𝔽 𝕜) :
    P.KummerOrder →+* IsLocalRing.ResidueField P.R :=
  AdjoinRoot.lift (IsLocalRing.residue P.R) 0 (by
    simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
    rw [zero_pow (by norm_num : (5 : ℕ) ≠ 0), zero_sub, neg_eq_zero,
      IsLocalRing.residue_eq_zero_iff, P.isUniformizer]
    exact Ideal.mem_span_singleton.mpr dvd_rfl)

theorem kummerOrderResidue_root (P : FunctionFieldPlace 𝔽 𝕜) :
    P.kummerOrderResidue (AdjoinRoot.root P.kummerOrderPoly) = 0 :=
  AdjoinRoot.lift_root _

/-- **The Kummer root is not a unit of the Eisenstein order.** Indeed the residue map of the model
sends it to `0`, while ring homomorphisms send units to units and `0` is not a unit. -/
theorem not_isUnit_root (P : FunctionFieldPlace 𝔽 𝕜) :
    ¬ IsUnit (AdjoinRoot.root P.kummerOrderPoly) := by
  intro hu
  have h := IsUnit.map P.kummerOrderResidue hu
  rw [P.kummerOrderResidue_root] at h
  exact not_isUnit_zero h

/-- **The Kummer root generates the maximal ideal of the model**: it is the uniformizer `s` of
`R[s]`.  Since `R[s]` is local, `s ∉ R[s]^×` puts it in the maximal ideal. -/
theorem root_mem_maximalIdeal (P : FunctionFieldPlace 𝔽 𝕜)
    [IsDomain P.KummerOrder] [IsDiscreteValuationRing P.KummerOrder] :
    AdjoinRoot.root P.kummerOrderPoly ∈ IsLocalRing.maximalIdeal P.KummerOrder := by
  by_contra h
  exact P.not_isUnit_root (IsLocalRing.notMem_maximalIdeal.mp h)

/-- The residue of the Kummer root is zero, i.e. `s` is the uniformizer of the model. -/
theorem residue_root (P : FunctionFieldPlace 𝔽 𝕜)
    [IsDomain P.KummerOrder] [IsDiscreteValuationRing P.KummerOrder] :
    IsLocalRing.residue P.KummerOrder (AdjoinRoot.root P.kummerOrderPoly) = 0 :=
  (IsLocalRing.residue_eq_zero_iff _).mpr P.root_mem_maximalIdeal

/-- **`s` divides `kummerOrderHom r - r`.** The endomorphism `kummerOrderHom` of the Eisenstein
order acts on the quotient `R[s]/(s)` exactly as the identity, because it sends the root `s` to
`ζ s ≡ 0` and fixes the base `R`.  Equivalently, `kummerOrderHom r - r` is divisible by the
uniformizer `s`. -/
theorem kummerOrderHom_sub_mem_span_root (P : FunctionFieldPlace 𝔽 𝕜) (ζ : 𝔽)
    (hζ : IsPrimitiveRoot ζ 5) (r : P.KummerOrder) :
    P.kummerOrderHom ζ hζ r - r ∈ Ideal.span {AdjoinRoot.root P.kummerOrderPoly} := by
  set q := Ideal.Quotient.mk (Ideal.span {AdjoinRoot.root P.kummerOrderPoly}) with hq
  have hcomp : q.comp (P.kummerOrderHom ζ hζ) = q.comp (RingHom.id P.KummerOrder) := by
    refine AdjoinRoot.ringHom_ext ?_ ?_
    · ext a
      simp only [RingHom.comp_apply, RingHom.id_apply]
      rw [P.kummerOrderHom_of ζ hζ a]
    · simp only [RingHom.comp_apply, RingHom.id_apply]
      rw [P.kummerOrderHom_root ζ hζ, Algebra.smul_def, map_mul]
      have hroot : q (AdjoinRoot.root P.kummerOrderPoly) = 0 := by
        rw [hq, Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.subset_span (Set.mem_singleton _)
      rw [hroot, mul_zero]
  have h := RingHom.congr_fun hcomp r
  simp only [RingHom.comp_apply, RingHom.id_apply] at h
  have hz : q (P.kummerOrderHom ζ hζ r - r) = 0 := by rw [map_sub, h, sub_self]
  rw [hq] at hz
  exact (Ideal.Quotient.eq_zero_iff_mem).mp hz

/-- **The umbrella residue step.** An element of `R[s]` that is killed by the inclusion into the
top field `𝕜(s)` is a non-unit of `R[s]`, hence lies in the maximal ideal, hence is killed by the
residue map.  (Ring homomorphisms send units to units; `kummerOrderMap` sends `x` to `0`, and `0` is
not a unit in the field `𝕜(s)`.) -/
theorem residue_eq_zero_of_kummerOrderMap_eq_zero (P : FunctionFieldPlace 𝔽 𝕜)
    [IsDomain P.KummerOrder] [IsDiscreteValuationRing P.KummerOrder] (x : P.KummerOrder)
    (hx : P.kummerOrderMap x = 0) : IsLocalRing.residue P.KummerOrder x = 0 := by
  have hnu : ¬ IsUnit x := by
    intro hu
    have h := IsUnit.map P.kummerOrderMap hu
    rw [hx] at h
    exact not_isUnit_zero h
  rw [IsLocalRing.residue_eq_zero_iff]
  by_contra h
  exact hnu (IsLocalRing.notMem_maximalIdeal.mp h)

/-- **The residue of `kummerOrderHom r` is the residue of `r`**: they differ by `(ζ - 1) · s`, and
`s` is the uniformizer of the model. -/
theorem residue_kummerOrderHom (P : FunctionFieldPlace 𝔽 𝕜)
    [IsDomain P.KummerOrder] [IsDiscreteValuationRing P.KummerOrder]
    (ζ : 𝔽) (hζ : IsPrimitiveRoot ζ 5) (r : P.KummerOrder) :
    IsLocalRing.residue P.KummerOrder (P.kummerOrderHom ζ hζ r)
      = IsLocalRing.residue P.KummerOrder r := by
  have hmem := P.kummerOrderHom_sub_mem_span_root ζ hζ r
  have hle : Ideal.span {AdjoinRoot.root P.kummerOrderPoly}
      ≤ IsLocalRing.maximalIdeal P.KummerOrder :=
    (Ideal.span_singleton_le_iff_mem _).mpr P.root_mem_maximalIdeal
  have hz : IsLocalRing.residue P.KummerOrder
      (P.kummerOrderHom ζ hζ r - r) = 0 :=
    (IsLocalRing.residue_eq_zero_iff _).mpr (hle hmem)
  rw [map_sub] at hz
  exact sub_eq_zero.mp hz

end FunctionFieldPlace

namespace Kummer

open FunctionFieldPlace

/-- **The Kummer automorphism `s ↦ ζ s` acts trivially on the residue field of the model**
`R[s]`: for an integral element, its image under the automorphism has the same residue, because
`σ x - x` is divisible by `s` (the uniformizer of the model). -/
theorem modelResidueTrivial_kummerOrder {𝔽 : Type} [Field 𝔽] {𝕜 : Type} [Field 𝕜]
    [Algebra 𝔽 𝕜] (P : Work.FFResidual.FunctionFieldPlace 𝔽 𝕜)
    [IsDomain (Work.FFResidual.FunctionFieldPlace.KummerOrder P)]
    [IsDiscreteValuationRing (Work.FFResidual.FunctionFieldPlace.KummerOrder P)]
    (ζ : 𝔽) (hζ : IsPrimitiveRoot ζ 5) :
    Work.ClassA.ModelResidueTrivial (Work.FFResidual.FunctionFieldPlace.KummerOrder P)
      ⇑(P.kummerEquiv ζ hζ) := by
  intro r r' hr
  change P.kummerOrderMap r' = P.kummerEquiv ζ hζ (P.kummerOrderMap r) at hr
  -- `r'` and `kummerOrderHom r` have the same image in the top field:
  have hτ : P.kummerOrderMap (P.kummerOrderHom ζ hζ r)
      = P.kummerEquiv ζ hζ (P.kummerOrderMap r) :=
    P.kummerOrderMap_kummerOrderHom ζ hζ r
  have hker : P.kummerOrderMap (r' - P.kummerOrderHom ζ hζ r) = 0 := by
    rw [map_sub, hr, hτ, sub_self]
  have hzero := P.residue_eq_zero_of_kummerOrderMap_eq_zero (r' - P.kummerOrderHom ζ hζ r) hker
  rw [map_sub] at hzero
  have h1 : IsLocalRing.residue P.KummerOrder r'
      = IsLocalRing.residue P.KummerOrder (P.kummerOrderHom ζ hζ r) := sub_eq_zero.mp hzero
  rw [h1, P.residue_kummerOrderHom ζ hζ r]

end Kummer

end

end Work.FFResidual
