/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE file.
Authors: Work.FFResidual
-/
import Mathlib
import Submission.Work.FFResidual.CharP.Order
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The Artin–Schreier automorphism acts trivially on the residue field of the Eisenstein order

Let `P : FunctionFieldPlace 𝔽 𝕜` be a place of a function field over its constants, of
characteristic `5`, and let `AsTop P = 𝕜(s)`, `s ^ 5 - s = π⁻¹`, be the Artin–Schreier extension of
`Submission/Work/FFResidual/CharP/Basic`, with generator the automorphism `σ : s ↦ s + 1`
(`P.asEquiv`).  Let `AsOrder P = R[w] = R[X]/(X ^ 5 + π X ^ 4 - π)` be the Eisenstein order of
`Submission/Work/FFResidual/CharP/Order`, the local model of the place of `AsTop P` above the place
`P`, where `w = asRecip P = s⁻¹` is the uniformizer (`asRecip_pow`).

This file proves `Work.ClassA.ModelResidueTrivial` for the model: `σ` acts **trivially on the
residue field** of `R[w]`, i.e. for `r r' ∈ R[w]` with `algebraMap r' = σ (algebraMap r)` one has
`residue r' = residue r`.

The mathematical content is the observation of the paper that `σ w - w` is divisible by the
uniformizer `w` of the model.  Since `σ(s) = s + 1` and `w = s⁻¹`,

  `σ(w) = 1/(s + 1) = w/(1 + w)`,

so `σ(w) = w · (1 + w)⁻¹` and, because `1 + w` is a unit of `R[w]` (its residue is `1`), the
element `w / (1 + w)` is *in* `R[w]`: it is `w · g(w)`, where `g ∈ R[X]` is the Bézout cofactor of
`X + 1` with respect to `X ^ 5 + π X ^ 4 - π` (`asOrderG_eq`: `(X + 1) * g - 1 = X ^ 5 + π X ^ 4 - π`).
The `R`-algebra endomorphism `asOrderHomRes` of `R[w]` sending `w ↦ w / (1 + w)` computes `σ` on
`R[w]` (`asOrderMap_asOrderHomResRes`: `asOrderMap (asOrderHomRes r) = σ (asOrderMap r)`), and
`asOrderHomRes r - r` is divisible by `w` (`asOrderHomRes_sub_mem_span_root`) — the formal content of
`σ(w) - w = -w²/(1 + w) ∈ (w)`.  As `w` generates the maximal ideal, the residue map kills it, and
`σ` acts trivially on the residue field.

## Main results

* `FunctionFieldPlace.asOrderHomRes` — the endomorphism `w ↦ w/(1 + w)` of `R[w]`.
* `FunctionFieldPlace.asOrderMap_asOrderHomResRes` — its compatibility with `σ` and `asOrderMap`.
* `Work.FFResidual.CharP.modelResidueTrivial_asOrder` — `σ` is residue-trivial on `R[w]`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace Work.FFResidual

noncomputable section

open Polynomial

namespace FunctionFieldPlace

variable {𝔽 : Type} [Field 𝔽] {𝕜 : Type} [Field 𝕜] [Algebra 𝔽 𝕜]

/-- The defining polynomial of the Eisenstein order of the Artin–Schreier place, as a polynomial
over `R`: `X ^ 5 + π X ^ 4 - π`. -/
abbrev asOrderPoly (P : FunctionFieldPlace 𝔽 𝕜) : P.R[X] := X ^ 5 + C P.π * X ^ 4 - C P.π

/-- **The Bézout cofactor of `X + 1`.**  `X + 1` is invertible modulo `asOrderPoly P` because
`asOrderPoly P` evaluates to `-1` at `-1`; the explicit inverse is this quartic `asOrderG P`, with
`(X + 1) * asOrderG P - 1 = asOrderPoly P` (`asOrderG_eq`). -/
def asOrderG (P : FunctionFieldPlace 𝔽 𝕜) : P.R[X] :=
  X ^ 4 + C (P.π - 1) * X ^ 3 + C (1 - P.π) * X ^ 2 + C (P.π - 1) * X + C (1 - P.π)

/-- The element `1 + w` of the Eisenstein order, where `w` is the uniformizer (the root of
`asOrderPoly P`). -/
def asOrderU (P : FunctionFieldPlace 𝔽 𝕜) : P.AsOrder :=
  AdjoinRoot.root (asOrderPoly P) + 1

/-- The element `g(w) = (1 + w)⁻¹` of the Eisenstein order. -/
def asOrderV (P : FunctionFieldPlace 𝔽 𝕜) : P.AsOrder :=
  AdjoinRoot.mk (asOrderPoly P) (asOrderG P)

/-- **The image of the uniformizer under the Artin–Schreier automorphism**: `σ(w) = w/(1 + w)`. -/
def asOrderTheta (P : FunctionFieldPlace 𝔽 𝕜) : P.AsOrder :=
  AdjoinRoot.root (asOrderPoly P) * asOrderV P

theorem asOrderG_eq (P : FunctionFieldPlace 𝔽 𝕜) :
    (X + 1) * asOrderG P - 1 = asOrderPoly P := by
  rw [asOrderG, asOrderPoly]
  simp only [C_sub, C_1]
  first | refl_ring1 | ring

theorem asOrderU_mul_V (P : FunctionFieldPlace 𝔽 𝕜) : asOrderU P * asOrderV P = 1 := by
  have h : AdjoinRoot.mk (asOrderPoly P) ((X + 1) * asOrderG P) = 1 := by
    have h2 : AdjoinRoot.mk (asOrderPoly P) ((X + 1) * asOrderG P)
        = AdjoinRoot.mk (asOrderPoly P) (asOrderPoly P + 1) := by
      rw [← asOrderG_eq]; ring_nf
    rw [h2, map_add, AdjoinRoot.mk_self, zero_add, map_one]
  have h3 : AdjoinRoot.mk (asOrderPoly P) (X + 1) = AdjoinRoot.root (asOrderPoly P) + 1 := by
    rw [map_add, map_one, AdjoinRoot.mk_X]
  rw [map_mul] at h
  rw [h3] at h
  rw [asOrderU, asOrderV]
  exact h

/-- The Eisenstein order of the Artin–Schreier place has characteristic `5`. -/
theorem charP_asOrderRes (P : FunctionFieldPlace 𝔽 𝕜) [CharP 𝕜 5] [IsDomain P.AsOrder] :
    CharP P.AsOrder 5 := by
  haveI : CharP P.R 5 := (algebraMap P.R 𝕜).charP (IsFractionRing.injective P.R 𝕜) 5
  exact CharP.of_ringHom_of_ne_zero (AdjoinRoot.of (asOrderPoly P)) 5 (by norm_num)

theorem asOrderU_pow_five (P : FunctionFieldPlace 𝔽 𝕜) [CharP 𝕜 5] [IsDomain P.AsOrder] :
    asOrderU P ^ 5 = 1 + AdjoinRoot.root (asOrderPoly P) ^ 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI := charP_asOrderRes P
  rw [asOrderU]
  rw [add_pow_char]
  first | refl_ring1 | ring

/-- **The relation of the uniformizer of the model**: `w ^ 5 + π w ^ 4 - π = 0`. -/
theorem asOrderRoot_poly (P : FunctionFieldPlace 𝔽 𝕜) :
    AdjoinRoot.root (asOrderPoly P) ^ 5
      + AdjoinRoot.of (asOrderPoly P) P.π * AdjoinRoot.root (asOrderPoly P) ^ 4
      - AdjoinRoot.of (asOrderPoly P) P.π = 0 := by
  have h := AdjoinRoot.eval₂_root (asOrderPoly P)
  simp only [asOrderPoly, eval₂_add, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, eval₂_mul] at h
  exact h

/-- **`σ(w) = w/(1 + w)` satisfies the Eisenstein equation.**  This is where the characteristic `5`
enters: `(1 + w) ^ 5 = 1 + w ^ 5` (`add_pow_char`), which makes the identity
`(1 + w) ^ 5 * (σ(w) ^ 5 + π σ(w) ^ 4 - π) = w ^ 5 + π w ^ 4 - π` collapse; `1 + w` is a unit, so
`σ(w)` is a root of `asOrderPoly P` in `R[w]`. -/
theorem asOrderTheta_poly (P : FunctionFieldPlace 𝔽 𝕜) [CharP 𝕜 5] [IsDomain P.AsOrder] :
    asOrderTheta P ^ 5 + AdjoinRoot.of (asOrderPoly P) P.π * asOrderTheta P ^ 4
      - AdjoinRoot.of (asOrderPoly P) P.π = 0 := by
  haveI := charP_asOrderRes P
  have h5 := asOrderU_pow_five P
  have hw := asOrderRoot_poly P
  have hUV := asOrderU_mul_V P
  have hU5 : IsUnit (asOrderU P ^ 5) := (isUnit_iff_exists_inv.mpr ⟨asOrderV P, hUV⟩).pow 5
  have huθ : asOrderU P * asOrderTheta P = AdjoinRoot.root (asOrderPoly P) := by
    rw [asOrderTheta]
    rw [show asOrderU P * (AdjoinRoot.root (asOrderPoly P) * asOrderV P)
        = AdjoinRoot.root (asOrderPoly P) * (asOrderU P * asOrderV P) from by ring]
    rw [hUV, mul_one]
  have key : asOrderU P ^ 5
      * (asOrderTheta P ^ 5 + AdjoinRoot.of (asOrderPoly P) P.π * asOrderTheta P ^ 4
          - AdjoinRoot.of (asOrderPoly P) P.π) = 0 := by
    rw [show asOrderU P ^ 5
        * (asOrderTheta P ^ 5 + AdjoinRoot.of (asOrderPoly P) P.π * asOrderTheta P ^ 4
            - AdjoinRoot.of (asOrderPoly P) P.π)
        = (asOrderU P * asOrderTheta P) ^ 5
          + AdjoinRoot.of (asOrderPoly P) P.π * ((asOrderU P * asOrderTheta P) ^ 4 * asOrderU P)
          - AdjoinRoot.of (asOrderPoly P) P.π * asOrderU P ^ 5 from by ring]
    rw [huθ, h5]
    rw [asOrderU]
    rw [show AdjoinRoot.root (asOrderPoly P) ^ 5
        + AdjoinRoot.of (asOrderPoly P) P.π
          * (AdjoinRoot.root (asOrderPoly P) ^ 4 * (AdjoinRoot.root (asOrderPoly P) + 1))
        - AdjoinRoot.of (asOrderPoly P) P.π * (1 + AdjoinRoot.root (asOrderPoly P) ^ 5)
        = AdjoinRoot.root (asOrderPoly P) ^ 5
          + AdjoinRoot.of (asOrderPoly P) P.π * AdjoinRoot.root (asOrderPoly P) ^ 4
          - AdjoinRoot.of (asOrderPoly P) P.π from by ring]
    exact hw
  exact (IsUnit.mul_right_eq_zero hU5).mp key

/-- **The `R`-algebra endomorphism `w ↦ w/(1 + w)` of the Eisenstein order `R[w]`.**  It realizes
the Artin–Schreier automorphism `σ : s ↦ s + 1` on the local model. -/
noncomputable def asOrderHomRes (P : FunctionFieldPlace 𝔽 𝕜) [CharP 𝕜 5] [IsDomain P.AsOrder] :
    P.AsOrder →+* P.AsOrder :=
  AdjoinRoot.lift (AdjoinRoot.of (asOrderPoly P)) (asOrderTheta P) (by
    simp only [asOrderPoly, eval₂_add, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, eval₂_mul]
    exact asOrderTheta_poly P)

theorem asOrderHomRes_of (P : FunctionFieldPlace 𝔽 𝕜) [CharP 𝕜 5] [IsDomain P.AsOrder] (a : P.R) :
    asOrderHomRes P (AdjoinRoot.of (asOrderPoly P) a) = AdjoinRoot.of (asOrderPoly P) a :=
  AdjoinRoot.lift_of _

theorem asOrderHomRes_root (P : FunctionFieldPlace 𝔽 𝕜) [CharP 𝕜 5] [IsDomain P.AsOrder] :
    asOrderHomRes P (AdjoinRoot.root (asOrderPoly P)) = asOrderTheta P :=
  AdjoinRoot.lift_root _

theorem asEquiv_algebraMap_R (P : FunctionFieldPlace 𝔽 𝕜) [CharP 𝕜 5] (r : P.R) :
    P.asEquiv (algebraMap P.R P.AsTop r) = algebraMap P.R P.AsTop r := by
  rw [algebraMap_R_AsTop]
  exact P.asHom_algebraMap _

/-- **`σ(w) * (1 + w) = w`**: the Artin–Schreier automorphism sends `w = s⁻¹` to `w/(1 + w)`. -/
theorem asEquiv_asRecip_mul (P : FunctionFieldPlace 𝔽 𝕜) [CharP 𝕜 5] :
    P.asEquiv P.asRecip * (1 + P.asRecip) = P.asRecip := by
  have hne : (P.asRoot + 1) ≠ 0 := by
    intro h
    have h2 : P.asEquiv P.asRoot = P.asEquiv 0 := by
      rw [map_zero, P.asEquiv_root]; exact h
    exact P.asRoot_ne_zero (P.asEquiv.injective h2)
  have hne0 : P.asRoot ≠ 0 := P.asRoot_ne_zero
  rw [show P.asEquiv P.asRecip = (P.asRoot + 1)⁻¹ from by
    rw [asRecip, map_inv₀, P.asEquiv_root]]
  rw [asRecip]
  rw [show (1 + P.asRoot⁻¹) = (P.asRoot + 1) * P.asRoot⁻¹ from by
    rw [add_mul, one_mul, mul_inv_cancel₀ hne0]]
  rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]

/-- **The endomorphism `asOrderHomRes` computes `σ` on the uniformizer**: `asOrderMap θ = σ w`. -/
theorem asOrderMap_theta (P : FunctionFieldPlace 𝔽 𝕜) [CharP 𝕜 5] :
    P.asOrderMap (asOrderTheta P) = P.asEquiv P.asRecip := by
  have hUV := asOrderU_mul_V P
  have hU : P.asOrderMap (asOrderU P) = P.asRecip + 1 := by
    rw [asOrderU, map_add, map_one, P.asOrderMap_root]
  have hmap : (P.asRecip + 1) * P.asOrderMap (asOrderV P) = 1 := by
    have h := congrArg P.asOrderMap hUV
    rw [map_mul, map_one, hU] at h
    exact h
  have hUne : P.asRecip + 1 ≠ 0 := by
    have hunit : IsUnit (P.asOrderMap (asOrderU P)) :=
      IsUnit.map P.asOrderMap (isUnit_iff_exists_inv.mpr ⟨asOrderV P, hUV⟩)
    rw [hU] at hunit
    exact hunit.ne_zero
  have h1 : P.asOrderMap (asOrderTheta P) * (P.asRecip + 1) = P.asRecip := by
    rw [asOrderTheta, map_mul, P.asOrderMap_root]
    rw [show P.asRecip * P.asOrderMap (asOrderV P) * (P.asRecip + 1)
        = P.asRecip * (P.asOrderMap (asOrderV P) * (P.asRecip + 1)) from by ring]
    rw [show P.asOrderMap (asOrderV P) * (P.asRecip + 1) = 1 from by rw [mul_comm, hmap]]
    rw [mul_one]
  have h2 : P.asEquiv P.asRecip * (P.asRecip + 1) = P.asRecip := by
    rw [show P.asRecip + 1 = 1 + P.asRecip from by ring]
    exact asEquiv_asRecip_mul P
  exact mul_right_cancel₀ hUne (by rw [h1, h2])

/-- **`asOrderHomRes` computes the Artin–Schreier automorphism** on the whole model `R[w]`:
`asOrderMap (asOrderHomRes r) = σ (asOrderMap r)`.  This is the precise statement `σ(R[w]) ⊆ R[w]`
needed for the residue triviality (and for `ModelPreserves`). -/
theorem asOrderMap_asOrderHomResRes (P : FunctionFieldPlace 𝔽 𝕜) [CharP 𝕜 5] [IsDomain P.AsOrder]
    (r : P.AsOrder) :
    P.asOrderMap (asOrderHomRes P r) = P.asEquiv (P.asOrderMap r) := by
  have hcomp : (P.asOrderMap.comp (asOrderHomRes P))
      = ((P.asEquiv : P.AsTop →+* P.AsTop)).comp P.asOrderMap := by
    refine AdjoinRoot.ringHom_ext ?_ ?_
    · ext a
      simp only [RingHom.comp_apply]
      rw [asOrderHomRes_of, ← AdjoinRoot.algebraMap_eq, P.asOrderMap_algebraMap]
      exact (asEquiv_algebraMap_R P a).symm
    · simp only [RingHom.comp_apply, asOrderHomRes_root, P.asOrderMap_root]
      exact asOrderMap_theta P
  exact RingHom.congr_fun hcomp r

/-- **The residue map of the model through the base.**  The ring hom `R[w] → R/𝔪` which is the
residue map `residue R` on the base `R` and sends the uniformizer `w` to `0`.  It exists because
`asOrderPoly P` evaluates at `0` to `-π`, and `π ∈ 𝔪`. -/
noncomputable def asOrderResidue (P : FunctionFieldPlace 𝔽 𝕜) :
    P.AsOrder →+* IsLocalRing.ResidueField P.R :=
  AdjoinRoot.lift (IsLocalRing.residue P.R) 0 (by
    have hπ : IsLocalRing.residue P.R P.π = 0 := by
      rw [IsLocalRing.residue_eq_zero_iff, P.isUniformizer]
      exact Ideal.mem_span_singleton_self P.π
    simp only [eval₂_add, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, eval₂_mul]
    rw [zero_pow (by norm_num : (5 : ℕ) ≠ 0), zero_pow (by norm_num : (4 : ℕ) ≠ 0), hπ]
    ring)

theorem asOrderResidue_root (P : FunctionFieldPlace 𝔽 𝕜) :
    asOrderResidue P (AdjoinRoot.root (asOrderPoly P)) = 0 :=
  AdjoinRoot.lift_root _

/-- **The uniformizer is not a unit of the model**: the residue map of the model sends it to `0`. -/
theorem not_isUnit_rootRes (P : FunctionFieldPlace 𝔽 𝕜) :
    ¬ IsUnit (AdjoinRoot.root (asOrderPoly P)) := by
  intro hu
  have h := IsUnit.map (asOrderResidue P) hu
  rw [asOrderResidue_root] at h
  exact not_isUnit_zero h

/-- **The uniformizer generates the maximal ideal of the model.** -/
theorem root_mem_maximalIdealRes (P : FunctionFieldPlace 𝔽 𝕜)
    [IsDomain P.AsOrder] [IsDiscreteValuationRing P.AsOrder] :
    AdjoinRoot.root (asOrderPoly P) ∈ IsLocalRing.maximalIdeal P.AsOrder := by
  by_contra h
  exact not_isUnit_rootRes P (IsLocalRing.notMem_maximalIdeal.mp h)

theorem residue_rootRes (P : FunctionFieldPlace 𝔽 𝕜)
    [IsDomain P.AsOrder] [IsDiscreteValuationRing P.AsOrder] :
    IsLocalRing.residue P.AsOrder (AdjoinRoot.root (asOrderPoly P)) = 0 :=
  (IsLocalRing.residue_eq_zero_iff _).mpr (root_mem_maximalIdealRes P)

/-- **`σ(w) - w` is divisible by the uniformizer `w` of the model.**  The endomorphism
`asOrderHomRes` of `R[w]` acts on the quotient `R[w]/(w)` exactly as the identity, because it sends
the root `w` to `w/(1 + w) ≡ 0` and fixes the base `R`.  Equivalently, `asOrderHomRes r - r` is
divisible by `w`. -/
theorem asOrderHomRes_sub_mem_span_root (P : FunctionFieldPlace 𝔽 𝕜) [CharP 𝕜 5]
    [IsDomain P.AsOrder] (r : P.AsOrder) :
    asOrderHomRes P r - r ∈ Ideal.span {AdjoinRoot.root (asOrderPoly P)} := by
  set q := Ideal.Quotient.mk (Ideal.span {AdjoinRoot.root (asOrderPoly P)}) with hq
  have hcomp : q.comp (asOrderHomRes P) = q.comp (RingHom.id P.AsOrder) := by
    refine AdjoinRoot.ringHom_ext ?_ ?_
    · ext a
      simp only [RingHom.comp_apply, RingHom.id_apply]
      rw [asOrderHomRes_of]
    · simp only [RingHom.comp_apply, RingHom.id_apply]
      rw [asOrderHomRes_root]
      have hroot : q (AdjoinRoot.root (asOrderPoly P)) = 0 := by
        rw [hq, Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.subset_span (Set.mem_singleton _)
      rw [asOrderTheta, map_mul, hroot, zero_mul]
  have h := RingHom.congr_fun hcomp r
  simp only [RingHom.comp_apply, RingHom.id_apply] at h
  have hz : q (asOrderHomRes P r - r) = 0 := by rw [map_sub, h, sub_self]
  rw [hq] at hz
  exact (Ideal.Quotient.eq_zero_iff_mem).mp hz

/-- **The residue of `asOrderHomRes r` is the residue of `r`**: they differ by an element divisible
by the uniformizer `w`, which generates the maximal ideal. -/
theorem residue_asOrderHomRes (P : FunctionFieldPlace 𝔽 𝕜) [CharP 𝕜 5]
    [IsDomain P.AsOrder] [IsDiscreteValuationRing P.AsOrder] (r : P.AsOrder) :
    IsLocalRing.residue P.AsOrder (asOrderHomRes P r) = IsLocalRing.residue P.AsOrder r := by
  have hmem := asOrderHomRes_sub_mem_span_root P r
  have hle : Ideal.span {AdjoinRoot.root (asOrderPoly P)}
      ≤ IsLocalRing.maximalIdeal P.AsOrder :=
    (Ideal.span_singleton_le_iff_mem _).mpr (root_mem_maximalIdealRes P)
  have hz : IsLocalRing.residue P.AsOrder (asOrderHomRes P r - r) = 0 :=
    (IsLocalRing.residue_eq_zero_iff _).mpr (hle hmem)
  rw [map_sub] at hz
  exact sub_eq_zero.mp hz

/-- **The umbrella residue step.**  An element of `R[w]` whose image in the top field `𝕜(s)` is
`0` is a non-unit of `R[w]`, hence lies in the maximal ideal, hence is killed by the residue map.
(Ring homomorphisms send units to units; `asOrderMap` sends `x` to `0`, and `0` is not a unit in
the field `𝕜(s)`.) -/
theorem residue_eq_zero_of_asOrderMap_eq_zero (P : FunctionFieldPlace 𝔽 𝕜) [CharP 𝕜 5]
    [IsDomain P.AsOrder] [IsDiscreteValuationRing P.AsOrder] (x : P.AsOrder)
    (hx : P.asOrderMap x = 0) : IsLocalRing.residue P.AsOrder x = 0 := by
  have hnu : ¬ IsUnit x := by
    intro hu
    have h := IsUnit.map P.asOrderMap hu
    rw [hx] at h
    exact not_isUnit_zero h
  rw [IsLocalRing.residue_eq_zero_iff]
  by_contra h
  exact hnu (IsLocalRing.notMem_maximalIdeal.mp h)

end FunctionFieldPlace

namespace CharP

open FunctionFieldPlace

/-- **The Artin–Schreier automorphism acts trivially on the residue field of the model**: for an
integral element, its image under `s ↦ s + 1` has the same residue, because
`σ w - w = -w ^ 2 / (1 + w)` is divisible by the uniformizer `w` of the model. -/
theorem modelResidueTrivial_asOrder {𝔽 : Type} [Field 𝔽] {𝕜 : Type} [Field 𝕜] [Algebra 𝔽 𝕜]
    (P : Work.FFResidual.FunctionFieldPlace 𝔽 𝕜) [CharP 𝕜 5]
    [IsDomain (Work.FFResidual.FunctionFieldPlace.AsOrder P)]
    [IsDiscreteValuationRing (Work.FFResidual.FunctionFieldPlace.AsOrder P)] :
    Work.ClassA.ModelResidueTrivial (Work.FFResidual.FunctionFieldPlace.AsOrder P) ⇑(P.asEquiv) := by
  intro r r' hr
  change P.asOrderMap r' = P.asEquiv (P.asOrderMap r) at hr
  have h0 : P.asOrderMap (r' - asOrderHomRes P r) = 0 := by
    rw [map_sub, hr, asOrderMap_asOrderHomResRes P r, sub_self]
  have hz := residue_eq_zero_of_asOrderMap_eq_zero P (r' - asOrderHomRes P r) h0
  rw [map_sub] at hz
  rw [sub_eq_zero.mp hz, residue_asOrderHomRes P r]

end CharP

end

end Work.FFResidual
