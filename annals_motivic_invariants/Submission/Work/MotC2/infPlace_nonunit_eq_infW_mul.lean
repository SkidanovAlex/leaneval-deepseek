/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.MotC2

# Non-units of the local ring at the point at infinity are multiples of `y/x²`

Let `E` be an elliptic Weierstrass curve over a field `L`, `A := infCoordRing E = L[u, w] ⊆ L(E)`
the chart-at-infinity coordinate ring (`u = 1/x = infU E`, `w = y/x² = infW E`) and
`R := infPlace E` the local ring of the point at infinity `O`, i.e. the localization of `A` at the
maximal ideal `I = ⟨u, w⟩`.

The chart relation `w² + a₁uw + a₃u²w = u + a₂u² + a₄u³ + a₆u⁴` can be written

  `u · h = w²`,   `h := 1 + a₂u + a₄u² + a₆u³ - (a₁ + a₃u)w ∈ A`,

and `h ≡ 1 (mod I)`, so `h` is a unit of `R` and `u = w·(w·h⁻¹)`.  Hence `w` generates the ideal
`I·R` of `R`, which is exactly the set of non-units of `R`:

* if `f ∈ R` is written as `a/b` with `a, b ∈ A`, `b ∉ I`, then `f` is a unit of `R` as soon as
  `a ∉ I` (its inverse is `b·a⁻¹`), so a non-unit has `a ∈ I = ⟨u, w⟩ ⊆ w·R`;
* writing `a = αu + βw` and `u = w·(w·h⁻¹)` exhibits `f·b = w·(α·(w·h⁻¹) + β)` with the second
  factor in `R`, hence `f = w·g` with `g ∈ R`.

The main result is `Work.MotC2.infPlace_nonunit_eq_infW_mul`, the dichotomy consumed by
`Work.MotC2.PoleCond`.
-/

import Mathlib
import Submission.Work.MotC2.Defs
import Submission.Work.MotC2.Relations
import Submission.Work.MotC2.InfPlaceRoute
import Submission.Work.MotC2.InfAux
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Polynomial WeierstrassCurve.Affine

namespace Work.MotC2

variable {L : Type*} [Field L]

/-! ## The element `h = 1 + a₂u + a₄u² + a₆u³ - (a₁ + a₃u)w` of the chart ring -/

/-- `u = 1/x` as an element of the chart-at-infinity coordinate ring `infCoordRing E`. -/
noncomputable def infPlaceAuxU (E : WeierstrassCurve L) : infCoordRing E :=
  ⟨infU E, InfAux.infU_mem_infCoordRing E⟩

/-- `w = y/x²` as an element of the chart-at-infinity coordinate ring `infCoordRing E`. -/
noncomputable def infPlaceAuxW (E : WeierstrassCurve L) : infCoordRing E :=
  ⟨infW E, InfAux.infW_mem_infCoordRing E⟩

/-- The element `h - 1` of the chart ring. -/
noncomputable def infPlaceAuxM (E : WeierstrassCurve L) : infCoordRing E :=
  algebraMap L (infCoordRing E) E.a₂ * infPlaceAuxU E +
      algebraMap L (infCoordRing E) E.a₄ * (infPlaceAuxU E) ^ 2 +
      algebraMap L (infCoordRing E) E.a₆ * (infPlaceAuxU E) ^ 3 -
      (algebraMap L (infCoordRing E) E.a₁ + algebraMap L (infCoordRing E) E.a₃ * infPlaceAuxU E) *
        infPlaceAuxW E

/-- The chart element `1 + a₂u + a₄u² + a₆u³ - (a₁ + a₃u)w`, which is `1` modulo the maximal ideal
`⟨u, w⟩` of the chart ring; it satisfies `u · h = w²` by the chart relation. -/
noncomputable def infPlaceAuxH (E : WeierstrassCurve L) : infCoordRing E :=
  1 + infPlaceAuxM E

lemma infPlaceAuxH_eq (E : WeierstrassCurve L) :
    infPlaceAuxH E = 1 + infPlaceAuxM E := rfl

/-- `h - 1` lies in the maximal ideal `⟨u, w⟩` of the chart ring. -/
lemma infPlaceAuxM_mem (E : WeierstrassCurve L) :
    infPlaceAuxM E ∈ InfAux.infIdealR E := by
  have hu : infPlaceAuxU E ∈ InfAux.infIdealR E :=
    Ideal.subset_span (Set.mem_insert _ _)
  have hw : infPlaceAuxW E ∈ InfAux.infIdealR E :=
    Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
  refine Ideal.sub_mem _ ?_ ?_
  · refine Ideal.add_mem _ (Ideal.add_mem _ ?_ ?_) ?_
    · exact Ideal.mul_mem_left _ _ hu
    · exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hu 2 (by norm_num))
    · exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hu 3 (by norm_num))
  · exact Ideal.mul_mem_left _ _ hw

/-- `h` is not in the maximal ideal `⟨u, w⟩` of the chart ring: it is `1` plus an element of that
ideal, and `1 ∉ ⟨u, w⟩` because `O` is a genuine point of `E`. -/
lemma infPlaceAuxH_notMem (E : WeierstrassCurve L) :
    infPlaceAuxH E ∉ InfAux.infIdealR E := by
  intro hmem
  have hsub : infPlaceAuxH E - infPlaceAuxM E ∈ InfAux.infIdealR E :=
    Ideal.sub_mem _ hmem (infPlaceAuxM_mem E)
  have hone : (1 : infCoordRing E) ∈ InfAux.infIdealR E := by
    have h : infPlaceAuxH E - infPlaceAuxM E = 1 := by
      rw [infPlaceAuxH_eq]
      first | refl_ring1 | ring
    rwa [h] at hsub
  exact InfAux.one_notMem_infIdealR E hone

lemma infPlaceAuxH_ne_zero (E : WeierstrassCurve L) : (infPlaceAuxH E : Func E) ≠ 0 := by
  intro h0
  have h : infPlaceAuxH E = 0 := Subtype.ext h0
  exact infPlaceAuxH_notMem E (h ▸ Ideal.zero_mem _)

/-- The chart relation `u · h = w²`. -/
lemma infPlaceAuxU_mul_H (E : WeierstrassCurve L) :
    infPlaceAuxU E * infPlaceAuxH E = infPlaceAuxW E ^ 2 := by
  apply Subtype.ext
  simp only [infPlaceAuxH, infPlaceAuxM, infPlaceAuxU, infPlaceAuxW, Subalgebra.coe_mul,
    Subalgebra.coe_pow, Subalgebra.coe_add, Subalgebra.coe_sub, Subalgebra.coe_one,
    Subalgebra.coe_algebraMap]
  linear_combination (norm := first | refl_ring1 | ring1) -infW_sq_relation E

/-- The chart relation in `L(E)`: `u = w · (w · h⁻¹)`. -/
lemma infPlaceAuxU_eq_W_mul (E : WeierstrassCurve L) :
    infU E = infW E * (infW E * ((infPlaceAuxH E : Func E))⁻¹) := by
  have hrel : infU E * (infPlaceAuxH E : Func E) = (infW E) ^ 2 := by
    have h := congrArg (fun z : infCoordRing E => (z : Func E)) (infPlaceAuxU_mul_H E)
    simpa [infPlaceAuxU, infPlaceAuxW] using h
  calc infU E = infU E * (infPlaceAuxH E : Func E) * ((infPlaceAuxH E : Func E))⁻¹ := by
        rw [mul_assoc, mul_inv_cancel₀ (infPlaceAuxH_ne_zero E), mul_one]
    _ = (infW E) ^ 2 * ((infPlaceAuxH E : Func E))⁻¹ := by rw [hrel]
    _ = infW E * (infW E * ((infPlaceAuxH E : Func E))⁻¹) := by ring

/-! ## The dichotomy -/

/-- **Non-units of the local ring at infinity are multiples of `infW E`.**  If `f ∈ infPlace E`
regarded as an element of the local ring at `O` is not a unit, then `f = infW E * g` for some
`g ∈ infPlace E`. -/
theorem infPlace_nonunit_eq_infW_mul (L : Type*) [Field L] (E : WeierstrassCurve L) [E.IsElliptic]
    (f : Work.MotC2.Func E) (hf : f ∈ Work.MotC2.infPlace E)
    (h : ¬ ∃ g : Work.MotC2.Func E, g ∈ Work.MotC2.infPlace E ∧ f * g = 1) :
    ∃ g : Work.MotC2.Func E, g ∈ Work.MotC2.infPlace E ∧ f = Work.MotC2.infW E * g := by
  -- write `f = a / b` with `a, b` in the chart ring and `b` outside the maximal ideal
  obtain ⟨a, b, hb, hab⟩ := (InfAux.infPlace_mem_iff E f).mp hf
  have hb0 : (b : Func E) ≠ 0 := by
    intro h0
    have h : b = 0 := Subtype.ext h0
    rw [h] at hb
    exact hb (Ideal.zero_mem _)
  -- `h` is a unit of the local ring, so `u = w · (w · h⁻¹)` with both factors in `infPlace E`
  have hHinv : ((infPlaceAuxH E : Func E))⁻¹ ∈ infPlace E :=
    InfAux.inv_mem_infPlace_of_notMem E (infPlaceAuxH_notMem E)
  have hWu : infW E * ((infPlaceAuxH E : Func E))⁻¹ ∈ infPlace E :=
    Subalgebra.mul_mem _ (InfAux.mem_infPlace_of_mem E (infPlaceAuxW E)) hHinv
  -- the numerator lies in the maximal ideal: otherwise `f` would be a unit
  have ha_mem : a ∈ InfAux.infIdealR E := by
    by_cases ha : a = 0
    · rw [ha]; exact Ideal.zero_mem _
    · by_contra hnot
      have ha0 : (a : Func E) ≠ 0 := fun h0 => ha (Subtype.ext h0)
      refine h ⟨(b : Func E) * ((a : Func E))⁻¹, ?_, ?_⟩
      · exact Subalgebra.mul_mem _ (InfAux.mem_infPlace_of_mem E b)
          (InfAux.inv_mem_infPlace_of_notMem E hnot)
      · rw [← mul_assoc, hab, mul_inv_cancel₀ ha0]
  -- write the numerator as `α u + β w`
  obtain ⟨α, β, hαβ⟩ := (InfAux.mem_infIdealR_iff' E a).mp ha_mem
  refine ⟨((α : Func E) * (infW E * ((infPlaceAuxH E : Func E))⁻¹) + (β : Func E)) *
    ((b : Func E))⁻¹, ?_, ?_⟩
  · refine Subalgebra.mul_mem _ (Subalgebra.add_mem _
      (Subalgebra.mul_mem _ (InfAux.mem_infPlace_of_mem E α) hWu)
      (InfAux.mem_infPlace_of_mem E β)) (InfAux.inv_mem_infPlace_of_notMem E hb)
  · have key : (a : Func E) = infW E * ((α : Func E) * (infW E * ((infPlaceAuxH E : Func E))⁻¹) +
        (β : Func E)) := by
      have hαβ' : (α : Func E) * infU E + (β : Func E) * infW E = (a : Func E) := by
        have h := congrArg (fun z : infCoordRing E => (z : Func E)) hαβ
        simpa [infPlaceAuxU, infPlaceAuxW] using h
      rw [← hαβ', infPlaceAuxU_eq_W_mul E]
      first | refl_ring1 | ring
    calc f = f * (b : Func E) * ((b : Func E))⁻¹ := by
          rw [mul_assoc, mul_inv_cancel₀ hb0, mul_one]
      _ = (a : Func E) * ((b : Func E))⁻¹ := by rw [hab]
      _ = (infW E * ((α : Func E) * (infW E * ((infPlaceAuxH E : Func E))⁻¹) + (β : Func E))) *
            ((b : Func E))⁻¹ := by rw [key]
      _ = infW E * (((α : Func E) * (infW E * ((infPlaceAuxH E : Func E))⁻¹) + (β : Func E)) *
            ((b : Func E))⁻¹) := by ring

end Work.MotC2
