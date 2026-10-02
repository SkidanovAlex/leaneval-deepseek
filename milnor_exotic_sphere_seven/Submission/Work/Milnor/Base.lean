import Mathlib
import Submission.Work.Milnor.Clutch

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The bundle projection `Mk k → S⁴`

Milnor's `M_k` is the total space of an `S³`-bundle over `S⁴`.  In the two-chart description of
`Submission.Work.Milnor.Clutch`, `Mk k` is the quotient of two copies of `ℝ⁴ × S³` glued along
`{x ≠ 0}` by `(x, y) ~ (x/‖x‖², u^{-k} y u⁻¹)`.  On the first factor the base coordinate of the
two charts is identified by the inversion `x ↦ x/‖x‖²`, so the base is
`S⁴ = ℝ⁴ ∪ {∞} = OnePoint (EuclideanSpace ℝ (Fin 4))`:
* the first chart contributes the finite points `x ↦ (x : S⁴)`;
* the second chart contributes the inverted points `x ↦ x/‖x‖²`, with `0 ↦ ∞`.

The map is well defined because the two contributions agree on the overlap (`invBase` is an
involution away from `0`).  This file defines that base map `baseMap k : Mk k → S⁴`, together with
the elementary descriptions of its values on the two charts.  The remaining properties (continuity,
surjectivity, local triviality with fibre `S³`) are left to subsequent lemmas.
-/

open scoped Manifold ContDiff Topology
open TopologicalSpace Set

namespace Submission.Milnor

noncomputable section

/-- The base of the bundle `Mk k → S⁴`, namely `S⁴ = ℝ⁴ ∪ {∞}`. -/
abbrev S4 : Type := OnePoint (EuclideanSpace ℝ (Fin 4))

/-- The contribution of the *second* chart to the base map: the inversion
`x ↦ x/‖x‖²`, viewed as a map to `S⁴ = ℝ⁴ ∪ {∞}` (sending `0` to `∞`). -/
def baseChart2 (x : EuclideanSpace ℝ (Fin 4)) : S4 :=
  if x = 0 then OnePoint.infty else ↑(invBase x)

lemma baseChart2_zero : baseChart2 0 = OnePoint.infty := by simp [baseChart2]

/-- The inversion is an involution away from the origin, so the two chart contributions to the
base map agree on the gluing region. -/
lemma baseChart2_invBase {x : EuclideanSpace ℝ (Fin 4)} (hx : x ≠ 0) :
    baseChart2 (invBase x) = (↑x : S4) := by
  have h : invBase x ≠ 0 := invBase_ne_zero hx
  rw [baseChart2, if_neg h, invBase_invBase hx]

/-- The underlying map on the disjoint union of two copies of `MSpace`: the first chart
contributes the finite point `x`, the second chart the inverted point `x/‖x‖²`. -/
def baseMapFun (k : ℤ) (a : MSpace ⊕ MSpace) : S4 :=
  Sum.elim (fun p : MSpace => (↑p.1 : S4)) (fun p : MSpace => baseChart2 p.1) a

lemma baseMapFun_inl (k : ℤ) (p : MSpace) : baseMapFun k (Sum.inl p) = (↑p.1 : S4) := rfl

lemma baseMapFun_inr (k : ℤ) (p : MSpace) : baseMapFun k (Sum.inr p) = baseChart2 p.1 := rfl

/-- The base map is well defined on the quotient: it respects the gluing relation. -/
lemma baseMapFun_respects (k : ℤ) {a b : MSpace ⊕ MSpace}
    (h : (clutchData k).rel a b) : baseMapFun k a = baseMapFun k b := by
  rcases a with p | p <;> rcases b with q | q
  · exact congrArg (fun z : MSpace => (↑z.1 : S4)) h
  · obtain ⟨hp, hq⟩ := h
    rw [baseMapFun_inl, baseMapFun_inr]
    have hq' : q.1 = invBase p.1 := by
      have h1 : q.1 = (clutchMap k p).1 := (congrArg (fun z : MSpace => z.1) hq).symm
      rw [h1]
      rfl
    rw [hq', baseChart2_invBase hp]
  · obtain ⟨hq, hp⟩ := h
    rw [baseMapFun_inr, baseMapFun_inl]
    have hp' : p.1 = invBase q.1 := by
      have h1 : p.1 = (clutchMap k q).1 := congrArg (fun z : MSpace => z.1) hp
      rw [h1]
      rfl
    rw [hp', baseChart2_invBase hq]
  · exact congrArg (fun z : MSpace => baseChart2 z.1) h

/-- **The base map** `Mk k → S⁴ = ℝ⁴ ∪ {∞}` of Milnor's bundle. -/
def baseMap (k : ℤ) : Mk k → S4 :=
  Quotient.lift (baseMapFun k) (fun a b h => baseMapFun_respects k h)

theorem baseMap_ιX (k : ℤ) (p : MSpace) : baseMap k ((clutchData k).ιX p) = (↑p.1 : S4) := rfl

theorem baseMap_ιY (k : ℤ) (p : MSpace) :
    baseMap k ((clutchData k).ιY p) = baseChart2 p.1 := rfl

/-- A point of the fibre `S³`. -/
def oneQS3 : QS3 := ⟨(1 : Quaternion ℝ), by simp⟩

/-- The base map is surjective: every point of `S⁴` occurs. -/
theorem baseMap_surjective (k : ℤ) : Function.Surjective (baseMap k) := by
  intro y
  rcases y with _ | y
  · exact ⟨(clutchData k).ιY (0, oneQS3), by rw [baseMap_ιY, baseChart2_zero]; rfl⟩
  · exact ⟨(clutchData k).ιX (y, oneQS3), by rw [baseMap_ιX]; rfl⟩

end

end Submission.Milnor
