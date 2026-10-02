import Mathlib
import Submission.Work.Milnor.VBundle
import Submission.Work.Milnor.Base
import Submission.Work.Milnor.continuous_baseMap

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The bundle projection `Vk k → S⁴` of the vector bundle over `S⁴`

`Vk k` is the total space of the rank-`4` vector bundle `ξ` over `S⁴`, described by the same
two-chart clutching construction as Milnor's `Mk k`, but with the fibre `S³` replaced by the whole
quaternion line `ℍ` (`Submission.Work.Milnor.VBundleDefs`).  Exactly as for the unit sphere bundle
(`Submission.Milnor.baseMap` in `Submission.Work.Milnor.Base`), the projection to the base `S⁴` is

* `x ↦ x` on the first chart, and
* `x ↦ x/‖x‖²` (`0 ↦ ∞`) on the second chart,

well defined because the two charts are glued by `x ↦ x/‖x‖²` on the base.

This file proves `Work.Milnor.exists_proj`: a continuous map `Vk k → S⁴` with these two
prescribed values on the two chart embeddings.
-/

namespace Work.Milnor

open scoped Manifold ContDiff Topology
open TopologicalSpace Set
open Submission.Milnor

noncomputable section

/-- The underlying map on the disjoint union of two copies of `MSpace8`: the first chart
contributes the finite point `x`, the second chart the inverted point `x/‖x‖²`. -/
def vBaseMapFun (k : ℤ) (a : MSpace8 ⊕ MSpace8) : S4 :=
  Sum.elim (fun p : MSpace8 => (↑p.1 : S4)) (fun p : MSpace8 => baseChart2 p.1) a


lemma vBaseMapFun_inl (k : ℤ) (p : MSpace8) : vBaseMapFun k (Sum.inl p) = (↑p.1 : S4) := rfl

lemma vBaseMapFun_inr (k : ℤ) (p : MSpace8) : vBaseMapFun k (Sum.inr p) = baseChart2 p.1 := rfl

/-- The base map is well defined on the quotient: it respects the gluing relation of `vData k`
(both charts are glued along the inversion `x ↦ x/‖x‖²` *on the base*). -/
lemma vBaseMapFun_respects (k : ℤ) {a b : MSpace8 ⊕ MSpace8}
    (h : (vData k).rel a b) : vBaseMapFun k a = vBaseMapFun k b := by
  rcases a with p | p <;> rcases b with q | q
  · exact congrArg (fun z : MSpace8 => (↑z.1 : S4)) h
  · obtain ⟨hp, hq⟩ := h
    rw [vBaseMapFun_inl, vBaseMapFun_inr]
    have hq' : q.1 = invBase p.1 := by
      have h1 : q.1 = ((vData k).φ p : MSpace8).1 :=
        (congrArg (fun z : MSpace8 => z.1) hq).symm
      rw [h1]
      rfl
    rw [hq', baseChart2_invBase hp]
  · obtain ⟨hq, hp⟩ := h
    rw [vBaseMapFun_inr, vBaseMapFun_inl]
    have hp' : p.1 = invBase q.1 := by
      have h1 : p.1 = ((vData k).φ q : MSpace8).1 :=
        congrArg (fun z : MSpace8 => z.1) hp
      rw [h1]
      rfl
    rw [hp', baseChart2_invBase hq]
  · exact congrArg (fun z : MSpace8 => baseChart2 z.1) h

/-- **The bundle projection** `Vk k → S⁴ = ℝ⁴ ∪ {∞}` of the rank-`4` vector bundle `ξ`. -/
def vBaseMap (k : ℤ) : Vk k → S4 :=
  Quotient.lift (vBaseMapFun k) (fun _a _b h => vBaseMapFun_respects k h)

theorem vBaseMap_ιX (k : ℤ) (p : MSpace8) : vBaseMap k ((vData k).ιX p) = (↑p.1 : S4) := rfl

theorem vBaseMap_ιY (k : ℤ) (p : MSpace8) :
    vBaseMap k ((vData k).ιY p) = baseChart2 p.1 := rfl

/-- The underlying map on `MSpace8 ⊕ MSpace8` is continuous. -/
lemma continuous_vBaseMapFun (k : ℤ) : Continuous (vBaseMapFun k) := by
  have h1 : Continuous (fun p : MSpace8 => (↑p.1 : S4)) :=
    OnePoint.continuous_coe.comp continuous_fst
  have h2 : Continuous (fun p : MSpace8 => baseChart2 p.1) :=
    continuous_baseChart2.comp continuous_fst
  exact Continuous.sumElim h1 h2

theorem continuous_vBaseMap (k : ℤ) : Continuous (vBaseMap k) :=
  (continuous_vBaseMapFun k).quotient_lift (fun _a _b h => vBaseMapFun_respects k h)

theorem exists_proj (k : ℤ) :
    ∃ p : Submission.Milnor.Vk k → Submission.Milnor.S4,
      Continuous p ∧
      (∀ q : Submission.Milnor.MSpace8,
        p ((Submission.Milnor.vData k).ιX q) = (q.1 : Submission.Milnor.S4)) ∧
      (∀ q : Submission.Milnor.MSpace8,
        p ((Submission.Milnor.vData k).ιY q) = Submission.Milnor.baseChart2 q.1) :=
  ⟨vBaseMap k, continuous_vBaseMap k, fun _ => rfl, fun _ => rfl⟩

end

end Work.Milnor
