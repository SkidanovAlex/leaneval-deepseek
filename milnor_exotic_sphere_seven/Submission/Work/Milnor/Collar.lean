import Mathlib
import Submission.Work.Milnor.VBundle
import Submission.Work.Milnor.fibreNorm

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The collar of the disc bundle `Vk k`, and the sphere bundle inside it

`Vk k = (vData k).Glued` is the total space of the rank-`4` real vector bundle `ξ` over `S⁴`
(two copies of `MSpace8 = ℝ⁴ × ℍ` glued along `{x ≠ 0} × ℍ` by the clutching map `vMap k`), and
`Mk k` is its unit sphere bundle (`Work.Milnor.mk_to_vk`).

`Work.Milnor.fibreNorm` provides a *continuous* function on `Vk k` restricting to `p ↦ ‖p.2‖` in
each chart.  Here we fix a choice of it once and for all (`fibreNormFun`) and define the **collar**

`collar k := {p : Vk k | 1/2 < fibreNormFun k p}`,

an open subset of the disc bundle which is a neighbourhood of the sphere bundle and which is
homotopy equivalent to it.  This is the piece that is glued to the complement of a ball in `ℝ⁸`
when the `S³`-bundle `Mk (-2)` is capped off by a disc to produce the closed `8`-manifold
`X = D(ξ) ∪_F D⁸` of `Submission/NOTES.md` §9.3.
-/

namespace Work.Milnor

open scoped Manifold ContDiff Topology

noncomputable section

open Submission.Milnor

/-- A chosen continuous fibre norm on the total space `Vk k` of `ξ`: on the two charts it is
`p ↦ ‖p.2‖`. -/
def fibreNormFun (k : ℤ) : Vk k → ℝ := Classical.choose (fibreNorm k)

@[simp]
theorem fibreNormFun_ιX (k : ℤ) (p : MSpace8) :
    fibreNormFun k ((vData k).ιX p) = ‖p.2‖ :=
  (Classical.choose_spec (fibreNorm k)).1 p

@[simp]
theorem fibreNormFun_ιY (k : ℤ) (p : MSpace8) :
    fibreNormFun k ((vData k).ιY p) = ‖p.2‖ :=
  (Classical.choose_spec (fibreNorm k)).2.1 p

theorem continuous_fibreNormFun (k : ℤ) : Continuous (fibreNormFun k) :=
  (Classical.choose_spec (fibreNorm k)).2.2

/-- The **collar** of the disc bundle: the open neighbourhood `{1/2 < ν}` of the sphere bundle,
where `ν` is the fibre norm. -/
def collar (k : ℤ) : Set (Vk k) := {p | 1/2 < fibreNormFun k p}

@[simp]
theorem mem_collar {k : ℤ} {p : Vk k} : p ∈ collar k ↔ 1/2 < fibreNormFun k p := Iff.rfl

theorem isOpen_collar (k : ℤ) : IsOpen (collar k) :=
  isOpen_lt continuous_const (continuous_fibreNormFun k)

end

end Work.Milnor
