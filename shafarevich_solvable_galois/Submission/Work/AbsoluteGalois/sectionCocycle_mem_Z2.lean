import Mathlib.Tactic.Group
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Submission.Work.AbsoluteGalois.Cohomology
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

-- The local instances in the proofs below are needed for instance resolution (`have`/`let`
-- would not register them); the linter's preference for `let` does not apply here.
set_option linter.style.haveILetI false

namespace Work.AbsoluteGalois

variable {G Q : Type*} [Group G] [Group Q]

/-- The action of `q : Q` on `Additive (ker π)` induced by `kernelAction` is conjugation by the
chosen lift `s q`, transported to the multiplicative notation for elements of the kernel. -/
lemma kernelAction_smul_toMul (π : G →* Q) (s : Q → G) (hs : ∀ q, π (s q) = q)
    (h1 : s 1 = 1) (hcomm : ∀ a b : π.ker, a * b = b * a) (q : Q) (a : Additive π.ker) :
    letI : CommGroup π.ker := { (inferInstance : Group π.ker) with mul_comm := hcomm }
    letI := kernelAction π s hs h1 hcomm
    (q • a).toMul = conjKernelMul π (s q) a.toMul := rfl

/-- **The `2`-cocycle identity for the section cocycle**, in multiplicative form: in the abelian
kernel of `π`,
`c (q, r) * c (q * r, t) = (s q) · c (r, t) · (s q)⁻¹ * c (q, r * t)`. -/
lemma sectionCocycle_mul_eq (π : G →* Q) (s : Q → G) (hs : ∀ q, π (s q) = q)
    (h1 : s 1 = 1) (hcomm : ∀ a b : π.ker, a * b = b * a) (q r t : Q) :
    letI : CommGroup π.ker := { (inferInstance : Group π.ker) with mul_comm := hcomm }
    letI := kernelAction π s hs h1 hcomm
    (sectionCocycle π s hs (q, r)).toMul * (sectionCocycle π s hs (q * r, t)).toMul =
      conjKernelMul π (s q) (sectionCocycle π s hs (r, t)).toMul *
        (sectionCocycle π s hs (q, r * t)).toMul := by
  letI : CommGroup π.ker := { (inferInstance : Group π.ker) with mul_comm := hcomm }
  letI : DistribMulAction Q (Additive π.ker) := kernelAction π s hs h1 hcomm
  refine Subtype.ext ?_
  simp only [Subgroup.coe_mul, conjKernelMul, sectionCocycle, toMul_ofMul]
  group

/-- **The section cocycle of an abelian-kernel extension is a `2`-cocycle.**  For a surjection
`π : G →* Q` with abelian kernel and a normalized section `s`, the cochain
`c (q, r) = s q * s r * (s (q * r))⁻¹` satisfies the `Z²`-condition with respect to the
conjugation action `kernelAction` of `Q` on the kernel:
`c (q * r, t) + c (q, r) = q • c (r, t) + c (q, r * t)`. -/
theorem sectionCocycle_mem_Z2 {G Q : Type*} [Group G] [Group Q] (π : G →* Q) (s : Q → G)
    (hs : ∀ q, π (s q) = q) (h1 : s 1 = 1) (hcomm : ∀ a b : π.ker, a * b = b * a) :
    letI : CommGroup π.ker := { (inferInstance : Group π.ker) with mul_comm := hcomm }
    letI := Work.AbsoluteGalois.kernelAction π s hs h1 hcomm
    Work.AbsoluteGalois.sectionCocycle π s hs ∈ Work.GroupCohomology.Z2 Q (Additive π.ker) := by
  letI : CommGroup π.ker := { (inferInstance : Group π.ker) with mul_comm := hcomm }
  letI : DistribMulAction Q (Additive π.ker) := kernelAction π s hs h1 hcomm
  rw [Work.GroupCohomology.mem_Z2_iff]
  intro q r t
  refine Additive.toMul.injective ?_
  rw [toMul_add, toMul_add]
  rw [show (q • sectionCocycle π s hs (r, t)).toMul =
        conjKernelMul π (s q) (sectionCocycle π s hs (r, t)).toMul from rfl,
      hcomm (sectionCocycle π s hs (q * r, t)).toMul (sectionCocycle π s hs (q, r)).toMul]
  refine Subtype.ext ?_
  simp only [Subgroup.coe_mul, conjKernelMul, sectionCocycle, toMul_ofMul]
  group

end Work.AbsoluteGalois
