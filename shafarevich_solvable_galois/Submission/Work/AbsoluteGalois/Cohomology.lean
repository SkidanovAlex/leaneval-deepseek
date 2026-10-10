import Mathlib.Tactic.Group
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Submission.Work.GroupCohomology.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.AbsoluteGalois

open scoped Classical

set_option warn.classDefReducibility false

noncomputable section

section KernelAction

variable {G Q : Type*} [Group G] [Group Q]

/-- Conjugation by `g : G` inside the kernel of `π` (which is normal in `G`). -/
def conjKernelMul (π : G →* Q) (g : G) (a : π.ker) : π.ker :=
  ⟨g * (a : G) * g⁻¹, by
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, a.2, mul_one, mul_inv_cancel]⟩

lemma conjKernelMul_one (π : G →* Q) (g : G) : conjKernelMul π g 1 = 1 :=
  Subtype.ext (by simp [conjKernelMul])

lemma conjKernelMul_mul (π : G →* Q) (g : G) (a b : π.ker) :
    conjKernelMul π g (a * b) = conjKernelMul π g a * conjKernelMul π g b :=
  Subtype.ext (by simp only [conjKernelMul, Subgroup.coe_mk, Subgroup.coe_mul]; group)

lemma conjKernelMul_mul_eq (π : G →* Q) (g h : G) (a : π.ker) :
    conjKernelMul π (g * h) a = conjKernelMul π g (conjKernelMul π h a) :=
  Subtype.ext (by simp only [conjKernelMul, Subgroup.coe_mk, mul_inv_rev]; group)

lemma conjKernelMul_one_left (π : G →* Q) (a : π.ker) : conjKernelMul π 1 a = a :=
  Subtype.ext (by simp [conjKernelMul])

/-- Conjugation by an element of the kernel is trivial when the kernel is abelian. -/
lemma conjKernelMul_of_mem_ker (π : G →* Q) (hcomm : ∀ a b : π.ker, a * b = b * a)
    (u a : π.ker) : conjKernelMul π (u : G) a = a := by
  refine Subtype.ext ?_
  have h : u * a * u⁻¹ = a := by rw [hcomm u a, mul_assoc, mul_inv_cancel, mul_one]
  exact congrArg (fun x : π.ker => (x : G)) h

/-- **The conjugation action of `Q` on the kernel of a surjection with abelian kernel.**  Given a
normalized section `s` of `π` (so `π (s q) = q` and `s 1 = 1`) and the commutativity of `ker π`,
conjugation by `s q` defines a `DistribMulAction` of `Q` on `Additive (ker π)`.  It is
independent of the choice of the section because inner conjugation by an element of the abelian
kernel is trivial. -/
def kernelAction (π : G →* Q) (s : Q → G) (hs : ∀ q, π (s q) = q) (h1 : s 1 = 1)
    (hcomm : ∀ a b : π.ker, a * b = b * a) : DistribMulAction Q (Additive π.ker) where
  smul q a := Additive.ofMul (conjKernelMul π (s q) (Additive.toMul a))
  one_smul a := by
    show Additive.ofMul (conjKernelMul π (s 1) (Additive.toMul a)) = a
    rw [h1, conjKernelMul_one_left]
    exact ofMul_toMul a
  mul_smul q r a := by
    set u : π.ker := ⟨(s q * s r)⁻¹ * s (q * r), by
      rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, hs q, hs r, hs (q * r)]
      simp⟩ with hu
    have key : s (q * r) = s q * s r * (u : G) := by
      rw [hu]
      simp only [Subgroup.coe_mk]
      group
    show Additive.ofMul (conjKernelMul π (s (q * r)) (Additive.toMul a)) =
      Additive.ofMul (conjKernelMul π (s q) (conjKernelMul π (s r) (Additive.toMul a)))
    rw [key, conjKernelMul_mul_eq, conjKernelMul_mul_eq, conjKernelMul_of_mem_ker π hcomm u]
  smul_zero q := by
    show Additive.ofMul (conjKernelMul π (s q) (Additive.toMul (0 : Additive π.ker))) = 0
    simp [conjKernelMul_one]
  smul_add q a b := by
    show Additive.ofMul (conjKernelMul π (s q) (Additive.toMul (a + b))) =
      Additive.ofMul (conjKernelMul π (s q) (Additive.toMul a)) +
        Additive.ofMul (conjKernelMul π (s q) (Additive.toMul b))
    simp only [toMul_add, conjKernelMul_mul, ofMul_mul]

end KernelAction

section SectionCocycle

variable {G Q : Type*} [Group G] [Group Q] (π : G →* Q) (s : Q → G)

/-- The `2`-cochain attached to a set-theoretic section `s` of `π`:
`c (q, r) = s q * s r * (s (q * r))⁻¹`, viewed in the (abelian) kernel of `π`.  Its class in
`H²(Q, ker π)` is independent of the section and is the extension class of `π`. -/
def sectionCocycle (hs : ∀ q, π (s q) = q) : Q × Q → Additive π.ker :=
  fun p => Additive.ofMul ⟨s p.1 * s p.2 * (s (p.1 * p.2))⁻¹, by
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, hs p.1, hs p.2, hs (p.1 * p.2)]
    simp⟩

end SectionCocycle

end

end Work.AbsoluteGalois
