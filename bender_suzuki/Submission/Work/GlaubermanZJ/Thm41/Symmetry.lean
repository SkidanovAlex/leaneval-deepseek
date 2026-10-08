import Mathlib
import Submission.Work.GlaubermanZJ.Thm41.PComm

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Symmetry of the iterated commutator on an abelian normal subgroup

Let `G` be a group, `C ⊴ G` a normal **abelian** subgroup and `A ≤ G` an abelian subgroup.
Then for `x ∈ C` and `b, c ∈ A` the two iterated (Glauberman) commutators `[[x,c],b]` and
`[[x,b],c]` agree.

The point is that the operators `δ_a(y) = [y,a]` on the abelian group `C` commute: `δ_a` is a
homomorphism `C → C` with `δ_a(y) = y⁻¹·y^a`, and `(y^a)^b = y^{ab}` where `ab = ba` because `A`
is abelian; in the abelian group `C` the two expressions `(x^c)⁻¹x(x^b)⁻¹x^{cb}` and
`(x^b)⁻¹x(x^c)⁻¹x^{bc}` therefore coincide.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped commutatorElement

namespace Work.GlaubermanZJ

variable {G : Type*} [Group G]

/-- Two elements of a commutative subgroup commute. -/
theorem mul_comm_of_mem {H : Subgroup G} (hH : IsMulCommutative H) {a b : G}
    (ha : a ∈ H) (hb : b ∈ H) : a * b = b * a := by
  have h := isMulCommutative_iff.mp hH ⟨a, ha⟩ ⟨b, hb⟩
  simpa using congrArg Subtype.val h

/-- **Symmetry of the iterated commutator.**  If `C ⊴ G` is abelian and `A` is abelian, then
for `x ∈ C` and `b, c ∈ A` one has `[[x,c],b] = [[x,b],c]` (Glauberman's commutator). -/
theorem pcomm_pcomm_comm {C A : Subgroup G} (hCn : C.Normal) (hC : IsMulCommutative C)
    (hA : IsMulCommutative A) {x b c : G} (hx : x ∈ C) (hb : b ∈ A) (hc : c ∈ A) :
    pcomm (pcomm x c) b = pcomm (pcomm x b) c := by
  have hAc : ∀ p ∈ A, ∀ q ∈ A, p * q = q * p := fun p hp q hq => mul_comm_of_mem hA hp hq
  have hCc : ∀ p ∈ C, ∀ q ∈ C, p * q = q * p := fun p hp q hq => mul_comm_of_mem hC hp hq
  -- membership of the conjugate elements
  have hY : c⁻¹ * x * c ∈ C := hCn.conj_mem' x hx c
  have hZ : b⁻¹ * x * b ∈ C := hCn.conj_mem' x hx b
  have hW : b⁻¹ * (c⁻¹ * x * c) * b ∈ C := hCn.conj_mem' _ hY b
  have hW' : c⁻¹ * (b⁻¹ * x * b) * c ∈ C := hCn.conj_mem' _ hZ c
  -- the two `pcomm`s written in terms of conjugates
  have hxc : pcomm x c = x⁻¹ * (c⁻¹ * x * c) := by simp only [pcomm]; group
  have hxb : pcomm x b = x⁻¹ * (b⁻¹ * x * b) := by simp only [pcomm]; group
  have hL : pcomm (pcomm x c) b
      = (c⁻¹ * x * c)⁻¹ * x * (b⁻¹ * x * b)⁻¹ * (b⁻¹ * (c⁻¹ * x * c) * b) := by
    rw [hxc]
    simp only [pcomm]
    group
  have hR : pcomm (pcomm x b) c
      = (b⁻¹ * x * b)⁻¹ * x * (c⁻¹ * x * c)⁻¹ * (c⁻¹ * (b⁻¹ * x * b) * c) := by
    rw [hxb]
    simp only [pcomm]
    group
  -- the two conjugate elements `x^{cb}` and `x^{bc}` agree
  have hcb : b * c = c * b := hAc b hb c hc
  have hWW : b⁻¹ * (c⁻¹ * x * c) * b = c⁻¹ * (b⁻¹ * x * b) * c := by
    calc b⁻¹ * (c⁻¹ * x * c) * b = (c * b)⁻¹ * x * (c * b) := by group
      _ = (b * c)⁻¹ * x * (b * c) := by rw [hcb]
      _ = c⁻¹ * (b⁻¹ * x * b) * c := by group
  rw [hL, hR, hWW]
  -- reorder inside the abelian group `C`
  have hxZ : x * (b⁻¹ * x * b)⁻¹ = (b⁻¹ * x * b)⁻¹ * x := hCc x hx _ (C.inv_mem hZ)
  have hxY : x * (c⁻¹ * x * c)⁻¹ = (c⁻¹ * x * c)⁻¹ * x := hCc x hx _ (C.inv_mem hY)
  have hYZ : (c⁻¹ * x * c)⁻¹ * (b⁻¹ * x * b)⁻¹
      = (b⁻¹ * x * b)⁻¹ * (c⁻¹ * x * c)⁻¹ := hCc _ (C.inv_mem hY) _ (C.inv_mem hZ)
  have key1 : (c⁻¹ * x * c)⁻¹ * x * (b⁻¹ * x * b)⁻¹ * (c⁻¹ * (b⁻¹ * x * b) * c)
      = ((b⁻¹ * x * b)⁻¹ * (c⁻¹ * x * c)⁻¹) * (x * (c⁻¹ * (b⁻¹ * x * b) * c)) := by
    calc (c⁻¹ * x * c)⁻¹ * x * (b⁻¹ * x * b)⁻¹ * (c⁻¹ * (b⁻¹ * x * b) * c)
        = (c⁻¹ * x * c)⁻¹ * (x * (b⁻¹ * x * b)⁻¹) * (c⁻¹ * (b⁻¹ * x * b) * c) := by group
      _ = (c⁻¹ * x * c)⁻¹ * ((b⁻¹ * x * b)⁻¹ * x) * (c⁻¹ * (b⁻¹ * x * b) * c) := by
            rw [hxZ]
      _ = (c⁻¹ * x * c)⁻¹ * (b⁻¹ * x * b)⁻¹ * x * (c⁻¹ * (b⁻¹ * x * b) * c) := by group
      _ = (b⁻¹ * x * b)⁻¹ * (c⁻¹ * x * c)⁻¹ * x * (c⁻¹ * (b⁻¹ * x * b) * c) := by
            rw [hYZ]
      _ = ((b⁻¹ * x * b)⁻¹ * (c⁻¹ * x * c)⁻¹) * (x * (c⁻¹ * (b⁻¹ * x * b) * c)) := by group
  have key2 : (b⁻¹ * x * b)⁻¹ * x * (c⁻¹ * x * c)⁻¹ * (c⁻¹ * (b⁻¹ * x * b) * c)
      = ((b⁻¹ * x * b)⁻¹ * (c⁻¹ * x * c)⁻¹) * (x * (c⁻¹ * (b⁻¹ * x * b) * c)) := by
    calc (b⁻¹ * x * b)⁻¹ * x * (c⁻¹ * x * c)⁻¹ * (c⁻¹ * (b⁻¹ * x * b) * c)
        = (b⁻¹ * x * b)⁻¹ * (x * (c⁻¹ * x * c)⁻¹) * (c⁻¹ * (b⁻¹ * x * b) * c) := by group
      _ = (b⁻¹ * x * b)⁻¹ * ((c⁻¹ * x * c)⁻¹ * x) * (c⁻¹ * (b⁻¹ * x * b) * c) := by
            rw [hxY]
      _ = (b⁻¹ * x * b)⁻¹ * (c⁻¹ * x * c)⁻¹ * x * (c⁻¹ * (b⁻¹ * x * b) * c) := by group
      _ = ((b⁻¹ * x * b)⁻¹ * (c⁻¹ * x * c)⁻¹) * (x * (c⁻¹ * (b⁻¹ * x * b) * c)) := by group
  rw [key1, key2]

end Work.GlaubermanZJ
