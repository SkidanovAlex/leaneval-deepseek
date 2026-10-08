import Mathlib
import Submission.Work.PStable.conjData

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

open scoped IsMulCommutative commutatorElement

namespace Work.PStable

lemma conjRep_eq_one_iff {G : Type*} [Group G] (M : Subgroup G) [M.Normal]
    [IsMulCommutative ↥M] {p : ℕ} [Fact (∀ x : ↥M, x ^ p = 1)] (g : G) :
    conjRep (p := p) M g = 1 ↔ g ∈ Subgroup.centralizer (M : Set G) := by
  constructor
  · -- if `g` acts trivially, then it commutes with every element of `M`
    intro h
    rw [Subgroup.mem_centralizer_iff]
    intro m hm
    have h1 := DFunLike.congr_fun h (Additive.ofMul (⟨m, hm⟩ : ↥M))
    have h1' : Additive.ofMul (MulAut.conjNormal g ⟨m, hm⟩) = Additive.ofMul ⟨m, hm⟩ := by
      simpa using h1
    have h2 : MulAut.conjNormal g ⟨m, hm⟩ = ⟨m, hm⟩ := Additive.ofMul.injective h1'
    have h3 : (g : G) * (m : G) * g⁻¹ = (m : G) := by
      have := congrArg (fun z : ↥M => (z : G)) h2
      simpa [MulAut.conjNormal_apply] using this
    rw [mul_inv_eq_iff_eq_mul] at h3
    exact h3.symm
  · -- if `g` centralizes `M`, then conjugation by `g` is the identity on `M`
    intro h
    rw [Subgroup.mem_centralizer_iff] at h
    ext x
    have key : ∀ m : ↥M, conjRep (p := p) M g (Additive.ofMul m) = Additive.ofMul m := by
      intro m
      rw [conjRep_apply]
      congr 1
      apply Subtype.ext
      rw [MulAut.conjNormal_apply, mul_inv_eq_iff_eq_mul]
      exact (h m m.2).symm
    have hx : x = Additive.ofMul (Additive.toMul x) := rfl
    rw [hx, key (Additive.toMul x), Module.End.one_apply]

end Work.PStable
