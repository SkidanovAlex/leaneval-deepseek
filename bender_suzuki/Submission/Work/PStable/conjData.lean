/-
Feit--Thompson odd order drive: `Work.PStable.conjData`.

Plumbing for the `p`-stability reduction `Work.PStable.pstable_minimal_normal`: an elementary
abelian `p`-subgroup `M` of a finite group `G` is a `ZMod p`-module, and conjugation gives a
representation of `G` on it.  We record the elementary facts:

* `instModuleAdditiveSubgroup` : the canonical `ZMod p`-module structure on `Additive ↥M` when
  `M` has exponent `p`;
* `conjRep` : the conjugation representation of `G` on `Additive ↥M` (for `M` normal);
* `conjRep_apply` : its value on a basis vector;
* `conjRep_eq_one_iff` : its kernel is the centralizer `C_G(M)`;
* `conjRep_sub_one_sq_eq_zero` : if `[[M,A],A] = 1` then every `a ∈ A` acts quadratically.
-/
import Mathlib
import Submission.Work.HallHigman.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

open scoped IsMulCommutative commutatorElement

namespace Work.PStable

/-- An abelian group of exponent `p` carries the canonical `ZMod p`-module structure. -/
instance instModuleAdditiveSubgroup {G : Type*} [Group G] (M : Subgroup G) [IsMulCommutative ↥M]
    {p : ℕ} [Fact (∀ x : ↥M, x ^ p = 1)] : Module (ZMod p) (Additive ↥M) :=
  AddCommGroup.zmodModule (fun x => (Fact.out : ∀ y : ↥M, y ^ p = 1) x)

/-- The conjugation representation of `G` on a normal subgroup `M` of exponent `p`. -/
noncomputable def conjRep {G : Type*} [Group G] (M : Subgroup G) [M.Normal]
    [IsMulCommutative ↥M] {p : ℕ} [Fact (∀ x : ↥M, x ^ p = 1)] :
    G →* Module.End (ZMod p) (Additive ↥M) where
  toFun g := (AddEquiv.toLinearEquiv (MulEquiv.toAdditive (MulAut.conjNormal g))
      (fun c x => ZMod.map_smul _ c x)).toLinearMap
  map_one' := by ext x; simp [MulAut.conjNormal]
  map_mul' := by intro a b; ext x; simp [mul_assoc]

@[simp] lemma conjRep_apply {G : Type*} [Group G] (M : Subgroup G) [M.Normal]
    [IsMulCommutative ↥M] {p : ℕ} [Fact (∀ x : ↥M, x ^ p = 1)] (g : G) (m : ↥M) :
    conjRep (p := p) M g (Additive.ofMul m) = Additive.ofMul (MulAut.conjNormal g m) := rfl

end Work.PStable
