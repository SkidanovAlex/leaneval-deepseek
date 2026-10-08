import Mathlib
import Submission.Work.PStable.conjData

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Conjugation representation of a subgroup normalizing an abelian subgroup

Plumbing used by `Work.ThmF.Prove.step3`: for `M ≤ G` an abelian subgroup of exponent dividing `n`
and `L ≤ N_G(M)`, the conjugation action of `L` on `M` is `ZMod n`-linear, hence defines a
`Representation (ZMod n) ↥L (Additive ↥M)`.
-/

noncomputable section

namespace Work.ThmF.Prove.S3

open Classical
open scoped IsMulCommutative

variable {G : Type*} [Group G]

/-- A `MulAut` of an abelian group of exponent dividing `n` is `ZMod n`-linear. -/
def mulAutToLinAut (M : Subgroup G) [IsMulCommutative ↥M] {n : ℕ}
    [Fact (∀ x : ↥M, x ^ n = 1)] (e : MulAut ↥M) :
    Additive ↥M ≃ₗ[ZMod n] Additive ↥M :=
  AddEquiv.toLinearEquiv (MulEquiv.toAdditive e) (fun c x => ZMod.map_smul _ c x)

/-- **The conjugation representation of `L ≤ N_G(M)`.**  `M` is abelian of exponent dividing `n`;
`L` acts on `↥M` by conjugation, hence on the additive group `Additive ↥M` by `ZMod n`-linear
automorphisms. -/
noncomputable def conjRepOfLe (L M : Subgroup G) (hLN : L ≤ Subgroup.normalizer (M : Set G))
    [IsMulCommutative ↥M] {n : ℕ} [Fact (∀ x : ↥M, x ^ n = 1)] :
    Representation (ZMod n) ↥L (Additive ↥M) where
  toFun l := (mulAutToLinAut M
    ((Subgroup.normalizerMonoidHom M).comp (Subgroup.inclusion hLN) l)).toLinearMap
  map_one' := by
    ext x
    simp [mulAutToLinAut]
  map_mul' := by
    intro a b
    ext x
    simp [mulAutToLinAut, Module.End.mul_apply]

/-- Evaluation of `conjRepOfLe` on a vector. -/
@[simp] theorem conjRepOfLe_apply (L M : Subgroup G)
    (hLN : L ≤ Subgroup.normalizer (M : Set G)) [IsMulCommutative ↥M] {n : ℕ}
    [Fact (∀ x : ↥M, x ^ n = 1)] (l : ↥L) (m : ↥M) :
    conjRepOfLe (n := n) L M hLN l (Additive.ofMul m)
      = Additive.ofMul (⟨(l : G) * (m : G) * (l : G)⁻¹, ((hLN l.2) (m : G)).mp m.2⟩ : ↥M) := by
  simp only [conjRepOfLe, mulAutToLinAut, MonoidHom.comp_apply]
  rfl

end Work.ThmF.Prove.S3
