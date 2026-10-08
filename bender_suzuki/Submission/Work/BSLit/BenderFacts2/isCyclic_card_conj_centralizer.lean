import Mathlib
import Submission.Work.BSLit.BenderFacts2.Facts2Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.BSLit.BenderFacts2

/-- Conjugation by `c` sends `a` to `c * a * c⁻¹`. -/
theorem conj_apply_eq_mul {G : Type*} [Group G] (a c : G) : MulAut.conj c a = c * a * c⁻¹ := by
  simp [MulAut.conj_apply]

/-- Conjugation transports the centraliser: for `a c : G`, the centraliser of `c * a * c⁻¹` is
the conjugate of the centraliser of `a`, so it is cyclic iff the centraliser of `a` is, and it
has the same cardinality. -/
theorem isCyclic_card_conj_centralizer {G : Type*} [Group G] (a c : G) :
    (IsCyclic ↥(Subgroup.centralizer ({a} : Set G)) ↔
      IsCyclic ↥(Subgroup.centralizer ({c * a * c⁻¹} : Set G))) ∧
    Nat.card ↥(Subgroup.centralizer ({c * a * c⁻¹} : Set G))
      = Nat.card ↥(Subgroup.centralizer ({a} : Set G)) := by
  have hmap : (Subgroup.centralizer ({a} : Set G)).map (MulAut.conj c).toMonoidHom
      = Subgroup.centralizer ({c * a * c⁻¹} : Set G) := by
    have h := centralizer_map_mulEquiv (MulAut.conj c) a
    rwa [conj_apply_eq_mul a c] at h
  have hiso : ↥(Subgroup.centralizer ({a} : Set G))
      ≃* ↥(Subgroup.centralizer ({c * a * c⁻¹} : Set G)) :=
    (Subgroup.equivMapOfInjective _ (MulAut.conj c).toMonoidHom
        (MulAut.conj c).injective).trans (MulEquiv.subgroupCongr hmap)
  exact ⟨MulEquiv.isCyclic hiso, (Nat.card_congr hiso.toEquiv).symm⟩

end Work.BSLit.BenderFacts2
