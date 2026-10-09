import Mathlib
import Submission.Work.SSGRoute.pTorsion_classLevelLimit
import Submission.Work.SSGRoute.phi0_defs
import Submission.Work.SSGRoute.phi1_class_level
import Submission.Work.SSGRoute.phi1_level_index
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.E9b

/-- **The `p`-torsion of `A = colim_L H²(Gal(L/k), C_L)` is `ℤ/p`.**  There is an additive
bijection from the `p`-torsion subgroup of the class-group colimit onto `ZMod p`
(`pTorsion_classLevelLimit` gives `Nat.card = p`). -/
theorem chi_pTor_classLevelLimit (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω] :
    ∃ χ : ↥(pTor p (ClassLevelLimit (k := k) (K := K) (Ω := Ω))) →+ ZMod p,
      Function.Bijective χ := by
  have hcard : Nat.card ↥(pTor p (ClassLevelLimit (k := k) (K := K) (Ω := Ω))) = p :=
    Work.SSGRoute.pTorsion_classLevelLimit p k K Ω
  have hZp : Nat.card (ZMod p) = p := by
    simp [Nat.card_eq_fintype_card, ZMod.card]
  refine ⟨(addEquivOfPrimeCardEq hcard hZp).toAddMonoidHom, ?_⟩
  exact (addEquivOfPrimeCardEq hcard hZp).bijective

end Work.SSGRoute.E9b
