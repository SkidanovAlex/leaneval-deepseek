import Mathlib
import Submission.Work.CohomologicalShrinking.Models
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.CohomologicalShrinking

/-- The augmentation functional `𝔽_p[G] → 𝔽_p`, `y ↦ ∑_g y.coeff g`, implemented as a
`𝔽_p`-linear map.  Elements of the augmentation ideal `I_G` lie in its kernel. -/
theorem augIdeal_coeff_sum (p : ℕ) (G : Type*) [Group G] [Fintype G]
    (y : MonoidAlgebra (ZMod p) G) (hy : y ∈ Work.CohomologicalShrinking.augIdeal p G) :
    ∑ g : G, y.coeff g = 0 := by
  let f : MonoidAlgebra (ZMod p) G →ₗ[ZMod p] ZMod p :=
    { toFun := fun y => ∑ g : G, y.coeff g
      map_add' := by
        intro x y
        simp only [MonoidAlgebra.coeff_add, Finsupp.add_apply, Finset.sum_add_distrib]
      map_smul' := by
        intro c x
        simp only [MonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul]
        rw [Finset.mul_sum]
        simp }
  have hker : Work.CohomologicalShrinking.augIdeal p G ≤ LinearMap.ker f := by
    rw [Work.CohomologicalShrinking.augIdeal, Submodule.span_le]
    rintro x ⟨g, rfl⟩
    show f (MonoidAlgebra.single g (1 : ZMod p) - 1) = 0
    change (∑ h : G, (MonoidAlgebra.single g (1 : ZMod p) - 1).coeff h) = 0
    simp only [MonoidAlgebra.coeff_sub, Finsupp.sub_apply, Finset.sum_sub_distrib]
    simp [MonoidAlgebra.one_def]
  have := hker hy
  exact this

end Work.CohomologicalShrinking
