import Mathlib
import Submission.Work.LocalFields.Ramification
import Submission.Work.LocalFields.exists_pow_eq_residueFrobenius
import Submission.Work.LocalFields.frobenius_spec
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.LocalFields

theorem exists_generator_mod_inertia {K L : Type*} [Field K] [Field L] [NumberField K]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (v : Work.LocalFields.FinitePrime K) (w : Work.LocalFields.FinitePrime L)
    [hw : w.asIdeal.LiesOver v.asIdeal] :
    ∃ f : ↥(Work.LocalFields.decompositionGroup K w),
      ∀ σ : ↥(Work.LocalFields.decompositionGroup K w),
        ∃ m : ℤ, σ⁻¹ * f ^ m ∈ Work.LocalFields.inertiaSubgroup K w := by
  refine ⟨frobenius v w, fun σ => ?_⟩
  obtain ⟨n, hn⟩ := exists_pow_eq_residueFrobenius v w
    ((ramificationExactSequence v w) (QuotientGroup.mk' (inertiaSubgroup K w) σ))
  refine ⟨(n : ℤ), ?_⟩
  rw [← QuotientGroup.ker_mk' (inertiaSubgroup K w)]
  apply MonoidHom.mem_ker.mpr
  apply (ramificationExactSequence v w).injective
  simp only [map_one, map_mul, map_inv, map_zpow, QuotientGroup.mk'_apply] at hn ⊢
  rw [frobenius_spec, hn, zpow_natCast]
  group

end Work.LocalFields
