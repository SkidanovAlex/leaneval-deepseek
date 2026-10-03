import Mathlib
import Submission.Work.ORTorsion.Defs
import Submission.Work.ORTorsion.Grading.Mk_Tm
import Submission.Work.ORTorsion.Grading.Mk_inclDN
import Submission.Work.ORTorsion.Grading.exists_single_smul_mem_range

namespace Work.ORTorsion.Grading

open scoped TensorProduct

/-- The diagonal action of `single (s ^ b) 1` on `V ⊗ D(N)`, embedded in `V ⊗ R`, lies in the
range of `Tm b ∘ inclDN`; consequently its degree-`j` coordinate vanishes unless `j = b`. -/
theorem Mk_single_zpow_smul_inclDN {K : Type*} [Field K] {G : Type*} [Group G] {U : Type*}
    [Ring U] [Algebra K U] (L : TorsionData K G U) {V : Type*} [AddCommGroup V] [Module K V]
    [Module (MonoidAlgebra K G) V] [IsScalarTower K (MonoidAlgebra K G) V]
    {H : Subgroup G} {φ : H →* Multiplicative ℤ} (Lb : LaurentBase K U G L.gen L.D H φ)
    (b j : ℤ) (z : TensorProduct K V ↥(L.D Lb.N)) :
    LaurentBase.Mk Lb j ((MonoidAlgebra.single (Lb.s ^ b) (1 : K) : MonoidAlgebra K H) •
        (LaurentBase.inclDN Lb z))
      = if j = b then LaurentBase.Mk Lb b ((MonoidAlgebra.single (Lb.s ^ b) (1 : K) :
          MonoidAlgebra K H) • (LaurentBase.inclDN Lb z)) else 0 := by
  -- `single (s^b) 1` has degree `b`, so it maps `V ⊗ D(N)` into `Tm b (V ⊗ D(N))`.
  obtain ⟨z', hz'⟩ := exists_single_smul_mem_range L Lb (Lb.s ^ b) z
  rw [deg_zpow Lb.hs_zpow b] at hz'
  rw [hz']
  by_cases h : j = b
  · subst h; simp
  · rw [if_neg h, Mk_Tm, Mk_inclDN, if_neg (sub_ne_zero.mpr h)]

end Work.ORTorsion.Grading
