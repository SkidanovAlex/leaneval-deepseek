import Mathlib
import Submission.Work.ORTorsion.Defs
import Submission.Work.ORTorsion.Grading.coord_left_mul_DN
import Submission.Work.ORTorsion.Grading.Mk_mapSubAlg
import Submission.Work.ORTorsion.Grading.Mk_single_zpow_smul_inclDN
import Submission.Work.ORTorsion.Support.mapSubAlg_degCoeff_mul

namespace Work.ORTorsion.Grading

open scoped TensorProduct

open Work.ORTorsion

open Work.ORTorsion.LaurentBase

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- **The degree-`j` part of the action of the degree-`b` part of `x`.**

On `V ⊗[K] R` the diagonal action of `degPart φ b x` splits according to the grading of `R`: it
acts as the degree-`b` coefficient `degCoeff Lb b x` of `x`, transported to `V ⊗[K] D(N)`, and
carries the degree-`0` part `V ⊗[K] D(N)` to degree exactly `b`. Concretely, writing
`degPart φ b x = mapSubAlg (degCoeff Lb b x) * single (s ^ b) 1` (`mapSubAlg_degCoeff_mul`), the
`K[N]`-part acts degree-wise (`Mk_mapSubAlg`) and the monomial `single (s ^ b) 1` contributes only
in degree `b` (`Mk_single_zpow_smul_inclDN`). -/
theorem Mk_degPart {K : Type*} [Field K] {G : Type*} [Group G] {U : Type*} [Ring U]
    [Algebra K U] (L : TorsionData K G U) {V : Type*} [AddCommGroup V] [Module K V]
    [Module (MonoidAlgebra K G) V] [IsScalarTower K (MonoidAlgebra K G) V]
    {H : Subgroup G} {φ : H →* Multiplicative ℤ} (Lb : LaurentBase K U G L.gen L.D H φ)
    (x : MonoidAlgebra K H) (b j : ℤ) (z : V ⊗[K] ↥(L.D Lb.N)) :
    Mk Lb j ((degPart φ b x) • (inclDN Lb z))
      = if j = b then (LaurentBase.degCoeff Lb b x) •
          (Mk Lb b ((MonoidAlgebra.single (Lb.s ^ b) (1 : K) : MonoidAlgebra K H) •
            (inclDN Lb z)))
        else 0 := by
  -- `degPart φ b x` factors as `mapSubAlg (degCoeff Lb b x) * single (s ^ b) 1`.
  have h16 := Work.ORTorsion.Support.mapSubAlg_degCoeff_mul L Lb b x
  rw [← h16, mul_smul]
  -- The `K[N]`-part acts degree-wise.
  rw [Mk_mapSubAlg L Lb (LaurentBase.degCoeff Lb b x) j
        ((MonoidAlgebra.single (Lb.s ^ b) (1 : K) : MonoidAlgebra K H) • (inclDN Lb z))]
  -- The monomial `single (s ^ b) 1` contributes only in degree `b`.
  rw [Mk_single_zpow_smul_inclDN L Lb b j z]
  by_cases hjb : j = b
  · simp [hjb]
  · simp [hjb]

end Work.ORTorsion.Grading
