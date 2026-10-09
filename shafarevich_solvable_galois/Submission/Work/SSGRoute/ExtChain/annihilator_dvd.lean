import Mathlib
import Submission.Work.SSGRoute.PTDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ExtChain

/-- If `v ≠ 0` is annihilated by the prime `p` (viewed in the coefficient ring `Coeff = ULift ℤ`),
then every coefficient `c` annihilating `v` is divisible by `p`.  Equivalently: a nonzero vector
killed by `p` has additive order exactly `p`, so its annihilator in `ℤ` is `(p)`.

The scalar action of `Coeff = ULift ℤ` agrees definitionally with the canonical `ℤ`-action on the
abelian group `V` (`ULift.smulLeft`), so the statement is the classical one about `addOrderOf`. -/
theorem annihilator_dvd {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module SSGRoute.PTExt.Coeff V] {v : V} (hv : v ≠ 0)
    (hpv : (p : SSGRoute.PTExt.Coeff) • v = 0) {c : SSGRoute.PTExt.Coeff} (hc : c • v = 0) :
    (p : ℤ) ∣ c.down := by
  have hcv : c.down • v = 0 := hc
  have hord : addOrderOf v = p := by
    apply addOrderOf_eq_prime
    · rw [← natCast_zsmul]
      exact hpv
    · exact hv
  rw [← hord]
  exact (addOrderOf_dvd_iff_zsmul_eq_zero (x := v) (i := c.down)).mpr hcv

end Work.SSGRoute.ExtChain
