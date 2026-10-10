import Submission.Work.MotC5N3.RulingX2.GamCert.Defs0
import Submission.Work.MotC5N3.RulingX2.SlicePhi
import Submission.Work.Reflect.PolyId

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Work.MotC5N3.RulingX2.GamCert.Idents

open MvPolynomial
open Work.MotC5N3.RulingX2
open Work.MotC5N3.RulingX2.GamCert

variable {K : Type*} [Field K] [CharP K 5]

theorem idR_0 (a b g : K) :
    E_ (K := K) a b g * (E_ (K := K) a b g * Slice.fhat0 a b g)
      = Eq_0 (K := K) a b g * P1_ (K := K) a b g
        + At_0 (K := K) a b g + Bt_0 (K := K) a b g * X0_ (K := K) := by
  dsimp only [E_, c1_, c0_, At_0, Bt_0, Eq_0, Z_0, Y_0, W0_0, W1_0, Dh_, Rh_, P_, P1_, X0_, Slice.fhat0, Slice.fhat0_p0, Slice.fhat0_p1]
  simp only [map_add, map_mul, map_pow, map_sub, map_one, map_zero, map_ofNat]
  refl_ring1 (mod := 5)

theorem idA_0 (a b g : K) :
    E_ (K := K) a b g * At_0 (K := K) a b g + W0_0 (K := K) a b g * P_ (K := K) a b g
      = Z_0 (K := K) a b g * Rh_ (K := K) a b g
        - Y_0 (K := K) a b g * (Dh_ (K := K) a b g * c0_ (K := K) a b g) := by
  dsimp only [E_, c1_, c0_, At_0, Bt_0, Eq_0, Z_0, Y_0, W0_0, W1_0, Dh_, Rh_, P_, P1_, X0_, Slice.fhat0, Slice.fhat0_p0, Slice.fhat0_p1]
  simp only [map_add, map_mul, map_pow, map_sub, map_one, map_zero, map_ofNat]
  refl_ring1 (mod := 5)

theorem idB_0 (a b g : K) :
    E_ (K := K) a b g * Bt_0 (K := K) a b g + W1_0 (K := K) a b g * P_ (K := K) a b g
      = Z_0 (K := K) a b g * Dh_ (K := K) a b g
        + Y_0 (K := K) a b g * (E_ (K := K) a b g * Rh_ (K := K) a b g - c1_ (K := K) a b g * Dh_ (K := K) a b g) := by
  dsimp only [E_, c1_, c0_, At_0, Bt_0, Eq_0, Z_0, Y_0, W0_0, W1_0, Dh_, Rh_, P_, P1_, X0_, Slice.fhat0, Slice.fhat0_p0, Slice.fhat0_p1]
  simp only [map_add, map_mul, map_pow, map_sub, map_one, map_zero, map_ofNat]
  refl_ring1 (mod := 5)

end Work.MotC5N3.RulingX2.GamCert.Idents
