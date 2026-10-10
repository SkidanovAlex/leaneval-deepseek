import Submission.Work.MotC5N3.RulingX2.GamCert.Defs4
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

theorem idR_4 (a b g : K) :
    E_ (K := K) a b g * (E_ (K := K) a b g * Slice.fhat4 a b g)
      = Eq_4 (K := K) a b g * P1_ (K := K) a b g
        + At_4 (K := K) a b g + Bt_4 (K := K) a b g * X0_ (K := K) := by
  dsimp only [E_, c1_, c0_, At_4, Bt_4, Eq_4, Z_4, Y_4, W0_4, W1_4, Dh_, Rh_, P_, P1_, X0_, Slice.fhat4]
  simp only [map_add, map_mul, map_pow, map_sub, map_one, map_zero, map_ofNat]
  refl_ring1 (mod := 5)

theorem idA_4 (a b g : K) :
    E_ (K := K) a b g * At_4 (K := K) a b g + W0_4 (K := K) a b g * P_ (K := K) a b g
      = Z_4 (K := K) a b g * Rh_ (K := K) a b g
        - Y_4 (K := K) a b g * (Dh_ (K := K) a b g * c0_ (K := K) a b g) := by
  dsimp only [E_, c1_, c0_, At_4, Bt_4, Eq_4, Z_4, Y_4, W0_4, W1_4, Dh_, Rh_, P_, P1_, X0_, Slice.fhat4]
  simp only [map_add, map_mul, map_pow, map_sub, map_one, map_zero, map_ofNat]
  refl_ring1 (mod := 5)

theorem idB_4 (a b g : K) :
    E_ (K := K) a b g * Bt_4 (K := K) a b g + W1_4 (K := K) a b g * P_ (K := K) a b g
      = Z_4 (K := K) a b g * Dh_ (K := K) a b g
        + Y_4 (K := K) a b g * (E_ (K := K) a b g * Rh_ (K := K) a b g - c1_ (K := K) a b g * Dh_ (K := K) a b g) := by
  dsimp only [E_, c1_, c0_, At_4, Bt_4, Eq_4, Z_4, Y_4, W0_4, W1_4, Dh_, Rh_, P_, P1_, X0_, Slice.fhat4]
  simp only [map_add, map_mul, map_pow, map_sub, map_one, map_zero, map_ofNat]
  refl_ring1 (mod := 5)

end Work.MotC5N3.RulingX2.GamCert.Idents
