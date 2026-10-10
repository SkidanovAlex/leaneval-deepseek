import Submission.Work.MotC5N3.RulingX2.GamCert.Defs3
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

theorem idR_3 (a b g : K) :
    E_ (K := K) a b g * (E_ (K := K) a b g * Slice.fhat3 a b g)
      = Eq_3 (K := K) a b g * P1_ (K := K) a b g
        + At_3 (K := K) a b g + Bt_3 (K := K) a b g * X0_ (K := K) := by
  dsimp only [E_, c1_, c0_, At_3, Bt_3, Eq_3, Z_3, Y_3, W0_3, W1_3, Dh_, Rh_, P_, P1_, X0_, Slice.fhat3]
  simp only [map_add, map_mul, map_pow, map_sub, map_one, map_zero, map_ofNat]
  refl_ring1 (mod := 5)

theorem idA_3 (a b g : K) :
    E_ (K := K) a b g * At_3 (K := K) a b g + W0_3 (K := K) a b g * P_ (K := K) a b g
      = Z_3 (K := K) a b g * Rh_ (K := K) a b g
        - Y_3 (K := K) a b g * (Dh_ (K := K) a b g * c0_ (K := K) a b g) := by
  dsimp only [E_, c1_, c0_, At_3, Bt_3, Eq_3, Z_3, Y_3, W0_3, W1_3, Dh_, Rh_, P_, P1_, X0_, Slice.fhat3]
  simp only [map_add, map_mul, map_pow, map_sub, map_one, map_zero, map_ofNat]
  refl_ring1 (mod := 5)

theorem idB_3 (a b g : K) :
    E_ (K := K) a b g * Bt_3 (K := K) a b g + W1_3 (K := K) a b g * P_ (K := K) a b g
      = Z_3 (K := K) a b g * Dh_ (K := K) a b g
        + Y_3 (K := K) a b g * (E_ (K := K) a b g * Rh_ (K := K) a b g - c1_ (K := K) a b g * Dh_ (K := K) a b g) := by
  dsimp only [E_, c1_, c0_, At_3, Bt_3, Eq_3, Z_3, Y_3, W0_3, W1_3, Dh_, Rh_, P_, P1_, X0_, Slice.fhat3]
  simp only [map_add, map_mul, map_pow, map_sub, map_one, map_zero, map_ofNat]
  refl_ring1 (mod := 5)

end Work.MotC5N3.RulingX2.GamCert.Idents
