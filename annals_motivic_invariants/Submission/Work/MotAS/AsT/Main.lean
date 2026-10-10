import Submission.Work.MotAS.AsT.Pat0
import Submission.Work.MotAS.AsT.Pat1
import Submission.Work.MotAS.AsT.Pat2
import Submission.Work.MotAS.AsT.Pat3
import Submission.Work.MotAS.AsT.Pat4
import Submission.Work.MotAS.AsT.Pat5
import Submission.Work.MotAS.AsT.Pat6
import Submission.Work.MotAS.AsT.Pat7
import Submission.Work.MotAS.AsT.Pat8
import Submission.Work.MotAS.AsT.Pat9
import Submission.Work.MotAS.AsT.Pat10
import Submission.Work.MotAS.AsT.Pat11
import Submission.Work.MotAS.AsT.Pat12
import Submission.Work.MotAS.AsT.Pat13
import Submission.Work.MotAS.AsT.Pat14
import Submission.Work.MotAS.AsT.Pat15
import Submission.Work.MotAS.AsT.Pat16
import Submission.Work.MotAS.AsT.Pat17
import Submission.Work.MotAS.AsT.Pat18
import Submission.Work.MotAS.AsT.Pat19
import Submission.Work.MotAS.AsT.Pat20
import Submission.Work.MotAS.AsT.Pat21
import Submission.Work.MotAS.AsT.Pat22
import Submission.Work.MotAS.AsT.Pat23
import Submission.Work.MotAS.AsT.Pat24
import Submission.Work.MotAS.AsT.Pat25
import Submission.Work.MotAS.AsT.Grp0
import Submission.Work.MotAS.AsT.Grp1
import Submission.Work.MotAS.AsT.Grp2
import Submission.Work.MotAS.AsT.Grp3
import Submission.Work.MotAS.AsT.Grp4
import Submission.Work.MotAS.AsT.Grp5
import Submission.Work.MotAS.AsT.Grp6
import Submission.Work.MotAS.AsT.Grp7
import Submission.Work.MotAS.AsT.Grp8
import Submission.Work.MotAS.AsT.Grp9
import Submission.Work.MotAS.AsT.Grp10
import Submission.Work.Reflect.PolyId

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000

namespace Work.MotAS.AsT

variable {R : Type*} [CommRing R]

/-- **The secant quintic in AS Galois coordinates.**  For `x_i = AX w y i` the quintic `s`
reduces to `kleinSecAS`. -/
theorem kleinSec_AX (a b g w : R) (h5 : (5:R) = 0) (hw : w ^(5:ℕ) = w + g) (y : Fin 5 → R) :
    Work.MotK.kleinSec a b (fun i => AX w y i) = Work.MotAS.kleinSecAS a b g y := by
  have hp0 := pat0 g w hw y
  have hp1 := pat1 g w hw y
  have hp2 := pat2 g w hw y
  have hp3 := pat3 g w hw y
  have hp4 := pat4 g w hw y
  have hp5 := pat5 g w hw y
  have hp6 := pat6 g w hw y
  have hp7 := pat7 g w hw y
  have hp8 := pat8 g w hw y
  have hp9 := pat9 g w hw y
  have hp10 := pat10 g w hw y
  have hp11 := pat11 g w hw y
  have hp12 := pat12 g w hw y
  have hp13 := pat13 g w hw y
  have hp14 := pat14 g w hw y
  have hp15 := pat15 g w hw y
  have hp16 := pat16 g w hw y
  have hp17 := pat17 g w hw y
  have hp18 := pat18 g w hw y
  have hp19 := pat19 g w hw y
  have hp20 := pat20 g w hw y
  have hp21 := pat21 g w hw y
  have hp22 := pat22 g w hw y
  have hp23 := pat23 g w hw y
  have hp24 := pat24 g w hw y
  have hp25 := pat25 g w hw y
  have hg0 := glem0 a b g w h5 hw y
  have hg1 := glem1 a b g w h5 hw y
  have hg2 := glem2 a b g w h5 hw y
  have hg3 := glem3 a b g w h5 hw y
  have hg4 := glem4 a b g w h5 hw y
  have hg5 := glem5 a b g w h5 hw y
  have hg6 := glem6 a b g w h5 hw y
  have hg7 := glem7 a b g w h5 hw y
  have hg8 := glem8 a b g w h5 hw y
  have hg9 := glem9 a b g w h5 hw y
  have hg10 := glem10 a b g w h5 hw y
  simp only [Work.MotK.kleinSec, mul_assoc, hp0, hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8, hp9, hp10, hp11, hp12, hp13, hp14, hp15, hp16, hp17, hp18, hp19, hp20, hp21, hp22, hp23, hp24, hp25]
  rw [show (16*(a^(5:ℕ)*(b^(5:ℕ)*(∑ l, K0_4 g y l * w ^ (l:ℕ))))) - (2*(a^(3:ℕ)*(b^(7:ℕ)*(∑ l, K1_4 g y l * w ^ (l:ℕ))))) - (2*(a^(3:ℕ)*(b^(7:ℕ)*(∑ l, K2_4 g y l * w ^ (l:ℕ))))) - (2*(a^(3:ℕ)*(b^(7:ℕ)*(∑ l, K3_4 g y l * w ^ (l:ℕ))))) - (2*(a^(3:ℕ)*(b^(7:ℕ)*(∑ l, K4_4 g y l * w ^ (l:ℕ))))) - (2*(a^(3:ℕ)*(b^(7:ℕ)*(∑ l, K5_4 g y l * w ^ (l:ℕ))))) - (2*(a^(7:ℕ)*(b^(3:ℕ)*(∑ l, K6_4 g y l * w ^ (l:ℕ))))) - (2*(a^(7:ℕ)*(b^(3:ℕ)*(∑ l, K7_4 g y l * w ^ (l:ℕ))))) - (2*(a^(7:ℕ)*(b^(3:ℕ)*(∑ l, K8_4 g y l * w ^ (l:ℕ))))) - (2*(a^(7:ℕ)*(b^(3:ℕ)*(∑ l, K9_4 g y l * w ^ (l:ℕ))))) - (2*(a^(7:ℕ)*(b^(3:ℕ)*(∑ l, K10_4 g y l * w ^ (l:ℕ))))) - (3*(a^(4:ℕ)*(b^(6:ℕ)*(∑ l, K11_4 g y l * w ^ (l:ℕ))))) - (3*(a^(4:ℕ)*(b^(6:ℕ)*(∑ l, K12_4 g y l * w ^ (l:ℕ))))) - (3*(a^(4:ℕ)*(b^(6:ℕ)*(∑ l, K13_4 g y l * w ^ (l:ℕ))))) - (3*(a^(4:ℕ)*(b^(6:ℕ)*(∑ l, K14_4 g y l * w ^ (l:ℕ))))) - (3*(a^(4:ℕ)*(b^(6:ℕ)*(∑ l, K15_4 g y l * w ^ (l:ℕ))))) + (3*(a^(6:ℕ)*(b^(4:ℕ)*(∑ l, K16_4 g y l * w ^ (l:ℕ))))) + (3*(a^(6:ℕ)*(b^(4:ℕ)*(∑ l, K17_4 g y l * w ^ (l:ℕ))))) + (3*(a^(6:ℕ)*(b^(4:ℕ)*(∑ l, K18_4 g y l * w ^ (l:ℕ))))) + (3*(a^(6:ℕ)*(b^(4:ℕ)*(∑ l, K19_4 g y l * w ^ (l:ℕ))))) + (3*(a^(6:ℕ)*(b^(4:ℕ)*(∑ l, K20_4 g y l * w ^ (l:ℕ))))) + (a*(b^(9:ℕ)*(∑ l, K16_4 g y l * w ^ (l:ℕ)))) + (a*(b^(9:ℕ)*(∑ l, K17_4 g y l * w ^ (l:ℕ)))) + (a*(b^(9:ℕ)*(∑ l, K18_4 g y l * w ^ (l:ℕ)))) + (a*(b^(9:ℕ)*(∑ l, K19_4 g y l * w ^ (l:ℕ)))) + (a*(b^(9:ℕ)*(∑ l, K20_4 g y l * w ^ (l:ℕ)))) - (a^(10:ℕ)*(∑ l, K0_4 g y l * w ^ (l:ℕ))) + (a^(2:ℕ)*(b^(8:ℕ)*(∑ l, K6_4 g y l * w ^ (l:ℕ)))) + (a^(2:ℕ)*(b^(8:ℕ)*(∑ l, K7_4 g y l * w ^ (l:ℕ)))) + (a^(2:ℕ)*(b^(8:ℕ)*(∑ l, K8_4 g y l * w ^ (l:ℕ)))) + (a^(2:ℕ)*(b^(8:ℕ)*(∑ l, K9_4 g y l * w ^ (l:ℕ)))) + (a^(2:ℕ)*(b^(8:ℕ)*(∑ l, K10_4 g y l * w ^ (l:ℕ)))) - (a^(5:ℕ)*(b^(5:ℕ)*(∑ l, K21_4 g y l * w ^ (l:ℕ)))) - (a^(5:ℕ)*(b^(5:ℕ)*(∑ l, K22_4 g y l * w ^ (l:ℕ)))) - (a^(5:ℕ)*(b^(5:ℕ)*(∑ l, K23_4 g y l * w ^ (l:ℕ)))) - (a^(5:ℕ)*(b^(5:ℕ)*(∑ l, K24_4 g y l * w ^ (l:ℕ)))) - (a^(5:ℕ)*(b^(5:ℕ)*(∑ l, K25_4 g y l * w ^ (l:ℕ)))) - (a^(8:ℕ)*(b^(2:ℕ)*(∑ l, K1_4 g y l * w ^ (l:ℕ)))) - (a^(8:ℕ)*(b^(2:ℕ)*(∑ l, K2_4 g y l * w ^ (l:ℕ)))) - (a^(8:ℕ)*(b^(2:ℕ)*(∑ l, K3_4 g y l * w ^ (l:ℕ)))) - (a^(8:ℕ)*(b^(2:ℕ)*(∑ l, K4_4 g y l * w ^ (l:ℕ)))) - (a^(8:ℕ)*(b^(2:ℕ)*(∑ l, K5_4 g y l * w ^ (l:ℕ)))) + (a^(9:ℕ)*(b*(∑ l, K11_4 g y l * w ^ (l:ℕ)))) + (a^(9:ℕ)*(b*(∑ l, K12_4 g y l * w ^ (l:ℕ)))) + (a^(9:ℕ)*(b*(∑ l, K13_4 g y l * w ^ (l:ℕ)))) + (a^(9:ℕ)*(b*(∑ l, K14_4 g y l * w ^ (l:ℕ)))) + (a^(9:ℕ)*(b*(∑ l, K15_4 g y l * w ^ (l:ℕ)))) + (b^(10:ℕ)*(∑ l, K0_4 g y l * w ^ (l:ℕ))) = ((16*(a^(5:ℕ)*(b^(5:ℕ)*(∑ l, K0_4 g y l * w ^ (l:ℕ))))) - (a^(5:ℕ)*(b^(5:ℕ)*(∑ l, K21_4 g y l * w ^ (l:ℕ)))) - (a^(5:ℕ)*(b^(5:ℕ)*(∑ l, K22_4 g y l * w ^ (l:ℕ)))) - (a^(5:ℕ)*(b^(5:ℕ)*(∑ l, K23_4 g y l * w ^ (l:ℕ)))) - (a^(5:ℕ)*(b^(5:ℕ)*(∑ l, K24_4 g y l * w ^ (l:ℕ)))) - (a^(5:ℕ)*(b^(5:ℕ)*(∑ l, K25_4 g y l * w ^ (l:ℕ))))) + (-(2*(a^(3:ℕ)*(b^(7:ℕ)*(∑ l, K1_4 g y l * w ^ (l:ℕ))))) - (2*(a^(3:ℕ)*(b^(7:ℕ)*(∑ l, K2_4 g y l * w ^ (l:ℕ))))) - (2*(a^(3:ℕ)*(b^(7:ℕ)*(∑ l, K3_4 g y l * w ^ (l:ℕ))))) - (2*(a^(3:ℕ)*(b^(7:ℕ)*(∑ l, K4_4 g y l * w ^ (l:ℕ))))) - (2*(a^(3:ℕ)*(b^(7:ℕ)*(∑ l, K5_4 g y l * w ^ (l:ℕ)))))) + (-(2*(a^(7:ℕ)*(b^(3:ℕ)*(∑ l, K6_4 g y l * w ^ (l:ℕ))))) - (2*(a^(7:ℕ)*(b^(3:ℕ)*(∑ l, K7_4 g y l * w ^ (l:ℕ))))) - (2*(a^(7:ℕ)*(b^(3:ℕ)*(∑ l, K8_4 g y l * w ^ (l:ℕ))))) - (2*(a^(7:ℕ)*(b^(3:ℕ)*(∑ l, K9_4 g y l * w ^ (l:ℕ))))) - (2*(a^(7:ℕ)*(b^(3:ℕ)*(∑ l, K10_4 g y l * w ^ (l:ℕ)))))) + (-(3*(a^(4:ℕ)*(b^(6:ℕ)*(∑ l, K11_4 g y l * w ^ (l:ℕ))))) - (3*(a^(4:ℕ)*(b^(6:ℕ)*(∑ l, K12_4 g y l * w ^ (l:ℕ))))) - (3*(a^(4:ℕ)*(b^(6:ℕ)*(∑ l, K13_4 g y l * w ^ (l:ℕ))))) - (3*(a^(4:ℕ)*(b^(6:ℕ)*(∑ l, K14_4 g y l * w ^ (l:ℕ))))) - (3*(a^(4:ℕ)*(b^(6:ℕ)*(∑ l, K15_4 g y l * w ^ (l:ℕ)))))) + ((3*(a^(6:ℕ)*(b^(4:ℕ)*(∑ l, K16_4 g y l * w ^ (l:ℕ))))) + (3*(a^(6:ℕ)*(b^(4:ℕ)*(∑ l, K17_4 g y l * w ^ (l:ℕ))))) + (3*(a^(6:ℕ)*(b^(4:ℕ)*(∑ l, K18_4 g y l * w ^ (l:ℕ))))) + (3*(a^(6:ℕ)*(b^(4:ℕ)*(∑ l, K19_4 g y l * w ^ (l:ℕ))))) + (3*(a^(6:ℕ)*(b^(4:ℕ)*(∑ l, K20_4 g y l * w ^ (l:ℕ)))))) + ((a*(b^(9:ℕ)*(∑ l, K16_4 g y l * w ^ (l:ℕ)))) + (a*(b^(9:ℕ)*(∑ l, K17_4 g y l * w ^ (l:ℕ)))) + (a*(b^(9:ℕ)*(∑ l, K18_4 g y l * w ^ (l:ℕ)))) + (a*(b^(9:ℕ)*(∑ l, K19_4 g y l * w ^ (l:ℕ)))) + (a*(b^(9:ℕ)*(∑ l, K20_4 g y l * w ^ (l:ℕ))))) + (-(a^(10:ℕ)*(∑ l, K0_4 g y l * w ^ (l:ℕ)))) + ((a^(2:ℕ)*(b^(8:ℕ)*(∑ l, K6_4 g y l * w ^ (l:ℕ)))) + (a^(2:ℕ)*(b^(8:ℕ)*(∑ l, K7_4 g y l * w ^ (l:ℕ)))) + (a^(2:ℕ)*(b^(8:ℕ)*(∑ l, K8_4 g y l * w ^ (l:ℕ)))) + (a^(2:ℕ)*(b^(8:ℕ)*(∑ l, K9_4 g y l * w ^ (l:ℕ)))) + (a^(2:ℕ)*(b^(8:ℕ)*(∑ l, K10_4 g y l * w ^ (l:ℕ))))) + (-(a^(8:ℕ)*(b^(2:ℕ)*(∑ l, K1_4 g y l * w ^ (l:ℕ)))) - (a^(8:ℕ)*(b^(2:ℕ)*(∑ l, K2_4 g y l * w ^ (l:ℕ)))) - (a^(8:ℕ)*(b^(2:ℕ)*(∑ l, K3_4 g y l * w ^ (l:ℕ)))) - (a^(8:ℕ)*(b^(2:ℕ)*(∑ l, K4_4 g y l * w ^ (l:ℕ)))) - (a^(8:ℕ)*(b^(2:ℕ)*(∑ l, K5_4 g y l * w ^ (l:ℕ))))) + ((a^(9:ℕ)*(b*(∑ l, K11_4 g y l * w ^ (l:ℕ)))) + (a^(9:ℕ)*(b*(∑ l, K12_4 g y l * w ^ (l:ℕ)))) + (a^(9:ℕ)*(b*(∑ l, K13_4 g y l * w ^ (l:ℕ)))) + (a^(9:ℕ)*(b*(∑ l, K14_4 g y l * w ^ (l:ℕ)))) + (a^(9:ℕ)*(b*(∑ l, K15_4 g y l * w ^ (l:ℕ))))) + ((b^(10:ℕ)*(∑ l, K0_4 g y l * w ^ (l:ℕ)))) from by abel]
  rw [hg0, hg1, hg2, hg3, hg4, hg5, hg6, hg7, hg8, hg9, hg10]
  simp only [Work.MotAS.kleinSecAS]
  linear_combination (norm := refl_ring1 (mod := 5))

end Work.MotAS.AsT
