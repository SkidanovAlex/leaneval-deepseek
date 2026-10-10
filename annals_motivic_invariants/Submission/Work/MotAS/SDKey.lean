import Submission.Work.MotAS.SDFin
import Submission.Work.MotAS.SDReord
import Submission.Work.Reflect.PolyId

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Work.MotAS.SDStage

variable {R : Type*} [CommRing R]

theorem key (a b g w : R) (z : Fin 5 → R) (h5 : (5 : R) = 0) (hw : w ^ 5 = w + g) :
    -(a)^(5:ℕ)*(b)^(5:ℕ) * ((Xk w z 4)^(5:ℕ)) + -(a)^(5:ℕ)*(b)^(5:ℕ) * ((Xk w z 3)^(5:ℕ)) + (2*(a)^(7:ℕ)*(b)^(3:ℕ)+-(a)^(2:ℕ)*(b)^(8:ℕ)) * (Xk w z 2*(Xk w z 3)^(3:ℕ)*Xk w z 4) + (-(a)^(9:ℕ)*b+3*(a)^(4:ℕ)*(b)^(6:ℕ)) * ((Xk w z 2)^(2:ℕ)*Xk w z 3*(Xk w z 4)^(2:ℕ)) + -(a)^(5:ℕ)*(b)^(5:ℕ) * ((Xk w z 2)^(5:ℕ)) + (-3*(a)^(6:ℕ)*(b)^(4:ℕ)+-a*(b)^(9:ℕ)) * (Xk w z 1*(Xk w z 3)^(2:ℕ)*(Xk w z 4)^(2:ℕ)) + ((a)^(8:ℕ)*(b)^(2:ℕ)+2*(a)^(3:ℕ)*(b)^(7:ℕ)) * (Xk w z 1*Xk w z 2*(Xk w z 4)^(3:ℕ)) + (2*(a)^(7:ℕ)*(b)^(3:ℕ)+-(a)^(2:ℕ)*(b)^(8:ℕ)) * (Xk w z 1*(Xk w z 2)^(3:ℕ)*Xk w z 3) + (-(a)^(9:ℕ)*b+3*(a)^(4:ℕ)*(b)^(6:ℕ)) * ((Xk w z 1)^(2:ℕ)*Xk w z 2*(Xk w z 3)^(2:ℕ)) + (-3*(a)^(6:ℕ)*(b)^(4:ℕ)+-a*(b)^(9:ℕ)) * ((Xk w z 1)^(2:ℕ)*(Xk w z 2)^(2:ℕ)*Xk w z 4) + ((a)^(8:ℕ)*(b)^(2:ℕ)+2*(a)^(3:ℕ)*(b)^(7:ℕ)) * ((Xk w z 1)^(3:ℕ)*Xk w z 3*Xk w z 4) + -(a)^(5:ℕ)*(b)^(5:ℕ) * ((Xk w z 1)^(5:ℕ)) + (2*(a)^(7:ℕ)*(b)^(3:ℕ)+-(a)^(2:ℕ)*(b)^(8:ℕ)) * (Xk w z 0*Xk w z 3*(Xk w z 4)^(3:ℕ)) + (-3*(a)^(6:ℕ)*(b)^(4:ℕ)+-a*(b)^(9:ℕ)) * (Xk w z 0*(Xk w z 2)^(2:ℕ)*(Xk w z 3)^(2:ℕ)) + ((a)^(8:ℕ)*(b)^(2:ℕ)+2*(a)^(3:ℕ)*(b)^(7:ℕ)) * (Xk w z 0*(Xk w z 2)^(3:ℕ)*Xk w z 4) + ((a)^(8:ℕ)*(b)^(2:ℕ)+2*(a)^(3:ℕ)*(b)^(7:ℕ)) * (Xk w z 0*Xk w z 1*(Xk w z 3)^(3:ℕ)) + (((a)^(10:ℕ)+-6*(a)^(5:ℕ)*(b)^(5:ℕ))+-(b)^(10:ℕ)) * (Xk w z 0*Xk w z 1*Xk w z 2*Xk w z 3*Xk w z 4) + (-(a)^(9:ℕ)*b+3*(a)^(4:ℕ)*(b)^(6:ℕ)) * (Xk w z 0*(Xk w z 1)^(2:ℕ)*(Xk w z 4)^(2:ℕ)) + (2*(a)^(7:ℕ)*(b)^(3:ℕ)+-(a)^(2:ℕ)*(b)^(8:ℕ)) * (Xk w z 0*(Xk w z 1)^(3:ℕ)*Xk w z 2) + (-(a)^(9:ℕ)*b+3*(a)^(4:ℕ)*(b)^(6:ℕ)) * ((Xk w z 0)^(2:ℕ)*(Xk w z 3)^(2:ℕ)*Xk w z 4) + (-3*(a)^(6:ℕ)*(b)^(4:ℕ)+-a*(b)^(9:ℕ)) * ((Xk w z 0)^(2:ℕ)*Xk w z 2*(Xk w z 4)^(2:ℕ)) + (-(a)^(9:ℕ)*b+3*(a)^(4:ℕ)*(b)^(6:ℕ)) * ((Xk w z 0)^(2:ℕ)*Xk w z 1*(Xk w z 2)^(2:ℕ)) + (-3*(a)^(6:ℕ)*(b)^(4:ℕ)+-a*(b)^(9:ℕ)) * ((Xk w z 0)^(2:ℕ)*(Xk w z 1)^(2:ℕ)*Xk w z 3) + ((a)^(8:ℕ)*(b)^(2:ℕ)+2*(a)^(3:ℕ)*(b)^(7:ℕ)) * ((Xk w z 0)^(3:ℕ)*Xk w z 2*Xk w z 3) + (2*(a)^(7:ℕ)*(b)^(3:ℕ)+-(a)^(2:ℕ)*(b)^(8:ℕ)) * ((Xk w z 0)^(3:ℕ)*Xk w z 1*Xk w z 4) + -(a)^(5:ℕ)*(b)^(5:ℕ) * ((Xk w z 0)^(5:ℕ)) = Work.MotAS.kleinSecDualAS a b g z := by
  rw [sdmon0, sdmon1, sdmon2, sdmon3, sdmon4, sdmon5, sdmon6, sdmon7, sdmon8, sdmon9, sdmon10, sdmon11, sdmon12, sdmon13, sdmon14, sdmon15, sdmon16, sdmon17, sdmon18, sdmon19, sdmon20, sdmon21, sdmon22, sdmon23, sdmon24, sdmon25]
  rw [split_0, split_1, split_2, split_3, split_4, split_5, split_6, split_7, split_8, split_9, split_10, split_11, split_12, split_13, split_14, split_15, split_16, split_17, split_18, split_19, split_20, split_21, split_22, split_23, split_24, split_25]
  rw [reord]
  rw [Lm_agg]
  rw [piece_0, piece_1, piece_2, piece_3, piece_4, piece_5, piece_6, piece_7, piece_8, piece_9, piece_10, piece_11, piece_12, piece_13, piece_14, piece_15, piece_16, piece_17, piece_18, piece_19, piece_20, piece_21, piece_22, piece_23, piece_24, piece_25, piece_26, piece_27, piece_28, piece_29, piece_30, piece_31, piece_32, piece_33, piece_34, piece_35, piece_36, piece_37, piece_38, piece_39, piece_40, piece_41, piece_42, piece_43, piece_44, piece_45, piece_46, piece_47, piece_48, piece_49, piece_50, piece_51, piece_52, piece_53, piece_54, piece_55, piece_56, piece_57, piece_58, piece_59, piece_60, piece_61, piece_62, piece_63, piece_64, piece_65, piece_66, piece_67, piece_68, piece_69, piece_70, piece_71, piece_72, piece_73, piece_74, piece_75, piece_76, piece_77, piece_78, piece_79, piece_80, piece_81, piece_82, piece_83, piece_84, piece_85, piece_86, piece_87, piece_88, piece_89, piece_90, piece_91, piece_92, piece_93, piece_94, piece_95, piece_96, piece_97, piece_98, piece_99, piece_100, piece_101, piece_102, piece_103, piece_104, piece_105, piece_106, piece_107, piece_108, piece_109, piece_110, piece_111, piece_112, piece_113, piece_114, piece_115, piece_116, piece_117, piece_118, piece_119, piece_120, piece_121, piece_122, piece_123, piece_124, piece_125]
  rw [show w ^ (5:ℕ) - w - g = 0 from by rw [hw]; ring]
  rw [h5]
  rw [kleinSecDualAS_collect]
  refl_ring1

end Work.MotAS.SDStage
