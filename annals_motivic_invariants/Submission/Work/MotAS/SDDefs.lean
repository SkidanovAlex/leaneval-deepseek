import Submission.Work.MotAS.ASData
import Submission.Work.MotAS.ASRed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Work.MotAS.SDStage

variable {R : Type*} [CommRing R]

/-- coefficients in `w` of `Σ_j z_j (w+2k)^j`. -/
def Xv (z : Fin 5 → R) : Fin 5 → Fin 5 → R := ![
![z 0, z 1, z 2, z 3, z 4],
  ![(((z 0+2*z 1)+(4*z 2+8*z 3))+16*z 4), ((z 1+4*z 2)+(12*z 3+32*z 4)), ((z 2+6*z 3)+24*z 4), (z 3+8*z 4), z 4],
  ![(((z 0+4*z 1)+(16*z 2+64*z 3))+256*z 4), ((z 1+8*z 2)+(48*z 3+256*z 4)), ((z 2+12*z 3)+96*z 4), (z 3+16*z 4), z 4],
  ![(((z 0+6*z 1)+(36*z 2+216*z 3))+1296*z 4), ((z 1+12*z 2)+(108*z 3+864*z 4)), ((z 2+18*z 3)+216*z 4), (z 3+24*z 4), z 4],
  ![(((z 0+8*z 1)+(64*z 2+512*z 3))+4096*z 4), ((z 1+16*z 2)+(192*z 3+2048*z 4)), ((z 2+24*z 3)+384*z 4), (z 3+32*z 4), z 4]
]

/-- `Σ_j z_j (w+2k)^j`. -/
def Xk (w : R) (z : Fin 5 → R) (k : Fin 5) : R :=
  Xv z k 0 + Xv z k 1 * w + Xv z k 2 * w ^ (2:ℕ) + Xv z k 3 * w ^ (3:ℕ) + Xv z k 4 * w ^ (4:ℕ)

end Work.MotAS.SDStage
