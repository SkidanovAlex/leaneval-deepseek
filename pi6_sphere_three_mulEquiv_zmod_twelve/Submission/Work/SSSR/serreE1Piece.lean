import Mathlib
import Submission.Work.Cohomology.SingBridge
import Submission.Work.SSSR.serreE1Defs
import Submission.Work.SSSR.StemsB.Fibrations
import Submission.Work.SSSR.Cohomology.Chains
import Submission.Work.Serre.serreE2dSimplex
import Submission.Work.SSSR.serreE1PieceDefs
import Submission.Work.SSSR.pieceContraction
import Submission.Work.SSSR.pieceHornAcyclic
import Submission.Work.SSSR.pieceBdryHornIso
import Submission.Work.SSSR.pieceConnectingIso
import Submission.Work.SSSR.pieceAlongZero
import Submission.Work.SSSR.sigmaVert_face
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]
