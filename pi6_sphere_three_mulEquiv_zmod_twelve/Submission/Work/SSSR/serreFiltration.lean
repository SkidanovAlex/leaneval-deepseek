import Mathlib
import Submission.Work.SSSR.Packet
import Submission.Work.SSSR.SSetChain
import Submission.Work.SSSR.StemsB.SerreFiltration
import Submission.Work.SSSR.Cohomology.Chains
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]
