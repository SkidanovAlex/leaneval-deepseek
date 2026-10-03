/-
Shared imports for the weak (hyperbolic) case of the drive.

This module collects, in one place, the workspace facts on which the two helper lemmas
`Work.Drive.unit_log_pole_at_every_point` and `Work.Drive.rigidity_at_pole` (and the assembly
`Work.Drive.weak_case`) rest.  It contains no declarations of its own.
-/
import Submission.Lib.Unif2.Work.Drive.Interfaces
import Submission.Lib.Unif2.Extremal
import Submission.Lib.Unif2.ExtremalExist
import Submission.Lib.Unif2.ExtremalInj
import Submission.Lib.Unif2.GreenConditional
import Submission.Lib.Unif2.Sweep
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.Defs
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.exists_posHarmonic_logPole_dominating
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.extremal_maximizer_proper
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.extremalValue_sharpness
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.rigidity_of_maximizer_decayfree
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.period_interface
import Submission.Lib.Unif2.Work.Potential.logCoefficient_of_pos_harmonic
import Submission.Lib.Unif2.Work.UnitGreen.Defs
