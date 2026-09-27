/-
Shared imports for the weak (hyperbolic) case of the drive.

This module collects, in one place, the workspace facts on which the two helper lemmas
`Work.Drive.unit_log_pole_at_every_point` and `Work.Drive.rigidity_at_pole` (and the assembly
`Work.Drive.weak_case`) rest.  It contains no declarations of its own.
-/
import Submission.Work.Drive.Interfaces
import Submission.Extremal
import Submission.ExtremalExist
import Submission.ExtremalInj
import Submission.GreenConditional
import Submission.Sweep
import Submission.Work.SimplyConnected.ABS.Defs
import Submission.Work.SimplyConnected.ABS.exists_posHarmonic_logPole_dominating
import Submission.Work.SimplyConnected.ABS.extremal_maximizer_proper
import Submission.Work.SimplyConnected.ABS.extremalValue_sharpness
import Submission.Work.SimplyConnected.ABS.rigidity_of_maximizer_decayfree
import Submission.Work.SimplyConnected.ABS.period_interface
import Submission.Work.Potential.logCoefficient_of_pos_harmonic
import Submission.Work.UnitGreen.Defs
