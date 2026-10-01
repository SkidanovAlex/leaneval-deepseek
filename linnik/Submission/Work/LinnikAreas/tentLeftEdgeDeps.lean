import Submission.Commons.NumberTheory.Linnik.tentMellin_bridge_scale
import Submission.Commons.Analysis.Integral.integrable_log_lorentz
import Submission.Commons.Analysis.Integral.integral_log_lorentz_le

/-!
Re-export hub for the `ζ` left-edge tent integral.  It exposes the tent kernel
`Commons.NumberTheory.Linnik.tentPhi` together with the Lorentz-type integral estimates
`Commons.Analysis.Integral.integrable_log_lorentz` and
`Commons.Analysis.Integral.integral_log_lorentz_le`, so that lemmas under `Work/LinnikAreas`
can list a single `Submission.Work.*` module in their `depends_on`.
-/
