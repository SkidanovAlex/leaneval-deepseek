/-
# ZeroFreeTables — Table8CertExt.lean

The rational certificate for the *remaining eight* printed entries of HB Table 8
(λ₁ = 0.30, 0.32, 0.34, 0.62, 0.64, 0.66, 0.68, 0.696), with the printed values
lowered by `1/1000` as targets.  Together with `Table8Cert` this covers all
twenty-one entries, so `HBTable8` is not needed as a hypothesis.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.CertData
import Submission.Work.ZeroFreeTables.Engine

namespace Work.ZeroFreeTables

theorem Table8CertExt : ∀ r ∈ Work.ZeroFreeTables.t8certRowsExt,
    Work.ZeroFreeTables.cond913 r.2.1 r.2.2.1 r.2.2.2 (Work.ZeroFreeTables.Kaff r.2.1) ∧
    Work.ZeroFreeTables.p913 r.2.1 r.2.2.1 r.2.2.2 (Work.ZeroFreeTables.Kaff r.2.1) < 0 := by
  intro r hr
  fin_cases hr <;>
    (constructor <;> norm_num [cond913, p913, Kaff, P3R, psi13, Kond])

end Work.ZeroFreeTables
