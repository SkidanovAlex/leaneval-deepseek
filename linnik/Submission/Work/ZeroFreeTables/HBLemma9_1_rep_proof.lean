import Mathlib
import Submission.Work.ZeroFreeTables.Rep9.Assembly

namespace Work.ZeroFreeTables

theorem HBLemma9_1_rep_proof : Work.ZeroFreeTables.HBLemma9_1_rep :=
  Work.ZeroFreeTables.Rep9.HBLemma9_1_rep_of_cases
    (fun a K ε ha hK hε => Work.ZeroFreeTables.Rep9.generic_case_prim ha hK hε)
    (fun a K ε ha hK hε => Work.ZeroFreeTables.Rep9.order3_case_prim ha hK hε)
    (fun a K ε ha hK hε => Work.ZeroFreeTables.Rep9.order2_case_prim ha hK hε)

end Work.ZeroFreeTables
