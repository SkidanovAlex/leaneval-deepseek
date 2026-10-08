import Mathlib
import Submission.Work.NormalComplement.SectionsV3
import Submission.Work.NormalComplement.Sections
import Submission.Work.NormalComplement.Prelim
import Submission.Work.NormalComplement.section2_prop1_v2
import Submission.Work.NormalComplement.case2_normalizer_le_v3
import Submission.Work.NormalComplement.case2_prop3b_v3
import Submission.Work.NormalComplement.normalizerCond_conj
import Submission.Work.NormalComplement.case1_normalizer_le
import Submission.Work.NormalComplement.prop2b_conj_into_centD
import Submission.Work.NormalComplement.section2_prop1_v3

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.NormalComplement

theorem section2_prop1_nokinv (hFT : Submission.Blueprint.FeitThompsonProp)
    (hBP : Work.NormalComplement.BenderPrelimProp)
    (hC4 : Submission.Blueprint.ChIIFourProp)
    (hP3 : Submission.Blueprint.ChIIFourP3SubnormalProp) :
    Work.NormalComplement.Section2Prop' :=
  section2_prop1_v3 hFT hBP hC4 hP3

end Work.NormalComplement
