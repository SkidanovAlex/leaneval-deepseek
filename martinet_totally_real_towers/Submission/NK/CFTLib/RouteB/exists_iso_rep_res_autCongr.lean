import Mathlib
import Submission.NK.CFTLib.RouteB.plan
import Submission.NK.GlobalCFT.GlobalCFT
import Submission.NK.CFTLib.RouteB.IdeleCongr.PlaceCongr
import Submission.NK.CFTLib.RouteB.IdeleCongr.localFieldCongr
import Submission.NK.CFTLib.RouteB.IdeleCongr.ideleCongr
import Submission.NK.CFTLib.RouteB.IdeleCongr.Assembly

namespace NK.CFTLib.RouteB

theorem exists_iso_rep_res_autCongr {K L L' : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Field L'] [NumberField L'] [Algebra K L] [Algebra K L']
    (e : L ≃ₐ[K] L') :
    Nonempty (Rep.res (AlgEquiv.autCongr e).toMonoidHom (NK.GlobalCFT.IdeleClassGroup.rep K L') ≅
      NK.GlobalCFT.IdeleClassGroup.rep K L) := by
  obtain ⟨Φ, hmap, hunits, hcont⟩ := IdeleCongr.localFieldCongr e
  obtain ⟨Ψ, hprin, hsmul⟩ := IdeleCongr.ideleCongr e Φ hmap hunits hcont
  obtain ⟨Ψc, hsmulc⟩ := IdeleCongr.exists_classGroupCongr e Ψ hprin hsmul
  exact IdeleCongr.rep_iso_of_classGroupCongr e Ψc hsmulc

end NK.CFTLib.RouteB
