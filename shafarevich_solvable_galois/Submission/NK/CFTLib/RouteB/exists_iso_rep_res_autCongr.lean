import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.Analysis.Normed.Field.Basic
import Submission.NK.CFTLib.RouteB.IdeleCongr.Assembly
import Submission.NK.CFTLib.RouteB.IdeleCongr.ideleCongr
import Submission.NK.CFTLib.RouteB.IdeleCongr.localFieldCongr
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

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
