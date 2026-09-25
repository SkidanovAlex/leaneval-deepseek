import Mathlib.FieldTheory.KrullTopology
import Mathlib.NumberTheory.NumberField.Basic
import Lake.Toml
import Lake.Util.Message
import Lean
import Submission.NK.NUV2.neukirch_uchida_of_chaptersV2_0
import Submission.NK.NUV2.lc_all0
import Submission.NK.NUV2.frob_all
import Submission.NK.NUV2.residuals_two0
import Submission.NK.NUV2.chebotarev_all0
import Submission.NK.NUV2.kernelCondition_all
import Submission.NK.CFTLib.fundamentalClassElement

namespace Submission

/-- **The Neukirch–Uchida theorem** (Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*,
Thm 12.2.1): a topological isomorphism of absolute Galois groups of number fields is induced by a
unique field isomorphism of the separable closures carrying one base field onto the other.

Assembled from the chapters of `Submission/NK/NUV2/`: the local correspondence (`lc_all0`), the
Frobenius correspondence (`frob_all`), the two residual inputs (`residuals_two0`) and Čebotarev
(`chebotarev_all0`), with the global fundamental class `NK.CFTLib.fundamentalClassElement` and the
kernel condition `NK.NUV2.kernelCondition_all`. -/
theorem neukirch_uchida {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
    [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂'] [IsSepClosure K₁ K₁']
    [IsSepClosure K₂ K₂'] (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (he : IsHomeomorph ϕ) :
    ∃! σ : K₂' ≃+* K₁', (algebraMap K₂ K₂').range.map σ.toRingHom = (algebraMap K₁ K₁').range ∧
      ∀ g : Gal(K₁'/K₁), ϕ g = σ.trans (g.toRingEquiv.trans σ.symm) := by
  have hKC : NK.NUV2.KCAll := fun K _ _ Q => NK.NUV2.kernelCondition_all K Q
  have hFC := NK.CFTLib.fundamentalClassElement
  exact NK.NUV2.neukirch_uchida_of_chaptersV2_0 (NK.NUV2.lc_all0 hFC hKC) (NK.NUV2.frob_all hKC)
    (NK.NUV2.residuals_two0 hFC hKC) (NK.NUV2.chebotarev_all0 hFC) ϕ he

end Submission
