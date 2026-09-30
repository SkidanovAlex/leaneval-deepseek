import Mathlib
import Submission.Work.Kunneth.EZAWDefs
import Submission.Work.Kunneth.ModelContr
import Submission.Work.Kunneth.modelH_comm
import Submission.Work.Kunneth.stdModelContr

/-!
# The model complexes of the Eilenberg–Zilber theorem are acyclic in positive degrees

`Work.Kunneth.tMod p q = C_*(Δ[p]) ⊗_ℤ C_*(Δ[q])` is the `(p,q)`-model of the acyclic-models
argument for the chain homotopy `ezMap ≫ awMap ≃ 𝟙`.  This file proves that every cycle in
positive degree of the model is a boundary (`Work.Kunneth.ezaw_model_acyclic`), the input of that
acyclic-models construction.

`Work.Kunneth.stdModelContr` supplies contractions of the two factors with deficiency operators
`P`, `Q` (zero in positive degrees) and `Work.Kunneth.modelH_comm` gives
`d (H z) + H (d z) = z - (P ⊗ Q) z` for the contracting homotopy `H = s ⊗ 1 + P ⊗ t` of the Koszul
tensor product.  In positive degree `P ⊗ Q = 0`, so `z = d (H z)`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory TensorProduct

namespace Work.Kunneth

noncomputable section

attribute [-instance] AddCommGroup.toIntModule

theorem ezaw_model_acyclic (p q m : ℕ) (hm : 1 ≤ m) (z : ↥((Work.Kunneth.tMod p q).X m))
    (hz : (Work.Kunneth.tMod p q).d m (m - 1) z = 0) :
    ∃ w : ↥((Work.Kunneth.tMod p q).X (m + 1)), (Work.Kunneth.tMod p q).d (m + 1) m w = z := by
  obtain ⟨cC⟩ := stdModelContr p
  obtain ⟨cD⟩ := stdModelContr q
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hz'' : ((tpC (sChain (SdS p)) (sChain (SdS q))).d (k + 1) k) z = 0 := by
    have h := hz
    simp only [tMod, sMod] at h
    exact h
  have hzk : (ModuleCat.Hom.hom (ModuleCat.ofHom
      (tpD (sChain (SdS p)) (sChain (SdS q)) k))) z = 0 := by
    have h := hz''
    rw [tpC_d] at h
    exact h
  have hQ : (modelQ cC cD (k + 1)) z = 0 := by
    have h0 := congrArg (fun (f : tpX (sChain (SdS p)) (sChain (SdS q)) (k + 1) →ₗ[ℤ]
        tpX (sChain (SdS p)) (sChain (SdS q)) (k + 1)) => f z) (modelQ_eq_zero cC cD k)
    simpa only [LinearMap.zero_apply] using h0
  have hcomm : (tpD (sChain (SdS p)) (sChain (SdS q)) (k + 1)) (modelH cC cD (k + 1) z) = z := by
    have h := modelH_comm (sChain (SdS p)) (sChain (SdS q)) cC cD k z
    have hk : (tpD (sChain (SdS p)) (sChain (SdS q)) k) z = 0 := by
      show (ModuleCat.Hom.hom (ModuleCat.ofHom
        (tpD (sChain (SdS p)) (sChain (SdS q)) k))) z = 0
      exact hzk
    rw [hk, map_zero, add_zero, hQ, sub_zero] at h
    exact h
  refine ⟨modelH cC cD (k + 1) z, ?_⟩
  change (ModuleCat.Hom.hom ((tpC (sChain (SdS p)) (sChain (SdS q))).d (k + 1 + 1) (k + 1)))
      (modelH cC cD (k + 1) z) = z
  rw [tpC_d]
  change (tpD (sChain (SdS p)) (sChain (SdS q)) (k + 1)) (modelH cC cD (k + 1) z) = z
  exact hcomm

end

end Work.Kunneth
