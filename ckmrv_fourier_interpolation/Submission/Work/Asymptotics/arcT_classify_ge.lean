/-
# Classification of the orbit points of the tangency region at heights `t ≥ 1`

`Work.Asymptotics.ArcClassify.arcT_orbit_classification` classifies the orbit points
`γ • (i t)` that lie in `closure arcT` for `t ≤ 1`.  Here we record the *mirror* statement for
`t ≥ 1`: the change of variable `i t ↦ i/t = S • (i t)` transports the hypothesis at height `t`
to the hypothesis at height `1/t ≤ 1` after replacing `γ` by `γ S`, so the same eight
"grazing" elements occur.

Combined with the `t ≤ 1` case this says that for *every* `t > 0` the element `γ` with
`γ • (i t) ∈ closure arcT` is one of the eight `±`-grazing elements.
-/
import Mathlib
import Submission.Work.Asymptotics.arcT_classify
import Submission.Work.Asymptotics.DeltaFun_imagAxis_atZero

namespace Work.Asymptotics

open UpperHalfPlane ModularGroup Matrix
open scoped MatrixGroups

/-- `S * S = -1` in `SL(2,ℤ)`. -/
lemma S_mul_S_sl'' : (ModularGroup.S * ModularGroup.S : SL(2, ℤ)) = -1 := by decide

/-- The eight grazing elements are closed under right multiplication by `S`. -/
lemma isGrazeElem_mul_S {δ : SL(2, ℤ)} (h : ArcClassify.isGrazeElem δ) :
    ArcClassify.isGrazeElem (δ * ModularGroup.S) := by
  simp only [ArcClassify.isGrazeElem] at h ⊢
  rcases h with h | h | h | h | h | h | h | h <;> rw [h] <;> decide

/-- **Classification of the orbit points of `closure arcT` at heights `t ≥ 1`.** -/
theorem arcT_orbit_classification_ge (γ : SL(2, ℤ)) (t : ℝ) (ht : 0 < t) (hle : 1 ≤ t)
    (hτ : γ • Work.Kernels.imagAxis t ht ∈ closure arcT) : ArcClassify.isGrazeElem γ := by
  have ht' : (0 : ℝ) < t⁻¹ := inv_pos.mpr ht
  have hle' : t⁻¹ ≤ 1 := by rw [inv_le_one₀ ht]; exact hle
  have hSinv : ModularGroup.S • Work.Kernels.imagAxis t⁻¹ ht' = Work.Kernels.imagAxis t ht := by
    rw [imagAxis_smul_S t⁻¹ ht']
    apply UpperHalfPlane.ext
    first
      | (simp only [Work.Kernels.imagAxis, UpperHalfPlane.coe_mk, inv_inv])
      | (simp [Work.Kernels.imagAxis, inv_inv])
      | (simp only [inv_inv])
  have hτ' : (γ * ModularGroup.S) • Work.Kernels.imagAxis t⁻¹ ht' ∈ closure arcT := by
    rw [mul_smul, hSinv]; exact hτ
  have hg := ArcClassify.arcT_orbit_classification (γ * ModularGroup.S) t⁻¹ ht' hle' hτ'
  have h1 := isGrazeElem_mul_S hg
  have h2 := isGrazeElem_mul_S h1
  have h3 := isGrazeElem_mul_S h2
  have h4 : (((γ * ModularGroup.S) * ModularGroup.S) * ModularGroup.S) * ModularGroup.S = γ := by
    have e : (((γ * ModularGroup.S) * ModularGroup.S) * ModularGroup.S) * ModularGroup.S
        = γ * (ModularGroup.S * ModularGroup.S) * (ModularGroup.S * ModularGroup.S) := by
      simp only [mul_assoc]
    rw [e, S_mul_S_sl'']
    rw [mul_neg, mul_one, mul_neg, mul_one, neg_neg]
  rwa [h4] at h3

end Work.Asymptotics
