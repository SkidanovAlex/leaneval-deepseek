/-
# `MubarAssemblyAux` — the structural lemmas of the `mubarData` assembly

* `SG_agree_g`, `SY_agree_PsiCan`, `Ftau_SG_agree`, `mubar_sanitized_eq` — the `mubar` of the
  *sanitised* family of `R5Parts` is the `mubar` of the reference family
  `(F_* + slice g τ, slice g τ)` / `(F_* + slice g τ, Φs + E (slice g τ))` (congruence on the
  open quadrant, where `SG α g = tauExt g = g` and `SΨ α Φs E g = PsiCan`).
* `mubar_ref_eq` — `μ̄(τ) = 2·pExp α·μ(τ) − L₁₂(3 D_θ g(τ)/(1+z))(0)`, the definitional identity
  of `Construction.mufunS` (`Work.FTS_MuLipC.muDyn_const_eq`).
* `Env_mono` — monotonicity of the envelope in the (nonnegative) size argument.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS_RegExport.RXR5.Basic
import Submission.Work.FTS_RegExport.RXR5.R5PiecesF
import Submission.Work.FTS_MuLipC.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology

namespace Work.FTS_RegExport.RXR5L

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.Regularity (pExp gSlice)

set_option autoImplicit false

/-- `Env` is monotone in the second (nonnegative) argument. -/
theorem Env_mono {β : ℝ} (hβ : 0 ≤ β) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    Work.FTS_MuLipC.Env β a ≤ Work.FTS_MuLipC.Env β b := by
  have h1 : Real.sqrt β * a ≤ Real.sqrt β * b :=
    mul_le_mul_of_nonneg_left hab (Real.sqrt_nonneg β)
  have h2 : a ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ ha hab 2
  have h3 : β ^ (-(3 / 2 : ℝ)) * a ^ 2 ≤ β ^ (-(3 / 2 : ℝ)) * b ^ 2 :=
    mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hβ _)
  simp only [Work.FTS_MuLipC.Env]
  linarith

/-- `SG α g` agrees with the raw family `g` on the open quadrant, for `τ ≥ 0`. -/
theorem SG_agree_g {α : ℝ} {g : Fam} {τ : ℝ} (hτ : 0 ≤ τ) :
    Work.FTS_RegExport.RXR5.AgreeOnQ (gSlice (Work.FTS_RegExport.RXR5.SG α g) τ)
      (gSlice g τ) := by
  intro z θ hz hθ hθ2
  change Work.FTS_RegExport.RXR5.SG α g z θ τ = g z θ τ
  rw [show Work.FTS_RegExport.RXR5.SG α g z θ τ
      = Work.FTS.FinalV2.tauExt g z θ τ from
    Work.FTS_RegExport.RXR5.SG_apply_of_pos hz hθ.le hθ2.le,
    Work.FTS.FinalV2.tauExt_of_nonneg g hτ]

/-- `SΨ α Φs E g` agrees with `PsiCan Φs E g` on the open quadrant, for `τ ≥ 0`. -/
theorem SY_agree_PsiCan {α : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g : Fam} {τ : ℝ}
    (hτ : 0 ≤ τ) :
    Work.FTS_RegExport.RXR5.AgreeOnQ (gSlice (Work.FTS_RegExport.RXR5.SΨ α Φs E g) τ)
      (gSlice (Work.FTS.Nonlin.PsiCan Φs E g) τ) := by
  intro z θ hz hθ hθ2
  have h1 := Work.FTS_RegExport.RXR5.SΨ_slice_agreeOnQ α Φs E g τ z θ hz hθ hθ2
  have h2 : Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.FinalV2.tauExt g)) τ z θ
      = Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E g) τ z θ := by
    have hfun : Work.FTS.Galerkin.slice (Work.FTS.FinalV2.tauExt g) τ
        = Work.FTS.Galerkin.slice g τ := by
      funext z' θ'
      exact Work.FTS.FinalV2.tauExt_of_nonneg g hτ
    simp only [Work.FTS.Nonlin.PsiCan, Work.FTS.Galerkin.slice]
    rw [hfun]
  exact h1.trans h2

/-- The `F`-profile `F_* + slice (SG α g) τ` agrees with `F_* + slice g τ` on the quadrant. -/
theorem Ftau_SG_agree {α : ℝ} {g : Fam} {τ : ℝ} (hτ : 0 ≤ τ) :
    Work.FTS_RegExport.RXR5.AgreeOnQ
      (Work.Construction.Ftau (pExp α) (Work.FTS_RegExport.RXR5.SG α g) τ)
      (Work.Construction.Ftau (pExp α) g τ) :=
  Work.FTS_RegExport.RXR5.Ftau_congr_of_agreeOnQ (SG_agree_g (α := α) hτ)

/-- **The `mubar` of the sanitised family is the reference `mubar`.** -/
theorem mubar_sanitized_eq {α : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g : Fam} {τ : ℝ}
    (hτ : 0 ≤ τ) :
    Work.Construction.mubar
        (Work.Construction.N0 (pExp α)
          (Work.Construction.Ftau (pExp α) (Work.FTS_RegExport.RXR5.SG α g) τ)
          (gSlice (Work.FTS_RegExport.RXR5.SG α g) τ))
        (Work.Construction.N (pExp α)
          (Work.Construction.Ftau (pExp α) (Work.FTS_RegExport.RXR5.SG α g) τ)
          (gSlice (Work.FTS_RegExport.RXR5.SΨ α Φs E g) τ))
      = Work.Construction.mubar
        (Work.Construction.N0 (pExp α)
          (Work.Construction.Ftau (pExp α) g τ) (gSlice g τ))
        (Work.Construction.N (pExp α)
          (Work.Construction.Ftau (pExp α) g τ)
          (gSlice (Work.FTS.Nonlin.PsiCan Φs E g) τ)) :=
  Work.FTS_RegExport.RXR5.mubar_congr_of_agreeOnQ (α := pExp α)
    (Ftau_SG_agree (α := α) hτ) (SG_agree_g (α := α) hτ) (SY_agree_PsiCan (α := α) hτ)

/-- **The modulation identity.**  The reference `mubar` is `2·pExp α·μ(τ)` minus the transport
zero-mode `L₁₂(3 D_θ g(τ)/(1+z))(0)`. -/
theorem mubar_ref_eq {α : ℝ} (hα : 0 < α) {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g : Fam} {τ : ℝ} :
    Work.Construction.mubar
        (Work.Construction.N0 (pExp α)
          (Work.Construction.Ftau (pExp α) g τ) (gSlice g τ))
        (Work.Construction.N (pExp α)
          (Work.Construction.Ftau (pExp α) g τ)
          (gSlice (Work.FTS.Nonlin.PsiCan Φs E g) τ))
      = 2 * (pExp α) * Work.FTS.Galerkin.muDyn (pExp α) (Work.FTS.Nonlin.PsiCan Φs E g) g τ
        - Work.Construction.L12
            (fun z θ => 3 * Work.Spaces.Dth (gSlice g τ) z θ / (1 + z)) 0 := by
  have hβ : (pExp α) ≠ 0 := ne_of_gt (Work.FTS.Regularity.pExp_pos hα)
  have hmu : Work.FTS.Galerkin.muDyn (pExp α) (Work.FTS.Nonlin.PsiCan Φs E g) g τ
      = Work.FTS.Galerkin.muDyn (pExp α)
          (Work.FTS.Nonlin.PsiCan Φs (⇑E) (Work.FTS.FinalV2.cst (gSlice g τ)))
          (Work.FTS.FinalV2.cst (gSlice g τ)) 0 := rfl
  rw [hmu, Work.FTS_MuLipC.muDyn_const_eq]
  simp only [Work.FTS_MuLipC.Sn0, Work.FTS_MuLipC.Sn]
  rw [show Work.Construction.Ftau (pExp α) g τ
        = Work.Construction.Ftot (pExp α) (gSlice g τ) from rfl,
      show gSlice (Work.FTS.Nonlin.PsiCan Φs (⇑E) g) τ
        = fun z θ => Φs z θ + E (gSlice g τ) z θ from rfl,
      Work.FTS.GalBasis.L12_congr_all (z := (0 : ℝ)) (a := Work.FTS_MuLipC.Tf (gSlice g τ))
        (b := fun z θ => Work.Spaces.Dth (gSlice g τ) z θ * (1 + z)⁻¹ * 3)
        (fun z θ => by simp only [Work.FTS_MuLipC.Tf]; ring),
      Work.Construction.mubar]
  field_simp
  ring_nf

end Work.FTS_RegExport.RXR5L
