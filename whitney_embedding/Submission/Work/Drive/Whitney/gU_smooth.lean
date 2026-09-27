import Mathlib
import Submission.Work.Drive.Whitney.glAuxCoreDefs

/-!
# Smoothness of the operator family `gU`

`Work.Drive.Whitney.gU` is assembled from the auxiliary fields
`gAm, gAl, gNn, gN, gC, gJ, gPu, gChi, gTheta, gLam, gZ, gCfam` by ring operations, scalar
multiplication, `ContinuousLinearMap.smulRight`, composition of continuous linear maps and the two
divisions (by `gAm` and by `1 + gTheta`).  Each auxiliary field is a composition of the smooth
ingredients `u, w, ψ, φ`; the only non-polynomial operations are `inner ℝ` (handled by
`ContDiff.inner`), the two divisions (handled by `ContDiff.div`, whose side conditions are exactly
the two hypotheses `hAm` and `hTh` of the target) and `ContinuousLinearMap.smulRight` (handled by
`ContDiff.smulRight`).

The lemmas below are ordered exactly as the definitions of `glAuxCoreDefs`, so that each smoothness
statement is proved from the previous ones.
-/

namespace Work.Drive.Whitney

open scoped Real ContDiff Topology
open Set

variable {m : ℕ}

/-- `gAm` is `C^∞`. -/
lemma contDiff_gAm (φ : ℝ × ℝ → ℝ) (u : ℝ × ℝ → EuclideanSpace ℝ (Fin m))
    (hu : ContDiff ℝ smw u) (hφ : ContDiff ℝ smw φ) : ContDiff ℝ smw (gAm φ u) := by
  unfold gAm
  exact (hφ.mul (ContDiff.inner (𝕜 := ℝ) hu hu)).add (contDiff_const.sub hφ)

/-- The map `p ↦ innerSL ℝ (u p)` (a continuous-linear-map valued map) is `C^∞`. -/
lemma contDiff_innerSL (u : ℝ × ℝ → EuclideanSpace ℝ (Fin m)) (hu : ContDiff ℝ smw u) :
    ContDiff ℝ smw
      (fun p => (innerSL ℝ (u p) : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ)) := by
  simpa only [Function.comp_def] using
    (ContinuousLinearMap.contDiff (innerSL ℝ : EuclideanSpace ℝ (Fin m) →L[ℝ]
      (EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ))).comp hu

/-- `gAl` is `C^∞` where `gAm` does not vanish. -/
lemma contDiff_gAl (φ : ℝ × ℝ → ℝ) (u w : ℝ × ℝ → EuclideanSpace ℝ (Fin m))
    (hu : ContDiff ℝ smw u) (hw : ContDiff ℝ smw w) (hφ : ContDiff ℝ smw φ)
    (hAm : ∀ p, gAm φ u p ≠ 0) : ContDiff ℝ smw (gAl φ u w) := by
  unfold gAl
  exact (ContDiff.inner (𝕜 := ℝ) hw hu).div (contDiff_gAm φ u hu hφ) hAm

/-- `gNn` is `C^∞` where `gAm` does not vanish. -/
lemma contDiff_gNn (φ : ℝ × ℝ → ℝ) (u w : ℝ × ℝ → EuclideanSpace ℝ (Fin m))
    (hu : ContDiff ℝ smw u) (hw : ContDiff ℝ smw w) (hφ : ContDiff ℝ smw φ)
    (hAm : ∀ p, gAm φ u p ≠ 0) : ContDiff ℝ smw (gNn φ u w) := by
  unfold gNn
  exact hw.sub ((contDiff_gAl φ u w hu hw hφ hAm).smul hu)

/-- `gN` is `C^∞` where `gAm` does not vanish. -/
lemma contDiff_gN (φ : ℝ × ℝ → ℝ) (u w : ℝ × ℝ → EuclideanSpace ℝ (Fin m))
    (hu : ContDiff ℝ smw u) (hw : ContDiff ℝ smw w) (hφ : ContDiff ℝ smw φ)
    (hAm : ∀ p, gAm φ u p ≠ 0) : ContDiff ℝ smw (gN φ u w) := by
  unfold gN
  exact ContDiff.inner (𝕜 := ℝ) (contDiff_gNn φ u w hu hw hφ hAm)
    (contDiff_gNn φ u w hu hw hφ hAm)

/-- `gC` is `C^∞` where `gAm` does not vanish. -/
lemma contDiff_gC (φ : ℝ × ℝ → ℝ) (u w : ℝ × ℝ → EuclideanSpace ℝ (Fin m))
    (hu : ContDiff ℝ smw u) (hw : ContDiff ℝ smw w) (hφ : ContDiff ℝ smw φ)
    (hAm : ∀ p, gAm φ u p ≠ 0) : ContDiff ℝ smw (gC φ u w) := by
  unfold gC
  exact (contDiff_gN φ u w hu hw hφ hAm).div (contDiff_gAm φ u hu hφ) hAm

/-- `gJ` is `C^∞` where `gAm` does not vanish. -/
lemma contDiff_gJ (φ : ℝ × ℝ → ℝ) (u w : ℝ × ℝ → EuclideanSpace ℝ (Fin m))
    (hu : ContDiff ℝ smw u) (hw : ContDiff ℝ smw w) (hφ : ContDiff ℝ smw φ)
    (hAm : ∀ p, gAm φ u p ≠ 0) : ContDiff ℝ smw (gJ φ u w) := by
  unfold gJ
  refine ((contDiff_gAm φ u hu hφ).inv hAm).smul ?_
  refine (ContDiff.smulRight (contDiff_innerSL u hu)
    (contDiff_gNn φ u w hu hw hφ hAm)).sub ?_
  exact ContDiff.smulRight (contDiff_innerSL (gNn φ u w)
    (contDiff_gNn φ u w hu hw hφ hAm)) hu

/-- `gPu` is `C^∞` where `gAm` does not vanish. -/
lemma contDiff_gPu (φ : ℝ × ℝ → ℝ) (u : ℝ × ℝ → EuclideanSpace ℝ (Fin m))
    (hu : ContDiff ℝ smw u) (hφ : ContDiff ℝ smw φ)
    (hAm : ∀ p, gAm φ u p ≠ 0) : ContDiff ℝ smw (gPu φ u) := by
  unfold gPu
  exact ((contDiff_gAm φ u hu hφ).inv hAm).smul
    (ContDiff.smulRight (contDiff_innerSL u hu) hu)

/-- `gChi` is `C^∞` where `gAm` does not vanish. -/
lemma contDiff_gChi (φ : ℝ × ℝ → ℝ) (u w ψ : ℝ × ℝ → EuclideanSpace ℝ (Fin m))
    (hu : ContDiff ℝ smw u) (hw : ContDiff ℝ smw w) (hψ : ContDiff ℝ smw ψ)
    (hφ : ContDiff ℝ smw φ) (hAm : ∀ p, gAm φ u p ≠ 0) :
    ContDiff ℝ smw (gChi φ u w ψ) := by
  unfold gChi
  refine (((contDiff_gAl φ u w hu hw hφ hAm).add
    (contDiff_gC φ u w hu hw hφ hAm)).smul hψ).sub ?_
  exact (((ContDiff.inner (𝕜 := ℝ) hψ (contDiff_gNn φ u w hu hw hφ hAm)).div
    (contDiff_gAm φ u hu hφ) hAm).smul (contDiff_gNn φ u w hu hw hφ hAm))

/-- `gTheta` is `C^∞` where `gAm` does not vanish. -/
lemma contDiff_gTheta (φ : ℝ × ℝ → ℝ) (u w ψ : ℝ × ℝ → EuclideanSpace ℝ (Fin m))
    (hu : ContDiff ℝ smw u) (hw : ContDiff ℝ smw w) (hψ : ContDiff ℝ smw ψ)
    (hφ : ContDiff ℝ smw φ) (hAm : ∀ p, gAm φ u p ≠ 0) :
    ContDiff ℝ smw (gTheta φ u w ψ) := by
  unfold gTheta
  refine (((contDiff_gAl φ u w hu hw hφ hAm).add
    (contDiff_gC φ u w hu hw hφ hAm)).mul
    (ContDiff.inner (𝕜 := ℝ) hψ (contDiff_gChi φ u w ψ hu hw hψ hφ hAm))).sub ?_
  exact ((ContDiff.inner (𝕜 := ℝ) hψ (contDiff_gNn φ u w hu hw hφ hAm)).mul
    (ContDiff.inner (𝕜 := ℝ) (contDiff_gChi φ u w ψ hu hw hψ hφ hAm)
      (contDiff_gNn φ u w hu hw hφ hAm))).div (contDiff_gAm φ u hu hφ) hAm

/-- `gLam` is `C^∞` where `gAm` does not vanish and `1 + gTheta` does not vanish. -/
lemma contDiff_gLam (φ : ℝ × ℝ → ℝ) (u w ψ : ℝ × ℝ → EuclideanSpace ℝ (Fin m))
    (hu : ContDiff ℝ smw u) (hw : ContDiff ℝ smw w) (hψ : ContDiff ℝ smw ψ)
    (hφ : ContDiff ℝ smw φ) (hAm : ∀ p, gAm φ u p ≠ 0)
    (hTh : ∀ p, 1 + gTheta φ u w ψ p ≠ 0) : ContDiff ℝ smw (gLam φ u w ψ) := by
  unfold gLam
  exact (contDiff_const.sub ((contDiff_gAl φ u w hu hw hφ hAm).add
    (contDiff_gC φ u w hu hw hφ hAm))).div
    (contDiff_const.add (contDiff_gTheta φ u w ψ hu hw hψ hφ hAm)) hTh

/-- `gZ` is `C^∞` where `gAm` and `1 + gTheta` do not vanish. -/
lemma contDiff_gZ (φ : ℝ × ℝ → ℝ) (u w ψ : ℝ × ℝ → EuclideanSpace ℝ (Fin m))
    (hu : ContDiff ℝ smw u) (hw : ContDiff ℝ smw w) (hψ : ContDiff ℝ smw ψ)
    (hφ : ContDiff ℝ smw φ) (hAm : ∀ p, gAm φ u p ≠ 0)
    (hTh : ∀ p, 1 + gTheta φ u w ψ p ≠ 0) : ContDiff ℝ smw (gZ φ u w ψ) := by
  unfold gZ
  exact (contDiff_gLam φ u w ψ hu hw hψ hφ hAm hTh).smul hψ

/-- `gCfam` is `C^∞` where `gAm` and `1 + gTheta` do not vanish. -/
lemma contDiff_gCfam (φ : ℝ × ℝ → ℝ) (u w ψ : ℝ × ℝ → EuclideanSpace ℝ (Fin m))
    (hu : ContDiff ℝ smw u) (hw : ContDiff ℝ smw w) (hψ : ContDiff ℝ smw ψ)
    (hφ : ContDiff ℝ smw φ) (hAm : ∀ p, gAm φ u p ≠ 0)
    (hTh : ∀ p, 1 + gTheta φ u w ψ p ≠ 0) : ContDiff ℝ smw (gCfam φ u w ψ) := by
  unfold gCfam
  exact (contDiff_const.sub (contDiff_gPu φ u hu hφ hAm)).add
    (ContDiff.smulRight
      (contDiff_innerSL (gZ φ u w ψ) (contDiff_gZ φ u w ψ hu hw hψ hφ hAm hTh))
      (contDiff_gChi φ u w ψ hu hw hψ hφ hAm))

/-- `gU` is `C^∞` where `gAm` and `1 + gTheta` do not vanish. -/
lemma contDiff_gU (φ : ℝ × ℝ → ℝ) (u w ψ : ℝ × ℝ → EuclideanSpace ℝ (Fin m))
    (hu : ContDiff ℝ smw u) (hw : ContDiff ℝ smw w) (hψ : ContDiff ℝ smw ψ)
    (hφ : ContDiff ℝ smw φ) (hAm : ∀ p, gAm φ u p ≠ 0)
    (hTh : ∀ p, 1 + gTheta φ u w ψ p ≠ 0) : ContDiff ℝ smw (gU φ u w ψ) := by
  unfold gU
  refine (((contDiff_gAl φ u w hu hw hφ hAm).smul contDiff_const).add
    (contDiff_gJ φ u w hu hw hφ hAm)).add ?_
  exact (((contDiff_gCfam φ u w ψ hu hw hψ hφ hAm hTh).sub
      ((contDiff_gAl φ u w hu hw hφ hAm).smul contDiff_const))).mul
    (contDiff_const.sub (contDiff_gPu φ u hu hφ hAm))

theorem gU_smooth {m : ℕ}
    (u w ψ : ℝ × ℝ → EuclideanSpace ℝ (Fin m)) (φ : ℝ × ℝ → ℝ)
    (hu : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u)
    (hw : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w)
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hAm : ∀ p, Work.Drive.Whitney.gAm φ u p ≠ 0)
    (hTh : ∀ p, 1 + Work.Drive.Whitney.gTheta φ u w ψ p ≠ 0) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => Work.Drive.Whitney.gU φ u w ψ p) := by
  exact contDiff_gU φ u w ψ hu hw hψ hφ hAm hTh

end Work.Drive.Whitney
