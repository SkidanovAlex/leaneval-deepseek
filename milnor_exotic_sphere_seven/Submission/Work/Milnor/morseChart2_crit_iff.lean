import Mathlib
import Submission.Work.Milnor.MorseFun
import Submission.Work.Milnor.ChartDefs
import Submission.Work.Milnor.eta_facts
import Submission.Work.Milnor.hfun_facts
import Submission.Work.Milnor.stereo_chart_re
import Submission.Work.Milnor.sphere_re_defs
import Submission.Work.Milnor.sphere_re_crit

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The critical points of `morseChart2`

`morseChart2 p = Re(p.2)/√(1 + ‖p.1‖²)` is the product of a function of the fibre coordinate
`p.2 ∈ S³` (the real part of a unit quaternion) and a function of the base coordinate
`p.1 ∈ ℝ⁴` (namely `eta u = 1/√(1 + ‖u‖²)`).

Since the two factors depend on the two different coordinates of the product manifold
`MSpace = ℝ⁴ × S³`, the differential

`d(morseChart2)_p = eta p.1 • d(Re)_{p.2} ∘ snd + Re(p.2) • d(eta)_{p.1} ∘ fst`

vanishes exactly when both pieces do, i.e. exactly at the points with `p.1 = 0` and `p.2 = ±1`.
The differential of `Re` on `S³` vanishes only at `±1` (`sphere_re_crit`), and the differential of
`eta` vanishes only at `0` (`eta_facts`).

To avoid the technical friction coming from the fact that `mfderiv` of an `ℝ`-valued function lands
in the (definitionally, but not syntactically, equal) type `TangentSpace 𝓘(ℝ,ℝ) x`, all statements
below are phrased through the canonical identification `NormedSpace.fromTangentSpace`.
-/

open scoped Manifold ContDiff Topology RealInnerProductSpace
open Topology TopologicalSpace Set
open Submission.Milnor

namespace Work.Milnor

noncomputable section

/-- The real part, as a function on the unit quaternions. -/
def reQS3 : QS3 → ℝ := fun y => (y : Quaternion ℝ).re

/-- The differential of `reQS3` at `y`, as a genuine continuous linear map into `ℝ` (via the
canonical identification `NormedSpace.fromTangentSpace`). -/
def Dre (y : QS3) : E3 →L[ℝ] ℝ :=
  (NormedSpace.fromTangentSpace (𝕜 := ℝ) (reQS3 y)).toContinuousLinearMap.comp
    (mfderiv (𝓡 3) 𝓘(ℝ,ℝ) reQS3 y)

/-- The canonical identification of the tangent space of `ℝ` at a point with `ℝ` is the identity. -/
lemma fromTS_comp_eq (y : QS3) {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : F →L[ℝ] TangentSpace 𝓘(ℝ,ℝ) (reQS3 y)) :
    (NormedSpace.fromTangentSpace (𝕜 := ℝ) (reQS3 y)).toContinuousLinearMap.comp f = f := by
  ext v
  rfl

lemma Dre_eq (y : QS3) : Dre y = mfderiv (𝓡 3) 𝓘(ℝ,ℝ) reQS3 y := by
  rw [Dre]
  exact fromTS_comp_eq y _

/-- Composing `Dre` with a further map is composition with `mfderiv reQS3`. -/
lemma Dre_comp (y : QS3) {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : F →L[ℝ] TangentSpace (𝓡 3) y) :
    (Dre y).comp f = (mfderiv (𝓡 3) 𝓘(ℝ,ℝ) reQS3 y).comp f := by
  apply ContinuousLinearMap.ext
  intro v
  rfl

/-- `eta` never vanishes. -/
lemma eta_ne_zero (u : E4) : eta u ≠ 0 := by
  rw [eta]
  exact inv_ne_zero (ne_of_gt (Real.sqrt_pos.mpr (by positivity)))

lemma mdifferentiableAt_reQS3 (y : QS3) : MDifferentiableAt (𝓡 3) 𝓘(ℝ,ℝ) reQS3 y := by
  have h : ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) ∞ reQS3 :=
    (ContinuousLinearMap.contMDiff (n := ∞) (𝕜 := ℝ) qreCLM).comp contMDiff_coe_sphere
  exact h.mdifferentiableAt (by simp)

lemma mdifferentiableAt_Gfun (p : MSpace) :
    MDifferentiableAt ((𝓡 4).prod (𝓡 3)) 𝓘(ℝ,ℝ) Gfun p := by
  have h1 : Gfun = reQS3 ∘ (@Prod.snd E4 QS3) := rfl
  rw [h1]
  exact (mdifferentiableAt_reQS3 p.2).comp p mdifferentiableAt_snd

lemma mdifferentiableAt_Hfun (p : MSpace) :
    MDifferentiableAt ((𝓡 4).prod (𝓡 3)) 𝓘(ℝ,ℝ) Hfun p := by
  have hmd : MDifferentiableAt (𝓡 4) 𝓘(ℝ,ℝ) eta p.1 :=
    (hasFDerivAt_eta p.1).differentiableAt.mdifferentiableAt
  have h1 : Hfun = eta ∘ (@Prod.fst E4 QS3) := rfl
  rw [h1]
  exact hmd.comp p mdifferentiableAt_fst

/-- The manifold derivative of the fibre factor `Gfun`. -/
lemma mfderiv_Gfun (p : MSpace) :
    mfderiv ((𝓡 4).prod (𝓡 3)) 𝓘(ℝ,ℝ) Gfun p
      = (Dre p.2).comp (ContinuousLinearMap.snd ℝ E4 E3) := by
  have hbasic : mfderiv ((𝓡 4).prod (𝓡 3)) 𝓘(ℝ,ℝ) Gfun p
      = (mfderiv (𝓡 3) 𝓘(ℝ,ℝ) reQS3 p.2).comp (ContinuousLinearMap.snd ℝ E4 E3) := by
    have h1 : Gfun = reQS3 ∘ (@Prod.snd E4 QS3) := rfl
    rw [h1, mfderiv_comp (I := (𝓡 4).prod (𝓡 3)) (I' := (𝓡 3)) (I'' := 𝓘(ℝ,ℝ)) p
        (mdifferentiableAt_reQS3 p.2) mdifferentiableAt_snd]
    rw [mfderiv_snd]
    rfl
  rw [hbasic]
  exact (Dre_comp p.2 (ContinuousLinearMap.snd ℝ E4 E3)).symm

/-- The manifold derivative of the base factor `Hfun`. -/
lemma mfderiv_Hfun (p : MSpace) :
    mfderiv ((𝓡 4).prod (𝓡 3)) 𝓘(ℝ,ℝ) Hfun p
      = (fderiv ℝ eta p.1).comp (ContinuousLinearMap.fst ℝ E4 E3) := by
  have hmd : MDifferentiableAt (𝓡 4) 𝓘(ℝ,ℝ) eta p.1 :=
    (hasFDerivAt_eta p.1).differentiableAt.mdifferentiableAt
  have h1 : Hfun = eta ∘ (@Prod.fst E4 QS3) := rfl
  rw [h1, mfderiv_comp (I := (𝓡 4).prod (𝓡 3)) (I' := (𝓡 4)) (I'' := 𝓘(ℝ,ℝ)) p
      hmd mdifferentiableAt_fst]
  rw [mfderiv_eq_fderiv, mfderiv_fst]
  rfl

/-- The differential of `reQS3` vanishes exactly at `±1`. -/
lemma Dre_eq_zero (y : QS3) :
    Dre y = 0 ↔ (y : Quaternion ℝ) = 1 ∨ (y : Quaternion ℝ) = -1 := by
  rw [Dre_eq y]
  exact sphere_re_crit y

/-- The differential of `eta` vanishes exactly at the origin. -/
lemma fderiv_eta_eq_zero (x : E4) : fderiv ℝ eta x = 0 ↔ x = 0 :=
  eta_facts.2.2.2 x

/-- The manifold derivative of `morseChart2` at `p`, evaluated on a tangent vector
`v = (v₁, v₂) ∈ ℝ⁴ × ℝ³`. -/
lemma mfderiv_morseChart2_apply (p : MSpace) (v : E4 × E3) :
    (NormedSpace.fromTangentSpace (𝕜 := ℝ) (morseChart2 p))
        ((mfderiv ((𝓡 4).prod (𝓡 3)) 𝓘(ℝ,ℝ) morseChart2 p) v)
      = Gfun p * (fderiv ℝ eta p.1 v.1) + Hfun p * (Dre p.2 v.2) := by
  rw [show morseChart2 = Gfun * Hfun from funext morseChart2_eq]
  rw [((mdifferentiableAt_Gfun p).hasMFDerivAt.mul
    (mdifferentiableAt_Hfun p).hasMFDerivAt).mfderiv]
  rw [mfderiv_Hfun, mfderiv_Gfun]
  change (Gfun p • ((fderiv ℝ eta p.1).comp (ContinuousLinearMap.fst ℝ E4 E3))
        + Hfun p • ((Dre p.2).comp (ContinuousLinearMap.snd ℝ E4 E3))) v
      = Gfun p * (fderiv ℝ eta p.1 v.1) + Hfun p * (Dre p.2 v.2)
  simp

/-- **The critical points of `morseChart2`** are the two points `(0, ±1)`. -/
theorem morseChart2_crit_iff (p : Submission.Milnor.MSpace) :
    mfderiv ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))).prod
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))))
      (modelWithCornersSelf ℝ ℝ) Submission.Milnor.morseChart2 p = 0 ↔
      p.1 = 0 ∧ ((p.2 : Quaternion ℝ) = 1 ∨ (p.2 : Quaternion ℝ) = -1) := by
  have hb : Hfun p ≠ 0 := eta_ne_zero p.1
  have key := mfderiv_morseChart2_apply p
  constructor
  · intro h
    have hzero2 : ∀ v2 : E3, Dre p.2 v2 = 0 := by
      intro v2
      have hv := key ((0 : E4), v2)
      rw [h] at hv
      simp at hv
      first
        | exact (mul_eq_zero.mp hv.symm).resolve_left hb
        | exact hv.resolve_right hb
        | exact hv.resolve_left hb
    have hDre : Dre p.2 = 0 := ContinuousLinearMap.ext hzero2
    have hp2 : (p.2 : Quaternion ℝ) = 1 ∨ (p.2 : Quaternion ℝ) = -1 :=
      (Dre_eq_zero p.2).mp hDre
    have hG : Gfun p ≠ 0 := by
      rcases hp2 with h2 | h2
      · rw [Gfun, h2, Quaternion.re_one]; norm_num
      · rw [Gfun, h2, Quaternion.re_neg, Quaternion.re_one]; norm_num
    have hzero1 : ∀ v1 : E4, fderiv ℝ eta p.1 v1 = 0 := by
      intro v1
      have hv := key (v1, (0 : E3))
      rw [h] at hv
      simp at hv
      first
        | exact (mul_eq_zero.mp hv.symm).resolve_left hG
        | exact hv.resolve_right hG
        | exact hv.resolve_left hG
    have hDeta : fderiv ℝ eta p.1 = 0 := ContinuousLinearMap.ext hzero1
    exact ⟨(fderiv_eta_eq_zero p.1).mp hDeta, hp2⟩
  · rintro ⟨hp1, hp2⟩
    have hDeta : fderiv ℝ eta p.1 = 0 := (fderiv_eta_eq_zero p.1).mpr hp1
    have hDre : Dre p.2 = 0 := (Dre_eq_zero p.2).mpr hp2
    ext v
    have hv := key v
    rw [hDeta, hDre] at hv
    simp at hv
    simpa using hv

end

end Work.Milnor
