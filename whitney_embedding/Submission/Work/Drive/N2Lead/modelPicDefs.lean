import Mathlib
import Submission.Work.Drive.N2Lead.twistToolkit
import Submission.Work.Drive.N2Lead.mobiusArcSmooth
import Submission.Work.Drive.N2Lead.mobiusArcDefs

/-!
# The plane model of the twisted Möbius upper picture

`Work.Drive.N2Lead.modelPic η δ a' ε Dp εp` is the *plane model* of the twisted Möbius picture
`Work.Drive.N2Lead.mobiusTwisted`: instead of `proj2 ∘ pushY Dp εp 1 ∘ twistX ε (-1) ∘ twistY a' (-1)`
applied to the *window drawing* `mobiusWindowDrawing D η S`, it is the same composition applied to
the flat model `cE3 ∘ saddlePsi η δ` on `ℂ`:

  `modelPic η δ a' ε Dp εp ζ = proj2 (pushY Dp εp 1 (twistX ε (-1) (twistY a' (-1)
      (cE3 (saddlePsi η δ ζ)))))`.

On the model region `saddleRegion (modelBall …) S.Z (39/20)` of the packet (with `ηs = packetEta D η`,
`δ = 1/20`, `a' = S.a'`) the twisted picture of the packet factors through `Z`:

  `proj2 (mobiusTwisted D η S ε εp Dp y) = modelPic ηs (1/20) S.a' ε Dp εp (S.Z y)`   (`y` in the
region), so the pointwise rows of the picture in the model region are properties of `modelPic` alone.

The two functions whose values are the `ζ = Z y`-side arcs of the model are
`mobiusAlpha η δ s a' ε` (`cE3 (-(√(modelZeta)))`) and `mobiusBeta η δ s a' ε`
(`cE3 (√(modelZeta))`), with `√(modelZeta) = mobiusRho η δ s`.
-/

namespace Work.Drive.N2Lead

open scoped Manifold ContDiff Topology
open Set Filter

noncomputable section

/-- **The plane model of the twisted Möbius upper picture** (see the module docstring). -/
def modelPic (η δ a' ε Dp εp : ℝ) : ℂ → ℂ :=
  fun ζ => proj2 (pushY Dp εp 1
    (twistX ε (-1) (twistY a' (-1) (Work.Drive.N2.cE3 (Work.Drive.N2.saddlePsi η δ ζ)))))

lemma modelPic_eq (η δ a' ε Dp εp : ℝ) (ζ : ℂ) :
    modelPic η δ a' ε Dp εp ζ
      = proj2 (pushY Dp εp 1
        (twistX ε (-1) (twistY a' (-1)
          (Work.Drive.N2.cE3 (Work.Drive.N2.saddlePsi η δ ζ))))) := rfl

/-- The model picture is smooth. -/
theorem contDiff_modelPic {η δ a' ε Dp εp : ℝ} (hδ : 0 < δ) (hδ₂ : δ < 1 / 2) :
    ContDiff ℝ tpTop (modelPic η δ a' ε Dp εp) := by
  have hψ : ContDiff ℝ tpTop (fun ζ : ℂ => Work.Drive.N2.saddlePsi η δ ζ) :=
    Work.Drive.N2.contDiff_saddlePsi η δ hδ hδ₂
  have h1 : ContDiff ℝ tpTop (fun ζ : ℂ => Work.Drive.N2.cE3 (Work.Drive.N2.saddlePsi η δ ζ)) :=
    Work.Drive.N2.cE3.contDiff.comp hψ
  have h2 : ContDiff ℝ tpTop (fun ζ : ℂ =>
      twistY a' (-1) (Work.Drive.N2.cE3 (Work.Drive.N2.saddlePsi η δ ζ))) :=
    (contDiff_twistY_apply a' (-1)).comp h1
  have h3 : ContDiff ℝ tpTop (fun ζ : ℂ => twistX ε (-1)
      (twistY a' (-1) (Work.Drive.N2.cE3 (Work.Drive.N2.saddlePsi η δ ζ)))) :=
    (contDiff_twistX_apply ε (-1)).comp h2
  have h4 : ContDiff ℝ tpTop (fun ζ : ℂ => pushY Dp εp 1 (twistX ε (-1)
      (twistY a' (-1) (Work.Drive.N2.cE3 (Work.Drive.N2.saddlePsi η δ ζ))))) :=
    (contDiff_pushY Dp εp).comp ((contDiff_const (c := 1)).prodMk h3)
  have hpc : ContDiff ℝ tpTop (proj2 : E3 → ℂ) := by
    have h : (proj2 : E3 → ℂ)
        = fun v => Complex.ofRealCLM (v 0) + Complex.I * Complex.ofRealCLM (v 1) := by
      funext v; apply Complex.ext <;> simp [proj2]
    rw [h]
    fun_prop
  exact hpc.comp h4

/-- The value of the model picture when the model coordinate is (the negative of) the arc
`mobiusRho`: it is the pushed `mobiusAlpha`. -/
lemma modelPic_of_saddlePsi_eq_neg {η δ s a' ε Dp εp : ℝ} {ζ : ℂ} {w : ℝ}
    (h : Work.Drive.N2.saddlePsi η δ ζ = -(mobiusRho η δ s w)) :
    modelPic η δ a' ε Dp εp ζ = proj2 (pushY Dp εp 1 (mobiusAlpha η δ s a' ε w)) := by
  rw [modelPic_eq, h, mobiusAlpha]

/-- The value of the model picture when the model coordinate is the arc `mobiusRho`: it is the pushed
`mobiusBeta`. -/
lemma modelPic_of_saddlePsi_eq {η δ s a' ε Dp εp : ℝ} {ζ : ℂ} {w : ℝ}
    (h : Work.Drive.N2.saddlePsi η δ ζ = mobiusRho η δ s w) :
    modelPic η δ a' ε Dp εp ζ = proj2 (pushY Dp εp 1 (mobiusBeta η δ s a' ε w)) := by
  rw [modelPic_eq, h, mobiusBeta]

end

end Work.Drive.N2Lead
