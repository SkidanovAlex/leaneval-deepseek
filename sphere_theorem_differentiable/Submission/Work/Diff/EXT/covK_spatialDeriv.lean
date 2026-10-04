import Mathlib
import Submission.Work.Diff.EXT.curvDefs
import Submission.Work.Diff.C.mvfderiv_contMDiffAt
import Submission.Work.Diff.GE.tower_jointSmooth

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

set_option linter.unusedSectionVars false

/-- **Smoothness of the time-dependent "tower section".**  If the family `X : ℝ → TField` is
jointly smooth at `p₀ : ℝ × M` (as a section of the tangent bundle of `M`), then the section
`p ↦ (0, X p.1 p.2)` of the tangent bundle of `ℝ × M` is smooth at `p₀`.  This is the
time-dependent analogue of `Work.Diff.GE.contMDiff_towerSection`. -/
theorem contMDiffAt_towerSection_fam
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    {X : ℝ → TField (I := I) (M := M)} {p₀ : ℝ × M}
    (hXs : ContMDiffAt ((𝓘(ℝ, ℝ)).prod I) I.tangent ∞
      (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)) p₀) :
    ContMDiffAt ((𝓘(ℝ, ℝ)).prod I) ((𝓘(ℝ, ℝ)).prod I).tangent ∞
      (T% (fun p : ℝ × M ↦ Work.Diff.GE.towerSection (I := I) (X p.1) p)) p₀ := by
  -- the zero section of the tangent bundle of `ℝ` in the first variable ...
  have hA : CMDiff ∞ (fun p : ℝ × M ↦
      (zeroSection ℝ (TangentSpace (𝓘(ℝ, ℝ))) p.1 : TangentBundle (𝓘(ℝ, ℝ)) ℝ)) :=
    (contMDiff_zeroSection ℝ (TangentSpace (𝓘(ℝ, ℝ)))).comp contMDiff_fst
  -- ... and the joint family in the second, together over `ℝ × M`
  have hAB : CMDiffAt ∞ (fun p : ℝ × M ↦
      ((zeroSection ℝ (TangentSpace (𝓘(ℝ, ℝ))) p.1 : TangentBundle (𝓘(ℝ, ℝ)) ℝ),
        ((T% (X p.1)) p.2 : TangentBundle I M))) p₀ := by
    have h2 : ContMDiffAt ((𝓘(ℝ, ℝ)).prod I) I.tangent ∞
        (fun p : ℝ × M ↦ ((T% (X p.1)) p.2 : TangentBundle I M)) p₀ := hXs
    exact hA.contMDiffAt.prodMk h2
  -- identify the tangent bundle of the product with the product of the tangent bundles
  have h := (contMDiff_equivTangentBundleProd_symm (𝕜 := ℝ) (n := ∞) (I := 𝓘(ℝ, ℝ))
    (M := ℝ) (I' := I) (M' := M)).contMDiffAt.comp p₀ hAB
  refine h.congr_of_eventuallyEq ?_
  filter_upwards with p
  simp only [Function.comp_apply, Work.Diff.GE.towerSection, zeroSection,
    equivTangentBundleProd, Equiv.coe_fn_symm_mk]

/-- **Spatial derivative of a jointly smooth family, along a jointly smooth family of fields.**
Generalises the proved `Work.Diff.GE.tower_jointSmooth` (which is the time-independent case on a
cylinder `J ×ˢ univ`): the direction field may depend on `t` and the ambient set may be any open
subset of `ℝ × M`.

PROOF HINT (the proof of `tower_jointSmooth` adapts verbatim): for fixed `p ∈ V`, `hV` open turns
`hΦ` and `hX` into `CMDiffAt` statements at `p`; rewrite with `mvfderiv_prod_snd`
(`Work.Diff.GE.tower_jointSmooth`) as the derivative on the product manifold `ℝ × M` of
`(t,y) ↦ Φ t y` along the section `(t,y) ↦ (0, X t y)` (smooth by `hX`: the analogue of
`contMDiff_towerSection` for time-dependent `X`), and apply `Work.Diff.C.mvfderiv_contMDiffAt`. -/
theorem covK_spatialDeriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    {Φ : ℝ → M → ℝ} {V : Set (ℝ × M)} (hV : IsOpen V)
    (hΦ : ContMDiffOn ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) ∞ (fun p : ℝ × M ↦ Φ p.1 p.2) V)
    {X : ℝ → TField (I := I) (M := M)} (hX : JointField X V) :
    ContMDiffOn ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M ↦ mvfderiv I (Φ p.1) p.2 (X p.1 p.2)) V := by
  intro p₀ hp₀
  have hmem : V ∈ 𝓝 p₀ := hV.mem_nhds hp₀
  -- the joint family is smooth at `p₀`
  have hFat : CMDiffAt ∞ (fun p : ℝ × M ↦ Φ p.1 p.2) p₀ := hΦ.contMDiffAt hmem
  -- the time-dependent tower section is a smooth section of the tangent bundle of `ℝ × M`
  have hsec := contMDiffAt_towerSection_fam (I := I) (X := X) (p₀ := p₀) (hX.contMDiffAt hmem)
  -- hence the derivative on `ℝ × M` along that section is smooth at `p₀`
  have hpt := Work.Diff.C.mvfderiv_contMDiffAt (I := (𝓘(ℝ, ℝ)).prod I)
    (F := fun p : ℝ × M ↦ Φ p.1 p.2)
    (X := fun p : ℝ × M ↦ Work.Diff.GE.towerSection (I := I) (X p.1) p) hFat hsec
  -- and it agrees with the requested function near `p₀`
  refine (hpt.congr_of_eventuallyEq ?_).contMDiffWithinAt
  filter_upwards [hmem] with p hp
  have hFp : MDifferentiableAt ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) (fun p : ℝ × M ↦ Φ p.1 p.2) p :=
    (hΦ.contMDiffAt (hV.mem_nhds hp)).mdifferentiableAt (by simp)
  rw [Work.Diff.GE.towerSection_eq_sndVec (I := I) (X p.1) p,
    ← Work.Diff.GE.mvfderiv_prod_snd (I := I) hFp (X p.1 p.2)]

end Work.Diff.EXT
