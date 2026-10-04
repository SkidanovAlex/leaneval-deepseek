import Mathlib
import Submission.Work.Diff.Dim2.Lib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.Dim2

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set Filter

/-- A nonzero continuous linear endomorphism of `ℝ` is invertible: it is multiplication by
`φ 1`, and the inverse is multiplication by `(φ 1)⁻¹`. -/
private lemma isInvertible_of_apply_one_ne_zero {φ : ℝ →L[ℝ] ℝ} (h : φ 1 ≠ 0) :
    φ.IsInvertible := by
  have hφa : ∀ a : ℝ, φ a = a * φ 1 := by
    intro a
    rw [show a = a • (1 : ℝ) by simp, map_smul]
    simp
  have hg : ∀ a : ℝ, ((φ 1)⁻¹ • (1 : ℝ →L[ℝ] ℝ)) a = (φ 1)⁻¹ * a := fun a => by simp
  refine ContinuousLinearMap.IsInvertible.of_inverse (g := (φ 1)⁻¹ • (1 : ℝ →L[ℝ] ℝ)) ?_ ?_
  · apply ContinuousLinearMap.ext
    intro a
    show φ (((φ 1)⁻¹ • (1 : ℝ →L[ℝ] ℝ)) a) = a
    rw [hg, hφa, mul_assoc, mul_comm a (φ 1), ← mul_assoc, inv_mul_cancel₀ h, one_mul]
  · apply ContinuousLinearMap.ext
    intro a
    show ((φ 1)⁻¹ • (1 : ℝ →L[ℝ] ℝ)) (φ a) = a
    rw [hg, hφa a, mul_comm a (φ 1), ← mul_assoc, inv_mul_cancel₀ h, one_mul]

/-- **The crossing time of a transversally crossed level set is smooth.**

Let `V` be a `C^∞` section of the tangent bundle of `M` and `Φ` a jointly `C^∞` global flow of the
constant-in-time field `V` (`Φ s s x = x`, and `τ ↦ Φ s τ x` has derivative `1 ↦ V (Φ s τ x)`).
Let `F : M → ℝ` be smooth at `x₀` with `mvfderiv I F x₀ (V x₀) ≠ 0`, i.e. `V` is transverse to the
level set `{F = F x₀}` at `x₀`. Then near `x₀` the crossing time of that level set is a smooth
function of the starting point: there is a smooth `t` near `x₀` with `t x₀ = 0` and
`F (Φ 0 (t x) x) = F x₀` for all `x` near `x₀`. -/
theorem crossing_time_smooth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [I.Boundaryless]
    {V : (x : M) → TangentSpace I x} {Φ : ℝ → ℝ → M → M}
    (hV : ContMDiff I (I.prod (modelWithCornersSelf ℝ E)) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : M ↦ (⟨x, V x⟩ : TangentBundle I M)))
    (hΦ : ContMDiff (((modelWithCornersSelf ℝ ℝ).prod (modelWithCornersSelf ℝ ℝ)).prod I) I
      ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : (ℝ × ℝ) × M ↦ Φ q.1.1 q.1.2 q.2))
    (hΦself : ∀ s x, Φ s s x = x)
    (hΦderiv : ∀ s t x, HasMFDerivAt (modelWithCornersSelf ℝ ℝ) I (fun τ : ℝ ↦ Φ s τ x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (V (Φ s t x))))
    {F : M → ℝ} {x₀ : M}
    (hF : ContMDiffAt I (modelWithCornersSelf ℝ ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) F x₀)
    (hFv : mvfderiv I F x₀ (V x₀) ≠ 0) :
    ∃ t : M → ℝ, ContMDiffAt I (modelWithCornersSelf ℝ ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) t x₀ ∧
      t x₀ = 0 ∧ (∀ᶠ x in nhds x₀, F (Φ 0 (t x) x) = F x₀) := by
  -- `x₀` in the chart at `x₀`
  have hy₀ : (extChartAt I x₀).symm ((extChartAt I x₀) x₀) = x₀ :=
    PartialEquiv.left_inv _ (by rw [extChartAt_source]; exact mem_chart_source H x₀)
  -- the chart-coordinate equation solved by the implicit function theorem
  let f : E × ℝ → ℝ := fun p => F (Φ 0 p.2 ((extChartAt I x₀).symm p.1))
  have hfval : f ((extChartAt I x₀) x₀, 0) = F x₀ := by
    show F (Φ 0 0 ((extChartAt I x₀).symm ((extChartAt I x₀) x₀))) = F x₀
    rw [hy₀, hΦself 0 x₀]
  -- `f` is smooth at `(x₀, 0)`: assemble it from the joint smoothness of the flow, the inverse
  -- of the chart and the smoothness of `F`
  have hC : ContDiffAt ℝ ∞ f ((extChartAt I x₀) x₀, 0) := by
    have hsymm : ContMDiffAt 𝓘(ℝ, E) I ∞ (fun y : E ↦ (extChartAt I x₀).symm y)
        (extChartAt I x₀ x₀) := by
      rw [← contMDiffWithinAt_univ, ← ModelWithCorners.range_eq_univ I]
      exact contMDiffWithinAt_extChartAt_symm_range_self x₀
    have hpr1 : ContMDiffAt 𝓘(ℝ, E × ℝ) 𝓘(ℝ,E) ∞ (fun p : E × ℝ ↦ p.1)
        (extChartAt I x₀ x₀, 0) := (contDiff_fst.contDiffAt).contMDiffAt
    have hpr2 : ContMDiffAt 𝓘(ℝ, E × ℝ) 𝓘(ℝ,ℝ) ∞ (fun p : E × ℝ ↦ p.2)
        (extChartAt I x₀ x₀, 0) := (contDiff_snd.contDiffAt).contMDiffAt
    have hsymm' : ContMDiffAt 𝓘(ℝ, E × ℝ) I ∞
        (fun p : E × ℝ ↦ (extChartAt I x₀).symm p.1) (extChartAt I x₀ x₀, 0) :=
      hsymm.comp (extChartAt I x₀ x₀, 0) hpr1
    have hΞ : ContMDiffAt 𝓘(ℝ, E × ℝ) (𝓘(ℝ,ℝ).prod I) ∞
        (fun p : E × ℝ ↦ (p.2, (extChartAt I x₀).symm p.1)) (extChartAt I x₀ x₀, 0) :=
      hpr2.prodMk hsymm'
    have hι1 : ContMDiffAt (𝓘(ℝ,ℝ).prod I) 𝓘(ℝ,ℝ) ∞ (fun p : ℝ × M ↦ (0:ℝ)) (0, x₀) :=
      contMDiffAt_const
    have hι2 : ContMDiffAt (𝓘(ℝ,ℝ).prod I) 𝓘(ℝ,ℝ) ∞ (fun p : ℝ × M ↦ p.1) (0, x₀) :=
      contMDiffAt_fst
    have hι12 : ContMDiffAt (𝓘(ℝ,ℝ).prod I) (𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ)) ∞
        (fun p : ℝ × M ↦ ((0:ℝ), p.1)) (0, x₀) := hι1.prodMk hι2
    have hι3 : ContMDiffAt (𝓘(ℝ,ℝ).prod I) I ∞ (fun p : ℝ × M ↦ p.2) (0, x₀) :=
      contMDiffAt_snd
    have hι : ContMDiffAt (𝓘(ℝ,ℝ).prod I) ((𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ)).prod I) ∞
        (fun p : ℝ × M ↦ (((0:ℝ), p.1), p.2)) (0, x₀) := hι12.prodMk hι3
    have hP0 : ContMDiffAt (𝓘(ℝ,ℝ).prod I) I ∞ (fun p : ℝ × M ↦ Φ 0 p.1 p.2) (0, x₀) :=
      (hΦ.contMDiffAt (x := (((0:ℝ),(0:ℝ)), x₀))).comp (0, x₀) hι
    have hP : ContMDiffAt (𝓘(ℝ,ℝ).prod I) I ∞ (fun p : ℝ × M ↦ Φ 0 p.1 p.2)
        (0, (extChartAt I x₀).symm ((extChartAt I x₀) x₀)) := by rw [hy₀]; exact hP0
    have hΨ : ContMDiffAt 𝓘(ℝ, E × ℝ) I ∞
        (fun p : E × ℝ ↦ Φ 0 p.2 ((extChartAt I x₀).symm p.1)) (extChartAt I x₀ x₀, 0) :=
      hP.comp (extChartAt I x₀ x₀, 0) hΞ
    have hF' : ContMDiffAt I 𝓘(ℝ,ℝ) ∞ F
        (Φ 0 0 ((extChartAt I x₀).symm ((extChartAt I x₀) x₀))) := by
      rw [hy₀, hΦself 0 x₀]; exact hF
    exact (hF'.comp (extChartAt I x₀ x₀, 0) hΨ).contDiffAt
  -- derivative of `F` along the flow line through `x₀` is `mvfderiv I F x₀ (V x₀)`
  have hflow : HasDerivAt (fun s : ℝ ↦ F (Φ 0 s x₀)) (mvfderiv I F x₀ (V x₀)) 0 := by
    have hfl : HasMFDerivAt 𝓘(ℝ,ℝ) I (fun τ : ℝ ↦ Φ 0 τ x₀) 0
        ((1 : ℝ →L[ℝ] ℝ).smulRight (V x₀)) := by
      have h := hΦderiv 0 0 x₀
      rw [hΦself 0 x₀] at h
      exact h
    have hFmd : MDifferentiableAt I 𝓘(ℝ,ℝ) F x₀ := hF.mdifferentiableAt (by simp)
    have hFmd' : HasMFDerivAt I 𝓘(ℝ,ℝ) F (Φ 0 0 x₀) (mfderiv I 𝓘(ℝ,ℝ) F x₀) := by
      rw [hΦself 0 x₀]; exact hFmd.hasMFDerivAt
    have hcomp : HasMFDerivAt 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) (F ∘ fun τ : ℝ ↦ Φ 0 τ x₀) 0
        ((mfderiv I 𝓘(ℝ,ℝ) F x₀) ∘L ((1 : ℝ →L[ℝ] ℝ).smulRight (V x₀))) :=
      hFmd'.comp (0 : ℝ) hfl
    have hCLeq : (mfderiv I 𝓘(ℝ,ℝ) F x₀) ∘L ((1 : ℝ →L[ℝ] ℝ).smulRight (V x₀))
        = (1 : ℝ →L[ℝ] ℝ).smulRight (mvfderiv I F x₀ (V x₀)) := by
      apply ContinuousLinearMap.ext
      intro a
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
        ContinuousLinearMap.one_apply, map_smul]
      rfl
    have hfd : HasFDerivAt (fun s : ℝ ↦ F (Φ 0 s x₀))
        ((1 : ℝ →L[ℝ] ℝ).smulRight (mvfderiv I F x₀ (V x₀))) 0 := by
      rw [← hCLeq]; exact hcomp.hasFDerivAt
    simpa [ContinuousLinearMap.smulRight_apply] using hfd.hasDerivAt
  -- the partial derivative of `f` in the second variable
  have hslice : HasDerivAt (fun s : ℝ ↦ f ((extChartAt I x₀) x₀, s))
      ((fderiv ℝ f ((extChartAt I x₀) x₀, 0)) (0,1)) 0 := by
    have hline : HasFDerivAt (fun s : ℝ ↦ ((extChartAt I x₀) x₀, s))
        (ContinuousLinearMap.inr ℝ E ℝ) 0 := hasFDerivAt_prodMk_right _ _
    have hcomp := ((hC.differentiableAt (by simp)).hasFDerivAt).comp 0 hline
    have hd := hcomp.hasDerivAt
    rwa [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply] at hd
  have hfun : (fun s : ℝ ↦ f ((extChartAt I x₀) x₀, s)) = (fun s : ℝ ↦ F (Φ 0 s x₀)) := by
    funext s
    show F (Φ 0 s ((extChartAt I x₀).symm ((extChartAt I x₀) x₀))) = F (Φ 0 s x₀)
    rw [hy₀]
  -- transversality: the partial derivative is the nonzero number `mvfderiv I F x₀ (V x₀)`
  have hder : (fderiv ℝ f ((extChartAt I x₀) x₀, 0)) (0,1) = mvfderiv I F x₀ (V x₀) := by
    have hflow' : HasDerivAt (fun s : ℝ ↦ f ((extChartAt I x₀) x₀, s))
        (mvfderiv I F x₀ (V x₀)) 0 := by
      rw [hfun]; exact hflow
    exact hslice.unique hflow'
  have hne : (fderiv ℝ f ((extChartAt I x₀) x₀, 0)) (0,1) ≠ 0 := by
    rw [hder]; exact hFv
  have hif : ((fderiv ℝ f ((extChartAt I x₀) x₀, 0)) ∘L
      ContinuousLinearMap.inr ℝ E ℝ).IsInvertible := by
    apply isInvertible_of_apply_one_ne_zero
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]
    exact hne
  -- the implicit function theorem in the chart
  let pn : ∞ ≠ 0 := by simp
  let ψ : E → ℝ := hC.implicitFunction pn hif
  have hψsm : ContDiffAt ℝ ∞ ψ ((extChartAt I x₀) x₀) := hC.contDiffAt_implicitFunction pn hif
  have hψ0 : ψ ((extChartAt I x₀) x₀) = 0 := hC.implicitFunction_apply_self pn hif
  have hψev : ∀ᶠ y in 𝓝 ((extChartAt I x₀) x₀), f (y, ψ y) = f ((extChartAt I x₀) x₀, 0) :=
    hC.eventually_apply_implicitFunction pn hif
  refine ⟨fun x => ψ ((extChartAt I x₀) x), ?_, ?_, ?_⟩
  · exact (hψsm.contMDiffAt).comp x₀ contMDiffAt_extChartAt
  · exact hψ0
  · have hcont : Tendsto (fun x : M => (extChartAt I x₀) x) (𝓝 x₀)
        (𝓝 ((extChartAt I x₀) x₀)) :=
      (continuousAt_extChartAt x₀).tendsto
    filter_upwards [hcont.eventually hψev, chart_source_mem_nhds H x₀] with x hx hxsrc
    have hxinv : (extChartAt I x₀).symm ((extChartAt I x₀) x) = x :=
      PartialEquiv.left_inv _ (by rwa [extChartAt_source])
    have hx' : F (Φ 0 (ψ ((extChartAt I x₀) x))
        ((extChartAt I x₀).symm ((extChartAt I x₀) x))) = F x₀ := by
      rw [← hfval]
      exact hx
    rwa [hxinv] at hx'

end Work.Diff.Dim2
