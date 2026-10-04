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

/-- **The crossing time is locally smooth, with an arbitrary crossing time at the base point.**

This is `Work.Diff.Dim2.crossing_time_smooth` with the implicit-function base point shifted from
`(chart x₀, 0)` to `(chart x₀, t₀)`: the solution of the equation `F (Φ 0 τ y) = F (Φ 0 t₀ x₀)`
satisfies `σ x₀ = t₀`, and only smoothness of `F` *at the crossing point* `Φ 0 t₀ x₀` is needed.
No group law for the flow is used: the shift is absorbed into the base point of the implicit
function theorem. -/
theorem crossing_time_local
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [I.Boundaryless]
    {V : (x : M) → TangentSpace I x} {Φ : ℝ → ℝ → M → M} {F : M → ℝ} {x₀ : M} {t₀ : ℝ}
    (hΦsm : ContMDiff ((𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ)).prod I) I ∞
      (fun q : (ℝ × ℝ) × M => Φ q.1.1 q.1.2 q.2))
    (hΦderiv : ∀ s t x, HasMFDerivAt 𝓘(ℝ,ℝ) I (fun τ : ℝ => Φ s τ x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (V (Φ s t x))))
    (hF : ContMDiffAt I 𝓘(ℝ,ℝ) ∞ F (Φ 0 t₀ x₀))
    (htrans : mvfderiv I F (Φ 0 t₀ x₀) (V (Φ 0 t₀ x₀)) ≠ 0) :
    ∃ σ : M → ℝ, ContMDiffAt I 𝓘(ℝ,ℝ) ∞ σ x₀ ∧ σ x₀ = t₀ ∧
      (∀ᶠ x in 𝓝 x₀, F (Φ 0 (σ x) x) = F (Φ 0 t₀ x₀)) := by
  -- `x₀` in the chart at `x₀`
  have hy₀ : (extChartAt I x₀).symm ((extChartAt I x₀) x₀) = x₀ :=
    PartialEquiv.left_inv _ (by rw [extChartAt_source]; exact mem_chart_source H x₀)
  -- the chart-coordinate equation solved by the implicit function theorem
  let f : E × ℝ → ℝ := fun p => F (Φ 0 p.2 ((extChartAt I x₀).symm p.1))
  have hfval : f ((extChartAt I x₀) x₀, t₀) = F (Φ 0 t₀ x₀) := by
    show F (Φ 0 t₀ ((extChartAt I x₀).symm ((extChartAt I x₀) x₀))) = F (Φ 0 t₀ x₀)
    rw [hy₀]
  -- `f` is smooth at `((chart x₀), t₀)`: assemble it from the joint smoothness of the flow, the
  -- inverse of the chart and the smoothness of `F` at the crossing point
  have hC : ContDiffAt ℝ ∞ f ((extChartAt I x₀) x₀, t₀) := by
    have hsymm : ContMDiffAt 𝓘(ℝ, E) I ∞ (fun y : E ↦ (extChartAt I x₀).symm y)
        (extChartAt I x₀ x₀) := by
      rw [← contMDiffWithinAt_univ, ← ModelWithCorners.range_eq_univ I]
      exact contMDiffWithinAt_extChartAt_symm_range_self x₀
    have hpr1 : ContMDiffAt 𝓘(ℝ, E × ℝ) 𝓘(ℝ,E) ∞ (fun p : E × ℝ ↦ p.1)
        (extChartAt I x₀ x₀, t₀) := (contDiff_fst.contDiffAt).contMDiffAt
    have hpr2 : ContMDiffAt 𝓘(ℝ, E × ℝ) 𝓘(ℝ,ℝ) ∞ (fun p : E × ℝ ↦ p.2)
        (extChartAt I x₀ x₀, t₀) := (contDiff_snd.contDiffAt).contMDiffAt
    have hsymm' : ContMDiffAt 𝓘(ℝ, E × ℝ) I ∞
        (fun p : E × ℝ ↦ (extChartAt I x₀).symm p.1) (extChartAt I x₀ x₀, t₀) :=
      hsymm.comp (extChartAt I x₀ x₀, t₀) hpr1
    have hΞ : ContMDiffAt 𝓘(ℝ, E × ℝ) (𝓘(ℝ,ℝ).prod I) ∞
        (fun p : E × ℝ ↦ (p.2, (extChartAt I x₀).symm p.1)) (extChartAt I x₀ x₀, t₀) :=
      hpr2.prodMk hsymm'
    have hι1 : ContMDiffAt (𝓘(ℝ,ℝ).prod I) 𝓘(ℝ,ℝ) ∞ (fun p : ℝ × M ↦ (0:ℝ)) (t₀, x₀) :=
      contMDiffAt_const
    have hι2 : ContMDiffAt (𝓘(ℝ,ℝ).prod I) 𝓘(ℝ,ℝ) ∞ (fun p : ℝ × M ↦ p.1) (t₀, x₀) :=
      contMDiffAt_fst
    have hι12 : ContMDiffAt (𝓘(ℝ,ℝ).prod I) (𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ)) ∞
        (fun p : ℝ × M ↦ ((0:ℝ), p.1)) (t₀, x₀) := hι1.prodMk hι2
    have hι3 : ContMDiffAt (𝓘(ℝ,ℝ).prod I) I ∞ (fun p : ℝ × M ↦ p.2) (t₀, x₀) :=
      contMDiffAt_snd
    have hι : ContMDiffAt (𝓘(ℝ,ℝ).prod I) ((𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ)).prod I) ∞
        (fun p : ℝ × M ↦ (((0:ℝ), p.1), p.2)) (t₀, x₀) := hι12.prodMk hι3
    have hP0 : ContMDiffAt (𝓘(ℝ,ℝ).prod I) I ∞ (fun p : ℝ × M ↦ Φ 0 p.1 p.2) (t₀, x₀) :=
      (hΦsm.contMDiffAt (x := (((0:ℝ), t₀), x₀))).comp (t₀, x₀) hι
    have hP : ContMDiffAt (𝓘(ℝ,ℝ).prod I) I ∞ (fun p : ℝ × M ↦ Φ 0 p.1 p.2)
        (t₀, (extChartAt I x₀).symm ((extChartAt I x₀) x₀)) := by rw [hy₀]; exact hP0
    have hΨ : ContMDiffAt 𝓘(ℝ, E × ℝ) I ∞
        (fun p : E × ℝ ↦ Φ 0 p.2 ((extChartAt I x₀).symm p.1)) (extChartAt I x₀ x₀, t₀) :=
      hP.comp (extChartAt I x₀ x₀, t₀) hΞ
    have hF' : ContMDiffAt I 𝓘(ℝ,ℝ) ∞ F
        (Φ 0 t₀ ((extChartAt I x₀).symm ((extChartAt I x₀) x₀))) := by
      rw [hy₀]; exact hF
    exact (hF'.comp (extChartAt I x₀ x₀, t₀) hΨ).contDiffAt
  -- derivative of `F` along the flow line through `x₀` is `mvfderiv I F (Φ 0 t₀ x₀) (V _)`
  have hflow : HasDerivAt (fun s : ℝ ↦ F (Φ 0 s x₀))
      (mvfderiv I F (Φ 0 t₀ x₀) (V (Φ 0 t₀ x₀))) t₀ := by
    have hfl : HasMFDerivAt 𝓘(ℝ,ℝ) I (fun τ : ℝ ↦ Φ 0 τ x₀) t₀
        ((1 : ℝ →L[ℝ] ℝ).smulRight (V (Φ 0 t₀ x₀))) := hΦderiv 0 t₀ x₀
    have hFmd : MDifferentiableAt I 𝓘(ℝ,ℝ) F (Φ 0 t₀ x₀) := hF.mdifferentiableAt (by simp)
    have hFmd' : HasMFDerivAt I 𝓘(ℝ,ℝ) F (Φ 0 t₀ x₀)
        (mfderiv I 𝓘(ℝ,ℝ) F (Φ 0 t₀ x₀)) := hFmd.hasMFDerivAt
    have hcomp : HasMFDerivAt 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) (F ∘ fun τ : ℝ ↦ Φ 0 τ x₀) t₀
        ((mfderiv I 𝓘(ℝ,ℝ) F (Φ 0 t₀ x₀)) ∘L ((1 : ℝ →L[ℝ] ℝ).smulRight (V (Φ 0 t₀ x₀)))) :=
      hFmd'.comp t₀ hfl
    have hCLeq : (mfderiv I 𝓘(ℝ,ℝ) F (Φ 0 t₀ x₀)) ∘L
          ((1 : ℝ →L[ℝ] ℝ).smulRight (V (Φ 0 t₀ x₀)))
        = (1 : ℝ →L[ℝ] ℝ).smulRight (mvfderiv I F (Φ 0 t₀ x₀) (V (Φ 0 t₀ x₀))) := by
      apply ContinuousLinearMap.ext
      intro a
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
        ContinuousLinearMap.one_apply, map_smul]
      rfl
    have hfd : HasFDerivAt (fun τ : ℝ ↦ F (Φ 0 τ x₀))
        ((1 : ℝ →L[ℝ] ℝ).smulRight (mvfderiv I F (Φ 0 t₀ x₀) (V (Φ 0 t₀ x₀)))) t₀ := by
      rw [← hCLeq]; exact hcomp.hasFDerivAt
    simpa [ContinuousLinearMap.smulRight_apply] using hfd.hasDerivAt
  -- the partial derivative of `f` in the second variable
  have hslice : HasDerivAt (fun s : ℝ ↦ f ((extChartAt I x₀) x₀, s))
      ((fderiv ℝ f ((extChartAt I x₀) x₀, t₀)) (0,1)) t₀ := by
    have hline : HasFDerivAt (fun s : ℝ ↦ ((extChartAt I x₀) x₀, s))
        (ContinuousLinearMap.inr ℝ E ℝ) t₀ := hasFDerivAt_prodMk_right _ _
    have hcomp := ((hC.differentiableAt (by simp)).hasFDerivAt).comp t₀ hline
    have hd := hcomp.hasDerivAt
    rwa [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply] at hd
  have hfun : (fun s : ℝ ↦ f ((extChartAt I x₀) x₀, s)) = (fun s : ℝ ↦ F (Φ 0 s x₀)) := by
    funext s
    show F (Φ 0 s ((extChartAt I x₀).symm ((extChartAt I x₀) x₀))) = F (Φ 0 s x₀)
    rw [hy₀]
  -- transversality: the partial derivative is the nonzero number `mvfderiv I F (Φ 0 t₀ x₀) (V _)`
  have hder : (fderiv ℝ f ((extChartAt I x₀) x₀, t₀)) (0,1)
      = mvfderiv I F (Φ 0 t₀ x₀) (V (Φ 0 t₀ x₀)) := by
    have hflow' : HasDerivAt (fun s : ℝ ↦ f ((extChartAt I x₀) x₀, s))
        (mvfderiv I F (Φ 0 t₀ x₀) (V (Φ 0 t₀ x₀))) t₀ := by
      rw [hfun]; exact hflow
    exact hslice.unique hflow'
  have hne : (fderiv ℝ f ((extChartAt I x₀) x₀, t₀)) (0,1) ≠ 0 := by
    rw [hder]; exact htrans
  have hif : ((fderiv ℝ f ((extChartAt I x₀) x₀, t₀)) ∘L
      ContinuousLinearMap.inr ℝ E ℝ).IsInvertible := by
    apply isInvertible_of_apply_one_ne_zero
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]
    exact hne
  -- the implicit function theorem in the chart
  let pn : ∞ ≠ 0 := by simp
  let ψ : E → ℝ := hC.implicitFunction pn hif
  have hψsm : ContDiffAt ℝ ∞ ψ ((extChartAt I x₀) x₀) := hC.contDiffAt_implicitFunction pn hif
  have hψ0 : ψ ((extChartAt I x₀) x₀) = t₀ := hC.implicitFunction_apply_self pn hif
  have hψev : ∀ᶠ y in 𝓝 ((extChartAt I x₀) x₀), f (y, ψ y) = f ((extChartAt I x₀) x₀, t₀) :=
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
        ((extChartAt I x₀).symm ((extChartAt I x₀) x))) = F (Φ 0 t₀ x₀) := by
      rw [← hfval]
      exact hx
    rwa [hxinv] at hx'

/-- **The crossing time of a transversally crossed level set is smooth, globally.**

Let `V` be a `C^∞` global vector field on `M`, `Φ` its global flow (`Φ s s x = x` with velocity
`V (Φ s t x)`), `F : M → ℝ` smooth at every point of the level set `{F = ℓ}` and transverse to it
(`mvfderiv I F y (V y) ≠ 0` for `F y = ℓ`).  Suppose that on a set `A` every point has a crossing
time of the level `ℓ` (`hex`) and that this time is unique (`huniq`).  Then the crossing time is a
`C^∞` function on `A`: there is `T` with `ContMDiffOn I 𝓘(ℝ,ℝ) ∞ T A`, `F (Φ 0 (T x) x) = ℓ` for
`x ∈ A`, and `T` is the unique such time.

This is the implicit function theorem, applied at the crossing point `Φ 0 (T x) x ∈ {F = ℓ}` where
`F` *is* smooth (no smoothness of `F` along the whole trajectory is needed), combined with `huniq`
to identify the local solution with the crossing time; smoothness is local, so no connectedness of
`A` is needed.  The boundaryless hypothesis is the one used by the sibling
`Work.Diff.Dim2.crossing_time_smooth` to feed Mathlib's `ContDiffAt.implicitFunction`. -/
theorem crossing_time
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [I.Boundaryless]
    {V : (x : M) → TangentSpace I x} {Φ : ℝ → ℝ → M → M} {F : M → ℝ} {ℓ : ℝ} {A : Set M}
    (hVsm : ContMDiff I (I.prod (modelWithCornersSelf ℝ E)) ∞
      (fun y : M => (⟨y, V y⟩ : TangentBundle I M)))
    (hΦsm : ContMDiff ((𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ)).prod I) I ∞
      (fun q : (ℝ × ℝ) × M => Φ q.1.1 q.1.2 q.2))
    (hΦself : ∀ s x, Φ s s x = x)
    (hΦderiv : ∀ s t x, HasMFDerivAt 𝓘(ℝ,ℝ) I (fun τ : ℝ => Φ s τ x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (V (Φ s t x))))
    (hF : ∀ y : M, F y = ℓ → ContMDiffAt I 𝓘(ℝ,ℝ) ∞ F y)
    (htrans : ∀ y : M, F y = ℓ → mvfderiv I F y (V y) ≠ 0)
    (hex : ∀ x ∈ A, ∃ t : ℝ, F (Φ 0 t x) = ℓ)
    (huniq : ∀ x ∈ A, ∀ t t' : ℝ, F (Φ 0 t x) = ℓ → F (Φ 0 t' x) = ℓ → t = t') :
    ∃ T : M → ℝ, ContMDiffOn I 𝓘(ℝ,ℝ) ∞ T A ∧ (∀ x ∈ A, F (Φ 0 (T x) x) = ℓ) ∧
      (∀ x ∈ A, ∀ t : ℝ, F (Φ 0 t x) = ℓ → t = T x) := by
  classical
  -- a global choice of a crossing time (only its values on `A` matter)
  let T : M → ℝ := fun x => if hx : x ∈ A then Classical.choose (hex x hx) else 0
  have hT : ∀ x ∈ A, F (Φ 0 (T x) x) = ℓ := by
    intro x hx
    have hx' : T x = Classical.choose (hex x hx) := dif_pos hx
    rw [hx']
    exact Classical.choose_spec (hex x hx)
  refine ⟨T, ?_, hT, ?_⟩
  · -- smoothness is local: near every `x ∈ A`, `T` agrees with the smooth local solution
    intro x hx
    have hTl : F (Φ 0 (T x) x) = ℓ := hT x hx
    obtain ⟨σ, hσsm, hσ0, hσev⟩ :=
      crossing_time_local (I := I) hΦsm hΦderiv (hF _ hTl) (htrans _ hTl)
    refine hσsm.contMDiffWithinAt.congr_of_eventuallyEq_of_mem ?_ hx
    filter_upwards [hσev.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with y hy hyA
    rw [hTl] at hy
    exact huniq y hyA (T y) (σ y) (hT y hyA) hy
  · intro x hx t ht
    exact huniq x hx t (T x) ht (hT x hx)

end Work.Diff.Dim2
