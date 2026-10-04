import Mathlib
import Submission.Work.Diff.Dim2.Lib
import Submission.Work.Diff.C.Defs
import Submission.Work.Diff.Dim2.flow_shift

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option backward.isDefEq.respectTransparency false

namespace Work.Diff.Dim2

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter Submission.Geodesic

theorem entry_along_flow
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [RegularSpace M]
    (hdim : 1 ≤ Module.finrank ℝ E)
    {N : Set M} (hN : IsOpen N)
    {V : (x : M) → TangentSpace I x} {Φ : ℝ → ℝ → M → M}
    (hVsm : ContMDiff I (I.prod (modelWithCornersSelf ℝ E)) ∞
      (fun y : M => (⟨y, V y⟩ : Bundle.TotalSpace E (TangentSpace I))))
    (hΦsm : ContMDiff ((𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ)).prod I) I ∞
      (fun q : (ℝ × ℝ) × M => Φ q.1.1 q.1.2 q.2))
    (hΦself : ∀ s x, Φ s s x = x)
    (hΦderiv : ∀ s t x, HasMFDerivAt 𝓘(ℝ,ℝ) I (fun τ : ℝ => Φ s τ x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (V (Φ s t x))))
    (hΦcoc : ∀ s t u x, Φ t u (Φ s t x) = Φ s u x)
    {g : M → ℝ} {c : ℝ}
    {t : M → ℝ} (htsm : ∀ x ∈ N, ContMDiffAt I 𝓘(ℝ,ℝ) ∞ t x)
    {y : M → M} (hysm : ∀ x ∈ N, ContMDiffAt I I ∞ y x)
    (hyform : ∀ x ∈ N, y x = Φ 0 (t x) x)
    (hyc : ∀ x ∈ N, g (y x) = c)
    (hgmd : ∀ x ∈ N, MDifferentiableAt I 𝓘(ℝ,ℝ) g (y x))
    (hgV : ∀ x ∈ N, mfderiv I 𝓘(ℝ,ℝ) g (y x) (V (y x)) = -1) :
    ∀ x ∈ N, mfderiv I I y x (V x) = 0 := by
  -- The `y`-map is the entry map of the level set `{g = c}` along the flow of `V`: `y x` is the
  -- point at flow time `t x` from `x`.  The whole content is that the flow direction is
  -- *tangential* to `{g = c}` at the entry point: flowing a little in the `V`-direction moves the
  -- entry point only to first order in the flow parameter, and hence not along `V`.
  intro x hx
  -- ### the flow curve through `x`
  have hφ_deriv : HasMFDerivAt 𝓘(ℝ,ℝ) I (fun s : ℝ => Φ 0 s x) 0
      ((1 : ℝ →L[ℝ] ℝ).smulRight (V x)) := by
    have h := hΦderiv 0 0 x
    rw [hΦself 0 x] at h
    exact h
  have hφ_tend : Tendsto (fun s : ℝ => Φ 0 s x) (𝓝 0) (𝓝 x) := by
    have h2 : Tendsto (fun s : ℝ => Φ 0 s x) (𝓝 0) (𝓝 ((fun s : ℝ => Φ 0 s x) 0)) :=
      hφ_deriv.continuousAt
    simpa only [hΦself 0 x] using h2
  have hφN : ∀ᶠ s in 𝓝 0, Φ 0 s x ∈ N := hφ_tend.eventually (hN.mem_nhds hx)
  -- ### the shift law: `y (Φ 0 s x) = Φ 0 (s + t (Φ 0 s x)) x` near `s = 0`
  have hΨev : (fun s : ℝ => y (Φ 0 s x)) =ᶠ[𝓝 0]
      (fun s : ℝ => Φ 0 (s + t (Φ 0 s x)) x) := by
    filter_upwards [hφN] with s hs
    rw [hyform _ hs]
    exact flow_shift hVsm hΦsm hΦself hΦderiv s (t (Φ 0 s x)) x
  -- ### the speed of `g` along the flow line through `x` is `-1` at time `t x`
  have hGderiv : HasDerivAt (fun s : ℝ => g (Φ 0 s x)) (-1) (t x) := by
    have h1 : HasMFDerivAt 𝓘(ℝ,ℝ) I (fun τ : ℝ => Φ 0 τ x) (t x)
        ((1 : ℝ →L[ℝ] ℝ).smulRight (V (Φ 0 (t x) x))) := hΦderiv 0 (t x) x
    have hg : HasMFDerivAt I 𝓘(ℝ,ℝ) g (y x) (mfderiv I 𝓘(ℝ,ℝ) g (y x)) :=
      (hgmd x hx).hasMFDerivAt
    have hg' : HasMFDerivAt I 𝓘(ℝ,ℝ) g (Φ 0 (t x) x) (mfderiv I 𝓘(ℝ,ℝ) g (y x)) := by
      rw [← hyform x hx]; exact hg
    have hcomp := hg'.comp (t x) h1
    have hval : ((mfderiv I 𝓘(ℝ,ℝ) g (y x)) ∘L
        ((1 : ℝ →L[ℝ] ℝ).smulRight (V (Φ 0 (t x) x)))) 1 = -1 := by
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
        one_apply_eq_self, one_smul]
      rw [show V (Φ 0 (t x) x) = V (y x) from congrArg V (hyform x hx).symm]
      exact hgV x hx
    exact HasDerivAt.congr_deriv hcomp.hasFDerivAt.hasDerivAt hval
  -- ### the total flow time `s ↦ s + t (Φ 0 s x)` is continuous at `0`
  have hu_tend : Tendsto (fun s : ℝ => s + t (Φ 0 s x)) (𝓝 0) (𝓝 (t x)) := by
    have htc : ContinuousAt t (Φ 0 0 x) := by rw [hΦself 0 x]; exact (htsm x hx).continuousAt
    have h1 : ContinuousAt (fun s : ℝ => t (Φ 0 s x)) 0 :=
      ContinuousAt.comp (f := fun s : ℝ => Φ 0 s x) (x := (0 : ℝ)) htc hφ_deriv.continuousAt
    have h2 : ContinuousAt (fun s : ℝ => s + t (Φ 0 s x)) 0 := continuousAt_id.add h1
    have h3 : Tendsto (fun s : ℝ => s + t (Φ 0 s x)) (𝓝 0)
        (𝓝 ((fun s : ℝ => s + t (Φ 0 s x)) 0)) := h2
    simpa only [zero_add, hΦself 0 x] using h3
  -- transversality: the level `{g = c}` is crossed only at the point `t x` on the flow line
  have hne : ∀ᶠ z in 𝓝 (t x), z ≠ t x → g (Φ 0 z x) ≠ c := by
    have h : ∀ᶠ z in 𝓝[≠] (t x), g (Φ 0 z x) ≠ c :=
      hGderiv.eventually_ne (by norm_num)
    rwa [eventually_nhdsWithin_iff] at h
  have hGeq : ∀ᶠ s in 𝓝 0, g (Φ 0 (s + t (Φ 0 s x)) x) = c := by
    filter_upwards [hΨev, hφN] with s hs hsN
    rw [← hs, hyc _ hsN]
  -- hence the total flow time is constantly `t x` near `0`
  have hu_const : ∀ᶠ s in 𝓝 0, s + t (Φ 0 s x) = t x := by
    filter_upwards [hu_tend.eventually hne, hGeq] with s hs hs'
    by_contra h
    exact hs h hs'
  -- so `y (Φ 0 s x)` is locally constant, and therefore the derivative along `V` vanishes
  have hΨconst : (fun s : ℝ => y (Φ 0 s x)) =ᶠ[𝓝 0] fun _ => y x := by
    filter_upwards [hΨev, hu_const] with s hs hu
    rw [hs, hu]
    exact (hyform x hx).symm
  have hmfΨ : mfderiv 𝓘(ℝ,ℝ) I (fun s : ℝ => y (Φ 0 s x)) 0 = 0 := by
    rw [Filter.EventuallyEq.mfderiv_eq hΨconst, mfderiv_const, ContinuousLinearMap.comp_zero]
  -- ### identify the two `mfderiv`s
  have hymd : MDifferentiableAt I I y (Φ 0 0 x) := by
    rw [hΦself 0 x]; exact (hysm x hx).mdifferentiableAt (by simp)
  have hcomp : mfderiv 𝓘(ℝ,ℝ) I (fun s : ℝ => y (Φ 0 s x)) 0
      = (mfderiv I I y (Φ 0 0 x)) ∘L (mfderiv 𝓘(ℝ,ℝ) I (fun s : ℝ => Φ 0 s x) 0) :=
    mfderiv_comp (0 : ℝ) hymd hφ_deriv.mdifferentiableAt
  have key : ∀ v : TangentSpace I x, ((1 : ℝ →L[ℝ] ℝ).smulRight v) 1 = v := by
    intro v
    rw [ContinuousLinearMap.smulRight_apply, one_apply_eq_self, one_smul]
  have h1val : (mfderiv 𝓘(ℝ,ℝ) I (fun s : ℝ => Φ 0 s x) 0) 1 = V x := by
    rw [hφ_deriv.mfderiv]
    exact key (V x)
  have hypt : mfderiv I I y (Φ 0 0 x) = mfderiv I I y x := by rw [hΦself 0 x]
  have hmfC : (mfderiv 𝓘(ℝ,ℝ) I (fun s : ℝ => y (Φ 0 s x)) 0) 1 = mfderiv I I y x (V x) := by
    rw [hcomp, ContinuousLinearMap.comp_apply, h1val, hypt]
    rfl
  calc mfderiv I I y x (V x)
      = (mfderiv 𝓘(ℝ,ℝ) I (fun s : ℝ => y (Φ 0 s x)) 0) 1 := hmfC.symm
    _ = 0 := by rw [hmfΨ]; rfl

end Work.Diff.Dim2
