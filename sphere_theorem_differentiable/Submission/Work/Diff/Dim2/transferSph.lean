import Mathlib
import Submission.Work.Diff.Dim2.Lib
import Submission.Work.Diff.Dim2.Azim
import Submission.Work.Diff.Dim2.Ambient
import Submission.Work.Diff.Dim2.azimuth
import Submission.Work.Diff.Dim2.lift_monotone
import Submission.Work.Diff.Dim2.flow_of_field
import Submission.Work.Diff.GE.exists_smooth_section_eq_nhds
import Submission.Work.Diff.T.mvfderiv_frameVector_real
import Submission.Work.Diff.C.exists_contMDiff_eventuallyEq_of_contMDiffOn_vec
import Submission.Work.Diff.ODE.flow_smooth
import Submission.Work.Diff.Dim2.circPt_injOn
import Submission.Work.Diff.Dim2.exists_apply_ne_zero_and_apply_ne_zero
import Submission.Work.Diff.Dim2.transfer_convert
import Submission.Work.Diff.Dim2.exists_angle_lift_at
import Submission.Work.Diff.Dim2.exists_global_field_mvfderiv_eq_one
import Submission.Work.Diff.Dim2.exists_curve_of_field
import Submission.Work.Diff.C.mvfderiv_inner_pair

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 800000

namespace Work.Diff.Dim2

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter Submission.Geodesic

/-- **Local smoothness of the transfer map, and non-vanishing of its angular velocity.**

Let `u`, `v : M → S¹` be smooth unit maps on an open set `N` with injective derivatives, and
suppose that on `N` the level sets of `u` and `v` agree (`huv`).  Let `w : ℝ → N` be a choice
function with `u (w θ) = circPt θ` (so that `w` parametrises `N` by the angle of `u`) and let
`κ := v ∘ w` be the induced map of the circle.

Then `κ` is `C^∞` at every `θ₀` and its angular velocity `⟪J (κ θ), κ' θ⟫` never vanishes.

The proof produces, at `x₀ := w θ₀`, a smooth *angle lift* `ϑ` of `u` (with `u = circPt ∘ ϑ` near
`x₀`) and a smooth angle lift `ϑᵥ` of `v`.  A vector `e` on which both `mvfderiv ϑ x₀` and
`mvfderiv ϑᵥ x₀` are non-zero is then normalised so that `mvfderiv ϑ x₀ e = 1`; the global field
`W` with `mvfderiv ϑ (W y) = 1` near `x₀` and its flow line `γ` through `x₀` give a parametrisation
`t ↦ γ t` of a piece of the level set of `u` with `u (γ t) = circPt (θ₀ + t)`, whence
`κ =ᶠ[𝓝 θ₀] v ∘ γ(· - θ₀)` is smooth.  For the angular velocity one uses the angle lift `ϑᵥ` of `v`:
`κ` agrees near `θ₀` with `circPt ∘ (ϑᵥ ∘ γ(· - θ₀))`, so `deriv κ θ₀ = z • rot90 (κ θ₀)` with
`z = deriv (ϑᵥ ∘ γ) 0 = mvfderiv ϑᵥ x₀ e ≠ 0`, whence `angVel κ θ₀ = z ≠ 0`. -/
theorem kappa_local
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [CompactSpace M]
    {N : Set M} (hN : IsOpen N)
    {u v : M → EuclideanSpace ℝ (Fin 2)}
    (hu : ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞ u N)
    (hu1 : ∀ x ∈ N, ‖u x‖ = 1)
    (huinj : ∀ x ∈ N, mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) u x ≠ 0)
    (hv : ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞ v N)
    (hv1 : ∀ x ∈ N, ‖v x‖ = 1)
    (hvinj : ∀ x ∈ N, mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) v x ≠ 0)
    (huv : ∀ x ∈ N, ∀ y ∈ N, u x = u y → v x = v y)
    {w : ℝ → M} (hwN : ∀ θ, w θ ∈ N) (hwu : ∀ θ, u (w θ) = circPt θ)
    {κ : ℝ → EuclideanSpace ℝ (Fin 2)} (hκdef : ∀ θ, κ θ = v (w θ))
    (θ₀ : ℝ) :
    ContDiffAt ℝ ∞ κ θ₀ ∧ angVel κ θ₀ ≠ 0 := by
  classical
  set x₀ : M := w θ₀ with hx₀def
  have hx₀N : x₀ ∈ N := hwN θ₀
  have huw₀ : u x₀ = circPt θ₀ := by rw [hx₀def]; exact hwu θ₀
  -- ## 1.  Angle lifts of `u` and of `v` at `x₀`
  obtain ⟨ϑ, hϑsm, hϑcirc, hϑne⟩ :
      ∃ ϑ : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ ϑ ∧
        (u =ᶠ[𝓝 x₀] fun y => circPt (ϑ y)) ∧ mvfderiv I ϑ x₀ ≠ 0 :=
    exists_angle_lift_at hN hu hu1 huinj hx₀N
  obtain ⟨ϑv, hϑvsm, hϑvcirc, hϑvne⟩ :
      ∃ ϑ : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ ϑ ∧
        (v =ᶠ[𝓝 x₀] fun y => circPt (ϑ y)) ∧ mvfderiv I ϑ x₀ ≠ 0 :=
    exists_angle_lift_at hN hv hv1 hvinj hx₀N
  -- ## 2.  A direction on which both angle derivatives are non-zero
  obtain ⟨e₀, he₀, he₀v⟩ := exists_apply_ne_zero_and_apply_ne_zero hϑne hϑvne
  set e : TangentSpace I x₀ := (mvfderiv I ϑ x₀ e₀)⁻¹ • e₀ with hedef
  have he : mvfderiv I ϑ x₀ e = 1 := by
    rw [hedef, map_smul, smul_eq_mul, inv_mul_cancel₀ he₀]
  have hev : mvfderiv I ϑv x₀ e ≠ 0 := by
    rw [hedef, map_smul, smul_eq_mul]
    exact mul_ne_zero (inv_ne_zero he₀) he₀v
  -- ## 3.  A global field with `mvfderiv ϑ (W y) = 1` near `x₀`, and its flow line through `x₀`
  obtain ⟨W, hWsm, hWx, hW1⟩ :
      ∃ W : (x : M) → TangentSpace I x,
        ContMDiff I (I.prod (modelWithCornersSelf ℝ E)) ∞
          (fun y : M => (⟨y, W y⟩ : Bundle.TotalSpace E (TangentSpace I))) ∧
        W x₀ = e ∧ (∀ᶠ y in 𝓝 x₀, mvfderiv I ϑ y (W y) = 1) :=
    exists_global_field_mvfderiv_eq_one hϑsm he
  obtain ⟨γ, hγsm, hγ0, hγder, hγϑ⟩ :
      ∃ γ : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I ∞ γ ∧ γ 0 = x₀ ∧
        (∀ t : ℝ, HasMFDerivAt 𝓘(ℝ, ℝ) I γ t
          ((1 : ℝ →L[ℝ] ℝ).smulRight (W (γ t)))) ∧
        (∀ᶠ t in 𝓝 (0 : ℝ), ϑ (γ t) = ϑ x₀ + t) :=
    exists_curve_of_field hWsm hϑsm hW1
  -- ## 4.  Along the flow line, `u (γ t) = circPt (θ₀ + t)`
  have hγcont : ContinuousAt γ 0 := hγsm.continuous.continuousAt
  have hγmem : ∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ N := by
    refine hγcont.preimage_mem_nhds ?_
    rw [hγ0]
    exact hN.mem_nhds hx₀N
  obtain ⟨S, hS_mem, hS_eq⟩ := Filter.eventuallyEq_iff_exists_mem.mp hϑcirc
  have hSγ : ∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ S := by
    refine hγcont.preimage_mem_nhds ?_
    rw [hγ0]
    exact hS_mem
  have hx₀S : x₀ ∈ S := mem_of_mem_nhds hS_mem
  have hux₀ : circPt (ϑ x₀) = circPt θ₀ := by
    have h : u x₀ = circPt (ϑ x₀) := by simpa using hS_eq hx₀S
    rw [← h, huw₀]
  have huγ : ∀ᶠ t in 𝓝 (0 : ℝ), u (γ t) = circPt (θ₀ + t) := by
    filter_upwards [hγϑ, hSγ] with t ht hSt
    have h1 : u (γ t) = circPt (ϑ (γ t)) := by simpa using hS_eq hSt
    rw [h1, ht]
    calc circPt (ϑ x₀ + t) = rotE t (circPt (ϑ x₀)) := circPt_add (ϑ x₀) t
      _ = rotE t (circPt θ₀) := by rw [hux₀]
      _ = circPt (θ₀ + t) := (circPt_add θ₀ t).symm
  -- ## 5.  `κ` agrees near `θ₀` with `v ∘ γ(· - θ₀)`
  have hgood : ∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ N ∧ u (γ t) = circPt (θ₀ + t) := by
    filter_upwards [hγmem, huγ] with t h1 h2
    exact ⟨h1, h2⟩
  have hκev : κ =ᶠ[𝓝 θ₀] fun θ => v (γ (θ - θ₀)) := by
    have hcont : ContinuousAt (fun θ : ℝ => θ - θ₀) θ₀ :=
      continuousAt_id.sub continuousAt_const
    have hpre : (fun θ : ℝ => θ - θ₀) ⁻¹'
        {t : ℝ | γ t ∈ N ∧ u (γ t) = circPt (θ₀ + t)} ∈ 𝓝 θ₀ := by
      have hmem0 : {t : ℝ | γ t ∈ N ∧ u (γ t) = circPt (θ₀ + t)} ∈
          𝓝 ((fun θ : ℝ => θ - θ₀) θ₀) := by
        have h0 : (fun θ : ℝ => θ - θ₀) θ₀ = 0 := sub_self θ₀
        rw [h0]
        exact hgood
      exact hcont.preimage_mem_nhds hmem0
    filter_upwards [hpre] with θ hθ
    obtain ⟨hmem, hueq⟩ := hθ
    rw [hκdef θ]
    refine huv _ (hwN θ) _ hmem ?_
    rw [hwu θ]
    exact (hueq.trans (by congr 1; ring)).symm
  -- ## 6.  Smoothness and the derivative of `κ` at `θ₀`
  have hγsh : ContMDiff 𝓘(ℝ, ℝ) I ∞ (fun θ : ℝ => γ (θ - θ₀)) :=
    hγsm.comp (contMDiff_id.sub contMDiff_const)
  have hpt : γ (θ₀ - θ₀) = x₀ := by rw [sub_self, hγ0]
  have hfun_sm : ContDiffAt ℝ ∞ (fun θ : ℝ => v (γ (θ - θ₀))) θ₀ := by
    have h1 : ContMDiffAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞ v (γ (θ₀ - θ₀)) := by
      rw [hpt]
      exact hv.contMDiffAt (hN.mem_nhds hx₀N)
    have h2 : ContMDiffAt 𝓘(ℝ, ℝ) I ∞ (fun θ : ℝ => γ (θ - θ₀)) θ₀ := hγsh.contMDiffAt
    have h3 : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞
        (fun θ : ℝ => v (γ (θ - θ₀))) θ₀ := by
      simpa only [Function.comp_def] using h1.comp θ₀ h2
    exact h3.contDiffAt
  have hκsm : ContDiffAt ℝ ∞ κ θ₀ := hfun_sm.congr_of_eventuallyEq hκev
  -- ## 6b.  The derivative of `κ` and its angular velocity
  have hκθ₀ : κ θ₀ = v x₀ := by rw [hκdef θ₀, hx₀def]
  have hγmd : MDifferentiableAt 𝓘(ℝ) I γ 0 := hγsm.mdifferentiableAt (by simp)
  have hϑvmd0 : MDifferentiableAt I 𝓘(ℝ, ℝ) ϑv (γ 0) := hϑvsm.mdifferentiableAt (by simp)
  have hγd0 : HasMFDerivAt 𝓘(ℝ, ℝ) I γ 0 ((1 : ℝ →L[ℝ] ℝ).smulRight e) := by
    have h := hγder 0
    rwa [hγ0, hWx] at h
  have hvel : (mfderiv 𝓘(ℝ) I γ 0) (1 : ℝ) = e := by
    rw [hγd0.mfderiv]
    show (1 : ℝ →L[ℝ] ℝ) (1 : ℝ) • e = e
    rw [one_apply_eq_self, one_smul]
  -- the derivative of `ϑv ∘ γ` at `0` (scalar chain rule along the flow line)
  have hderiv_v : deriv (fun t : ℝ => ϑv (γ t)) 0 = mvfderiv I ϑv x₀ e := by
    have h := Commons.Geometry.Manifold.Tangent.mvfderiv_comp_curve (I := I) (g := ϑv)
      (γ := γ) (t := 0) hϑvmd0 hγmd
    rw [hvel, hγ0] at h
    simpa only [Function.comp_def] using h.symm
  -- the scalar track `ψ θ = ϑv (γ (θ - θ₀))`
  have hψ_sm : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun θ : ℝ => ϑv (γ (θ - θ₀))) := by
    have h1 : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ ((ϑv ∘ γ) ∘ fun θ : ℝ => θ - θ₀) :=
      (hϑvsm.comp hγsm).comp (contMDiff_id.sub contMDiff_const)
    simpa only [Function.comp_def] using h1
  have hψ_deriv : deriv (fun θ : ℝ => ϑv (γ (θ - θ₀))) θ₀ = mvfderiv I ϑv x₀ e := by
    rw [show deriv (fun θ : ℝ => ϑv (γ (θ - θ₀))) θ₀
        = deriv (fun t : ℝ => ϑv (γ t)) (θ₀ - θ₀) from
      deriv_comp_sub_const (f := fun t : ℝ => ϑv (γ t)) (a := θ₀) (x := θ₀), sub_self]
    exact hderiv_v
  have hψ_cd : ContDiff ℝ ∞ (fun θ : ℝ => ϑv (γ (θ - θ₀))) := hψ_sm.contDiff
  have hψd : HasDerivAt (fun θ : ℝ => ϑv (γ (θ - θ₀))) (mvfderiv I ϑv x₀ e) θ₀ :=
    (((hψ_cd.differentiable (by simp)).differentiableAt.hasFDerivAt).hasDerivAt).congr_deriv
      hψ_deriv
  -- `κ` agrees with `circPt ∘ ψ` near `θ₀`
  have hκψ : κ =ᶠ[𝓝 θ₀] fun θ => circPt (ϑv (γ (θ - θ₀))) := by
    obtain ⟨S, hS_mem, hS_eq⟩ := Filter.eventuallyEq_iff_exists_mem.mp hϑvcirc
    have hγc : ContinuousAt (fun θ : ℝ => γ (θ - θ₀)) θ₀ :=
      (hγsm.continuous.comp (continuous_id.sub continuous_const)).continuousAt
    have hpre : (fun θ : ℝ => γ (θ - θ₀)) ⁻¹' S ∈ 𝓝 θ₀ := by
      refine hγc.preimage_mem_nhds ?_
      have hpt : γ (θ₀ - θ₀) = x₀ := by rw [sub_self, hγ0]
      rw [hpt]
      exact hS_mem
    have hvEv : ∀ᶠ θ in 𝓝 θ₀, v (γ (θ - θ₀)) = circPt (ϑv (γ (θ - θ₀))) := by
      filter_upwards [hpre] with θ hθ
      simpa using (hS_eq hθ)
    filter_upwards [hκev, hvEv] with θ h1 h2
    rw [h1, h2]
  have hchain : HasDerivAt (fun θ : ℝ => circPt (ϑv (γ (θ - θ₀))))
      ((mvfderiv I ϑv x₀ e) • rot90 (circPt (ϑv (γ (θ₀ - θ₀))))) θ₀ := by
    have h := HasDerivAt.scomp (𝕜 := ℝ) (x := θ₀)
      (hasDerivAt_circPt (ϑv (γ (θ₀ - θ₀)))) hψd
    simpa only [Function.comp_def] using h
  have hderivκ : deriv κ θ₀ = (mvfderiv I ϑv x₀ e) • rot90 (κ θ₀) := by
    rw [hκψ.deriv_eq, hchain.deriv]
    congr 2
    rw [sub_self, hγ0]
    exact ((hϑvcirc.eq_of_nhds).symm).trans hκθ₀.symm
  have hangle : angVel κ θ₀ = mvfderiv I ϑv x₀ e := by
    have hκ1 : ‖κ θ₀‖ = 1 := by rw [hκθ₀]; exact hv1 x₀ hx₀N
    rw [angVel, hderivκ, real_inner_smul_right, real_inner_self_eq_norm_sq, norm_rot90, hκ1]
    ring
  -- ## 7.  Non-vanishing of the angular velocity
  exact ⟨hκsm, by rw [hangle]; exact hev⟩

theorem transferSph
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [RegularSpace M]
    {N : Set M} (hN : IsOpen N) (hNc : IsPreconnected N)
    {V : (x : M) → TangentSpace I x}
    (hVsm : ContMDiff I (I.prod (modelWithCornersSelf ℝ E)) ∞
      (fun y : M => (⟨y, V y⟩ : Bundle.TotalSpace E (TangentSpace I))))
    {u v : M → EuclideanSpace ℝ (Fin 2)}
    (hu : ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞ u N)
    (hv : ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞ v N)
    (hu1 : ∀ x ∈ N, ‖u x‖ = 1) (hv1 : ∀ x ∈ N, ‖v x‖ = 1)
    (huV : ∀ x ∈ N, mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) u x (V x) = 0)
    (hvV : ∀ x ∈ N, mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) v x (V x) = 0)
    (huinj : ∀ x ∈ N, mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) u x ≠ 0)
    (hvinj : ∀ x ∈ N, mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) v x ≠ 0)
    (huv : ∀ x ∈ N, ∀ y ∈ N, u x = u y → v x = v y)
    (hvu : ∀ x ∈ N, ∀ y ∈ N, v x = v y → u x = u y)
    (husurj : ∀ z : EuclideanSpace ℝ (Fin 2), ‖z‖ = 1 → ∃ x ∈ N, u x = z) :
    ∃ (s : ℝ) (ρ : ℝ → ℝ), (s = 1 ∨ s = -1) ∧ ContDiff ℝ ∞ ρ ∧
      (∀ θ : ℝ, 0 < deriv ρ θ) ∧
      (∀ θ : ℝ, ρ (θ + 2 * Real.pi) = ρ θ + 2 * Real.pi) ∧
      (∀ x ∈ N, reflE s (v x) = rotE (ρ (argE (u x)) - argE (u x)) (u x)) := by
  classical
  have hsurj : ∀ θ : ℝ, ∃ x : M, x ∈ N ∧ u x = circPt θ :=
    fun θ => husurj (circPt θ) (norm_circPt θ)
  choose w hwN hwu using hsurj
  set κ : ℝ → EuclideanSpace ℝ (Fin 2) := fun θ => v (w θ) with hκ_eq
  have hκvd : ∀ θ : ℝ, κ θ = v (w θ) := fun θ => congrFun hκ_eq θ
  have hκper : ∀ θ : ℝ, κ (θ + 2 * Real.pi) = κ θ := by
    intro θ
    have h : u (w (θ + 2 * Real.pi)) = u (w θ) := by
      rw [hwu (θ + 2 * Real.pi), hwu θ]
      simpa using circPt_periodic θ (1 : ℤ)
    exact huv _ (hwN _) _ (hwN _) h
  have hκunit : ∀ θ : ℝ, ‖κ θ‖ = 1 := fun θ => hv1 (w θ) (hwN θ)
  have hκinj : Set.InjOn κ (Set.Ico 0 (2 * Real.pi)) := by
    intro θ hθ θ' hθ' heq
    have hu' : u (w θ) = u (w θ') := hvu _ (hwN θ) _ (hwN θ') heq
    rw [hwu θ, hwu θ'] at hu'
    exact circPt_injOn hθ hθ' hu'
  have hsm : ContDiff ℝ ∞ κ := by
    rw [contDiff_iff_contDiffAt]
    intro θ
    exact (kappa_local hN hu hu1 huinj hv hv1 hvinj huv hwN hwu hκvd θ).1
  have hang : ∀ θ : ℝ, angVel κ θ ≠ 0 := fun θ =>
    (kappa_local hN hu hu1 huinj hv hv1 hvinj huv hwN hwu hκvd θ).2
  obtain ⟨s, ρ, hs, hρsm, hρd, hρper, hρcs⟩ :=
    lift_monotone hsm hκper hκunit hκinj hang
  have hκevx : ∀ x ∈ N, κ (argE (u x)) = v x := by
    intro x hx
    have h : u (w (argE (u x))) = u x :=
      (hwu (argE (u x))).trans (circPt_argE (hu1 x hx))
    exact huv _ (hwN _) x hx h
  refine ⟨s, ρ, hs, hρsm, hρd, hρper, ?_⟩
  intro x hx
  exact transfer_convert (s := s) (ρ := ρ) (κ := κ) (ux := u x) (vx := v x)
    (hρcs (argE (u x))).1 (hρcs (argE (u x))).2 (hκevx x hx) (hu1 x hx)

end Work.Diff.Dim2
