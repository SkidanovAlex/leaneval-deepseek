import Mathlib
import Submission.Work.Diff.C.geoCrux.RadialKit
import Submission.Work.Diff.C.far_sphere_size
import Submission.GExpRay
import Submission.Work.Diff.C.ray_minimising
import Submission.CutWitness
import Submission.Commons.Geometry.Manifold.Tangent.mvfderiv_comp_curve

set_option backward.isDefEq.respectTransparency.types false

/-!
# `CutTimeGeProp`: no cut point in the closed ball of radius `π - arccos (1-c)`

This file proves `Work.Diff.C.GeoCrux.CutTimeGeProp` by the ODE/Grönwall route documented in
`RadialKit.lean`.

The scalar Grönwall step is isolated first (`eq_zero_of_deriv_le_mul`), then the geometric inputs.
-/

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.C.geoCrux

/-! ## The scalar Grönwall step -/

/-- **A nonnegative function with `Ψ(t₁) = 0` and `Ψ' ≤ K Ψ` vanishes identically.**

Proof: `t ↦ Ψ t * exp (-(K * t))` is antitone on `[t₁,T]` (its derivative is
`(Ψ' - K Ψ) e^{-Kt} ≤ 0`), so it is `≤ 0` everywhere, whence `Ψ ≤ 0`. -/
theorem eq_zero_of_deriv_le_mul
    {Ψ : ℝ → ℝ} {K t₁ T : ℝ} (ht₁T : t₁ < T)
    (hcont : ContinuousOn Ψ (Set.Icc t₁ T))
    (hdiff : ∀ t ∈ Set.Ioo t₁ T, DifferentiableAt ℝ Ψ t)
    (hderiv : ∀ t ∈ Set.Ioo t₁ T, deriv Ψ t ≤ K * Ψ t)
    (hnn : ∀ t ∈ Set.Icc t₁ T, 0 ≤ Ψ t) (h₁ : Ψ t₁ = 0) :
    ∀ t ∈ Set.Icc t₁ T, Ψ t = 0 := by
  set g : ℝ → ℝ := fun s => Real.exp (-K * s) with hg
  have hg_cont : Continuous g :=
    Real.continuous_exp.comp (continuous_const.mul continuous_id)
  have hg_deriv : ∀ t : ℝ, HasDerivAt g (g t * (-K)) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => -K * s) (-K) t := by
      simpa using (hasDerivAt_id t).const_mul (-K)
    exact h1.exp
  have hφderiv : ∀ t ∈ Set.Ioo t₁ T, deriv (Ψ * g) t ≤ 0 := by
    intro t ht
    have hψd : HasDerivAt Ψ (deriv Ψ t) t := (hdiff t ht).hasDerivAt
    have h := hψd.mul (hg_deriv t)
    rw [h.deriv]
    have hb := hderiv t ht
    have hgt : 0 < g t := Real.exp_pos _
    have hvv : deriv Ψ t * g t ≤ K * (Ψ t) * g t :=
      mul_le_mul_of_nonneg_right hb hgt.le
    have hcons : deriv Ψ t * g t + Ψ t * (g t * (-K))
        = (deriv Ψ t - K * Ψ t) * g t := by ring
    rw [hcons]
    nlinarith [hvv, hgt]
  have hφcont : ContinuousOn (Ψ * g) (Set.Icc t₁ T) := hcont.mul hg_cont.continuousOn
  have hφdiff : DifferentiableOn ℝ (Ψ * g) (interior (Set.Icc t₁ T)) := by
    rw [interior_Icc]
    intro t ht
    exact ((hdiff t ht).hasDerivAt.mul (hg_deriv t)).differentiableAt.differentiableWithinAt
  have hanti : AntitoneOn (Ψ * g) (Set.Icc t₁ T) :=
    antitoneOn_of_deriv_nonpos (convex_Icc t₁ T) hφcont hφdiff (by
      rw [interior_Icc]
      exact hφderiv)
  intro t ht
  have hle : (Ψ * g) t ≤ (Ψ * g) t₁ :=
    hanti ⟨le_refl t₁, le_of_lt ht₁T⟩ ht ht.1
  have hval : (Ψ * g) t₁ = 0 := by
    rw [Pi.mul_apply, h₁, zero_mul]
  rw [hval] at hle
  have hnn' := hnn t ht
  have hgt : 0 < g t := Real.exp_pos _
  have hgoal : Ψ t ≤ 0 := by
    by_contra hcon
    rw [not_le] at hcon
    have : (Ψ * g) t = Ψ t * g t := rfl
    nlinarith [hle, hgt, hcon, this]
  linarith

/-- **The scalar `C ≡ 1` step with the sine coefficient.**

If `A ∈ (0,π)` is continuous on `[t₁,T]`, `C` is continuous there with `|C| ≤ 1`, `C t₁ = 1`, and
`(1 - C²)' ≤ (2(1+ε)/sin (A ·))·(1 - C²)` on the interior, then `C ≡ 1` on `[t₁,T]`.

The coefficient is bounded by a *constant* `K` on the interval (its numerator is nonnegative and
`sin ∘ A` is continuous and positive on the compact interval `[t₁,T]`, so it has a positive minimum
`m`, and `2(1+ε)/sin (A t) ≤ 2(1+ε)/m`), so `eq_zero_of_deriv_le_mul` applies. -/
theorem C_eq_one_of_deriv_bound
    {A C : ℝ → ℝ} {ε t₁ T : ℝ} (hε : 0 ≤ ε) (ht₁T : t₁ < T)
    (hAcont : ContinuousOn A (Set.Icc t₁ T)) (hCcont : ContinuousOn C (Set.Icc t₁ T))
    (hApos : ∀ t ∈ Set.Icc t₁ T, 0 < A t) (hApi : ∀ t ∈ Set.Icc t₁ T, A t < Real.pi)
    (hCabs : ∀ t ∈ Set.Icc t₁ T, |C t| ≤ 1) (hCt₁ : C t₁ = 1)
    (hCdiff : ∀ t ∈ Set.Ioo t₁ T, DifferentiableAt ℝ C t)
    (hderiv : ∀ t ∈ Set.Ioo t₁ T, deriv (fun s : ℝ => 1 - C s ^ 2) t
      ≤ (2 * (1 + ε) / Real.sin (A t)) * (1 - C t ^ 2)) :
    ∀ t ∈ Set.Icc t₁ T, C t = 1 := by
  obtain ⟨m, hmpos, hmle⟩ : ∃ m : ℝ, 0 < m ∧ ∀ t ∈ Set.Icc t₁ T, m ≤ Real.sin (A t) := by
    have hcont : ContinuousOn (fun t : ℝ => Real.sin (A t)) (Set.Icc t₁ T) :=
      Real.continuous_sin.comp_continuousOn hAcont
    obtain ⟨t₀, ht₀, hmin⟩ := isCompact_Icc.exists_isMinOn
      ⟨t₁, ⟨le_refl t₁, ht₁T.le⟩⟩ hcont
    exact ⟨Real.sin (A t₀),
      Real.sin_pos_of_pos_of_lt_pi (hApos t₀ ht₀) (hApi t₀ ht₀), fun t ht => hmin ht⟩
  set K : ℝ := 2 * (1 + ε) / m with hK
  have hKb : ∀ t ∈ Set.Ioo t₁ T, 2 * (1 + ε) / Real.sin (A t) ≤ K := by
    intro t ht
    have hmem : t ∈ Set.Icc t₁ T := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    have hs : 0 < Real.sin (A t) :=
      Real.sin_pos_of_pos_of_lt_pi (hApos t hmem) (hApi t hmem)
    rw [hK]
    exact div_le_div_of_nonneg_left (by linarith) hmpos (hmle t hmem)
  have hΨnn : ∀ t ∈ Set.Icc t₁ T, 0 ≤ 1 - C t ^ 2 := by
    intro t ht
    have h := hCabs t ht
    nlinarith [abs_le.mp h]
  have hΨcont : ContinuousOn (fun s : ℝ => 1 - C s ^ 2) (Set.Icc t₁ T) :=
    continuousOn_const.sub (hCcont.pow 2)
  have hΨdiff : ∀ t ∈ Set.Ioo t₁ T, DifferentiableAt ℝ (fun s : ℝ => 1 - C s ^ 2) t := by
    intro t ht
    exact (differentiableAt_const (1 : ℝ)).sub ((hCdiff t ht).pow 2)
  have hbound : ∀ t ∈ Set.Ioo t₁ T, deriv (fun s : ℝ => 1 - C s ^ 2) t ≤ K * (1 - C t ^ 2) := by
    intro t ht
    have h1 := hderiv t ht
    have h2 := hKb t ht
    have h3 : 0 ≤ 1 - C t ^ 2 := hΨnn t ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    nlinarith [h1, h2, h3]
  have hzero : ∀ t ∈ Set.Icc t₁ T, 1 - C t ^ 2 = 0 :=
    eq_zero_of_deriv_le_mul ht₁T hΨcont hΨdiff hbound hΨnn (by rw [hCt₁]; norm_num)
  intro t ht
  have hsq : C t ^ 2 = 1 := by have := hzero t ht; linarith
  rcases eq_or_ne (C t) 1 with h | h
  · exact h
  · have hneg : C t = -1 := (sq_eq_one_iff.mp hsq).resolve_left h
    -- intermediate value: `C` takes the value `0` between `t₁` and `t`
    have hle : t₁ ≤ t := ht.1
    have hcont' : ContinuousOn C (Set.Icc t₁ t) := hCcont.mono (Set.Icc_subset_Icc le_rfl ht.2)
    have hsub := intermediate_value_Icc' hle hcont'
    obtain ⟨s, hs, hszero⟩ := hsub (show (0 : ℝ) ∈ Set.Icc (C t) (C t₁) from by
      rw [Set.mem_Icc, hneg, hCt₁]
      norm_num)
    have hmem : s ∈ Set.Icc t₁ T := ⟨hs.1, le_trans hs.2 ht.2⟩
    have := hzero s hmem
    rw [hszero] at this
    norm_num at this

/-! ## The two geometric inputs along the ray -/

/-- **The distance along a radial ray grows with derivative `⟪∇d, γ'⟫`.** -/
theorem hasDerivAt_rdist_ray
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {c ε₁ : ℝ} (hc : 0 < c) (hc1 : c ≤ 1 / 4) (hε₁ : 0 ≤ ε₁)
    (hnum2 : 4 * ε₁ * Real.pi < c)
    (hsmC : ∀ (q y : M), -1 + c ≤ fcos (I := I) (M := M) q y →
      CMDiffAt ∞ (fcos (I := I) (M := M) q) y)
    (hHess : ∀ q : M, HessBoundRegion (I := I) (M := M) cov c ε₁ (fcos (I := I) (M := M) q))
    (hcont : ∀ q : M, Continuous (fcos (I := I) (M := M) q))
    (hgrad : ∀ (q y : M), -1 + c < fcos (I := I) (M := M) q y →
      Inner.inner ℝ (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) y)
        (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) y)
        = 1 - (fcos (I := I) (M := M) q y) ^ 2)
    (hdiam : ∀ x y : M, rdist (I := I) (M := M) x y ≤ Real.pi)
    {q : M} {ξ : TangentSpace I q} (hξ : Inner.inner ℝ ξ ξ = 1) {t : ℝ} (ht0 : 0 < t)
    (hrd0 : 0 < rdist (I := I) (M := M) q
      (Submission.GlobalExp.GExp (cov := cov) hmet q (t • ξ)))
    (hrd : rdist (I := I) (M := M) q
      (Submission.GlobalExp.GExp (cov := cov) hmet q (t • ξ)) < Real.pi - Real.arccos (1 - c)) :
    HasDerivAt (fun s : ℝ => rdist (I := I) (M := M) q
        (Submission.GlobalExp.GExp (cov := cov) hmet q (s • ξ)))
      (Inner.inner ℝ
        (rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) q z)
          (Submission.GlobalExp.GExp (cov := cov) hmet q (t • ξ)))
        (Submission.Geodesic.curveVelocity (I := I)
          (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (s • ξ)) t)) t := by
  have hξ' : ‖ξ‖ = 1 := by
    have h : ‖ξ‖ ^ 2 = 1 := by rw [← real_inner_self_eq_norm_sq]; exact hξ
    nlinarith [norm_nonneg ξ]
  have hξ0 : ξ ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hξ'; norm_num at hξ'
  set γ : ℝ → M := fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (s • ξ) with hγ
  have hsm : CMDiffAt ∞ (fun z : M ↦ rdist (I := I) (M := M) q z) (γ t) :=
    Work.Diff.C.GeoCrux.rdist_smooth_eikonal (I := I) (M := M) (cov := cov) hmet htor hc hc1
      hε₁ hnum2 hsmC hHess hcont hgrad hdiam q (γ t) hrd0 hrd
  have hgmd : MDifferentiableAt I (𝓘(ℝ, ℝ)) (fun z : M ↦ rdist (I := I) (M := M) q z) (γ t) :=
    hsm.mdifferentiableAt (by simp)
  have hγsm : ContMDiffOn 𝓘(ℝ) I ∞ γ Set.univ :=
    Submission.LensLoop.contMDiffOn_GExp_smul (cov := cov) hmet q hξ0
  have hγmd : MDifferentiableAt 𝓘(ℝ) I γ t :=
    (hγsm.contMDiffAt Filter.univ_mem).mdifferentiableAt (by simp)
  have hcomp : MDifferentiableAt 𝓘(ℝ) (𝓘(ℝ, ℝ))
      ((fun z : M ↦ rdist (I := I) (M := M) q z) ∘ γ) t :=
    hgmd.comp t hγmd
  have hval : deriv ((fun z : M ↦ rdist (I := I) (M := M) q z) ∘ γ) t
      = Inner.inner ℝ
          (rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) q z) (γ t))
          (Submission.Geodesic.curveVelocity (I := I) γ t) := by
    have h := Commons.Geometry.Manifold.Tangent.mvfderiv_comp_curve (I := I)
      (g := fun z : M ↦ rdist (I := I) (M := M) q z) (γ := γ) (t := t) hgmd hγmd
    rw [← h, ← Work.Diff.C.inner_rgrad_mvfderiv_local
      (fun z : M ↦ rdist (I := I) (M := M) q z) (γ t)]
    rfl
  have hd : HasDerivAt ((fun z : M ↦ rdist (I := I) (M := M) q z) ∘ γ)
      (deriv ((fun z : M ↦ rdist (I := I) (M := M) q z) ∘ γ) t) t :=
    (hcomp.differentiableAt).hasDerivAt
  rw [hval] at hd
  exact hd

/-! ## Two algebraic facts about the orthogonal part of `γ'` -/

/-- **The orthogonal part of a unit vector is `1 - C²` long.**

For `g, w` with `⟪g,g⟫ = 1`, `⟪w,w⟫ = 1` and `C = ⟪g,w⟫`, the vector `w - C • g` is orthogonal to `g`
and has squared norm `1 - C²`. -/
theorem inner_perp_self {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (g w : V)
    (C : ℝ) (hg : Inner.inner ℝ g g = 1) (hw : Inner.inner ℝ w w = 1)
    (hC : C = Inner.inner ℝ g w) :
    Inner.inner ℝ (w - C • g) (w - C • g) = 1 - C ^ 2 := by
  have hgw : Inner.inner ℝ g w = C := hC.symm
  have hwg : Inner.inner ℝ w g = C := by rw [real_inner_comm]; exact hgw
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
    hg, hw, hgw, hwg]
  ring

/-- The orthogonal part `w - C • g` is orthogonal to `g`. -/
theorem inner_perp_eq_zero {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (g w : V)
    (C : ℝ) (hg : Inner.inner ℝ g g = 1) (hC : C = Inner.inner ℝ g w) :
    Inner.inner ℝ g (w - C • g) = 0 := by
  simp only [inner_sub_right, real_inner_smul_right, hg, hC]
  ring

/-! ## The eikonal equation holds *eventually* on the region -/

/-- **The gradient of the distance is a unit vector on a neighbourhood.**

If `0 < rdist q x < π - arccos (1-c)` then `⟪∇(rdist q), ∇(rdist q)⟫ = 1` holds on a neighbourhood of
`x`: on the region `{0 < rdist q < π - arccos (1-c)}` the function `fcos q = cos ∘ rdist q` satisfies
the eikonal equation (`hgrad`) and `∇(fcos q) = -sin (rdist q) • ∇(rdist q)`, so
`sin²(rdist q)·⟪∇(rdist q), ∇(rdist q)⟫ = 1 - cos²(rdist q) = sin²(rdist q)`. -/
theorem eventually_eikonal_rdist
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {c ε₁ : ℝ} (hc : 0 < c) (hc1 : c ≤ 1 / 4) (hε₁ : 0 ≤ ε₁)
    (hnum2 : 4 * ε₁ * Real.pi < c)
    (hsmC : ∀ (q y : M), -1 + c ≤ fcos (I := I) (M := M) q y →
      CMDiffAt ∞ (fcos (I := I) (M := M) q) y)
    (hHess : ∀ q : M, HessBoundRegion (I := I) (M := M) cov c ε₁ (fcos (I := I) (M := M) q))
    (hcont : ∀ q : M, Continuous (fcos (I := I) (M := M) q))
    (hgrad : ∀ (q y : M), -1 + c < fcos (I := I) (M := M) q y →
      Inner.inner ℝ (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) y)
        (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) y)
        = 1 - (fcos (I := I) (M := M) q y) ^ 2)
    (hdiam : ∀ x y : M, rdist (I := I) (M := M) x y ≤ Real.pi)
    {q x : M} (hx0 : 0 < rdist (I := I) (M := M) q x)
    (hxρ : rdist (I := I) (M := M) q x < Real.pi - Real.arccos (1 - c)) :
    ∀ᶠ y in 𝓝 x, Inner.inner ℝ
        (rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) q z) y)
        (rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) q z) y) = 1 := by
  have hρπ : Real.pi - Real.arccos (1 - c) ≤ Real.pi := by
    have h : 0 ≤ Real.arccos (1 - c) := Real.arccos_nonneg (1 - c)
    linarith
  have hρcos : Real.cos (Real.pi - Real.arccos (1 - c)) = -1 + c := by
    rw [Real.cos_pi_sub, Real.cos_arccos (by linarith) (by linarith)]
    ring
  have hcont' : Continuous (fun y : M ↦ rdist (I := I) (M := M) q y) :=
    rdist_continuous (I := I) (M := M) q
  have h1 : ∀ᶠ y in 𝓝 x, 0 < rdist (I := I) (M := M) q y :=
    hcont'.continuousAt (isOpen_Ioi.mem_nhds hx0)
  have h2 : ∀ᶠ y in 𝓝 x, rdist (I := I) (M := M) q y < Real.pi - Real.arccos (1 - c) :=
    hcont'.continuousAt (isOpen_Iio.mem_nhds hxρ)
  filter_upwards [h1, h2] with y hy0 hyρ
  have hyπ : rdist (I := I) (M := M) q y < Real.pi := lt_of_lt_of_le hyρ hρπ
  have hsm : CMDiffAt ∞ (fun z : M ↦ rdist (I := I) (M := M) q z) y :=
    Work.Diff.C.GeoCrux.rdist_smooth_eikonal (I := I) (M := M) (cov := cov) hmet htor hc hc1
      hε₁ hnum2 hsmC hHess hcont hgrad hdiam q y hy0 hyρ
  have hfcos_gt : -1 + c < fcos (I := I) (M := M) q y := by
    have hcos : Real.cos (Real.pi - Real.arccos (1 - c)) < Real.cos (rdist (I := I) (M := M) q y) :=
      Real.cos_lt_cos_of_nonneg_of_le_pi hy0.le hρπ hyρ
    rw [hρcos] at hcos
    exact hcos
  have hgf : rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) y
      = (-Real.sin (rdist (I := I) (M := M) q y))
        • rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) q z) y :=
    Work.Diff.C.rgrad_fcos (I := I) (M := M) (q := q) hsm
  have hg := hgrad q y hfcos_gt
  rw [hgf] at hg
  simp only [real_inner_smul_left, real_inner_smul_right] at hg
  have hsin : Real.sin (rdist (I := I) (M := M) q y) ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hy0 hyπ)
  have hfcosval : fcos (I := I) (M := M) q y = Real.cos (rdist (I := I) (M := M) q y) := rfl
  rw [hfcosval] at hg
  have hg' : Real.sin (rdist (I := I) (M := M) q y) ^ 2
      * Inner.inner ℝ (rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) q z) y)
          (rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) q z) y)
      = 1 - Real.cos (rdist (I := I) (M := M) q y) ^ 2 := by
    nlinarith [hg]
  have hkey : Real.sin (rdist (I := I) (M := M) q y) ^ 2
      * Inner.inner ℝ (rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) q z) y)
          (rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) q z) y)
      = Real.sin (rdist (I := I) (M := M) q y) ^ 2 := by
    rw [hg', Real.sin_sq]
  have hss : 0 < Real.sin (rdist (I := I) (M := M) q y) ^ 2 := pow_pos (Real.sin_pos_of_pos_of_lt_pi hy0 hyπ) 2
  nlinarith [hkey, hss]

/-! ## The derivative of `C` along the ray -/

/-- **The derivative of the pairing `C`.**  Along the unit ray `γ t = GExp q (t • ξ)`, the function
`C t = ⟪∇(rdist q)(γ t), γ'(t)⟫` is differentiable at `t` with derivative
`Hess(rdist q)(γ t)(γ'(t), γ'(t))`, whenever `0 < rdist q (γ t) < π - arccos (1-c)`.

(This is the `hCderiv` step isolated out of `deriv_psi_le`, so that the Grönwall assembly can use
the differentiability and continuity of `C` on its own.) -/
theorem hasDerivAt_C
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {c ε₁ : ℝ} (hc : 0 < c) (hc1 : c ≤ 1 / 4) (hε₁ : 0 ≤ ε₁)
    (hnum2 : 4 * ε₁ * Real.pi < c)
    (hsmC : ∀ (q y : M), -1 + c ≤ fcos (I := I) (M := M) q y →
      CMDiffAt ∞ (fcos (I := I) (M := M) q) y)
    (hHess : ∀ q : M, HessBoundRegion (I := I) (M := M) cov c ε₁ (fcos (I := I) (M := M) q))
    (hcont : ∀ q : M, Continuous (fcos (I := I) (M := M) q))
    (hgrad : ∀ (q y : M), -1 + c < fcos (I := I) (M := M) q y →
      Inner.inner ℝ (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) y)
        (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) y)
        = 1 - (fcos (I := I) (M := M) q y) ^ 2)
    (hdiam : ∀ x y : M, rdist (I := I) (M := M) x y ≤ Real.pi)
    {q : M} {ξ : TangentSpace I q} (hξ : Inner.inner ℝ ξ ξ = 1) {t : ℝ} (ht0 : 0 < t)
    (hrd0 : 0 < rdist (I := I) (M := M) q
      (Submission.GlobalExp.GExp (cov := cov) hmet q (t • ξ)))
    (hrd : rdist (I := I) (M := M) q
      (Submission.GlobalExp.GExp (cov := cov) hmet q (t • ξ)) < Real.pi - Real.arccos (1 - c)) :
    HasDerivAt (fun τ : ℝ => Inner.inner ℝ
        (rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) q z)
          (Submission.GlobalExp.GExp (cov := cov) hmet q (τ • ξ)))
        (Submission.Geodesic.curveVelocity (I := I)
          (fun u : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (u • ξ)) τ))
      (Work.Diff.C.rhess cov (fun z : M ↦ rdist (I := I) (M := M) q z)
        (Submission.GlobalExp.GExp (cov := cov) hmet q (t • ξ))
        (Submission.Geodesic.curveVelocity (I := I)
          (fun u : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (u • ξ)) t)
        (Submission.Geodesic.curveVelocity (I := I)
          (fun u : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (u • ξ)) t)) t := by
  classical
  have hξ' : ‖ξ‖ = 1 := by
    have h : ‖ξ‖ ^ 2 = 1 := by rw [← real_inner_self_eq_norm_sq]; exact hξ
    nlinarith [norm_nonneg ξ]
  have hξ0 : ξ ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hξ'; norm_num at hξ'
  set γ : ℝ → M := fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (s • ξ) with hγ
  have hsm : CMDiffAt ∞ (fun z : M ↦ rdist (I := I) (M := M) q z) (γ t) :=
    Work.Diff.C.GeoCrux.rdist_smooth_eikonal (I := I) (M := M) (cov := cov) hmet htor hc hc1
      hε₁ hnum2 hsmC hHess hcont hgrad hdiam q (γ t) hrd0 hrd
  have hγsm : ContMDiffOn 𝓘(ℝ) I ∞ γ Set.univ :=
    Submission.LensLoop.contMDiffOn_GExp_smul (cov := cov) hmet q hξ0
  have hnorm : ‖Submission.Geodesic.curveVelocity (I := I) γ t‖ = 1 := by
    have h := Submission.LensLoop.norm_curveVelocity_GExp_smul_ne (cov := cov) hmet q hξ0
      (s := t) (ne_of_gt ht0)
    rw [hγ]
    rw [h, hξ']
  have hne : Submission.Geodesic.curveVelocity (I := I) γ t ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hnorm; norm_num at hnorm
  have hfd : MDiffAt (T% (rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) q z)))
      (γ t) :=
    (Work.Diff.C.grad_smoothAt (I := I) (F := fun z : M ↦ rdist (I := I) (M := M) q z) (x := γ t)
      hsm).mdifferentiableAt (by simp)
  have hCderiv : HasDerivAt (fun τ : ℝ => Inner.inner ℝ
      (rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) q z) (γ τ))
      (Submission.Geodesic.curveVelocity (I := I) γ τ))
      (Work.Diff.C.rhess cov (fun z : M ↦ rdist (I := I) (M := M) q z) (γ t)
        (Submission.Geodesic.curveVelocity (I := I) γ t)
        (Submission.Geodesic.curveVelocity (I := I) γ t)) t := by
    have h := Work.Diff.C.hasDerivAt_secondDeriv_along_geodesic (cov := cov) hmet
      (V := Set.univ) isOpen_univ (t := t) (by simp) hγsm
      (fun τ _ => Submission.GExpRayZero.isGeodesicAt_GExp_smul_all (cov := cov) hmet q hξ0 τ)
      hne hfd
    have hfun : (fun τ : ℝ => mvfderiv I (fun z : M ↦ rdist (I := I) (M := M) q z) (γ τ)
        (Submission.Geodesic.curveVelocity (I := I) γ τ))
        = fun τ : ℝ => Inner.inner ℝ
            (rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) q z) (γ τ))
            (Submission.Geodesic.curveVelocity (I := I) γ τ) := by
      funext τ
      rw [Work.Diff.C.inner_rgrad_mvfderiv_local]
    rw [hfun] at h
    exact h
  exact hCderiv

/-! ## Step 1: the `Ψ`-derivative bound along the ray -/

/-- **The `1 - C²` derivative bound.**  Along the unit ray `γ t = GExp q (t • ξ)`, with
`C t = ⟪∇(rdist q)(γ t), γ'(t)⟫` and at a time `t` where `0 < rdist q (γ t) < π - arccos (1-c)`,

`(1 - C²)'(t) ≤ (2 (1+ε₁) / sin (rdist q (γ t))) · (1 - C t²)`.

This is the analytic input of the Grönwall step: `C' = Hess(rdist q)(γ',γ')`, the orthogonal part
`γ'⊥ = γ' - C • ∇(rdist q)` (so `rhess_eq_rhess_sub_smul` replaces `γ'` by `γ'⊥` and its squared
length is `1 - C²`), the shape-operator bound on `γ'⊥ ⊥ ∇(rdist q)`, and `|cot| ≤ 1/sin`. -/
theorem deriv_psi_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {c ε₁ : ℝ} (hc : 0 < c) (hc1 : c ≤ 1 / 4) (hε₁ : 0 ≤ ε₁)
    (hnum2 : 4 * ε₁ * Real.pi < c)
    (hsmC : ∀ (q y : M), -1 + c ≤ fcos (I := I) (M := M) q y →
      CMDiffAt ∞ (fcos (I := I) (M := M) q) y)
    (hHess : ∀ q : M, HessBoundRegion (I := I) (M := M) cov c ε₁ (fcos (I := I) (M := M) q))
    (hcont : ∀ q : M, Continuous (fcos (I := I) (M := M) q))
    (hgrad : ∀ (q y : M), -1 + c < fcos (I := I) (M := M) q y →
      Inner.inner ℝ (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) y)
        (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) y)
        = 1 - (fcos (I := I) (M := M) q y) ^ 2)
    (hdiam : ∀ x y : M, rdist (I := I) (M := M) x y ≤ Real.pi)
    {q : M} {ξ : TangentSpace I q} (hξ : Inner.inner ℝ ξ ξ = 1) {t : ℝ} (ht0 : 0 < t)
    (hrd0 : 0 < rdist (I := I) (M := M) q
      (Submission.GlobalExp.GExp (cov := cov) hmet q (t • ξ)))
    (hrd : rdist (I := I) (M := M) q
      (Submission.GlobalExp.GExp (cov := cov) hmet q (t • ξ)) < Real.pi - Real.arccos (1 - c)) :
    deriv (fun s : ℝ => 1 - (Inner.inner ℝ
        (rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) q z)
          (Submission.GlobalExp.GExp (cov := cov) hmet q (s • ξ)))
        (Submission.Geodesic.curveVelocity (I := I)
          (fun u : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (u • ξ)) s)) ^ 2) t
      ≤ (2 * (1 + ε₁) / Real.sin (rdist (I := I) (M := M) q
            (Submission.GlobalExp.GExp (cov := cov) hmet q (t • ξ))))
        * (1 - (Inner.inner ℝ
            (rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) q z)
              (Submission.GlobalExp.GExp (cov := cov) hmet q (t • ξ)))
            (Submission.Geodesic.curveVelocity (I := I)
              (fun u : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (u • ξ)) t)) ^ 2) := by
  classical
  have hξ' : ‖ξ‖ = 1 := by
    have h : ‖ξ‖ ^ 2 = 1 := by rw [← real_inner_self_eq_norm_sq]; exact hξ
    nlinarith [norm_nonneg ξ]
  have hξ0 : ξ ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hξ'; norm_num at hξ'
  set γ : ℝ → M := fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (s • ξ) with hγ
  set d : ℝ := rdist (I := I) (M := M) q (γ t) with hd
  set g : TangentSpace I (γ t) := rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) q z) (γ t)
    with hg
  set w : TangentSpace I (γ t) := Submission.Geodesic.curveVelocity (I := I) γ t with hw
  -- basic facts
  have hsm : CMDiffAt ∞ (fun z : M ↦ rdist (I := I) (M := M) q z) (γ t) :=
    Work.Diff.C.GeoCrux.rdist_smooth_eikonal (I := I) (M := M) (cov := cov) hmet htor hc hc1
      hε₁ hnum2 hsmC hHess hcont hgrad hdiam q (γ t) hrd0 hrd
  have heik : Inner.inner ℝ g g = 1 := by
    have h := Work.Diff.C.rgrad_rdist_eikonal (I := I) (M := M) (cov := cov) hmet htor
      (q := q) (x := γ t) (ne_of_gt hrd0) hsm
    rw [hg]; exact h
  have heik' : ∀ᶠ y in 𝓝 (γ t), Inner.inner ℝ
      (rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) q z) y)
      (rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) q z) y) = 1 :=
    eventually_eikonal_rdist (I := I) (M := M) (cov := cov) hmet htor hc hc1 hε₁ hnum2
      hsmC hHess hcont hgrad hdiam (q := q) (x := γ t) hrd0 hrd
  have hw_unit : Inner.inner ℝ w w = 1 := by
    have h := Submission.LensLoop.norm_curveVelocity_GExp_smul_ne (cov := cov) hmet q hξ0
      (s := t) (ne_of_gt ht0)
    rw [hw, hγ, real_inner_self_eq_norm_sq, h, hξ']
    norm_num
  have hgt0 : 0 < d := by rw [hd]; exact hrd0
  have hdπ : d < Real.pi := by
    have h : Real.pi - Real.arccos (1 - c) ≤ Real.pi := by
      have := Real.arccos_nonneg (1 - c); linarith
    rw [hd]; exact lt_of_lt_of_le hrd h
  -- the derivative of `C`
  have hγsm : ContMDiffOn 𝓘(ℝ) I ∞ γ Set.univ :=
    Submission.LensLoop.contMDiffOn_GExp_smul (cov := cov) hmet q hξ0
  have hne : Submission.Geodesic.curveVelocity (I := I) γ t ≠ 0 := by
    rw [hw] at hw_unit
    intro h0; rw [h0] at hw_unit; norm_num at hw_unit
  have hfd : MDiffAt (T% (rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) q z)))
      (γ t) :=
    (Work.Diff.C.grad_smoothAt (I := I) (F := fun z : M ↦ rdist (I := I) (M := M) q z) (x := γ t)
      hsm).mdifferentiableAt (by simp)
  have hCderiv : HasDerivAt (fun τ : ℝ => Inner.inner ℝ
      (rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) q z) (γ τ))
      (Submission.Geodesic.curveVelocity (I := I) γ τ))
      (Work.Diff.C.rhess cov (fun z : M ↦ rdist (I := I) (M := M) q z) (γ t)
        (Submission.Geodesic.curveVelocity (I := I) γ t)
        (Submission.Geodesic.curveVelocity (I := I) γ t)) t := by
    have h := Work.Diff.C.hasDerivAt_secondDeriv_along_geodesic (cov := cov) hmet
      (V := Set.univ) isOpen_univ (t := t) (by simp) hγsm
      (fun τ _ => Submission.GExpRayZero.isGeodesicAt_GExp_smul_all (cov := cov) hmet q hξ0 τ)
      hne hfd
    have hfun : (fun τ : ℝ => mvfderiv I (fun z : M ↦ rdist (I := I) (M := M) q z) (γ τ)
        (Submission.Geodesic.curveVelocity (I := I) γ τ))
        = fun τ : ℝ => Inner.inner ℝ
            (rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) q z) (γ τ))
            (Submission.Geodesic.curveVelocity (I := I) γ τ) := by
      funext τ
      rw [Work.Diff.C.inner_rgrad_mvfderiv_local]
    rw [hfun] at h
    exact h
  -- the shape-operator bound on the orthogonal part
  have hperp_self : Inner.inner ℝ (w - (Inner.inner ℝ g w) • g) (w - (Inner.inner ℝ g w) • g)
      = 1 - (Inner.inner ℝ g w) ^ 2 :=
    inner_perp_self g w _ heik hw_unit rfl
  have hperp_orth : Inner.inner ℝ g (w - (Inner.inner ℝ g w) • g) = 0 :=
    inner_perp_eq_zero g w _ heik rfl
  have hgf : rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) (γ t)
      = (-Real.sin d) • g := by
    have h := Work.Diff.C.rgrad_fcos (I := I) (M := M) (q := q) hsm
    rw [hg, hd]
    exact h
  have hVorth : Inner.inner ℝ (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) (γ t))
      (w - (Inner.inner ℝ g w) • g) = 0 := by
    rw [hgf, real_inner_smul_left, hperp_orth, mul_zero]
  have hshape := Work.Diff.C.rhess_rdist_bound_of_hHess (I := I) (M := M) (cov := cov)
    (c := c) (ε := ε₁) (q := q) (hHess q)
    (x := γ t) (by
      -- -1 + c < fcos q (γ t)
      have hρcos : Real.cos (Real.pi - Real.arccos (1 - c)) = -1 + c := by
        rw [Real.cos_pi_sub, Real.cos_arccos (by linarith) (by linarith)]; ring
      have hcos : Real.cos (Real.pi - Real.arccos (1 - c)) < Real.cos d :=
        Real.cos_lt_cos_of_nonneg_of_le_pi hgt0.le (by
          have h : Real.pi - Real.arccos (1 - c) ≤ Real.pi := by
            have := Real.arccos_nonneg (1 - c); linarith
          exact h) (by rw [hd]; exact hrd)
      rw [hρcos] at hcos
      exact hcos)
    hsm hgt0 hdπ (w - (Inner.inner ℝ g w) • g) hVorth
  -- the decomposition
  have hdecomp : Work.Diff.C.rhess cov (fun z : M ↦ rdist (I := I) (M := M) q z) (γ t) w w
      = Work.Diff.C.rhess cov (fun z : M ↦ rdist (I := I) (M := M) q z) (γ t)
          (w - (Inner.inner ℝ g w) • g) (w - (Inner.inner ℝ g w) • g) := by
    have h := Work.Diff.C.GeoCrux.rhess_eq_rhess_sub_smul (I := I) (M := M) (cov := cov) hmet htor
      (F := fun z : M ↦ rdist (I := I) (M := M) q z) (x := γ t) hsm heik' w
    simpa only [hg] using h
  -- the two-sided bound on `C'`
  have hbound : |Work.Diff.C.rhess cov (fun z : M ↦ rdist (I := I) (M := M) q z) (γ t) w w
      - Real.cot d * (1 - (Inner.inner ℝ g w) ^ 2)|
      ≤ (ε₁ / Real.sin d) * (1 - (Inner.inner ℝ g w) ^ 2) := by
    rw [hdecomp, ← hperp_self]
    exact hshape
  have hsinpos : 0 < Real.sin d := Real.sin_pos_of_pos_of_lt_pi hgt0 hdπ
  have hgn : ‖g‖ = 1 := by
    have h : ‖g‖ ^ 2 = 1 := by rw [← real_inner_self_eq_norm_sq]; exact heik
    nlinarith [norm_nonneg g]
  have hwn : ‖w‖ = 1 := by
    have h : ‖w‖ ^ 2 = 1 := by rw [← real_inner_self_eq_norm_sq]; exact hw_unit
    nlinarith [norm_nonneg w]
  have hCabs : |Inner.inner ℝ g w| ≤ 1 := by
    have h := abs_real_inner_le_norm g w
    rw [hgn, hwn, mul_one] at h
    exact h
  have hPsi_nn : 0 ≤ 1 - (Inner.inner ℝ g w) ^ 2 := by
    nlinarith [abs_le.mp hCabs]
  -- assemble
  have hPsi' : HasDerivAt (fun s : ℝ => 1 - (Inner.inner ℝ
      (rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) q z) (γ s))
      (Submission.Geodesic.curveVelocity (I := I) γ s)) ^ 2)
      (-(2 * Inner.inner ℝ g w) * (Work.Diff.C.rhess cov
        (fun z : M ↦ rdist (I := I) (M := M) q z) (γ t) w w)) t := by
    have h := hCderiv.pow 2
    have h2 := h.const_sub 1
    simpa [hg, hw, mul_comm, mul_left_comm, mul_assoc] using h2
  rw [hPsi'.deriv]
  have hC'b : |Work.Diff.C.rhess cov (fun z : M ↦ rdist (I := I) (M := M) q z) (γ t) w w|
      ≤ (|Real.cot d| + ε₁ / Real.sin d) * (1 - (Inner.inner ℝ g w) ^ 2) := by
    have h := hbound
    have := abs_le.mp h
    have hA : Work.Diff.C.rhess cov (fun z : M ↦ rdist (I := I) (M := M) q z) (γ t) w w
        ≤ Real.cot d * (1 - (Inner.inner ℝ g w) ^ 2)
          + (ε₁ / Real.sin d) * (1 - (Inner.inner ℝ g w) ^ 2) := by linarith [this.2]
    have hB : Real.cot d * (1 - (Inner.inner ℝ g w) ^ 2)
          - (ε₁ / Real.sin d) * (1 - (Inner.inner ℝ g w) ^ 2)
        ≤ Work.Diff.C.rhess cov (fun z : M ↦ rdist (I := I) (M := M) q z) (γ t) w w := by
      linarith [this.1]
    have hcot : |Real.cot d| ≤ 1 / Real.sin d := by
      rw [Real.cot_eq_cos_div_sin, abs_div, abs_of_pos hsinpos]
      rw [div_le_div_iff_of_pos_right hsinpos]
      exact Real.abs_cos_le_one d
    rw [abs_le]
    constructor
    · have hc : -(Real.cot d) ≤ |Real.cot d| := neg_le_abs _
      nlinarith [hB, hPsi_nn, hsinpos, hc]
    · have hc : Real.cot d ≤ |Real.cot d| := le_abs_self _
      nlinarith [hA, hPsi_nn, hc, hε₁, hsinpos]
  have hkey : -(2 * Inner.inner ℝ g w) * (Work.Diff.C.rhess cov
      (fun z : M ↦ rdist (I := I) (M := M) q z) (γ t) w w)
      ≤ (2 * (1 + ε₁) / Real.sin d) * (1 - (Inner.inner ℝ g w) ^ 2) := by
    have h1 : -(2 * Inner.inner ℝ g w) * (Work.Diff.C.rhess cov
        (fun z : M ↦ rdist (I := I) (M := M) q z) (γ t) w w)
        ≤ |2 * Inner.inner ℝ g w| * |Work.Diff.C.rhess cov
            (fun z : M ↦ rdist (I := I) (M := M) q z) (γ t) w w| := by
      have h := le_abs_self (-(2 * Inner.inner ℝ g w) * (Work.Diff.C.rhess cov
        (fun z : M ↦ rdist (I := I) (M := M) q z) (γ t) w w))
      rwa [abs_mul, abs_neg] at h
    have h2 : |2 * Inner.inner ℝ g w| = 2 * |Inner.inner ℝ g w| := by
      rw [abs_mul]; norm_num
    have h3 : |Inner.inner ℝ g w| * |Work.Diff.C.rhess cov
          (fun z : M ↦ rdist (I := I) (M := M) q z) (γ t) w w|
        ≤ 1 * ((|Real.cot d| + ε₁ / Real.sin d) * (1 - (Inner.inner ℝ g w) ^ 2)) :=
      mul_le_mul hCabs hC'b (abs_nonneg _) (by norm_num)
    have hcot' : |Real.cot d| * Real.sin d ≤ 1 := by
      rw [Real.cot_eq_cos_div_sin, abs_div, abs_of_pos hsinpos,
        div_mul_cancel₀ _ (ne_of_gt hsinpos)]
      exact Real.abs_cos_le_one d
    have hkey2 : 2 * (|Real.cot d| + ε₁ / Real.sin d) ≤ 2 * (1 + ε₁) / Real.sin d := by
      have hdiv : ε₁ / Real.sin d * Real.sin d = ε₁ := by
        field_simp
      rw [le_div_iff₀ hsinpos]
      nlinarith [hcot', hdiv]
    have hlast : 2 * (1 * ((|Real.cot d| + ε₁ / Real.sin d)
          * (1 - (Inner.inner ℝ g w) ^ 2)))
        ≤ (2 * (1 + ε₁) / Real.sin d) * (1 - (Inner.inner ℝ g w) ^ 2) := by
      have h := mul_le_mul_of_nonneg_right hkey2 hPsi_nn
      linarith [h]
    calc -(2 * Inner.inner ℝ g w) * (Work.Diff.C.rhess cov
          (fun z : M ↦ rdist (I := I) (M := M) q z) (γ t) w w)
        ≤ |2 * Inner.inner ℝ g w| * |Work.Diff.C.rhess cov
            (fun z : M ↦ rdist (I := I) (M := M) q z) (γ t) w w| := h1
      _ = 2 * |Inner.inner ℝ g w| * |Work.Diff.C.rhess cov
            (fun z : M ↦ rdist (I := I) (M := M) q z) (γ t) w w| := by rw [h2]
      _ = 2 * (|Inner.inner ℝ g w| * |Work.Diff.C.rhess cov
            (fun z : M ↦ rdist (I := I) (M := M) q z) (γ t) w w|) := by ring
      _ ≤ 2 * (1 * ((|Real.cot d| + ε₁ / Real.sin d) * (1 - (Inner.inner ℝ g w) ^ 2))) :=
          mul_le_mul_of_nonneg_left h3 (by norm_num)
      _ ≤ (2 * (1 + ε₁) / Real.sin d) * (1 - (Inner.inner ℝ g w) ^ 2) := hlast
  rw [hd, hg, hw] at hkey
  exact hkey

/-! ## The ray does not overshoot its parameter -/

/-- **`rdist q (GExp q (t • ξ)) ≤ t` for `t ≥ 0` and `‖ξ‖ = 1`.** -/
theorem rdist_GExp_smul_le_ray
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov)
    {q : M} {ξ : TangentSpace I q} (hξ : Inner.inner ℝ ξ ξ = 1) {t : ℝ} (ht : 0 ≤ t) :
    rdist (I := I) (M := M) q
      (Submission.GlobalExp.GExp (cov := cov) hmet q (t • ξ)) ≤ t := by
  have hξn : ‖ξ‖ = 1 := by
    have h : ‖ξ‖ ^ 2 = 1 := by rw [← real_inner_self_eq_norm_sq]; exact hξ
    nlinarith [norm_nonneg ξ]
  have h1 : Manifold.riemannianEDist I q
      (Submission.GlobalExp.GExp (cov := cov) hmet q (t • ξ)) ≤ ENNReal.ofReal t := by
    have h := Submission.CutWitness.edist_GExp_le_norm (cov := cov) hmet (p := q) (t • ξ)
    rw [norm_smul, Real.norm_of_nonneg ht, hξn, mul_one] at h
    exact h
  have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
  rw [ENNReal.toReal_ofReal ht] at h2
  exact h2

/-! ## The assembly of `CutTimeGeProp`

Along the unit ray `γ t = GExp q (t • ξ)`, let `A t = rdist q (γ t)`, `C t = ⟪∇(rdist q)(γ t), γ'(t)⟫`
and `Ψ t = 1 - C t²`.  `A ≤ id`; the profile `C` satisfies the Riccati comparison `Ψ' ≤ (2(1+ε₁)/sin A) Ψ`
wherever `0 < A < ρ₀` (`deriv_psi_le`), and `C = 1` on a short initial interval (`ray_minimising`);
`C_eq_one_of_deriv_bound` then propagates `C ≡ 1`, i.e. `A = id`, up to `ρ₀`. -/

set_option maxHeartbeats 1600000 in
/-- **No cut point in the closed ball of radius `π - arccos (1-c)`.** -/
theorem cutTime_ge : Work.Diff.C.GeoCrux.CutTimeGeProp := by
  intro E iE1 iE2 iE3 iE4 H iH I M iM1 iM2 iM3 iM4 iRB iCM iBL iNE iCS iPC cov iCD
    hmet htor c ε₁ hc hc1 hε₁ hnum2 hsmC hHess hcont hgrad hdiam q ξ hξ
  classical
  have hξn : ‖ξ‖ = 1 := by
    have h : ‖ξ‖ ^ 2 = 1 := by rw [← real_inner_self_eq_norm_sq]; exact hξ
    nlinarith [norm_nonneg ξ]
  have hξ0 : ξ ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hξn; norm_num at hξn
  set ρ₀ : ℝ := Real.pi - Real.arccos (1 - c) with hρ₀def
  have hρ₀pos : 0 < ρ₀ := by
    rw [hρ₀def]
    have h : Real.arccos (1 - c) < Real.pi := Real.arccos_lt_pi.mpr (by linarith)
    linarith
  have hρ₀π : ρ₀ < Real.pi := by
    rw [hρ₀def]
    have h : 0 < Real.arccos (1 - c) := Real.arccos_pos.mpr (by linarith)
    linarith
  -- the ray and its distance profile
  let γ : ℝ → M := fun s => Submission.GlobalExp.GExp (cov := cov) hmet q (s • ξ)
  let A : ℝ → ℝ := fun s => rdist (I := I) (M := M) q (γ s)
  let C : ℝ → ℝ := fun s => Inner.inner ℝ
      (rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) q z) (γ s))
      (Submission.Geodesic.curveVelocity (I := I) γ s)
  have hγc : Continuous γ :=
    (Submission.ConjEnergy.contMDiff_GExp_smul (cov := cov) hmet q hξ0).continuous
  have hAc : Continuous A := (Work.Diff.C.rdist_continuous (I := I) (M := M) q).comp hγc
  have hAle : ∀ t : ℝ, 0 ≤ t → A t ≤ t := fun t ht =>
    rdist_GExp_smul_le_ray (I := I) (M := M) (cov := cov) hmet hξ ht
  -- a short initial interval on which the ray is minimising
  obtain ⟨δ₀, hδ₀pos, hshort⟩ :=
    Work.Diff.C.ray_minimising (I := I) (M := M) cov hmet htor q ξ hξ0
  have hshort' : ∀ s : ℝ, 0 ≤ s → s < δ₀ → A s = s := by
    intro s hs0 hsδ
    have h := hshort s (by rwa [abs_of_nonneg hs0])
    rw [abs_of_nonneg hs0, hξn, mul_one] at h
    have h2 : (Manifold.riemannianEDist I q (γ s)).toReal = (ENNReal.ofReal s).toReal := by
      rw [h]
    rwa [ENNReal.toReal_ofReal hs0] at h2
  set δ : ℝ := min δ₀ ρ₀ / 2 with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]
    have h : 0 < min δ₀ ρ₀ := lt_min hδ₀pos hρ₀pos
    linarith
  have hδleρ : δ ≤ ρ₀ := by
    rw [hδdef]
    have h : min δ₀ ρ₀ ≤ ρ₀ := min_le_right _ _
    linarith
  have hδltδ₀ : δ < δ₀ := by
    rw [hδdef]
    have h1 : 0 < min δ₀ ρ₀ := lt_min hδ₀pos hρ₀pos
    have h2 : min δ₀ ρ₀ ≤ δ₀ := min_le_left _ _
    linarith
  have hδshort : ∀ s ∈ Set.Icc (0 : ℝ) δ, A s = s :=
    fun s hs => hshort' s hs.1 (lt_of_le_of_lt hs.2 hδltδ₀)
  -- the set of times up to which `A = id`
  set S : Set ℝ := {T : ℝ | 0 ≤ T ∧ T ≤ ρ₀ ∧
    ∀ s ∈ Set.Icc (0 : ℝ) T, A s = s} with hSdef
  have hδS : δ ∈ S := ⟨hδpos.le, hδleρ, hδshort⟩
  have hSne : S.Nonempty := ⟨δ, hδS⟩
  have hSbd : BddAbove S := ⟨ρ₀, fun T hT => hT.2.1⟩
  obtain ⟨u, _, huT, huS⟩ := exists_seq_tendsto_sSup hSne hSbd
  have hTmem : sSup S ∈ S := by
    refine ⟨?_, ?_, ?_⟩
    · exact le_trans (huS 0).1 (le_csSup hSbd (huS 0))
    · exact le_of_tendsto_of_tendsto' huT tendsto_const_nhds (fun n => (huS n).2.1)
    · intro s hs
      rcases lt_or_eq_of_le hs.2 with hlt | heq
      · obtain ⟨n, hn⟩ := ((tendsto_order.1 huT).1 s hlt).exists
        exact (huS n).2.2 s ⟨hs.1, le_of_lt hn⟩
      · subst heq
        have h1 : Tendsto (fun n : ℕ => A (u n)) atTop (𝓝 (A (sSup S))) :=
          (hAc.continuousAt.tendsto).comp huT
        have h2 : Tendsto (fun n : ℕ => A (u n)) atTop (𝓝 (sSup S)) := by
          have h3 : (fun n : ℕ => A (u n)) = fun n : ℕ => u n := by
            funext n
            exact (huS n).2.2 (u n) ⟨(huS n).1, le_rfl⟩
          rw [h3]; exact huT
        exact tendsto_nhds_unique h1 h2
  set T : ℝ := sSup S with hTdef
  have hTge0 : 0 ≤ T := hTmem.1
  have hTle : T ≤ ρ₀ := hTmem.2.1
  have hTid : ∀ s ∈ Set.Icc (0 : ℝ) T, A s = s := hTmem.2.2
  have hδleT : δ ≤ T := le_csSup hSbd hδS
  have hTpos : 0 < T := lt_of_lt_of_le hδpos hδleT
  have hTeq : T = ρ₀ := by
    by_contra hne
    have hlt : T < ρ₀ := lt_of_le_of_ne hTle hne
    have hATpos : 0 < A T := by rw [hTid T ⟨hTpos.le, le_rfl⟩]; exact hTpos
    obtain ⟨ε₀, hε₀pos, hε₀⟩ : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ s : ℝ, |s - T| < ε₀ → 0 < A s := by
      have h : ∀ᶠ s in 𝓝 T, 0 < A s := hAc.continuousAt (isOpen_Ioi.mem_nhds hATpos)
      rw [Metric.eventually_nhds_iff] at h
      exact h
    set ε : ℝ := min (ε₀ / 2) ((ρ₀ - T) / 2) with hεdef
    have hεpos : 0 < ε := by
      rw [hεdef]; exact lt_min (by linarith) (by linarith)
    have hεε₀ : ε < ε₀ := by
      rw [hεdef]
      have h : min (ε₀ / 2) ((ρ₀ - T) / 2) ≤ ε₀ / 2 := min_le_left _ _
      linarith
    have hTερ : T + ε < ρ₀ := by
      rw [hεdef]
      have h : min (ε₀ / 2) ((ρ₀ - T) / 2) ≤ (ρ₀ - T) / 2 := min_le_right _ _
      linarith
    have hAposT : ∀ s ∈ Set.Icc T (T + ε), 0 < A s := by
      intro s hs
      refine hε₀ s ?_
      rw [abs_of_nonneg (by linarith [hs.1])]
      linarith [hs.2, hεε₀]
    have h2δ : (0 : ℝ) < δ / 2 := by linarith
    have hδ2T : δ / 2 < T := by linarith
    have hAposI : ∀ s ∈ Set.Icc (δ / 2) (T + ε), 0 < A s := by
      intro s hs
      rcases lt_or_ge s T with hsT | hsT
      · rw [hTid s ⟨by linarith [hs.1], hsT.le⟩]; linarith [hs.1]
      · exact hAposT s ⟨hsT, hs.2⟩
    have hAlt : ∀ s ∈ Set.Icc (δ / 2) (T + ε), A s < ρ₀ := by
      intro s hs
      have h1 := hAle s (by linarith [hs.1])
      linarith [hs.2, hTερ]
    have hDiffC : ∀ s ∈ Set.Icc (δ / 2) (T + ε), DifferentiableAt ℝ C s := by
      intro s hs
      have hs0 : 0 < s := by linarith [hs.1]
      exact (hasDerivAt_C (I := I) (M := M) (cov := cov) hmet htor hc hc1 hε₁ hnum2 hsmC hHess
        hcont hgrad hdiam hξ hs0 (hAposI s hs) (hAlt s hs)).differentiableAt
    have hCcont : ContinuousOn C (Set.Icc (δ / 2) (T + ε)) :=
      fun s hs => (hDiffC s hs).continuousAt.continuousWithinAt
    have hCt₁ : C (δ / 2) = 1 := by
      have hnear : A =ᶠ[𝓝 (δ / 2)] id := by
        filter_upwards [Icc_mem_nhds h2δ hδ2T] with s hs
        exact hTid s hs
      have h1 : HasDerivAt A 1 (δ / 2) :=
        (hasDerivAt_id (δ / 2)).congr_of_eventuallyEq hnear
      have h2 : HasDerivAt A (C (δ / 2)) (δ / 2) :=
        hasDerivAt_rdist_ray (I := I) (M := M) (cov := cov) hmet htor hc hc1 hε₁ hnum2 hsmC hHess
          hcont hgrad hdiam hξ (by linarith [h2δ])
          (hAposI (δ / 2) ⟨le_rfl, by linarith [hTερ, hεpos]⟩)
          (hAlt (δ / 2) ⟨le_rfl, by linarith [hTερ, hεpos]⟩)
      exact h2.unique h1
    have hCabs : ∀ s ∈ Set.Icc (δ / 2) (T + ε), |C s| ≤ 1 := by
      intro s hs
      have hs0 : 0 < s := by linarith [hs.1]
      have hsm : CMDiffAt ∞ (fun z : M ↦ rdist (I := I) (M := M) q z) (γ s) :=
        Work.Diff.C.GeoCrux.rdist_smooth_eikonal (I := I) (M := M) (cov := cov) hmet htor hc hc1
          hε₁ hnum2 hsmC hHess hcont hgrad hdiam q (γ s) (hAposI s hs) (hAlt s hs)
      have heik : Inner.inner ℝ
          (rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) q z) (γ s))
          (rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) q z) (γ s)) = 1 :=
        rgrad_rdist_eikonal (I := I) (M := M) (cov := cov) hmet htor (q := q) (x := γ s)
          (ne_of_gt (hAposI s hs)) hsm
      have hn1 : ‖rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) q z) (γ s)‖
          = 1 := by
        have h : ‖rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) q z) (γ s)‖ ^ 2
            = 1 := by rw [← real_inner_self_eq_norm_sq]; exact heik
        nlinarith [norm_nonneg (rgrad (I := I) (M := M)
          (fun z : M ↦ rdist (I := I) (M := M) q z) (γ s))]
      have hn2 : ‖Submission.Geodesic.curveVelocity (I := I) γ s‖ = 1 := by
        have h := Submission.LensLoop.norm_curveVelocity_GExp_smul_ne (cov := cov) hmet q hξ0
          (s := s) (ne_of_gt hs0)
        rw [h, hξn]
      have h := abs_real_inner_le_norm
        (rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) q z) (γ s))
        (Submission.Geodesic.curveVelocity (I := I) γ s)
      rw [hn1, hn2, mul_one] at h
      exact h
    have hderiv : ∀ s ∈ Set.Ioo (δ / 2) (T + ε),
        deriv (fun s : ℝ => 1 - C s ^ 2) s
          ≤ (2 * (1 + ε₁) / Real.sin (A s)) * (1 - C s ^ 2) := by
      intro s hs
      have hmem : s ∈ Set.Icc (δ / 2) (T + ε) := ⟨hs.1.le, hs.2.le⟩
      exact deriv_psi_le (I := I) (M := M) (cov := cov) hmet htor hc hc1 hε₁ hnum2 hsmC hHess
        hcont hgrad hdiam hξ (by linarith [hs.1]) (hAposI s hmem) (hAlt s hmem)
    have hC1 : ∀ s ∈ Set.Icc (δ / 2) (T + ε), C s = 1 :=
      C_eq_one_of_deriv_bound (A := A) (C := C) (ε := ε₁) hε₁ (by linarith [h2δ, hTερ])
        hAc.continuousOn hCcont hAposI (fun s hs => lt_of_lt_of_le (hAlt s hs) hρ₀π.le)
        hCabs hCt₁ (fun t ht => hDiffC t ⟨ht.1.le, ht.2.le⟩) hderiv
    /- the same statement with the explicit form of `C`, for rewriting -/
    have hC1e : ∀ s ∈ Set.Icc (δ / 2) (T + ε), Inner.inner ℝ
        (rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) q z) (γ s))
        (Submission.Geodesic.curveVelocity (I := I) γ s) = 1 := hC1
    -- `A = id` on `[δ/2, T+ε]`, hence on `[T, T+ε]`
    have hAidT : ∀ s ∈ Set.Icc T (T + ε), A s = s := by
      have hFcont : ContinuousOn (fun s : ℝ => A s - s) (Set.Icc T (T + ε)) :=
        hAc.continuousOn.sub continuousOn_id
      have hFdiff : DifferentiableOn ℝ (fun s : ℝ => A s - s)
          (interior (Set.Icc T (T + ε))) := by
        rw [interior_Icc]
        intro s hs
        have hmem : s ∈ Set.Icc (δ / 2) (T + ε) := ⟨by linarith [hs.1], hs.2.le⟩
        have h := hasDerivAt_rdist_ray (I := I) (M := M) (cov := cov) hmet htor hc hc1 hε₁ hnum2
          hsmC hHess hcont hgrad hdiam hξ (by linarith [hs.1]) (hAposI s hmem) (hAlt s hmem)
        rw [hC1e s hmem] at h
        exact ((h.sub (hasDerivAt_id s)).differentiableAt).differentiableWithinAt
      have hFderiv : ∀ s ∈ interior (Set.Icc T (T + ε)),
          deriv (fun s : ℝ => A s - s) s = 0 := by
        rw [interior_Icc]
        intro s hs
        have hmem : s ∈ Set.Icc (δ / 2) (T + ε) := ⟨by linarith [hs.1], hs.2.le⟩
        have h := hasDerivAt_rdist_ray (I := I) (M := M) (cov := cov) hmet htor hc hc1 hε₁ hnum2
          hsmC hHess hcont hgrad hdiam hξ (by linarith [hs.1]) (hAposI s hmem) (hAlt s hmem)
        rw [hC1e s hmem] at h
        have h2 := (h.sub (hasDerivAt_id s)).deriv
        norm_num at h2
        exact h2
      have hmono : MonotoneOn (fun s : ℝ => A s - s) (Set.Icc T (T + ε)) :=
        monotoneOn_of_deriv_nonneg (convex_Icc T (T + ε)) hFcont hFdiff
          (fun s hs => by have := hFderiv s hs; linarith)
      have hanti : AntitoneOn (fun s : ℝ => A s - s) (Set.Icc T (T + ε)) :=
        antitoneOn_of_deriv_nonpos (convex_Icc T (T + ε)) hFcont hFdiff
          (fun s hs => by have := hFderiv s hs; linarith)
      intro s hs
      have hTs : T ∈ Set.Icc T (T + ε) := ⟨le_rfl, by linarith [hεpos]⟩
      have hFT : A T - T = 0 := by rw [hTid T ⟨hTpos.le, le_rfl⟩]; ring
      have h1 : A s - s ≤ A T - T := hanti hTs hs hs.1
      have h2 : A T - T ≤ A s - s := hmono hTs hs hs.1
      linarith [hFT, h1, h2]
    have hTεS : T + ε ∈ S := by
      refine ⟨by linarith [hTpos, hεpos], hTερ.le, ?_⟩
      intro s hs
      rcases lt_or_ge s T with hsT | hsT
      · exact hTid s ⟨hs.1, hsT.le⟩
      · exact hAidT s ⟨hsT, hs.2⟩
    have hle : T + ε ≤ sSup S := le_csSup hSbd hTεS
    rw [← hTdef] at hle
    linarith [hεpos]
  -- conclusion: the ray is minimising at time `ρ₀`
  have hAρ : A ρ₀ = ρ₀ := by
    rw [← hTeq]
    exact hTid T ⟨hTpos.le, le_rfl⟩
  have hed : Manifold.riemannianEDist I q (γ ρ₀) = ENNReal.ofReal ρ₀ := by
    have hle := Submission.CutWitness.edist_GExp_le_norm (cov := cov) hmet (p := q) (ρ₀ • ξ)
    rw [norm_smul, Real.norm_of_nonneg hρ₀pos.le, hξn, mul_one] at hle
    have hfin : Manifold.riemannianEDist I q (γ ρ₀) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
    have h1 : (Manifold.riemannianEDist I q (γ ρ₀)).toReal = ρ₀ := hAρ
    calc Manifold.riemannianEDist I q (γ ρ₀)
        = ENNReal.ofReal ((Manifold.riemannianEDist I q (γ ρ₀)).toReal) :=
          (ENNReal.ofReal_toReal hfin).symm
      _ = ENNReal.ofReal ρ₀ := by rw [h1]
  have hmem : ρ₀ ∈ Submission.CutTime.minimisingSet (I := I) hmet q ξ := ⟨hρ₀pos.le, hed⟩
  have hgoal : ρ₀ ≤ Submission.CutTime.cutTime (I := I) hmet q ξ :=
    ((Submission.CutTime.mem_minimisingSet_iff (I := I) (cov := cov) hmet htor hξn).mp hmem).2
  exact hgoal

end Work.Diff.C.geoCrux
