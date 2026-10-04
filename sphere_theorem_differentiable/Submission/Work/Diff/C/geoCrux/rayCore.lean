import Mathlib
import Submission.Work.Diff.C.geoCrux.RadialKit
import Submission.Work.Diff.C.far_sphere_size
import Submission.GExpRay
import Submission.Work.Diff.C.ray_minimising
import Submission.CutWitness
import Submission.Commons.Geometry.Manifold.Tangent.mvfderiv_comp_curve

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Analytic core of the Grönwall route for the injectivity radius (frozen snapshot)

**What this file is.**  This is a *frozen, namespace-isolated snapshot* of the analytic core of
`Submission/Work/Diff/C/geoCrux/cutTime_ge.lean` (which is the canonical home of these lemmas and
also proves the `∀ q` cut-time statement `Work.Diff.C.GeoCrux.CutTimeGeProp`).  It was taken because
`Work.Diff.C.geoCrux.injectivity_radius` had to be proved while `cutTime_ge.lean` was being edited by
another agent; freezing the analytic core here decouples the two files.

**Namespace.**  Everything is placed in the nested namespace `Work.Diff.C.geoCrux.RayCore`, so there
are no clashes with the declarations of `Work.Diff.C.geoCrux.*`, and both modules can be imported
together.

**Contents** (all the scalar Grönwall machinery along the unit ray `γ t = GExp q (t • ξ)`):

* `eq_zero_of_deriv_le_mul` — a nonnegative `Ψ` with `Ψ(t₁) = 0`, `Ψ' ≤ K Ψ` vanishes on the
  interval;
* `C_eq_one_of_deriv_bound` — the scalar conclusion `C ≡ 1` from `C(t₁) = 1` and the
  Riccati-type bound `(1 - C²)' ≤ (2(1+ε)/sin (A ·)) (1 - C²)`;
* `hasDerivAt_rdist_ray` — `(rdist q ∘ γ)' = ⟪∇(rdist q)(γ ·), γ'⟫`;
* `hasDerivAt_C` — the derivative of that pairing is `Hess (rdist q)(γ', γ')`;
* `deriv_psi_le` — the Riccati-type bound for `Ψ = 1 - C²`;
* `eventually_eikonal_rdist`, `inner_perp_self`, `inner_perp_eq_zero` — the supporting facts.
-/

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.C.geoCrux

/-! The analytic core is placed in the nested namespace `RayCore` so that it can be used
independently of `Work.Diff.C.geoCrux.cutTime_ge`. -/

namespace RayCore

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

end RayCore

end Work.Diff.C.geoCrux
