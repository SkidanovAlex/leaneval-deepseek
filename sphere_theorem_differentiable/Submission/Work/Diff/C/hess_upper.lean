import Mathlib
import Submission.Work.Diff.C.Defs
import Submission.HingePiece
import Submission.GlobalBM
import Submission.HopfRinow2
import Submission.ChartIndep
import Submission.ChartCurvCont
import Submission.CurveField
import Submission.GExpVelocity
import Submission.GeodesicExtend
import Submission.Minimal
import Submission.EDist
import Submission.Commons.Analysis.Calculus.deriv_deriv_nonneg_of_isLocalMin
import Submission.Commons.Geometry.Manifold.Tangent.mvfderiv_comp_curve
import Submission.Work.Diff.C.hinge_bound
import Submission.Work.Diff.C.dist_lt_pi
import Submission.Work.Diff.C.model_defs
import Submission.Work.Diff.C.modelF_hasDerivAt_zero
import Submission.Work.Diff.C.modelW_hasDerivAt_zero
import Submission.Work.Diff.C.gram_along
import Submission.Work.Diff.C.ray_cos_compare
import Submission.Work.Diff.C.ray_minimising_near_perturbation
import Submission.ConjEnergy
import Submission.GExpRayZero
import Submission.GExpTranslate

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-! Guidance from the project lead (the requester):

CONTEXT: this is one area of the Brendle–Schoen differentiable sphere theorem, driven by the lead. Read HANDOFF.md.
The contracts in Submission/Diff/Interfaces.lean and Submission/Diff/Alg.lean are frozen. Your statement's hypotheses are other
areas' contracts: USE them, do not re-prove them. Go wide: file all the independent sub-lemmas at once,
each with an exact statement, and write your assembly against their statements. If your statement looks
false or unprovable as stated, say so at once in `declare_false` with a precise reason. The lead will fix it.
Part of area C (owner H4). ROUTE: Hess d(V,V) = I(J,J), the index form of the Jacobi field J along the unit-speed minimising geodesic
γ from p to x, with J(0) = 0 and J(d) = V⊥. It is minimising among fields with those boundary values: IndexForm*.lean, IndexMin.lean,
IndexLemma.lean, SecondVariation*.lean.
UPPER (sec ≥ 1): compare with W(t) = (sin t / sin d)·P_t V⊥ (parallel). I(W,W) = ∫ |W'|² − K(W,γ')|W|² ≤ ∫ |W'|² − |W|² = cot d·|V⊥|².
LOWER (sec ≤ 1+η, √(1+η)·d < π): Rauch/Riccati comparison (RauchUpper.lean, RauchCompareK.lean, RauchK.lean). The model is
the space form of curvature 1+η, giving √(1+η)·cot(√(1+η)d)·|V⊥|².
The radial part: Hess d(γ', ·) = 0 since |∇d| = 1.
-/

namespace Work.Diff.C

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg Work.Diff.C
open scoped Manifold ContDiff Bundle Topology
open Bundle Set VectorField CovariantDerivative Metric
open Submission.GlobalExp Submission.Geodesic
open Filter

set_option linter.unusedSectionVars false

section Helpers

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- The tangent-bundle maps of two sections that agree near `x` agree near `x`. -/
lemma tangentMap_eventuallyEq {x : M} {P Q : Π y : M, TangentSpace I y}
    (h : ∀ᶠ y in 𝓝 x, P y = Q y) : (T% P) =ᶠ[𝓝 x] (T% Q) := by
  filter_upwards [h] with y hy
  exact congrArg (fun v : TangentSpace I y => TotalSpace.mk' E y v) hy

/-- **The covariant derivative of the gradient field agrees with that of a smooth field agreeing
with it near `x`.**  This is the bridge between `rhess`, whose definition uses the *global* field
`y ↦ rgrad F y`, and the chart/curve machinery, which works with smooth sections. -/
theorem cov_rgrad_eq_cov_extension
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    {F : M → ℝ} {x : M} {𝒱 : Π y : M, TangentSpace I y}
    (h𝒱sm : CMDiff ∞ (T% 𝒱)) (h𝒱 : ∀ᶠ y in 𝓝 x, 𝒱 y = rgrad (I := I) F y)
    (V : TangentSpace I x) :
    cov (fun y : M ↦ rgrad (I := I) F y) x V = cov 𝒱 x V := by
  have h1 : MDifferentiableAt I I.tangent (T% 𝒱) x := h𝒱sm.mdifferentiableAt (by simp)
  have h2 : MDifferentiableAt I I.tangent (T% (fun y : M ↦ rgrad (I := I) F y)) x :=
    h1.congr_of_eventuallyEq (tangentMap_eventuallyEq (h𝒱.mono fun y hy => hy.symm))
  have heqV : (fun y : M ↦ rgrad (I := I) F y) =ᶠ[𝓝 x] 𝒱 := h𝒱.mono fun y hy => hy.symm
  have h := (cov.isCovariantDerivativeOn (s := Set.univ)).congr_of_eventuallyEq h2 h1
    Filter.univ_mem heqV
  exact congrArg (fun (f : TangentSpace I x →L[ℝ] TangentSpace I x) => f V) h

/-- **`rhess` in terms of a smooth extension of the gradient.** -/
theorem rhess_eq_cov_extension
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    {F : M → ℝ} {x : M} {𝒱 : Π y : M, TangentSpace I y}
    (h𝒱sm : CMDiff ∞ (T% 𝒱)) (h𝒱 : ∀ᶠ y in 𝓝 x, 𝒱 y = rgrad (I := I) F y)
    (V W : TangentSpace I x) :
    rhess cov F x V W = Inner.inner ℝ (cov 𝒱 x V) W := by
  rw [rhess, cov_rgrad_eq_cov_extension h𝒱sm h𝒱 V]

/-- **The second-order comparison bootstrap**: if `f ≤ g` near `0` with `f 0 = g 0` and both have
the same first derivative at `0`, then the second derivative of `f` at `0` is at most that of
`g`. -/
theorem deriv_deriv_le_of_eventually_le {f g : ℝ → ℝ} {c : ℝ}
    (hle : ∀ᶠ s in 𝓝 (0 : ℝ), f s ≤ g s) (h0 : f 0 = g 0)
    (hf : HasDerivAt f c 0) (hg : HasDerivAt g c 0)
    (hf2 : HasDerivAt (deriv f) (deriv (deriv f) 0) 0)
    (hg2 : HasDerivAt (deriv g) (deriv (deriv g) 0) 0)
    (hdiff : ∀ᶠ s in 𝓝 (0 : ℝ), DifferentiableAt ℝ f s ∧ DifferentiableAt ℝ g s) :
    deriv (deriv f) 0 ≤ deriv (deriv g) 0 := by
  have hmin : IsLocalMin (g - f) 0 := by
    filter_upwards [hle] with s hs
    simp only [Pi.sub_apply]
    rw [h0]
    linarith
  have hd1 : HasDerivAt (g - f) 0 0 := by
    have h := hg.sub hf
    simpa using h
  have hd2 : HasDerivAt (deriv (g - f)) (deriv (deriv g) 0 - deriv (deriv f) 0) 0 := by
    have hder : deriv (g - f) =ᶠ[𝓝 (0:ℝ)] (deriv g - deriv f) := by
      filter_upwards [hdiff] with s hs
      exact deriv_sub hs.2 hs.1
    have hsum : HasDerivAt (deriv g - deriv f) (deriv (deriv g) 0 - deriv (deriv f) 0) 0 :=
      hg2.sub hf2
    exact hsum.congr_of_eventuallyEq hder
  have := Commons.Analysis.Calculus.deriv_deriv_nonneg_of_isLocalMin hd1 hd2 hmin
  linarith

/-- **In a tangent space of dimension at most `1`, every vector is a multiple of any nonzero
vector.** -/
theorem exists_smul_eq_of_finrank_le_one {x : M} {W V : TangentSpace I x} (hW : W ≠ 0)
    (hdim : Module.finrank ℝ (TangentSpace I x) ≤ 1) :
    ∃ c : ℝ, V = c • W := by
  have hspan : Module.finrank ℝ (Submodule.span ℝ {W}) = 1 := by
    have h := finrank_span_singleton (K := ℝ) hW
    simpa using h
  have hge : 1 ≤ Module.finrank ℝ (TangentSpace I x) := by
    rw [← hspan]
    exact Submodule.finrank_le _
  have hrank : Module.finrank ℝ (Submodule.span ℝ {W})
      = Module.finrank ℝ (TangentSpace I x) := by
    rw [hspan]; omega
  have heq : Submodule.span ℝ ({W} : Set (TangentSpace I x)) = ⊤ :=
    Submodule.eq_top_of_finrank_eq hrank
  have hV : V ∈ Submodule.span ℝ ({W} : Set (TangentSpace I x)) := by
    rw [heq]; exact Submodule.mem_top
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hV
  exact ⟨c, hc.symm⟩

/-! ### The model function: closed form of the derivative -/

/-- Near `0`, the model cosine `modelG a u κ` avoids `±1` when `a ∈ (0, π)`. -/
lemma eventually_modelG_ne_pm_one {a u κ : ℝ} (ha0 : 0 < a) (haπ : a < Real.pi) :
    ∀ᶠ s in 𝓝 (0 : ℝ), modelG a u κ s ≠ 1 ∧ modelG a u κ s ≠ -1 := by
  have hcos_lt : Real.cos a < 1 := by
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi (x := 0) (y := a) le_rfl haπ.le ha0
    rwa [Real.cos_zero] at h
  have hcos_gt : -1 < Real.cos a := by
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi (x := a) (y := Real.pi) ha0.le le_rfl haπ
    rwa [Real.cos_pi] at h
  have hcont : ContinuousAt (modelG a u κ) 0 := (modelG_hasDerivAt a u κ 0).continuousAt
  filter_upwards [hcont.eventually
      (isOpen_ne.mem_nhds (by rw [modelG_zero]; exact ne_of_lt hcos_lt)),
    hcont.eventually
      (isOpen_ne.mem_nhds (by rw [modelG_zero]; exact ne_of_gt hcos_gt))] with s hs1 hs2
  exact ⟨hs1, hs2⟩

/-- On a neighbourhood of `0`, `deriv (modelF a u κ) = modelW a u κ`. -/
lemma deriv_modelF_eventuallyEq_modelW {a u κ : ℝ} (ha0 : 0 < a) (haπ : a < Real.pi) :
    deriv (modelF a u κ) =ᶠ[𝓝 (0 : ℝ)] modelW a u κ := by
  filter_upwards [eventually_modelG_ne_pm_one (u := u) (κ := κ) ha0 haπ] with s hs
  have hd := (Real.hasDerivAt_arccos hs.2 hs.1).comp s (modelG_hasDerivAt a u κ s)
  have hval : -(1 / Real.sqrt (1 - (modelG a u κ s) ^ 2)) * modelD a u κ s = modelW a u κ s := by
    rw [modelW]; ring
  rw [show modelF a u κ = Real.arccos ∘ modelG a u κ from rfl, hd.deriv, hval]

/-! ### Positivity of the distance where the gradient is a unit vector -/

/-- **Fermat on a ray.**  If `rdist p ·` has its minimum at `x` and is differentiable there, then
its gradient vanishes; contrapositively, a unit gradient forces `rdist p x ≠ 0`. -/
theorem rdist_pos_of_unit_grad
    [I.Boundaryless] [T2Space M] [CompactSpace M] [Nontrivial E]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (p : M) {x : M}
    (hsm : CMDiffAt ∞ (fun z : M ↦ rdist (I := I) p z) x)
    (hunit : Inner.inner ℝ (rgrad (I := I) (rdist (I := I) p) x)
      (rgrad (I := I) (rdist (I := I) p) x) = 1) :
    0 < rdist (I := I) p x := by
  classical
  have hnonneg : ∀ y : M, 0 ≤ rdist (I := I) p y := fun y => ENNReal.toReal_nonneg
  have hgradne : rgrad (I := I) (rdist (I := I) p) x ≠ 0 := by
    intro h
    rw [h, inner_zero_left] at hunit
    exact one_ne_zero hunit.symm
  by_contra hle
  have h0 : rdist (I := I) p x = 0 := le_antisymm (not_lt.mp hle) (hnonneg x)
  have hmin : IsLocalMin (fun z : M ↦ rdist (I := I) p z) x := by
    filter_upwards with y
    rw [h0]
    exact hnonneg y
  set γ : ℝ → M := fun t : ℝ => GExp (cov := cov) hmet x (t • rgrad (I := I) (rdist (I := I) p) x)
    with hγdef
  have hγ0 : γ 0 = x := by simp [hγdef, GExp_zero]
  have hγsm : ContMDiff 𝓘(ℝ) I ∞ γ :=
    Submission.ConjEnergy.contMDiff_GExp_smul (cov := cov) hmet x hgradne
  have hγmd0 : MDifferentiableAt 𝓘(ℝ) I γ 0 := hγsm.mdifferentiableAt (by simp)
  have hFmd : MDifferentiableAt I 𝓘(ℝ,ℝ) (fun z : M ↦ rdist (I := I) p z) (γ 0) := by
    rw [hγ0]; exact hsm.mdifferentiableAt (by simp)
  have hminc : IsLocalMin (fun t : ℝ ↦ rdist (I := I) p (γ t)) 0 := by
    have h := hγsm.continuous.continuousAt.eventually (by rw [hγ0]; exact hmin)
    filter_upwards [h] with t ht
    rwa [hγ0]
  have hd0 : deriv (fun t : ℝ ↦ rdist (I := I) p (γ t)) 0 = 0 := hminc.deriv_eq_zero
  have hd1 : deriv (fun t : ℝ ↦ rdist (I := I) p (γ t)) 0 = 1 := by
    have hγv : curveVelocity (I := I) γ 0 = rgrad (I := I) (rdist (I := I) p) x :=
      Submission.GExpVelocity.curveVelocity_GExp_smul_zero (cov := cov) hmet x hgradne
    have hder : deriv ((fun z : M ↦ rdist (I := I) p z) ∘ γ) 0
        = mvfderiv I (fun z : M ↦ rdist (I := I) p z) (γ 0) (curveVelocity (I := I) γ 0) :=
      (Commons.Geometry.Manifold.Tangent.mvfderiv_comp_curve (I := I)
        (g := fun z : M ↦ rdist (I := I) p z) (γ := γ) (t := 0) hFmd hγmd0).symm
    rw [show (fun t : ℝ ↦ rdist (I := I) p (γ t))
        = (fun z : M ↦ rdist (I := I) p z) ∘ γ from rfl, hder, hγv, hγ0]
    rw [← inner_rgrad_eq_mvfderiv (I := I) (fun z : M ↦ rdist (I := I) p z) x
      (rgrad (I := I) (rdist (I := I) p) x)]
    exact hunit
  rw [hd1] at hd0
  exact one_ne_zero hd0

/-! ### The second derivative of a function along a geodesic -/

/-- **The second derivative of `F` along a geodesic is the Hessian**: for a `C^∞` (at the base
point) function `F` and a global geodesic `γ` with non-vanishing velocity, the derivative of
`deriv (F ∘ γ)` at `t` is `rhess cov F (γ t) (γ' t) (γ' t)`. -/
theorem hasDerivAt_deriv_comp_geodesic
    [I.Boundaryless] [T2Space M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov)
    {F : M → ℝ} {γ : ℝ → M} {t : ℝ}
    (hF : CMDiffAt ∞ F (γ t)) (hγsm : ContMDiff 𝓘(ℝ) I ∞ γ)
    (hne : curveVelocity (I := I) γ t ≠ 0) (hgeo : ∀ τ, IsGeodesicAt cov γ τ) :
    HasDerivAt (deriv (fun s : ℝ => F (γ s)))
      (rhess cov F (γ t) (curveVelocity (I := I) γ t) (curveVelocity (I := I) γ t)) t := by
  have hfd : MDiffAt (T% (rgrad (I := I) F)) (γ t) :=
    (rgrad_contMDiffAt (I := I) (F := F) (x := γ t) hF).mdifferentiableAt (by simp)
  have hmain := hasDerivAt_secondDeriv_along_geodesic (I := I) (M := M) (cov := cov) hmet
    (γ := γ) (V := Set.univ) isOpen_univ (Set.mem_univ t) hγsm.contMDiffOn
    (fun τ _ => hgeo τ) hne hfd
  refine hmain.congr_of_eventuallyEq ?_
  haveI : IsManifold I (1 : ℕ∞ω) M :=
    IsManifold.of_le (I := I) (M := M) (m := (1 : ℕ∞ω)) (n := ∞) (by simp)
  obtain ⟨u, hu, hFu⟩ :=
    (contMDiffAt_iff_contMDiffOn_nhds (I := I) (I' := 𝓘(ℝ,ℝ)) (n := (1 : ℕ∞ω))
      (f := F) (x := γ t) (by simp)).mp (hF.of_le (by simp))
  obtain ⟨v, hvu, hvopen, hxv⟩ := mem_nhds_iff.mp hu
  have hFOn' : MDifferentiableOn I 𝓘(ℝ,ℝ) F v := (hFu.mono hvu).mdifferentiableOn one_ne_zero
  have hγc : ∀ᶠ τ in 𝓝 t, γ τ ∈ v :=
    hγsm.continuous.continuousAt.eventually (hvopen.mem_nhds hxv)
  filter_upwards [hγc] with τ hτ
  have hFmdτ : MDifferentiableAt I 𝓘(ℝ,ℝ) F (γ τ) :=
    hFOn'.mdifferentiableAt (hvopen.mem_nhds hτ)
  have hγmdτ : MDifferentiableAt 𝓘(ℝ) I γ τ := hγsm.mdifferentiableAt (by simp)
  exact (Commons.Geometry.Manifold.Tangent.mvfderiv_comp_curve (I := I) (g := F) (γ := γ)
    (t := τ) hFmdτ hγmdτ).symm

/-! ### The geodesic ray from `x` towards `p` -/

/-- **The ray from `x` towards `p`.**  If `rdist p ·` is smooth at `x` with unit gradient, then for
`t ∈ [0, rdist p x]` the point at distance `t` from `x` on the geodesic ray in the direction
`-∇(rdist p)` is at distance `rdist p x - t` from `p`. -/
theorem rdist_GExp_smul_neg_rgrad
    [I.Boundaryless] [T2Space M] [CompactSpace M] [Nontrivial E] [PathConnectedSpace M]
    [RegularSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    (p : M) {x : M} (hd : 0 < rdist (I := I) p x)
    (hsm : CMDiffAt ∞ (fun z : M ↦ rdist (I := I) p z) x)
    (hunit : Inner.inner ℝ (rgrad (I := I) (rdist (I := I) p) x)
      (rgrad (I := I) (rdist (I := I) p) x) = 1) :
    ∀ t ∈ Set.Icc (0 : ℝ) (rdist (I := I) p x),
      rdist (I := I) p (GExp (cov := cov) hmet x
          (t • (- rgrad (I := I) (rdist (I := I) p) x)))
        = rdist (I := I) p x - t := by
  classical
  set a : ℝ := rdist (I := I) p x with hadef
  have ha : 0 < a := hd
  obtain ⟨v, hvG, hvd⟩ := Submission.HopfRinow.exists_geodesic_riemannianEDist_eq
    (I := I) (cov := cov) hmet htor p x
  have hvlen : a = ‖v‖ := by
    rw [hadef, Work.Diff.C.rdist, hvd, ENNReal.toReal_ofReal (norm_nonneg v)]
  have hvne : v ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hvlen; linarith
  set ξ : TangentSpace I p := Submission.GlobalExp.unitOf v hvne with hξdef
  have hξ1 : ‖ξ‖ = 1 := Submission.GlobalExp.unitOf_norm v hvne
  have hξne : ξ ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hξ1; norm_num at hξ1
  have hdξ : ‖v‖ • ξ = v := by
    simp only [hξdef, Submission.GlobalExp.unitOf, smul_smul,
      mul_inv_cancel₀ (norm_ne_zero_iff.mpr hvne), one_smul]
  have hGx : GExp (cov := cov) hmet p (a • ξ) = x := by
    rw [hvlen, hdξ]; exact hvG
  have hsm' : CMDiffAt ∞ (fun z : M ↦ rdist (I := I) p z)
      (GExp (cov := cov) hmet p ((1 : ℝ) • v)) := by
    rw [one_smul, hvG]; exact hsm
  have hunit' : Inner.inner ℝ
      (rgrad (I := I) (rdist (I := I) p) (GExp (cov := cov) hmet p ((1 : ℝ) • v)))
      (rgrad (I := I) (rdist (I := I) p) (GExp (cov := cov) hmet p ((1 : ℝ) • v))) = 1 := by
    rw [one_smul, hvG]; exact hunit
  have hvd' : Manifold.riemannianEDist I p (GExp (cov := cov) hmet p v)
      = ENNReal.ofReal ‖v‖ := by
    rw [hvG]; exact hvd
  have hvel := curveVelocity_GExp_eq_smul_rgrad (I := I) (M := M) (cov := cov) hmet hvne
    hvd' hsm' hunit'
  have hvel' : curveVelocity (I := I) (fun s : ℝ ↦ GExp (cov := cov) hmet p (s • v)) 1
      = a • rgrad (I := I) (rdist (I := I) p) x := by
    rw [hvel, one_smul, hvG, ← hvlen]
  have hξsm : ContMDiff 𝓘(ℝ) I ∞ (fun r : ℝ ↦ GExp (cov := cov) hmet p (r • ξ)) :=
    Submission.ConjEnergy.contMDiff_GExp_smul (cov := cov) hmet p hξne
  have hcm := Submission.GlobalExp.curveVelocity_comp_mul (I := I)
    (γ := fun r : ℝ ↦ GExp (cov := cov) hmet p (r • ξ)) (c := ‖v‖) (t := 1)
    (hξsm.mdifferentiableAt (by simp))
  have hcurve : (fun s : ℝ ↦ GExp (cov := cov) hmet p ((‖v‖ * s) • ξ))
      = (fun s : ℝ ↦ GExp (cov := cov) hmet p (s • v)) := by
    funext s
    rw [mul_comm ‖v‖ s, mul_smul, hdξ]
  rw [hcurve, mul_one, ← hvlen] at hcm
  have hw : curveVelocity (I := I) (fun r : ℝ ↦ GExp (cov := cov) hmet p (r • ξ)) a
      = rgrad (I := I) (rdist (I := I) p) x := by
    have h2 : a • curveVelocity (I := I) (fun r : ℝ ↦ GExp (cov := cov) hmet p (r • ξ)) a
        = a • rgrad (I := I) (rdist (I := I) p) x := by
      rw [← hcm, hvel']
    exact (smul_right_inj (ne_of_gt ha)).mp h2
  intro t ht
  have hid : GExp (cov := cov) hmet x (t • (- rgrad (I := I) (rdist (I := I) p) x))
      = GExp (cov := cov) hmet p ((a - t) • ξ) := by
    have htrans := Submission.GExpTranslate.GExp_translate (I := I) (cov := cov) hmet p hξ1 a (-t)
    rw [hGx, hw] at htrans
    have e : (-t) • rgrad (I := I) (rdist (I := I) p) x
        = t • (- rgrad (I := I) (rdist (I := I) p) x) := by rw [neg_smul, smul_neg]
    rw [e] at htrans
    simpa only [sub_eq_add_neg] using htrans
  rw [hid]
  have hs : (a - t) / a ∈ Set.Icc (0 : ℝ) 1 := by
    refine ⟨div_nonneg (by linarith [ht.2]) ha.le, div_le_one ha |>.mpr (by linarith [ht.1])⟩
  have h2 := rdist_GExp_smul_of_minimising (I := I) (M := M) (cov := cov) hmet hvne hvd'
    hs.1 hs.2
  have e1 : ((a - t) / a) • v = (a - t) • ξ := by
    rw [← hdξ, smul_smul, ← hvlen]
    congr 1
    field_simp
  have e2 : (a - t) / a * ‖v‖ = a - t := by
    rw [← hvlen]
    field_simp
  rw [e1, e2] at h2
  exact h2

/-- **The geodesic ray from `x` in the direction `-∇(rdist p)` reaches `p`.** -/
theorem GExp_smul_neg_rgrad
    [I.Boundaryless] [T2Space M] [CompactSpace M] [Nontrivial E] [PathConnectedSpace M]
    [RegularSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    (p : M) {x : M} (hd : 0 < rdist (I := I) p x)
    (hsm : CMDiffAt ∞ (fun z : M ↦ rdist (I := I) p z) x)
    (hunit : Inner.inner ℝ (rgrad (I := I) (rdist (I := I) p) x)
      (rgrad (I := I) (rdist (I := I) p) x) = 1) :
    GExp (cov := cov) hmet x
      (rdist (I := I) p x • (- rgrad (I := I) (rdist (I := I) p) x)) = p := by
  have h0 := rdist_GExp_smul_neg_rgrad (I := I) (M := M) (cov := cov) hmet htor p hd hsm hunit
    (rdist (I := I) p x) ⟨ENNReal.toReal_nonneg, le_rfl⟩
  simp only [sub_self] at h0
  obtain ⟨v, hvG, hvd⟩ := Submission.HopfRinow.exists_geodesic_riemannianEDist_eq
    (I := I) (cov := cov) hmet htor p x
  -- the extended distance to `p` is finite
  have hfin : Manifold.riemannianEDist I p
      (GExp (cov := cov) hmet x (rdist (I := I) p x • (- rgrad (I := I) (rdist (I := I) p) x)))
      ≤ ENNReal.ofReal ‖v‖
        + ENNReal.ofReal ‖rdist (I := I) p x • (- rgrad (I := I) (rdist (I := I) p) x)‖ := by
    calc Manifold.riemannianEDist I p
          (GExp (cov := cov) hmet x (rdist (I := I) p x • (- rgrad (I := I) (rdist (I := I) p) x)))
        ≤ Manifold.riemannianEDist I p x
            + Manifold.riemannianEDist I x (GExp (cov := cov) hmet x
                (rdist (I := I) p x • (- rgrad (I := I) (rdist (I := I) p) x))) :=
          Manifold.riemannianEDist_triangle
      _ = ENNReal.ofReal ‖v‖
            + Manifold.riemannianEDist I x (GExp (cov := cov) hmet x
                (rdist (I := I) p x • (- rgrad (I := I) (rdist (I := I) p) x))) := by rw [hvd]
      _ ≤ ENNReal.ofReal ‖v‖
            + ENNReal.ofReal ‖rdist (I := I) p x • (- rgrad (I := I) (rdist (I := I) p) x)‖ :=
          add_le_add le_rfl (Submission.CutWitness.edist_GExp_le_norm (cov := cov) hmet _)
  have hne : Manifold.riemannianEDist I p
      (GExp (cov := cov) hmet x (rdist (I := I) p x • (- rgrad (I := I) (rdist (I := I) p) x)))
      ≠ ⊤ :=
    ne_top_of_le_ne_top (ne_of_lt (ENNReal.add_lt_top.mpr
      ⟨ENNReal.ofReal_lt_top, ENNReal.ofReal_lt_top⟩)) hfin
  have hz : Manifold.riemannianEDist I p
      (GExp (cov := cov) hmet x (rdist (I := I) p x • (- rgrad (I := I) (rdist (I := I) p) x)))
      = 0 := by
    have h1 : (Manifold.riemannianEDist I p
        (GExp (cov := cov) hmet x (rdist (I := I) p x
          • (- rgrad (I := I) (rdist (I := I) p) x)))).toReal = 0 := h0
    rw [← ENNReal.ofReal_toReal hne, h1, ENNReal.ofReal_zero]
  exact ((Submission.EDist.riemannianEDist_eq_zero_iff (I := I)).mp hz).symm

/-! ### The first derivative along a ray of the exponential map -/

/-- **First derivative along a `GExp` ray.**  If `F` is `C^∞` at `x`, then
`s ↦ F (GExp hmet x (s • V))` has derivative `mvfderiv I F x V` at `0`. -/
theorem hasDerivAt_comp_GExp_smul
    [I.Boundaryless] [T2Space M] [CompactSpace M] [Nontrivial E]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) {F : M → ℝ} {x : M} {V : TangentSpace I x}
    (hF : CMDiffAt ∞ F x) :
    HasDerivAt (fun s : ℝ ↦ F (GExp (cov := cov) hmet x (s • V))) (mvfderiv I F x V) 0 := by
  have hFmd : MDifferentiableAt I 𝓘(ℝ,ℝ) F x := hF.mdifferentiableAt (by simp)
  rcases eq_or_ne V 0 with hV | hV
  · subst hV
    have hfun : (fun s : ℝ ↦ F (GExp (cov := cov) hmet x (s • (0 : TangentSpace I x))))
        = fun _ : ℝ ↦ F x := by
      funext s; rw [smul_zero, GExp_zero]
    rw [hfun]
    have hz : mvfderiv I F x (0 : TangentSpace I x) = 0 := map_zero _
    rw [hz]
    exact hasDerivAt_const (0 : ℝ) (F x)
  · have hγsm : ContMDiff 𝓘(ℝ) I ∞ (fun s : ℝ ↦ GExp (cov := cov) hmet x (s • V)) :=
      Submission.ConjEnergy.contMDiff_GExp_smul (cov := cov) hmet x hV
    have hγmd : MDifferentiableAt 𝓘(ℝ) I (fun s : ℝ ↦ GExp (cov := cov) hmet x (s • V)) 0 :=
      hγsm.mdifferentiableAt (by simp)
    have hγ0 : (fun s : ℝ ↦ GExp (cov := cov) hmet x (s • V)) 0 = x := by
      simp only [zero_smul, GExp_zero]
    have hFmd' : MDifferentiableAt I 𝓘(ℝ,ℝ) F
        ((fun s : ℝ ↦ GExp (cov := cov) hmet x (s • V)) 0) := by
      rw [hγ0]; exact hFmd
    have hder : deriv (F ∘ fun s : ℝ ↦ GExp (cov := cov) hmet x (s • V)) 0
        = mvfderiv I F ((fun s : ℝ ↦ GExp (cov := cov) hmet x (s • V)) 0)
            (curveVelocity (I := I) (fun s : ℝ ↦ GExp (cov := cov) hmet x (s • V)) 0) :=
      (Commons.Geometry.Manifold.Tangent.mvfderiv_comp_curve (I := I) (g := F)
        (γ := fun s : ℝ ↦ GExp (cov := cov) hmet x (s • V)) (t := 0) hFmd' hγmd).symm
    have hvel : curveVelocity (I := I) (fun s : ℝ ↦ GExp (cov := cov) hmet x (s • V)) 0 = V :=
      Submission.GExpVelocity.curveVelocity_GExp_smul_zero (cov := cov) hmet x hV
    have hcomp : MDifferentiableAt 𝓘(ℝ) 𝓘(ℝ,ℝ)
        (F ∘ fun s : ℝ ↦ GExp (cov := cov) hmet x (s • V)) 0 := hFmd'.comp 0 hγmd
    rw [mdifferentiableAt_iff_differentiableAt] at hcomp
    have hd : HasDerivAt (F ∘ fun s : ℝ ↦ GExp (cov := cov) hmet x (s • V))
        (deriv (F ∘ fun s : ℝ ↦ GExp (cov := cov) hmet x (s • V)) 0) 0 := hcomp.hasDerivAt
    rw [hder, hγ0, hvel] at hd
    exact hd

end Helpers

theorem hess_upper
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [T2Space M] [CompactSpace M] [SimplyConnectedSpace M]
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    (hpinch : Pinched cov 1 4) (p : M) {x : M} {V : TangentSpace I x}
    (hsm : CMDiffAt ∞ (fun z : M ↦ rdist (I := I) p z) x)
    (hunit : Inner.inner ℝ (rgrad (I := I) (rdist (I := I) p) x)
      (rgrad (I := I) (rdist (I := I) p) x) = 1) :
    rhess cov (rdist (I := I) p) x V V
      ≤ Real.cot (rdist (I := I) p x)
        * (Inner.inner ℝ V V - (Inner.inner ℝ (rgrad (I := I) (rdist (I := I) p) x) V) ^ 2) := by
  classical
  rcases eq_or_ne V 0 with hV0 | hV
  · subst hV0
    simp [rhess]
  rcases lt_or_ge (Module.finrank ℝ E) 2 with hsmall | hbig
  · -- ## the tangent space has dimension at most one
    have hgradne : rgrad (I := I) (rdist (I := I) p) x ≠ 0 := by
      intro h
      rw [h, inner_zero_left] at hunit
      exact one_ne_zero hunit.symm
    have hfin : Module.finrank ℝ (TangentSpace I x) ≤ 1 := by
      have h1 : Module.finrank ℝ (TangentSpace I x) = Module.finrank ℝ E := rfl
      omega
    obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_le_one
      (W := rgrad (I := I) (rdist (I := I) p) x) (V := V) hgradne hfin
    rw [hc]
    have hrhs : Real.cot (rdist (I := I) p x)
        * (Inner.inner ℝ (c • rgrad (I := I) (rdist (I := I) p) x)
              (c • rgrad (I := I) (rdist (I := I) p) x)
            - (Inner.inner ℝ (rgrad (I := I) (rdist (I := I) p) x)
                (c • rgrad (I := I) (rdist (I := I) p) x)) ^ 2) = 0 := by
      simp only [real_inner_smul_left, real_inner_smul_right, hunit]
      ring
    have hcube : rhess cov (rdist (I := I) p) x (c • rgrad (I := I) (rdist (I := I) p) x)
        (c • rgrad (I := I) (rdist (I := I) p) x)
        = c ^ 2 * rhess cov (rdist (I := I) p) x (rgrad (I := I) (rdist (I := I) p) x)
            (rgrad (I := I) (rdist (I := I) p) x) := by
      simp only [rhess, map_smul, real_inner_smul_left, real_inner_smul_right]
      ring
    rw [hrhs, hcube]
    haveI : Nontrivial E := ⟨rgrad (I := I) (rdist (I := I) p) x, 0, hgradne⟩
    have hzero : rhess cov (rdist (I := I) p) x (rgrad (I := I) (rdist (I := I) p) x)
        (rgrad (I := I) (rdist (I := I) p) x) = 0 := by
      have hd : 0 < rdist (I := I) p x := rdist_pos_of_unit_grad (cov := cov) hmet p hsm hunit
      set w : TangentSpace I x := - rgrad (I := I) (rdist (I := I) p) x with hwdef
      have hwnorm : ‖w‖ = 1 := by
        rw [hwdef, norm_neg]
        have h : ‖rgrad (I := I) (rdist (I := I) p) x‖ ^ 2 = 1 := by
          rw [← real_inner_self_eq_norm_sq, hunit]
        nlinarith [norm_nonneg (rgrad (I := I) (rdist (I := I) p) x)]
      have hwne : w ≠ 0 := by
        intro h0; rw [h0, norm_zero] at hwnorm; norm_num at hwnorm
      -- the distance along the ray is affine on `[0, a]`
      have haff : ∀ t ∈ Set.Icc (0 : ℝ) (rdist (I := I) p x),
          rdist (I := I) p (GExp (cov := cov) hmet x (t • w)) = rdist (I := I) p x - t := by
        intro t ht
        rw [hwdef]
        exact rdist_GExp_smul_neg_rgrad (cov := cov) hmet htor p hd hsm hunit t ht
      -- the Hessian identity for that ray
      have hψ2 : HasDerivAt
          (deriv (fun s : ℝ ↦ rdist (I := I) p (GExp (cov := cov) hmet x (s • w))))
          (rhess cov (rdist (I := I) p) x w w) 0 := by
        have hγsm : ContMDiff 𝓘(ℝ) I ∞ (fun s : ℝ ↦ GExp (cov := cov) hmet x (s • w)) :=
          Submission.ConjEnergy.contMDiff_GExp_smul (cov := cov) hmet x hwne
        have hgeo : ∀ τ, IsGeodesicAt cov (fun s : ℝ ↦ GExp (cov := cov) hmet x (s • w)) τ :=
          fun τ => Submission.GExpRayZero.isGeodesicAt_GExp_smul_all (cov := cov) hmet x hwne τ
        have hne : curveVelocity (I := I) (fun s : ℝ ↦ GExp (cov := cov) hmet x (s • w)) 0
            ≠ 0 := by
          rw [Submission.GExpVelocity.curveVelocity_GExp_smul_zero (cov := cov) hmet x hwne]
          exact hwne
        have h0 : GExp (cov := cov) hmet x ((0 : ℝ) • w) = x := by
          simp only [zero_smul, GExp_zero]
        have h := hasDerivAt_deriv_comp_geodesic (cov := cov) hmet
          (F := fun z : M ↦ rdist (I := I) p z)
          (γ := fun s : ℝ ↦ GExp (cov := cov) hmet x (s • w))
          (t := 0) (by rw [h0]; exact hsm) hγsm hne hgeo
        rwa [h0, Submission.GExpVelocity.curveVelocity_GExp_smul_zero (cov := cov) hmet x hwne]
          at h
      have hψ1 : deriv (fun s : ℝ ↦ rdist (I := I) p (GExp (cov := cov) hmet x (s • w))) 0
          = -1 := by
        have h := (hasDerivAt_comp_GExp_smul (I := I) (M := M) (cov := cov) hmet
          (F := fun z : M ↦ rdist (I := I) p z) (x := x) (V := w) hsm).deriv
        rw [← inner_rgrad_eq_mvfderiv (I := I) (fun z : M ↦ rdist (I := I) p z) x w] at h
        rw [hwdef, inner_neg_right, hunit] at h
        exact h
      have hslope : ∀ᶠ s in 𝓝[>] (0 : ℝ),
          slope (deriv (fun s : ℝ ↦ rdist (I := I) p (GExp (cov := cov) hmet x (s • w)))) 0 s
            = 0 := by
        filter_upwards [Ioo_mem_nhdsGT hd] with s hs
        have heq : (fun t : ℝ ↦ rdist (I := I) p (GExp (cov := cov) hmet x (t • w)))
            =ᶠ[𝓝 s] (fun t : ℝ ↦ rdist (I := I) p x - t) := by
          filter_upwards [isOpen_Ioo.mem_nhds hs] with t ht
          exact haff t ⟨ht.1.le, ht.2.le⟩
        have hder : deriv (fun t : ℝ ↦ rdist (I := I) p (GExp (cov := cov) hmet x (t • w))) s
            = -1 := by
          rw [heq.deriv_eq]
          have h := (hasDerivAt_id s).const_sub (rdist (I := I) p x)
          simpa using h.deriv
        rw [slope_def_module, hder, hψ1, sub_self, smul_zero]
      have hW : rhess cov (rdist (I := I) p) x w w = 0 := by
        have h1 : Tendsto (slope (deriv (fun s : ℝ ↦
              rdist (I := I) p (GExp (cov := cov) hmet x (s • w)))) 0)
            (𝓝[>] (0 : ℝ)) (𝓝 (rhess cov (rdist (I := I) p) x w w)) :=
          hψ2.tendsto_slope.mono_left (nhdsWithin_mono 0 fun s hs => by
            simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
            exact ne_of_gt hs)
        have h2 : Tendsto (slope (deriv (fun s : ℝ ↦
              rdist (I := I) p (GExp (cov := cov) hmet x (s • w)))) 0)
            (𝓝[>] (0 : ℝ)) (𝓝 0) :=
          Tendsto.congr' (hslope.mono fun s hs => hs.symm) tendsto_const_nhds
        exact tendsto_nhds_unique h1 h2
      rw [hwdef] at hW
      have hev : rhess cov (rdist (I := I) p) x (- rgrad (I := I) (rdist (I := I) p) x)
          (- rgrad (I := I) (rdist (I := I) p) x)
          = rhess cov (rdist (I := I) p) x (rgrad (I := I) (rdist (I := I) p) x)
              (rgrad (I := I) (rdist (I := I) p) x) := by
        simp only [rhess, map_neg, inner_neg_left, inner_neg_right, neg_neg]
      rw [hev] at hW
      exact hW
    rw [hzero, mul_zero]
  · -- ## `2 ≤ Module.finrank ℝ E`
    haveI : Nontrivial E := Module.nontrivial_of_finrank_pos (by linarith)
    haveI : PathConnectedSpace M := inferInstance
    haveI : RegularSpace M := inferInstance
    haveI : Nonempty M := ⟨p⟩
    have hd : 0 < rdist (I := I) p x := rdist_pos_of_unit_grad (cov := cov) hmet p hsm hunit
    have hdπ : rdist (I := I) p x < Real.pi :=
      dist_lt_pi (I := I) (M := M) hbig cov hmet htor hpinch p x
    let ξ : TangentSpace I x := - rgrad (I := I) (rdist (I := I) p) x
    have hunitξ : Inner.inner ℝ ξ ξ = 1 := by
      simp only [ξ, inner_neg_left, inner_neg_right, neg_neg]
      exact hunit
    have hξp : GExp (cov := cov) hmet x (rdist (I := I) p x • ξ) = p := by
      simp only [ξ]
      exact GExp_smul_neg_rgrad (I := I) (M := M) (cov := cov) hmet htor p hd hsm hunit
    have hpinchQ : QuarterPinched cov := hpinch
    obtain ⟨ε, hε, hleε⟩ := hinge_bound (cov := cov) hmet htor hpinchQ p x hdπ ξ hunitξ hξp V hV
    let d : ℝ := rdist (I := I) p x
    let κ : ℝ := Inner.inner ℝ ξ V / ‖V‖
    let f : ℝ → ℝ := fun s : ℝ ↦ rdist (I := I) p (GExp (cov := cov) hmet x (s • V))
    let g : ℝ → ℝ := modelF d ‖V‖ κ
    have hVnorm : (0 : ℝ) < ‖V‖ := norm_pos_iff.mpr hV
    have hVne : (‖V‖ : ℝ) ≠ 0 := ne_of_gt hVnorm
    -- ## `f ≤ g` near `0`
    have hle : ∀ᶠ s in 𝓝 (0 : ℝ), f s ≤ g s := by
      refine Filter.mem_of_superset (Metric.ball_mem_nhds (0 : ℝ) hε) ?_
      intro s hs
      show f s ≤ g s
      have hs' : |s| < ε := by
        have h := Metric.mem_ball.mp hs
        rwa [Real.dist_eq, sub_zero] at h
      have h1 := hleε s hs'
      have h2 : g s = Real.arccos (Real.cos d * Real.cos (s * ‖V‖)
          + Real.sin d * Real.sin (s * ‖V‖) * (Inner.inner ℝ ξ V / ‖V‖)) := by
        simp only [g, κ, modelF, modelG]
        rw [mul_comm ‖V‖ s]
      rw [h2]
      simpa only [f, d] using h1
    -- ## the values at `0`
    have h0 : f 0 = g 0 := by
      simp only [f, g, d, modelF, modelG]
      rw [zero_smul, GExp_zero]
      simp only [mul_zero, zero_mul, Real.cos_zero, Real.sin_zero, mul_one, add_zero]
      exact (Real.arccos_cos hd.le hdπ.le).symm
    -- ## the first derivatives
    have hf : HasDerivAt f (Inner.inner ℝ (rgrad (I := I) (rdist (I := I) p) x) V) 0 := by
      have hbase := hasDerivAt_comp_GExp_smul (I := I) (M := M) (cov := cov) hmet
        (F := fun z : M ↦ rdist (I := I) p z) (x := x) (V := V) hsm
      exact hbase.congr_deriv
        (inner_rgrad_eq_mvfderiv (I := I) (fun z : M ↦ rdist (I := I) p z) x V).symm
    have hκval : ‖V‖ * κ = - Inner.inner ℝ (rgrad (I := I) (rdist (I := I) p) x) V := by
      simp only [κ, ξ, inner_neg_left]
      rw [← mul_div_assoc, div_eq_iff hVne]
      ring
    have hg : HasDerivAt g (Inner.inner ℝ (rgrad (I := I) (rdist (I := I) p) x) V) 0 :=
      (modelF_hasDerivAt_zero (a := d) (u := ‖V‖) (κ := κ) hd hdπ).congr_deriv
        (by rw [hκval, neg_neg])
    -- ## the second derivatives
    have hγsm : ContMDiff 𝓘(ℝ) I ∞ (fun s : ℝ ↦ GExp (cov := cov) hmet x (s • V)) :=
      Submission.ConjEnergy.contMDiff_GExp_smul (cov := cov) hmet x hV
    have hneV : curveVelocity (I := I) (fun s : ℝ ↦ GExp (cov := cov) hmet x (s • V)) 0 ≠ 0 := by
      rw [Submission.GExpVelocity.curveVelocity_GExp_smul_zero (cov := cov) hmet x hV]
      exact hV
    have hgeoV : ∀ τ, IsGeodesicAt cov (fun s : ℝ ↦ GExp (cov := cov) hmet x (s • V)) τ :=
      fun τ => Submission.GExpRayZero.isGeodesicAt_GExp_smul_all (cov := cov) hmet x hV τ
    have hγ0V : GExp (cov := cov) hmet x ((0 : ℝ) • V) = x := by
      simp only [zero_smul, GExp_zero]
    have hvelV : curveVelocity (I := I) (fun s : ℝ ↦ GExp (cov := cov) hmet x (s • V)) 0 = V :=
      Submission.GExpVelocity.curveVelocity_GExp_smul_zero (cov := cov) hmet x hV
    have hf2 : HasDerivAt (deriv f) (rhess cov (rdist (I := I) p) x V V) 0 := by
      have hsmV : CMDiffAt ∞ (fun z : M ↦ rdist (I := I) p z)
          (GExp (cov := cov) hmet x ((0 : ℝ) • V)) := by
        rw [zero_smul, GExp_zero]; exact hsm
      have hbase := hasDerivAt_deriv_comp_geodesic (cov := cov) hmet
        (F := fun z : M ↦ rdist (I := I) p z)
        (γ := fun s : ℝ ↦ GExp (cov := cov) hmet x (s • V)) (t := 0) hsmV hγsm hneV hgeoV
      rw [hγ0V, hvelV] at hbase
      exact hbase
    have hg2 : HasDerivAt (deriv g) (Real.cot (rdist (I := I) p x)
        * (Inner.inner ℝ V V
          - (Inner.inner ℝ (rgrad (I := I) (rdist (I := I) p) x) V) ^ 2)) 0 := by
      have hbase := modelW_hasDerivAt_zero (a := d) (u := ‖V‖) (κ := κ) hd hdπ
      have heq : deriv (modelF d ‖V‖ κ) =ᶠ[𝓝 (0 : ℝ)] modelW d ‖V‖ κ :=
        deriv_modelF_eventuallyEq_modelW (a := d) (u := ‖V‖) (κ := κ) hd hdπ
      have h1 : HasDerivAt (deriv (modelF d ‖V‖ κ))
          (Real.cot d * (‖V‖ ^ 2 - (‖V‖ * κ) ^ 2)) 0 :=
        hbase.congr_of_eventuallyEq heq
      have hval : Real.cot d * (‖V‖ ^ 2 - (‖V‖ * κ) ^ 2)
          = Real.cot (rdist (I := I) p x)
            * (Inner.inner ℝ V V
              - (Inner.inner ℝ (rgrad (I := I) (rdist (I := I) p) x) V) ^ 2) := by
        rw [hκval, neg_sq, ← real_inner_self_eq_norm_sq]
      exact h1.congr_deriv hval
    -- ## differentiability near `0`
    have hdiff : ∀ᶠ s in 𝓝 (0 : ℝ), DifferentiableAt ℝ f s ∧ DifferentiableAt ℝ g s := by
      have hgdiff : ∀ᶠ s in 𝓝 (0 : ℝ), DifferentiableAt ℝ g s := by
        filter_upwards [eventually_modelG_ne_pm_one (u := ‖V‖) (κ := κ) hd hdπ] with s hs
        exact ((Real.hasDerivAt_arccos hs.2 hs.1).comp s (modelG_hasDerivAt d ‖V‖ κ s)).differentiableAt
      have hfdiff : ∀ᶠ s in 𝓝 (0 : ℝ), DifferentiableAt ℝ f s := by
        haveI : IsManifold I (1 : ℕ∞ω) M :=
          IsManifold.of_le (I := I) (M := M) (m := (1 : ℕ∞ω)) (n := ∞) (by simp)
        obtain ⟨u, hu, hFu⟩ :=
          (contMDiffAt_iff_contMDiffOn_nhds (I := I) (I' := 𝓘(ℝ,ℝ)) (n := (1 : ℕ∞ω))
            (f := fun z : M ↦ rdist (I := I) p z) (x := x) (by simp)).mp (hsm.of_le (by simp))
        obtain ⟨v, hvu, hvopen, hxv⟩ := mem_nhds_iff.mp hu
        have hFOn' : MDifferentiableOn I 𝓘(ℝ,ℝ) (fun z : M ↦ rdist (I := I) p z) v :=
          (hFu.mono hvu).mdifferentiableOn one_ne_zero
        have hmem : v ∈ 𝓝 ((fun s : ℝ ↦ GExp (cov := cov) hmet x (s • V)) 0) := by
          simpa only [zero_smul, GExp_zero] using hvopen.mem_nhds hxv
        filter_upwards [hγsm.continuous.continuousAt.eventually hmem] with s hs
        have h1 : MDifferentiableAt I 𝓘(ℝ,ℝ) (fun z : M ↦ rdist (I := I) p z)
            (GExp (cov := cov) hmet x (s • V)) :=
          hFOn'.mdifferentiableAt (hvopen.mem_nhds hs)
        have h2 : MDifferentiableAt 𝓘(ℝ) I (fun s : ℝ ↦ GExp (cov := cov) hmet x (s • V)) s :=
          hγsm.mdifferentiableAt (by simp)
        have h3 : MDifferentiableAt 𝓘(ℝ) 𝓘(ℝ,ℝ) f s :=
          h1.comp (f := fun s : ℝ ↦ GExp (cov := cov) hmet x (s • V)) (x := s) h2
        rwa [mdifferentiableAt_iff_differentiableAt] at h3
      filter_upwards [hfdiff, hgdiff] with s h1 h2
      exact ⟨h1, h2⟩
    have hmain := deriv_deriv_le_of_eventually_le hle h0 hf hg
      (hf2.congr_deriv hf2.deriv.symm) (hg2.congr_deriv hg2.deriv.symm) hdiff
    rwa [hf2.deriv, hg2.deriv] at hmain

end Work.Diff.C
