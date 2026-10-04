import Mathlib
import Submission.Work.Diff.C.ShapeAux.Kit

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.C.ShapeAux

open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle CovariantDerivative
open Filter

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [I.Boundaryless] [T2Space M] [CompactSpace M] [Nontrivial E]
  {cov : CovariantDerivative I E (TangentSpace I (M := M))}
  [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]


/-! ## Auxiliary analytic lemmas -/


/-- **The slice derivative of a `C^∞` two-variable function is `C^∞`** (in the second variable). -/
theorem contDiffAt_sliceDeriv_snd {F : ℝ × ℝ → E} {s₀ t₀ : ℝ}
    (hF : ContDiffAt ℝ ∞ F (s₀, t₀)) :
    ContDiffAt ℝ ∞ (fun s => deriv (fun t => F (s, t)) t₀) s₀ := by
  have huncurry : Function.uncurry (fun (s : ℝ) (t : ℝ) => F (s, t)) = F := by
    funext p; cases p with | mk a b => rfl
  have hmain : ContDiffAt ℝ ∞ (fun s => fderiv ℝ (fun t => F (s, t)) t₀) s₀ :=
    ContDiffAt.fderiv (𝕜 := ℝ) (x₀ := s₀)
      (f := fun (s : ℝ) (t : ℝ) => F (s, t)) (g := fun _ : ℝ => t₀)
      (n := ∞) (m := ∞) (by rw [huncurry]; exact hF) contDiffAt_const (by simp)
  have hev : ContDiffAt ℝ ∞ (fun L : ℝ →L[ℝ] E => L (1 : ℝ))
      (fderiv ℝ (fun t => F (s₀, t)) t₀) :=
    (ContinuousLinearMap.contDiff ((ContinuousLinearMap.apply ℝ E) (1 : ℝ))).contDiffAt
  refine (hev.comp s₀ hmain).congr_of_eventuallyEq (Filter.EventuallyEq.of_eq ?_)
  funext s
  simp only [Function.comp_apply]
  exact (fderiv_apply_one_eq_deriv (f := fun t : ℝ => F (s, t)) (x := t₀)).symm

/-- **The slice derivative of a `C^∞` two-variable function is `C^∞`** (in the first variable). -/
theorem contDiffAt_sliceDeriv_fst {F : ℝ × ℝ → E} {s₀ t₀ : ℝ}
    (hF : ContDiffAt ℝ ∞ F (s₀, t₀)) :
    ContDiffAt ℝ ∞ (fun t => deriv (fun s => F (s, t)) s₀) t₀ := by
  have hswap : ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => F (p.2, p.1)) (t₀, s₀) :=
    hF.comp (t₀, s₀) (contDiffAt_snd.prodMk contDiffAt_fst)
  exact contDiffAt_sliceDeriv_snd (F := fun p : ℝ × ℝ => F (p.2, p.1)) hswap

/-- `ContMDiffOn` from pointwise `ContMDiffAt` on the same set. -/
lemma contMDiffOn_of_contMDiffAt {γ : ℝ → M} {V : Set ℝ}
    (h : ∀ t ∈ V, ContMDiffAt 𝓘(ℝ) I ∞ γ t) : ContMDiffOn 𝓘(ℝ) I ∞ γ V := fun s hs =>
  ContMDiffWithinAt.mono (contMDiffWithinAt_univ.mpr (h s hs)) (Set.subset_univ V)

/-- `SmoothAlongAt` only depends on the germ of the field. -/
lemma SmoothAlongAt_congr {γ : ℝ → M} {V V' : (t : ℝ) → TangentSpace I (γ t)} {t : ℝ}
    (h : V =ᶠ[𝓝 t] V') (hV : Submission.JacobiGlobal.SmoothAlongAt (I := I) γ V t) :
    Submission.JacobiGlobal.SmoothAlongAt (I := I) γ V' t := by
  obtain ⟨U, hUo, htU, hsrc, hcd⟩ := hV
  obtain ⟨O, hOsub, hOo, htO⟩ := mem_nhds_iff.mp h
  refine ⟨U ∩ O, hUo.inter hOo, ⟨htU, htO⟩, fun s hs => hsrc s hs.1, ?_⟩
  refine (hcd.mono Set.inter_subset_left).congr (fun s hs => ?_)
  show Submission.JacobiCoords.chartCoords (I := I) (γ t) γ V' s
      = Submission.JacobiCoords.chartCoords (I := I) (γ t) γ V s
  rw [Submission.JacobiCoords.chartCoords, Submission.JacobiCoords.chartCoords, hOsub hs.2]

/-- **The derivative of a `C^∞` function `ℝ → E` is `C^∞`.** -/
lemma contDiffAt_deriv {φ : ℝ → E} {x : ℝ} (h : ContDiffAt ℝ ∞ φ x) :
    ContDiffAt ℝ ∞ (deriv φ) x := by
  have hf : ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => φ p.2) (x, x) := h.comp (x, x) contDiffAt_snd
  have hmain : ContDiffAt ℝ ∞ (fun y => fderiv ℝ (fun z : ℝ => φ z) y) x :=
    ContDiffAt.fderiv (𝕜 := ℝ) (x₀ := x) (f := fun (y : ℝ) (z : ℝ) => φ z)
      (g := fun y : ℝ => y) (n := ∞) (m := ∞) hf contDiffAt_id (by simp)
  have hev : ContDiffAt ℝ ∞ (fun L : ℝ →L[ℝ] E => L (1 : ℝ))
      (fderiv ℝ (fun z : ℝ => φ z) x) :=
    (ContinuousLinearMap.contDiff ((ContinuousLinearMap.apply ℝ E) (1 : ℝ))).contDiffAt
  refine (hev.comp x hmain).congr_of_eventuallyEq (Filter.EventuallyEq.of_eq ?_)
  funext s
  simp only [Function.comp_apply]
  exact (fderiv_apply_one_eq_deriv (f := fun z : ℝ => φ z) (x := s)).symm

/-- `deriv φ` is `C^∞` on `V` as soon as `φ` is `C^∞` at every point of `V`. -/
lemma contDiffOn_deriv {φ : ℝ → E} {V : Set ℝ} (h : ∀ s ∈ V, ContDiffAt ℝ ∞ φ s) :
    ContDiffOn ℝ ∞ (deriv φ) V := fun s hs =>
  (contDiffAt_deriv (h s hs)).mono (Set.subset_univ V)

/-- A slice derivative in the second variable is `C^∞` on `V`. -/
lemma contDiffOn_sliceDeriv_snd {F : ℝ × ℝ → E} {V : Set ℝ} {t₀ : ℝ}
    (h : ∀ s ∈ V, ContDiffAt ℝ ∞ F (s, t₀)) :
    ContDiffOn ℝ ∞ (fun s => deriv (fun t => F (s, t)) t₀) V := fun s hs =>
  (contDiffAt_sliceDeriv_snd (h s hs)).mono (Set.subset_univ V)

/-- A slice derivative in the first variable is `C^∞` on `W`. -/
lemma contDiffOn_sliceDeriv_fst {F : ℝ × ℝ → E} {W : Set ℝ} {s₀ : ℝ}
    (h : ∀ t ∈ W, ContDiffAt ℝ ∞ F (s₀, t)) :
    ContDiffOn ℝ ∞ (fun t => deriv (fun s => F (s, t)) s₀) W := fun t ht =>
  (contDiffAt_sliceDeriv_fst (h t ht)).mono (Set.subset_univ W)

/-- The inner product on tangent spaces transports across a point equality.  (`TangentSpace I x` is
a type synonym for `E`, so the two `InnerProductSpace` instances are only propositionally equal.) -/
lemma inner_congr_point {X Y : M} (h : X = Y) (a b : E) :
    Inner.inner ℝ (show TangentSpace I X from a) (show TangentSpace I X from b)
      = Inner.inner ℝ (show TangentSpace I Y from a) (show TangentSpace I Y from b) := by
  subst h
  rfl

/-- The velocity of a curve is invariant under the reparametrisation `r ↦ r + a`, stated in the
plain model space `E` (sidestepping the tangent-space instance mismatch). -/
lemma curveVelocity_comp_add_rightE (γ : ℝ → M) (a t : ℝ)
    (hd : MDifferentiableAt 𝓘(ℝ) I γ (t + a)) :
    (Submission.Geodesic.curveVelocity (I := I) (fun x : ℝ => γ (x + a)) t : E)
      = (Submission.Geodesic.curveVelocity (I := I) γ (t + a) : E) :=
  Submission.SecondVarGlobal.curveVelocity_comp_add_right (I := I) γ a t hd

/-- `curveVelocity` depends only on the point, so propositionally equal parameters give the same
velocity (stated in `E`). -/
lemma curveVelocity_congr_pointE (γ : ℝ → M) {t t' : ℝ} (h : t = t') :
    (Submission.Geodesic.curveVelocity (I := I) γ t : E)
      = (Submission.Geodesic.curveVelocity (I := I) γ t' : E) := by
  subst h
  rfl

/-- **The Gauss pairing of the ray family, scalar form.**  For every `s`, the pairing of the
variation field `∂_r GExp p (d • (u + s•η))|_0` with the ray velocity `∂_t GExp p (t • (u+s•η))|_d`
is `d ⟪η, u + s•η⟫`.  This is `Work.OddBound.longHomotopy.gauss_pairing_fibre` with `v := u + s•η`,
after the reparametrisation `r ↦ s + r` of the variation curve. -/
theorem gauss_pairing_scalar
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {p : M} (d : ℝ) {u η : TangentSpace I p} :
    ∀ s : ℝ,
      Inner.inner ℝ
        (Submission.Geodesic.curveVelocity (I := I)
          (fun s' : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (d • (u + s' • η))) s)
        (Submission.Geodesic.curveVelocity (I := I)
          (fun t : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (t • (u + s • η))) d)
      = d * Inner.inner ℝ η (u + s • η) := by
  intro s
  set v : TangentSpace I p := u + s • η with hv
  set γ : ℝ → M := fun s' => Submission.GlobalExp.GExp (cov := cov) hmet p (d • (u + s' • η)) with hγ
  have hγsm : ContMDiffAt 𝓘(ℝ) I ∞ γ s := by
    have hpair : ContMDiffAt 𝓘(ℝ) (𝓘(ℝ, ℝ × ℝ)) ∞ (fun s' : ℝ => (d, s')) s := by
      have hcd : ContDiffAt ℝ ∞ (fun s' : ℝ => (d, s')) s :=
        contDiffAt_const.prodMk contDiffAt_id
      rw [contMDiffAt_iff_contDiffAt]
      exact hcd
    have hfam := Submission.RayJacobi.contMDiffAt_GExp_family (cov := cov) hmet (p := p) (u := u) (η := η) d s
    exact hfam.comp s hpair
  have hmd : MDifferentiableAt 𝓘(ℝ) I γ s := hγsm.mdifferentiableAt (by norm_num)
  have hfun : (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (d • (v + r • η)))
      = fun r : ℝ => γ (r + s) := by
    funext r
    have hvec : v + r • η = u + (r + s) • η := by
      rw [hv, add_assoc, ← add_smul, add_comm s r]
    rw [hγ, hvec]
  have hXeq : (Submission.Geodesic.curveVelocity (I := I)
        (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (d • (v + r • η))) 0 : E)
      = (Submission.Geodesic.curveVelocity (I := I) γ s : E) := by
    rw [hfun]
    rw [curveVelocity_comp_add_rightE γ s 0 (by simpa using hmd)]
    exact curveVelocity_congr_pointE γ (by simp)
  have hpt : Submission.GlobalExp.GExp (cov := cov) hmet p (d • (v + (0 : ℝ) • η)) = γ s := by
    rw [hγ, hv, zero_smul, add_zero]
  have hb := Work.OddBound.longHomotopy.gauss_pairing_fibre (cov := cov) hmet htor (p := p)
    (v := v) (η := η) d
  have hbr := inner_congr_point (I := I) (X := Submission.GlobalExp.GExp (cov := cov) hmet p (d • (v + (0 : ℝ) • η)))
    (Y := γ s) hpt
    (Submission.Geodesic.curveVelocity (I := I) (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (d • (v + r • η))) 0 : E)
    (Submission.Geodesic.curveVelocity (I := I) (fun t : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (t • v)) d : E)
  have hb2 := hbr.symm.trans hb
  rw [hXeq] at hb2
  exact hb2


/-- Joint smoothness of the chart description `(s,t) ↦ χ (GExp p (t • (u + s • η)))` of the
two-parameter family, in the parameter order (variation, ray). -/
lemma contDiffAt_chartFamily_swap
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov)
    {p : M} {u η : TangentSpace I p} {x : M} {s t : ℝ}
    (hsrc : Submission.GlobalExp.GExp (cov := cov) hmet p (t • (u + s • η)) ∈ (chartAt H x).source) :
    ContDiffAt ℝ ∞ (fun q : ℝ × ℝ => (extChartAt I x)
      (Submission.GlobalExp.GExp (cov := cov) hmet p (q.2 • (u + q.1 • η)))) (s, t) := by
  have h := Submission.RayJacobi.contDiffAt_chartFamily (cov := cov) hmet (p := p) (u := u) (η := η)
    (x₀ := x) (σ := t) (ρ := s) hsrc
  have hswap : ContDiffAt ℝ ∞ (fun q : ℝ × ℝ => (q.2, q.1)) (s, t) :=
    contDiffAt_snd.prodMk contDiffAt_fst
  refine (h.comp (s, t) hswap).congr_of_eventuallyEq (Filter.EventuallyEq.of_eq ?_)
  funext q; rfl


/-- **The Gauss pairing, differentiated in the variation parameter** (the second variation of the
energy of the family of rays).  With `Φ := GExp p`, `σ s t := Φ (t • (u + s • η))`,
`X s t := ∂_s σ s t`, `Y s t := ∂_t σ s t`, the Gauss pairing reads
`⟪X(s,t), Y(s,t)⟫ = t ⟪η, u + s•η⟫` for all `s, t` (`Work.OddBound.longHomotopy.gauss_pairing_fibre`).
Differentiating it in `s` at `(s,t) = (0,d)` gives this statement:
`⟪∇_{(s↦σ s d)} (s ↦ X s d) (0), Y(0,d)⟫ + ⟪covAlong (t ↦ X 0 t) d, X(0,d)⟫ = d ⟪η,η⟫`,
i.e. `⟪A, γ'(d)⟫ + ⟪∇_t Z(d), Z(d)⟫ = d‖η‖²`, where `A` is the covariant acceleration at `0` of the
curve `s ↦ Φ (d • (u + s•η))`, `γ` is the unit-speed ray `t ↦ Φ (t•u)` and
`Z t = ∂_s σ(0,t) = curveVelocity (fun r ↦ Φ (t • (u + r•η))) 0` is the Jacobi field along `γ`
with `Z 0 = 0` and `∇_t Z(0) = η`. -/
theorem gauss_pairing_second_deriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [T2Space M] [CompactSpace M] [Nontrivial E]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {p : M} {d : ℝ} (hd : 0 < d) {u η : TangentSpace I p} (hu : ‖u‖ = 1)
    (hvec : Submission.Geodesic.curveVelocity (I := I)
      (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (d • (u + s • η))) 0 ≠ 0) :
    Inner.inner ℝ
      (Submission.JacobiGlobal.covAlong cov
        (γ := fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (d • (u + s • η)))
        (fun s : ℝ => Submission.Geodesic.curveVelocity (I := I)
          (fun s' : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (d • (u + s' • η))) s) 0)
      (Submission.Geodesic.curveVelocity (I := I)
        (fun t : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (t • (u + 0 • η))) d)
    + Inner.inner ℝ
      (Submission.JacobiGlobal.covAlong cov
        (γ := fun t : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (t • (u + 0 • η)))
        (fun t : ℝ => Submission.Geodesic.curveVelocity (I := I)
          (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (t • (u + r • η))) 0) d)
      (Submission.Geodesic.curveVelocity (I := I)
        (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (d • (u + r • η))) 0)
    = d * Inner.inner ℝ η η := by
  classical
  set c : ℝ → M := fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (d • (u + s • η)) with hc
  set ray : ℝ → M := fun t : ℝ =>
    (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (t • (u + r • η))) 0 with hray
  set x : M := c 0 with hx
  have hrayx : ray d = x := by rw [hx, hc]
  have hc0x : c 0 = x := rfl
  -- the chart family
  set Ψ : ℝ → ℝ → E := fun s t =>
    (extChartAt I x) (Submission.GlobalExp.GExp (cov := cov) hmet p (t • (u + s • η))) with hΨ
  have hΨcd : ContDiffAt ℝ ∞ (Function.uncurry Ψ) (0, d) := by
    have hsrc : Submission.GlobalExp.GExp (cov := cov) hmet p (d • (u + (0 : ℝ) • η)) ∈ (chartAt H x).source := by
      exact mem_chart_source H x
    have h := contDiffAt_chartFamily_swap (cov := cov) hmet (p := p) (u := u) (η := η) (x := x)
      (s := 0) (t := d) hsrc
    refine h.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq ?_)
    funext q; rfl
  set u₁ : ℝ → E := fun s => Ψ s d with hu₁
  set y₂ : ℝ → E := fun s => deriv (fun t => Ψ s t) d with hy₂
  set w₁ : ℝ → E := fun s => deriv (fun s' => Ψ s' d) s with hw₁
  set u₂ : ℝ → E := fun t => Ψ 0 t with hu₂
  set y₃ : ℝ → E := fun t => deriv (fun r => Ψ r t) 0 with hy₃
  have hu₁cd : ContDiffAt ℝ ∞ u₁ 0 := by
    have h2 : ContDiffAt ℝ ∞ (fun s : ℝ => (s, d)) 0 := contDiffAt_id.prodMk contDiffAt_const
    refine (hΨcd.comp 0 h2).congr_of_eventuallyEq (Filter.EventuallyEq.of_eq ?_)
    funext s; rfl
  have hy₂cd : ContDiffAt ℝ ∞ y₂ 0 := by
    refine (contDiffAt_sliceDeriv_snd (F := Function.uncurry Ψ) (s₀ := 0) (t₀ := d) hΨcd).congr_of_eventuallyEq
      (Filter.EventuallyEq.of_eq ?_)
    funext s; rfl
  have hu₂cd : ContDiffAt ℝ ∞ u₂ d := by
    have h2 : ContDiffAt ℝ ∞ (fun t : ℝ => ((0 : ℝ), t)) d := contDiffAt_const.prodMk contDiffAt_id
    refine (hΨcd.comp d h2).congr_of_eventuallyEq (Filter.EventuallyEq.of_eq ?_)
    funext t; rfl
  have hy₃cd : ContDiffAt ℝ ∞ y₃ d := by
    refine (contDiffAt_sliceDeriv_fst (F := Function.uncurry Ψ) (s₀ := 0) (t₀ := d) hΨcd).congr_of_eventuallyEq
      (Filter.EventuallyEq.of_eq ?_)
    funext t; rfl
  have hw₁cd : ContDiffAt ℝ ∞ w₁ 0 := by
    have h := contDiffAt_deriv (φ := u₁) hu₁cd
    have hdw : deriv u₁ = w₁ := by funext s; rfl
    rwa [hdw] at h
  -- ## the box on which the family stays in the chart at `x`
  have hfam_cont : ContinuousAt (fun q : ℝ × ℝ =>
      Submission.GlobalExp.GExp (cov := cov) hmet p (q.1 • (u + q.2 • η))) (d, 0) :=
    (Submission.RayJacobi.contMDiffAt_GExp_family (cov := cov) hmet (p := p) (u := u) (η := η)
      d 0).continuousAt
  have hmem0 : (fun q : ℝ × ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (q.1 • (u + q.2 • η))) (d, 0)
      ∈ (chartAt H x).source := by
    show Submission.GlobalExp.GExp (cov := cov) hmet p (d • (u + (0 : ℝ) • η)) ∈ (chartAt H x).source
    exact mem_chart_source H x
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp
    (hfam_cont.preimage_mem_nhds ((chartAt H x).open_source.mem_nhds hmem0))
  set Vs : Set ℝ := Set.Ioo (-(ε / 2)) (ε / 2) with hVs
  set Wt : Set ℝ := Set.Ioo (d - ε / 2) (d + ε / 2) with hWt
  have hVs_open : IsOpen Vs := by rw [hVs]; exact isOpen_Ioo
  have hWt_open : IsOpen Wt := by rw [hWt]; exact isOpen_Ioo
  have h0Vs : (0 : ℝ) ∈ Vs := by rw [hVs]; exact ⟨by linarith, by linarith⟩
  have hdWt : d ∈ Wt := by rw [hWt]; exact ⟨by linarith, by linarith⟩
  have hbox : ∀ s ∈ Vs, ∀ t ∈ Wt,
      Submission.GlobalExp.GExp (cov := cov) hmet p (t • (u + s • η)) ∈ (chartAt H x).source := by
    intro s hs t ht
    have hmem : (t, s) ∈ Metric.ball (d, 0) ε := by
      rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq]
      rw [hVs] at hs; rw [hWt] at ht
      exact ⟨by rw [abs_lt]; exact ⟨by linarith [ht.1], by linarith [ht.2]⟩,
             by rw [abs_lt]; exact ⟨by linarith [hs.1], by linarith [hs.2]⟩⟩
    exact hεsub hmem
  have hΨst : ∀ s ∈ Vs, ∀ t ∈ Wt, ContDiffAt ℝ ∞ (Function.uncurry Ψ) (s, t) := by
    intro s hs t ht
    refine (contDiffAt_chartFamily_swap (cov := cov) hmet (p := p) (u := u) (η := η)
      (x := x) (s := s) (t := t) (hbox s hs t ht)).congr_of_eventuallyEq
      (Filter.EventuallyEq.of_eq ?_)
    funext q; rfl
  have hu₁On : ContDiffOn ℝ ∞ u₁ Vs := fun s hs => by
    have h2 : ContDiffAt ℝ ∞ (fun σ : ℝ => (σ, d)) s := contDiffAt_id.prodMk contDiffAt_const
    have hcomp : ContDiffAt ℝ ∞ (fun σ : ℝ => Function.uncurry Ψ (σ, d)) s :=
      ContDiffAt.comp (f := fun σ : ℝ => (σ, d)) (g := Function.uncurry Ψ) s
        (hΨst s hs d hdWt) h2
    exact hcomp.mono (Set.subset_univ Vs)
  have hw₁On : ContDiffOn ℝ ∞ w₁ Vs := by
    have h : ContDiffOn ℝ ∞ (deriv u₁) Vs := contDiffOn_deriv (φ := u₁) (V := Vs) (fun s hs =>
      (hu₁On s hs).contDiffAt (hVs_open.mem_nhds hs))
    have hdw : deriv u₁ = w₁ := by funext s; rfl
    rwa [hdw] at h
  have hy₂On : ContDiffOn ℝ ∞ y₂ Vs :=
    contDiffOn_sliceDeriv_snd (V := Vs) (t₀ := d) (fun s hs => hΨst s hs d hdWt)
  have hy₃On : ContDiffOn ℝ ∞ y₃ Wt :=
    contDiffOn_sliceDeriv_fst (W := Wt) (s₀ := 0) (fun t ht => hΨst 0 h0Vs t ht)
  set Xf : (s : ℝ) → TangentSpace I (c s) := fun s => Submission.Geodesic.curveVelocity (I := I) c s with hXf
  set Yf : (s : ℝ) → TangentSpace I (c s) := fun s => Submission.Geodesic.curveVelocity (I := I)
    (fun t : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (t • (u + s • η))) d with hYf
  set Zf : (t : ℝ) → TangentSpace I (ray t) := fun t => Submission.Geodesic.curveVelocity (I := I)
    (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (t • (u + r • η))) 0 with hZf
  -- ## the fields are `frameVector`s of the coordinate functions
  have hu₁eq : ∀ s, u₁ s = (extChartAt I x) (c s) := fun s => rfl
  have hC3 : Xf =ᶠ[𝓝 (0 : ℝ)] fun s => Submission.Geodesic.frameVector (I := I) x (c s) (w₁ s) := by
    filter_upwards [hVs_open.mem_nhds h0Vs] with s hs
    have hcsrc : c s ∈ (chartAt H x).source := hbox s hs d hdWt
    have hcext : c s ∈ (extChartAt I x).source := by rwa [extChartAt_source]
    have hder : HasDerivAt u₁ (w₁ s) s := by
      have hcd : ContDiffAt ℝ ∞ u₁ s := (hu₁On s hs).contDiffAt (hVs_open.mem_nhds hs)
      have h1 : HasDerivAt u₁ (deriv u₁ s) s := (hcd.differentiableAt (by norm_num)).hasDerivAt
      have hdw : deriv u₁ s = w₁ s := rfl
      rwa [hdw] at h1
    have htgt : u₁ s ∈ (extChartAt I x).target := by
      rw [hu₁eq s]; exact (extChartAt I x).map_source hcext
    have hstay : ∀ᶠ σ in 𝓝 s, u₁ σ ∈ (extChartAt I x).target := by
      filter_upwards [hVs_open.mem_nhds hs] with σ hσ
      rw [hu₁eq σ]
      exact (extChartAt I x).map_source (by rw [extChartAt_source]; exact hbox σ hσ d hdWt)
    have hcv := Submission.Geodesic.curveVelocity_extChartAt_symm (I := I) (x₀ := x) (u := u₁)
      (t := s) (v := w₁ s) hder htgt hstay
    have hcveg : c =ᶠ[𝓝 s] fun σ => (extChartAt I x).symm (u₁ σ) := by
      filter_upwards [hVs_open.mem_nhds hs] with σ hσ
      have hσsrc : c σ ∈ (extChartAt I x).source := by
        rw [extChartAt_source]; exact hbox σ hσ d hdWt
      rw [hu₁eq σ]
      exact ((extChartAt I x).left_inv hσsrc).symm
    have hXfs : Xf s = Submission.Geodesic.curveVelocity (I := I)
        (fun σ => (extChartAt I x).symm (u₁ σ)) s := by
      rw [hXf]
      exact Submission.RayJacobi.curveVelocity_congr (I := I) hcveg
    rw [hXfs, hcv]
    rw [show (extChartAt I x).symm (u₁ s) = c s from by
      rw [hu₁eq s]; exact (extChartAt I x).left_inv hcext]
    rfl
  have hC4 : Yf =ᶠ[𝓝 (0 : ℝ)] fun s => Submission.Geodesic.frameVector (I := I) x (c s) (y₂ s) := by
    filter_upwards [hVs_open.mem_nhds h0Vs] with s hs
    have hcsrc : c s ∈ (chartAt H x).source := hbox s hs d hdWt
    have hcext : c s ∈ (extChartAt I x).source := by rwa [extChartAt_source]
    have hder : HasDerivAt (fun t : ℝ => Ψ s t) (y₂ s) d := by
      have hcd : ContDiffAt ℝ ∞ (Function.uncurry Ψ) (s, d) := hΨst s hs d hdWt
      have h2 : ContDiffAt ℝ ∞ (fun t : ℝ => (s, t)) d := contDiffAt_const.prodMk contDiffAt_id
      have hcomp : ContDiffAt ℝ ∞ (fun t : ℝ => Function.uncurry Ψ (s, t)) d :=
        ContDiffAt.comp (f := fun t : ℝ => (s, t)) (g := Function.uncurry Ψ) d hcd h2
      exact ((hcomp.differentiableAt (by norm_num)).hasDerivAt).congr_deriv (by
        show deriv (fun t : ℝ => Function.uncurry Ψ (s, t)) d = y₂ s
        rfl)
    have htgt : (fun t : ℝ => Ψ s t) d ∈ (extChartAt I x).target := by
      show Ψ s d ∈ (extChartAt I x).target
      rw [show Ψ s d = (extChartAt I x) (c s) from rfl]
      exact (extChartAt I x).map_source hcext
    have hstay : ∀ᶠ t in 𝓝 d, (fun t : ℝ => Ψ s t) t ∈ (extChartAt I x).target := by
      filter_upwards [hWt_open.mem_nhds hdWt] with t ht
      show Ψ s t ∈ (extChartAt I x).target
      rw [show Ψ s t = (extChartAt I x) (Submission.GlobalExp.GExp (cov := cov) hmet p (t • (u + s • η))) from rfl]
      exact (extChartAt I x).map_source (by rw [extChartAt_source]; exact hbox s hs t ht)
    have hcv := Submission.Geodesic.curveVelocity_extChartAt_symm (I := I) (x₀ := x) (u := fun t : ℝ => Ψ s t)
      (t := d) (v := y₂ s) hder htgt hstay
    have hcveg : (fun t : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (t • (u + s • η)))
        =ᶠ[𝓝 d] fun t => (extChartAt I x).symm (Ψ s t) := by
      filter_upwards [hWt_open.mem_nhds hdWt] with t ht
      have htsrc : Submission.GlobalExp.GExp (cov := cov) hmet p (t • (u + s • η)) ∈ (extChartAt I x).source := by
        rw [extChartAt_source]; exact hbox s hs t ht
      show Submission.GlobalExp.GExp (cov := cov) hmet p (t • (u + s • η))
        = (extChartAt I x).symm ((extChartAt I x) (Submission.GlobalExp.GExp (cov := cov) hmet p (t • (u + s • η))))
      exact ((extChartAt I x).left_inv htsrc).symm
    have hYfs : Yf s = Submission.Geodesic.curveVelocity (I := I)
        (fun t => (extChartAt I x).symm (Ψ s t)) d := by
      rw [hYf]
      exact Submission.RayJacobi.curveVelocity_congr (I := I) hcveg
    rw [hYfs, hcv]
    rw [show (extChartAt I x).symm (Ψ s d) = c s from by
      rw [show Ψ s d = (extChartAt I x) (c s) from rfl]
      exact (extChartAt I x).left_inv hcext]
    rfl
  have hC5 : Zf =ᶠ[𝓝 d] fun t => Submission.Geodesic.frameVector (I := I) x (ray t) (y₃ t) := by
    filter_upwards [hWt_open.mem_nhds hdWt] with t ht
    have hrsrc : ray t ∈ (chartAt H x).source := hbox 0 h0Vs t ht
    have hrext : ray t ∈ (extChartAt I x).source := by rwa [extChartAt_source]
    have hder : HasDerivAt (fun r : ℝ => Ψ r t) (y₃ t) 0 := by
      have hcd : ContDiffAt ℝ ∞ (Function.uncurry Ψ) (0, t) := hΨst 0 h0Vs t ht
      have h2 : ContDiffAt ℝ ∞ (fun r : ℝ => (r, t)) 0 := contDiffAt_id.prodMk contDiffAt_const
      have hcomp : ContDiffAt ℝ ∞ (fun r : ℝ => Function.uncurry Ψ (r, t)) 0 :=
        ContDiffAt.comp (f := fun r : ℝ => (r, t)) (g := Function.uncurry Ψ) 0 hcd h2
      exact ((hcomp.differentiableAt (by norm_num)).hasDerivAt).congr_deriv (by
        show deriv (fun r : ℝ => Function.uncurry Ψ (r, t)) 0 = y₃ t
        rfl)
    have htgt : (fun r : ℝ => Ψ r t) 0 ∈ (extChartAt I x).target := by
      show Ψ 0 t ∈ (extChartAt I x).target
      rw [show Ψ 0 t = (extChartAt I x) (ray t) from rfl]
      exact (extChartAt I x).map_source hrext
    have hstay : ∀ᶠ r in 𝓝 (0 : ℝ), (fun r : ℝ => Ψ r t) r ∈ (extChartAt I x).target := by
      filter_upwards [hVs_open.mem_nhds h0Vs] with r hr
      show Ψ r t ∈ (extChartAt I x).target
      rw [show Ψ r t = (extChartAt I x) (Submission.GlobalExp.GExp (cov := cov) hmet p (t • (u + r • η))) from rfl]
      exact (extChartAt I x).map_source (by rw [extChartAt_source]; exact hbox r hr t ht)
    have hcv := Submission.Geodesic.curveVelocity_extChartAt_symm (I := I) (x₀ := x) (u := fun r : ℝ => Ψ r t)
      (t := 0) (v := y₃ t) hder htgt hstay
    have hcveg : (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (t • (u + r • η)))
        =ᶠ[𝓝 (0 : ℝ)] fun r => (extChartAt I x).symm (Ψ r t) := by
      filter_upwards [hVs_open.mem_nhds h0Vs] with r hr
      have hrsrc' : Submission.GlobalExp.GExp (cov := cov) hmet p (t • (u + r • η)) ∈ (extChartAt I x).source := by
        rw [extChartAt_source]; exact hbox r hr t ht
      show Submission.GlobalExp.GExp (cov := cov) hmet p (t • (u + r • η))
        = (extChartAt I x).symm ((extChartAt I x) (Submission.GlobalExp.GExp (cov := cov) hmet p (t • (u + r • η))))
      exact ((extChartAt I x).left_inv hrsrc').symm
    have hZfs : Zf t = Submission.Geodesic.curveVelocity (I := I)
        (fun r => (extChartAt I x).symm (Ψ r t)) 0 := by
      rw [hZf]
      exact Submission.RayJacobi.curveVelocity_congr (I := I) hcveg
    rw [hZfs, hcv]
    rw [show (extChartAt I x).symm (Ψ 0 t) = ray t from by
      rw [show Ψ 0 t = (extChartAt I x) (ray t) from rfl]
      exact (extChartAt I x).left_inv hrext]
    rfl
  -- ## smoothness of the curves
  have hu0 : u ≠ 0 := by
    intro h; rw [h, norm_zero] at hu; norm_num at hu
  have hcOn : ContMDiffOn 𝓘(ℝ) I ∞ c Vs := contMDiffOn_of_contMDiffAt (fun s _ => by
    have hpair : ContMDiffAt 𝓘(ℝ) (𝓘(ℝ, ℝ × ℝ)) ∞ (fun s' : ℝ => (d, s')) s := by
      have hcd : ContDiffAt ℝ ∞ (fun s' : ℝ => (d, s')) s :=
        contDiffAt_const.prodMk contDiffAt_id
      rw [contMDiffAt_iff_contDiffAt]; exact hcd
    exact (Submission.RayJacobi.contMDiffAt_GExp_family (cov := cov) hmet (p := p) (u := u) (η := η) d s).comp s hpair)
  have hrayOn : ContMDiffOn 𝓘(ℝ) I ∞ ray Wt := contMDiffOn_of_contMDiffAt (fun t _ => by
    have hv : (u + (0 : ℝ) • η) ≠ 0 := by simpa using hu0
    have h := contMDiffOn_univ.mp (Submission.LensLoop.contMDiffOn_GExp_smul (cov := cov) hmet p hv)
    exact h.contMDiffAt)
  -- ## `SmoothAlongAt` for the three fields
  have hSA_Xf : Submission.JacobiGlobal.SmoothAlongAt (I := I) c Xf 0 := by
    have hbase : Submission.JacobiGlobal.SmoothAlongAt (I := I) c
        (fun s => Submission.Geodesic.frameVector (I := I) x (c s) (w₁ s)) 0 :=
      Submission.JacobiGlobal.smoothAlongAt_frameVector (I := I) (z := x) (a := w₁) (γ := c)
        hVs_open h0Vs hw₁On hcOn (fun s hs => hbox s hs d hdWt)
        (fun s hs => by rw [hc0x]; exact hbox s hs d hdWt)
    exact SmoothAlongAt_congr hC3.symm hbase
  have hSA_Yf : Submission.JacobiGlobal.SmoothAlongAt (I := I) c Yf 0 := by
    have hbase : Submission.JacobiGlobal.SmoothAlongAt (I := I) c
        (fun s => Submission.Geodesic.frameVector (I := I) x (c s) (y₂ s)) 0 :=
      Submission.JacobiGlobal.smoothAlongAt_frameVector (I := I) (z := x) (a := y₂) (γ := c)
        hVs_open h0Vs hy₂On hcOn (fun s hs => hbox s hs d hdWt)
        (fun s hs => by rw [hc0x]; exact hbox s hs d hdWt)
    exact SmoothAlongAt_congr hC4.symm hbase
  have hSA_Zf : Submission.JacobiGlobal.SmoothAlongAt (I := I) ray Zf d := by
    have hbase : Submission.JacobiGlobal.SmoothAlongAt (I := I) ray
        (fun t => Submission.Geodesic.frameVector (I := I) x (ray t) (y₃ t)) d :=
      Submission.JacobiGlobal.smoothAlongAt_frameVector (I := I) (z := x) (a := y₃) (γ := ray)
        hWt_open hdWt hy₃On hrayOn (fun t ht => hbox 0 h0Vs t ht)
        (fun t ht => by rw [hrayx]; exact hbox 0 h0Vs t ht)
    exact SmoothAlongAt_congr hC5.symm hbase
  set A : E := deriv w₁ 0 + Submission.ChartCurv.chrB cov x x (w₁ 0) (w₁ 0) with hA
  set B : E := deriv y₂ 0 + Submission.ChartCurv.chrB cov x x (y₂ 0) (w₁ 0) with hB
  -- ## the chart formulas for the three covariant derivatives
  have hc_sm : ∀ s : ℝ, ContMDiffAt 𝓘(ℝ) I ∞ c s := fun s => by
    have hpair : ContMDiffAt 𝓘(ℝ) (𝓘(ℝ, ℝ × ℝ)) ∞ (fun s' : ℝ => (d, s')) s := by
      have hcd : ContDiffAt ℝ ∞ (fun s' : ℝ => (d, s')) s :=
        contDiffAt_const.prodMk contDiffAt_id
      rw [contMDiffAt_iff_contDiffAt]; exact hcd
    exact (Submission.RayJacobi.contMDiffAt_GExp_family (cov := cov) hmet (p := p) (u := u) (η := η)
      d s).comp s hpair
  have hray_sm : ∀ t : ℝ, ContMDiffAt 𝓘(ℝ) I ∞ ray t := fun t => by
    have hv : (u + (0 : ℝ) • η) ≠ 0 := by simpa using hu0
    exact (contMDiffOn_univ.mp (Submission.LensLoop.contMDiffOn_GExp_smul (cov := cov) hmet p hv)).contMDiffAt
  have hγc : ContMDiffOn 𝓘(ℝ) I ∞ c (Set.Ioo ((0 : ℝ) - 1) ((0 : ℝ) + 1)) :=
    contMDiffOn_of_contMDiffAt (fun s _ => hc_sm s)
  have hγr : ContMDiffOn 𝓘(ℝ) I ∞ ray (Set.Ioo (d - 1) (d + 1)) :=
    contMDiffOn_of_contMDiffAt (fun t _ => hray_sm t)
  have hne_c : Submission.Geodesic.curveVelocity (I := I) c 0 ≠ 0 := hvec
  have hne_r : Submission.Geodesic.curveVelocity (I := I) ray d ≠ 0 := by
    have hv : (u + (0 : ℝ) • η) ≠ 0 := by simpa using hu0
    have h := Submission.EnergyRayCover.curveVelocity_GExp_smul_ne_zero (cov := cov) hmet hv d
    simpa only [hray] using h
  have hu₁_target : ∀ᶠ s in 𝓝 (0 : ℝ), u₁ s ∈ (extChartAt I x).target := by
    filter_upwards [hVs_open.mem_nhds h0Vs] with s hs
    rw [hu₁eq s]
    exact (extChartAt I x).map_source (by rw [extChartAt_source]; exact hbox s hs d hdWt)
  have hγeq_c : c =ᶠ[𝓝 (0 : ℝ)] fun s => (extChartAt I x).symm (u₁ s) := by
    filter_upwards [hVs_open.mem_nhds h0Vs] with s hs
    have hσsrc : c s ∈ (extChartAt I x).source := by
      rw [extChartAt_source]; exact hbox s hs d hdWt
    rw [hu₁eq s]
    exact ((extChartAt I x).left_inv hσsrc).symm
  have hu₁_der : ∀ᶠ s in 𝓝 (0 : ℝ), HasDerivAt u₁ (w₁ s) s := by
    filter_upwards [Submission.JacobiGlobal.eventually_hasDerivAt_of_contDiffOn hVs_open h0Vs hu₁On]
      with s hs
    have hdw : deriv u₁ s = w₁ s := rfl
    rwa [hdw] at hs
  have hw₁_der : ∀ᶠ s in 𝓝 (0 : ℝ), HasDerivAt w₁ (deriv w₁ s) s :=
    Submission.JacobiGlobal.eventually_hasDerivAt_of_contDiffOn hVs_open h0Vs hw₁On
  have hy₂_der : ∀ᶠ s in 𝓝 (0 : ℝ), HasDerivAt y₂ (deriv y₂ s) s :=
    Submission.JacobiGlobal.eventually_hasDerivAt_of_contDiffOn hVs_open h0Vs hy₂On
  have hy₃_der : ∀ᶠ t in 𝓝 d, HasDerivAt y₃ (deriv y₃ t) t :=
    Submission.JacobiGlobal.eventually_hasDerivAt_of_contDiffOn hWt_open hdWt hy₃On
  -- E1
  have hE1 : Submission.JacobiGlobal.covAlong cov Xf 0
      = Submission.Geodesic.frameVector (I := I) x x A := by
    have hsrc : c 0 ∈ (chartAt H x).source := by rw [hc0x]; exact mem_chart_source H x
    have hsrcEv : ∀ᶠ s in 𝓝 (0 : ℝ), c s ∈ (chartAt H x).source := by
      filter_upwards [hVs_open.mem_nhds h0Vs] with s hs; exact hbox s hs d hdWt
    have hchart := Submission.JacobiGlobal.covAlong_eq_chart (cov := cov) htor
      (γ := c) (V := Xf) (t := 0) (hγ := hγc) hne_c hSA_Xf hsrc hsrcEv hu₁_target hγeq_c
      hu₁_der hC3.symm hw₁_der
    rw [hchart]
    have hpt0 : (extChartAt I x).symm (u₁ 0) = x := by
      rw [show u₁ 0 = (extChartAt I x) (c 0) from rfl]
      rw [(extChartAt I x).left_inv (by rw [extChartAt_source]; exact hbox 0 h0Vs d hdWt), hc0x]
    rw [show c 0 = x from hc0x]
    congr 1
    simp only [Submission.BonnetMyers.DtQ, Submission.SecondVariation.covDsP, Submission.SecondVariation.fam,
      Submission.SecondVariation.famP, zero_smul, add_zero, hpt0, hA]
  -- E2
  have hE2 : Submission.JacobiGlobal.covAlong cov Yf 0
      = Submission.Geodesic.frameVector (I := I) x x B := by
    have hsrc : c 0 ∈ (chartAt H x).source := by rw [hc0x]; exact mem_chart_source H x
    have hsrcEv : ∀ᶠ s in 𝓝 (0 : ℝ), c s ∈ (chartAt H x).source := by
      filter_upwards [hVs_open.mem_nhds h0Vs] with s hs; exact hbox s hs d hdWt
    have hchart := Submission.JacobiGlobal.covAlong_eq_chart (cov := cov) htor
      (γ := c) (V := Yf) (t := 0) (hγ := hγc) hne_c hSA_Yf hsrc hsrcEv hu₁_target hγeq_c
      hu₁_der hC4.symm hy₂_der
    rw [hchart]
    have hpt0 : (extChartAt I x).symm (u₁ 0) = x := by
      rw [show u₁ 0 = (extChartAt I x) (c 0) from rfl]
      rw [(extChartAt I x).left_inv (by rw [extChartAt_source]; exact hbox 0 h0Vs d hdWt), hc0x]
    rw [show c 0 = x from hc0x]
    congr 1
    simp only [Submission.BonnetMyers.DtQ, Submission.SecondVariation.covDsP, Submission.SecondVariation.fam,
      Submission.SecondVariation.famP, zero_smul, add_zero, hpt0, hB,
      Submission.SecondVariation.chrB_comm (cov := cov) htor (x₀ := x) (p := x)
        (mem_chart_source H x) (w₁ 0) (y₂ 0)]
  have hu₂On : ContDiffOn ℝ ∞ u₂ Wt := fun t ht => by
    have h2 : ContDiffAt ℝ ∞ (fun τ : ℝ => ((0 : ℝ), τ)) t := contDiffAt_const.prodMk contDiffAt_id
    have hcomp : ContDiffAt ℝ ∞ (fun τ : ℝ => Function.uncurry Ψ ((0 : ℝ), τ)) t :=
      ContDiffAt.comp (f := fun τ : ℝ => ((0 : ℝ), τ)) (g := Function.uncurry Ψ) t (hΨst 0 h0Vs t ht) h2
    exact hcomp.mono (Set.subset_univ Wt)
  -- E3
  have hE3 : Submission.JacobiGlobal.covAlong cov Zf d
      = Submission.Geodesic.frameVector (I := I) x x (deriv y₃ d + Submission.ChartCurv.chrB cov x x (y₂ 0) (w₁ 0)) := by
    have hsrc : ray d ∈ (chartAt H x).source := by rw [hrayx]; exact mem_chart_source H x
    have hsrcEv : ∀ᶠ t in 𝓝 d, ray t ∈ (chartAt H x).source := by
      filter_upwards [hWt_open.mem_nhds hdWt] with t ht
      exact hbox 0 h0Vs t ht
    have hγeq_r : ray =ᶠ[𝓝 d] fun t => (extChartAt I x).symm (u₂ t) := by
      filter_upwards [hWt_open.mem_nhds hdWt] with t ht
      have htsrc : ray t ∈ (extChartAt I x).source := by
        rw [extChartAt_source]; exact hbox 0 h0Vs t ht
      show ray t = (extChartAt I x).symm (u₂ t)
      rw [show u₂ t = (extChartAt I x) (ray t) from rfl]
      exact ((extChartAt I x).left_inv htsrc).symm
    have hu₂_der : ∀ᶠ t in 𝓝 d, HasDerivAt u₂ (deriv u₂ t) t :=
      Submission.JacobiGlobal.eventually_hasDerivAt_of_contDiffOn hWt_open hdWt hu₂On
    have hchart := Submission.JacobiGlobal.covAlong_eq_chart (cov := cov) htor
      (γ := ray) (V := Zf) (t := d) (hγ := hγr) hne_r hSA_Zf hsrc hsrcEv
      (by
        filter_upwards [hWt_open.mem_nhds hdWt] with t ht
        show Ψ 0 t ∈ (extChartAt I x).target
        rw [show Ψ 0 t = (extChartAt I x) (ray t) from rfl]
        exact (extChartAt I x).map_source (by rw [extChartAt_source]; exact hbox 0 h0Vs t ht))
      hγeq_r hu₂_der hC5.symm hy₃_der
    rw [hchart]
    have hptd : (extChartAt I x).symm (u₂ d) = x := by
      show (extChartAt I x).symm ((extChartAt I x) (Submission.GlobalExp.GExp (cov := cov) hmet p (d • (u + (0 : ℝ) • η)))) = x
      exact (extChartAt I x).left_inv (by rw [extChartAt_source]; exact mem_chart_source H x)
    rw [hrayx]
    congr 1
    simp only [Submission.BonnetMyers.DtQ, Submission.SecondVariation.covDsP, Submission.SecondVariation.fam,
      Submission.SecondVariation.famP, zero_smul, add_zero, hptd]
    rfl
  -- the mixed partial symmetry
  have hmix : Submission.JacobiGlobal.covAlong cov Zf d = Submission.JacobiGlobal.covAlong cov Yf 0 := by
    rw [hE3, hE2]
    have hcl : deriv y₃ d = deriv y₂ 0 := by
      have h2 : ContDiffAt ℝ 2 (Function.uncurry Ψ) (0, d) := hΨcd.of_le (by norm_num)
      exact Commons.Analysis.Calculus.deriv_deriv_swap h2
    rw [hcl, ← hB]
  -- ## the Gauss pairing and the product rule
  have hGaussX : ∀ s : ℝ, Inner.inner ℝ (Xf s) (Yf s) = d * Inner.inner ℝ η (u + s • η) := by
    intro s
    have h := gauss_pairing_scalar (cov := cov) hmet htor (p := p) d (u := u) (η := η) s
    simpa only [hXf, hc, hYf] using h
  have hu₁der0 : HasDerivAt u₁ (deriv u₁ 0) 0 :=
    (((hu₁On 0 h0Vs).contDiffAt (hVs_open.mem_nhds h0Vs)).differentiableAt (by norm_num)).hasDerivAt
  have hw₁der0 : HasDerivAt w₁ (deriv w₁ 0) 0 :=
    (((hw₁On 0 h0Vs).contDiffAt (hVs_open.mem_nhds h0Vs)).differentiableAt (by norm_num)).hasDerivAt
  have hy₂der0 : HasDerivAt y₂ (deriv y₂ 0) 0 :=
    (((hy₂On 0 h0Vs).contDiffAt (hVs_open.mem_nhds h0Vs)).differentiableAt (by norm_num)).hasDerivAt
  have htgt0 : u₁ 0 ∈ (extChartAt I x).target := by
    rw [hu₁eq 0]
    exact (extChartAt I x).map_source (by rw [extChartAt_source]; exact hbox 0 h0Vs d hdWt)
  have hPR := Submission.ChartConnection.hasDerivAt_chartGram_curve (cov := cov) hmet x
    (u := u₁) (v := deriv u₁ 0) (t := 0) hu₁der0 htgt0 hu₁_target (h₁ := w₁) (h₁' := deriv w₁ 0)
    (h₂ := y₂) (h₂' := deriv y₂ 0) hw₁der0 hy₂der0
  have hdw0 : deriv u₁ 0 = w₁ 0 := rfl
  have hpt0 : (extChartAt I x).symm (u₁ 0) = c 0 := by
    rw [show u₁ 0 = (extChartAt I x) (c 0) from rfl]
    exact (extChartAt I x).left_inv (by rw [extChartAt_source]; exact hbox 0 h0Vs d hdWt)
  have hPRc : HasDerivAt (fun s : ℝ => Submission.ChartConnection.chartGram (I := I) x (c s) (w₁ s) (y₂ s))
      (Submission.ChartConnection.chartGram (I := I) x x A (y₂ 0)
        + Submission.ChartConnection.chartGram (I := I) x x (w₁ 0) B) 0 := by
    have hev : (fun s : ℝ =>
          Submission.ChartConnection.chartGram (I := I) x ((extChartAt I x).symm (u₁ s)) (w₁ s) (y₂ s))
        =ᶠ[𝓝 (0 : ℝ)] fun s : ℝ => Submission.ChartConnection.chartGram (I := I) x (c s) (w₁ s) (y₂ s) := by
      filter_upwards [hVs_open.mem_nhds h0Vs] with s hs
      have hσsrc : c s ∈ (extChartAt I x).source := by rw [extChartAt_source]; exact hbox s hs d hdWt
      rw [show (extChartAt I x).symm (u₁ s) = c s from by
        rw [show u₁ s = (extChartAt I x) (c s) from rfl]
        exact (extChartAt I x).left_inv hσsrc]
    refine (hPR.congr_of_eventuallyEq hev.symm).congr_deriv ?_
    simp only [hdw0, hpt0, hc0x, hA, hB, ← Submission.ChartCurv.chrB_apply]
  have hPRP : HasDerivAt (fun s : ℝ => Inner.inner ℝ (Xf s) (Yf s))
      (Submission.ChartConnection.chartGram (I := I) x x A (y₂ 0)
        + Submission.ChartConnection.chartGram (I := I) x x (w₁ 0) B) 0 := by
    have hev : (fun s : ℝ => Submission.ChartConnection.chartGram (I := I) x (c s) (w₁ s) (y₂ s))
        =ᶠ[𝓝 (0 : ℝ)] fun s : ℝ => Inner.inner ℝ (Xf s) (Yf s) := by
      filter_upwards [hVs_open.mem_nhds h0Vs, hC3, hC4] with s _ h3 h4
      rw [h3, h4, Submission.ChartConnection.chartGram_apply (I := I)]
    exact hPRc.congr_of_eventuallyEq hev.symm
  have hP_eq : (fun s : ℝ => Inner.inner ℝ (Xf s) (Yf s))
      = fun s : ℝ => d * Inner.inner ℝ η (u + s • η) := funext hGaussX
  have hder2 : HasDerivAt (fun s : ℝ => d * Inner.inner ℝ η (u + s • η)) (d * Inner.inner ℝ η η) 0 := by
    have hlin : HasDerivAt (fun s : ℝ => u + s • η) η 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const η).const_add u
    have hcst : HasDerivAt (fun _ : ℝ => η) (0 : TangentSpace I p) 0 := hasDerivAt_const (0 : ℝ) η
    have h1 : HasDerivAt (fun s : ℝ => Inner.inner ℝ η (u + s • η)) (Inner.inner ℝ η η) 0 := by
      have h := HasDerivAt.inner (𝕜 := ℝ) hcst hlin
      have hval : Inner.inner ℝ η η + Inner.inner ℝ (0 : TangentSpace I p) (u + (0 : ℝ) • η)
          = Inner.inner ℝ η η := by
        rw [inner_zero_left, add_zero]
      rwa [hval] at h
    exact h1.const_mul d
  have hder2' : HasDerivAt (fun s : ℝ => Inner.inner ℝ (Xf s) (Yf s)) (d * Inner.inner ℝ η η) 0 :=
    hder2.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq hP_eq)
  have hV0 : Submission.ChartConnection.chartGram (I := I) x x A (y₂ 0)
      + Submission.ChartConnection.chartGram (I := I) x x (w₁ 0) B = d * Inner.inner ℝ η η :=
    hPRP.unique hder2'
  -- ## rewriting the target into the chart expression
  have hYeq1 : Submission.Geodesic.curveVelocity (I := I)
      (fun t : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (t • (u + 0 • η))) d = Yf 0 := by
    rw [hYf]
  have hZeq1 : Submission.Geodesic.curveVelocity (I := I) c 0 = Zf d := by
    rw [hZf]
  have hC40 : Yf 0 = Submission.Geodesic.frameVector (I := I) x x (y₂ 0) := by
    have h4 := Filter.Eventually.self_of_nhds
      (p := fun s => Yf s = Submission.Geodesic.frameVector (I := I) x (c s) (y₂ s)) hC4
    rw [h4, hc0x]
  have hZ0 : Zf d = Submission.Geodesic.frameVector (I := I) x x (w₁ 0) := by
    rw [show Zf d = Xf 0 from rfl]
    have h3 := Filter.Eventually.self_of_nhds
      (p := fun s => Xf s = Submission.Geodesic.frameVector (I := I) x (c s) (w₁ s)) hC3
    rw [h3, hc0x]
  have hcl : deriv y₃ d = deriv y₂ 0 := by
    have h2 : ContDiffAt ℝ 2 (Function.uncurry Ψ) (0, d) := hΨcd.of_le (by norm_num)
    exact Commons.Analysis.Calculus.deriv_deriv_swap h2
  have hconv2 := inner_congr_point (I := I) (X := ray d) (Y := x) hrayx
    (Submission.JacobiGlobal.covAlong cov (γ := ray) Zf d : E) (Zf d : E)
  rw [hYeq1, hZeq1, hconv2]
  rw [hE1, hE3, hC40, hZ0]
  rw [← Submission.ChartConnection.chartGram_apply (I := I), ← Submission.ChartConnection.chartGram_apply (I := I)]
  nth_rewrite 2 [Submission.ChartConnection.chartGram_comm (I := I)]
  rw [hcl, ← hB]
  exact hV0
