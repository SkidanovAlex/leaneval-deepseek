import Mathlib
import Submission.Work.Diff.C.Setup
import Submission.Work.Diff.C.ray_cos_compare
import Submission.Work.Diff.C.rhess_comp
import Submission.Work.Diff.C.rgrad_fcos
import Submission.Work.Diff.C.ray_cover
import Submission.JacobiTensor

set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.C

open Bundle
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric
set_option backward.isDefEq.respectTransparency false


/-! ## The shape-operator bound for `rdist q` derived from `hHess`

The hypotheses of `far_sphere_size` control the Hessian of `cos ∘ rdist z`, for every centre `z`, on
the region `{rdist z < π - arccos (1-c)}`.  The first step of the proof is the conversion into the
*shape-operator* bound for the distance function itself: on the directions orthogonal to
`∇ (rdist z)`, the Hessian of `rdist z` equals `cot (rdist z)` times the metric up to
`ε₁ / sin (rdist z)`.  This is the input of the Riccati/Sturm comparison.

Both lemmas below are pure chain-rule computations (using `rhess_comp` and
`rgrad (cos ∘ F) = -sin (F ·) • rgrad F`); nothing about geodesics or Jacobi fields is needed. -/

open Bundle in
/-- **The chain rule for `cos`** (the `c = Real.cos` case of `Work.Diff.C.rhess_comp`). -/
lemma rhess_cos_far
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    {F : M → ℝ} {x : M} (hF : CMDiffAt ∞ F x) (V W : TangentSpace I x) :
    Work.Diff.C.rhess cov (fun y : M ↦ Real.cos (F y)) x V W
      = - Real.cos (F x) * (mvfderiv I F x V * mvfderiv I F x W)
        - Real.sin (F x) * Work.Diff.C.rhess cov F x V W := by
  have h := rhess_comp (I := I) (M := M) (cov := cov) Real.cos F x V W
    Real.contDiff_cos.contDiffAt hF
  have h2 : iteratedDeriv 2 Real.cos (F x) = - Real.cos (F x) := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ', iteratedDeriv_one]
    have hfun : deriv Real.cos = fun z => - Real.sin z := funext fun z => Real.deriv_cos
    rw [hfun]
    exact (Real.hasDerivAt_sin (F x)).neg.deriv
  have h1 : deriv Real.cos (F x) = - Real.sin (F x) := Real.deriv_cos
  rw [h, h2, h1]
  ring

open Bundle in
/-- **The shape-operator bound for the distance function, from `hHess`.**  If `x` lies in the region
`-1 + c < fcos q x`, the distance function `rdist q` is smooth at `x`, `0 < rdist q x < π`, and `V` is
orthogonal to `∇ (fcos q) x` (equivalently, to `∇ (rdist q) x`), then

`|rhess (rdist q) x V V - cot (rdist q x) · ‖V‖²| ≤ (ε / sin (rdist q x)) · ‖V‖²`. -/
lemma rhess_rdist_bound_of_hHess
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    {c ε : ℝ} {q : M}
    (hHess : HessBoundRegion (I := I) (M := M) cov c ε (fcos (I := I) (M := M) q))
    {x : M} (hx : -1 + c < fcos (I := I) (M := M) q x)
    (hsm : CMDiffAt ∞ (fun z : M ↦ rdist (I := I) (M := M) q z) x)
    (hpos : 0 < rdist (I := I) (M := M) q x)
    (hdπ : rdist (I := I) (M := M) q x < Real.pi)
    (V : TangentSpace I x)
    (hV : Inner.inner ℝ (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) x) V = 0) :
    |rhess cov (fun z : M ↦ rdist (I := I) (M := M) q z) x V V
        - Real.cot (rdist (I := I) (M := M) q x) * Inner.inner ℝ V V|
      ≤ (ε / Real.sin (rdist (I := I) (M := M) q x)) * Inner.inner ℝ V V := by
  set d : ℝ := rdist (I := I) (M := M) q x with hd
  have hsind : 0 < Real.sin d := Real.sin_pos_of_pos_of_lt_pi hpos hdπ
  -- the orthogonality transfers from `∇ (fcos q)` to `∇ (rdist q)`
  have hgradf : rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) x
      = (-Real.sin d) • rgrad (I := I) (M := M) (rdist (I := I) (M := M) q) x := by
    have h := rgrad_fcos (I := I) (M := M) (q := q) hsm
    simpa [hd] using h
  have hneg : (-Real.sin d) ≠ 0 := by
    intro h0
    exact absurd h0 (ne_of_lt (neg_lt_zero.mpr hsind))
  have horth : Inner.inner ℝ (rgrad (I := I) (M := M) (rdist (I := I) (M := M) q) x) V = 0 := by
    have h := hV
    rw [hgradf, inner_smul_left] at h
    exact (mul_eq_zero.mp h).resolve_left hneg
  have hmfd : mvfderiv I (fun z : M ↦ rdist (I := I) (M := M) q z) x V = 0 := by
    rw [← inner_rgrad_mvfderiv_local]
    exact horth
  -- the chain rule, and `hHess` at `(V,V)`
  have hchain := rhess_cos_far (I := I) (M := M) (cov := cov)
    (F := fun z : M ↦ rdist (I := I) (M := M) q z) hsm V V
  rw [hmfd] at hchain
  have hb := hHess x V V hx
  have hfcos : fcos (I := I) (M := M) q x = Real.cos d := by rw [hd]; rfl
  have hrhs : rhess cov (fcos (I := I) (M := M) q) x V V
      = - Real.sin d * rhess cov (fun z : M ↦ rdist (I := I) (M := M) q z) x V V := by
    show rhess cov (fun y : M ↦ Real.cos (rdist (I := I) (M := M) q y)) x V V = _
    rw [hchain]
    ring
  rw [hrhs, hfcos] at hb
  -- `‖V‖ * ‖V‖ = ⟪V,V⟫`
  have hVnorm : ‖V‖ * ‖V‖ = Inner.inner ℝ V V := by
    rw [real_inner_self_eq_norm_sq]
    ring
  have hb' : |-Real.sin d * rhess cov (fun z : M ↦ rdist (I := I) (M := M) q z) x V V
      + Real.cos d * Inner.inner ℝ V V| ≤ ε * Inner.inner ℝ V V := by
    have h1 : ε * ‖V‖ * ‖V‖ = ε * (‖V‖ * ‖V‖) := by ring
    rw [h1, hVnorm] at hb
    exact hb
  -- `sin d * cot d = cos d`
  have hcot : Real.sin d * Real.cot d = Real.cos d := by
    rw [Real.cot_eq_cos_div_sin]
    field_simp
  -- the key inequality: `|A| ≤ ε g` with `A = -sin d * (R - cot d * g)`
  have hkey : Real.sin d * |rhess cov (fun z : M ↦ rdist (I := I) (M := M) q z) x V V
      - Real.cot d * Inner.inner ℝ V V| ≤ ε * Inner.inner ℝ V V := by
    have hAa : (-Real.sin d * rhess cov (fun z : M ↦ rdist (I := I) (M := M) q z) x V V
          + Real.cos d * Inner.inner ℝ V V)
        = -Real.sin d * (rhess cov (fun z : M ↦ rdist (I := I) (M := M) q z) x V V
            - Real.cot d * Inner.inner ℝ V V) := by
      rw [← hcot]
      ring
    rw [hAa, abs_mul, abs_neg, abs_of_pos hsind] at hb'
    linarith [hb']
  have hfin : |rhess cov (fun z : M ↦ rdist (I := I) (M := M) q z) x V V
      - Real.cot d * Inner.inner ℝ V V| ≤ (ε / Real.sin d) * Inner.inner ℝ V V := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hsind]
    linarith [hkey]
  simpa [hd] using hfin


/-! ## The reverse shape-operator identity

Along a chart geodesic, let `(Y, U)` be the Jacobi tensor with `(Y 0, U 0) = (0, 1)` (the "sine"
solution, supplied by `Submission.JacobiTensor.exists_jacobiSystem`) and `(Yc, Uc)` the one with
`(Yc 0, Uc 0) = (1, 0)` (the "cosine" solution).  Let `(C, D)` be any solution with `C s = 0` (the
"backward" solution vanishing at the time `s` — geometrically the Jacobi tensor of the sphere of
radius `s` around `γ(s)`).  Then

  `Y s * D 0 + Yc s * C 0 = 0`,

equivalently (when both `Y s` and `C 0` are invertible)
`-(D 0) * (C 0)⁻¹ = (Y s)⁻¹ * Yc s`: the shape operator at `γ 0` of the sphere around `γ s` is
`(Y s)⁻¹ Yc s`.

The proof is the span/uniqueness of solutions of the linear Jacobi system
(`Commons.Analysis.ODE.exists_linearODE_solution_Icc`): every solution is `Y * (U-slot at 0) +
Yc * (Y-slot at 0)`, so `0 = C s = Y s * D 0 + Yc s * C 0`. -/

open Bundle in
/-- **The "cosine" fundamental solution.**  The same linear Jacobi system as
`Submission.JacobiTensor.exists_jacobiSystem`, with the other initial condition `(1, 0)`. -/
theorem exists_jacobiSystem_cos
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    {x₀ : M} {v : E} {u w : ℝ → E}
    (htor : cov.torsion = 0) (h : Submission.Geodesic.HasChartGeodesic cov x₀ v u w)
    {a b : ℝ} (hab : a < b) (habt : Set.Icc a b ⊆ Set.Ioo (-2 : ℝ) 2)
    (h0 : (0 : ℝ) ∈ Set.Icc a b) :
    ∃ Y U : ℝ → E →L[ℝ] E, Y 0 = 1 ∧ U 0 = 0 ∧
      (∀ t ∈ Set.Icc a b,
        HasDerivAt Y (U t - (Submission.JacobiTensor.gammaOp (cov := cov) x₀ u w t).comp (Y t)) t) ∧
      (∀ t ∈ Set.Icc a b,
        HasDerivAt U (-((Submission.JacobiTensor.gammaOp (cov := cov) x₀ u w t).comp (U t))
          - (Submission.JacobiTensor.curvOp (cov := cov) x₀ u w t).comp (Y t)) t) := by
  have hc : ContinuousOn (Submission.JacobiTensor.jacobiSys (cov := cov) x₀ u w) (Set.Icc a b) :=
    (Submission.JacobiTensor.continuousOn_jacobiSys (cov := cov) htor h).mono habt
  obtain ⟨Z, hZ0, hZode, -⟩ :=
    Commons.Analysis.ODE.exists_linearODE_solution_Icc
      (E := (E →L[ℝ] E) × (E →L[ℝ] E)) hab hc h0
      ((1 : E →L[ℝ] E), (0 : E →L[ℝ] E))
  refine ⟨fun t => (Z t).1, fun t => (Z t).2, ?_, ?_, ?_, ?_⟩
  · simpa using congrArg Prod.fst hZ0
  · simpa using congrArg Prod.snd hZ0
  · intro t ht
    have h1 : HasDerivAt (fun s : ℝ => (Z s).1)
        ((Submission.JacobiTensor.jacobiSys (cov := cov) x₀ u w t (Z t)).1) t :=
      (hZode t ht).fst
    rw [Submission.JacobiTensor.jacobiSys_apply] at h1
    exact h1
  · intro t ht
    have h1 : HasDerivAt (fun s : ℝ => (Z s).2)
        ((Submission.JacobiTensor.jacobiSys (cov := cov) x₀ u w t (Z t)).2) t :=
      (hZode t ht).snd
    rw [Submission.JacobiTensor.jacobiSys_apply] at h1
    exact h1


open Bundle in
/-- **Span of the solution space of the chart Jacobi system.**  If `(Y, U)` and `(Yc, Uc)` are the
two fundamental solutions (initial values `(0,1)` and `(1,0)` at `t = 0`), then every solution
`(X, V)` on `[a,b] ∋ 0` is `X = Y * (V 0) + Yc * (X 0)`, `V = U * (V 0) + Uc * (X 0)`.

This is linearity of the (linear) Jacobi system together with the uniqueness part of
`Commons.Analysis.ODE.exists_linearODE_solution_Icc`. -/
theorem jacobi_solution_combination
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    {x₀ : M} {v : E} {u w : ℝ → E}
    (htor : cov.torsion = 0) (h : Submission.Geodesic.HasChartGeodesic cov x₀ v u w)
    {a b : ℝ} (hab : a < b) (habt : Set.Icc a b ⊆ Set.Ioo (-2 : ℝ) 2)
    (h0 : (0 : ℝ) ∈ Set.Icc a b)
    {Y U Yc Uc : ℝ → E →L[ℝ] E}
    (hY : ∀ t ∈ Set.Icc a b,
      HasDerivAt Y (U t - (Submission.JacobiTensor.gammaOp (cov := cov) x₀ u w t).comp (Y t)) t)
    (hU : ∀ t ∈ Set.Icc a b,
      HasDerivAt U (-((Submission.JacobiTensor.gammaOp (cov := cov) x₀ u w t).comp (U t))
        - (Submission.JacobiTensor.curvOp (cov := cov) x₀ u w t).comp (Y t)) t)
    (hYc : ∀ t ∈ Set.Icc a b,
      HasDerivAt Yc (Uc t - (Submission.JacobiTensor.gammaOp (cov := cov) x₀ u w t).comp (Yc t)) t)
    (hUc : ∀ t ∈ Set.Icc a b,
      HasDerivAt Uc (-((Submission.JacobiTensor.gammaOp (cov := cov) x₀ u w t).comp (Uc t))
        - (Submission.JacobiTensor.curvOp (cov := cov) x₀ u w t).comp (Yc t)) t)
    (hY0 : Y 0 = 0) (hU0 : U 0 = 1) (hYc0 : Yc 0 = 1) (hUc0 : Uc 0 = 0)
    {X V : ℝ → E →L[ℝ] E}
    (hX : ∀ t ∈ Set.Icc a b,
      HasDerivAt X (V t - (Submission.JacobiTensor.gammaOp (cov := cov) x₀ u w t).comp (X t)) t)
    (hV : ∀ t ∈ Set.Icc a b,
      HasDerivAt V (-((Submission.JacobiTensor.gammaOp (cov := cov) x₀ u w t).comp (V t))
        - (Submission.JacobiTensor.curvOp (cov := cov) x₀ u w t).comp (X t)) t) :
    ∀ t ∈ Set.Icc a b, X t = Y t * (V 0) + Yc t * (X 0) ∧
      V t = U t * (V 0) + Uc t * (X 0) := by
  set N : E →L[ℝ] E := X 0 with hN
  set M : E →L[ℝ] E := V 0 with hM
  -- the combination and its initial data
  set Xt : ℝ → E →L[ℝ] E := fun t => Y t * M + Yc t * N with hXt
  set Vt : ℝ → E →L[ℝ] E := fun t => U t * M + Uc t * N with hVt
  have hXt0 : Xt 0 = N := by simp [hXt, hY0, hYc0, hN]
  have hVt0 : Vt 0 = M := by simp [hVt, hU0, hUc0, hM]
  -- the combination solves the system
  have hXtode : ∀ t ∈ Set.Icc a b,
      HasDerivAt Xt (Vt t - (Submission.JacobiTensor.gammaOp (cov := cov) x₀ u w t).comp (Xt t)) t := by
    intro t ht
    have h1 : HasDerivAt (fun s => Y s * M + Yc s * N)
        ((U t - (Submission.JacobiTensor.gammaOp (cov := cov) x₀ u w t).comp (Y t)) * M
          + (Uc t - (Submission.JacobiTensor.gammaOp (cov := cov) x₀ u w t).comp (Yc t)) * N) t :=
      ((hY t ht).mul_const M).add ((hYc t ht).mul_const N)
    have h2 : (U t - (Submission.JacobiTensor.gammaOp (cov := cov) x₀ u w t).comp (Y t)) * M
          + (Uc t - (Submission.JacobiTensor.gammaOp (cov := cov) x₀ u w t).comp (Yc t)) * N
        = Vt t - (Submission.JacobiTensor.gammaOp (cov := cov) x₀ u w t).comp (Xt t) := by
      simp only [hXt, hVt, ← ContinuousLinearMap.mul_def]
      noncomm_ring
    exact h1.congr_deriv h2
  have hVtode : ∀ t ∈ Set.Icc a b,
      HasDerivAt Vt (-((Submission.JacobiTensor.gammaOp (cov := cov) x₀ u w t).comp (Vt t))
        - (Submission.JacobiTensor.curvOp (cov := cov) x₀ u w t).comp (Xt t)) t := by
    intro t ht
    have h1 : HasDerivAt (fun s => U s * M + Uc s * N)
        ((-((Submission.JacobiTensor.gammaOp (cov := cov) x₀ u w t).comp (U t))
            - (Submission.JacobiTensor.curvOp (cov := cov) x₀ u w t).comp (Y t)) * M
          + (-((Submission.JacobiTensor.gammaOp (cov := cov) x₀ u w t).comp (Uc t))
            - (Submission.JacobiTensor.curvOp (cov := cov) x₀ u w t).comp (Yc t)) * N) t :=
      ((hU t ht).mul_const M).add ((hUc t ht).mul_const N)
    have h2 : (-((Submission.JacobiTensor.gammaOp (cov := cov) x₀ u w t).comp (U t))
            - (Submission.JacobiTensor.curvOp (cov := cov) x₀ u w t).comp (Y t)) * M
          + (-((Submission.JacobiTensor.gammaOp (cov := cov) x₀ u w t).comp (Uc t))
            - (Submission.JacobiTensor.curvOp (cov := cov) x₀ u w t).comp (Yc t)) * N
        = -((Submission.JacobiTensor.gammaOp (cov := cov) x₀ u w t).comp (Vt t))
          - (Submission.JacobiTensor.curvOp (cov := cov) x₀ u w t).comp (Xt t) := by
      simp only [hXt, hVt, ← ContinuousLinearMap.mul_def]
      noncomm_ring
    exact h1.congr_deriv h2
  -- uniqueness
  have hc : ContinuousOn (Submission.JacobiTensor.jacobiSys (cov := cov) x₀ u w) (Set.Icc a b) :=
    (Submission.JacobiTensor.continuousOn_jacobiSys (cov := cov) htor h).mono habt
  obtain ⟨y, hy0, hyode, hyuniq⟩ :=
    Commons.Analysis.ODE.exists_linearODE_solution_Icc
      (E := (E →L[ℝ] E) × (E →L[ℝ] E)) hab hc h0 (N, M)
  have hXVsol : ∀ t ∈ Set.Icc a b,
      HasDerivAt (fun s : ℝ => (X s, V s))
        (Submission.JacobiTensor.jacobiSys (cov := cov) x₀ u w t (X t, V t)) t := by
    intro t ht
    have h1 := (hX t ht).prodMk (hV t ht)
    rw [Submission.JacobiTensor.jacobiSys_apply]
    simpa using h1
  have hXtVtsol : ∀ t ∈ Set.Icc a b,
      HasDerivAt (fun s : ℝ => (Xt s, Vt s))
        (Submission.JacobiTensor.jacobiSys (cov := cov) x₀ u w t (Xt t, Vt t)) t := by
    intro t ht
    have h1 := (hXtode t ht).prodMk (hVtode t ht)
    rw [Submission.JacobiTensor.jacobiSys_apply]
    simpa using h1
  have h1 : Set.EqOn (fun s : ℝ => (X s, V s)) (fun s : ℝ => (Xt s, Vt s)) (Set.Icc a b) := by
    have hyX := hyuniq _ (by simp [hN, hM]) hXVsol
    have hyXt := hyuniq _ (by simp [hN, hM, hXt0, hVt0]) hXtVtsol
    exact fun t ht => (hyX ht).trans (hyXt ht).symm
  intro t ht
  have := h1 ht
  simp only [Prod.mk.injEq] at this
  exact ⟨this.1, this.2⟩

open Bundle in
/-- **The reverse shape-operator identity** (inversion-free form).  With `(Y,U)` the solution with
initial value `(0,1)`, `(Yc,Uc)` the one with `(1,0)`, and `(C,D)` any solution with `C s = 0`,
one has
`Y s * D 0 + Yc s * C 0 = 0`,
i.e. the shape operator of the sphere of radius `s` around `γ s`, at the point `γ 0`, is
`(Y s)⁻¹ * Yc s` (the log-derivative of the backward solution `C`). -/
theorem jacobi_backward_orth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    {x₀ : M} {v : E} {u w : ℝ → E}
    (htor : cov.torsion = 0) (h : Submission.Geodesic.HasChartGeodesic cov x₀ v u w)
    {a b : ℝ} (hab : a < b) (habt : Set.Icc a b ⊆ Set.Ioo (-2 : ℝ) 2)
    (h0 : (0 : ℝ) ∈ Set.Icc a b)
    {Y U Yc Uc C D : ℝ → E →L[ℝ] E}
    (hY : ∀ t ∈ Set.Icc a b,
      HasDerivAt Y (U t - (Submission.JacobiTensor.gammaOp (cov := cov) x₀ u w t).comp (Y t)) t)
    (hU : ∀ t ∈ Set.Icc a b,
      HasDerivAt U (-((Submission.JacobiTensor.gammaOp (cov := cov) x₀ u w t).comp (U t))
        - (Submission.JacobiTensor.curvOp (cov := cov) x₀ u w t).comp (Y t)) t)
    (hYc : ∀ t ∈ Set.Icc a b,
      HasDerivAt Yc (Uc t - (Submission.JacobiTensor.gammaOp (cov := cov) x₀ u w t).comp (Yc t)) t)
    (hUc : ∀ t ∈ Set.Icc a b,
      HasDerivAt Uc (-((Submission.JacobiTensor.gammaOp (cov := cov) x₀ u w t).comp (Uc t))
        - (Submission.JacobiTensor.curvOp (cov := cov) x₀ u w t).comp (Yc t)) t)
    (hY0 : Y 0 = 0) (hU0 : U 0 = 1) (hYc0 : Yc 0 = 1) (hUc0 : Uc 0 = 0)
    (hC : ∀ t ∈ Set.Icc a b,
      HasDerivAt C (D t - (Submission.JacobiTensor.gammaOp (cov := cov) x₀ u w t).comp (C t)) t)
    (hD : ∀ t ∈ Set.Icc a b,
      HasDerivAt D (-((Submission.JacobiTensor.gammaOp (cov := cov) x₀ u w t).comp (D t))
        - (Submission.JacobiTensor.curvOp (cov := cov) x₀ u w t).comp (C t)) t)
    {s : ℝ} (hs : s ∈ Set.Icc a b) (hCs : C s = 0) :
    Y s * (D 0) + Yc s * (C 0) = 0 := by
  have hcomb := jacobi_solution_combination (cov := cov) htor h hab habt h0
    hY hU hYc hUc hY0 hU0 hYc0 hUc0 hC hD
  have := (hcomb s hs).1
  rw [hCs] at this
  exact this.symm


open Bundle in
/-- Field form of `jacobi_backward_orth`: for every direction `w` one has
`Y s (D 0 w) + Yc s (C 0 w) = 0`.  This is the form in which the identity is consumed by the
Jacobi-field (column) arguments. -/
theorem jacobi_backward_orth_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    {x₀ : M} {v : E} {u w : ℝ → E}
    (htor : cov.torsion = 0) (h : Submission.Geodesic.HasChartGeodesic cov x₀ v u w)
    {a b : ℝ} (hab : a < b) (habt : Set.Icc a b ⊆ Set.Ioo (-2 : ℝ) 2)
    (h0 : (0 : ℝ) ∈ Set.Icc a b)
    {Y U Yc Uc C D : ℝ → E →L[ℝ] E}
    (hY : ∀ t ∈ Set.Icc a b,
      HasDerivAt Y (U t - (Submission.JacobiTensor.gammaOp (cov := cov) x₀ u w t).comp (Y t)) t)
    (hU : ∀ t ∈ Set.Icc a b,
      HasDerivAt U (-((Submission.JacobiTensor.gammaOp (cov := cov) x₀ u w t).comp (U t))
        - (Submission.JacobiTensor.curvOp (cov := cov) x₀ u w t).comp (Y t)) t)
    (hYc : ∀ t ∈ Set.Icc a b,
      HasDerivAt Yc (Uc t - (Submission.JacobiTensor.gammaOp (cov := cov) x₀ u w t).comp (Yc t)) t)
    (hUc : ∀ t ∈ Set.Icc a b,
      HasDerivAt Uc (-((Submission.JacobiTensor.gammaOp (cov := cov) x₀ u w t).comp (Uc t))
        - (Submission.JacobiTensor.curvOp (cov := cov) x₀ u w t).comp (Yc t)) t)
    (hY0 : Y 0 = 0) (hU0 : U 0 = 1) (hYc0 : Yc 0 = 1) (hUc0 : Uc 0 = 0)
    (hC : ∀ t ∈ Set.Icc a b,
      HasDerivAt C (D t - (Submission.JacobiTensor.gammaOp (cov := cov) x₀ u w t).comp (C t)) t)
    (hD : ∀ t ∈ Set.Icc a b,
      HasDerivAt D (-((Submission.JacobiTensor.gammaOp (cov := cov) x₀ u w t).comp (D t))
        - (Submission.JacobiTensor.curvOp (cov := cov) x₀ u w t).comp (C t)) t)
    {s : ℝ} (hs : s ∈ Set.Icc a b) (hCs : C s = 0) (z : E) :
    Y s (D 0 z) + Yc s (C 0 z) = 0 := by
  have h := jacobi_backward_orth (cov := cov) htor h hab habt h0
    hY hU hYc hUc hY0 hU0 hYc0 hUc0 hC hD hs hCs
  have h2 := congrArg (fun (L : E →L[ℝ] E) => L z) h
  simpa using h2

/-- **The geodesic sphere of radius `π - arccos (1-c)` around `q` is small.**  In the setting of
`Work.Diff.C.dip_far_ball` (`hHess`/`hgrad`/`hsmC`/`hcont`: the metric is the round unit sphere up to
`ε₁`; `p`, `e` orthonormal; `q := qpt hmet p e (Fin.succ k)`, the point at distance `π/2` from `p`),
any two points `x, x'` at distance exactly `π - arccos (1-c)` from `q` satisfy

`rdist x x' ≤ π * (π - arccos (1-c)) * sin (π - arccos (1-c)) + 100 * ε₁ * π`.

The region of `hHess` is exactly `{y : rdist q y < π - arccos (1-c)}`, so the Hessian comparison is
available along the whole minimising ray up to (and by a limit at) the radius `ρ` of the statement.
On the round unit sphere the point set `{y : rdist q y = ρ}` is a round sphere of radius `sin ρ`
and hence of diameter `2(π - ρ) ≤ πρ sin ρ`; the factor `ρ ≤ π` and the additive `100 ε₁ π` are the
generous slack of the application, which only needs `≤ 256(√c + ε₁π)` (recall
`sin (π - arccos (1-c)) ≤ √(2c)`, so the main term is at most `π²√(2c) ≤ 13.96√c`).

Intended route: both `x` and `x'` are reached by minimising unit-speed rays from `q`
(`Submission.HopfRinow.exists_geodesic_riemannianEDist_eq`), with directions `v`, `v'`.  The
derivative of the map `v ↦ GExp q (ρ • v)` in a direction `w ⊥ v` is the Jacobi field `J` along
`γ_v` with `J(0) = 0`, `J'(0) = ρ w`; from `hHess` (via `Work.Diff.C.rhess_comp` for `cos ∘ rdist q`
with `Real.deriv_cos`, plus the eikonal identity `hgrad` and `sin (rdist q ·) > 0`) one gets the
shape-operator bound `|Hess (rdist q)(γ t)(V,V) - cot t ‖V‖²| ≤ ε₁‖V‖²/sin t` for `V ⊥ γ'`,
`t ∈ (0,ρ)`.  The Riccati/Sturm comparison for `t ↦ log ‖J(t)‖ - log (sin t)` — with the limit
`‖J(t)‖/(t‖J'(0)‖) → 1` at `0⁺` (smoothness at the centre) and the pointwise error bound — gives
`‖J(t)‖ ≤ (sin t + C ε₁)‖J'(0)‖` for `t ∈ (0,ρ)`; integrating the derivative along the geodesic of
directions joining `v` to `v'` (the unit sphere has diameter `π`) bounds `rdist x x'` by
`π ρ sin ρ + C' ε₁ π`.  Only the shape `π ρ sin ρ + C' ε₁ π` with `C' ≤ 100` matters. -/
theorem far_sphere_size
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ((⊤ : ENat) : WithTop ENat) E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [CovariantDerivative.ContMDiffCovariantDerivative cov ((⊤ : ENat) : WithTop ENat)]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {α c ε₁ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hc : 0 < c) (hc1 : c ≤ 1 / 4)
    (hε₁ : 0 ≤ ε₁) (hnum1 : 3 * c ≤ 1 - Real.cos α) (hnum2 : 4 * ε₁ * Real.pi < c)
    {p : M} {e : Fin (Module.finrank ℝ E) → TangentSpace I p}
    (hON : ∀ i j, Inner.inner ℝ (e i) (e j) = if i = j then 1 else 0)
    (hsmC : ∀ (q y : M), -1 + c ≤ Work.Diff.C.fcos (I := I) (M := M) q y →
      ContMDiffAt I (modelWithCornersSelf ℝ ℝ) ((⊤ : ENat) : WithTop ENat) (Work.Diff.C.fcos (I := I) (M := M) q) y)
    (hHess : ∀ q : M, Work.Diff.C.HessBoundRegion (I := I) (M := M) cov c ε₁ (Work.Diff.C.fcos (I := I) (M := M) q))
    (hcont : ∀ q : M, Continuous (Work.Diff.C.fcos (I := I) (M := M) q))
    (hgrad : ∀ (q y : M), -1 + c < Work.Diff.C.fcos (I := I) (M := M) q y →
      Inner.inner ℝ (Work.Diff.C.rgrad (I := I) (M := M) (Work.Diff.C.fcos (I := I) (M := M) q) y)
        (Work.Diff.C.rgrad (I := I) (M := M) (Work.Diff.C.fcos (I := I) (M := M) q) y)
        = 1 - (Work.Diff.C.fcos (I := I) (M := M) q y) ^ 2)
    (hinit : Work.Diff.C.InitData (I := I) (M := M) (cov := cov) hmet p e)
    (hdiam : ∀ y : M, Work.Diff.C.rdist (I := I) (M := M) p y ≤ Real.pi)
    {k : Fin (Module.finrank ℝ E)} :
    ∀ x x' : M,
      Work.Diff.C.rdist (I := I) (M := M) (Work.Diff.C.qpt (I := I) (M := M) (cov := cov) hmet p e (Fin.succ k)) x
          = Real.pi - Real.arccos (1 - c) →
      Work.Diff.C.rdist (I := I) (M := M) (Work.Diff.C.qpt (I := I) (M := M) (cov := cov) hmet p e (Fin.succ k)) x'
          = Real.pi - Real.arccos (1 - c) →
      Work.Diff.C.rdist (I := I) (M := M) x x'
        ≤ Real.pi * (Real.pi - Real.arccos (1 - c)) * Real.sin (Real.pi - Real.arccos (1 - c))
          + 100 * ε₁ * Real.pi := by
  sorry

end Work.Diff.C
