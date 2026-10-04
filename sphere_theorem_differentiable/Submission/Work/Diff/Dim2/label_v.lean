import Mathlib
import Submission.Work.Diff.Dim2.Lib
import Submission.Work.Diff.C.Defs
import Submission.Work.Diff.C.GExp_localInverse
import Submission.Work.Diff.Dim2.tau
import Submission.Work.Diff.C.rgrad_rdist_eikonal
import Submission.Work.Diff.C.rdist_continuous
import Submission.Work.Diff.Dim2.crossing_time
import Submission.GSFlow
import Submission.Work.Diff.ODE.eqOn_Ioo_of_isXCurveOn
import Submission.Work.Diff.Dim2.flow_g_interval
import Submission.Work.Diff.Dim2.local_left_strictMono

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Work.Diff.Dim2

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter Submission.Geodesic

section Helpers

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
variable [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
variable [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [RegularSpace M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
  [ContMDiffCovariantDerivative cov ∞]

/-- **Time-translation invariance of a flow given by its derivative axiom.**  Although `Φ s t x`
is indexed by *absolute* times `s`, `t`, the differential equation is autonomous, so the position
depends only on the elapsed time: `Φ s t x = Φ 0 (t - s) x`.  (Uniqueness of solutions of the ODE,
`Work.Diff.ODE.eqOn_Ioo_of_isXCurveOn`, applied to the two curves
`τ ↦ Φ s (s + τ) x` and `τ ↦ Φ 0 τ x`.) -/
lemma flow_translate
    {V : (x : M) → TangentSpace I x} {Φ : ℝ → ℝ → M → M}
    (hVsm : ContMDiff I (I.prod (modelWithCornersSelf ℝ E)) ∞
      (fun y : M => (⟨y, V y⟩ : Bundle.TotalSpace E (TangentSpace I))))
    (hΦself : ∀ s x, Φ s s x = x)
    (hΦderiv : ∀ s t x, HasMFDerivAt 𝓘(ℝ,ℝ) I (fun τ : ℝ => Φ s τ x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (V (Φ s t x)))) :
    ∀ s t x, Φ s t x = Φ 0 (t - s) x := by
  intro s t x
  have hXs : ContMDiff (𝓘(ℝ,ℝ).prod I) I.tangent ∞
      (fun p : ℝ × M => (⟨p.2, V p.2⟩ : TangentBundle I M)) := by
    have h2 : ContMDiff (𝓘(ℝ,ℝ).prod I) I ∞ (fun p : ℝ × M => p.2) := contMDiff_snd
    exact hVsm.comp h2
  have hmem2 : t - s ∈ Set.Ioo (-(|t - s| + 1)) (|t - s| + 1) := by
    rw [Set.mem_Ioo]
    constructor <;> linarith [abs_nonneg (t - s), neg_abs_le (t - s), le_abs_self (t - s)]
  have h₁ : Work.Diff.ODE.IsXCurveOn (fun _ : ℝ => V) s x (|t - s| + 1)
      (fun τ' => Φ s (s + τ') x) := by
    refine ⟨?_, fun τ' _ => ?_⟩
    · show Φ s (s + 0) x = x
      rw [add_zero]; exact hΦself s x
    · have h1 : HasMFDerivAt 𝓘(ℝ,ℝ) I (fun ρ : ℝ => Φ s ρ x) (s + τ')
          ((1 : ℝ →L[ℝ] ℝ).smulRight (V (Φ s (s + τ') x))) := hΦderiv s (s + τ') x
      have h2 : HasMFDerivAt 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) (fun τ'' : ℝ => s + τ'') τ' (1 : ℝ →L[ℝ] ℝ) :=
        ((hasFDerivAt_id τ').const_add s).hasMFDerivAt
      rw [← ContinuousLinearMap.comp_id ((1 : ℝ →L[ℝ] ℝ).smulRight (V (Φ s (s + τ') x)))]
      exact h1.comp τ' h2
  have h₂ : Work.Diff.ODE.IsXCurveOn (fun _ : ℝ => V) s x (|t - s| + 1)
      (fun τ' => Φ 0 τ' x) :=
    ⟨hΦself 0 x, fun τ' _ => hΦderiv 0 τ' x⟩
  have hpos : (0:ℝ) < |t - s| + 1 := by positivity
  have h := Work.Diff.ODE.eqOn_Ioo_of_isXCurveOn (I := I) hXs hpos h₁ h₂ hmem2
  simpa using h

/-- **The derivative of a function is `-1` along the flow of `V` when `V = -∇g` and `g` has unit
gradient.** -/
lemma mfderiv_flow_eq_neg_one
    {V : (x : M) → TangentSpace I x} {g : M → ℝ} {lo hi : ℝ}
    (hinner : ∀ (y : M) (w : TangentSpace I y), mvfderiv I g y w
      = inner ℝ (Work.Diff.C.rgrad (I := I) (M := M) g y) w)
    (heik : ∀ y : M, inner ℝ (Work.Diff.C.rgrad (I := I) (M := M) g y)
      (Work.Diff.C.rgrad (I := I) (M := M) g y) = 1)
    (hval : ∀ y : M, g y ∈ Set.Icc lo hi →
      V y = - Work.Diff.C.rgrad (I := I) (M := M) g y) :
    ∀ y : M, g y ∈ Set.Icc lo hi → mvfderiv I g y (V y) = -1 := by
  intro y hy
  rw [hval y hy, map_neg, hinner y (Work.Diff.C.rgrad (I := I) (M := M) g y), heik y]

/-- **The derivative along the flow.**  If `mvfderiv g (V) = -1` on the window `[lo,hi]` and `g` is
differentiable there, then for any trajectory of `Φ` the function `τ ↦ g (Φ 0 τ x)` has derivative
`-1` at every time at which its value lies in `[lo,hi]`. -/
lemma hasDerivAt_flow_of_mfderiv_eq_neg_one
    {V : (x : M) → TangentSpace I x} {Φ : ℝ → ℝ → M → M} {g : M → ℝ} {lo hi : ℝ}
    (hΦderiv : ∀ s t x, HasMFDerivAt 𝓘(ℝ,ℝ) I (fun τ : ℝ => Φ s τ x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (V (Φ s t x))))
    (hgsm : ∀ y : M, g y ∈ Set.Icc lo hi → MDifferentiableAt I 𝓘(ℝ,ℝ) g y)
    (hval : ∀ y : M, g y ∈ Set.Icc lo hi → mvfderiv I g y (V y) = -1)
    {x : M} {s : ℝ} (hs : g (Φ 0 s x) ∈ Set.Icc lo hi) :
    HasDerivAt (fun τ : ℝ => g (Φ 0 τ x)) (-1) s := by
  have hgmd : MDifferentiableAt I 𝓘(ℝ,ℝ) g (Φ 0 s x) := hgsm _ hs
  have hfl : HasMFDerivAt 𝓘(ℝ,ℝ) I (fun τ : ℝ => Φ 0 τ x) s
      ((1 : ℝ →L[ℝ] ℝ).smulRight (V (Φ 0 s x))) := hΦderiv 0 s x
  have hcomp : HasMFDerivAt 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) (fun τ : ℝ => g (Φ 0 τ x)) s
      ((mfderiv I 𝓘(ℝ,ℝ) g (Φ 0 s x)) ∘L ((1 : ℝ →L[ℝ] ℝ).smulRight (V (Φ 0 s x)))) :=
    hgmd.hasMFDerivAt.comp s hfl
  have hCLeq : (mfderiv I 𝓘(ℝ,ℝ) g (Φ 0 s x)) ∘L ((1 : ℝ →L[ℝ] ℝ).smulRight (V (Φ 0 s x)))
      = (1 : ℝ →L[ℝ] ℝ).smulRight (mvfderiv I g (Φ 0 s x) (V (Φ 0 s x))) := by
    apply ContinuousLinearMap.ext
    intro a
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.one_apply, map_smul]
    rfl
  have hfd : HasFDerivAt (fun τ : ℝ => g (Φ 0 τ x))
      ((1 : ℝ →L[ℝ] ℝ).smulRight (mvfderiv I g (Φ 0 s x) (V (Φ 0 s x)))) s := by
    rw [← hCLeq]
    exact hcomp.hasFDerivAt
  have hval' : mvfderiv I g (Φ 0 s x) (V (Φ 0 s x)) = -1 := hval _ hs
  rw [hval'] at hfd
  simpa [ContinuousLinearMap.smulRight_apply] using hfd.hasDerivAt

/-- **`z ↦ (g z)⁻¹ • Φq z` is smooth on the annulus `γ/4 ≤ g ≤ 3γ/2`.** -/
lemma inv_smul_Phiq_contMDiffAt
    {q : M} {Φq : M → TangentSpace I q} {g : M → ℝ} {v γ : ℝ}
    (hγ : 0 < γ) (h5g : 5 * γ / 2 < v)
    (hsmQ : ∀ y : M, 0 < g y → g y < v → CMDiffAt ∞ g y)
    (hsmΦq : ∀ y : M, g y < v →
      ContMDiffAt I (modelWithCornersSelf ℝ (TangentSpace I q)) ∞ Φq y) :
    ∀ y : M, γ / 4 ≤ g y → g y ≤ 3 * γ / 2 →
      ContMDiffAt I (modelWithCornersSelf ℝ (TangentSpace I q)) ∞
        (fun z : M => (g z)⁻¹ • Φq z) y := by
  intro y hy1 hy2
  have hpos : 0 < g y := lt_of_lt_of_le (by linarith : (0:ℝ) < γ / 4) hy1
  have hlt : g y < v := lt_of_le_of_lt hy2 (by linarith)
  have h1 : ContMDiffAt I 𝓘(ℝ,ℝ) ∞ (fun z : M => (g z)⁻¹) y :=
    (hsmQ y hpos hlt).inv₀ (ne_of_gt hpos)
  have h2 : ContMDiffAt I (modelWithCornersSelf ℝ (TangentSpace I q)) ∞ Φq y := hsmΦq y hlt
  have h3 : ContMDiffAt I (modelWithCornersSelf ℝ (TangentSpace I q)) ∞
      ((fun z : M => (g z)⁻¹) • Φq) y := h1.smul h2
  have heq : (fun z : M => (g z)⁻¹ • Φq z) = ((fun z : M => (g z)⁻¹) • Φq) := by
    funext z; rfl
  rw [heq]; exact h3

/-- **`z ↦ (g z)⁻¹ • Φq z` is constant along a trajectory while `g` stays in the annulus.**  The
hypothesis `hconst` says that the directional derivative of `H z := (g z)⁻¹ • Φq z` in the direction
of the flow field `V` vanishes on the annulus; since the trajectory is an integral curve of `V`, the
mean value inequality gives `H (Φ 0 T x) = H (Φ 0 0 x)`. -/
lemma inv_smul_Phiq_const_along_flow
    {q : M} {Φq : M → TangentSpace I q} {g : M → ℝ} {γ : ℝ}
    {V : (x : M) → TangentSpace I x} {Φ : ℝ → ℝ → M → M}
    (hΦsm : ContMDiff ((𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ)).prod I) I ∞
      (fun q : (ℝ × ℝ) × M => Φ q.1.1 q.1.2 q.2))
    (hΦself : ∀ s x, Φ s s x = x)
    (hΦderiv : ∀ s t x, HasMFDerivAt 𝓘(ℝ,ℝ) I (fun τ : ℝ => Φ s τ x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (V (Φ s t x))))
    (hKc : ∀ y : M, γ / 4 ≤ g y → g y ≤ 3 * γ / 2 →
      ContMDiffAt I (modelWithCornersSelf ℝ (TangentSpace I q)) ∞
        (fun z : M => (g z)⁻¹ • Φq z) y)
    (hconst : ∀ y : M, γ / 4 ≤ g y → g y ≤ 3 * γ / 2 →
      mfderiv I (modelWithCornersSelf ℝ (TangentSpace I q))
        (fun z : M => (g z)⁻¹ • Φq z) y (V y) = 0)
    {x : M} {T : ℝ}
    (hT : ∀ s ∈ Set.Icc (min 0 T) (max 0 T),
      γ / 4 ≤ g (Φ 0 s x) ∧ g (Φ 0 s x) ≤ 3 * γ / 2) :
    (g (Φ 0 T x))⁻¹ • Φq (Φ 0 T x) = (g x)⁻¹ • Φq x := by
  have hslice : ∀ s : ℝ, ContMDiffAt 𝓘(ℝ,ℝ) I ∞ (fun τ : ℝ => Φ 0 τ x) s := by
    intro s
    have h1 : ContMDiffAt 𝓘(ℝ,ℝ) (𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ)) ∞
        (fun τ : ℝ => (((0 : ℝ), τ) : ℝ × ℝ)) s :=
      ContMDiffAt.prodMk (contMDiffAt_const (c := (0 : ℝ)) (x := s)) contMDiffAt_id
    have h2 : ContMDiffAt 𝓘(ℝ,ℝ) ((𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ)).prod I) ∞
        (fun τ : ℝ => ((((0 : ℝ), τ) : ℝ × ℝ), x)) s :=
      ContMDiffAt.prodMk h1 (contMDiffAt_const (c := x) (x := s))
    exact ContMDiffAt.comp s (hΦsm ((((0 : ℝ), s) : ℝ × ℝ), x)) h2
  have hderiv0 : ∀ s ∈ Set.Icc (min 0 T) (max 0 T),
      deriv ((fun z : M => (g z)⁻¹ • Φq z) ∘ fun τ : ℝ => Φ 0 τ x) s = 0 := by
    intro s hs
    obtain ⟨hy1, hy2⟩ := hT s hs
    have hKmd : MDifferentiableAt I (modelWithCornersSelf ℝ (TangentSpace I q))
        (fun z : M => (g z)⁻¹ • Φq z) (Φ 0 s x) := (hKc (Φ 0 s x) hy1 hy2).mdifferentiableAt (by simp)
    have hγmd : MDifferentiableAt 𝓘(ℝ,ℝ) I (fun τ : ℝ => Φ 0 τ x) s :=
      (hΦderiv 0 s x).mdifferentiableAt
    have hkey := Commons.Geometry.Manifold.Tangent.mvfderiv_comp_curve (I := I)
      (g := fun z : M => (g z)⁻¹ • Φq z) (γ := fun τ : ℝ => Φ 0 τ x) (t := s) hKmd hγmd
    have hstep : (mfderiv 𝓘(ℝ,ℝ) I (fun τ : ℝ => Φ 0 τ x)) s (1 : ℝ) = V (Φ 0 s x) := by
      rw [(hΦderiv 0 s x).mfderiv]
      change ((1 : ℝ →L[ℝ] ℝ).smulRight (V (Φ 0 s x))) (1 : ℝ) = V (Φ 0 s x)
      rw [ContinuousLinearMap.smulRight_apply]
      simp
    have hzero : mvfderiv I (fun z : M => (g z)⁻¹ • Φq z) (Φ 0 s x) (V (Φ 0 s x)) = 0 := by
      show (NormedSpace.fromTangentSpace ((g (Φ 0 s x))⁻¹ • Φq (Φ 0 s x))).toContinuousLinearMap
        ((mfderiv I (modelWithCornersSelf ℝ (TangentSpace I q))
          (fun z : M => (g z)⁻¹ • Φq z) (Φ 0 s x)) (V (Φ 0 s x))) = 0
      rw [hconst (Φ 0 s x) hy1 hy2, map_zero]
    rw [hstep] at hkey
    exact hkey.symm.trans hzero
  have hdiff : ∀ s ∈ Set.Icc (min 0 T) (max 0 T),
      DifferentiableAt ℝ ((fun z : M => (g z)⁻¹ • Φq z) ∘ fun τ : ℝ => Φ 0 τ x) s := by
    intro s hs
    obtain ⟨hy1, hy2⟩ := hT s hs
    have h1 := (hKc (Φ 0 s x) hy1 hy2).comp s (hslice s)
    exact (h1.contDiffAt.differentiableAt (by simp)).congr_of_eventuallyEq
      (Filter.EventuallyEq.of_eq (by rfl))
  have hnorm : ∀ s ∈ Set.Icc (min 0 T) (max 0 T),
      ‖deriv ((fun z : M => (g z)⁻¹ • Φq z) ∘ fun τ : ℝ => Φ 0 τ x) s‖ ≤ 0 := by
    intro s hs
    rw [hderiv0 s hs, norm_zero]
  have hle := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ)
    (f := (fun z : M => (g z)⁻¹ • Φq z) ∘ fun τ : ℝ => Φ 0 τ x) hdiff hnorm
    (convex_Icc (min 0 T) (max 0 T)) (Set.mem_Icc.mpr ⟨min_le_left _ _, le_max_left _ _⟩)
    (Set.mem_Icc.mpr ⟨min_le_right _ _, le_max_right _ _⟩)
  have hEq : (g (Φ 0 T x))⁻¹ • Φq (Φ 0 T x) = (g (Φ 0 0 x))⁻¹ • Φq (Φ 0 0 x) := by
    have h0 : ‖(g (Φ 0 T x))⁻¹ • Φq (Φ 0 T x)
        - (g (Φ 0 0 x))⁻¹ • Φq (Φ 0 0 x)‖ ≤ 0 := by
      simpa [Function.comp_def] using hle
    exact sub_eq_zero.mp (norm_le_zero_iff.mp h0)
  rwa [hΦself 0 x] at hEq

/-- **The reverse-flow first variation along a trajectory.**  At a point `y` at which `V` is an
ascent direction for the distance from `p`, the distance from `p` strictly decreases along the
backward flow. -/
lemma flow_left_lt_rdist
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (hpinch : QuarterPinched cov)
    {V : (x : M) → TangentSpace I x} {Φ : ℝ → ℝ → M → M}
    (hΦsm : ContMDiff ((𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ)).prod I) I ∞
      (fun q : (ℝ × ℝ) × M => Φ q.1.1 q.1.2 q.2))
    (hΦself : ∀ s x, Φ s s x = x)
    (hΦderiv : ∀ s t x, HasMFDerivAt 𝓘(ℝ,ℝ) I (fun τ : ℝ => Φ s τ x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (V (Φ s t x))))
    {p : M} {y : M} (hV : Submission.GSField.IsAscentAt hmet p y (V y)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ Set.Ioo (0:ℝ) δ,
      Work.Diff.C.rdist (I := I) (M := M) p (Φ 0 (-t) y)
        < Work.Diff.C.rdist (I := I) (M := M) p y := by
  have hself : Φ 0 0 y = y := hΦself 0 y
  have hσsm : ContMDiffAt 𝓘(ℝ,ℝ) I ∞ (fun s : ℝ => Φ 0 (-s) y) (0 : ℝ) := by
    have hneg : ContMDiffAt 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) ∞ (fun s : ℝ => -s) (0 : ℝ) :=
      contMDiff_neg 𝓘(ℝ,ℝ) ∞ (0 : ℝ)
    have h1 : ContMDiffAt 𝓘(ℝ,ℝ) (𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ)) ∞
        (fun s : ℝ => (((0 : ℝ), -s) : ℝ × ℝ)) (0 : ℝ) :=
      ContMDiffAt.prodMk (contMDiffAt_const (c := (0 : ℝ)) (x := (0 : ℝ))) hneg
    have h2 : ContMDiffAt 𝓘(ℝ,ℝ) ((𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ)).prod I) ∞
        (fun s : ℝ => ((((0 : ℝ), -s) : ℝ × ℝ), y)) (0 : ℝ) :=
      ContMDiffAt.prodMk h1 (contMDiffAt_const (c := y) (x := (0 : ℝ)))
    have h3 : ContMDiffAt 𝓘(ℝ,ℝ) I ∞
        ((fun q : (ℝ × ℝ) × M => Φ q.1.1 q.1.2 q.2)
          ∘ fun s : ℝ => ((((0 : ℝ), -s) : ℝ × ℝ), y)) (0 : ℝ) :=
      ContMDiffAt.comp (0 : ℝ) (hΦsm ((((0 : ℝ), -(0 : ℝ)) : ℝ × ℝ), y)) h2
    exact h3
  have hvel : Submission.Geodesic.curveVelocity (I := I) (fun s : ℝ => Φ 0 (-s) y) 0 = - V y := by
    have hg : HasMFDerivAt 𝓘(ℝ,ℝ) I (fun τ : ℝ => Φ 0 τ y) (-(0 : ℝ))
        ((1 : ℝ →L[ℝ] ℝ).smulRight (V (Φ 0 (-(0 : ℝ)) y))) :=
      hΦderiv 0 (-(0 : ℝ)) y
    have hn : HasMFDerivAt 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) (fun s : ℝ => -s) (0 : ℝ)
        (-(1 : ℝ →L[ℝ] ℝ)) :=
      (hasMFDerivAt_id (I := 𝓘(ℝ,ℝ)) (0 : ℝ)).neg
    have hcomp := hg.comp (0 : ℝ) hn
    have hNval : (-(1 : ℝ →L[ℝ] ℝ)) (1 : ℝ) = -(1 : ℝ) := by
      rw [neg_apply, ContinuousLinearMap.one_def, ContinuousLinearMap.id_apply]
    have hGval : ((1 : ℝ →L[ℝ] ℝ).smulRight (V (Φ 0 (-(0 : ℝ)) y))) (-(1 : ℝ))
        = - V (Φ 0 (-(0 : ℝ)) y) := by
      rw [ContinuousLinearMap.smulRight_apply]
      rw [show (1 : ℝ →L[ℝ] ℝ) (-(1 : ℝ)) = -(1 : ℝ) by
        rw [ContinuousLinearMap.one_def, ContinuousLinearMap.id_apply]]
      rw [neg_one_smul]
    have hself' : Φ 0 (-(0 : ℝ)) y = y := by
      rw [neg_zero]; exact hself
    have hfun : (fun s : ℝ => Φ 0 (-s) y)
        = ((fun τ : ℝ => Φ 0 τ y) ∘ (fun s : ℝ => -s)) := rfl
    rw [Submission.Geodesic.curveVelocity_apply, hfun, hcomp.mfderiv]
    change ((1 : ℝ →L[ℝ] ℝ).smulRight (V (Φ 0 (-(0 : ℝ)) y)))
        ((-(1 : ℝ →L[ℝ] ℝ)) (1 : ℝ)) = - V y
    rw [hNval, hGval, hself']
  obtain ⟨δ, hδ, hlt⟩ := Submission.GSFlow.flow_left_lt (cov := cov) hmet htor hpinch hV
    (by simpa using hself) hσsm hvel
  refine ⟨δ, hδ, fun t ht => ?_⟩
  have h1 := hlt t ht
  have hfin1 : Manifold.riemannianEDist I p (Φ 0 (-t) y) ≠ ⊤ :=
    (Submission.HopfRinow.riemannianEDist_lt_top (I := I) (cov := cov) hmet htor p _).ne
  have hfin2 : Manifold.riemannianEDist I p y ≠ ⊤ :=
    (Submission.HopfRinow.riemannianEDist_lt_top (I := I) (cov := cov) hmet htor p y).ne
  show (Manifold.riemannianEDist I p (Φ 0 (-t) y)).toReal
    < (Manifold.riemannianEDist I p y).toReal
  exact (ENNReal.toReal_lt_toReal hfin1 hfin2).mpr h1

/-- **The velocity of a flow trajectory is the field.** -/
lemma mfderiv_flow_apply_one
    {V : (x : M) → TangentSpace I x} {Φ : ℝ → ℝ → M → M}
    (hΦderiv : ∀ s t x, HasMFDerivAt 𝓘(ℝ,ℝ) I (fun τ : ℝ => Φ s τ x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (V (Φ s t x)))) (x : M) (s : ℝ) :
    (mfderiv 𝓘(ℝ,ℝ) I (fun τ : ℝ => Φ 0 τ x)) s (1 : ℝ) = V (Φ 0 s x) := by
  rw [(hΦderiv 0 s x).mfderiv]
  change ((1 : ℝ →L[ℝ] ℝ).smulRight (V (Φ 0 s x))) (1 : ℝ) = V (Φ 0 s x)
  rw [ContinuousLinearMap.smulRight_apply]
  simp

/-- **`d(q,·)` decreases at unit speed along the flow of `V = -∇d(q,·)` on the annulus.** -/
lemma rdistQ_flow_eq_neg_one
    {q : M} {v γ : ℝ} (hγ : 0 < γ) (h5g : 5 * γ / 2 < v)
    {V : (x : M) → TangentSpace I x}
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    (hsmQ : ∀ y : M, 0 < Work.Diff.C.rdist (I := I) (M := M) q y →
      Work.Diff.C.rdist (I := I) (M := M) q y < v →
      CMDiffAt ∞ (fun z : M => Work.Diff.C.rdist (I := I) (M := M) q z) y)
    (hvalq : ∀ y : M, γ / 4 ≤ Work.Diff.C.rdist (I := I) (M := M) q y →
      Work.Diff.C.rdist (I := I) (M := M) q y ≤ 5 * γ / 2 →
      V y = - Work.Diff.C.rgrad (I := I) (M := M)
        (fun z : M => Work.Diff.C.rdist (I := I) (M := M) q z) y) :
    ∀ y : M, γ / 4 ≤ Work.Diff.C.rdist (I := I) (M := M) q y →
      Work.Diff.C.rdist (I := I) (M := M) q y ≤ 5 * γ / 2 →
      mvfderiv I (fun z : M => Work.Diff.C.rdist (I := I) (M := M) q z) y (V y) = -1 := by
  intro y h1 h2
  have hpos : 0 < Work.Diff.C.rdist (I := I) (M := M) q y := by linarith [h1, hγ]
  have hlt : Work.Diff.C.rdist (I := I) (M := M) q y < v := by linarith [h2, h5g]
  have heik := Work.Diff.C.rgrad_rdist_eikonal (I := I) (cov := cov) hmet htor (ne_of_gt hpos)
    (hsmQ y hpos hlt)
  have hinner : mvfderiv I (fun z : M => Work.Diff.C.rdist (I := I) (M := M) q z) y
      (Work.Diff.C.rgrad (I := I) (M := M)
        (fun z : M => Work.Diff.C.rdist (I := I) (M := M) q z) y)
      = inner ℝ (Work.Diff.C.rgrad (I := I) (M := M)
          (fun z : M => Work.Diff.C.rdist (I := I) (M := M) q z) y)
        (Work.Diff.C.rgrad (I := I) (M := M)
          (fun z : M => Work.Diff.C.rdist (I := I) (M := M) q z) y) := by
    rw [Work.Diff.C.inner_rgrad]
    rfl
  rw [hvalq y h1 h2, map_neg, hinner, heik]

/-- **The derivative of `d(q,·)` along a flow trajectory is `-1` while it stays in the annulus.** -/
lemma hasDerivAt_rdistQ_flow
    {q : M} {v γ : ℝ} (hγ : 0 < γ) (h5g : 5 * γ / 2 < v)
    {V : (x : M) → TangentSpace I x} {Φ : ℝ → ℝ → M → M}
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    (hsmQ : ∀ y : M, 0 < Work.Diff.C.rdist (I := I) (M := M) q y →
      Work.Diff.C.rdist (I := I) (M := M) q y < v →
      CMDiffAt ∞ (fun z : M => Work.Diff.C.rdist (I := I) (M := M) q z) y)
    (hvalq : ∀ y : M, γ / 4 ≤ Work.Diff.C.rdist (I := I) (M := M) q y →
      Work.Diff.C.rdist (I := I) (M := M) q y ≤ 5 * γ / 2 →
      V y = - Work.Diff.C.rgrad (I := I) (M := M)
        (fun z : M => Work.Diff.C.rdist (I := I) (M := M) q z) y)
    (hΦderiv : ∀ s t x, HasMFDerivAt 𝓘(ℝ,ℝ) I (fun τ : ℝ => Φ s τ x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (V (Φ s t x)))) :
    ∀ (x : M) (s : ℝ), γ / 4 ≤ Work.Diff.C.rdist (I := I) (M := M) q (Φ 0 s x) →
      Work.Diff.C.rdist (I := I) (M := M) q (Φ 0 s x) ≤ 5 * γ / 2 →
      HasDerivAt (fun τ : ℝ => Work.Diff.C.rdist (I := I) (M := M) q (Φ 0 τ x)) (-1) s := by
  intro x s h1 h2
  refine hasDerivAt_flow_of_mfderiv_eq_neg_one (lo := γ / 4) (hi := 5 * γ / 2)
    (g := fun z : M => Work.Diff.C.rdist (I := I) (M := M) q z) hΦderiv ?_ ?_ ⟨h1, h2⟩
  · intro y hy
    exact (hsmQ y (by linarith [hy.1, hγ]) (by linarith [hy.2, h5g])).mdifferentiableAt (by simp)
  · intro y hy
    exact rdistQ_flow_eq_neg_one (v := v) (γ := γ) hγ h5g hmet htor hsmQ hvalq y hy.1 hy.2

/-- **The unit `q`-direction at the level `g = c`.** -/
lemma norm_neg_inv_smul_Phiq
    {q : M} {Φq : M → TangentSpace I q} {g : M → ℝ} {v c : ℝ} (hc : 0 < c)
    (hnormQ : ∀ y : M, g y < v → g y = ‖Φq y‖)
    {y : M} (hyv : g y < v) (hyc : g y = c) :
    ‖- c⁻¹ • Φq y‖ = 1 := by
  rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg (inv_nonneg.mpr hc.le),
    ← hnormQ y hyv, hyc, inv_mul_cancel₀ (ne_of_gt hc)]

/-- **The slice of a smooth flow at a fixed point is smooth.** -/
lemma contMDiffAt_flow_slice
    {Φ : ℝ → ℝ → M → M}
    (hΦsm : ContMDiff ((𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ)).prod I) I ∞
      (fun q : (ℝ × ℝ) × M => Φ q.1.1 q.1.2 q.2)) (s : ℝ) (x : M) :
    ContMDiffAt 𝓘(ℝ,ℝ) I ∞ (fun τ : ℝ => Φ 0 τ x) s := by
  have h1 : ContMDiffAt 𝓘(ℝ,ℝ) (𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ)) ∞
      (fun τ : ℝ => (((0 : ℝ), τ) : ℝ × ℝ)) s :=
    ContMDiffAt.prodMk (contMDiffAt_const (c := (0 : ℝ)) (x := s)) contMDiffAt_id
  have h2 : ContMDiffAt 𝓘(ℝ,ℝ) ((𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ)).prod I) ∞
      (fun τ : ℝ => ((((0 : ℝ), τ) : ℝ × ℝ), x)) s :=
    ContMDiffAt.prodMk h1 (contMDiffAt_const (c := x) (x := s))
  exact ContMDiffAt.comp s (hΦsm ((((0 : ℝ), s) : ℝ × ℝ), x)) h2

/-- **The slice of a smooth flow at a fixed time is smooth in the base point.** -/
lemma contMDiffAt_flow_base
    {Φ : ℝ → ℝ → M → M}
    (hΦsm : ContMDiff ((𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ)).prod I) I ∞
      (fun q : (ℝ × ℝ) × M => Φ q.1.1 q.1.2 q.2)) (s : ℝ) (y : M) :
    ContMDiffAt I I ∞ (fun z : M => Φ 0 s z) y := by
  have h1 : ContMDiffAt I ((𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ)).prod I) ∞
      (fun z : M => ((((0 : ℝ), s) : ℝ × ℝ), z)) y :=
    ContMDiffAt.prodMk (contMDiffAt_const (c := (((0 : ℝ), s) : ℝ × ℝ)) (x := y)) contMDiffAt_id
  have h2 : ContMDiffAt I I ∞
      ((fun q : (ℝ × ℝ) × M => Φ q.1.1 q.1.2 q.2) ∘
        fun z : M => ((((0 : ℝ), s) : ℝ × ℝ), z)) y :=
    ContMDiffAt.comp (x := y) (f := fun z : M => ((((0 : ℝ), s) : ℝ × ℝ), z))
      (hΦsm ((((0 : ℝ), s) : ℝ × ℝ), y)) h1
  simpa [Function.comp_def] using h2

/-- **One-sided monotonicity of `d(p,·)` along the flow.**  At a point of the trajectory lying
in the ascent region, `d(p,·)` is strictly larger than slightly earlier on the trajectory. -/
lemma flow_c_mono
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (hpinch : QuarterPinched cov)
    {p q : M} {a γ : ℝ} {V : (x : M) → TangentSpace I x} {Φ : ℝ → ℝ → M → M}
    (hVsm : ContMDiff I (I.prod (modelWithCornersSelf ℝ E)) ∞
      (fun y : M => (⟨y, V y⟩ : Bundle.TotalSpace E (TangentSpace I))))
    (hΦsm : ContMDiff ((𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ)).prod I) I ∞
      (fun q : (ℝ × ℝ) × M => Φ q.1.1 q.1.2 q.2))
    (hΦself : ∀ s x, Φ s s x = x)
    (hΦcoc : ∀ s t u x, Φ t u (Φ s t x) = Φ s u x)
    (hΦderiv : ∀ s t x, HasMFDerivAt 𝓘(ℝ,ℝ) I (fun τ : ℝ => Φ s τ x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (V (Φ s t x))))
    (hasc : ∀ y : M, a / 4 ≤ Work.Diff.C.rdist (I := I) (M := M) p y →
      γ / 8 < Work.Diff.C.rdist (I := I) (M := M) q y →
      Submission.GSField.IsAscentAt hmet p y (V y))
    {x : M} {τ : ℝ}
    (h1 : a / 4 ≤ Work.Diff.C.rdist (I := I) (M := M) p (Φ 0 τ x))
    (h2 : γ / 8 < Work.Diff.C.rdist (I := I) (M := M) q (Φ 0 τ x)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Set.Ioo (τ - δ) τ,
      Work.Diff.C.rdist (I := I) (M := M) p (Φ 0 s x)
        < Work.Diff.C.rdist (I := I) (M := M) p (Φ 0 τ x) := by
  obtain ⟨δ, hδ, hlt⟩ :=
    flow_left_lt_rdist (I := I) (cov := cov) hmet htor hpinch hΦsm hΦself hΦderiv
      (hasc (Φ 0 τ x) h1 h2)
  have htrans := flow_translate (I := I) hVsm hΦself hΦderiv
  refine ⟨δ, hδ, fun s hs => ?_⟩
  have ht : τ - s ∈ Set.Ioo (0 : ℝ) δ := by
    rw [Set.mem_Ioo] at hs ⊢
    exact ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have h := hlt (τ - s) ht
  have hkey : Φ 0 (-(τ - s)) (Φ 0 τ x) = Φ 0 s x := by
    have hstep : Φ 0 (-(τ - s)) (Φ 0 τ x) = Φ τ (τ - (τ - s)) (Φ 0 τ x) := by
      rw [htrans τ (τ - (τ - s)) (Φ 0 τ x)]
      ring_nf
    rw [hstep, hΦcoc 0 τ (τ - (τ - s)) x]
    ring_nf
  rwa [hkey] at h

/-- **The crossing time of the level `3γ/4` is unique.** -/
lemma rdistQ_crossing_unique
    {q : M} {v γ : ℝ} (hγ : 0 < γ) (h5g : 5 * γ / 2 < v)
    {V : (x : M) → TangentSpace I x} {Φ : ℝ → ℝ → M → M}
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    (hsmQ : ∀ y : M, 0 < Work.Diff.C.rdist (I := I) (M := M) q y →
      Work.Diff.C.rdist (I := I) (M := M) q y < v →
      CMDiffAt ∞ (fun z : M => Work.Diff.C.rdist (I := I) (M := M) q z) y)
    (hvalq : ∀ y : M, γ / 4 ≤ Work.Diff.C.rdist (I := I) (M := M) q y →
      Work.Diff.C.rdist (I := I) (M := M) q y ≤ 5 * γ / 2 →
      V y = - Work.Diff.C.rgrad (I := I) (M := M)
        (fun z : M => Work.Diff.C.rdist (I := I) (M := M) q z) y)
    (hΦsm : ContMDiff ((𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ)).prod I) I ∞
      (fun q : (ℝ × ℝ) × M => Φ q.1.1 q.1.2 q.2))
    (hΦderiv : ∀ s t x, HasMFDerivAt 𝓘(ℝ,ℝ) I (fun τ : ℝ => Φ s τ x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (V (Φ s t x)))) :
    ∀ (x : M) (s₁ s₂ : ℝ),
      Work.Diff.C.rdist (I := I) (M := M) q (Φ 0 s₁ x) = 3 * γ / 4 →
      Work.Diff.C.rdist (I := I) (M := M) q (Φ 0 s₂ x) = 3 * γ / 4 → s₁ = s₂ := by
  intro x s₁ s₂ hs₁ hs₂
  have hcont : Continuous (fun τ : ℝ => Work.Diff.C.rdist (I := I) (M := M) q (Φ 0 τ x)) := by
    rw [continuous_iff_continuousAt]
    intro τ
    exact ((Work.Diff.C.rdist_continuous (I := I) (M := M) q).continuousAt).comp
      (contMDiffAt_flow_slice (I := I) (Φ := Φ) hΦsm τ x).continuousAt
  have hderiv : ∀ s : ℝ, (fun τ : ℝ => Work.Diff.C.rdist (I := I) (M := M) q (Φ 0 τ x)) s
      ∈ Set.Icc (γ / 4) (5 * γ / 2) →
      HasDerivAt (fun τ : ℝ => Work.Diff.C.rdist (I := I) (M := M) q (Φ 0 τ x)) (-1) s :=
    fun s hs => hasDerivAt_rdistQ_flow (I := I) (cov := cov) hγ h5g hmet htor hsmQ hvalq hΦderiv x s hs.1 hs.2
  have hs₀ : Work.Diff.C.rdist (I := I) (M := M) q (Φ 0 s₁ x) ∈ Set.Icc (γ / 4) (5 * γ / 2) := by
    rw [hs₁]; constructor <;> linarith
  obtain ⟨-, -, -, -, huniq⟩ := flow_g_interval (lo := γ / 4) (hi := 5 * γ / 2)
    (by linarith) hcont hderiv hs₀
  exact huniq s₁ s₂ rfl (by rw [hs₂, hs₁])

/-- **The time at which the trajectory crosses the level `3γ/4` while inside the annulus.** -/
lemma rdistQ_interval_at
    {q : M} {v γ : ℝ} (hγ : 0 < γ) (h5g : 5 * γ / 2 < v)
    {V : (x : M) → TangentSpace I x} {Φ : ℝ → ℝ → M → M}
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    (hsmQ : ∀ y : M, 0 < Work.Diff.C.rdist (I := I) (M := M) q y →
      Work.Diff.C.rdist (I := I) (M := M) q y < v →
      CMDiffAt ∞ (fun z : M => Work.Diff.C.rdist (I := I) (M := M) q z) y)
    (hvalq : ∀ y : M, γ / 4 ≤ Work.Diff.C.rdist (I := I) (M := M) q y →
      Work.Diff.C.rdist (I := I) (M := M) q y ≤ 5 * γ / 2 →
      V y = - Work.Diff.C.rgrad (I := I) (M := M)
        (fun z : M => Work.Diff.C.rdist (I := I) (M := M) q z) y)
    (hΦsm : ContMDiff ((𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ)).prod I) I ∞
      (fun q : (ℝ × ℝ) × M => Φ q.1.1 q.1.2 q.2))
    (hΦself : ∀ s x, Φ s s x = x)
    (hΦderiv : ∀ s t x, HasMFDerivAt 𝓘(ℝ,ℝ) I (fun τ : ℝ => Φ s τ x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (V (Φ s t x)))) :
    ∀ x : M, γ / 4 ≤ Work.Diff.C.rdist (I := I) (M := M) q x →
      Work.Diff.C.rdist (I := I) (M := M) q x ≤ 5 * γ / 2 →
      Work.Diff.C.rdist (I := I) (M := M) q
          (Φ 0 (Work.Diff.C.rdist (I := I) (M := M) q x - 3 * γ / 4) x) = 3 * γ / 4 := by
  intro x h1 h2
  have hcont : Continuous (fun τ : ℝ => Work.Diff.C.rdist (I := I) (M := M) q (Φ 0 τ x)) := by
    rw [continuous_iff_continuousAt]
    intro τ
    exact ((Work.Diff.C.rdist_continuous (I := I) (M := M) q).continuousAt).comp
      (contMDiffAt_flow_slice (I := I) (Φ := Φ) hΦsm τ x).continuousAt
  have hderiv : ∀ s : ℝ, (fun τ : ℝ => Work.Diff.C.rdist (I := I) (M := M) q (Φ 0 τ x)) s
      ∈ Set.Icc (γ / 4) (5 * γ / 2) →
      HasDerivAt (fun τ : ℝ => Work.Diff.C.rdist (I := I) (M := M) q (Φ 0 τ x)) (-1) s :=
    fun s hs => hasDerivAt_rdistQ_flow (I := I) (cov := cov) hγ h5g hmet htor hsmQ hvalq hΦderiv x s hs.1 hs.2
  rcases flow_g_interval (lo := γ / 4) (hi := 5 * γ / 2) (by linarith) hcont hderiv
    (s₀ := 0) (by simpa [hΦself 0 x] using ⟨h1, h2⟩) with ⟨hcl1, hcl2, hcl3, hcl4, hcl5⟩
  by_cases hge : 3 * γ / 4 ≤ Work.Diff.C.rdist (I := I) (M := M) q x
  · have hmem : Work.Diff.C.rdist (I := I) (M := M) q x - 3 * γ / 4
        ∈ Set.Icc (0:ℝ) (0 + (Work.Diff.C.rdist (I := I) (M := M) q (Φ 0 0 x) - γ / 4)) := by
      rw [hΦself 0 x]
      exact Set.mem_Icc.mpr ⟨by linarith, by linarith⟩
    have h := hcl1 _ hmem
    have h' : Work.Diff.C.rdist (I := I) (M := M) q
          (Φ 0 (Work.Diff.C.rdist (I := I) (M := M) q x - 3 * γ / 4) x)
        = Work.Diff.C.rdist (I := I) (M := M) q x
          - (Work.Diff.C.rdist (I := I) (M := M) q x - 3 * γ / 4) := by
      simpa [hΦself 0 x] using h
    rw [h']; ring
  · have hmem : Work.Diff.C.rdist (I := I) (M := M) q x - 3 * γ / 4
        ∈ Set.Icc (0 - (5 * γ / 2 - Work.Diff.C.rdist (I := I) (M := M) q (Φ 0 0 x))) 0 := by
      rw [hΦself 0 x]
      exact Set.mem_Icc.mpr ⟨by linarith, by linarith⟩
    have h := hcl3 _ hmem
    have h' : Work.Diff.C.rdist (I := I) (M := M) q
          (Φ 0 (Work.Diff.C.rdist (I := I) (M := M) q x - 3 * γ / 4) x)
        = Work.Diff.C.rdist (I := I) (M := M) q x
          + (0 - (Work.Diff.C.rdist (I := I) (M := M) q x - 3 * γ / 4)) := by
      simpa [hΦself 0 x] using h
    rw [h']; ring

/-- **The `p`-distance is nondecreasing along the flow** while the `q`-distance stays above `γ/8`.

The proof is a bootstrap: the ascent hypothesis only applies where `a/4 ≤ d(p,·)`, so one first
shows that the floor `a/4 ≤ d(p,·)` can never be crossed (if `σ₁` were the first crossing time, the
one-sided monotonicity `local_left_strictMono` would force the value at `σ₁` to be at least
`d(p,x) > a/4`, contradicting that crossing times accumulate at `σ₁`); with the floor available, the
ascent hypothesis holds at every point of the trajectory and one more application of
`local_left_strictMono` gives the monotonicity. -/
lemma rdistP_nondecr_along_flow
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (hpinch : QuarterPinched cov)
    {p q : M} {a γ : ℝ}
    {V : (x : M) → TangentSpace I x} {Φ : ℝ → ℝ → M → M}
    (hVsm : ContMDiff I (I.prod (modelWithCornersSelf ℝ E)) ∞
      (fun y : M => (⟨y, V y⟩ : Bundle.TotalSpace E (TangentSpace I))))
    (hΦsm : ContMDiff ((𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ)).prod I) I ∞
      (fun q : (ℝ × ℝ) × M => Φ q.1.1 q.1.2 q.2))
    (hΦself : ∀ s x, Φ s s x = x)
    (hΦcoc : ∀ s t u x, Φ t u (Φ s t x) = Φ s u x)
    (hΦderiv : ∀ s t x, HasMFDerivAt 𝓘(ℝ,ℝ) I (fun τ : ℝ => Φ s τ x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (V (Φ s t x))))
    (hasc : ∀ y : M, a / 4 ≤ Work.Diff.C.rdist (I := I) (M := M) p y →
      γ / 8 < Work.Diff.C.rdist (I := I) (M := M) q y →
      Submission.GSField.IsAscentAt hmet p y (V y))
    {x : M} (hx : a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x)
    (hg : ∀ σ : ℝ, 0 ≤ σ →
      γ / 8 < Work.Diff.C.rdist (I := I) (M := M) q (Φ 0 σ x)) :
    ∀ s : ℝ, 0 ≤ s →
      Work.Diff.C.rdist (I := I) (M := M) p x
        ≤ Work.Diff.C.rdist (I := I) (M := M) p (Φ 0 s x) := by
  set φ : ℝ → ℝ := fun τ => Work.Diff.C.rdist (I := I) (M := M) p (Φ 0 τ x) with hφ
  have hφcont : Continuous φ := by
    rw [continuous_iff_continuousAt]
    intro τ
    exact ((Work.Diff.C.rdist_continuous (I := I) (M := M) p).continuousAt).comp
      (contMDiffAt_flow_slice (I := I) (Φ := Φ) hΦsm τ x).continuousAt
  have hφ0 : φ 0 = Work.Diff.C.rdist (I := I) (M := M) p x := by
    simp only [hφ, hΦself 0 x]
  have hfloor : ∀ σ : ℝ, 0 ≤ σ → a / 4 ≤ φ σ := by
    intro σ hσ
    by_contra hcon
    push_neg at hcon
    set V : Set ℝ := {τ : ℝ | τ ∈ Set.Icc (0:ℝ) σ ∧ φ τ < a / 4} with hV
    have hVne : V.Nonempty := ⟨σ, ⟨⟨hσ, le_rfl⟩, hcon⟩⟩
    have hVbdd : BddBelow V := ⟨0, fun τ hτ => hτ.1.1⟩
    set σ₁ : ℝ := sInf V with hσ₁def
    have hσ₁le : σ₁ ≤ σ := csInf_le hVbdd (show σ ∈ V from ⟨⟨hσ, le_rfl⟩, hcon⟩)
    have hσ₁ge : 0 ≤ σ₁ := le_csInf hVne (fun τ hτ => hτ.1.1)
    have hlower : ∀ τ ∈ V, σ₁ ≤ τ := fun τ hτ => csInf_le hVbdd hτ
    have hfloor' : ∀ τ ∈ Set.Ico (0:ℝ) σ₁, a / 4 ≤ φ τ := by
      intro τ hτ
      by_contra hlt
      push_neg at hlt
      exact absurd (hlower τ ⟨⟨hτ.1, le_trans hτ.2.le hσ₁le⟩, hlt⟩) (not_le.mpr hτ.2)
    have hσ₁floor : a / 4 ≤ φ σ₁ := by
      by_contra hlt
      push_neg at hlt
      rcases eq_or_lt_of_le hσ₁ge with h0 | hpos
      · rw [← h0] at hlt
        linarith [hx, hφ0]
      · have hev : ∀ᶠ τ in 𝓝 σ₁, φ τ < a / 4 :=
          hφcont.continuousAt.eventually (isOpen_Iio.mem_nhds hlt)
        obtain ⟨ε, hε, hε'⟩ := Metric.mem_nhds_iff.mp hev
        set δ₀ : ℝ := min (ε / 2) (σ₁ / 2) with hδ₀
        have hδ₀pos : 0 < δ₀ := lt_min (by linarith) (by linarith)
        have hδ₀ltε : δ₀ < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
        have hδ₀ltσ₁ : δ₀ < σ₁ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
        have hmem : σ₁ - δ₀ ∈ Set.Ioo (0:ℝ) σ₁ := ⟨by linarith, by linarith⟩
        have hlt' : φ (σ₁ - δ₀) < a / 4 := by
          apply hε'
          rw [Metric.mem_ball, Real.dist_eq, abs_of_neg (by linarith)]
          linarith
        exact absurd (hlower _ ⟨⟨hmem.1.le, le_trans hmem.2.le hσ₁le⟩, hlt'⟩)
          (not_le.mpr hmem.2)
    have hC : ∀ τ ∈ Set.Icc (0:ℝ) σ₁, ∃ δ > 0, ∀ ρ ∈ Set.Ioo (τ - δ) τ, φ ρ < φ τ := by
      intro τ hτ
      have h1 : a / 4 ≤ φ τ := by
        rcases lt_or_eq_of_le hτ.2 with h | h
        · exact hfloor' τ ⟨hτ.1, h⟩
        · rw [h]; exact hσ₁floor
      have h1' : a / 4 ≤ Work.Diff.C.rdist (I := I) (M := M) p (Φ 0 τ x) := by
        simpa only [hφ] using h1
      exact flow_c_mono (I := I) (cov := cov) hmet htor hpinch hVsm hΦsm hΦself hΦcoc hΦderiv
        hasc h1' (hg τ hτ.1)
    have hmono := local_left_strictMono (m := φ) hφcont hC
    have hφ0le : φ 0 ≤ φ σ₁ := by
      rcases lt_or_eq_of_le hσ₁ge with h | h
      · exact (hmono ⟨le_rfl, hσ₁ge⟩ ⟨hσ₁ge, le_rfl⟩ h).le
      · rw [← h]
    have hpos' : a / 4 < φ σ₁ := by
      rw [← hφ0] at hx
      exact lt_of_lt_of_le hx hφ0le
    have hev2 : ∀ᶠ τ in 𝓝 σ₁, a / 4 < φ τ :=
      hφcont.continuousAt.eventually (isOpen_Ioi.mem_nhds hpos')
    obtain ⟨η, hη, hη'⟩ := Metric.mem_nhds_iff.mp hev2
    obtain ⟨τ, hτV, hτlt⟩ : ∃ τ ∈ V, τ < σ₁ + η := by
      by_contra h
      push_neg at h
      have : σ₁ + η ≤ σ₁ := le_csInf hVne (fun τ hτ => h τ hτ)
      linarith
    have hτge : σ₁ ≤ τ := hlower τ hτV
    have hdist : dist τ σ₁ < η := by
      rw [Real.dist_eq, abs_of_nonneg (by linarith)]
      linarith
    exact absurd (hη' hdist) (not_lt.mpr hτV.2.le)
  intro s hs
  have hC : ∀ τ ∈ Set.Icc (0:ℝ) s, ∃ δ > 0, ∀ ρ ∈ Set.Ioo (τ - δ) τ, φ ρ < φ τ :=
    fun τ hτ => flow_c_mono (I := I) (cov := cov) hmet htor hpinch hVsm hΦsm hΦself hΦcoc hΦderiv
      hasc (by simpa only [hφ] using hfloor τ hτ.1) (hg τ hτ.1)
  have hmono := local_left_strictMono (m := φ) hφcont hC
  have hmain : φ 0 ≤ φ s := by
    rcases lt_or_eq_of_le hs with h | h
    · exact (hmono ⟨le_rfl, hs⟩ ⟨hs, le_rfl⟩ h).le
    · rw [← h]
  have h2 : φ s = Work.Diff.C.rdist (I := I) (M := M) p (Φ 0 s x) := by
    simp only [hφ]
  rw [hφ0, h2] at hmain
  exact hmain

/-- **Time-shift identity for the flow**: `Φ 0 t (Φ 0 s y) = Φ 0 (s + t) y`. -/
lemma flow_shift_apply
    {V : (x : M) → TangentSpace I x} {Φ : ℝ → ℝ → M → M}
    (hVsm : ContMDiff I (I.prod (modelWithCornersSelf ℝ E)) ∞
      (fun y : M => (⟨y, V y⟩ : Bundle.TotalSpace E (TangentSpace I))))
    (hΦself : ∀ s x, Φ s s x = x)
    (hΦcoc : ∀ s t u x, Φ t u (Φ s t x) = Φ s u x)
    (hΦderiv : ∀ s t x, HasMFDerivAt 𝓘(ℝ,ℝ) I (fun τ : ℝ => Φ s τ x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (V (Φ s t x)))) :
    ∀ (y : M) (s t : ℝ), Φ 0 t (Φ 0 s y) = Φ 0 (s + t) y := by
  intro y s t
  have htrans := flow_translate (I := I) hVsm hΦself hΦderiv
  have h1 : Φ 0 t (Φ 0 s y) = Φ s (s + t) (Φ 0 s y) := by
    rw [htrans s (s + t) (Φ 0 s y)]
    ring_nf
  rw [h1, hΦcoc 0 s (s + t)]

/-- **A cluster point of a filter along which `f` tends to `L` has value `L`.** -/
lemma eq_of_clusterPt_tendsto
    {F : Filter M} {z : M} {f : M → ℝ} {L : ℝ}
    (hz : ClusterPt z F) (htend : Tendsto f F (𝓝 L)) (hf : ContinuousAt f z) :
    f z = L := by
  haveI : (𝓝 z ⊓ F).NeBot := hz
  have h1 : Tendsto f (𝓝 z ⊓ F) (𝓝 (f z)) := hf.tendsto.mono_left inf_le_left
  have h2 : Tendsto f (𝓝 z ⊓ F) (𝓝 L) := htend.mono_left inf_le_right
  exact tendsto_nhds_unique h1 h2

/-- **The `q`-distance drops below any level `c > γ/8` along the flow.**  This is the ω-limit
argument: if the trajectory stayed in `{c < d(q,·)}` (hence in `{γ/8 < d(q,·)}`), then the ascent
hypothesis would hold at every point of the trajectory and the bootstrap
`rdistP_nondecr_along_flow` would make `d(p,·)` nondecreasing along it; it therefore converges to
some `L`, and at a cluster point `z` of the trajectory its value is `L`.  But `z` also satisfies
`γ/8 < d(q,z)`, so `V z` is an ascent direction, and the strict decrease
`flow_left_lt_rdist` backwards from `z` produces a cluster point (of the time-shifted trajectory)
with value `< L` — while the same limit argument gives value `L` there as well. -/
lemma rdistQ_reaches_low
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (hpinch : QuarterPinched cov)
    {p q : M} {a γ c D : ℝ} (hγ : 0 < γ) (hc : γ / 8 < c)
    {V : (x : M) → TangentSpace I x} {Φ : ℝ → ℝ → M → M}
    (hVsm : ContMDiff I (I.prod (modelWithCornersSelf ℝ E)) ∞
      (fun y : M => (⟨y, V y⟩ : Bundle.TotalSpace E (TangentSpace I))))
    (hΦsm : ContMDiff ((𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ)).prod I) I ∞
      (fun q : (ℝ × ℝ) × M => Φ q.1.1 q.1.2 q.2))
    (hΦself : ∀ s x, Φ s s x = x)
    (hΦcoc : ∀ s t u x, Φ t u (Φ s t x) = Φ s u x)
    (hΦderiv : ∀ s t x, HasMFDerivAt 𝓘(ℝ,ℝ) I (fun τ : ℝ => Φ s τ x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (V (Φ s t x))))
    (hasc : ∀ y : M, a / 4 ≤ Work.Diff.C.rdist (I := I) (M := M) p y →
      γ / 8 < Work.Diff.C.rdist (I := I) (M := M) q y →
      Submission.GSField.IsAscentAt hmet p y (V y))
    (hdiam : ∀ r s : M, Manifold.riemannianEDist I r s ≤ ENNReal.ofReal D)
    {x : M} (hx : a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x) :
    ∃ s : ℝ, 0 ≤ s ∧ Work.Diff.C.rdist (I := I) (M := M) q (Φ 0 s x) ≤ c := by
  by_contra hcon
  push_neg at hcon
  have hstay : ∀ σ : ℝ, 0 ≤ σ → γ / 8 < Work.Diff.C.rdist (I := I) (M := M) q (Φ 0 σ x) :=
    fun σ hσ => lt_trans hc (hcon σ hσ)
  have hbase : ∀ s : ℝ, 0 ≤ s →
      Work.Diff.C.rdist (I := I) (M := M) p x
        ≤ Work.Diff.C.rdist (I := I) (M := M) p (Φ 0 s x) :=
    fun s hs => rdistP_nondecr_along_flow (I := I) (cov := cov) hmet htor hpinch hVsm hΦsm
      hΦself hΦcoc hΦderiv hasc hx hstay s hs
  have hmono : ∀ s t : ℝ, 0 ≤ s → s ≤ t →
      Work.Diff.C.rdist (I := I) (M := M) p (Φ 0 s x)
        ≤ Work.Diff.C.rdist (I := I) (M := M) p (Φ 0 t x) := by
    intro s t hs hst
    have hlt : a / 4 < Work.Diff.C.rdist (I := I) (M := M) p (Φ 0 s x) :=
      lt_of_lt_of_le hx (hbase s hs)
    have hstay' : ∀ σ : ℝ, 0 ≤ σ →
        γ / 8 < Work.Diff.C.rdist (I := I) (M := M) q (Φ 0 σ (Φ 0 s x)) := by
      intro σ hσ
      rw [flow_shift_apply (I := I) hVsm hΦself hΦcoc hΦderiv x s σ]
      exact hstay (s + σ) (by linarith)
    have h2 := rdistP_nondecr_along_flow (I := I) (cov := cov) hmet htor hpinch hVsm hΦsm hΦself
      hΦcoc hΦderiv hasc hlt hstay' (t - s) (by linarith)
    rw [flow_shift_apply (I := I) hVsm hΦself hΦcoc hΦderiv x s (t - s)] at h2
    have heq : s + (t - s) = t := by ring
    rwa [heq] at h2
  set u : ℝ → ℝ := fun s => Work.Diff.C.rdist (I := I) (M := M) p (Φ 0 (max s 0) x) with hu
  have hu_mono : Monotone u := by
    intro s t hst
    simp only [hu]
    exact hmono (max s 0) (max t 0) (le_max_right s 0) (max_le_max hst le_rfl)
  have hbdd : BddAbove (range u) := by
    refine ⟨(ENNReal.ofReal D).toReal, ?_⟩
    rintro v ⟨s, rfl⟩
    have h := hdiam p (Φ 0 (max s 0) x)
    rw [hu]
    calc Work.Diff.C.rdist (I := I) (M := M) p (Φ 0 (max s 0) x)
        = (Manifold.riemannianEDist I p (Φ 0 (max s 0) x)).toReal := rfl
      _ ≤ (ENNReal.ofReal D).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  set L : ℝ := ⨆ s : ℝ, u s with hL
  have hu_tend : Tendsto u atTop (𝓝 L) := by
    rw [hL]
    exact tendsto_atTop_ciSup hu_mono hbdd
  have hLtend : Tendsto (fun σ : ℝ => Work.Diff.C.rdist (I := I) (M := M) p (Φ 0 σ x))
      atTop (𝓝 L) := by
    have hev : ∀ᶠ b : ℝ in atTop, u b = Work.Diff.C.rdist (I := I) (M := M) p (Φ 0 b x) := by
      rw [Filter.eventually_atTop]
      exact ⟨0, fun b hb => by simp only [hu, max_eq_left hb]⟩
    exact Filter.Tendsto.congr' hev hu_tend
  have hLx : Work.Diff.C.rdist (I := I) (M := M) p x ≤ L := by
    rw [hL]
    have h1 : u 0 = Work.Diff.C.rdist (I := I) (M := M) p x := by
      rw [hu]; simp only [max_eq_left le_rfl, hΦself 0 x]
    rw [← h1]
    exact le_ciSup hbdd 0
  set F : Filter M := atTop.map (fun σ : ℝ => Φ 0 σ x) with hF
  haveI : F.NeBot := by rw [hF]; exact map_neBot (m := fun σ : ℝ => Φ 0 σ x)
  obtain ⟨z, -, hz⟩ := IsCompact.exists_clusterPt (s := Set.univ) isCompact_univ (f := F)
    (by rw [Filter.principal_univ]; exact le_top)
  have hfF : Tendsto (fun y : M => Work.Diff.C.rdist (I := I) (M := M) p y) F (𝓝 L) := by
    rw [hF]
    exact tendsto_map' hLtend
  have hfz : Work.Diff.C.rdist (I := I) (M := M) p z = L :=
    eq_of_clusterPt_tendsto hz hfF
      (Work.Diff.C.rdist_continuous (I := I) (M := M) p).continuousAt
  have hgz : c ≤ Work.Diff.C.rdist (I := I) (M := M) q z := by
    have h1 : ClusterPt (Work.Diff.C.rdist (I := I) (M := M) q z)
        (map (fun y : M => Work.Diff.C.rdist (I := I) (M := M) q y) F) :=
      ClusterPt.map hz (Work.Diff.C.rdist_continuous (I := I) (M := M) q).continuousAt
        tendsto_map
    have hle : (map (fun y : M => Work.Diff.C.rdist (I := I) (M := M) q y) F)
        ≤ 𝓟 (Set.Ici c) := by
      rw [hF, Filter.map_map, Filter.le_principal_iff, Filter.mem_map, Filter.mem_atTop_sets]
      exact ⟨0, fun b hb => (hcon b hb).le⟩
    have h2 := h1.mono hle
    have h3 : Work.Diff.C.rdist (I := I) (M := M) q z ∈ closure (Set.Ici c) :=
      mem_closure_iff_clusterPt.mpr h2
    rwa [isClosed_Ici.closure_eq, Set.mem_Ici] at h3
  have hzγ : γ / 8 < Work.Diff.C.rdist (I := I) (M := M) q z := lt_of_lt_of_le hc hgz
  have hza : a / 4 ≤ Work.Diff.C.rdist (I := I) (M := M) p z := by
    rw [hfz]
    exact le_trans hx.le hLx
  obtain ⟨δ, hδ, hδ'⟩ := flow_left_lt_rdist (I := I) (cov := cov) hmet htor hpinch hΦsm
    hΦself hΦderiv (hasc z hza hzγ)
  set t : ℝ := δ / 2 with ht
  have htpos : 0 < t := by rw [ht]; linarith
  have htt : t ∈ Set.Ioo (0:ℝ) δ := ⟨htpos, by rw [ht]; linarith⟩
  have hw := hδ' t htt
  have hcont_shift : ContinuousAt (fun y : M => Φ 0 (-t) y) z :=
    (contMDiffAt_flow_base (I := I) hΦsm (-t) z).continuousAt
  have hz' : ClusterPt (Φ 0 (-t) z) (map (fun y : M => Φ 0 (-t) y) F) :=
    ClusterPt.map hz hcont_shift tendsto_map
  have hfF' : Tendsto (fun y : M => Work.Diff.C.rdist (I := I) (M := M) p y)
      (map (fun y : M => Φ 0 (-t) y) F) (𝓝 L) := by
    rw [hF, Filter.map_map]
    apply tendsto_map'
    have h2 : (fun σ : ℝ => Work.Diff.C.rdist (I := I) (M := M) p (Φ 0 (-t) (Φ 0 σ x)))
        = (fun σ : ℝ => Work.Diff.C.rdist (I := I) (M := M) p (Φ 0 (σ - t) x)) := by
      funext σ
      rw [flow_shift_apply (I := I) hVsm hΦself hΦcoc hΦderiv x σ (-t)]
      ring_nf
    change Tendsto (fun σ : ℝ => Work.Diff.C.rdist (I := I) (M := M) p (Φ 0 (-t) (Φ 0 σ x)))
      atTop (𝓝 L)
    rw [h2]
    exact hLtend.comp (tendsto_atTop_add_const_right atTop (-t) tendsto_id)
  have hfz' : Work.Diff.C.rdist (I := I) (M := M) p (Φ 0 (-t) z) = L :=
    eq_of_clusterPt_tendsto hz' hfF'
      (Work.Diff.C.rdist_continuous (I := I) (M := M) p).continuousAt
  rw [hfz, hfz'] at hw
  exact absurd hw (lt_irrefl L)

/-- **The slice of a smooth flow in the base point, jointly with the time.** -/
lemma contMDiffAt_flow_family
    {Φ : ℝ → ℝ → M → M}
    (hΦsm : ContMDiff ((𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ)).prod I) I ∞
      (fun q : (ℝ × ℝ) × M => Φ q.1.1 q.1.2 q.2)) (t : ℝ) (y : M) :
    ContMDiffAt (𝓘(ℝ,ℝ).prod I) I ∞ (fun p : ℝ × M => Φ 0 p.1 p.2) (t, y) := by
  have h1 : ContMDiffAt (𝓘(ℝ,ℝ).prod I) (𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ)) ∞
      (fun p : ℝ × M => (((0 : ℝ), p.1) : ℝ × ℝ)) (t, y) :=
    ContMDiffAt.prodMk (contMDiffAt_const (c := (0 : ℝ)) (x := (t, y))) contMDiffAt_fst
  have h2 : ContMDiffAt (𝓘(ℝ,ℝ).prod I) ((𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ)).prod I) ∞
      (fun p : ℝ × M => ((((0 : ℝ), p.1) : ℝ × ℝ), p.2)) (t, y) :=
    ContMDiffAt.prodMk h1 contMDiffAt_snd
  exact ContMDiffAt.comp (x := (t, y))
    (f := fun p : ℝ × M => ((((0 : ℝ), p.1) : ℝ × ℝ), p.2))
    (hΦsm ((((0 : ℝ), t) : ℝ × ℝ), y)) h2

/-- **The map `z ↦ Φ 0 (t z) z` is smooth where `t` is.** -/
lemma contMDiffAt_flow_box
    {Φ : ℝ → ℝ → M → M} (hΦsm : ContMDiff ((𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ)).prod I) I ∞
      (fun q : (ℝ × ℝ) × M => Φ q.1.1 q.1.2 q.2))
    {t : M → ℝ} {x : M} (ht : ContMDiffAt I 𝓘(ℝ,ℝ) ∞ t x) :
    ContMDiffAt I I ∞ (fun z : M => Φ 0 (t z) z) x := by
  have h1 : ContMDiffAt I (𝓘(ℝ,ℝ).prod I) ∞ (fun z : M => (t z, z)) x :=
    ContMDiffAt.prodMk ht contMDiffAt_id
  exact ContMDiffAt.comp (x := x) (f := fun z : M => (t z, z))
    (contMDiffAt_flow_family (I := I) hΦsm (t x) x) h1

/-- **Existence of a crossing time of the level `3γ/4`.** -/
lemma rdistQ_exists_crossing
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (hpinch : QuarterPinched cov)
    {p q : M} {a γ v D : ℝ} (hγ : 0 < γ) (h5g : 5 * γ / 2 < v)
    {V : (x : M) → TangentSpace I x} {Φ : ℝ → ℝ → M → M}
    (hVsm : ContMDiff I (I.prod (modelWithCornersSelf ℝ E)) ∞
      (fun y : M => (⟨y, V y⟩ : Bundle.TotalSpace E (TangentSpace I))))
    (hΦsm : ContMDiff ((𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ)).prod I) I ∞
      (fun q : (ℝ × ℝ) × M => Φ q.1.1 q.1.2 q.2))
    (hΦself : ∀ s x, Φ s s x = x)
    (hΦcoc : ∀ s t u x, Φ t u (Φ s t x) = Φ s u x)
    (hΦderiv : ∀ s t x, HasMFDerivAt 𝓘(ℝ,ℝ) I (fun τ : ℝ => Φ s τ x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (V (Φ s t x))))
    (hsmQ : ∀ y : M, 0 < Work.Diff.C.rdist (I := I) (M := M) q y →
      Work.Diff.C.rdist (I := I) (M := M) q y < v →
      CMDiffAt ∞ (fun z : M => Work.Diff.C.rdist (I := I) (M := M) q z) y)
    (hvalq : ∀ y : M, γ / 4 ≤ Work.Diff.C.rdist (I := I) (M := M) q y →
      Work.Diff.C.rdist (I := I) (M := M) q y ≤ 5 * γ / 2 →
      V y = - Work.Diff.C.rgrad (I := I) (M := M)
        (fun z : M => Work.Diff.C.rdist (I := I) (M := M) q z) y)
    (hasc : ∀ y : M, a / 4 ≤ Work.Diff.C.rdist (I := I) (M := M) p y →
      γ / 8 < Work.Diff.C.rdist (I := I) (M := M) q y →
      Submission.GSField.IsAscentAt hmet p y (V y))
    (hdiam : ∀ r s : M, Manifold.riemannianEDist I r s ≤ ENNReal.ofReal D)
    {x : M} (hx : a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x)
    (hgx : γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q x) :
    ∃ t : ℝ, Work.Diff.C.rdist (I := I) (M := M) q (Φ 0 t x) = 3 * γ / 4 := by
  by_cases hcase : Work.Diff.C.rdist (I := I) (M := M) q x ≤ 5 * γ / 2
  · exact ⟨Work.Diff.C.rdist (I := I) (M := M) q x - 3 * γ / 4,
      rdistQ_interval_at (I := I) (cov := cov) hγ h5g hmet htor hsmQ hvalq hΦsm hΦself hΦderiv
        x hgx.le hcase⟩
  · push_neg at hcase
    obtain ⟨s, hs0, hs⟩ := rdistQ_reaches_low (I := I) (cov := cov) hmet htor hpinch hγ
      (by linarith : γ / 8 < 3 * γ / 4) hVsm hΦsm hΦself hΦcoc hΦderiv hasc hdiam hx
    have hcont : ContinuousOn (fun τ : ℝ => Work.Diff.C.rdist (I := I) (M := M) q (Φ 0 τ x))
        (Set.Icc (0:ℝ) s) := by
      refine Continuous.continuousOn ?_
      rw [continuous_iff_continuousAt]
      intro τ
      exact ((Work.Diff.C.rdist_continuous (I := I) (M := M) q).continuousAt).comp
        (contMDiffAt_flow_slice (I := I) hΦsm τ x).continuousAt
    have h0 : 3 * γ / 4 ≤ Work.Diff.C.rdist (I := I) (M := M) q (Φ 0 0 x) := by
      rw [hΦself 0 x]
      linarith
    have hmem : (3 * γ / 4) ∈ Set.Icc (Work.Diff.C.rdist (I := I) (M := M) q (Φ 0 s x))
        (Work.Diff.C.rdist (I := I) (M := M) q (Φ 0 0 x)) := ⟨hs, h0⟩
    obtain ⟨τ, -, hτeq⟩ := intermediate_value_Icc' hs0 hcont hmem
    exact ⟨τ, hτeq⟩

/-- **The trajectory segment from `x` to the crossing level `3γ/4` stays in the annulus.** -/
lemma rdistQ_annulus_between
    {q : M} {v γ : ℝ} (hγ : 0 < γ) (h5g : 5 * γ / 2 < v)
    {V : (x : M) → TangentSpace I x} {Φ : ℝ → ℝ → M → M}
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    (hsmQ : ∀ y : M, 0 < Work.Diff.C.rdist (I := I) (M := M) q y →
      Work.Diff.C.rdist (I := I) (M := M) q y < v →
      CMDiffAt ∞ (fun z : M => Work.Diff.C.rdist (I := I) (M := M) q z) y)
    (hvalq : ∀ y : M, γ / 4 ≤ Work.Diff.C.rdist (I := I) (M := M) q y →
      Work.Diff.C.rdist (I := I) (M := M) q y ≤ 5 * γ / 2 →
      V y = - Work.Diff.C.rgrad (I := I) (M := M)
        (fun z : M => Work.Diff.C.rdist (I := I) (M := M) q z) y)
    (hΦsm : ContMDiff ((𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ)).prod I) I ∞
      (fun q : (ℝ × ℝ) × M => Φ q.1.1 q.1.2 q.2))
    (hΦself : ∀ s x, Φ s s x = x)
    (hΦderiv : ∀ s t x, HasMFDerivAt 𝓘(ℝ,ℝ) I (fun τ : ℝ => Φ s τ x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (V (Φ s t x))))
    {x : M} (hx1 : γ / 4 ≤ Work.Diff.C.rdist (I := I) (M := M) q x)
    (hx2 : Work.Diff.C.rdist (I := I) (M := M) q x ≤ 3 * γ / 2) :
    ∀ s ∈ Set.Icc (min 0 (Work.Diff.C.rdist (I := I) (M := M) q x - 3 * γ / 4))
        (max 0 (Work.Diff.C.rdist (I := I) (M := M) q x - 3 * γ / 4)),
      γ / 4 ≤ Work.Diff.C.rdist (I := I) (M := M) q (Φ 0 s x) ∧
      Work.Diff.C.rdist (I := I) (M := M) q (Φ 0 s x) ≤ 3 * γ / 2 := by
  set G : ℝ → ℝ := fun τ => Work.Diff.C.rdist (I := I) (M := M) q (Φ 0 τ x) with hG
  have hcont : Continuous G := by
    rw [continuous_iff_continuousAt]
    intro τ
    exact ((Work.Diff.C.rdist_continuous (I := I) (M := M) q).continuousAt).comp
      (contMDiffAt_flow_slice (I := I) hΦsm τ x).continuousAt
  have hderiv : ∀ s : ℝ, G s ∈ Set.Icc (γ / 4) (5 * γ / 2) → HasDerivAt G (-1) s :=
    fun s hs => hasDerivAt_rdistQ_flow (I := I) (cov := cov) hγ h5g hmet htor hsmQ hvalq hΦderiv
      x s hs.1 hs.2
  have hG0 : G 0 = Work.Diff.C.rdist (I := I) (M := M) q x := by
    simp only [hG, hΦself 0 x]
  obtain ⟨hcl1, hcl2, hcl3, hcl4, hcl5⟩ := flow_g_interval (lo := γ / 4) (hi := 5 * γ / 2)
    (by linarith) hcont hderiv (s₀ := 0)
    (by rw [hG0]; exact ⟨hx1, by linarith⟩)
  intro s hs
  rw [← hG0] at hs
  have hval : G s = G 0 - s := by
    by_cases hT0 : 0 ≤ G 0 - 3 * γ / 4
    · have hs' : s ∈ Set.Icc (0:ℝ) (0 + (G 0 - γ / 4)) := by
        refine Set.mem_Icc.mpr ⟨?_, ?_⟩
        · rw [min_eq_left hT0] at hs; exact hs.1
        · rw [max_eq_right hT0] at hs
          linarith [hs.2]
      have h := hcl1 s hs'
      rw [h]; ring
    · have hTle : G 0 - 3 * γ / 4 ≤ 0 := (not_le.mp hT0).le
      have hs' : s ∈ Set.Icc (0 - (5 * γ / 2 - G 0)) 0 := by
        refine Set.mem_Icc.mpr ⟨?_, ?_⟩
        · rw [min_eq_right hTle] at hs
          linarith [hs.1]
        · rw [max_eq_left hTle] at hs
          exact hs.2
      have h := hcl3 s hs'
      rw [h]; ring
  have hG0lo : γ / 4 ≤ G 0 := by rw [hG0]; exact hx1
  have hG0hi : G 0 ≤ 3 * γ / 2 := by rw [hG0]; exact hx2
  have hsle : s ≤ max 0 (G 0 - 3 * γ / 4) := hs.2
  have hsge : min 0 (G 0 - 3 * γ / 4) ≤ s := hs.1
  have hfin : γ / 4 ≤ G s ∧ G s ≤ 3 * γ / 2 := by
    rw [hval]
    by_cases hT0 : 0 ≤ G 0 - 3 * γ / 4
    · have h1 : 0 ≤ s := by
        rw [min_eq_left hT0] at hsge; exact hsge
      have h2 : s ≤ G 0 - 3 * γ / 4 := by
        rw [max_eq_right hT0] at hsle; exact hsle
      constructor <;> linarith
    · have hTle : G 0 - 3 * γ / 4 ≤ 0 := (not_le.mp hT0).le
      have h1 : G 0 - 3 * γ / 4 ≤ s := by
        rw [min_eq_right hTle] at hsge; exact hsge
      have h2 : s ≤ 0 := by
        rw [max_eq_left hTle] at hsle; exact hsle
      constructor <;> linarith
  exact hfin

end Helpers

theorem label_v
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [RegularSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (hpinch : QuarterPinched cov)
    {p q : M} {D v a γ : ℝ} (ha : 0 < a) (hγ : 0 < γ) (hv : 0 < v)
    (h5g : 5 * γ / 2 < v)
    (hsmQ : ∀ y : M, 0 < Work.Diff.C.rdist (I := I) (M := M) q y →
      Work.Diff.C.rdist (I := I) (M := M) q y < v →
      CMDiffAt ∞ (fun z : M => Work.Diff.C.rdist (I := I) (M := M) q z) y)
    {Φq : M → TangentSpace I q}
    (hsmΦq : ∀ y : M, Work.Diff.C.rdist (I := I) (M := M) q y < v →
      ContMDiffAt I (modelWithCornersSelf ℝ (TangentSpace I q)) ∞ Φq y)
    (hnormQ : ∀ y : M, Work.Diff.C.rdist (I := I) (M := M) q y < v →
      Work.Diff.C.rdist (I := I) (M := M) q y = ‖Φq y‖)
    (hDGt : Real.pi / 2 < D)
    (htri : ∀ y : M, D ≤ Work.Diff.C.rdist (I := I) (M := M) p y +
      Work.Diff.C.rdist (I := I) (M := M) q y)
    (hdiam : ∀ r s : M, Manifold.riemannianEDist I r s ≤ ENNReal.ofReal D)
    {V : (x : M) → TangentSpace I x} {Φ : ℝ → ℝ → M → M}
    (hVsm : ContMDiff I (I.prod (modelWithCornersSelf ℝ E)) ∞
      (fun y : M => (⟨y, V y⟩ : Bundle.TotalSpace E (TangentSpace I))))
    (hΦsm : ContMDiff ((𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ)).prod I) I ∞
      (fun q : (ℝ × ℝ) × M => Φ q.1.1 q.1.2 q.2))
    (hΦself : ∀ s x, Φ s s x = x)
    (hΦderiv : ∀ s t x, HasMFDerivAt 𝓘(ℝ,ℝ) I (fun τ : ℝ => Φ s τ x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (V (Φ s t x))))
    (hΦcoc : ∀ s t u x, Φ t u (Φ s t x) = Φ s u x)
    (hvalq : ∀ y : M, γ / 4 ≤ Work.Diff.C.rdist (I := I) (M := M) q y →
      Work.Diff.C.rdist (I := I) (M := M) q y ≤ 5 * γ / 2 →
      V y = - Work.Diff.C.rgrad (I := I) (M := M)
        (fun z : M => Work.Diff.C.rdist (I := I) (M := M) q z) y)
    (hconst : ∀ y : M, γ / 4 ≤ Work.Diff.C.rdist (I := I) (M := M) q y →
      Work.Diff.C.rdist (I := I) (M := M) q y ≤ 3 * γ / 2 →
      mfderiv I (modelWithCornersSelf ℝ (TangentSpace I q))
        (fun z : M => (Work.Diff.C.rdist (I := I) (M := M) q z)⁻¹ • Φq z) y (V y) = 0)
    (hnz : ∀ y : M, a / 4 ≤ Work.Diff.C.rdist (I := I) (M := M) p y →
      γ / 8 ≤ Work.Diff.C.rdist (I := I) (M := M) q y → V y ≠ 0)
    (hasc : ∀ y : M, a / 4 ≤ Work.Diff.C.rdist (I := I) (M := M) p y →
      γ / 8 < Work.Diff.C.rdist (I := I) (M := M) q y →
      Submission.GSField.IsAscentAt hmet p y (V y)) :
    ∃ (vE : M → TangentSpace I q) (t : M → ℝ) (y : M → M),
      (∀ x : M, a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x →
        γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q x →
        ContMDiffAt I 𝓘(ℝ, TangentSpace I q) ∞ vE x) ∧
      (∀ x : M, a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x →
        γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q x → ‖vE x‖ = 1) ∧
      (∀ x : M, a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x →
        γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q x →
        mfderiv I 𝓘(ℝ, TangentSpace I q) vE x (V x) = 0) ∧
      (∀ x : M, a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x →
        γ / 4 ≤ Work.Diff.C.rdist (I := I) (M := M) q x →
        Work.Diff.C.rdist (I := I) (M := M) q x ≤ 3 * γ / 2 →
        vE x = - (Work.Diff.C.rdist (I := I) (M := M) q x)⁻¹ • Φq x) ∧
      (∀ x : M, a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x →
        γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q x →
        ContMDiffAt I 𝓘(ℝ,ℝ) ∞ t x) ∧
      (∀ x : M, a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x →
        γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q x →
        ContMDiffAt I I ∞ y x) ∧
      (∀ x : M, a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x →
        γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q x →
        y x = Φ 0 (t x) x) ∧
      (∀ x : M, a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x →
        γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q x →
        Work.Diff.C.rdist (I := I) (M := M) q (y x) = 3 * γ / 4) ∧
      (∀ x : M, a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x →
        γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q x →
        vE x = - (3 * γ / 4)⁻¹ • Φq (y x)) := by
  -- ## The region `A` on which the crossing time is constructed
  have hAopen : IsOpen {z : M | a / 4 < Work.Diff.C.rdist (I := I) (M := M) p z ∧
      γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q z} :=
    ((Work.Diff.C.rdist_continuous (I := I) (M := M) p).isOpen_preimage _ isOpen_Ioi).inter
      ((Work.Diff.C.rdist_continuous (I := I) (M := M) q).isOpen_preimage _ isOpen_Ioi)
  -- ## existence and uniqueness of the crossing time on `A`
  have hex : ∀ x ∈ {z : M | a / 4 < Work.Diff.C.rdist (I := I) (M := M) p z ∧
      γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q z},
      ∃ t : ℝ, Work.Diff.C.rdist (I := I) (M := M) q (Φ 0 t x) = 3 * γ / 4 := by
    intro x hx
    exact rdistQ_exists_crossing (I := I) (cov := cov) hmet htor hpinch hγ h5g hVsm hΦsm hΦself
      hΦcoc hΦderiv hsmQ hvalq hasc hdiam hx.1 hx.2
  have huniq : ∀ x ∈ {z : M | a / 4 < Work.Diff.C.rdist (I := I) (M := M) p z ∧
      γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q z}, ∀ t t' : ℝ,
      Work.Diff.C.rdist (I := I) (M := M) q (Φ 0 t x) = 3 * γ / 4 →
      Work.Diff.C.rdist (I := I) (M := M) q (Φ 0 t' x) = 3 * γ / 4 → t = t' := by
    intro x _ t t' ht ht'
    exact rdistQ_crossing_unique (I := I) (cov := cov) hγ h5g hmet htor hsmQ hvalq hΦsm hΦderiv x t t' ht ht'
  have hFlev : ∀ y : M, Work.Diff.C.rdist (I := I) (M := M) q y = 3 * γ / 4 →
      ContMDiffAt I 𝓘(ℝ,ℝ) ∞ (fun z : M => Work.Diff.C.rdist (I := I) (M := M) q z) y := by
    intro y hy
    exact hsmQ y (by rw [hy]; linarith) (by rw [hy]; linarith)
  have htrans : ∀ y : M, Work.Diff.C.rdist (I := I) (M := M) q y = 3 * γ / 4 →
      mvfderiv I (fun z : M => Work.Diff.C.rdist (I := I) (M := M) q z) y (V y) ≠ 0 := by
    intro y hy
    have h := rdistQ_flow_eq_neg_one (I := I) (cov := cov) (v := v) (γ := γ) hγ h5g hmet htor
      hsmQ hvalq y (by rw [hy]; linarith) (by rw [hy]; linarith)
    rw [h]; norm_num
  obtain ⟨T₀, hT₀sm, hT₀val, hT₀uniq⟩ := Work.Diff.Dim2.crossing_time (I := I) (V := V) (Φ := Φ)
    (F := fun z : M => Work.Diff.C.rdist (I := I) (M := M) q z) (ℓ := 3 * γ / 4)
    (A := {z : M | a / 4 < Work.Diff.C.rdist (I := I) (M := M) p z ∧
      γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q z})
    hVsm hΦsm hΦself hΦderiv hFlev htrans hex huniq
  -- ## the extended crossing time
  let T : M → ℝ := fun x => if γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q x then T₀ x
    else Work.Diff.C.rdist (I := I) (M := M) q x - 3 * γ / 4
  have hTeq : ∀ x : M, γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q x → T x = T₀ x := by
    intro x hx; simp only [T, if_pos hx]
  have hTeq2 : ∀ x : M, ¬ γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q x →
      T x = Work.Diff.C.rdist (I := I) (M := M) q x - 3 * γ / 4 := by
    intro x hx; simp only [T, if_neg hx]
  -- ## the smoothness of `(g ·)⁻¹ • Φq ·` on the annulus
  have hKc : ∀ y : M, γ / 4 ≤ Work.Diff.C.rdist (I := I) (M := M) q y →
      Work.Diff.C.rdist (I := I) (M := M) q y ≤ 3 * γ / 2 →
      ContMDiffAt I (modelWithCornersSelf ℝ (TangentSpace I q)) ∞
        (fun z : M => (Work.Diff.C.rdist (I := I) (M := M) q z)⁻¹ • Φq z) y :=
    inv_smul_Phiq_contMDiffAt (I := I) (q := q) (Φq := Φq)
      (g := fun z : M => Work.Diff.C.rdist (I := I) (M := M) q z) (v := v) hγ h5g hsmQ hsmΦq
  -- ## the value identity on the annulus
  have hvalann : ∀ x : M, a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x →
      γ / 4 ≤ Work.Diff.C.rdist (I := I) (M := M) q x →
      Work.Diff.C.rdist (I := I) (M := M) q x ≤ 3 * γ / 2 →
      Work.Diff.C.rdist (I := I) (M := M) q (Φ 0 (T x) x) = 3 * γ / 4 ∧
      (Work.Diff.C.rdist (I := I) (M := M) q (Φ 0 (T x) x))⁻¹ • Φq (Φ 0 (T x) x)
        = (Work.Diff.C.rdist (I := I) (M := M) q x)⁻¹ • Φq x := by
    intro x hx1 hx2 hx3
    have hTx : T x = Work.Diff.C.rdist (I := I) (M := M) q x - 3 * γ / 4 := by
      by_cases hlt : γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q x
      · rw [hTeq x hlt]
        exact (hT₀uniq x ⟨hx1, hlt⟩ (Work.Diff.C.rdist (I := I) (M := M) q x - 3 * γ / 4)
          (rdistQ_interval_at (I := I) (cov := cov) hγ h5g hmet htor hsmQ hvalq hΦsm hΦself
            hΦderiv x hx2 (by linarith))).symm
      · have heq : Work.Diff.C.rdist (I := I) (M := M) q x = γ / 4 :=
          le_antisymm (not_lt.mp hlt) hx2
        rw [hTeq2 x hlt, heq]
    have hgval : Work.Diff.C.rdist (I := I) (M := M) q (Φ 0 (T x) x) = 3 * γ / 4 := by
      rw [hTx]
      exact rdistQ_interval_at (I := I) (cov := cov) hγ h5g hmet htor hsmQ hvalq hΦsm hΦself
        hΦderiv x hx2 (by linarith)
    refine ⟨hgval, ?_⟩
    have hann := rdistQ_annulus_between (I := I) (cov := cov) hγ h5g hmet htor hsmQ hvalq hΦsm
      hΦself hΦderiv (x := x) hx2 hx3
    have hTxmem : T x ∈ Set.Icc (min 0 (Work.Diff.C.rdist (I := I) (M := M) q x - 3 * γ / 4))
        (max 0 (Work.Diff.C.rdist (I := I) (M := M) q x - 3 * γ / 4)) := by
      rw [hTx]; exact ⟨min_le_right _ _, le_max_right _ _⟩
    have hconst := inv_smul_Phiq_const_along_flow (I := I) (q := q) (Φq := Φq)
      (g := fun z : M => Work.Diff.C.rdist (I := I) (M := M) q z) (γ := γ)
      hΦsm hΦself hΦderiv hKc hconst (x := x) (T := T x)
      (fun s hs => hann s (by rw [hTx] at hs; exact hs))
    exact hconst
  refine ⟨fun x => - (3 * γ / 4)⁻¹ • Φq (Φ 0 (T x) x), T, fun x => Φ 0 (T x) x,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- ## smoothness of `vE`
    intro x hx1 hx2
    have hxA : x ∈ {z : M | a / 4 < Work.Diff.C.rdist (I := I) (M := M) p z ∧
        γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q z} := ⟨hx1, hx2⟩
    have hreg : {z : M | a / 4 < Work.Diff.C.rdist (I := I) (M := M) p z ∧
        γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q z} ∈ 𝓝 x := hAopen.mem_nhds hxA
    have hTsmx : ContMDiffAt I 𝓘(ℝ,ℝ) ∞ T x := by
      refine (hT₀sm.contMDiffAt hreg).congr_of_eventuallyEq ?_
      filter_upwards [hreg] with z hz
      exact hTeq z hz.2
    have hysm : ContMDiffAt I I ∞ (fun z : M => Φ 0 (T z) z) x :=
      contMDiffAt_flow_box (I := I) hΦsm hTsmx
    have hyval : Work.Diff.C.rdist (I := I) (M := M) q (Φ 0 (T x) x) = 3 * γ / 4 := by
      rw [hTeq x hx2]; exact hT₀val x hxA
    have hPhism : ContMDiffAt I (modelWithCornersSelf ℝ (TangentSpace I q)) ∞ Φq (Φ 0 (T x) x) :=
      hsmΦq _ (by rw [hyval]; linarith)
    have hcomp : ContMDiffAt I (modelWithCornersSelf ℝ (TangentSpace I q)) ∞
        (fun z : M => Φq (Φ 0 (T z) z)) x := by
      have h := ContMDiffAt.comp (x := x) (f := fun z : M => Φ 0 (T z) z) hPhism hysm
      simpa [Function.comp_def] using h
    have hcc : ContMDiffAt I 𝓘(ℝ,ℝ) ∞ (fun _ : M => (-(3 * γ / 4)⁻¹ : ℝ)) x :=
      contMDiffAt_const
    have hs := hcc.smul hcomp
    have heq : (fun z : M => - (3 * γ / 4)⁻¹ • Φq (Φ 0 (T z) z))
        = ((fun _ : M => (-(3 * γ / 4)⁻¹ : ℝ)) • (fun z : M => Φq (Φ 0 (T z) z))) := by
      funext z; rfl
    rw [heq]; exact hs
  · -- ## `‖vE x‖ = 1`
    intro x hx1 hx2
    have hxA : x ∈ {z : M | a / 4 < Work.Diff.C.rdist (I := I) (M := M) p z ∧
        γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q z} := ⟨hx1, hx2⟩
    have hyval : Work.Diff.C.rdist (I := I) (M := M) q (Φ 0 (T x) x) = 3 * γ / 4 := by
      rw [hTeq x hx2]; exact hT₀val x hxA
    exact norm_neg_inv_smul_Phiq (I := I) (q := q) (Φq := Φq)
      (g := fun z : M => Work.Diff.C.rdist (I := I) (M := M) q z) (v := v) (c := 3 * γ / 4)
      (by linarith) (fun y hy => hnormQ y hy) (by rw [hyval]; linarith) hyval
  · -- ## `mfderiv vE x (V x) = 0`
    intro x hx1 hx2
    have hxA : x ∈ {z : M | a / 4 < Work.Diff.C.rdist (I := I) (M := M) p z ∧
        γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q z} := ⟨hx1, hx2⟩
    have hreg : {z : M | a / 4 < Work.Diff.C.rdist (I := I) (M := M) p z ∧
        γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q z} ∈ 𝓝 x := hAopen.mem_nhds hxA
    have hTsmx : ContMDiffAt I 𝓘(ℝ,ℝ) ∞ T x := by
      refine (hT₀sm.contMDiffAt hreg).congr_of_eventuallyEq ?_
      filter_upwards [hreg] with z hz
      exact hTeq z hz.2
    have hymd : MDifferentiableAt I I (fun z : M => Φ 0 (T z) z) x :=
      (contMDiffAt_flow_box (I := I) hΦsm hTsmx).mdifferentiableAt (by simp)
    -- `y` is constant along the trajectory through `x`
    have hflow : ∀ᶠ s in 𝓝 (0:ℝ), (fun z : M => Φ 0 (T z) z) (Φ 0 s x)
        = (fun z : M => Φ 0 (T z) z) x := by
      have hc : ∀ᶠ s in 𝓝 (0:ℝ), Φ 0 s x ∈ {z : M | a / 4 < Work.Diff.C.rdist (I := I) (M := M) p z ∧
          γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q z} := by
        have hcont : Tendsto (fun s : ℝ => Φ 0 s x) (𝓝 (0:ℝ)) (𝓝 x) := by
          have h : Tendsto (fun s : ℝ => Φ 0 s x) (𝓝 (0:ℝ)) (𝓝 (Φ 0 0 x)) :=
            (contMDiffAt_flow_slice (I := I) hΦsm 0 x).continuousAt
          rwa [hΦself 0 x] at h
        exact hcont.eventually hreg
      filter_upwards [hc] with s hs
      have hTseq : T (Φ 0 s x) = T x - s := by
        rw [hTeq _ hs.2, hTeq x hx2]
        have hcross : Work.Diff.C.rdist (I := I) (M := M) q
            (Φ 0 (s + T₀ (Φ 0 s x)) x) = 3 * γ / 4 := by
          rw [← flow_shift_apply (I := I) hVsm hΦself hΦcoc hΦderiv x s (T₀ (Φ 0 s x))]
          exact hT₀val _ hs
        have := hT₀uniq x hxA (s + T₀ (Φ 0 s x)) hcross
        linarith
      rw [hTseq, flow_shift_apply (I := I) hVsm hΦself hΦcoc hΦderiv x s (T x - s)]
      ring_nf
    have hymd' : MDifferentiableAt I I (fun z : M => Φ 0 (T z) z) (Φ 0 0 x) := by
      rw [hΦself 0 x]; exact hymd
    have hder0 : HasMFDerivAt 𝓘(ℝ,ℝ) I
        ((fun z : M => Φ 0 (T z) z) ∘ fun s : ℝ => Φ 0 s x) 0 0 := by
      refine (hasMFDerivAt_const ((fun z : M => Φ 0 (T z) z) x) (0:ℝ)).congr_of_eventuallyEq_abuse ?_
      filter_upwards [hflow] with s hs
      exact hs
    have hchain : mfderiv 𝓘(ℝ,ℝ) I ((fun z : M => Φ 0 (T z) z) ∘ fun s : ℝ => Φ 0 s x) 0
        = (mfderiv I I (fun z : M => Φ 0 (T z) z) (Φ 0 0 x)) ∘L
          (mfderiv 𝓘(ℝ,ℝ) I (fun s : ℝ => Φ 0 s x) 0) :=
      mfderiv_comp (I := 𝓘(ℝ,ℝ)) (I' := I) (I'' := I) (x := (0:ℝ))
        (f := fun s : ℝ => Φ 0 s x) (g := fun z : M => Φ 0 (T z) z)
        hymd' ((hΦderiv 0 0 x).mdifferentiableAt)
    have hyV : (mfderiv I I (fun z : M => Φ 0 (T z) z) x) (V x) = 0 := by
      have hcompCLM : (mfderiv I I (fun z : M => Φ 0 (T z) z) (Φ 0 0 x)) ∘L
          (mfderiv 𝓘(ℝ,ℝ) I (fun s : ℝ => Φ 0 s x) 0) = 0 := by
        rw [← hchain, hder0.mfderiv]
      have hvel : (mfderiv 𝓘(ℝ,ℝ) I (fun s : ℝ => Φ 0 s x)) 0 (1:ℝ) = V (Φ 0 0 x) :=
        mfderiv_flow_apply_one (I := I) hΦderiv x 0
      have h3 : (mfderiv I I (fun z : M => Φ 0 (T z) z) (Φ 0 0 x)) (V (Φ 0 0 x)) = 0 := by
        rw [← hvel]
        exact (congrArg (fun (L : TangentSpace 𝓘(ℝ,ℝ) (0:ℝ) →L[ℝ]
          TangentSpace I (Φ 0 0 x)) => L 1) hcompCLM)
      rw [hΦself 0 x] at h3
      exact h3
    -- the chain rule for `Φq ∘ y`
    have hyval : Work.Diff.C.rdist (I := I) (M := M) q (Φ 0 (T x) x) = 3 * γ / 4 := by
      rw [hTeq x hx2]; exact hT₀val x hxA
    have hPhismd : MDifferentiableAt I (modelWithCornersSelf ℝ (TangentSpace I q)) Φq (Φ 0 (T x) x) :=
      (hsmΦq _ (by rw [hyval]; linarith)).mdifferentiableAt (by simp)
    have hcompmd : MDifferentiableAt I (modelWithCornersSelf ℝ (TangentSpace I q))
        (fun z : M => Φq (Φ 0 (T z) z)) x := by
      have h := hPhismd.comp (x := x) (f := fun z : M => Φ 0 (T z) z) hymd
      have hfun : (fun z : M => Φq (Φ 0 (T z) z))
          = (Φq ∘ fun z : M => Φ 0 (T z) z) := rfl
      rwa [← hfun] at h
    have hsmΦqy : HasMFDerivAt I (modelWithCornersSelf ℝ (TangentSpace I q))
        (fun z : M => Φq (Φ 0 (T z) z)) x
        (mfderiv I (modelWithCornersSelf ℝ (TangentSpace I q))
          (fun z : M => Φq (Φ 0 (T z) z)) x) :=
      hcompmd.hasMFDerivAt
    have hchain2 := mfderiv_comp (I := I) (I' := I)
      (I'' := modelWithCornersSelf ℝ (TangentSpace I q)) (x := x)
      (f := fun z : M => Φ 0 (T z) z) (g := Φq) hPhismd hymd
    have hcomp0 : (mfderiv I (modelWithCornersSelf ℝ (TangentSpace I q))
        (fun z : M => Φq (Φ 0 (T z) z)) x) (V x) = 0 := by
      change mfderiv I (modelWithCornersSelf ℝ (TangentSpace I q))
        (Φq ∘ fun z : M => Φ 0 (T z) z) x (V x) = 0
      rw [hchain2]
      show (mfderiv I (modelWithCornersSelf ℝ (TangentSpace I q)) Φq (Φ 0 (T x) x))
        ((mfderiv I I (fun z : M => Φ 0 (T z) z) x) (V x)) = 0
      rw [hyV, map_zero]
    have hvE : mfderiv I (modelWithCornersSelf ℝ (TangentSpace I q))
        (fun z : M => - (3 * γ / 4)⁻¹ • Φq (Φ 0 (T z) z)) x (V x) = 0 := by
      have hder : HasMFDerivAt I (modelWithCornersSelf ℝ (TangentSpace I q))
          (fun z : M => (-(3 * γ / 4)⁻¹ : ℝ) • Φq (Φ 0 (T z) z)) x
          ((-(3 * γ / 4)⁻¹ : ℝ) • mfderiv I (modelWithCornersSelf ℝ (TangentSpace I q))
            (fun z : M => Φq (Φ 0 (T z) z)) x) :=
        hsmΦqy.const_smul (-(3 * γ / 4)⁻¹)
      rw [show (fun z : M => - (3 * γ / 4)⁻¹ • Φq (Φ 0 (T z) z))
          = (fun z : M => (-(3 * γ / 4)⁻¹ : ℝ) • Φq (Φ 0 (T z) z)) from rfl]
      rw [hder.mfderiv]
      show (-(3 * γ / 4)⁻¹ : ℝ) • ((mfderiv I (modelWithCornersSelf ℝ (TangentSpace I q))
        (fun z : M => Φq (Φ 0 (T z) z)) x) (V x)) = 0
      rw [hcomp0, smul_zero]
    exact hvE
  · -- ## the value identity on the annulus
    intro x hx1 hx2 hx3
    obtain ⟨hgval, hconstval⟩ := hvalann x hx1 hx2 hx3
    have h1 : (3 * γ / 4)⁻¹ • Φq (Φ 0 (T x) x)
        = (Work.Diff.C.rdist (I := I) (M := M) q x)⁻¹ • Φq x := by
      rw [hgval] at hconstval
      exact hconstval
    show (-(3 * γ / 4)⁻¹ : ℝ) • Φq (Φ 0 (T x) x)
        = (-(Work.Diff.C.rdist (I := I) (M := M) q x)⁻¹ : ℝ) • Φq x
    simp only [neg_smul, h1]
  · -- ## smoothness of `t`
    intro x hx1 hx2
    have hxA : x ∈ {z : M | a / 4 < Work.Diff.C.rdist (I := I) (M := M) p z ∧
        γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q z} := ⟨hx1, hx2⟩
    have hreg : {z : M | a / 4 < Work.Diff.C.rdist (I := I) (M := M) p z ∧
        γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q z} ∈ 𝓝 x := hAopen.mem_nhds hxA
    refine (hT₀sm.contMDiffAt hreg).congr_of_eventuallyEq ?_
    filter_upwards [hreg] with z hz
    exact hTeq z hz.2
  · -- ## smoothness of `y`
    intro x hx1 hx2
    have hxA : x ∈ {z : M | a / 4 < Work.Diff.C.rdist (I := I) (M := M) p z ∧
        γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q z} := ⟨hx1, hx2⟩
    have hreg : {z : M | a / 4 < Work.Diff.C.rdist (I := I) (M := M) p z ∧
        γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q z} ∈ 𝓝 x := hAopen.mem_nhds hxA
    have hTsmx : ContMDiffAt I 𝓘(ℝ,ℝ) ∞ T x := by
      refine (hT₀sm.contMDiffAt hreg).congr_of_eventuallyEq ?_
      filter_upwards [hreg] with z hz
      exact hTeq z hz.2
    exact contMDiffAt_flow_box (I := I) hΦsm hTsmx
  · -- ## `y x = Φ 0 (t x) x`
    intro x hx1 hx2
    rfl
  · -- ## `g (y x) = 3γ/4`
    intro x hx1 hx2
    have hxA : x ∈ {z : M | a / 4 < Work.Diff.C.rdist (I := I) (M := M) p z ∧
        γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q z} := ⟨hx1, hx2⟩
    show Work.Diff.C.rdist (I := I) (M := M) q (Φ 0 (T x) x) = 3 * γ / 4
    rw [hTeq x hx2]
    exact hT₀val x hxA
  · -- ## `vE x = -(3γ/4)⁻¹ • Φq (y x)`
    intro x hx1 hx2
    rfl

end Work.Diff.Dim2
