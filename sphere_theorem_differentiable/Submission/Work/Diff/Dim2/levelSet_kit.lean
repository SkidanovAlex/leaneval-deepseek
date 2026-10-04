import Mathlib
import Submission.Work.Diff.Dim2.Lib
import Submission.Work.Diff.C.Defs
import Submission.Work.Diff.ODE.exists_isXCurve
import Submission.Commons.Geometry.Manifold.locally_injective_of_injective_mfderiv
import Submission.Commons.Geometry.Manifold.LocalDiffeomorph.isLocalDiffeomorphAt_infty_of_contMDiffOn_of_mfderiv_isInvertible

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Support lemmas for the level-set/orbit lemma in dimension `2`

This is the shared kit used by `Submission/Work/Diff/Dim2/levelSet_orbit.lean` (the target
`Work.Diff.Dim2.levelSet_orbit`) and by the separately proved local claim
`Work.Diff.Dim2.level_nbhd`.

It contains

* the flow identities for `Φ` (`phi_shift`, `phi_cocycle`, `phi_flow_add`, `phi_orbit_congr`),
* the fact that `u` is constant along the flow lines of `V` inside `N` (`u_flow_eq`),
* the straight chart paths `chartLine` and their smoothness/derivative properties,
* the two-parameter family `twoParam` and the smoothness of the pair map `(s, y) ↦ Φ 0 s y`.
-/

namespace Work.Diff.Dim2

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter Submission.Geodesic

set_option linter.unusedSectionVars false

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless]

/-- The target of the label function `u`. -/
abbrev Sph2 : Type := EuclideanSpace ℝ (Fin 2)

/-- The parameter space of the two-parameter family `(λ, s) ↦ Φ 0 s (σ λ)`. -/
abbrev Par : Type := Fin 2 → ℝ

/-! ## 1.  The flow of `Φ`

The hypothesis `hΦderiv` says that for every `s` and `x` the curve `τ ↦ Φ s τ x` is an integral
curve of `V`, and `hΦself` that it starts at `x` at time `s`.  Uniqueness of integral curves of the
smooth field `V` (`isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless`) turns `Φ` into a genuine
flow: `Φ t u x = Φ 0 (u - t) x` and `Φ 0 a (Φ 0 b x) = Φ 0 (a + b) x`. -/

section Flow

variable {V : (x : M) → TangentSpace I x} {Φ : ℝ → ℝ → M → M}

/-- Uniqueness of integral curves, applied to two curves of the shape `τ ↦ Φ s τ x`. -/
lemma phi_eq_of_eq (hVsm : ContMDiff I (I.prod (modelWithCornersSelf ℝ E)) ∞
      (fun y : M => (⟨y, V y⟩ : Bundle.TotalSpace E (TangentSpace I))))
    {γ γ' : ℝ → M} {t₀ : ℝ} (hγ : IsMIntegralCurve γ V) (hγ' : IsMIntegralCurve γ' V)
    (h : γ t₀ = γ' t₀) : γ = γ' :=
  isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless (t₀ := t₀)
    (hVsm.of_le (by simp)) hγ hγ' h

/-- The time-shift identity for `Φ`. -/
lemma phi_shift
    (hVsm : ContMDiff I (I.prod (modelWithCornersSelf ℝ E)) ∞
      (fun y : M => (⟨y, V y⟩ : Bundle.TotalSpace E (TangentSpace I))))
    (hΦself : ∀ s x, Φ s s x = x)
    (hΦderiv : ∀ s t x, HasMFDerivAt (modelWithCornersSelf ℝ ℝ) I (fun τ : ℝ => Φ s τ x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (V (Φ s t x))))
    (s t u : ℝ) (x : M) : Φ t u x = Φ 0 (u - t) x := by
  have h1 : IsMIntegralCurve (fun τ : ℝ => Φ t τ x) V := fun τ => hΦderiv t τ x
  have h2 : IsMIntegralCurve (fun τ : ℝ => Φ 0 (τ - t) x) V := fun τ =>
    Work.Diff.ODE.hasMFDerivAt_comp_sub_const (σ := t) (τ := τ) (hΦderiv 0 (τ - t) x)
  have huniq := phi_eq_of_eq hVsm h1 h2 (t₀ := t) (by simp [hΦself])
  exact congrFun huniq u

/-- The cocycle identity for `Φ`. -/
lemma phi_cocycle
    (hVsm : ContMDiff I (I.prod (modelWithCornersSelf ℝ E)) ∞
      (fun y : M => (⟨y, V y⟩ : Bundle.TotalSpace E (TangentSpace I))))
    (hΦself : ∀ s x, Φ s s x = x)
    (hΦderiv : ∀ s t x, HasMFDerivAt (modelWithCornersSelf ℝ ℝ) I (fun τ : ℝ => Φ s τ x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (V (Φ s t x))))
    (s t u : ℝ) (x : M) : Φ t u (Φ s t x) = Φ s u x := by
  have h1 : IsMIntegralCurve (fun τ : ℝ => Φ t τ (Φ s t x)) V := fun τ => hΦderiv t τ (Φ s t x)
  have h2 : IsMIntegralCurve (fun τ : ℝ => Φ s τ x) V := fun τ => hΦderiv s τ x
  have huniq := phi_eq_of_eq hVsm h1 h2 (t₀ := t) (by simp [hΦself])
  exact congrFun huniq u

/-- The flow law for the one-parameter flow `Φ 0 ·`. -/
lemma phi_flow_add
    (hVsm : ContMDiff I (I.prod (modelWithCornersSelf ℝ E)) ∞
      (fun y : M => (⟨y, V y⟩ : Bundle.TotalSpace E (TangentSpace I))))
    (hΦself : ∀ s x, Φ s s x = x)
    (hΦderiv : ∀ s t x, HasMFDerivAt (modelWithCornersSelf ℝ ℝ) I (fun τ : ℝ => Φ s τ x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (V (Φ s t x))))
    (a b : ℝ) (x : M) : Φ 0 a (Φ 0 b x) = Φ 0 (a + b) x := by
  have h := phi_cocycle hVsm hΦself hΦderiv 0 b (a + b) x
  have h2 := phi_shift hVsm hΦself hΦderiv 0 b (a + b) (Φ 0 b x)
  rw [h2, show a + b - b = a from by ring] at h
  exact h

/-- Two points of the same flow line of `Φ 0 ·` have the same orbit. -/
lemma phi_orbit_congr
    (hVsm : ContMDiff I (I.prod (modelWithCornersSelf ℝ E)) ∞
      (fun y : M => (⟨y, V y⟩ : Bundle.TotalSpace E (TangentSpace I))))
    (hΦself : ∀ s x, Φ s s x = x)
    (hΦderiv : ∀ s t x, HasMFDerivAt (modelWithCornersSelf ℝ ℝ) I (fun τ : ℝ => Φ s τ x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (V (Φ s t x))))
    {x z : M} {s : ℝ} (hs : z = Φ 0 s x) (w : M) :
    (∃ a : ℝ, w = Φ 0 a z) ↔ (∃ a : ℝ, w = Φ 0 a x) := by
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a + s, by rw [hs]; exact phi_flow_add hVsm hΦself hΦderiv a s x⟩
  · rintro ⟨b, rfl⟩
    refine ⟨b - s, ?_⟩
    have hb : Φ 0 b x = Φ 0 (b - s) (Φ 0 s x) := by
      have h := phi_flow_add hVsm hΦself hΦderiv (b - s) s x
      rw [show b - s + s = b from by ring] at h
      exact h.symm
    exact hb.trans (by rw [← hs])

end Flow

/-! ## 2.  `u` is constant along the flow inside `N` -/

section UFlow

variable {N : Set M} {u : M → Sph2}
  {V : (x : M) → TangentSpace I x} {Φ : ℝ → ℝ → M → M}

/-- **`u` is constant along the flow lines of `V`, as long as they stay in `N`.** -/
lemma u_flow_eq
    (hΦself : ∀ s x, Φ s s x = x)
    (hΦderiv : ∀ s t x, HasMFDerivAt 𝓘(ℝ,ℝ) I (fun τ : ℝ => Φ s τ x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (V (Φ s t x))))
    (hN : IsOpen N)
    (hu : ContMDiffOn I 𝓘(ℝ, Sph2) ∞ u N)
    (huV : ∀ x ∈ N, mfderiv I 𝓘(ℝ, Sph2) u x (V x) = 0)
    {a b : ℝ} (h0 : (0 : ℝ) ∈ Set.Ioo a b)
    (z : M) {t : ℝ} (ht : t ∈ Set.Ioo a b)
    (hin : ∀ τ ∈ Set.Ioo a b, Φ 0 τ z ∈ N) :
    u (Φ 0 t z) = u z := by
  have hγ : IsMIntegralCurveOn (fun τ : ℝ => u (Φ 0 τ z))
      (fun x : Sph2 => (0 : TangentSpace (𝓘(ℝ, Sph2)) x)) (Set.Ioo a b) := by
    intro τ hτ
    have hcomp := ((hu.contMDiffAt (hN.mem_nhds (hin τ hτ))).mdifferentiableAt (by simp)).hasMFDerivAt.comp
      τ (hΦderiv 0 τ z)
    have hL : (mfderiv I 𝓘(ℝ, Sph2) u (Φ 0 τ z)) ∘SL
        ((1 : ℝ →L[ℝ] ℝ).smulRight (V (Φ 0 τ z)))
        = (1 : ℝ →L[ℝ] ℝ).smulRight
            (0 : TangentSpace (𝓘(ℝ, Sph2)) (u (Φ 0 τ z))) := by
      ext s
      simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
        huV (Φ 0 τ z) (hin τ hτ)]
    rw [← hL]
    exact hcomp.hasMFDerivWithinAt
  have hc : IsMIntegralCurveOn (fun _ : ℝ => u (Φ 0 0 z))
      (fun x : Sph2 => (0 : TangentSpace (𝓘(ℝ, Sph2)) x)) (Set.Ioo a b) := by
    intro τ hτ
    rw [show (1 : ℝ →L[ℝ] ℝ).smulRight
        (0 : TangentSpace (𝓘(ℝ, Sph2)) (u (Φ 0 0 z))) = 0 from by ext s; simp]
    exact (hasMFDerivAt_const (u (Φ 0 0 z)) τ).hasMFDerivWithinAt
  have huniq := isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless
    (I := 𝓘(ℝ, Sph2)) (t₀ := 0) h0
    ((Bundle.contMDiff_zeroSection (𝕜 := ℝ) (E := TangentSpace (𝓘(ℝ, Sph2)))
      (IB := 𝓘(ℝ, Sph2)) (n := ∞)).of_le (by simp))
    hγ hc (by rfl)
  have h1 := huniq ht
  simpa [Function.comp_def, hΦself] using h1

end UFlow

/-! ## 3.  Straight chart paths -/

section ChartLine

/-- The straight path through the chart centre `z` with chart velocity `w`. -/
def chartLine (z : M) (w : E) : ℝ → M :=
  fun t => (extChartAt I z).symm ((extChartAt I z) z + t • w)

/-- The set of parameters for which `chartLine` is inside the chart target. -/
def chartLineSet (z : M) (w : E) : Set ℝ :=
  {t : ℝ | (extChartAt I z) z + t • w ∈ (extChartAt I z).target}

lemma chartLine_zero (z : M) (w : E) : chartLine (I := I) z w 0 = z := by
  rw [chartLine, zero_smul, add_zero]
  exact PartialEquiv.left_inv _ (mem_extChartAt_source z)

lemma chartLine_set_open (z : M) (w : E) : IsOpen (chartLineSet (I := I) z w) :=
  (isOpen_extChartAt_target (I := I) z).preimage (by fun_prop)

lemma chartLine_set_mem (z : M) (w : E) : (0 : ℝ) ∈ chartLineSet (I := I) z w := by
  rw [chartLineSet, Set.mem_setOf_eq, zero_smul, add_zero]
  exact mem_extChartAt_target z

lemma chartLine_smoothOn (z : M) (w : E) :
    ContMDiffOn 𝓘(ℝ,ℝ) I ∞ (chartLine (I := I) z w) (chartLineSet (I := I) z w) := by
  have h1 : ContMDiffOn 𝓘(ℝ,ℝ) 𝓘(ℝ,E) ∞
      (fun t : ℝ => (extChartAt I z) z + t • w) (chartLineSet (I := I) z w) :=
    (contMDiffOn_const (c := (extChartAt I z) z)).add
      (ContinuousLinearMap.contMDiffOn ((1 : ℝ →L[ℝ] ℝ).smulRight w))
  exact (contMDiffOn_extChartAt_symm (I := I) z).comp h1 (fun t ht => ht)

/-- The derivative of the straight chart path at its base point. -/
lemma chartLine_hasMFDerivAt (z : M) (w : E) :
    HasMFDerivAt 𝓘(ℝ,ℝ) I (chartLine (I := I) z w) 0
      ((1 : ℝ →L[ℝ] ℝ).smulRight (show TangentSpace I z from w)) := by
  have hχval : mfderiv 𝓘(ℝ,E) I (extChartAt I z).symm ((extChartAt I z) z)
      = (ContinuousLinearMap.id ℝ E : E →L[ℝ] TangentSpace I z) := by
    have h1 := mfderivWithin_range_extChartAt_symm (I := I) (x := z) (𝕜 := ℝ)
    rw [ModelWithCorners.Boundaryless.range_eq_univ (I := I)] at h1
    rw [mfderivWithin_univ] at h1
    exact h1
  have hχ : HasMFDerivAt 𝓘(ℝ,E) I (extChartAt I z).symm ((extChartAt I z) z)
      (ContinuousLinearMap.id ℝ E : E →L[ℝ] TangentSpace I z) := by
    have hmd : MDifferentiableAt 𝓘(ℝ,E) I (extChartAt I z).symm ((extChartAt I z) z) :=
      (mdifferentiableWithinAt_extChartAt_symm (I := I) (x := z)
        (mem_extChartAt_target z)).mdifferentiableAt
        (by rw [ModelWithCorners.Boundaryless.range_eq_univ]; exact univ_mem)
    have h := hmd.hasMFDerivAt
    rwa [hχval] at h
  have hlin : HasMFDerivAt 𝓘(ℝ,ℝ) 𝓘(ℝ,E)
      (fun t : ℝ => (extChartAt I z) z + t • w) 0 ((1 : ℝ →L[ℝ] ℝ).smulRight w) :=
    hasMFDerivAt_iff_hasFDerivAt.mpr
      (((hasFDerivAt_id (𝕜 := ℝ) (0 : ℝ)).smul_const w).const_add ((extChartAt I z) z))
  have hχ' : HasMFDerivAt 𝓘(ℝ,E) I (extChartAt I z).symm ((extChartAt I z) z + (0 : ℝ) • w)
      (ContinuousLinearMap.id ℝ E : E →L[ℝ] TangentSpace I z) := by
    rw [show (extChartAt I z) z + (0 : ℝ) • w = (extChartAt I z) z from by simp]
    exact hχ
  have hcomp := HasMFDerivAt.comp (x := (0 : ℝ)) (g := (extChartAt I z).symm)
    (f := fun t : ℝ => (extChartAt I z) z + t • w) hχ' hlin
  convert hcomp using 2 <;>
    first
      | rfl
      | (ext x; rfl)
      | (ext s; simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply])

end ChartLine

/-! ## 4.  The two-parameter family `(λ, s) ↦ Φ 0 s (σ λ)` -/

section TwoParam

variable {Φ : ℝ → ℝ → M → M}

/-- The two-parameter family associated with a transversal curve `σ`. -/
def twoParam (Φ : ℝ → ℝ → M → M) (σ : ℝ → M) (p : Par) : M :=
  Φ 0 (p 1) (σ (p 0))

lemma contMDiff_pair_flow (hΦsm : ContMDiff ((𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ)).prod I) I ∞
      (fun q : (ℝ × ℝ) × M => Φ q.1.1 q.1.2 q.2)) :
    ContMDiff (𝓘(ℝ,ℝ).prod I) I ∞ (fun q : ℝ × M => Φ 0 q.1 q.2) := by
  have h1 : ContMDiff (𝓘(ℝ,ℝ).prod I) (𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ)) ∞
      (fun q : ℝ × M => ((0 : ℝ), q.1)) :=
    contMDiff_const.prodMk contMDiff_fst
  have h2 : ContMDiff (𝓘(ℝ,ℝ).prod I) ((𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ)).prod I) ∞
      (fun q : ℝ × M => (((0 : ℝ), q.1), q.2)) := h1.prodMk contMDiff_snd
  have h3 := hΦsm.comp h2
  simpa [Function.comp_def] using h3

lemma twoParam_smoothOn {σ : ℝ → M} {z : M} {w : E}
    (hΦsm : ContMDiff ((𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ)).prod I) I ∞
      (fun q : (ℝ × ℝ) × M => Φ q.1.1 q.1.2 q.2))
    (hσ : ContMDiffOn 𝓘(ℝ,ℝ) I ∞ σ (chartLineSet (I := I) z w)) :
    ContMDiffOn 𝓘(ℝ, Par) I ∞ (twoParam Φ σ) {p : Par | p 0 ∈ chartLineSet (I := I) z w} := by
  have h1 : ContMDiffOn 𝓘(ℝ, Par) ((𝓘(ℝ,ℝ)).prod I) ∞
      (fun p : Par => (p 1, σ (p 0))) {p : Par | p 0 ∈ chartLineSet (I := I) z w} :=
    ContMDiffOn.prodMk
      (ContinuousLinearMap.contMDiffOn
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1))
      (hσ.comp (ContinuousLinearMap.contMDiffOn
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0))
        (fun p hp => hp))
  exact ((contMDiff_pair_flow hΦsm).contMDiffOn (s := Set.univ)).comp h1 (fun p _ => trivial)

end TwoParam

end

end Work.Diff.Dim2
