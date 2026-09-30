import Submission.Work.RiemLib.EnergyRayCover
import Submission.Work.RiemLib.IndexScale
import Submission.Work.RiemLib.EnergyRaySmooth
import Submission.Work.RiemLib.IndexBackUnique
import Submission.Work.RiemLib.GlobalBM
import Submission.Work.RiemLib.Commons.Analysis.Calculus.exists_lt_of_deriv_eq_zero_of_hasDerivAt_deriv_neg
import Submission.Work.RiemLib.Commons.Analysis.Calculus.exists_lt_of_hasDerivAt_deriv_neg
import Submission.Work.RiemLib.Minimal
import Submission.Work.RiemLib.GeodesicSpeed
import Submission.Work.RiemLib.Length
import Submission.Work.RiemLib.BumpField
import Submission.Work.RiemLib.JacobiGlobal
import Submission.Work.RiemLib.IndexFTC
import Submission.Work.RiemLib.CutTime
import Submission.Work.RiemLib.ConjCut
import Submission.Work.RiemLib.SingularConj
import Submission.Work.RiemLib.Commons.Topology.continuousOn_Icc_of_continuousOn_pieces
import Submission.Work.RiemLib.Commons.Analysis.Calculus.hasDerivAt_deriv_add

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open MeasureTheory
open scoped MeasureTheory
open Submission.Geodesic
open Submission.JacobiGlobal
open Submission.IndexIntrinsic
open Submission.IndexIntrinsic2
open Submission.BonnetMyers
open Submission.JacobiCoords
open Submission.SecondVarGlobal
open Submission.IndexCorner
open Submission.IntrinsicVariation
open Submission.GExpFlow
open Submission.SmoothFieldCover
open Submission.GlobalExp
open Submission.Length
open Submission.GeodesicSpeed
open Submission.EnergyRayCover
open Submission.CurvatureVec
open Submission.IndexScale
open Submission.IndexFTC

namespace Submission.ConjEnergy

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

/-! ## 1. Elementary algebra of the fields -/

/-- `DtQ` is additive in the field and its derivative. -/
lemma DtQ_add (x₀ : M) (u w η η' e e' : ℝ → E) (t : ℝ) :
    DtQ cov x₀ u (fun s => η s + η' s) w (fun s => e s + e' s) t
      = DtQ cov x₀ u η w e t + DtQ cov x₀ u η' w e' t := by
  have h := DtQ_add_smul (cov := cov) x₀ u w η e η' e' (1 : ℝ) t
  simpa using h

/-- The chart coordinates of a sum of two fields along a curve. -/
lemma chartCoords_add {z : M} {γ : ℝ → M}
    (V W : (t : ℝ) → TangentSpace I (γ t)) :
    chartCoords (I := I) z γ (fun t => V t + W t)
      = fun t => chartCoords (I := I) z γ V t + chartCoords (I := I) z γ W t := by
  funext t
  exact map_add ((trivializationAt E (TangentSpace I) z).continuousLinearMapAt ℝ (γ t)) (V t) (W t)

/-- A field smooth along a curve stays smooth after adding another such field. -/
lemma SmoothAlongAt_add {γ : ℝ → M} {V W : (t : ℝ) → TangentSpace I (γ t)} {t : ℝ}
    (hV : SmoothAlongAt (I := I) γ V t) (hW : SmoothAlongAt (I := I) γ W t) :
    SmoothAlongAt (I := I) γ (fun s => V s + W s) t := by
  obtain ⟨U, hUopen, htU, hUsrc, hUcd⟩ := hV
  obtain ⟨U', hU'open, htU', hUsrc', hUcd'⟩ := hW
  refine ⟨U ∩ U', hUopen.inter hU'open, ⟨htU, htU'⟩, fun s hs => hUsrc s hs.1, ?_⟩
  rw [chartCoords_add]
  exact (hUcd.mono (fun s hs => hs.1)).add (hUcd'.mono (fun s hs => hs.2))

/-- `covAlong` is additive in the field. -/
theorem covAlong_add (htor : cov.torsion = 0) {γ : ℝ → M}
    {V W : (t : ℝ) → TangentSpace I (γ t)} {t : ℝ}
    (hV : SmoothAlongAt (I := I) γ V t) (hW : SmoothAlongAt (I := I) γ W t) :
    covAlong cov (fun s => V s + W s) t = covAlong cov V t + covAlong cov W t := by
  obtain ⟨U, hUopen, htU, hUsrc, hUcd⟩ := hV
  obtain ⟨U', hU'open, htU', hUsrc', hUcd'⟩ := hW
  have hd1 : DifferentiableAt ℝ (chartCoords (I := I) (γ t) γ V) t :=
    (hUcd.differentiableOn (by simp)).differentiableAt (hUopen.mem_nhds htU)
  have hd2 : DifferentiableAt ℝ (chartCoords (I := I) (γ t) γ W) t :=
    (hUcd'.differentiableOn (by simp)).differentiableAt (hU'open.mem_nhds htU')
  have h2 : chartCoords (I := I) (γ t) γ (fun s => V s + W s) t
      = chartCoords (I := I) (γ t) γ V t + (1 : ℝ) • chartCoords (I := I) (γ t) γ W t := by
    rw [chartCoords_add]
    simp
  have h4 : deriv (chartCoords (I := I) (γ t) γ (fun s => V s + W s)) t
      = deriv (chartCoords (I := I) (γ t) γ V) t
        + (1 : ℝ) • deriv (chartCoords (I := I) (γ t) γ W) t := by
    have heq : chartCoords (I := I) (γ t) γ (fun s => V s + W s)
        =ᶠ[𝓝 t] fun s => chartCoords (I := I) (γ t) γ V s
          + chartCoords (I := I) (γ t) γ W s :=
      Filter.EventuallyEq.of_eq (chartCoords_add V W)
    rw [Filter.EventuallyEq.deriv_eq heq,
      show (fun s : ℝ => chartCoords (I := I) (γ t) γ V s
          + chartCoords (I := I) (γ t) γ W s)
        = (fun s : ℝ => chartCoords (I := I) (γ t) γ V s)
          + (fun s : ℝ => chartCoords (I := I) (γ t) γ W s) from rfl,
      deriv_add hd1 hd2, one_smul]
  rw [covAlong, covAlong, covAlong]
  have hkey := DtQ_congr (cov := cov) (x₀ := γ t)
    (u₁ := chartCoord (I := I) (γ t) γ) (u₂ := chartCoord (I := I) (γ t) γ)
    (η₁ := chartCoords (I := I) (γ t) γ (fun s => V s + W s))
    (η₂ := fun s => chartCoords (I := I) (γ t) γ V s
      + (1 : ℝ) • chartCoords (I := I) (γ t) γ W s)
    (w₁ := deriv (chartCoord (I := I) (γ t) γ))
    (w₂ := deriv (chartCoord (I := I) (γ t) γ))
    (e₁ := deriv (chartCoords (I := I) (γ t) γ (fun s => V s + W s)))
    (e₂ := fun s => deriv (chartCoords (I := I) (γ t) γ V) s
      + (1 : ℝ) • deriv (chartCoords (I := I) (γ t) γ W) s)
    (t := t) rfl h2 rfl h4
  rw [hkey]
  rw [DtQ_add_smul (cov := cov) (x₀ := γ t) (u := chartCoord (I := I) (γ t) γ)
    (w := deriv (chartCoord (I := I) (γ t) γ))
    (η := chartCoords (I := I) (γ t) γ V) (e := deriv (chartCoords (I := I) (γ t) γ V))
    (W := chartCoords (I := I) (γ t) γ W) (W' := deriv (chartCoords (I := I) (γ t) γ W))
    (ε := 1) (t := t)]
  rw [one_smul, frameVector_add]

/-- `covAlong` of a linear combination. -/
theorem covAlong_add_smul (htor : cov.torsion = 0) {γ : ℝ → M}
    {V W : (t : ℝ) → TangentSpace I (γ t)} {t : ℝ} (c : ℝ)
    (hV : SmoothAlongAt (I := I) γ V t) (hW : SmoothAlongAt (I := I) γ W t) :
    covAlong cov (fun s => V s + c • W s) t = covAlong cov V t + c • covAlong cov W t := by
  rw [covAlong_add (cov := cov) htor hV (Submission.EnergyRay.SmoothAlongAt_smul (I := I) c hW),
    Submission.IndexScale.covAlong_smul htor]

/-- **The `GExp`-ray is smooth on all of `ℝ`.** -/
theorem contMDiff_GExp_smul (hmet : IsMetricCompatible cov) (x : M)
    {v : TangentSpace I x} (hv : v ≠ 0) :
    ContMDiff 𝓘(ℝ) I ∞ (fun s : ℝ => GExp (cov := cov) hmet x (s • v)) := by
  intro s
  have hs : s ∈ Ioo (-(|s| + 2)) (|s| + 2) :=
    ⟨by linarith [neg_abs_le s], by linarith [le_abs_self s]⟩
  exact (Submission.LensLoop.contMDiffOn_GExp_smul_Ioo_symm (cov := cov) hmet x hv (|s| + 2)
    s hs).contMDiffAt (isOpen_Ioo.mem_nhds hs)

/-! ## 2. Bilinearity of `bilAlong` -/

/-- `bilAlong` is linear in its first pair of arguments. -/
lemma bilAlong_smul_left (γ : ℝ → M) (V W Z Y : (t : ℝ) → TangentSpace I (γ t))
    (c : ℝ) (t : ℝ) :
    bilAlong (cov := cov) γ (fun s => c • V s) W (fun s => c • Z s) Y t
      = c * bilAlong (cov := cov) γ V W Z Y t := by
  simp only [bilAlong, inner_smul_left, curvVec_smul_left, starRingEnd_apply, star_trivial]
  ring

/-- `bilAlong` is linear in its second pair of arguments. -/
lemma bilAlong_smul_right (γ : ℝ → M) (V W Z Y : (t : ℝ) → TangentSpace I (γ t))
    (c : ℝ) (t : ℝ) :
    bilAlong (cov := cov) γ V (fun s => c • W s) Z (fun s => c • Y s) t
      = c * bilAlong (cov := cov) γ V W Z Y t := by
  simp only [bilAlong, inner_smul_right]
  ring

/-! ## 3. Continuity and integrability of the intrinsic index integrand -/

/-- **Continuity of the intrinsic index integrand along a smooth field.**  For a `C^∞` curve `γ` with
nonvanishing velocity and a field `V` smooth along `γ`, the function
`t ↦ idxAlong γ V (∇V) t` is continuous on `[a,b]`. -/
theorem continuousOn_idxAlong_of_smooth (htor : cov.torsion = 0)
    {γ : ℝ → M} {V : (t : ℝ) → TangentSpace I (γ t)} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContMDiff 𝓘(ℝ) I ∞ γ) (hne : ∀ s, curveVelocity (I := I) γ s ≠ 0)
    (hVs : ∀ s ∈ Icc (a - 1) (b + 1), SmoothAlongAt (I := I) γ V s) :
    ContinuousOn (fun t => idxAlong (cov := cov) γ V (covAlong cov V) t) (Icc a b) := by
  classical
  obtain ⟨N, c, S, T, z, hc0, hcN, hmono, hSB, hsrc, hcdU, hcdV, hVfr, hroomA⟩ :=
    exists_partition_smoothField (I := I) hab (hγ.contMDiffOn.mono (subset_univ _))
      (fun s hs => hVs s ⟨by linarith [hs.1], by linarith [hs.2]⟩)
  have hZc : ∀ k < N, IsCompact (γ '' Icc (S k) (T k)) :=
    fun k _ => isCompact_Icc.image_of_continuousOn hγ.continuous.continuousOn
  have hZs : ∀ k < N, γ '' Icc (S k) (T k) ⊆ (chartAt H (z k)).source := by
    rintro k hk _ ⟨t, ht, rfl⟩
    exact hsrc k hk t ht
  have hD : ∀ k < N, ∃ D : ChartFlowData (cov := cov) (I := I) (z k) (γ '' Icc (S k) (T k)), True :=
    fun k hk => exists_chartFlowData (cov := cov) (I := I) (z₀ := z k) (hZc k hk) (hZs k hk)
  choose D _ using hD
  have hpiece : ∀ k < N, ContinuousOn (fun t => idxAlong (cov := cov) γ V (covAlong cov V) t)
      (Icc (c k) (c (k + 1))) := by
    intro k hk
    have hcont := Submission.EnergyRayCover.continuousOn_idxAlong_piece (cov := cov) htor (D k hk)
      (hSB k hk).1 (hSB k hk).2 (hmono k hk).le (hsrc k hk) (hcdU k hk) (hcdV k hk) (hVfr k hk)
      (fun t _ => hγ.contMDiffOn) (fun t _ => hne t)
      (fun t ht => hVs t ⟨(hroomA k hk ht).1.le, (hroomA k hk ht).2.le⟩) 1
    refine hcont.congr (fun t ht => ?_)
    have h1 : (fun s : ℝ => (1 : ℝ) • V s) = V := by funext s; rw [one_smul]
    rw [h1]
  exact Commons.Topology.continuousOn_Icc_of_continuousOn_pieces hc0 hcN
    (fun k hk => (hmono k hk).le) hpiece

/-- **Interval-integrability of the intrinsic index integrand.** -/
theorem intervalIntegrable_idxAlong_of_smooth (htor : cov.torsion = 0)
    {γ : ℝ → M} {V : (t : ℝ) → TangentSpace I (γ t)} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContMDiff 𝓘(ℝ) I ∞ γ) (hne : ∀ s, curveVelocity (I := I) γ s ≠ 0)
    (hVs : ∀ s, SmoothAlongAt (I := I) γ V s) :
    IntervalIntegrable (fun t => idxAlong (cov := cov) γ V (covAlong cov V) t) volume a b :=
  (continuousOn_idxAlong_of_smooth (cov := cov) htor hab hγ hne
    (fun s _ => hVs s)).intervalIntegrable_of_Icc hab

/-- **Interval-integrability of the polarised index integrand**, from the polarisation identity. -/
theorem intervalIntegrable_bilAlong_of_smooth (hmet : IsMetricCompatible cov)
    (htor : cov.torsion = 0)
    {γ : ℝ → M} {A B : (t : ℝ) → TangentSpace I (γ t)} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContMDiff 𝓘(ℝ) I ∞ γ) (hne : ∀ s, curveVelocity (I := I) γ s ≠ 0)
    (hAs : ∀ s, SmoothAlongAt (I := I) γ A s) (hBs : ∀ s, SmoothAlongAt (I := I) γ B s) :
    IntervalIntegrable
      (fun t => bilAlong (cov := cov) γ A B (covAlong cov A) (covAlong cov B) t) volume a b := by
  have hsum : ∀ s, SmoothAlongAt (I := I) γ (fun s => A s + B s) s :=
    fun s => SmoothAlongAt_add (hAs s) (hBs s)
  have hAB := intervalIntegrable_idxAlong_of_smooth (cov := cov) htor hab hγ hne hsum
  have hA := intervalIntegrable_idxAlong_of_smooth (cov := cov) htor hab hγ hne hAs
  have hB := intervalIntegrable_idxAlong_of_smooth (cov := cov) htor hab hγ hne hBs
  have hcov : covAlong cov (fun s => A s + B s) = fun s => covAlong cov A s + covAlong cov B s := by
    funext t
    exact covAlong_add (cov := cov) htor (hAs t) (hBs t)
  have hpolar : (fun t => 2 * bilAlong (cov := cov) γ A B (covAlong cov A) (covAlong cov B) t)
      = fun t => idxAlong (cov := cov) γ (fun s => A s + B s) (covAlong cov (fun s => A s + B s)) t
          - idxAlong (cov := cov) γ A (covAlong cov A) t
          - idxAlong (cov := cov) γ B (covAlong cov B) t := by
    funext t
    rw [bilAlong_polar (cov := cov) hmet htor γ A B (covAlong cov A)
      (covAlong cov B) t, hcov]
  have h2 : IntervalIntegrable (fun t => 2 * bilAlong (cov := cov) γ A B (covAlong cov A)
      (covAlong cov B) t) volume a b := by
    rw [hpolar]
    exact (hAB.sub hA).sub hB
  have hfac : (fun t => bilAlong (cov := cov) γ A B (covAlong cov A) (covAlong cov B) t)
      = fun t => (2 : ℝ)⁻¹ * (2 * bilAlong (cov := cov) γ A B (covAlong cov A) (covAlong cov B) t) := by
    funext t; ring
  rw [hfac]
  exact h2.const_mul _

/-- **The polarisation expansion under the integral**: for `A`, `B` smooth along the `C^∞` curve `γ`
with nonvanishing velocity, the index integral of `A + δB` expands into the three pieces. -/
theorem integral_idxAlong_add_smul (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {γ : ℝ → M} {A B : (t : ℝ) → TangentSpace I (γ t)} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContMDiff 𝓘(ℝ) I ∞ γ) (hne : ∀ s, curveVelocity (I := I) γ s ≠ 0)
    (hAs : ∀ s, SmoothAlongAt (I := I) γ A s) (hBs : ∀ s, SmoothAlongAt (I := I) γ B s)
    (δ : ℝ) :
    ∫ t in a..b, idxAlong (cov := cov) γ (fun s => A s + δ • B s)
        (covAlong cov (fun s => A s + δ • B s)) t
      = (∫ t in a..b, idxAlong (cov := cov) γ A (covAlong cov A) t)
        + 2 * δ * (∫ t in a..b,
            bilAlong (cov := cov) γ A B (covAlong cov A) (covAlong cov B) t)
        + δ ^ 2 * (∫ t in a..b, idxAlong (cov := cov) γ B (covAlong cov B) t) := by
  have hA := intervalIntegrable_idxAlong_of_smooth (cov := cov) htor hab hγ hne hAs
  have hB := intervalIntegrable_idxAlong_of_smooth (cov := cov) htor hab hγ hne hBs
  have hbil := intervalIntegrable_bilAlong_of_smooth (cov := cov) hmet htor hab hγ hne hAs hBs
  have hδB : ∀ s, SmoothAlongAt (I := I) γ (fun s => δ • B s) s :=
    fun s => Submission.EnergyRay.SmoothAlongAt_smul (I := I) δ (hBs s)
  have hAB : ∀ s, SmoothAlongAt (I := I) γ (fun s => A s + δ • B s) s :=
    fun s => SmoothAlongAt_add (hAs s) (hδB s)
  -- step 1: identify `covAlong (A + δB)`
  have hcov : covAlong cov (fun s => A s + δ • B s)
      = fun s => covAlong cov A s + δ • covAlong cov B s := by
    funext t
    exact covAlong_add_smul (cov := cov) htor δ (hAs t) (hBs t)
  rw [intervalIntegral.integral_congr (g := fun t => idxAlong (cov := cov) γ
      (fun s => A s + δ • B s) (fun s => covAlong cov A s + δ • covAlong cov B s) t)
    (fun t _ => by rw [hcov])]
  -- step 2: expand pointwise
  rw [intervalIntegral.integral_congr (g := fun t => idxAlong (cov := cov) γ A (covAlong cov A) t
      + 2 * δ * bilAlong (cov := cov) γ A B (covAlong cov A) (covAlong cov B) t
      + δ ^ 2 * idxAlong (cov := cov) γ B (covAlong cov B) t)
    (fun t _ => idxAlong_add_smul (cov := cov) hmet htor γ A B (covAlong cov A)
      (covAlong cov B) δ t)]
  -- step 3: split
  have hY : IntervalIntegrable (fun t => 2 * δ * bilAlong (cov := cov) γ A B (covAlong cov A)
      (covAlong cov B) t) volume a b := hbil.const_mul (2 * δ)
  have hZ : IntervalIntegrable (fun t => δ ^ 2 * idxAlong (cov := cov) γ B (covAlong cov B) t)
      volume a b := hB.const_mul _
  rw [intervalIntegral.integral_add (hA.add hY) hZ, intervalIntegral.integral_add hA hY,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  try ring


/-! ## 5. The cut-off field of the shortening argument -/

/-- The `C^∞` bump of the shortening argument: supported in `(t - 2δ, t + 2δ)`, equal to `1` at
`t`. -/
noncomputable def bumpChi (t δ : ℝ) (u : ℝ) : ℝ :=
  Real.smoothTransition ((u - (t - 2 * δ)) / δ) * Real.smoothTransition (((t + 2 * δ) - u) / δ)

lemma bumpChi_t {t δ : ℝ} (hδ : 0 < δ) : bumpChi t δ t = 1 := by
  unfold bumpChi
  have h1 : (1 : ℝ) ≤ (t - (t - 2 * δ)) / δ := by
    rw [le_div_iff₀ hδ]; linarith
  have h2 : (1 : ℝ) ≤ ((t + 2 * δ) - t) / δ := by
    rw [le_div_iff₀ hδ]; linarith
  rw [Real.smoothTransition.eq_one_iff_one_le.mpr h1,
    Real.smoothTransition.eq_one_iff_one_le.mpr h2, mul_one]

lemma bumpChi_eq_zero_of_le {t δ u : ℝ} (hδ : 0 < δ) (hu : u ≤ t - 2 * δ) :
    bumpChi t δ u = 0 := by
  have hz : Real.smoothTransition ((u - (t - 2 * δ)) / δ) = 0 :=
    Real.smoothTransition.zero_of_nonpos (by
      rw [div_nonpos_iff]; exact Or.inr ⟨by linarith, hδ.le⟩)
  unfold bumpChi
  rw [hz, zero_mul]

lemma bumpChi_eq_zero_of_ge {t δ u : ℝ} (hδ : 0 < δ) (hu : t + 2 * δ ≤ u) :
    bumpChi t δ u = 0 := by
  have hz : Real.smoothTransition (((t + 2 * δ) - u) / δ) = 0 :=
    Real.smoothTransition.zero_of_nonpos (by
      rw [div_nonpos_iff]; exact Or.inr ⟨by linarith, hδ.le⟩)
  unfold bumpChi
  rw [hz, mul_zero]

lemma contDiff_bumpChi (t δ : ℝ) : ContDiff ℝ ∞ (bumpChi t δ) := by
  unfold bumpChi
  exact ((Real.smoothTransition.contDiff (n := ⊤)).comp
      ((contDiff_id.sub contDiff_const).div_const δ)).mul
    ((Real.smoothTransition.contDiff (n := ⊤)).comp
      ((contDiff_const.sub contDiff_id).div_const δ))

/-- **The cut-off field**: `χ • c` in the chart at `γ t`, where `χ = bumpChi t δ`. -/
noncomputable def shortField (γ : ℝ → M) (t δ : ℝ) (c : E) :
    (u : ℝ) → TangentSpace I (γ u) :=
  Submission.BumpField.bumpField (I := I) (γ t) γ (bumpChi t δ) c

lemma shortField_apply (γ : ℝ → M) (t δ : ℝ) (c : E) (u : ℝ) :
    shortField (I := I) γ t δ c u
      = bumpChi t δ u • frameVector (I := I) (γ t) (γ u) c :=
  Submission.BumpField.bumpField_apply (I := I) (γ t) γ (bumpChi t δ) c u

lemma shortField_eq_zero_of_le {γ : ℝ → M} {t δ : ℝ} {c : E} {u : ℝ} (hδ : 0 < δ)
    (hu : u ≤ t - 2 * δ) : shortField (I := I) γ t δ c u = 0 := by
  rw [shortField_apply, bumpChi_eq_zero_of_le hδ hu, zero_smul]

lemma shortField_eq_zero_of_ge {γ : ℝ → M} {t δ : ℝ} {c : E} {u : ℝ} (hδ : 0 < δ)
    (hu : t + 2 * δ ≤ u) : shortField (I := I) γ t δ c u = 0 := by
  rw [shortField_apply, bumpChi_eq_zero_of_ge hδ hu, zero_smul]

/-- **Smoothness of the cut-off field along the curve**: the field `shortField γ t δ c` is smooth
along `γ` at *every* point of `ℝ`, provided the curve stays in the chart at `γ t` on the support
interval. -/
theorem smoothAlongAt_shortField {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ) I ∞ γ) {t δ : ℝ} (hδ : 0 < δ)
    (hsmall : γ '' Ioo (t - 3 * δ) (t + 3 * δ) ⊆ (chartAt H (γ t)).source) (c : E) (s : ℝ) :
    SmoothAlongAt (I := I) γ (shortField (I := I) γ t δ c) s := by
  rcases lt_or_ge s (t + 3 * δ) with hs | hs
  rcases lt_or_ge (t - 3 * δ) s with hs' | hs'
  · -- inside the support interval
    refine Submission.BumpField.smoothAlongAt_bumpField (I := I) (z := γ t) (c := c)
      (U := Ioo (t - 3 * δ) (t + 3 * δ) ∩ γ ⁻¹' (chartAt H (γ s)).source)
      (isOpen_Ioo.inter ((chartAt H (γ s)).open_source.preimage hγ.continuous))
      ⟨⟨hs', hs⟩, mem_chart_source H (γ s)⟩
      ((contDiff_bumpChi t δ).contDiffOn) (hγ.contMDiffOn.mono Set.inter_subset_left)
      (fun u hu => hsmall ⟨u, hu.1, rfl⟩) (fun u hu => hu.2)
  · -- outside, on the left
    have hsU : s ∈ Iio (t - 2 * δ) ∪ Ioi (t + 2 * δ) := by
      rw [Set.mem_union]
      exact Or.inl (by rw [Set.mem_Iio]; linarith [hδ, hs'])
    refine ⟨(Iio (t - 2 * δ) ∪ Ioi (t + 2 * δ)) ∩ γ ⁻¹' (chartAt H (γ s)).source,
      (isOpen_Iio.union isOpen_Ioi).inter ((chartAt H (γ s)).open_source.preimage hγ.continuous),
      ⟨hsU, mem_chart_source H (γ s)⟩, fun u hu => hu.2, ?_⟩
    refine (contDiffOn_const (c := (0 : E))).congr (fun u hu => ?_)
    change ((trivializationAt E (TangentSpace I) (γ s)).continuousLinearMapAt ℝ (γ u))
        (shortField (I := I) γ t δ c u) = 0
    rcases hu.1 with h | h
    · rw [shortField_eq_zero_of_le (γ := γ) hδ (le_of_lt h)]
      exact map_zero _
    · rw [shortField_eq_zero_of_ge (γ := γ) hδ (le_of_lt h)]
      exact map_zero _
  · -- outside, on the right
    have hsU : s ∈ Iio (t - 2 * δ) ∪ Ioi (t + 2 * δ) := by
      rw [Set.mem_union]
      exact Or.inr (by rw [Set.mem_Ioi]; linarith [hδ, hs])
    refine ⟨(Iio (t - 2 * δ) ∪ Ioi (t + 2 * δ)) ∩ γ ⁻¹' (chartAt H (γ s)).source,
      (isOpen_Iio.union isOpen_Ioi).inter ((chartAt H (γ s)).open_source.preimage hγ.continuous),
      ⟨hsU, mem_chart_source H (γ s)⟩, fun u hu => hu.2, ?_⟩
    refine (contDiffOn_const (c := (0 : E))).congr (fun u hu => ?_)
    change ((trivializationAt E (TangentSpace I) (γ s)).continuousLinearMapAt ℝ (γ u))
        (shortField (I := I) γ t δ c u) = 0
    rcases hu.1 with h | h
    · rw [shortField_eq_zero_of_le (γ := γ) hδ (le_of_lt h)]
      exact map_zero _
    · rw [shortField_eq_zero_of_ge (γ := γ) hδ (le_of_lt h)]
      exact map_zero _


/-! ## 6. The energy of the two-piece variation and its second derivative -/

/-- The cover assembly of `EnergyCover.energy_second_deriv_cover_eventually`, **keeping** the
eventual differentiability of the energy (which is what the addition of the two piece energies
needs). -/
theorem energy_second_deriv_cover_eventually_ev
    {γ : ℝ → M} {V Z : (t : ℝ) → TangentSpace I (γ t)} {a b : ℝ}
    {N : ℕ} {c : ℕ → ℝ} {F : ℝ → ℝ → ℝ}
    (hc0 : c 0 = a) (hcN : c N = b)
    (hint : ∀ᶠ σ in 𝓝 (0 : ℝ), ∀ k : ℕ, k < N →
      IntervalIntegrable (fun t : ℝ => F σ t) volume (c k) (c (k + 1)))
    (hintZ : ∀ k : ℕ, k < N → IntervalIntegrable (fun t : ℝ => idxAlong (cov := cov) γ V Z t)
      volume (c k) (c (k + 1)))
    (hk : ∀ k : ℕ, k < N →
      (∀ᶠ σ in 𝓝 (0 : ℝ),
        DifferentiableAt ℝ (fun σ : ℝ => ∫ t in c k..c (k + 1), F σ t) σ) ∧
      HasDerivAt (deriv (fun σ : ℝ => ∫ t in c k..c (k + 1), F σ t))
        (2 * ∫ t in c k..c (k + 1), idxAlong (cov := cov) γ V Z t) 0) :
    HasDerivAt (deriv (fun σ : ℝ => ∫ t in a..b, F σ t))
      (2 * ∫ t in a..b, idxAlong (cov := cov) γ V Z t) 0 ∧
    (∀ᶠ σ in 𝓝 (0 : ℝ), DifferentiableAt ℝ (fun σ : ℝ => ∫ t in a..b, F σ t) σ) := by
  classical
  have hsum : (fun σ : ℝ => ∫ t in a..b, F σ t)
      =ᶠ[𝓝 (0 : ℝ)] fun σ : ℝ => ∑ k ∈ Finset.range N, ∫ t in c k..c (k + 1), F σ t := by
    filter_upwards [hint] with σ hσ
    have h := intervalIntegral.sum_integral_adjacent_intervals (μ := volume)
      (f := fun t : ℝ => F σ t) (a := c) (n := N) (fun k hk' => hσ k hk')
    rw [hc0, hcN] at h
    exact h.symm
  have hdiff : ∀ᶠ σ in 𝓝 (0 : ℝ), ∀ k ∈ Finset.range N,
      DifferentiableAt ℝ (fun σ : ℝ => ∫ t in c k..c (k + 1), F σ t) σ := by
    rw [Finset.eventually_all]
    intro k hk'
    exact (hk k (Finset.mem_range.mp hk')).1
  have hderiv : deriv (fun σ : ℝ => ∑ k ∈ Finset.range N, ∫ t in c k..c (k + 1), F σ t)
      =ᶠ[𝓝 (0 : ℝ)] (fun σ : ℝ => ∑ k ∈ Finset.range N,
        deriv (fun σ : ℝ => ∫ t in c k..c (k + 1), F σ t) σ) := by
    filter_upwards [hdiff] with σ hσ
    exact deriv_fun_sum hσ
  have hsecond : HasDerivAt (fun σ : ℝ => ∑ k ∈ Finset.range N,
      deriv (fun σ : ℝ => ∫ t in c k..c (k + 1), F σ t) σ)
      (∑ k ∈ Finset.range N, 2 * ∫ t in c k..c (k + 1), idxAlong (cov := cov) γ V Z t) 0 :=
    HasDerivAt.fun_sum (fun k hk' => (hk k (Finset.mem_range.mp hk')).2)
  have hsecond' : HasDerivAt (deriv (fun σ : ℝ => ∑ k ∈ Finset.range N,
      ∫ t in c k..c (k + 1), F σ t))
      (∑ k ∈ Finset.range N, 2 * ∫ t in c k..c (k + 1), idxAlong (cov := cov) γ V Z t) 0 :=
    hsecond.congr_of_eventuallyEq hderiv
  have hZsum : (∑ k ∈ Finset.range N, ∫ t in c k..c (k + 1), idxAlong (cov := cov) γ V Z t)
      = ∫ t in a..b, idxAlong (cov := cov) γ V Z t := by
    have h := intervalIntegral.sum_integral_adjacent_intervals (μ := volume)
      (f := fun t : ℝ => idxAlong (cov := cov) γ V Z t) (a := c) (n := N) hintZ
    rwa [hc0, hcN] at h
  refine ⟨?_, ?_⟩
  · have h2 := hsecond'
    rw [← Finset.mul_sum, hZsum] at h2
    exact h2.congr_of_eventuallyEq hsum.deriv
  · have hV : interior ({σ : ℝ | ∀ k : ℕ, k < N → IntervalIntegrable (fun t : ℝ => F σ t)
        volume (c k) (c (k + 1))} ∩ {σ : ℝ | ∀ k ∈ Finset.range N,
        DifferentiableAt ℝ (fun σ : ℝ => ∫ t in c k..c (k + 1), F σ t) σ}) ∈ 𝓝 (0 : ℝ) :=
      isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.mpr (inter_mem hint hdiff))
    filter_upwards [hV] with σ hσ
    have hsub1 : σ ∈ {σ : ℝ | ∀ k : ℕ, k < N → IntervalIntegrable (fun t : ℝ => F σ t)
        volume (c k) (c (k + 1))} := (interior_subset hσ).1
    have hsub2 : σ ∈ {σ : ℝ | ∀ k ∈ Finset.range N,
        DifferentiableAt ℝ (fun σ : ℝ => ∫ t in c k..c (k + 1), F σ t) σ} :=
      (interior_subset hσ).2
    have h1 : DifferentiableAt ℝ (fun σ : ℝ => ∑ k ∈ Finset.range N,
        ∫ t in c k..c (k + 1), F σ t) σ := DifferentiableAt.fun_sum hsub2
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_interior.mem_nhds hσ] with σ' hσ'
    have hsub1' : σ' ∈ {σ : ℝ | ∀ k : ℕ, k < N → IntervalIntegrable (fun t : ℝ => F σ t)
        volume (c k) (c (k + 1))} := (interior_subset hσ').1
    have h := intervalIntegral.sum_integral_adjacent_intervals (μ := volume)
      (f := fun t : ℝ => F σ' t) (a := c) (n := N) (fun k hk' => hsub1' k hk')
    rw [hc0, hcN] at h
    exact h.symm

/-- **The second variation of the energy of a geodesic variation of a `GExp`-ray**, *with* the
eventual differentiability of the energy (the form used by the shortening argument). -/
theorem energy_second_deriv_ray_ev (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {p : M} {ξ : TangentSpace I p} (hξ : ξ ≠ 0)
    {V : (t : ℝ) → TangentSpace I (GExp (cov := cov) hmet p (t • ξ))}
    {a b : ℝ}
    (hVs : ∀ s ∈ Icc (a - 1) (b + 1),
      SmoothAlongAt (I := I) (fun s : ℝ => GExp (cov := cov) hmet p (s • ξ)) V s)
    (hab : a < b) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ d ∈ Set.Ioc (0 : ℝ) c₀,
      (HasDerivAt (deriv (fun σ : ℝ => ∫ t in a..b, (curveSpeed (I := I)
          (fun s : ℝ => GExp (cov := cov) hmet (GExp (cov := cov) hmet p (s • ξ))
            (σ • (d • V s))) t) ^ 2))
        (2 * ∫ t in a..b, idxAlong (cov := cov)
          (fun s : ℝ => GExp (cov := cov) hmet p (s • ξ)) (fun s => d • V s)
          (covAlong cov (fun s => d • V s)) t) 0) ∧
      (∀ᶠ σ in 𝓝 (0 : ℝ), DifferentiableAt ℝ (fun σ : ℝ => ∫ t in a..b, (curveSpeed (I := I)
          (fun s : ℝ => GExp (cov := cov) hmet (GExp (cov := cov) hmet p (s • ξ))
            (σ • (d • V s))) t) ^ 2) σ) := by
  obtain ⟨N, c, c₀, hc₀pos, hc0, hcN, hmono, hspec⟩ :=
    Submission.EnergyRayCover.exists_pos_piece_second_deriv (cov := cov) hmet htor hξ hVs hab
  refine ⟨c₀, hc₀pos, fun d hd => ?_⟩
  obtain ⟨hint, hintZ, hk⟩ := hspec d hd
  exact energy_second_deriv_cover_eventually_ev (cov := cov) hc0 hcN hint hintZ hk

/-- **The shortening lemma in its local form**: a function with a *local* minimum at `0` cannot have
`f''(0) < 0` (in the sense `HasDerivAt (deriv f) c 0` with `c < 0`). -/
theorem false_of_localMin_deriv_deriv_neg {f : ℝ → ℝ} {L c : ℝ}
    (hloc : ∀ᶠ σ in 𝓝 (0 : ℝ), L ≤ f σ) (h0 : f 0 = L) (hdiff : DifferentiableAt ℝ f 0)
    (h2 : HasDerivAt (deriv f) c 0) (hc : c < 0) : False := by
  have hmin : IsLocalMin f 0 := hloc.mono (fun σ hσ => by rw [h0]; exact hσ)
  have h1 : deriv f 0 = 0 := hmin.deriv_eq_zero
  obtain ⟨δ, hδpos, hδ⟩ :=
    Commons.Analysis.Calculus.exists_lt_of_deriv_eq_zero_of_hasDerivAt_deriv_neg
      hdiff.continuousAt h1 h2 hc
  obtain ⟨ε, hεpos, hε⟩ := Metric.mem_nhds_iff.mp hloc
  have hminpos : 0 < min δ ε := lt_min hδpos hεpos
  have hlt : f (min δ ε / 2) < f 0 := hδ _ (by linarith) (by
    have h := min_le_left δ ε; linarith)
  rw [h0] at hlt
  have hge : L ≤ f (min δ ε / 2) := hε (by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    have h := min_le_right δ ε
    constructor <;> linarith)
  linarith

/-- **Distance bound by the energy, on an arbitrary interval.** -/
theorem edist_le_sqrt_mul_energy_Icc
    (hmet : IsMetricCompatible cov) {γ : ℝ → M} {a b : ℝ} (hab : a < b)
    (hγ : ContMDiffOn (modelWithCornersSelf ℝ ℝ) I 1 γ (Icc a b))
    (hspc : ContinuousOn (fun t => curveSpeed (I := I) γ t) (Icc a b)) :
    Manifold.riemannianEDist I (γ a) (γ b)
      ≤ ENNReal.ofReal (Real.sqrt ((b - a) * ∫ t in a..b, curveSpeed (I := I) γ t ^ 2)) := by
  have h1 : Manifold.riemannianEDist I (γ a) (γ b) ≤ Manifold.pathELength I γ a b :=
    Manifold.riemannianEDist_le_pathELength (x := γ a) (y := γ b) (a := a) (b := b) (γ := γ)
      hγ rfl rfl hab.le
  have hlen : Manifold.pathELength I γ a b
      = ENNReal.ofReal (∫ t in a..b, curveSpeed (I := I) γ t) := by
    refine Commons.Geometry.Manifold.pathELength_eq_ofReal_integral_of_enorm_eq_nonneg (I := I)
      (γ := γ) (a := a) (b := b) (f := fun t => curveSpeed (I := I) γ t) hab.le
      (hspc.integrableOn_Icc) (fun t _ => curveSpeed_nonneg (I := I) γ t) ?_
    intro t ht
    show ‖curveVelocity (I := I) γ t‖ₑ = ENNReal.ofReal (curveSpeed (I := I) γ t)
    rw [Submission.Minimal.enorm_eq_ofReal_norm,
      Submission.GeodesicSpeed.curveSpeed_eq_norm (I := I) γ t]
  rw [hlen] at h1
  refine h1.trans ?_
  have hint : 0 ≤ ∫ t in a..b, curveSpeed (I := I) γ t :=
    intervalIntegral.integral_nonneg hab.le (fun t _ => curveSpeed_nonneg (I := I) γ t)
  rw [ENNReal.ofReal_le_ofReal_iff (Real.sqrt_nonneg _)]
  have hcs := Commons.Analysis.Calculus.sq_intervalIntegral_le_length_mul_intervalIntegral_sq
    (f := fun t => curveSpeed (I := I) γ t) hab.le (by rwa [uIcc_of_le hab.le])
    (fun t _ => curveSpeed_nonneg (I := I) γ t)
  rw [← Real.sqrt_sq hint]
  exact Real.sqrt_le_sqrt (by simpa using hcs)

/-- **The energy of a curve joining two points at distance `b - a` is at least `b - a`** (arbitrary
interval). -/
theorem le_energy_of_edist_eq_Icc
    (hmet : IsMetricCompatible cov) {γ : ℝ → M} {a b : ℝ} (hab : a < b)
    (hγ : ContMDiffOn (modelWithCornersSelf ℝ ℝ) I 1 γ (Icc a b))
    (hspc : ContinuousOn (fun t => curveSpeed (I := I) γ t) (Icc a b))
    (hmin : Manifold.riemannianEDist I (γ a) (γ b) = ENNReal.ofReal (b - a)) :
    b - a ≤ ∫ t in a..b, curveSpeed (I := I) γ t ^ 2 := by
  have h := edist_le_sqrt_mul_energy_Icc (cov := cov) hmet hab hγ hspc
  rw [hmin] at h
  rw [ENNReal.ofReal_le_ofReal_iff (Real.sqrt_nonneg _)] at h
  have hE : 0 ≤ ∫ t in a..b, curveSpeed (I := I) γ t ^ 2 :=
    intervalIntegral.integral_nonneg hab.le
      (fun t _ => pow_nonneg (curveSpeed_nonneg (I := I) γ t) 2)
  have h2 : (b - a) ^ 2 ≤ (Real.sqrt ((b - a) * ∫ t in a..b, curveSpeed (I := I) γ t ^ 2)) ^ 2 :=
    pow_le_pow_left₀ (by linarith) h 2
  rw [Real.sq_sqrt (by positivity)] at h2
  nlinarith [hab]


/-! ## 7. The shortening argument and `σ ≤ κ` -/

/-- The `C¹`-condition is implied by `C^∞`. -/
lemma one_le_infty : (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by
  show ((1 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
  exact WithTop.coe_le_coe.mpr le_top

/-- **The speed of a `GExp`-ray is the norm of its direction** (away from the base point; the value
at the base point is not needed since integrals do not see it). -/
lemma curveSpeed_ray (hmet : IsMetricCompatible cov) (x : M) {v : TangentSpace I x}
    (hv : v ≠ 0) {s : ℝ} (hs : s ≠ 0) :
    curveSpeed (I := I) (fun r : ℝ => GExp (cov := cov) hmet x (r • v)) s = ‖v‖ :=
  Submission.LensLoop.curveSpeed_GExp_smul_ne (cov := cov) hmet x hv hs

/-- **The classical inequality `σ ≤ κ`**: a conjugate time of a ray bounds the cut time from
above. -/
theorem cutTime_le_of_isConjugateTime (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {p : M} {ξ : TangentSpace I p} (hξ1 : ‖ξ‖ = 1) {t : ℝ}
    (hconj : ConjRadius.IsConjugateTime cov (fun s : ℝ => GExp (cov := cov) hmet p (s • ξ)) t) :
    Submission.CutTime.cutTime (I := I) hmet p ξ ≤ t := by
  classical
  have hξ : ξ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hξ1
    norm_num at hξ1
  set γ : ℝ → M := fun s : ℝ => GExp (cov := cov) hmet p (s • ξ) with hγdef
  have hne : ∀ s, curveVelocity (I := I) γ s ≠ 0 := by
    intro s
    rw [hγdef]
    exact Submission.EnergyRayCover.curveVelocity_GExp_smul_ne_zero (cov := cov) hmet hξ s
  have hγ : ContMDiff 𝓘(ℝ) I ∞ γ := by
    rw [hγdef]
    exact contMDiff_GExp_smul (cov := cov) hmet p hξ
  obtain ⟨htpos, J, hJ, hJ0, hJt, hnontriv⟩ := hconj
  by_contra hle
  rw [not_le] at hle
  obtain ⟨L, hLmem, htL⟩ := exists_lt_of_lt_csSup
    (s := Submission.CutTime.minimisingSet (I := I) hmet p ξ)
    ⟨0, le_refl 0, by rw [zero_smul, GExp_zero, Manifold.riemannianEDist_self, ENNReal.ofReal_zero]⟩
    hle
  have hLmin : Manifold.riemannianEDist I p (γ L) = ENNReal.ofReal L := hLmem.2
  have hJsm : ∀ s, SmoothAlongAt (I := I) γ J s := fun s =>
    Submission.JacobiGlobal.smoothAlongAt_of_isJacobiAt (cov := cov) htor hJ
      (hγ.contMDiffOn.mono (fun u _ => trivial))
  have hzp : covAlong cov J t ≠ 0 :=
    Submission.IndexBackUnique.covAlong_ne_zero_of_isJacobiAt (cov := cov) htor hJ hγ hne htpos
      hJt hnontriv
  -- the bump parameters
  obtain ⟨η, hηpos, hηsub⟩ := Metric.mem_nhds_iff.mp
    (hγ.continuous.continuousAt.preimage_mem_nhds
      ((chartAt H (γ t)).open_source.mem_nhds (mem_chart_source H (γ t))))
  set δ : ℝ := min (min (t / 4) ((L - t) / 4)) (η / 4) with hδdef
  have hδle1 : δ ≤ t / 4 := le_trans (min_le_left _ _) (min_le_left _ _)
  have hδle2 : δ ≤ (L - t) / 4 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hδle3 : δ ≤ η / 4 := min_le_right _ _
  have hδpos : 0 < δ := by
    rw [hδdef]
    exact lt_min (lt_min (by linarith) (by linarith)) (by linarith)
  have hδt : 3 * δ < t := by linarith
  have hδL : 3 * δ < L - t := by linarith
  have hsmall : γ '' Ioo (t - 3 * δ) (t + 3 * δ) ⊆ (chartAt H (γ t)).source := by
    rintro _ ⟨u, hu, rfl⟩
    rw [Set.mem_Ioo] at hu
    exact hηsub (by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [hu.1, hu.2, hδle3, hηpos])
  -- the cut-off field
  set c : E := (trivializationAt E (TangentSpace I) (γ t)).continuousLinearMapAt ℝ (γ t)
    (-(covAlong cov J t)) with hcdef
  set W : (u : ℝ) → TangentSpace I (γ u) := shortField (I := I) γ t δ c with hWdef
  have hWt : W t = -(covAlong cov J t) := by
    rw [hWdef, hcdef, shortField_apply, bumpChi_t hδpos, one_smul]
    exact Submission.GExpFlow.frameVector_clm (I := I) (z₀ := γ t) (q := γ t)
      (by rw [extChartAt_source]; exact mem_chart_source H (γ t)) (-(covAlong cov J t))
  have hW0 : W 0 = 0 := by
    rw [hWdef]
    exact shortField_eq_zero_of_le (γ := γ) hδpos (by linarith)
  have hWL : W L = 0 := by
    rw [hWdef]
    exact shortField_eq_zero_of_ge (γ := γ) hδpos (by linarith)
  have hWs : ∀ s, SmoothAlongAt (I := I) γ W s := fun s => by
    rw [hWdef]
    exact smoothAlongAt_shortField hγ hδpos hsmall c s
  -- the two quadratic coefficients of the perturbation
  set C₁ : ℝ := ∫ u in (0 : ℝ)..t, idxAlong (cov := cov) γ W (covAlong cov W) u with hC₁def
  set C₂ : ℝ := ∫ u in t..L, idxAlong (cov := cov) γ W (covAlong cov W) u with hC₂def
  set ε : ℝ := min 1 (‖covAlong cov J t‖ ^ 2 / (|C₁ + C₂| + 1)) with hεdef
  have hεpos : 0 < ε := by
    rw [hεdef]
    exact lt_min one_pos (div_pos (by positivity) (by positivity))
  have hεle : ε ≤ ‖covAlong cov J t‖ ^ 2 / (|C₁ + C₂| + 1) := by
    rw [hεdef]; exact min_le_right _ _
  have hzp2 : 0 < ‖covAlong cov J t‖ ^ 2 := by positivity
  have hεC : ε * (C₁ + C₂) ≤ ‖covAlong cov J t‖ ^ 2 := by
    have h3 : 0 < |C₁ + C₂| + 1 := by positivity
    calc ε * (C₁ + C₂) ≤ ε * |C₁ + C₂| := mul_le_mul_of_nonneg_left (le_abs_self _) hεpos.le
      _ ≤ (‖covAlong cov J t‖ ^ 2 / (|C₁ + C₂| + 1)) * |C₁ + C₂| :=
          mul_le_mul_of_nonneg_right hεle (abs_nonneg _)
      _ = ‖covAlong cov J t‖ ^ 2 * (|C₁ + C₂| / (|C₁ + C₂| + 1)) := by ring
      _ ≤ ‖covAlong cov J t‖ ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left (by rw [div_le_one h3]; linarith) hzp2.le
      _ = ‖covAlong cov J t‖ ^ 2 := mul_one _
  -- the fields of the variation
  set U₁ : (u : ℝ) → TangentSpace I (γ u) := fun u => J u + ε • W u with hU₁def
  set U₂ : (u : ℝ) → TangentSpace I (γ u) := fun u => ε • W u with hU₂def
  have hU₁sAll : ∀ s, SmoothAlongAt (I := I) γ U₁ s := fun s => by
    rw [hU₁def]
    exact SmoothAlongAt_add (hJsm s) (Submission.EnergyRay.SmoothAlongAt_smul (I := I) ε (hWs s))
  have hU₂sAll : ∀ s, SmoothAlongAt (I := I) γ U₂ s := fun s => by
    rw [hU₂def]
    exact Submission.EnergyRay.SmoothAlongAt_smul (I := I) ε (hWs s)
  have hU₁t : U₁ t = U₂ t := by
    simp only [hU₁def, hU₂def]
    rw [hJt, zero_add]
  -- the common scale
  obtain ⟨c₁, hc₁pos, h₁⟩ :=
    energy_second_deriv_ray_ev (cov := cov) hmet htor hξ
      (fun s _ => hU₁sAll s) (a := 0) (b := t) htpos
  obtain ⟨c₂, hc₂pos, h₂⟩ :=
    energy_second_deriv_ray_ev (cov := cov) hmet htor hξ
      (fun s _ => hU₂sAll s) (a := t) (b := L) htL
  obtain ⟨ca, hcapos, hfa⟩ :=
    Submission.EnergyRaySmooth.contMDiffOn_ray_family (cov := cov) hmet htor hξ
      (fun s _ => hU₁sAll s) (a := 0) (b := t) htpos
  obtain ⟨cb, hcbpos, hfb⟩ :=
    Submission.EnergyRaySmooth.contMDiffOn_ray_family (cov := cov) hmet htor hξ
      (fun s _ => hU₂sAll s) (a := t) (b := L) htL
  set d : ℝ := min (min c₁ c₂) (min ca cb) / 2 with hddef
  have hdcm : 0 < min (min c₁ c₂) (min ca cb) := lt_min (lt_min hc₁pos hc₂pos) (lt_min hcapos hcbpos)
  have hdpos : 0 < d := by rw [hddef]; exact div_pos hdcm two_pos
  have hdle : d ≤ min (min c₁ c₂) (min ca cb) := by rw [hddef]; linarith
  have hd₁ : d ∈ Set.Ioc (0 : ℝ) c₁ := ⟨hdpos, le_trans hdle (le_trans (min_le_left _ _) (min_le_left _ _))⟩
  have hd₂ : d ∈ Set.Ioc (0 : ℝ) c₂ := ⟨hdpos, le_trans hdle (le_trans (min_le_left _ _) (min_le_right _ _))⟩
  have hda : d ∈ Set.Ioc (0 : ℝ) ca := ⟨hdpos, le_trans hdle (le_trans (min_le_right _ _) (min_le_left _ _))⟩
  have hdb : d ∈ Set.Ioc (0 : ℝ) cb := ⟨hdpos, le_trans hdle (le_trans (min_le_right _ _) (min_le_right _ _))⟩
  -- the energies
  set E₁ : ℝ → ℝ := fun σ : ℝ => ∫ u in (0 : ℝ)..t, (curveSpeed (I := I)
      (fun s : ℝ => GExp (cov := cov) hmet (γ s) (σ • (d • U₁ s))) u) ^ 2 with hE₁def
  set E₂ : ℝ → ℝ := fun σ : ℝ => ∫ u in t..L, (curveSpeed (I := I)
      (fun s : ℝ => GExp (cov := cov) hmet (γ s) (σ • (d • U₂ s))) u) ^ 2 with hE₂def
  set E : ℝ → ℝ := fun σ : ℝ => E₁ σ + E₂ σ with hEdef
  have hE₁ : HasDerivAt (deriv E₁)
      (2 * ∫ u in (0 : ℝ)..t, idxAlong (cov := cov) γ (fun s => d • U₁ s)
        (covAlong cov (fun s => d • U₁ s)) u) 0 := (h₁ d hd₁).1
  have hE₁ev : ∀ᶠ σ in 𝓝 (0 : ℝ), DifferentiableAt ℝ E₁ σ := (h₁ d hd₁).2
  have hE₂ : HasDerivAt (deriv E₂)
      (2 * ∫ u in t..L, idxAlong (cov := cov) γ (fun s => d • U₂ s)
        (covAlong cov (fun s => d • U₂ s)) u) 0 := (h₂ d hd₂).1
  have hE₂ev : ∀ᶠ σ in 𝓝 (0 : ℝ), DifferentiableAt ℝ E₂ σ := (h₂ d hd₂).2
  have hE : HasDerivAt (deriv E)
      ((2 * ∫ u in (0 : ℝ)..t, idxAlong (cov := cov) γ (fun s => d • U₁ s)
          (covAlong cov (fun s => d • U₁ s)) u)
        + (2 * ∫ u in t..L, idxAlong (cov := cov) γ (fun s => d • U₂ s)
          (covAlong cov (fun s => d • U₂ s)) u)) 0 := by
    rw [hEdef]
    exact Commons.Analysis.Calculus.hasDerivAt_deriv_add hE₁ hE₂ hE₁ev hE₂ev
  -- the value of the second derivative
  have hA : ∀ s, SmoothAlongAt (I := I) γ (fun u => J u + ε • W u) s := by
    intro s; rw [← hU₁def]; exact hU₁sAll s
  have hcovU₁ : covAlong cov U₁ = fun u => covAlong cov J u + ε • covAlong cov W u := by
    funext u
    rw [hU₁def]
    exact covAlong_add_smul (cov := cov) htor ε (hJsm u) (hWs u)
  have hI₁ : (∫ u in (0 : ℝ)..t, idxAlong (cov := cov) γ U₁ (covAlong cov U₁) u)
      = -2 * ε * ‖covAlong cov J t‖ ^ 2 + ε ^ 2 * C₁ := by
    have hJint : IntervalIntegrable (fun u => idxAlong (cov := cov) γ J (covAlong cov J) u)
        volume (0 : ℝ) t :=
      intervalIntegrable_idxAlong_of_smooth (cov := cov) htor htpos.le hγ hne hJsm
    have hWint : IntervalIntegrable (fun u => idxAlong (cov := cov) γ W (covAlong cov W) u)
        volume (0 : ℝ) t :=
      intervalIntegrable_idxAlong_of_smooth (cov := cov) htor htpos.le hγ hne hWs
    have hbilint := intervalIntegrable_bilAlong_of_smooth (cov := cov) hmet htor htpos.le hγ hne
      hJsm hWs
    have h₁' : (∫ u in (0 : ℝ)..t, idxAlong (cov := cov) γ U₁ (covAlong cov U₁) u)
        = ∫ u in (0 : ℝ)..t, idxAlong (cov := cov) γ J (covAlong cov J) u
          + 2 * ε * bilAlong (cov := cov) γ J W (covAlong cov J) (covAlong cov W) u
          + ε ^ 2 * idxAlong (cov := cov) γ W (covAlong cov W) u := by
      refine intervalIntegral.integral_congr (fun u _ => ?_)
      rw [hcovU₁]
      exact idxAlong_add_smul (cov := cov) hmet htor γ J W (covAlong cov J) (covAlong cov W) ε u
    have hJval : (∫ u in (0 : ℝ)..t, idxAlong (cov := cov) γ J (covAlong cov J) u) = 0 :=
      Submission.IndexFTC.integral_idxAlong_eq_zero (cov := cov) hmet htor hJ hγ hne htpos.le
        hJ0 hJt
    have hbilval : (∫ u in (0 : ℝ)..t,
          bilAlong (cov := cov) γ J W (covAlong cov J) (covAlong cov W) u)
        = -‖covAlong cov J t‖ ^ 2 := by
      rw [Submission.IndexFTC.integral_bilAlong_eq_sub (cov := cov) hmet htor hJ hγ hne hWs
        htpos.le]
      rw [hWt, hW0, inner_neg_right, inner_zero_right, sub_zero, real_inner_self_eq_norm_sq]
    rw [h₁', intervalIntegral.integral_add (hJint.add (hbilint.const_mul (2 * ε)))
        (hWint.const_mul (ε ^ 2)),
      intervalIntegral.integral_add hJint (hbilint.const_mul (2 * ε)),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      hJval, hbilval, ← hC₁def]
    ring
  have hI₂ : (∫ u in t..L, idxAlong (cov := cov) γ (fun s => d • U₂ s)
        (covAlong cov (fun s => d • U₂ s)) u) = d ^ 2 * (ε ^ 2 * C₂) := by
    have hstep : (∫ u in t..L, idxAlong (cov := cov) γ (fun s => d • U₂ s)
          (covAlong cov (fun s => d • U₂ s)) u)
        = ∫ u in t..L, d ^ 2 * idxAlong (cov := cov) γ U₂ (covAlong cov U₂) u := by
      refine intervalIntegral.integral_congr (fun u _ => ?_)
      have hc : covAlong cov (fun s : ℝ => d • U₂ s) = fun s => d • covAlong cov U₂ s := by
        funext v; exact Submission.IndexScale.covAlong_smul htor γ U₂ d v
      rw [hc]
      exact Submission.IndexScale.idxAlong_smul (cov := cov) hmet htor γ U₂ (covAlong cov U₂) d u
    have hstep2 : (∫ u in t..L, idxAlong (cov := cov) γ U₂ (covAlong cov U₂) u)
        = ε ^ 2 * C₂ := by
      have h₂' : (∫ u in t..L, idxAlong (cov := cov) γ U₂ (covAlong cov U₂) u)
          = ∫ u in t..L, ε ^ 2 * idxAlong (cov := cov) γ W (covAlong cov W) u := by
        refine intervalIntegral.integral_congr (fun u _ => ?_)
        have hc : covAlong cov (fun s : ℝ => ε • W s) = fun s => ε • covAlong cov W s := by
          funext v; exact Submission.IndexScale.covAlong_smul htor γ W ε v
        rw [hU₂def, hc]
        exact Submission.IndexScale.idxAlong_smul (cov := cov) hmet htor γ W (covAlong cov W) ε u
      rw [h₂', intervalIntegral.integral_const_mul, hC₂def]
    rw [hstep, intervalIntegral.integral_const_mul, hstep2]
  have hI₁' : (∫ u in (0 : ℝ)..t, idxAlong (cov := cov) γ (fun s => d • U₁ s)
        (covAlong cov (fun s => d • U₁ s)) u)
      = d ^ 2 * (-2 * ε * ‖covAlong cov J t‖ ^ 2 + ε ^ 2 * C₁) := by
    have hstep : (∫ u in (0 : ℝ)..t, idxAlong (cov := cov) γ (fun s => d • U₁ s)
          (covAlong cov (fun s => d • U₁ s)) u)
        = ∫ u in (0 : ℝ)..t, d ^ 2 * idxAlong (cov := cov) γ U₁ (covAlong cov U₁) u := by
      refine intervalIntegral.integral_congr (fun u _ => ?_)
      have hc : covAlong cov (fun s : ℝ => d • U₁ s) = fun s => d • covAlong cov U₁ s := by
        funext v; exact Submission.IndexScale.covAlong_smul htor γ U₁ d v
      rw [hc]
      exact Submission.IndexScale.idxAlong_smul (cov := cov) hmet htor γ U₁ (covAlong cov U₁) d u
    rw [hstep, intervalIntegral.integral_const_mul, hI₁]
  have hneg : (2 * (∫ u in (0 : ℝ)..t, idxAlong (cov := cov) γ (fun s => d • U₁ s)
        (covAlong cov (fun s => d • U₁ s)) u)
      + 2 * (∫ u in t..L, idxAlong (cov := cov) γ (fun s => d • U₂ s)
        (covAlong cov (fun s => d • U₂ s)) u)) < 0 := by
    rw [hI₁', hI₂]
    have hpos : 0 < 2 * d ^ 2 * ε :=
      mul_pos (mul_pos two_pos (pow_pos hdpos 2)) hεpos
    have hneg' : ε * (C₁ + C₂) - 2 * ‖covAlong cov J t‖ ^ 2 < 0 := by linarith
    have heq : 2 * (d ^ 2 * (-2 * ε * ‖covAlong cov J t‖ ^ 2 + ε ^ 2 * C₁))
        + 2 * (d ^ 2 * (ε ^ 2 * C₂))
        = 2 * d ^ 2 * ε * (ε * (C₁ + C₂) - 2 * ‖covAlong cov J t‖ ^ 2) := by ring
    rw [heq]
    exact mul_neg_of_pos_of_neg hpos hneg'
  -- the lower bound
  have hE0 : E 0 = L := by
    have hcongr : ∀ (V : (u : ℝ) → TangentSpace I (γ u)) (a b : ℝ), 0 ≤ a → a ≤ b →
        (fun σ : ℝ => ∫ u in a..b, (curveSpeed (I := I)
          (fun s : ℝ => GExp (cov := cov) hmet (γ s) (σ • (d • V s))) u) ^ 2) 0
          = ∫ u in a..b, (1 : ℝ) ^ 2 := by
      intro V a b ha hab
      have hmain : (∫ u in a..b, (curveSpeed (I := I)
          (fun s : ℝ => GExp (cov := cov) hmet (γ s) ((0 : ℝ) • (d • V s))) u) ^ 2)
          = ∫ u in a..b, (1 : ℝ) ^ 2 :=
        intervalIntegral.integral_congr_ae (μ := volume) (by
          filter_upwards with u hu
          rw [Set.uIoc_of_le hab] at hu
          have hu0 : u ≠ 0 := ne_of_gt (lt_of_le_of_lt ha hu.1)
          have hcurve : (fun s : ℝ => GExp (cov := cov) hmet (γ s) ((0 : ℝ) • (d • V s))) = γ := by
            funext s
            rw [zero_smul]
            exact GExp_zero hmet (γ s)
          rw [hcurve, hγdef]
          rw [curveSpeed_ray (cov := cov) hmet p hξ hu0, hξ1])
      simp only []
      exact hmain
    have h1 : E₁ 0 = t := by
      rw [hE₁def]
      rw [hcongr U₁ 0 t le_rfl htpos.le, intervalIntegral.integral_const]
      ring
    have h2 : E₂ 0 = L - t := by
      rw [hE₂def]
      rw [hcongr U₂ t L htpos.le htL.le, intervalIntegral.integral_const]
      ring
    rw [hEdef]
    simp only []
    rw [h1, h2]
    ring
  have hminL : ∀ᶠ σ in 𝓝 (0 : ℝ), L ≤ E σ := by
    have hfam₁ := hfa d hda
    have hfam₂ := hfb d hdb
    filter_upwards [hfam₁, hfam₂] with σ hσ₁ hσ₂
    set Ψ₁ : ℝ → M := fun u => GExp (cov := cov) hmet (γ u) (σ • (d • U₁ u)) with hΨ₁def
    set Ψ₂ : ℝ → M := fun u => GExp (cov := cov) hmet (γ u) (σ • (d • U₂ u)) with hΨ₂def
    have hb₁ : Manifold.riemannianEDist I (Ψ₁ 0) (Ψ₁ t)
        ≤ ENNReal.ofReal (Real.sqrt (t * E₁ σ)) := by
      have h := edist_le_sqrt_mul_energy_Icc (cov := cov) hmet (γ := Ψ₁) (a := 0) (b := t)
        htpos (hσ₁.1.of_le one_le_infty) hσ₁.2
      simpa [hΨ₁def, hE₁def] using h
    have hb₂ : Manifold.riemannianEDist I (Ψ₂ t) (Ψ₂ L)
        ≤ ENNReal.ofReal (Real.sqrt ((L - t) * E₂ σ)) := by
      have h := edist_le_sqrt_mul_energy_Icc (cov := cov) hmet (γ := Ψ₂) (a := t) (b := L)
        htL (hσ₂.1.of_le one_le_infty) hσ₂.2
      simpa [hΨ₂def, hE₂def] using h
    have h0₁ : Ψ₁ 0 = p := by
      change GExp (cov := cov) hmet (γ 0) (σ • (d • U₁ 0)) = p
      have hz : σ • (d • U₁ 0) = (0 : TangentSpace I (γ 0)) := by
        change σ • (d • (J 0 + ε • W 0)) = 0
        rw [hJ0, hW0]
        simp
      rw [hz, GExp_zero, hγdef]
      simp only []
      rw [zero_smul, GExp_zero]
    have hL₂ : Ψ₂ L = γ L := by
      change GExp (cov := cov) hmet (γ L) (σ • (d • U₂ L)) = γ L
      have hz : σ • (d • U₂ L) = (0 : TangentSpace I (γ L)) := by
        change σ • (d • (ε • W L)) = 0
        rw [hWL]
        simp
      rw [hz, GExp_zero]
    have hglue : Ψ₁ t = Ψ₂ t := by
      simp only [hΨ₁def, hΨ₂def]
      rw [hU₁t]
    have hb₁' : Manifold.riemannianEDist I (Ψ₁ 0) (Ψ₂ t) ≤ ENNReal.ofReal (Real.sqrt (t * E₁ σ)) := by
      simpa only [← hglue] using hb₁
    have htri : Manifold.riemannianEDist I p (γ L) ≤ ENNReal.ofReal (Real.sqrt (t * E₁ σ))
        + ENNReal.ofReal (Real.sqrt ((L - t) * E₂ σ)) := by
      calc Manifold.riemannianEDist I p (γ L)
          = Manifold.riemannianEDist I (Ψ₁ 0) (Ψ₂ L) := by rw [h0₁, hL₂]
        _ ≤ Manifold.riemannianEDist I (Ψ₁ 0) (Ψ₂ t) + Manifold.riemannianEDist I (Ψ₂ t) (Ψ₂ L) :=
            Manifold.riemannianEDist_triangle (I := I) (x := Ψ₁ 0) (y := Ψ₂ t) (z := Ψ₂ L)
        _ ≤ ENNReal.ofReal (Real.sqrt (t * E₁ σ)) + ENNReal.ofReal (Real.sqrt ((L - t) * E₂ σ)) :=
            add_le_add hb₁' hb₂
    rw [hLmin, ← ENNReal.ofReal_add (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)] at htri
    have hreal : L ≤ Real.sqrt (t * E₁ σ) + Real.sqrt ((L - t) * E₂ σ) :=
      (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp htri
    have hE₁σ : 0 ≤ E₁ σ := by
      rw [hE₁def]
      exact intervalIntegral.integral_nonneg htpos.le (fun u _ => by positivity)
    have hE₂σ : 0 ≤ E₂ σ := by
      rw [hE₂def]
      exact intervalIntegral.integral_nonneg htL.le (fun u _ => by positivity)
    have hcs := Commons.Analysis.Calculus.sq_sqrt_mul_add_sqrt_mul_le (a := t) (b := L - t)
      (c := E₁ σ) (d := E₂ σ) htpos.le (by linarith) hE₁σ hE₂σ
    have hsqrt : Real.sqrt (t * E₁ σ) + Real.sqrt ((L - t) * E₂ σ)
        = Real.sqrt t * Real.sqrt (E₁ σ) + Real.sqrt (L - t) * Real.sqrt (E₂ σ) := by
      rw [Real.sqrt_mul htpos.le, Real.sqrt_mul (by linarith : (0 : ℝ) ≤ L - t)]
    rw [hsqrt] at hreal
    have h2 : L ^ 2 ≤ (Real.sqrt t * Real.sqrt (E₁ σ)
        + Real.sqrt (L - t) * Real.sqrt (E₂ σ)) ^ 2 :=
      pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ L) hreal 2
    have h3 : (Real.sqrt t * Real.sqrt (E₁ σ) + Real.sqrt (L - t) * Real.sqrt (E₂ σ)) ^ 2
        ≤ (t + (L - t)) * (E₁ σ + E₂ σ) := hcs
    rw [hEdef]
    nlinarith [h2, h3, htpos]
  exact false_of_localMin_deriv_deriv_neg hminL hE0
    (hE₁ev.self_of_nhds.add hE₂ev.self_of_nhds) hE hneg


/-- **The classical inequality `σ ≤ κ`**: no conjugate point lies strictly inside the tangential
segment domain, in the packaged form used by the library
(`Submission.ConjCut.CutConjInequality`). -/
theorem cutConjInequality (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) :
    Submission.ConjCut.CutConjInequality (I := I) hmet htor :=
  fun p ξ hξ t ht => cutTime_le_of_isConjugateTime (cov := cov) hmet htor hξ ht


/-- **Invertibility of the differential of `GExp p` on the tangential segment domain**, with *no*
remaining hypotheses: `σ ≤ κ` (`cutConjInequality`) together with the κ-side bridge
(`SingularConj.singularImpConjTime_of_torsion_free`).  This is the first paragraph of Xu's proof of
the Klingenberg lemma. -/
theorem isInvertible_mfderiv_of_mem_segmentDomain (hmet : IsMetricCompatible cov)
    (htor : cov.torsion = 0) {p : M} {v : TangentSpace I p}
    (hv : v ∈ Submission.SegmentDomain.segmentDomain hmet p) (hv0 : v ≠ 0) :
    (mfderiv 𝓘(ℝ, E) I
      (fun u : E => GExp (cov := cov) hmet p (show TangentSpace I p from u))
      (show E from v)).IsInvertible :=
  Submission.SingularConj.isInvertible_mfderiv_of_mem_segmentDomain_of_cutConj (I := I) hmet htor
    (cutConjInequality (cov := cov) hmet htor) hv hv0


end

end Submission.ConjEnergy
