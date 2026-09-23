import Mathlib
import Submission.Work.OddBound.IndexPair
import Submission.ParallelRoom
import Submission.Variation

/-!
# The strong index bound (no negative-definite plane) from a parallel normal pair

`Work.OddBound.DirichletIndexNotLeOne cov γ L` is the negation of the loop-space minimax conclusion
`Work.OddBound.DirichletIndexLeOne`: the existence of two smooth Dirichlet fields along `γ` (vanishing
at `0` and `L`) spanning a two-dimensional space on which the index form is *negative definite*.

This module proves that such a plane exists as soon as the curvature is bounded below by `δ + ε`
(`ε > 0`) on the planes `span{X_j, γ'}` of a parallel normal pair, provided `π / √(δ+ε) < L`.  The
plane is spanned by the two Dirichlet fields `V_j = sin (π s / L) • X_j`; for a non-trivial linear
combination `Z = a V₁ + b W₁ = sin (π s / L) • (a X₁ + b X₂)` one has, pointwise,

`idxAlong γ Z (∇Z) = f'² ‖a X₁ + b X₂‖² - f² ⟪R(aX₁+bX₂, γ')γ', aX₁+bX₂⟫`,

where `f = sin (π s / L)`.  Because `X₁, X₂` are parallel, both `‖a X₁ + b X₂‖² = A` (a positive
constant, by the independence of `X₁, X₂`) and the curvature pairing is `≥ (δ+ε) A`.  Hence

`∫₀^L idxAlong γ Z (∇Z) ≤ A (π²/(2L) - (δ+ε) L/2) < 0`

whenever `π² < (δ+ε) L²`.

The constancy of `‖a X₁ + b X₂‖²` is the only place metric compatibility (`IsMetricCompatible`) and
`cov.torsion = 0` are used for this part of the argument: a parallel field has constant norm and two
parallel fields have constant inner product (`Work.OddBound.strongIndex.inner_const_Icc_of_parallel`,
a closed-interval form of `Submission.ParallelRoom.isConst_inner_of_parallel`).
-/

namespace Work.OddBound.strongIndex

open scoped ContDiff Manifold
open Bundle
open ContDiff
open Set
open MeasureTheory
open Filter
open scoped Interval
open scoped Topology
open Submission.JacobiGlobal (SmoothAlongAt covAlong)
open Submission.IndexIntrinsic (idxAlong)
open Submission.CurvatureVec (curvVec curvVec_smul_left)

/-! ## 0. Elementary algebra -/

/-- Parallelogram expansion for a linear combination of two unit vectors. -/
lemma norm_add_smul_smul_sq {F : Type*} [SeminormedAddCommGroup F] [InnerProductSpace ℝ F]
    (x₁ x₂ : F) (a b : ℝ) (h₁ : ‖x₁‖ = 1) (h₂ : ‖x₂‖ = 1) :
    ‖a • x₁ + b • x₂‖ ^ 2 = a ^ 2 + b ^ 2 + 2 * a * b * inner ℝ x₁ x₂ := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
  have h11 : inner ℝ x₁ x₁ = 1 := by rw [real_inner_self_eq_norm_sq, h₁, one_pow]
  have h22 : inner ℝ x₂ x₂ = 1 := by rw [real_inner_self_eq_norm_sq, h₂, one_pow]
  have h21 : inner ℝ x₂ x₁ = inner ℝ x₁ x₂ := real_inner_comm x₁ x₂
  rw [h11, h22, h21]
  ring

/-- Scalar bookkeeping: `a • (s • x₁) + b • (s • x₂) = s • (a • x₁ + b • x₂)`. -/
lemma smul_smul_add_smul_smul {F : Type*} [AddCommMonoid F] [Module ℝ F]
    (x₁ x₂ : F) (a b s : ℝ) :
    a • (s • x₁) + b • (s • x₂) = s • (a • x₁ + b • x₂) := by
  rw [smul_add, smul_smul, smul_smul, smul_smul, smul_smul, mul_comm a s, mul_comm b s]

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [I.Boundaryless] [Nontrivial E] [CompactSpace M]
  {cov : CovariantDerivative I E (TangentSpace I (M := M))}
  [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]

/-! ## 1. Linear combinations of fields along a curve -/

/-- A linear combination of two fields smooth along `γ` is smooth along `γ`. -/
lemma smoothAlongAt_smul_add {γ : ℝ → M} {X₁ X₂ : (t : ℝ) → TangentSpace I (γ t)} {a b t : ℝ}
    (h₁ : Submission.JacobiGlobal.SmoothAlongAt (I := I) γ X₁ t)
    (h₂ : Submission.JacobiGlobal.SmoothAlongAt (I := I) γ X₂ t) :
    Submission.JacobiGlobal.SmoothAlongAt (I := I) γ (fun s => a • X₁ s + b • X₂ s) t := by
  have ha := Submission.EnergyRay.SmoothAlongAt_smul (I := I) a h₁
  have hb := Submission.EnergyRay.SmoothAlongAt_smul (I := I) b h₂
  simpa only [] using Submission.ConjEnergy.SmoothAlongAt_add (I := I) ha hb

/-- The covariant derivative of a linear combination of two fields. -/
lemma covAlong_smul_add (htor : cov.torsion = 0) {γ : ℝ → M}
    {X₁ X₂ : (t : ℝ) → TangentSpace I (γ t)} {a b t : ℝ}
    (h₁ : Submission.JacobiGlobal.SmoothAlongAt (I := I) γ X₁ t)
    (h₂ : Submission.JacobiGlobal.SmoothAlongAt (I := I) γ X₂ t) :
    Submission.JacobiGlobal.covAlong cov (fun s => a • X₁ s + b • X₂ s) t
      = a • Submission.JacobiGlobal.covAlong cov X₁ t
        + b • Submission.JacobiGlobal.covAlong cov X₂ t := by
  have ha := Submission.EnergyRay.SmoothAlongAt_smul (I := I) a h₁
  have hb := Submission.EnergyRay.SmoothAlongAt_smul (I := I) b h₂
  have h := Submission.ConjEnergy.covAlong_add (cov := cov) htor ha hb
  rw [Submission.IndexScale.covAlong_smul (cov := cov) htor γ X₁ a t,
      Submission.IndexScale.covAlong_smul (cov := cov) htor γ X₂ b t] at h
  simpa only [] using h

/-- The curvature pairing of a rescaled vector: `⟪R(c u, v)v, c u⟫ = c² ⟪R(u,v)v, u⟫`. -/
lemma inner_curvVec_smul_smul (x : M) (c : ℝ) (u v : TangentSpace I x) :
    inner ℝ (curvVec cov x (c • u) v v) (c • u)
      = c ^ 2 * inner ℝ (curvVec cov x u v v) u := by
  rw [curvVec_smul_left (cov := cov) (hcov := inferInstance), real_inner_smul_left,
    real_inner_smul_right]
  ring

/-! ## 2. Constancy of the inner product of two parallel fields on `[0, L]` -/

/-- **Two parallel fields along a curve have constant inner product on `[0, L]`**, computed from the
left endpoint.  This is `Submission.ParallelRoom.isConst_inner_of_parallel` with the base point moved
to the endpoint `0` and the hypothesis interval widened to the closed `[0, L]` (the derivative
formula holds at every point of `[0, L]`, and the fundamental theorem of calculus is applied on
`[0, t]`). -/
lemma inner_const_Icc_of_parallel
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov)
    (htor : cov.torsion = 0) {γ : ℝ → M} {L : ℝ} (hL : 0 < L)
    (hγ1 : ∀ t ∈ Icc (0 : ℝ) L, ContMDiffOn 𝓘(ℝ) I ∞ γ (Ioo (t - 1) (t + 1)))
    (hne : ∀ t ∈ Icc (0 : ℝ) L, Submission.Geodesic.curveVelocity (I := I) γ t ≠ 0)
    {U W : (t : ℝ) → TangentSpace I (γ t)}
    (hU : ∀ t ∈ Icc (0 : ℝ) L, Submission.JacobiGlobal.SmoothAlongAt (I := I) γ U t)
    (hW : ∀ t ∈ Icc (0 : ℝ) L, Submission.JacobiGlobal.SmoothAlongAt (I := I) γ W t)
    (hUp : ∀ t ∈ Icc (0 : ℝ) L, Submission.JacobiGlobal.covAlong cov U t = 0)
    (hWp : ∀ t ∈ Icc (0 : ℝ) L, Submission.JacobiGlobal.covAlong cov W t = 0) :
    ∀ t ∈ Icc (0 : ℝ) L,
      inner ℝ (U t) (W t) = inner ℝ (U 0) (W 0) := by
  have hderiv : ∀ t ∈ Icc (0 : ℝ) L,
      HasDerivAt (fun s => inner ℝ (U s) (W s)) 0 t := by
    intro t ht
    obtain ⟨𝒱, h𝒱sm, h𝒱ev⟩ :=
      Submission.JacobiGlobal.exists_section_of_smoothAlongAt (hγ1 t ht) (hne t ht) (hU t ht)
    obtain ⟨𝒲, h𝒲sm, h𝒲ev⟩ :=
      Submission.JacobiGlobal.exists_section_of_smoothAlongAt (hγ1 t ht) (hne t ht) (hW t ht)
    have hγmd : MDifferentiableAt 𝓘(ℝ) I γ t :=
      ((hγ1 t ht).contMDiffAt (isOpen_Ioo.mem_nhds ⟨by linarith [ht.1], by linarith [ht.2]⟩)).mdifferentiableAt
        (by simp)
    have h1 := Submission.Variation.hasDerivAt_inner_sections (I := I) cov hmet h𝒱sm h𝒲sm hγmd
    have hev : (fun s => inner ℝ (𝒱 (γ s)) (𝒲 (γ s))) =ᶠ[𝓝 t]
        (fun s => inner ℝ (U s) (W s)) := by
      filter_upwards [h𝒱ev, h𝒲ev] with s h1 h2
      rw [h1, h2]
    refine (h1.congr_of_eventuallyEq hev.symm).congr_deriv ?_
    rw [← Submission.JacobiGlobal.covAlong_eq_cov (cov := cov) htor (hγ1 t ht) (hne t ht)
          (hU t ht) h𝒱sm h𝒱ev,
      ← Submission.JacobiGlobal.covAlong_eq_cov (cov := cov) htor (hγ1 t ht) (hne t ht)
          (hW t ht) h𝒲sm h𝒲ev,
      hUp t ht, hWp t ht, inner_zero_left, inner_zero_right, add_zero]
  intro t ht
  rcases eq_or_lt_of_le ht.1 with h0 | h0
  · rw [← h0]
  · have hcont : ContinuousOn (fun s => inner ℝ (U s) (W s)) (Icc (0 : ℝ) t) :=
      HasDerivAt.continuousOn (fun s hs => hderiv s ⟨hs.1, le_trans hs.2 ht.2⟩)
    have hder : ∀ s ∈ Ioo (0 : ℝ) t,
        HasDerivAt (fun s => inner ℝ (U s) (W s)) ((fun _ : ℝ => (0 : ℝ)) s) s :=
      fun s hs => hderiv s ⟨hs.1.le, le_trans hs.2.le ht.2⟩
    have hkey := Commons.Analysis.Calculus.integral_eq_sub_of_hasDerivAt_of_continuousOn_Icc
      (F := fun s => inner ℝ (U s) (W s)) (g := fun _ : ℝ => (0 : ℝ)) h0.le hcont
      continuousOn_const hder
    rw [intervalIntegral.integral_zero] at hkey
    linarith

/-! ## 3. The curvature lower bound for a normal vector -/

/-- If the curvature on orthonormal pairs is `≥ δ + ε` and `Y t` is a non-zero vector orthogonal to
the unit velocity of `γ`, then the curvature pairing of `Y t` is at least `(δ+ε) ‖Y t‖²`. -/
lemma curvVec_inner_lower_of_ne {γ : ℝ → M} {L δ ε : ℝ}
    (hcurv : ∀ t ∈ Icc (0 : ℝ) L, ∀ u v : TangentSpace I (γ t), ‖u‖ = 1 → ‖v‖ = 1 →
      inner ℝ u v = 0 → δ + ε ≤ inner ℝ (curvVec cov (γ t) u v v) u)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) L) {Y : (t : ℝ) → TangentSpace I (γ t)}
    (hYne : Y t ≠ 0) (hv1 : ‖Submission.Geodesic.curveVelocity (I := I) γ t‖ = 1)
    (hYorth : inner ℝ (Y t) (Submission.Geodesic.curveVelocity (I := I) γ t) = 0) :
    (δ + ε) * ‖Y t‖ ^ 2
      ≤ inner ℝ (curvVec cov (γ t) (Y t) (Submission.Geodesic.curveVelocity (I := I) γ t)
          (Submission.Geodesic.curveVelocity (I := I) γ t)) (Y t) := by
  have hpos : 0 < ‖Y t‖ := norm_pos_iff.mpr hYne
  have hu1 : ‖(‖Y t‖)⁻¹ • Y t‖ = 1 := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity), inv_mul_cancel₀ (ne_of_gt hpos)]
  have huo : inner ℝ ((‖Y t‖)⁻¹ • Y t) (Submission.Geodesic.curveVelocity (I := I) γ t) = 0 := by
    rw [real_inner_smul_left, hYorth, mul_zero]
  have hsec := hcurv t ht ((‖Y t‖)⁻¹ • Y t) (Submission.Geodesic.curveVelocity (I := I) γ t)
    hu1 hv1 huo
  have hYU : Y t = ‖Y t‖ • ((‖Y t‖)⁻¹ • Y t) := by
    rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hpos), one_smul]
  have hsm := inner_curvVec_smul_smul (I := I) (cov := cov) (x := γ t) (c := ‖Y t‖)
    (u := (‖Y t‖)⁻¹ • Y t) (v := Submission.Geodesic.curveVelocity (I := I) γ t)
  rw [← hYU] at hsm
  rw [hsm]
  nlinarith [hsec, hpos]

/-! ## 4. The index integral of the Dirichlet field of a parallel field -/

/-- **The Dirichlet-index computation.**  Let `Y` be a field along a curve `γ` with speed one on
`[0, L]`, smooth along `γ` on `[-1, L+1]`, parallel and orthogonal to `γ'` on `[0, L]`, and with
constant squared norm on `[0, L]` (and `Y 0 ≠ 0`).  If the curvature on orthonormal pairs is at least
`δ + ε` (with `π < √(δ+ε) L`, which in particular forces `δ + ε > 0`), then the Dirichlet field
`sin (π s / L) • Y` has *negative* index integral.

The hypothesis is stated as `π < √(δ+ε) · L` rather than `π / √(δ+ε) < L` because the two are
equivalent only when `√(δ+ε) > 0`; the form used here already encodes `δ + ε > 0`, which is what the
computation `π² < (δ+ε) L²` needs. -/
theorem integral_idxAlong_sin_smul_neg
    (htor : cov.torsion = 0)
    {γ : ℝ → M} (hγsm : ContMDiffOn 𝓘(ℝ) I ∞ γ Set.univ)
    (hne : ∀ t : ℝ, Submission.Geodesic.curveVelocity (I := I) γ t ≠ 0)
    {L δ ε : ℝ} (hL : 0 < L)
    (hspeed : ∀ t ∈ Icc (0 : ℝ) L, Submission.Length.curveSpeed (I := I) γ t = 1)
    (hε : 0 < ε) (hπ : Real.pi < Real.sqrt (δ + ε) * L)
    (hcurv : ∀ t ∈ Icc (0 : ℝ) L, ∀ u v : TangentSpace I (γ t), ‖u‖ = 1 → ‖v‖ = 1 →
      inner ℝ u v = 0 → δ + ε ≤ inner ℝ (curvVec cov (γ t) u v v) u)
    {Y : (t : ℝ) → TangentSpace I (γ t)}
    (hYsm : ∀ t ∈ Icc (-1 : ℝ) (L + 1), Submission.JacobiGlobal.SmoothAlongAt (I := I) γ Y t)
    (hYpar : ∀ t ∈ Icc (0 : ℝ) L, Submission.JacobiGlobal.covAlong cov Y t = 0)
    (hYnrm : ∀ t ∈ Icc (0 : ℝ) L, ‖Y t‖ ^ 2 = ‖Y 0‖ ^ 2)
    (hY0 : Y 0 ≠ 0)
    (hYorth : ∀ t ∈ Icc (0 : ℝ) L,
      inner ℝ (Y t) (Submission.Geodesic.curveVelocity (I := I) γ t) = 0) :
    (∫ t in (0 : ℝ)..L, idxAlong (cov := cov) γ
        (fun s : ℝ => Real.sin (Real.pi * s / L) • Y s)
        (Submission.JacobiGlobal.covAlong cov (fun s : ℝ => Real.sin (Real.pi * s / L) • Y s)) t)
      < 0 := by
  set A : ℝ := ‖Y 0‖ ^ 2 with hAdef
  have hApos : 0 < A := by rw [hAdef]; exact pow_pos (norm_pos_iff.mpr hY0) 2
  -- the pointwise bound
  have hpt : ∀ t ∈ Icc (0 : ℝ) L,
      idxAlong (cov := cov) γ (fun s : ℝ => Real.sin (Real.pi * s / L) • Y s)
        (Submission.JacobiGlobal.covAlong cov (fun s : ℝ => Real.sin (Real.pi * s / L) • Y s)) t
      ≤ A * ((deriv (fun s : ℝ => Real.sin (Real.pi * s / L)) t) ^ 2
          - (δ + ε) * (Real.sin (Real.pi * t / L)) ^ 2) := by
    intro t ht
    have htsm : Submission.JacobiGlobal.SmoothAlongAt (I := I) γ Y t :=
      hYsm t ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hid := idxAlong_dirichletField (cov := cov) (L := L) htor htsm (hYpar t ht)
    have hYtA : ‖Y t‖ ^ 2 = A := by rw [hAdef]; exact hYnrm t ht
    have hYne : Y t ≠ 0 := by
      intro hzero
      rw [hzero, norm_zero] at hYtA
      linarith [hApos]
    have hv1 : ‖Submission.Geodesic.curveVelocity (I := I) γ t‖ = 1 := by
      rw [← Submission.GeodesicSpeed.curveSpeed_eq_norm]
      exact hspeed t ht
    have hcurvY := curvVec_inner_lower_of_ne hcurv ht hYne hv1 (hYorth t ht)
    rw [hYtA] at hcurvY
    rw [hid, hYtA]
    nlinarith [hcurvY, sq_nonneg (Real.sin (Real.pi * t / L))]
  -- continuity of the integrand on `[0, L]`
  have hγ' : ContMDiffOn 𝓘(ℝ) I ∞ γ (Ioo ((0 : ℝ) - 1) (L + 1)) := by
    simpa only [zero_sub] using hγsm.mono (Set.subset_univ _)
  have hne' : ∀ t ∈ Ioo ((0 : ℝ) - 1) (L + 1),
      Submission.Geodesic.curveVelocity (I := I) γ t ≠ 0 := fun t _ => hne t
  have hVsm : ∀ t ∈ Icc (0 : ℝ) L, Submission.JacobiGlobal.SmoothAlongAt (I := I) γ
      (fun s : ℝ => Real.sin (Real.pi * s / L) • Y s) t := fun t ht =>
    dirichletField_smooth (L := L) (hYsm t ⟨by linarith [ht.1], by linarith [ht.2]⟩)
  have hcont := continuousOn_idxAlong_of_smoothOn (cov := cov) htor hL.le hγ' hne' hVsm
  have hint : IntervalIntegrable (fun t => idxAlong (cov := cov) γ
      (fun s : ℝ => Real.sin (Real.pi * s / L) • Y s)
      (Submission.JacobiGlobal.covAlong cov (fun s : ℝ => Real.sin (Real.pi * s / L) • Y s)) t)
      volume (0 : ℝ) L := hcont.intervalIntegrable_of_Icc hL.le
  -- the dominating function
  set Hb : ℝ → ℝ := fun t : ℝ => A * ((deriv (fun s : ℝ => Real.sin (Real.pi * s / L)) t) ^ 2
      - (δ + ε) * (Real.sin (Real.pi * t / L)) ^ 2) with hHbdef
  have hHfun : Hb = fun t : ℝ => A * ((Real.pi / L) ^ 2 * Real.cos (Real.pi * t / L) ^ 2
      - (δ + ε) * Real.sin (Real.pi * t / L) ^ 2) := by
    funext t
    show A * ((deriv (fun s : ℝ => Real.sin (Real.pi * s / L)) t) ^ 2
        - (δ + ε) * (Real.sin (Real.pi * t / L)) ^ 2)
      = A * ((Real.pi / L) ^ 2 * Real.cos (Real.pi * t / L) ^ 2
        - (δ + ε) * Real.sin (Real.pi * t / L) ^ 2)
    rw [deriv_sin_dirichlet L t]
    ring
  have hHcont : Continuous Hb := by
    rw [hHfun]
    fun_prop
  set G : ℝ → ℝ := fun t : ℝ => if t ∈ Icc (0 : ℝ) L
    then idxAlong (cov := cov) γ (fun s : ℝ => Real.sin (Real.pi * s / L) • Y s)
      (Submission.JacobiGlobal.covAlong cov (fun s : ℝ => Real.sin (Real.pi * s / L) • Y s)) t
    else Hb t with hGdef
  have hGcont : ContinuousOn G (Icc (0 : ℝ) L) :=
    hcont.congr (fun t ht => by simp only [hGdef, ht, if_true])
  have hGint : IntervalIntegrable G volume (0 : ℝ) L := hGcont.intervalIntegrable_of_Icc hL.le
  have hGle : G ≤ Hb := by
    intro t
    by_cases ht : t ∈ Icc (0 : ℝ) L
    · simp only [hGdef, ht, if_true]; exact hpt t ht
    · simp only [hGdef, ht, if_false]
      exact le_rfl
  have hle := intervalIntegral.integral_mono hL.le hGint (hHcont.intervalIntegrable 0 L) hGle
  have hcongr : (∫ t in (0 : ℝ)..L, G t) = ∫ t in (0 : ℝ)..L, idxAlong (cov := cov) γ
      (fun s : ℝ => Real.sin (Real.pi * s / L) • Y s)
      (Submission.JacobiGlobal.covAlong cov (fun s : ℝ => Real.sin (Real.pi * s / L) • Y s)) t := by
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    rw [uIcc_of_le hL.le] at ht
    simp only [hGdef, ht, if_true]
  rw [hcongr] at hle
  -- value of the dominating integral
  have hval : (∫ t in (0 : ℝ)..L, Hb t)
      = A * (Real.pi ^ 2 / (2 * L) - (δ + ε) * (L / 2)) := by
    rw [hHfun, intervalIntegral.integral_const_mul]
    congr 1
    have hA1 : IntervalIntegrable
        (fun t : ℝ => (Real.pi / L) ^ 2 * Real.cos (Real.pi * t / L) ^ 2) volume (0 : ℝ) L :=
      ((continuous_const.mul (by fun_prop : Continuous fun t : ℝ => Real.cos (Real.pi * t / L) ^ 2))).intervalIntegrable _ _
    have hA2 : IntervalIntegrable
        (fun t : ℝ => (δ + ε) * Real.sin (Real.pi * t / L) ^ 2) volume (0 : ℝ) L :=
      ((continuous_const.mul (by fun_prop : Continuous fun t : ℝ => Real.sin (Real.pi * t / L) ^ 2))).intervalIntegrable _ _
    rw [intervalIntegral.integral_sub hA1 hA2, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, intervalIntegral_cos_sq_pi_mul_div L hL,
      Commons.Analysis.Calculus.intervalIntegral_sin_sq_pi_mul_div L hL]
    have hL0 : L ≠ 0 := ne_of_gt hL
    field_simp
  rw [hval] at hle
  -- negativity
  have hkey : A * (Real.pi ^ 2 / (2 * L) - (δ + ε) * (L / 2)) < 0 := by
    have hs : 0 < Real.sqrt (δ + ε) := by
      by_contra hcon
      push_neg at hcon
      have : Real.sqrt (δ + ε) * L ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hcon hL.le
      linarith [hπ, Real.pi_pos]
    have hd : 0 < δ + ε := Real.sqrt_pos.mp hs
    have hprod : 0 < (Real.sqrt (δ + ε) * L - Real.pi) * (Real.sqrt (δ + ε) * L + Real.pi) :=
      mul_pos (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
    have hsq : (Real.sqrt (δ + ε)) ^ 2 = δ + ε := Real.sq_sqrt hd.le
    have h2 : Real.pi ^ 2 < (δ + ε) * L ^ 2 := by nlinarith [hprod, hsq]
    have hnum : Real.pi ^ 2 - (δ + ε) * L ^ 2 < 0 := by linarith
    have hpos : (0 : ℝ) < 2 * L := by linarith
    have hsplit : Real.pi ^ 2 / (2 * L) - (δ + ε) * (L / 2)
        = (Real.pi ^ 2 - (δ + ε) * L ^ 2) / (2 * L) := by field_simp
    rw [hsplit]
    exact mul_neg_of_pos_of_neg hApos (div_neg_of_neg_of_pos hnum hpos)
  linarith [hle, hkey]

/-! ## 5. The strong index bound -/

theorem not_dirichletIndexLeOne_of_parallelNormalPair
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {γ : ℝ → M} (hγsm : ContMDiffOn 𝓘(ℝ) I ∞ γ Set.univ)
    (hne : ∀ t : ℝ, Submission.Geodesic.curveVelocity (I := I) γ t ≠ 0)
    {L δ ε : ℝ} (hL : 0 < L)
    (hspeed : ∀ t ∈ Set.Icc (0 : ℝ) L, Submission.Length.curveSpeed (I := I) γ t = 1)
    (hδ : 0 < δ) (hε : 0 < ε) (hπ : Real.pi / Real.sqrt (δ + ε) < L)
    (hcurv : ∀ t ∈ Set.Icc (0 : ℝ) L, ∀ u v : TangentSpace I (γ t), ‖u‖ = 1 → ‖v‖ = 1 →
      inner ℝ u v = 0 →
      δ + ε ≤ inner ℝ (Submission.CurvatureVec.curvVec cov (γ t) u v v) u)
    (hp : Work.OddBound.ParallelNormalPair (I := I) cov γ L) :
    Work.OddBound.DirichletIndexNotLeOne (I := I) (cov := cov) γ L := by
  set V : (t : ℝ) → TangentSpace I (γ t) := fun s => Real.sin (Real.pi * s / L) • hp.X₁ s with hV
  set W : (t : ℝ) → TangentSpace I (γ t) := fun s => Real.sin (Real.pi * s / L) • hp.X₂ s with hW
  refine ⟨V, W, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs
    rw [hV]
    exact dirichletField_smooth (L := L) (hp.smooth₁ s hs)
  · rw [hV]
    exact dirichletField_zero (I := I) hp.X₁
  · rw [hV]
    exact dirichletField_at_right (I := I) (ne_of_gt hL) hp.X₁
  · intro s hs
    rw [hW]
    exact dirichletField_smooth (L := L) (hp.smooth₂ s hs)
  · rw [hW]
    exact dirichletField_zero (I := I) hp.X₂
  · rw [hW]
    exact dirichletField_at_right (I := I) (ne_of_gt hL) hp.X₂
  · intro a b hab
    let Y : (t : ℝ) → TangentSpace I (γ t) := fun s => a • hp.X₁ s + b • hp.X₂ s
    have hZeq : (fun s : ℝ => a • V s + b • W s)
        = fun s : ℝ => Real.sin (Real.pi * s / L) • Y s := by
      funext s
      rw [hV, hW]
      exact smul_smul_add_smul_smul (hp.X₁ s) (hp.X₂ s) a b (Real.sin (Real.pi * s / L))
    rw [hZeq]
    -- constancy of the inner product of the two parallel fields
    have hconst : ∀ t ∈ Icc (0 : ℝ) L,
        inner ℝ (hp.X₁ t) (hp.X₂ t) = inner ℝ (hp.X₁ 0) (hp.X₂ 0) :=
      inner_const_Icc_of_parallel (cov := cov) hmet htor hL
        (fun t _ => hγsm.mono (Set.subset_univ _)) (fun t _ => hne t)
        (fun t ht => hp.smooth₁ t ⟨by linarith [ht.1], by linarith [ht.2]⟩)
        (fun t ht => hp.smooth₂ t ⟨by linarith [ht.1], by linarith [ht.2]⟩)
        (fun t ht => hp.parallel₁ t ht) (fun t ht => hp.parallel₂ t ht)
    have hpi : Real.pi < Real.sqrt (δ + ε) * L := by
      have hd : 0 < δ + ε := by linarith
      have hs : 0 < Real.sqrt (δ + ε) := Real.sqrt_pos.mpr hd
      have h1 : Real.pi < L * Real.sqrt (δ + ε) := (div_lt_iff₀ hs).mp hπ
      linarith
    refine integral_idxAlong_sin_smul_neg (cov := cov) (Y := Y) htor hγsm hne hL hspeed hε hpi hcurv
      ?_ ?_ ?_ ?_ ?_
    · intro t ht
      exact smoothAlongAt_smul_add (hp.smooth₁ t ht) (hp.smooth₂ t ht)
    · intro t ht
      have h := covAlong_smul_add (cov := cov) (a := a) (b := b) htor
        (hp.smooth₁ t ⟨by linarith [ht.1], by linarith [ht.2]⟩)
        (hp.smooth₂ t ⟨by linarith [ht.1], by linarith [ht.2]⟩)
      rw [h, hp.parallel₁ t ht, hp.parallel₂ t ht, smul_zero, smul_zero, add_zero]
    · intro t ht
      show ‖a • hp.X₁ t + b • hp.X₂ t‖ ^ 2 = ‖a • hp.X₁ 0 + b • hp.X₂ 0‖ ^ 2
      rw [norm_add_smul_smul_sq (hp.X₁ t) (hp.X₂ t) a b (hp.unitNormal₁ t ht).1
            (hp.unitNormal₂ t ht).1,
        norm_add_smul_smul_sq (hp.X₁ 0) (hp.X₂ 0) a b (hp.unitNormal₁ 0 ⟨le_rfl, hL.le⟩).1
            (hp.unitNormal₂ 0 ⟨le_rfl, hL.le⟩).1,
        hconst t ht]
    · show a • hp.X₁ 0 + b • hp.X₂ 0 ≠ 0
      intro h0
      rcases eq_or_ne a 0 with ha | ha
      · have hb : b ≠ 0 := by rintro rfl; exact hab (by simp [ha])
        have hX₂0 : hp.X₂ 0 = 0 := by
          have h1 := h0
          rw [ha, zero_smul, zero_add] at h1
          rcases (smul_eq_zero.mp h1) with h | h
          · exact absurd h hb
          · exact h
        have hnorm := (hp.unitNormal₂ 0 ⟨le_rfl, hL.le⟩).1
        rw [hX₂0, norm_zero] at hnorm
        exact zero_ne_one hnorm
      · have h1 : a • hp.X₁ 0 = -(b • hp.X₂ 0) := by
          have h2 := h0
          rw [add_eq_zero_iff_eq_neg] at h2
          exact h2
        have hX₁0 : hp.X₁ 0 = (-(b / a)) • hp.X₂ 0 := by
          have h2 := congrArg (fun v => a⁻¹ • v) h1
          rw [smul_smul, inv_mul_cancel₀ ha, one_smul, smul_neg, smul_smul] at h2
          rw [h2, neg_smul, div_eq_inv_mul]
        rcases eq_or_ne (-(b / a)) 0 with hd | hd
        · rw [hd, zero_smul] at hX₁0
          have hnorm := (hp.unitNormal₁ 0 ⟨le_rfl, hL.le⟩).1
          rw [hX₁0, norm_zero] at hnorm
          exact zero_ne_one hnorm
        · have hX₂ : hp.X₂ 0 = (-(b / a))⁻¹ • hp.X₁ 0 := by
            have h2 := congrArg (fun v => (-(b / a))⁻¹ • v) hX₁0
            rw [smul_smul, inv_mul_cancel₀ hd, one_smul] at h2
            exact h2.symm
          exact hp.independent 0 ⟨le_rfl, hL.le⟩ ⟨(-(b / a))⁻¹, hX₂⟩
    · intro t ht
      show inner ℝ (a • hp.X₁ t + b • hp.X₂ t)
        (Submission.Geodesic.curveVelocity (I := I) γ t) = 0
      rw [inner_add_left, real_inner_smul_left, real_inner_smul_left,
        (hp.unitNormal₁ t ht).2, (hp.unitNormal₂ t ht).2, mul_zero, mul_zero, add_zero]

end Work.OddBound.strongIndex
