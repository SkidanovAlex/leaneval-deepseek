import ChallengeDeps
import Mathlib
import Submission.Work.Diff.C.geoCrux.BadGeoDefs
import Submission.Work.Diff.C.geoCrux.CoreStmts
import Submission.Work.Diff.C.far_ball_excess
import Submission.Work.Diff.C.RadialBound.GExp_radius_mfderiv_bound
import Submission.Work.Diff.C.RadialBound.far_sphere_path_bound
import Submission.Work.Diff.C.geoCrux.hmod_prop
import Submission.HingeClosed

set_option backward.isDefEq.respectTransparency.types false

/-!
# The far ball of `q_k` has small diameter (`Work.Diff.C.GeoCrux.FarBallDiamProp`)

Statement (`Submission/Work/Diff/C/geoCrux/BadGeoDefs.lean`): in the setting of the C-area endgame
(`hHess`/`hgrad`/`hsmC`/`hcont`: for every centre `y` the function `fcos y = cos ∘ rdist y` has
`Hess (fcos y) = -(fcos y)·g + E` with `|E| ≤ ε₁` on `{fcos y > -1+c}` and the eikonal identity),
with `p`, `e` orthonormal at `p` and `q := qpt hmet p e (Fin.succ k)`, any two points of the far ball
of `q`, i.e. at distance at least `π - arccos (1-c)` from `q`, are within `50 (√c + ε₁π)`.

## The proof (reference for the assembly below)

Write `δ := arccos (1-c)`, `ρ := π - δ`.

* **(1) Excess (Myers) bound** — `Work.Diff.C.geoCrux.far_excess`: every `z` of the far ball
  satisfies `rdist q z ≤ π + arcsin (2 ε₁)`.  (The classical "sum of two distance functions"
  argument: along a minimising geodesic from `q` to `z`, `F := rdist q · + rdist z ·` has a global
  minimum on the geodesic, so its Hessian is positive semidefinite there; the two shape-operator
  bounds `Work.Diff.C.rhess_rdist_bound_of_hHess` give `cos (L/2) ≥ -ε₁` at the midpoint, i.e.
  `L ≤ π + 2 arcsin ε₁ ≤ π + arcsin (2 ε₁)`.)
* **(2) Projection onto the sphere of radius `ρ`**: for `z` in the far ball, the point `x` at
  parameter `ρ` of a minimising ray from `q` to `z` satisfies `rdist q x = ρ` (so `x` is on the
  geodesic sphere `S(q,ρ)`) and `rdist x z = rdist q z - ρ ≤ (π + arcsin (2 ε₁)) - ρ
  = δ + arcsin (2 ε₁)`.  (`sphere_point_near` below, via Hopf–Rinow.)
* **(3) Size of the sphere `S(q,ρ)`** — `Work.Diff.C.RadialBound.far_sphere_path_bound`, fed with
  the differential bound `Work.Diff.C.RadialBound.GExp_radius_mfderiv_bound`, which is fed with the
  sharp radial Jacobi modulus bound `Work.Diff.C.RadialBound.radial_modulus_bound`: for unit
  `u u' ∈ T_qM`, `rdist (GExp q (ρ • u)) (GExp q (ρ • u')) ≤ (sin ρ + 25 ε₁) π`.
  (`far_sphere_param` provides the directions `u`, `u'` with `x = GExp q (ρ • u)`,
  `x' = GExp q (ρ • u')`.)
* **(4) Triangle inequality plus arithmetic**: with `sin ρ = sin δ = sin (arccos (1-c)) ≤ √(2c)`,
  `δ ≤ π √(c/2)`, `arcsin (2 ε₁) ≤ 4 ε₁` (`2 ε₁ ≤ 1/2`):
  `rdist z z' ≤ 2 (δ + arcsin (2 ε₁)) + π (sin δ + 25 ε₁) ≤ 2π√2 √c + (8 + 25π) ε₁
   ≤ 50 √c + 50 π ε₁ = 50 (√c + ε₁ π)`.
* **Dimension one** is a separate (delegated) statement `far_ball_dim_one`: in dimension one `M` is
  a circle of length `L ≤ 2π`, the far ball of `q` is an arc of length `L - 2ρ ≤ 2δ`, and the
  diameter of an arc is at most its length; `2δ ≤ 2π√(c/2) ≤ 50 √c`.

## The sharp radial modulus input

The `hmod` argument of `Work.Diff.C.RadialBound.GExp_radius_mfderiv_bound` at the end of
`far_ball_of_inputs` is supplied by `Work.Diff.C.geoCrux.hmod_prop`
(module `Submission.Work.Diff.C.geoCrux.hmod_prop`), whose `Work.Diff.C.geoCrux.HmodProp` is
assembled in `geoCrux/CoreStmts.lean` from `Work.Diff.C.geoCrux.inj_radius_core` (proved) and
`Work.Diff.C.geoCrux.variation_modulus` (proved), using the smooth-level Jacobi uniqueness
`Work.Diff.C.geoCrux.jacobiUniqSmooth`.  It replaces the earlier call to
`Work.Diff.C.RadialBound.radial_modulus_bound`, which is the same statement in a colleague's file.
-/


namespace Work.Diff.C.geoCrux

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle Set VectorField CovariantDerivative Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M]
  {cov : CovariantDerivative I E (TangentSpace I (M := M))}
  [ContMDiffCovariantDerivative cov ∞]

/-! ## 1. The projection onto the geodesic sphere of radius `ρ` -/

/-- **The point of a minimising ray from `q` at a prescribed distance.**

If `0 < ρ ≤ rdist q z`, and `rdist q z ≤ B`, then there is `x` with `rdist q x = ρ` and
`rdist x z ≤ B - ρ` (take `x` at parameter `ρ` of a minimising geodesic from `q` to `z`).

(The proof is the argument of `Work.Diff.C.exists_sphere_point_near`, repeated here so that this file
does not depend on the modules of the (in-flux) `dip_far_ball` development.) -/
private lemma sphere_point_near (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {q z : M} {ρ B : ℝ} (hρ : 0 < ρ) (hz : ρ ≤ rdist (I := I) (M := M) q z)
    (hexc : rdist (I := I) (M := M) q z ≤ B) :
    ∃ x : M, rdist (I := I) (M := M) q x = ρ ∧ rdist (I := I) (M := M) x z ≤ B - ρ := by
  obtain ⟨v, hvz, hvd⟩ :=
    Submission.HopfRinow.exists_geodesic_riemannianEDist_eq (I := I) (cov := cov) hmet htor q z
  have hLval : rdist (I := I) (M := M) q z = ‖v‖ := by
    rw [rdist, hvd, ENNReal.toReal_ofReal (norm_nonneg v)]
  have hLge : ρ ≤ ‖v‖ := by rw [← hLval]; exact hz
  have hLpos : 0 < ‖v‖ := lt_of_lt_of_le hρ hLge
  have hvne : v ≠ 0 := norm_pos_iff.mp hLpos
  set u : TangentSpace I q := Submission.GlobalExp.unitOf v hvne with hudef
  have hu : ‖u‖ = 1 := Submission.GlobalExp.unitOf_norm v hvne
  have hLu : ‖v‖ • u = v := by
    rw [hudef, Submission.GlobalExp.unitOf, smul_smul,
      mul_inv_cancel₀ (by simpa [norm_eq_zero] using hvne), one_smul]
  refine ⟨Submission.GlobalExp.GExp (cov := cov) hmet q (ρ • u), ?_, ?_⟩
  · have hmin : Manifold.riemannianEDist I q
        (Submission.GlobalExp.GExp (cov := cov) hmet q (‖v‖ • u)) = ENNReal.ofReal ‖v‖ := by
      rw [hLu, hvz]
      exact hvd
    have hle := Submission.HingeClosed.edist_GExp_smul_min_sub (cov := cov) hmet q hu hρ hLge hmin
    rw [rdist, hle, ENNReal.toReal_ofReal (le_of_lt hρ)]
  · have hray := Submission.HopfRinow.riemannianEDist_GExp_ray_le (cov := cov) hmet q hu
      (a := ρ) (b := ‖v‖) (le_of_lt hρ) hLge
    have hz_eq : Submission.GlobalExp.GExp (cov := cov) hmet q (‖v‖ • u) = z := by
      rw [hLu]; exact hvz
    have hfin : rdist (I := I) (M := M)
        (Submission.GlobalExp.GExp (cov := cov) hmet q (ρ • u)) z ≤ ‖v‖ - ρ := by
      calc rdist (I := I) (M := M) (Submission.GlobalExp.GExp (cov := cov) hmet q (ρ • u)) z
          = (Manifold.riemannianEDist I (Submission.GlobalExp.GExp (cov := cov) hmet q (ρ • u))
              (Submission.GlobalExp.GExp (cov := cov) hmet q (‖v‖ • u))).toReal := by
            rw [rdist, hz_eq]
        _ ≤ (ENNReal.ofReal (‖v‖ - ρ)).toReal :=
            ENNReal.toReal_mono ENNReal.ofReal_ne_top hray
        _ = ‖v‖ - ρ := ENNReal.toReal_ofReal (by linarith)
    have hB : ‖v‖ ≤ B := by rw [← hLval]; exact hexc
    linarith

/-! ## 2. The numerical endgame -/

private lemma arcsin_two_mul_le {ε : ℝ} (hε : 0 ≤ ε) (hε' : 2 * ε ≤ 1 / 2) :
    Real.arcsin (2 * ε) ≤ 4 * ε := by
  have h2ε : 0 ≤ 2 * ε := by linarith
  have hx : (2 * ε) ∈ Set.Icc (-1) 1 := ⟨by linarith, by linarith⟩
  have hy : (4 * ε) ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    refine ⟨by linarith [Real.pi_pos], ?_⟩
    nlinarith [hε', Real.pi_gt_three]
  refine (Real.arcsin_le_iff_le_sin hx hy).mpr ?_
  have hlow : 4 * ε - (4 * ε) ^ 3 / 6 ≤ Real.sin (4 * ε) := Real.sin_ge_sub_cube (by linarith)
  have hε4 : ε ≤ 1 / 4 := by linarith
  have hε2 : ε ^ 2 ≤ 1 / 16 := by nlinarith
  nlinarith [hlow, h2ε, hε, hε4, hε2]

private lemma delta_bounds {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    Real.arccos (1 - c) ≤ Real.pi * Real.sqrt (c / 2)
      ∧ Real.sin (Real.arccos (1 - c)) ≤ Real.sqrt (2 * c) := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have hcosδ : Real.cos (Real.arccos (1 - c)) = 1 - c :=
    Real.cos_arccos (by linarith) (by linarith)
  have hδ0 : 0 ≤ Real.arccos (1 - c) := Real.arccos_nonneg _
  have hδπ : Real.arccos (1 - c) ≤ Real.pi := Real.arccos_le_pi _
  have hδhalf : Real.arccos (1 - c) / 2 ≤ Real.pi / 2 := by
    have h := Real.arccos_le_pi_div_two.mpr (show (0 : ℝ) ≤ 1 - c by linarith)
    linarith
  constructor
  · have hδhalf0 : 0 ≤ Real.arccos (1 - c) / 2 := by linarith
    have hsinhalf : Real.sin (Real.arccos (1 - c) / 2) = Real.sqrt (c / 2) := by
      have hcos2 : Real.cos (Real.arccos (1 - c))
          = 2 * Real.cos (Real.arccos (1 - c) / 2) ^ 2 - 1 := by
        have h := Real.cos_two_mul (Real.arccos (1 - c) / 2)
        rw [show 2 * (Real.arccos (1 - c) / 2) = Real.arccos (1 - c) by ring] at h
        exact h
      have hs2 : Real.sin (Real.arccos (1 - c) / 2) ^ 2
          + Real.cos (Real.arccos (1 - c) / 2) ^ 2 = 1 := Real.sin_sq_add_cos_sq _
      have hsq : Real.sin (Real.arccos (1 - c) / 2) ^ 2 = c / 2 := by
        rw [hcosδ] at hcos2; nlinarith
      rw [← hsq, Real.sqrt_sq (Real.sin_nonneg_of_nonneg_of_le_pi hδhalf0 (by linarith))]
    have hj := Real.mul_le_sin hδhalf0 hδhalf
    rw [hsinhalf] at hj
    have h5 : 2 / Real.pi * (Real.arccos (1 - c) / 2) = Real.arccos (1 - c) / Real.pi := by
      field_simp
    rw [h5] at hj
    have := (div_le_iff₀ hπ).mp hj
    linarith [this]
  · have hsq : Real.sin (Real.arccos (1 - c)) ^ 2 = 2 * c - c ^ 2 := by
      have h := Real.sin_sq_add_cos_sq (Real.arccos (1 - c))
      rw [hcosδ] at h; nlinarith
    have hval : Real.sin (Real.arccos (1 - c)) = Real.sqrt (2 * c - c ^ 2) := by
      rw [← hsq, Real.sqrt_sq (Real.sin_nonneg_of_nonneg_of_le_pi hδ0 hδπ)]
    rw [hval]
    exact Real.sqrt_le_sqrt (by nlinarith)

private lemma far_ball_arith {c ε₁ : ℝ} (hc : 0 < c) (hc1 : c ≤ 1 / 4) (hε₁ : 0 ≤ ε₁)
    (hε₂ : 2 * ε₁ ≤ 1 / 2) :
    2 * (Real.arccos (1 - c) + Real.arcsin (2 * ε₁))
        + Real.pi * (Real.sin (Real.arccos (1 - c)) + 25 * ε₁)
      ≤ 50 * (Real.sqrt c + ε₁ * Real.pi) := by
  obtain ⟨hδ, hsinδ⟩ := delta_bounds hc (by linarith)
  have harc := arcsin_two_mul_le hε₁ hε₂
  have hπ : 0 < Real.pi := Real.pi_pos
  have hA : 0 ≤ Real.sqrt c := Real.sqrt_nonneg c
  have hB : 0 < Real.sqrt 2 := Real.sqrt_pos_of_pos (by norm_num)
  have hBB : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hsqc : Real.sqrt (c / 2) = Real.sqrt c / Real.sqrt 2 := Real.sqrt_div (le_of_lt hc) 2
  have hsqrt2c : Real.sqrt (2 * c) = Real.sqrt 2 * Real.sqrt c := Real.sqrt_mul (by norm_num) c
  -- step 1: `2 δ ≤ π √2 √c`
  have hstep1 : 2 * Real.arccos (1 - c) ≤ Real.pi * Real.sqrt 2 * Real.sqrt c := by
    have h := mul_le_mul_of_nonneg_left hδ (by norm_num : (0:ℝ) ≤ 2)
    rw [hsqc] at h
    have h2 : 2 * (Real.pi * (Real.sqrt c / Real.sqrt 2)) = 2 * Real.pi * Real.sqrt c / Real.sqrt 2 := by
      ring
    rw [h2] at h
    have h2over : 2 / Real.sqrt 2 = Real.sqrt 2 := by
      rw [div_eq_iff (ne_of_gt hB), Real.mul_self_sqrt (by norm_num)]
    have h3 : 2 * Real.pi * Real.sqrt c / Real.sqrt 2 = Real.pi * Real.sqrt 2 * Real.sqrt c := by
      rw [show 2 * Real.pi * Real.sqrt c / Real.sqrt 2
            = Real.pi * (2 / Real.sqrt 2) * Real.sqrt c by ring, h2over]
    linarith [h, h3.le, h3.ge]
  -- step 2: `π sin δ ≤ π √2 √c`
  have hstep2 : Real.pi * Real.sin (Real.arccos (1 - c)) ≤ Real.pi * Real.sqrt 2 * Real.sqrt c := by
    rw [hsqrt2c] at hsinδ
    nlinarith [hsinδ, hπ]
  -- step 3: assemble
  have hconst : (2:ℝ) * Real.pi * Real.sqrt 2 + Real.pi * Real.sqrt 2 ≤ 50 := by
    have hπ4 : Real.pi < 4 := Real.pi_lt_four
    have h2 : Real.sqrt 2 < 3 / 2 := Real.sqrt_two_lt_three_halves
    nlinarith [hπ4, h2, hπ, Real.sqrt_nonneg 2]
  have heps : 2 * (4 * ε₁) + Real.pi * (25 * ε₁) ≤ 50 * (ε₁ * Real.pi) := by
    nlinarith [hπ, Real.pi_gt_three, hε₁]
  have hsplit : 2 * (Real.arccos (1 - c) + Real.arcsin (2 * ε₁))
        + Real.pi * (Real.sin (Real.arccos (1 - c)) + 25 * ε₁)
      = (2 * Real.arccos (1 - c) + Real.pi * Real.sin (Real.arccos (1 - c)))
        + (2 * Real.arcsin (2 * ε₁) + Real.pi * (25 * ε₁)) := by ring
  rw [hsplit]
  have h1 : 2 * Real.arccos (1 - c) + Real.pi * Real.sin (Real.arccos (1 - c))
      ≤ (2 * Real.pi * Real.sqrt 2) * Real.sqrt c := by
    have : (2 * Real.pi * Real.sqrt 2) * Real.sqrt c
        = Real.pi * Real.sqrt 2 * Real.sqrt c + Real.pi * Real.sqrt 2 * Real.sqrt c := by ring
    linarith [hstep1, hstep2, this.le, this.ge]
  have h2 : 2 * Real.arcsin (2 * ε₁) + Real.pi * (25 * ε₁) ≤ 50 * (ε₁ * Real.pi) := by
    linarith [harc, heps]
  have h3 : (2 * Real.pi * Real.sqrt 2) * Real.sqrt c ≤ 50 * Real.sqrt c := by
    have := mul_le_mul_of_nonneg_right (by linarith [hconst] : (2:ℝ) * Real.pi * Real.sqrt 2 ≤ 50) hA
    linarith [this]
  linarith [h1, h2, h3]

private lemma dim_one_arith {c ε₁ : ℝ} (hc : 0 < c) (hc1 : c ≤ 1 / 4) (hε₁ : 0 ≤ ε₁) :
    2 * Real.arccos (1 - c) ≤ 50 * (Real.sqrt c + ε₁ * Real.pi) := by
  obtain ⟨hδ, -⟩ := delta_bounds hc (by linarith)
  have hπ : 0 < Real.pi := Real.pi_pos
  have hA : 0 ≤ Real.sqrt c := Real.sqrt_nonneg c
  have hsqc : Real.sqrt (c / 2) = Real.sqrt c / Real.sqrt 2 := Real.sqrt_div (le_of_lt hc) 2
  have hB : 0 < Real.sqrt 2 := Real.sqrt_pos_of_pos (by norm_num)
  have h1 : 2 * Real.arccos (1 - c) ≤ Real.pi * Real.sqrt 2 * Real.sqrt c := by
    have h := mul_le_mul_of_nonneg_left hδ (by norm_num : (0:ℝ) ≤ 2)
    rw [hsqc] at h
    have h2' : 2 * (Real.pi * (Real.sqrt c / Real.sqrt 2)) = 2 * Real.pi * Real.sqrt c / Real.sqrt 2 := by ring
    rw [h2'] at h
    have h2over : 2 / Real.sqrt 2 = Real.sqrt 2 := by
      rw [div_eq_iff (ne_of_gt hB), Real.mul_self_sqrt (by norm_num)]
    have h3 : 2 * Real.pi * Real.sqrt c / Real.sqrt 2 = Real.pi * Real.sqrt 2 * Real.sqrt c := by
      rw [show 2 * Real.pi * Real.sqrt c / Real.sqrt 2
            = Real.pi * (2 / Real.sqrt 2) * Real.sqrt c by ring, h2over]
    linarith [h, h3.le, h3.ge]
  have h567 : Real.pi * Real.sqrt 2 ≤ 50 := by
    nlinarith [Real.pi_lt_four, Real.sqrt_two_lt_three_halves, Real.sqrt_nonneg 2]
  have h4 : Real.pi * Real.sqrt 2 * Real.sqrt c ≤ 50 * Real.sqrt c := by
    have := mul_le_mul_of_nonneg_right h567 hA
    linarith [this]
  have h5 : 0 ≤ 50 * (ε₁ * Real.pi) := by positivity
  linarith [h1, h4, h5]

/-! ## 3. The one-dimensional case -/

/-- The far-ball diameter bound in dimension one. -/
private lemma dim_one_far_ball (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    (hdim1 : Module.finrank ℝ E = 1) {p : M} (hdiam : ∀ y : M, rdist (I := I) (M := M) p y ≤ Real.pi)
    {c : ℝ} {q : M} :
    ∀ z z' : M, Real.pi - Real.arccos (1 - c) ≤ rdist (I := I) (M := M) q z →
      Real.pi - Real.arccos (1 - c) ≤ rdist (I := I) (M := M) q z' →
      rdist (I := I) (M := M) z z' ≤ 2 * Real.arccos (1 - c) := by
  intro z z' hz hz'
  haveI : ConnectedSpace M := connectedSpace_iff_univ.mpr isPathConnected_univ.isConnected
  haveI : RegularSpace M := inferInstance
  -- the global diameter bound in dimension one
  have hdiam' : ∀ x y : M, rdist (I := I) (M := M) x y ≤ Real.pi :=
    fun x y => Work.Diff.C.fbcap_diam_one (I := I) (M := M) (cov := cov) hmet htor hdim1 hdiam x y
  -- a unit vector at `q`
  obtain ⟨v₀, hv₀⟩ := exists_ne (0 : E)
  set u : TangentSpace I q := Submission.GlobalExp.unitOf v₀ hv₀ with hudef
  have hu : ‖u‖ = 1 := Submission.GlobalExp.unitOf_norm v₀ hv₀
  have hu_ne : u ≠ 0 := by
    intro h; rw [h, norm_zero] at hu; norm_num at hu
  -- the minimal period `P` of the unit-speed ray from `q`
  obtain ⟨a, b, hab, heq⟩ :=
    Work.Final.DimOne.exists_ne_of_GExp_ray (I := I) (M := M) (cov := cov) hmet htor hdim1 q u hu
  obtain ⟨Q, hQpos, -, hQper⟩ :=
    Work.Final.DimOne.period_of_GExp_ray_eq (I := I) (M := M) (cov := cov) hmet hdim1 q u hu_ne hab heq
  obtain ⟨ρ₀, hρ₀pos, hρ₀bd⟩ :=
    Work.Final.DimOne.periods_bddBelow (I := I) (M := M) (cov := cov) hmet htor q u hu
  obtain ⟨P, hPpos, hPper, hPmin⟩ :=
    Work.Final.DimOne.exists_minimal_period (I := I) (M := M) (cov := cov) hmet q u hu_ne
      ⟨Q, hQpos, hQper⟩ ⟨ρ₀, hρ₀pos, hρ₀bd⟩
  have hcont := Work.Final.DimOne.continuous_rayLift (I := I) (M := M) (cov := cov) hmet q u hu_ne
    hPpos hPper
  have hsurj := Work.Final.DimOne.surjective_rayLift (I := I) (M := M) (cov := cov) hmet htor hdim1
    q u hu_ne hPpos hPper hcont
  set γ : ℝ → M := fun τ : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (τ • u) with hγdef
  have hγ0 : γ 0 = q := by
    rw [hγdef]
    simp [Submission.GlobalExp.GExp_zero]
  have hγP : γ P = q := by
    have h := hPper 0
    rw [zero_add, zero_smul, Submission.GlobalExp.GExp_zero] at h
    rw [hγdef]
    exact h
  have hγs : ∀ s : ℝ, γ (s + P) = γ s := by
    intro s
    rw [hγdef]
    exact hPper s
  -- the ray distance estimate
  have hray : ∀ s t : ℝ, 0 ≤ s → s ≤ t → rdist (I := I) (M := M) (γ s) (γ t) ≤ t - s := by
    intro s t hs0 hst
    have h := Submission.HopfRinow.riemannianEDist_GExp_ray_le (cov := cov) hmet q hu
      (a := s) (b := t) hs0 hst
    rw [rdist]
    calc (Manifold.riemannianEDist I (γ s) (γ t)).toReal
        ≤ (ENNReal.ofReal (t - s)).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top (by simpa only [hγdef] using h)
      _ = t - s := ENNReal.toReal_ofReal (by linarith)
  have hcomm' : ∀ x y : M, rdist (I := I) (M := M) x y = rdist (I := I) (M := M) y x := by
    intro x y
    rw [rdist, rdist, Manifold.riemannianEDist_comm]
  -- `P ≤ 2π`
  have hlow : P / 2 ≤ rdist (I := I) (M := M) q (γ (P / 2)) := by
    obtain ⟨v, hvG, hvd⟩ :=
      Submission.HopfRinow.exists_geodesic_riemannianEDist_eq (I := I) (cov := cov) hmet htor q (γ (P / 2))
    obtain ⟨cc, hcc⟩ := Work.Final.DimOne.exists_smul_eq_of_finrank_eq_one hdim1 hu_ne (v := v)
    have hℓc : rdist (I := I) (M := M) q (γ (P / 2)) = |cc| := by
      rw [rdist, hvd, ENNReal.toReal_ofReal (norm_nonneg v), hcc, norm_smul, hu, mul_one,
        Real.norm_eq_abs]
    have hcG : Submission.GlobalExp.GExp (cov := cov) hmet q (cc • u)
        = Submission.GlobalExp.GExp (cov := cov) hmet q ((P / 2) • u) := by
      rw [← hcc]
      simpa only [hγdef] using hvG
    have hcase : cc = P / 2 ∨ P ≤ |cc - P / 2| := by
      by_cases h : cc = P / 2
      · exact Or.inl h
      · refine Or.inr ?_
        obtain ⟨Q', hQ'pos, hQ'le, hQ'per⟩ :=
          Work.Final.DimOne.period_of_GExp_ray_eq (I := I) (M := M) (cov := cov) hmet hdim1 q u hu_ne
            h hcG
        calc P ≤ Q' := hPmin Q' hQ'pos hQ'per
          _ ≤ |P / 2 - cc| := hQ'le
          _ = |cc - P / 2| := abs_sub_comm _ _
    rcases hcase with hcase | hcase
    · rw [hℓc, hcase, abs_of_pos (show (0 : ℝ) < P / 2 by linarith [hPpos])]
    · rw [hℓc]
      have hP2 : (0 : ℝ) < P / 2 := by linarith [hPpos]
      have h1 : |cc - P / 2| ≤ |cc| + P / 2 := by
        calc |cc - P / 2| = |cc + -(P / 2)| := by ring_nf
          _ ≤ |cc| + |-(P / 2)| := abs_add_le cc (-(P / 2))
          _ = |cc| + P / 2 := by rw [abs_neg, abs_of_pos hP2]
      linarith
  have hP2π : P ≤ 2 * Real.pi := by
    have h := hdiam' q (γ (P / 2))
    linarith
  -- the far ball is an interval of the circle
  have hfar : ∀ s : ℝ, 0 ≤ s → s ≤ P →
      rdist (I := I) (M := M) q (γ s) ≤ s ∧ rdist (I := I) (M := M) q (γ s) ≤ P - s := by
    intro s hs0 hsP
    constructor
    · have h := hray 0 s le_rfl hs0
      rw [hγ0] at h
      linarith [h]
    · have h := hray s P hs0 hsP
      rw [hγP] at h
      rw [hcomm'] at h
      exact h
  -- conclude
  haveI : Fact (0 < P) := ⟨hPpos⟩
  obtain ⟨ξ, hξ⟩ := hsurj z
  obtain ⟨η, hη⟩ := hsurj z'
  set s : ℝ := (AddCircle.equivIco (p := P) (0 : ℝ) ξ).1 with hsdef
  set t : ℝ := (AddCircle.equivIco (p := P) (0 : ℝ) η).1 with htdef
  have hs0 : 0 ≤ s := (AddCircle.equivIco (p := P) (0 : ℝ) ξ).2.1
  have hsP : s < P := by
    have h : ((AddCircle.equivIco (p := P) (0 : ℝ) ξ).1 : ℝ) < P := by
      have h0 := (AddCircle.equivIco (p := P) (0 : ℝ) ξ).2.2
      simpa only [zero_add] using h0
    rwa [hsdef]
  have ht0 : 0 ≤ t := (AddCircle.equivIco (p := P) (0 : ℝ) η).2.1
  have htP : t < P := by
    have h : ((AddCircle.equivIco (p := P) (0 : ℝ) η).1 : ℝ) < P := by
      have h0 := (AddCircle.equivIco (p := P) (0 : ℝ) η).2.2
      simpa only [zero_add] using h0
    rwa [htdef]
  have hsc : (s : AddCircle P) = ξ := by rw [hsdef]; exact AddCircle.coe_equivIco
  have htc : (t : AddCircle P) = η := by rw [htdef]; exact AddCircle.coe_equivIco
  have hzγ : z = γ s := by
    rw [← hξ, ← hsc, Work.Final.rayLift_coe (cov := cov) hmet q u P hPper s]
  have hz'γ : z' = γ t := by
    rw [← hη, ← htc, Work.Final.rayLift_coe (cov := cov) hmet q u P hPper t]
  subst hzγ
  subst hz'γ
  -- the parameters lie in `[ρ, P - ρ]`
  set ρ : ℝ := Real.pi - Real.arccos (1 - c) with hρdef
  have hsρ : ρ ≤ s := le_trans hz (hfar s hs0 hsP.le).1
  have hsPρ : s ≤ P - ρ := by
    have := (hfar s hs0 hsP.le).2
    linarith
  have htρ : ρ ≤ t := le_trans hz' (hfar t ht0 htP.le).1
  have htPρ : t ≤ P - ρ := by
    have := (hfar t ht0 htP.le).2
    linarith
  rcases le_total s t with hst | hts
  · have h1 : rdist (I := I) (M := M) (γ s) (γ t) ≤ t - s := hray s t hs0 hst
    have h2 : t - s ≤ P - 2 * ρ := by linarith
    have h3 : P - 2 * ρ ≤ 2 * Real.arccos (1 - c) := by
      rw [hρdef] at *; linarith
    linarith
  · have h1 : rdist (I := I) (M := M) (γ s) (γ t) ≤ s - t := by
      have h := hray t s ht0 hts
      rw [hcomm'] at h
      exact h
    have h2 : s - t ≤ P - 2 * ρ := by linarith
    have h3 : P - 2 * ρ ≤ 2 * Real.arccos (1 - c) := by
      rw [hρdef] at *; linarith
    linarith

/-! ## 3. The assembly -/

/-- **The far-ball diameter bound from the two geometric inputs.**

Given the Myers-type excess bound (`hexcess`, the statement of `Work.Diff.C.geoCrux.far_excess`)
and the one-dimensional case (`hdim1b`, the statement of `Work.Diff.C.geoCrux.far_ball_dim_one`),
the target `FarBallDiamProp` follows.  The remaining ingredients are the (proved) sphere-size bound
`Work.Diff.C.RadialBound.far_sphere_path_bound` (dimension `≥ 2`) fed with
`Work.Diff.C.RadialBound.GExp_radius_mfderiv_bound` and the radial modulus bound
`Work.Diff.C.RadialBound.radial_modulus_bound`, the parametrisation `Work.Diff.C.far_sphere_param`,
the projection `sphere_point_near`, and `far_ball_arith`. -/
private lemma far_ball_of_inputs
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {α c ε₁ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hc : 0 < c) (hc1 : c ≤ 1 / 4)
    (hε₁ : 0 ≤ ε₁) (hnum1 : 3 * c ≤ 1 - Real.cos α) (hnum2 : 4 * ε₁ * Real.pi < c)
    {p : M} {e : Fin (Module.finrank ℝ E) → TangentSpace I p}
    (hON : ∀ i j, Inner.inner ℝ (e i) (e j) = if i = j then 1 else 0)
    (hsmC : ∀ (q y : M), -1 + c ≤ fcos (I := I) (M := M) q y →
      CMDiffAt ∞ (fcos (I := I) (M := M) q) y)
    (hHess : ∀ q : M, HessBoundRegion (I := I) (M := M) cov c ε₁ (fcos (I := I) (M := M) q))
    (hcont : ∀ q : M, Continuous (fcos (I := I) (M := M) q))
    (hgrad : ∀ (q y : M), -1 + c < fcos (I := I) (M := M) q y →
      Inner.inner ℝ (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) y)
        (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) y)
        = 1 - (fcos (I := I) (M := M) q y) ^ 2)
    (hinit : InitData (I := I) (M := M) (cov := cov) hmet p e)
    (hdiam : ∀ y : M, rdist (I := I) (M := M) p y ≤ Real.pi)
    {k : Fin (Module.finrank ℝ E)}
    (hexcess : ∀ z : M,
      Real.pi - Real.arccos (1 - c)
          ≤ rdist (I := I) (M := M) (qpt (I := I) (M := M) (cov := cov) hmet p e (Fin.succ k)) z →
      rdist (I := I) (M := M) (qpt (I := I) (M := M) (cov := cov) hmet p e (Fin.succ k)) z
        ≤ Real.pi + Real.arcsin (2 * ε₁))
    (hdim1b : Module.finrank ℝ E = 1 → ∀ z z' : M,
      Real.pi - Real.arccos (1 - c)
          ≤ rdist (I := I) (M := M) (qpt (I := I) (M := M) (cov := cov) hmet p e (Fin.succ k)) z →
      Real.pi - Real.arccos (1 - c)
          ≤ rdist (I := I) (M := M) (qpt (I := I) (M := M) (cov := cov) hmet p e (Fin.succ k)) z' →
      rdist (I := I) (M := M) z z' ≤ 2 * Real.arccos (1 - c)) :
    ∀ z z' : M,
      Real.pi - Real.arccos (1 - c)
          ≤ rdist (I := I) (M := M) (qpt (I := I) (M := M) (cov := cov) hmet p e (Fin.succ k)) z →
      Real.pi - Real.arccos (1 - c)
          ≤ rdist (I := I) (M := M) (qpt (I := I) (M := M) (cov := cov) hmet p e (Fin.succ k)) z' →
      rdist (I := I) (M := M) z z' ≤ 50 * (Real.sqrt c + ε₁ * Real.pi) := by
  intro z z' hz hz'
  obtain ⟨hδ, hsinδ⟩ := delta_bounds hc (by linarith)
  have hε₂ : 2 * ε₁ ≤ 1 / 2 := by
    have : ε₁ < 1 / (4 * Real.pi) := by
      rw [lt_div_iff₀ (by positivity)] at *
      nlinarith [hnum2, Real.pi_pos]
    nlinarith [this, Real.pi_gt_three]
  -- the trivial case `2 δ ≥ 50 √c` cannot happen (we always have `2δ ≤ 2π√(c/2) ≤ 2.23√c`),
  -- so it suffices to run the dimension-`≥ 2` argument; the dimension-one case is `hdim1b`.
  by_cases hd1 : Module.finrank ℝ E = 1
  · have hmain := hdim1b hd1 z z' hz hz'
    have h2δ : 2 * Real.arccos (1 - c) ≤ 50 * (Real.sqrt c + ε₁ * Real.pi) :=
      dim_one_arith hc hc1 hε₁
    linarith
  · -- dimension at least two
    have hdim2 : 2 ≤ Module.finrank ℝ E := by
      have hpos : 0 < Module.finrank ℝ E := by
        obtain ⟨v, hv⟩ := exists_ne (0 : E)
        exact Module.finrank_pos_iff_exists_ne_zero.mpr ⟨v, hv⟩
      omega
    set δ : ℝ := Real.arccos (1 - c) with hδdef
    set ρ : ℝ := Real.pi - δ with hρdef
    set q : M := qpt (I := I) (M := M) (cov := cov) hmet p e (Fin.succ k) with hqdef
    have hρpos : 0 < ρ := by
      have h1 : δ ≤ Real.pi / 2 := by
        rw [hδdef]
        exact Real.arccos_le_pi_div_two.mpr (by linarith)
      rw [hρdef]; linarith [Real.pi_pos]
    have hρπ : ρ ≤ Real.pi - Real.arccos (1 - c) := by rw [hρdef, hδdef]
    have hρe : Real.sqrt ε₁ ≤ ρ := by
      -- `√ε₁ ≤ √(c/(4π))` and `π - arccos (1-c) ≥ π - π√(c/2) ≥ π (1 - 1/2) = π/2`
      have hcpos : 0 < c := hc
      have h4 : Real.sqrt ε₁ ≤ Real.sqrt (c / (4 * Real.pi)) := by
        apply Real.sqrt_le_sqrt
        rw [le_div_iff₀ (by positivity)]
        nlinarith [hnum2]
      have h5 : Real.sqrt (c / (4 * Real.pi)) ≤ Real.pi / 2 := by
        have h6 : c / (4 * Real.pi) ≤ (Real.pi / 2) ^ 2 := by
          have hpos : (0 : ℝ) < 4 * Real.pi := by positivity
          exact (div_le_iff₀ hpos).mpr (by nlinarith [hc1, Real.pi_gt_three])
        calc Real.sqrt (c / (4 * Real.pi)) ≤ Real.sqrt ((Real.pi / 2) ^ 2) := Real.sqrt_le_sqrt h6
          _ = Real.pi / 2 := Real.sqrt_sq (by positivity)
      have h7 : Real.pi / 2 ≤ ρ := by
        have h8 : Real.sqrt (c / 2) ≤ 1 / 2 := by
          have : c / 2 ≤ (1/2 : ℝ)^2 := by nlinarith [hc1]
          calc Real.sqrt (c / 2) ≤ Real.sqrt ((1/2:ℝ)^2) := Real.sqrt_le_sqrt this
            _ = 1 / 2 := Real.sqrt_sq (by norm_num)
        have h9 : δ ≤ Real.pi * (1/2) := le_trans hδ (by
          apply mul_le_mul_of_nonneg_left h8 Real.pi_pos.le)
        rw [hρdef]
        linarith
      linarith
    -- the excess bound for both points
    have hzB : rdist (I := I) (M := M) q z ≤ Real.pi + Real.arcsin (2 * ε₁) := hexcess z hz
    have hzB' : rdist (I := I) (M := M) q z' ≤ Real.pi + Real.arcsin (2 * ε₁) := hexcess z' hz'
    -- the projections, and the directions
    obtain ⟨x, hxq, hxz⟩ := sphere_point_near (I := I) (M := M) (cov := cov) hmet htor
      (q := q) (z := z) (ρ := ρ) (B := Real.pi + Real.arcsin (2 * ε₁)) hρpos (by rw [hρdef, hδdef] at hz ⊢; exact hz) hzB
    obtain ⟨x', hx'q, hx'z'⟩ := sphere_point_near (I := I) (M := M) (cov := cov) hmet htor
      (q := q) (z := z') (ρ := ρ) (B := Real.pi + Real.arcsin (2 * ε₁)) hρpos (by rw [hρdef, hδdef] at hz' ⊢; exact hz') hzB'
    obtain ⟨u, hu, hxu, -⟩ := far_sphere_param (I := I) (M := M) (cov := cov) hmet htor
      (q := q) (x := x) (ρ := ρ) hρpos hxq
    obtain ⟨u', hu', hx'u', -⟩ := far_sphere_param (I := I) (M := M) (cov := cov) hmet htor
      (q := q) (x := x') (ρ := ρ) hρpos hx'q
    -- the sphere-size bound
    have hC : 0 ≤ Real.sin ρ + 25 * ε₁ := by
      have : 0 ≤ Real.sin ρ := Real.sin_nonneg_of_nonneg_of_le_pi (le_of_lt hρpos) (by
        rw [hρdef]; linarith [Real.arccos_nonneg (1 - c)])
      linarith
    have hdiff : ∀ (u w : TangentSpace I q), ‖u‖ = 1 → Inner.inner ℝ u w = 0 →
      ‖(mfderiv (modelWithCornersSelf ℝ E) I
          (fun x : E => Submission.GlobalExp.GExp (cov := cov) hmet q
            (ρ • (show TangentSpace I q from x)))
          (show E from u)) (show E from w)‖ ≤ (Real.sin ρ + 25 * ε₁) * ‖w‖ := by
      intro u w hu hw
      exact Work.Diff.C.RadialBound.GExp_radius_mfderiv_bound (I := I) (M := M) (cov := cov)
        hmet htor hα hα1 hc hc1 hε₁ hnum1 hnum2 hsmC hHess hcont hgrad
        (hmod := fun {q} {v} hv {ρ'} hρ'0 hρ'π hρ'e {Z} hJ hZ0 horth =>
          Work.Diff.C.geoCrux.hmod_prop (I := I) (M := M) (cov := cov)
            hmet htor hc hc1 hε₁ hnum2 hsmC hHess hcont hgrad hv hρ'0 hρ'π hρ'e
            hJ hZ0 horth)
        hρpos hρπ hρe hu hw
    have hsph := Work.Diff.C.RadialBound.far_sphere_path_bound (I := I) (M := M) (cov := cov)
      hmet htor hdim2 hρpos hC hdiff hu hu'
    rw [hxu, hx'u'] at hsph
    -- triangle inequality and arithmetic
    have htri1 : rdist (I := I) (M := M) z z' ≤ rdist (I := I) (M := M) z x
        + rdist (I := I) (M := M) x x' + rdist (I := I) (M := M) x' z' := by
      have h1 := Manifold.riemannianEDist_triangle (I := I) (x := z) (y := x) (z := x')
      have h2 := Manifold.riemannianEDist_triangle (I := I) (x := z) (y := x') (z := z')
      have hfin1 : Manifold.riemannianEDist I z x ≠ ⊤ :=
        (Submission.HopfRinow.riemannianEDist_lt_top (I := I) hmet htor z x).ne
      have hfin2 : Manifold.riemannianEDist I x x' ≠ ⊤ :=
        (Submission.HopfRinow.riemannianEDist_lt_top (I := I) hmet htor x x').ne
      have hfin3 : Manifold.riemannianEDist I x' z' ≠ ⊤ :=
        (Submission.HopfRinow.riemannianEDist_lt_top (I := I) hmet htor x' z').ne
      have hfin4 : Manifold.riemannianEDist I z x' ≠ ⊤ :=
        (Submission.HopfRinow.riemannianEDist_lt_top (I := I) hmet htor z x').ne
      have h3 := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfin1, hfin2⟩) h1
      have h4 := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfin4, hfin3⟩) h2
      rw [ENNReal.toReal_add hfin1 hfin2] at h3
      rw [ENNReal.toReal_add hfin4 hfin3] at h4
      simp only [rdist] at h3 h4 ⊢
      linarith
    have hxyz : rdist (I := I) (M := M) z x ≤ δ + Real.arcsin (2 * ε₁) := by
      have h1 : rdist (I := I) (M := M) z x
          ≤ (Real.pi + Real.arcsin (2 * ε₁)) - ρ := by
        have hcomm : rdist (I := I) (M := M) z x = rdist (I := I) (M := M) x z := by
          rw [rdist, rdist, Manifold.riemannianEDist_comm]
        rw [hcomm]
        exact hxz
      have h2 : (Real.pi + Real.arcsin (2 * ε₁)) - ρ = δ + Real.arcsin (2 * ε₁) := by
        rw [hρdef]; ring
      linarith [h1, h2.le, h2.ge]
    have hx'yz : rdist (I := I) (M := M) x' z' ≤ δ + Real.arcsin (2 * ε₁) := by
      have h2 : (Real.pi + Real.arcsin (2 * ε₁)) - ρ = δ + Real.arcsin (2 * ε₁) := by
        rw [hρdef]; ring
      linarith [hx'z', h2.le, h2.ge]
    have hsph' : rdist (I := I) (M := M) x x'
        ≤ (Real.sin ρ + 25 * ε₁) * Real.pi := hsph
    have hsinρ : Real.sin ρ = Real.sin δ := by rw [hρdef, Real.sin_pi_sub]
    have hbound : rdist (I := I) (M := M) z z'
        ≤ 2 * (δ + Real.arcsin (2 * ε₁)) + Real.pi * (Real.sin δ + 25 * ε₁) := by
      have h1 : Real.sin ρ + 25 * ε₁ ≤ Real.sin δ + 25 * ε₁ := by rw [hsinρ]
      have h2 : (Real.sin ρ + 25 * ε₁) * Real.pi = Real.pi * (Real.sin ρ + 25 * ε₁) := by ring
      rw [h2] at hsph'
      nlinarith [htri1, hxyz, hx'yz, hsph', h1, Real.pi_pos]
    have harith := far_ball_arith (c := c) (ε₁ := ε₁) hc hc1 hε₁ hε₂
    rw [← hδdef] at harith
    linarith [hbound, harith]

end Work.Diff.C.geoCrux

namespace Work.Diff.C.geoCrux

theorem far_ball_diam : Work.Diff.C.GeoCrux.FarBallDiamProp := by
  intro E iE1 iE2 iE3 iE4 H iH I M iM1 iM2 iM3 iM4 iRB iCM iBL iNE iCS iPC cov iCD
    hmet htor α c ε₁ hα hα1 hc hc1 hε₁ hnum1 hnum2 p e hON hsmC hHess hcont hgrad hinit hdiam k
    z z' hz hz'
  exact far_ball_of_inputs (I := I) (M := M) (cov := cov) hmet htor hα hα1 hc hc1 hε₁ hnum1 hnum2
    hON hsmC hHess hcont hgrad hinit hdiam
    (fun w hw => far_ball_excess (I := I) (M := M) (cov := cov) hmet htor hα hα1 hc hc1 hε₁ hnum1
      hnum2 hON hsmC hHess hcont hgrad hinit hdiam w hw)
    (fun hd1 w w' hw hw' =>
      dim_one_far_ball (I := I) (M := M) (cov := cov) hmet htor hd1 hdiam w w' hw hw')
    z z' hz hz'

end Work.Diff.C.geoCrux
