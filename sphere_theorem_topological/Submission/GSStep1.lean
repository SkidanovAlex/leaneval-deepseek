import Submission.GSConcaveGen

/-!
# Grove–Shiohama step 1 (uniqueness of the maximum) for the full diameter range `π/2 < D < π`

`Submission/GSCritical.step1_diameter_unique` proves that the maximum of `d(p,·)` is attained at a
unique point, but only for `D ≤ 2π/3`, because it uses the two-sided hinge inequality at the
midpoint `m` of a minimising geodesic between two maximal points, which needs
`ℓ/2 + d(p,m) ≤ π`.

The restriction is removed here:

* the *unrestricted* concavity of `d(p,·)` (`GSConcaveGen.concaveOn_dist_geodCurve_of_lt_pi`)
  forces `d(p,·) ≡ D` on any minimising geodesic between two maximal points;
* the two hinge comparisons at an *interior* point `z` of that geodesic, with two *small* opposite
  rays (`a ≤ (π - D)/2`), then give `cos θ < 0` and, for the opposite direction, `cos θ > 0`, where
  `θ` is the angle between the ray and a shortest geodesic from `z` to `p`.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 2000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal InnerProductSpace
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.GlobalExp
open Submission.HingeGlobal
open Submission.HingeKey
open Submission.HingePiece
open Submission.HingeClosed
open Submission.HopfRinow

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

namespace Submission.GSStep1

noncomputable section

variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

/-- **The two hinge comparisons at a point at maximal distance are incompatible.**  If `z`, `x`,
`y` and `p` satisfy `d(z,p) = d(x,p) = d(y,p) = D` with `π/2 < D < π`, where `x` and `y` are the
two ends at distance `a > 0` of a minimising geodesic through `z` (`a + D ≤ π`), and all the
relevant distances are realised by minimising geodesics, then this is impossible.

Indeed the hinge comparison at `z` (with the shortest direction to `p`) applied to `x` gives
`cos θ < 0` for the hinge angle `θ`, while applied to `y` (whose hinge angle is `π - θ`) gives
`cos θ > 0`. -/
theorem not_both_eq_of_hinge_pair
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (hpinch : QuarterPinched cov)
    [PathConnectedSpace M] [RegularSpace M]
    {z x y p : M} {a D : ℝ} {ux up : TangentSpace I z}
    (ha : 0 < a) (haD : a + D ≤ Real.pi)
    (hDgt : Real.pi / 2 < D) (hDπ : D < Real.pi)
    (hux : ‖ux‖ = 1) (hup : ‖up‖ = 1)
    (hx : x = GExp (cov := cov) hmet z (a • ux))
    (hy : y = GExp (cov := cov) hmet z (a • (-ux)))
    (hp : p = GExp (cov := cov) hmet z (D • up))
    (hzx : Manifold.riemannianEDist I z x = ENNReal.ofReal a)
    (hzy : Manifold.riemannianEDist I z y = ENNReal.ofReal a)
    (hzp : Manifold.riemannianEDist I z p = ENNReal.ofReal D)
    (hxp : Manifold.riemannianEDist I x p = ENNReal.ofReal D)
    (hyp : Manifold.riemannianEDist I y p = ENNReal.ofReal D) : False := by
  have hDpos : 0 < D := by linarith [Real.pi_pos]
  have hDle : D ≤ Real.pi := hDπ.le
  have hD2π : D < Real.pi + Real.pi / 2 := by linarith [Real.pi_pos]
  have hcosDneg : Real.cos D < 0 := Real.cos_neg_of_pi_div_two_lt_of_lt hDgt hD2π
  have hsinapos : 0 < Real.sin a := Real.sin_pos_of_pos_of_lt_pi ha (by linarith)
  have hsinDpos : 0 < Real.sin D := Real.sin_pos_of_pos_of_lt_pi hDpos hDπ
  have hcosa1 : Real.cos a < 1 := by
    nlinarith [Real.sin_sq_add_cos_sq a, hsinapos]
  have hux' : ‖(-ux : TangentSpace I z)‖ = 1 := by rw [norm_neg]; exact hux
  -- the two hinge comparisons
  have hH1 := gcompHolds_pi_le (cov := cov) hmet htor hpinch (z := z) ha hDpos haD hux hup
    (by rw [← hx]; exact hzx) (by rw [← hp]; exact hzp)
  have hH2 := gcompHolds_pi_le (cov := cov) hmet htor hpinch (z := z) ha hDpos haD hux' hup
    (by rw [← hy]; exact hzy) (by rw [← hp]; exact hzp)
  have hr1 : D ≤ modelDist1 (hingeAngle ux up) a D := by
    have h := hH1
    rw [← hx, ← hp, hxp] at h
    exact (ENNReal.ofReal_le_ofReal_iff (modelDist1_nonneg _ _ _)).mp h
  have hr2 : D ≤ modelDist1 (hingeAngle (-ux) up) a D := by
    have h := hH2
    rw [← hy, ← hp, hyp] at h
    exact (ENNReal.ofReal_le_ofReal_iff (modelDist1_nonneg _ _ _)).mp h
  -- the cosine bounds
  have hDmem : D ∈ Set.Icc (0:ℝ) Real.pi := ⟨hDpos.le, hDle⟩
  have hc1 : Real.cos a * Real.cos D + Real.sin a * Real.sin D * Real.cos (hingeAngle ux up)
      ≤ Real.cos D := by
    have hm : modelDist1 (hingeAngle ux up) a D ∈ Set.Icc (0:ℝ) Real.pi :=
      ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩
    have h := Real.antitoneOn_cos hDmem hm hr1
    rw [modelDist1] at h
    rw [Commons.Geometry.Sphere.modelDist_cos (a := a) (b := D) (θ := hingeAngle ux up)
      (le_of_lt ha) (by linarith [haD, hDpos]) hDpos.le hDle
      (Real.arccos_nonneg _) (Real.arccos_le_pi _)] at h
    exact h
  have hc2 : Real.cos a * Real.cos D + Real.sin a * Real.sin D * Real.cos (hingeAngle (-ux) up)
      ≤ Real.cos D := by
    have hm : modelDist1 (hingeAngle (-ux) up) a D ∈ Set.Icc (0:ℝ) Real.pi :=
      ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩
    have h := Real.antitoneOn_cos hDmem hm hr2
    rw [modelDist1] at h
    rw [Commons.Geometry.Sphere.modelDist_cos (a := a) (b := D) (θ := hingeAngle (-ux) up)
      (le_of_lt ha) (by linarith [haD, hDpos]) hDpos.le hDle
      (Real.arccos_nonneg _) (Real.arccos_le_pi _)] at h
    exact h
  -- the angle of the opposite ray
  have hcos' : Real.cos (hingeAngle (-ux) up) = - Real.cos (hingeAngle ux up) := by
    have e1 : Real.cos (hingeAngle (-ux) up) = inner ℝ (-ux) up := cos_hingeAngle hux' hup
    have e2 : inner ℝ (-ux) up = -inner ℝ ux up := inner_neg_left _ _
    have e3 : Real.cos (hingeAngle ux up) = inner ℝ ux up := cos_hingeAngle hux hup
    rw [e1, e2, e3]
  -- from the first: `cos θ < 0`
  have hneg1 : Real.cos (hingeAngle ux up) < 0 := by
    have h1 : Real.sin a * Real.sin D * Real.cos (hingeAngle ux up)
        ≤ Real.cos D * (1 - Real.cos a) := by nlinarith [hc1]
    have h2 : Real.cos D * (1 - Real.cos a) < 0 :=
      mul_neg_of_neg_of_pos hcosDneg (by linarith)
    have h3 : Real.sin a * Real.sin D * Real.cos (hingeAngle ux up) < 0 := lt_of_le_of_lt h1 h2
    have hsp : 0 < Real.sin a * Real.sin D := mul_pos hsinapos hsinDpos
    nlinarith [h3, hsp]
  have hneg2 : Real.cos (hingeAngle (-ux) up) < 0 := by
    have h1 : Real.sin a * Real.sin D * Real.cos (hingeAngle (-ux) up)
        ≤ Real.cos D * (1 - Real.cos a) := by nlinarith [hc2]
    have h2 : Real.cos D * (1 - Real.cos a) < 0 :=
      mul_neg_of_neg_of_pos hcosDneg (by linarith)
    have h3 : Real.sin a * Real.sin D * Real.cos (hingeAngle (-ux) up) < 0 := lt_of_le_of_lt h1 h2
    have hsp : 0 < Real.sin a * Real.sin D := mul_pos hsinapos hsinDpos
    nlinarith [h3, hsp]
  rw [hcos'] at hneg2
  linarith


/-- **Grove–Shiohama step 1 for the full range `π/2 < D < π`.**  If `D` bounds all mutual distances
and `d(p,·)` attains the value `D` at two distinct points `q₁ ≠ q₂`, with `π/2 < D < π`, this is
impossible. -/
theorem step1_diameter_unique_of_lt_pi
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (hpinch : QuarterPinched cov)
    [PathConnectedSpace M] [RegularSpace M]
    {p q₁ q₂ : M} {D : ℝ}
    (hdiam : ∀ r s : M, Manifold.riemannianEDist I r s ≤ ENNReal.ofReal D)
    (hDgt : Real.pi / 2 < D) (hDπ : D < Real.pi)
    (hq₁ : Manifold.riemannianEDist I p q₁ = ENNReal.ofReal D)
    (hq₂ : Manifold.riemannianEDist I p q₂ = ENNReal.ofReal D)
    (hne : q₁ ≠ q₂) : False := by
  haveI : IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x) :=
    Submission.EDist.isContinuousRiemannianBundle_infty (I := I)
  have hDnn : 0 ≤ D := le_trans (by linarith [Real.pi_pos]) hDgt.le
  -- the length `ℓ` of a minimising geodesic from `q₁` to `q₂`
  have hqfin : Manifold.riemannianEDist I q₁ q₂ ≠ ⊤ :=
    (lt_of_le_of_lt (hdiam q₁ q₂) ENNReal.ofReal_lt_top).ne
  set ℓ : ℝ := (Manifold.riemannianEDist I q₁ q₂).toReal with hℓdef
  have hℓ : Manifold.riemannianEDist I q₁ q₂ = ENNReal.ofReal ℓ :=
    (ENNReal.ofReal_toReal hqfin).symm
  have hℓle : ℓ ≤ D := by
    rw [hℓdef, ← ENNReal.toReal_ofReal hDnn]
    exact ENNReal.toReal_mono ENNReal.ofReal_ne_top (hdiam q₁ q₂)
  have hℓnn : 0 ≤ ℓ := by rw [hℓdef]; exact ENNReal.toReal_nonneg
  have hℓpos : 0 < ℓ := by
    rcases eq_or_lt_of_le hℓnn with h0 | h0
    · have hz : Manifold.riemannianEDist I q₁ q₂ = 0 := by
        rw [hℓ, ← h0, ENNReal.ofReal_zero]
      exact absurd ((Submission.EDist.riemannianEDist_eq_zero_iff (I := I)).mp hz) hne
    · exact h0
  obtain ⟨v, hvG, hvd⟩ :=
    Submission.HopfRinow.exists_geodesic_riemannianEDist_eq (cov := cov) hmet htor q₁ q₂
  have hnorm : ‖v‖ = ℓ := by
    rw [hℓ] at hvd
    exact (ENNReal.ofReal_eq_ofReal_iff (norm_nonneg v) hℓnn).mp hvd.symm
  have hvne : v ≠ 0 := by intro h0; rw [h0, norm_zero] at hnorm; linarith
  set ξ : TangentSpace I q₁ := unitOf v hvne with hξdef
  have hξ1 : ‖ξ‖ = 1 := unitOf_norm v hvne
  have hℓξ : ℓ • ξ = v := by
    rw [hξdef, unitOf, show ℓ = ‖v‖ from hnorm.symm, smul_smul,
      mul_inv_cancel₀ (norm_ne_zero_iff.mpr hvne), one_smul]
  set G : ℝ → M := geodCurve (cov := cov) hmet ℓ hℓnn q₁ ξ hξ1 with hGdef
  have hG0 : G 0 = q₁ := (geodCurve_spec (cov := cov) hmet ℓ hℓnn q₁ ξ hξ1).1
  have hGℓ : G ℓ = q₂ := by
    rw [hGdef]
    rw [← GExp_eq_geodCurve (cov := cov) hmet (x := q₁) (u := ξ) hξ1 (T := ℓ) hℓnn
      (r := ℓ) hℓnn le_rfl, hℓξ, hvG]
  have hminℓ : Manifold.riemannianEDist I q₁ (G ℓ) = ENNReal.ofReal ℓ := by rw [hGℓ, hℓ]
  have hsub : ∀ a ∈ Set.Icc (0:ℝ) ℓ, ∀ b ∈ Set.Icc (0:ℝ) ℓ, a ≤ b →
      Manifold.riemannianEDist I (G a) (G b) = ENNReal.ofReal (b - a) := by
    have h := geodCurve_sub_arc_minimising' (cov := cov) hmet (T := ℓ) hℓnn hξ1 (s := ℓ) hℓnn
      le_rfl hminℓ
    intro a ha b hb hab
    simp only [hGdef]
    exact h a ha b hb hab
  -- the distance function along the segment
  set F : ℝ → ℝ := fun t : ℝ => (Manifold.riemannianEDist I p (G t)).toReal with hFdef
  have hGcont : ContinuousOn G (Set.Icc (0:ℝ) ℓ) := by
    have hδ := geodDelta_pos (cov := cov) hmet
    have hsm : ContMDiffOn 𝓘(ℝ) I ∞ G
        (Set.Ioo (-(geodDelta (cov := cov) hmet)) (ℓ + geodDelta (cov := cov) hmet)) := by
      rw [hGdef]; exact (geodCurve_spec (cov := cov) hmet ℓ hℓnn q₁ ξ hξ1).2.2.1
    have hsub' : Set.Icc (0:ℝ) ℓ ⊆
        Set.Ioo (-(geodDelta (cov := cov) hmet)) (ℓ + geodDelta (cov := cov) hmet) := by
      intro t ht; exact ⟨by linarith [ht.1, hδ], by linarith [ht.2, hδ]⟩
    exact ((hsm.mono hsub').continuousOn)
  have hcont : ContinuousOn F (Set.Icc (0:ℝ) ℓ) := by
    have h1 : ContinuousOn (fun t : ℝ => Manifold.riemannianEDist I p (G t))
        (Set.Icc (0:ℝ) ℓ) :=
      ((Submission.HopfRinow.continuous_riemannianEDist_left (I := I) p).continuousOn).comp
        hGcont (fun t _ => Set.mem_univ _)
    have h2 : ∀ t ∈ Set.Icc (0:ℝ) ℓ, Manifold.riemannianEDist I p (G t) ≠ ⊤ := fun t ht =>
      (lt_of_le_of_lt (hdiam p (G t)) ENNReal.ofReal_lt_top).ne
    exact ENNReal.continuousOn_toReal.comp h1 (fun t ht => h2 t ht)
  have hbd : ∀ t ∈ Set.Icc (0:ℝ) ℓ, F t ≤ D := by
    intro t ht
    calc F t ≤ (ENNReal.ofReal D).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top (hdiam p (G t))
      _ = D := ENNReal.toReal_ofReal hDnn
  have hF0 : F 0 = D := by rw [hFdef]; simp only [hG0, hq₁, ENNReal.toReal_ofReal hDnn]
  have hFℓ : F ℓ = D := by rw [hFdef]; simp only [hGℓ, hq₂, ENNReal.toReal_ofReal hDnn]
  have hfar0 : Real.pi / 2 < F 0 := by rw [hF0]; exact hDgt
  have hfarℓ : Real.pi / 2 < F ℓ := by rw [hFℓ]; exact hDgt
  have hℓπ : ℓ ≤ Real.pi := le_of_lt (lt_of_le_of_lt hℓle hDπ)
  have hfar :=
    Submission.GSConcaveSeg.far_of_far_endpoints (cov := cov) hmet htor hpinch hξ1
      hℓnn hℓπ hDπ.le hminℓ hcont hbd hfar0 hfarℓ
  have hlt : ∀ t ∈ Set.Icc (0:ℝ) ℓ, F t < Real.pi := fun t ht => lt_of_le_of_lt (hbd t ht) hDπ
  have hconc :=
    Submission.GSConcaveGen.concaveOn_dist_geodCurve_of_lt_pi (cov := cov) hmet htor hpinch hξ1
      hℓnn hminℓ hcont hfar hlt
  -- concavity forces the distance to be constantly `D`
  have hconst : ∀ t ∈ Set.Icc (0:ℝ) ℓ, F t = D := by
    intro t ht
    have hge : D ≤ F t := by
      have hmem0 : (0:ℝ) ∈ Set.Icc 0 ℓ := ⟨le_refl 0, hℓnn⟩
      have hmemℓ : ℓ ∈ Set.Icc (0:ℝ) ℓ := ⟨hℓnn, le_refl ℓ⟩
      have hu : t / ℓ ∈ Set.Icc (0:ℝ) 1 :=
        ⟨div_nonneg ht.1 hℓnn, (div_le_one hℓpos).mpr ht.2⟩
      have h := hconc.2 hmem0 hmemℓ (by linarith [hu.2] : (0:ℝ) ≤ 1 - t / ℓ) hu.1
        (by ring : (1:ℝ) - t / ℓ + t / ℓ = 1)
      have harg : (1 - t / ℓ) • (0:ℝ) + (t / ℓ) • ℓ = t := by
        rw [smul_eq_mul, smul_eq_mul, mul_zero, zero_add, div_mul_cancel₀ _ hℓpos.ne']
      rw [harg] at h
      simp only [smul_eq_mul] at h
      have e0 : (Manifold.riemannianEDist I p
          (geodCurve (cov := cov) hmet ℓ hℓnn q₁ ξ hξ1 0)).toReal = D := by
        simpa only [hFdef, hGdef] using hF0
      have eℓ : (Manifold.riemannianEDist I p
          (geodCurve (cov := cov) hmet ℓ hℓnn q₁ ξ hξ1 ℓ)).toReal = D := by
        simpa only [hFdef, hGdef] using hFℓ
      rw [e0, eℓ] at h
      have hD : D ≤ (Manifold.riemannianEDist I p
          (geodCurve (cov := cov) hmet ℓ hℓnn q₁ ξ hξ1 t)).toReal := by linarith
      simpa only [hFdef, hGdef] using hD
    exact le_antisymm (hbd t ht) hge
  have hval : ∀ t ∈ Set.Icc (0:ℝ) ℓ,
      (Manifold.riemannianEDist I p
        (geodCurve (cov := cov) hmet ℓ hℓnn q₁ ξ hξ1 t)).toReal = D :=
    fun t ht => hconst t ht
  -- an interior point with two small opposite rays
  set t₀ : ℝ := ℓ / 2 with ht₀def
  have ht₀0 : 0 < t₀ := by rw [ht₀def]; linarith
  have ht₀ℓ : t₀ ≤ ℓ := by rw [ht₀def]; linarith
  set a : ℝ := min (ℓ / 4) ((Real.pi - D) / 2) with hadef
  have hapos : 0 < a := by
    rw [hadef]; exact lt_min (by linarith) (by linarith)
  have haℓ : a ≤ ℓ / 4 := le_trans (min_le_left _ _) le_rfl
  have haπ : a ≤ (Real.pi - D) / 2 := le_trans (min_le_right _ _) le_rfl
  have haD : a + D ≤ Real.pi := by linarith
  have ht₀a0 : 0 ≤ t₀ - a := by linarith
  have ht₀aℓ : t₀ + a ≤ ℓ := by linarith
  have hat₀ : a ≤ t₀ := by linarith
  have ht₀mem : t₀ ∈ Set.Icc (0:ℝ) ℓ := ⟨ht₀0.le, ht₀ℓ⟩
  have hmemx : t₀ + a ∈ Set.Icc (0:ℝ) ℓ := ⟨by linarith, ht₀aℓ⟩
  have hmemy : t₀ - a ∈ Set.Icc (0:ℝ) ℓ := ⟨ht₀a0, by linarith⟩
  -- the geometry at `z = G t₀`
  set vel : TangentSpace I (G t₀) := curveVelocity (I := I) G t₀ with hveldef
  have hvel1 : ‖vel‖ = 1 := by
    rw [hveldef]
    exact norm_curveVelocity_geodCurve (cov := cov) hmet hℓnn q₁ ξ hξ1 ht₀0.le ht₀ℓ
  have hx : G (t₀ + a) = GExp (cov := cov) hmet (G t₀) (a • vel) := by
    rw [hveldef]
    exact (GExp_add_curveVelocity_geodCurve (cov := cov) hmet hξ1 hℓnn ht₀0.le ht₀ℓ
      hapos.le ht₀aℓ).symm
  have hy : G (t₀ - a) = GExp (cov := cov) hmet (G t₀) (a • (-vel)) := by
    rw [hveldef]
    exact (GExp_neg_curveVelocity_geodCurve (cov := cov) hmet hξ1 hℓnn ht₀0.le ht₀ℓ
      hapos.le hat₀).symm
  -- Hopf–Rinow from `z` to `p`
  obtain ⟨vp, hpG, hpd⟩ :=
    Submission.HopfRinow.exists_geodesic_riemannianEDist_eq (cov := cov) hmet htor (G t₀) p
  have hfinz : Manifold.riemannianEDist I p (G t₀) ≠ ⊤ :=
    (lt_of_le_of_lt (hdiam p (G t₀)) ENNReal.ofReal_lt_top).ne
  have hzp : Manifold.riemannianEDist I (G t₀) p = ENNReal.ofReal D := by
    rw [Manifold.riemannianEDist_comm, ← ENNReal.ofReal_toReal hfinz, hval t₀ ht₀mem]
  have hnormvp : ‖vp‖ = D := by
    have h : ENNReal.ofReal ‖vp‖ = ENNReal.ofReal D := by rw [← hpd, hzp]
    exact (ENNReal.ofReal_eq_ofReal_iff (norm_nonneg vp) hDnn).mp h
  have hvpn : vp ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hnormvp; linarith
  set up : TangentSpace I (G t₀) := unitOf vp hvpn with hupdef
  have hup1 : ‖up‖ = 1 := unitOf_norm vp hvpn
  have huup : D • up = vp := by
    rw [hupdef, show D = ‖vp‖ from hnormvp.symm, unitOf, smul_smul,
      mul_inv_cancel₀ (norm_ne_zero_iff.mpr hvpn), one_smul]
  have hp : p = GExp (cov := cov) hmet (G t₀) (D • up) := by rw [huup]; exact hpG.symm
  exact not_both_eq_of_hinge_pair (cov := cov) hmet htor hpinch (z := G t₀)
    (x := G (t₀ + a)) (y := G (t₀ - a)) (p := p) (ux := vel) (up := up)
    hapos haD hDgt hDπ hvel1 hup1 hx hy hp
    (by rw [hsub t₀ ht₀mem (t₀ + a) hmemx (by linarith),
      show t₀ + a - t₀ = a from by ring])
    (by rw [Manifold.riemannianEDist_comm, hsub (t₀ - a) hmemy t₀ ht₀mem (by linarith),
      show t₀ - (t₀ - a) = a from by ring])
    hzp
    (by
      have hfin : Manifold.riemannianEDist I p (G (t₀ + a)) ≠ ⊤ :=
        (lt_of_le_of_lt (hdiam p (G (t₀ + a))) ENNReal.ofReal_lt_top).ne
      have h1 : Manifold.riemannianEDist I (G (t₀ + a)) p
          = ENNReal.ofReal ((Manifold.riemannianEDist I p (G (t₀ + a))).toReal) := by
        rw [Manifold.riemannianEDist_comm]
        exact (ENNReal.ofReal_toReal hfin).symm
      rw [h1]
      congr 1
      exact hval _ hmemx)
    (by
      have hfin : Manifold.riemannianEDist I p (G (t₀ - a)) ≠ ⊤ :=
        (lt_of_le_of_lt (hdiam p (G (t₀ - a))) ENNReal.ofReal_lt_top).ne
      have h1 : Manifold.riemannianEDist I (G (t₀ - a)) p
          = ENNReal.ofReal ((Manifold.riemannianEDist I p (G (t₀ - a))).toReal) := by
        rw [Manifold.riemannianEDist_comm]
        exact (ENNReal.ofReal_toReal hfin).symm
      rw [h1]
      congr 1
      exact hval _ hmemy)

end

end Submission.GSStep1
