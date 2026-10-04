import Mathlib
import Submission.Work.Diff.C.Lib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.C

set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle Set VectorField CovariantDerivative Metric
open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg Work.Diff.C
open Submission.GlobalExp Submission.HingeGlobal

/-!
# The hinge bound (area C)

`Work.Diff.C.hinge_bound` is the hinge (Toponogov) comparison at a point `x`, in the form needed to
differentiate the model angle `Work.Diff.C.modelF`: if `p` is at distance `d = rdist p x < π` from `x`
and is the endpoint of the geodesic ray in the unit direction `ξ ∈ TₓM`, then for small `|s|`

`rdist p (GExp x (s • V)) ≤ arccos (cos d * cos (s ‖V‖) + sin d * sin (s ‖V‖) * ⟨ξ, V⟩/‖V‖)`,

i.e. the distance is at most the distance in the model space of constant curvature `1`, given by the
spherical law of cosines applied to the hinge with sides `d` and `|s| ‖V‖` and enclosed angle
`∡(ξ, V)`.

This file contains the elementary trigonometric bookkeeping (converting the library's
`modelDist1 (hingeAngle ξ W) d b` into the displayed form), the comparison itself
(`Submission.HingePiece.gcompHolds_pi_apply`, i.e. global Toponogov), and the assembly.
-/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- Trigonometry of the model distance for the hinge direction `V/‖V‖`: the cosine of the hinge
angle of the unit vectors `ξ` and `V/‖V‖` is `⟨ξ, V⟩/‖V‖`. -/
lemma modelDist1_hingeAngle_inv_smul {x : M} [T2Space M] [I.Boundaryless]
    {d : ℝ} {ξ V : TangentSpace I x}
    (hV : V ≠ 0) (hξ : ‖ξ‖ = 1) (s : ℝ) :
    modelDist1 (hingeAngle ξ ((‖V‖)⁻¹ • V)) d (s * ‖V‖)
      = Real.arccos (Real.cos d * Real.cos (s * ‖V‖)
        + Real.sin d * Real.sin (s * ‖V‖) * (Inner.inner ℝ ξ V / ‖V‖)) := by
  have hVpos : 0 < ‖V‖ := norm_pos_iff.mpr hV
  have hw : ‖((‖V‖)⁻¹ • V : TangentSpace I x)‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hVpos)]
    field_simp
  have hc : Real.cos (hingeAngle ξ ((‖V‖)⁻¹ • V)) = Inner.inner ℝ ξ V / ‖V‖ := by
    rw [cos_hingeAngle hξ hw, real_inner_smul_right]
    ring
  rw [modelDist1, hc]

/-- Trigonometry of the model distance for the hinge direction `-V/‖V‖` with side `-s ‖V‖` (the
negative time direction): `cos (-s ‖V‖) = cos (s ‖V‖)` and
`sin (-s ‖V‖) * (-⟨ξ, V⟩/‖V‖) = sin (s ‖V‖) * ⟨ξ, V⟩/‖V‖`. -/
lemma modelDist1_hingeAngle_neg_inv_smul {x : M} [T2Space M] [I.Boundaryless]
    {d s : ℝ} {ξ V : TangentSpace I x}
    (hV : V ≠ 0) (hξ : ‖ξ‖ = 1) :
    modelDist1 (hingeAngle ξ (-((‖V‖)⁻¹ • V))) d ((-s) * ‖V‖)
      = Real.arccos (Real.cos d * Real.cos (s * ‖V‖)
        + Real.sin d * Real.sin (s * ‖V‖) * (Inner.inner ℝ ξ V / ‖V‖)) := by
  have hVpos : 0 < ‖V‖ := norm_pos_iff.mpr hV
  have hw : ‖(-((‖V‖)⁻¹ • V) : TangentSpace I x)‖ = 1 := by
    rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hVpos)]
    field_simp
  have hc : Real.cos (hingeAngle ξ (-((‖V‖)⁻¹ • V))) = -(Inner.inner ℝ ξ V / ‖V‖) := by
    rw [cos_hingeAngle hξ hw, inner_neg_right, real_inner_smul_right]
    ring
  have hcos : Real.cos ((-s) * ‖V‖) = Real.cos (s * ‖V‖) := by
    rw [show (-s) * ‖V‖ = -(s * ‖V‖) by ring, Real.cos_neg]
  have hsin : Real.sin ((-s) * ‖V‖) = -Real.sin (s * ‖V‖) := by
    rw [show (-s) * ‖V‖ = -(s * ‖V‖) by ring, Real.sin_neg]
  rw [modelDist1, hc, hcos, hsin]
  ring_nf

section Geometric

variable [I.Boundaryless] [T2Space M] [CompactSpace M] [Nonempty M] [Nontrivial E]
  [PathConnectedSpace M] [RegularSpace M]

/-- **Toponogov's hinge comparison at `x`, in the form used below.**  If the unit direction `ξ`
reaches `p` (at distance `d = rdist p x > 0`) and `b • W` is a minimising segment of length `b`,
then the distance from `p` to its endpoint is at most the model distance of the hinge. -/
lemma hinge_edist_le_model
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (hpinch : QuarterPinched cov)
    {p x : M} {ξ : TangentSpace I x} (hξ : Inner.inner ℝ ξ ξ = 1)
    (hξp : GExp (cov := cov) hmet x (rdist (I := I) p x • ξ) = p)
    (hd : 0 < rdist (I := I) p x)
    {W : TangentSpace I x} (hW : ‖W‖ = 1) {b : ℝ} (hb : 0 < b)
    (hminW : Manifold.riemannianEDist I x (GExp (cov := cov) hmet x (b • W))
      = ENNReal.ofReal b)
    (hbd : rdist (I := I) p x + b < Real.pi) :
    Manifold.riemannianEDist I p (GExp (cov := cov) hmet x (b • W))
      ≤ ENNReal.ofReal (modelDist1 (hingeAngle ξ W) (rdist (I := I) p x) b) := by
  have hξnorm : ‖ξ‖ = 1 := by
    have h : ‖ξ‖ ^ 2 = (1 : ℝ) := by
      rw [← real_inner_self_eq_norm_sq, hξ]
    nlinarith [norm_nonneg ξ, sq_nonneg (‖ξ‖ - 1)]
  -- the `x`-to-`p` segment is minimising, because `rdist` is *defined* as the (real) distance
  have hmina : Manifold.riemannianEDist I x (GExp (cov := cov) hmet x (rdist (I := I) p x • ξ))
      = ENNReal.ofReal (rdist (I := I) p x) := by
    rw [hξp, Manifold.riemannianEDist_comm, rdist]
    exact (ENNReal.ofReal_toReal (ne_of_lt (Submission.HopfRinow.riemannianEDist_lt_top
      (cov := cov) hmet htor p x))).symm
  have hmain := Submission.HingePiece.gcompHolds_pi_apply (cov := cov) hmet htor hpinch hd hb hbd
    hξnorm hW hmina hminW
  rwa [hξp] at hmain

/-- **The degenerate case `p = x` of the hinge bound**: here the right hand side is
`arccos (cos (s ‖V‖)) = |s| ‖V‖`, and the left hand side is the same by local minimality. -/
lemma rdist_GExp_le_self
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov)
    {p x : M} {V : TangentSpace I x} {ξ : TangentSpace I x} {s : ℝ}
    (hpx : p = x) (hV : V ≠ 0)
    (hmin : Manifold.riemannianEDist I x (GExp (cov := cov) hmet x (s • V))
      = ENNReal.ofReal (|s| * ‖V‖))
    (hsπ : |s| * ‖V‖ < Real.pi) :
    rdist (I := I) p (GExp (cov := cov) hmet x (s • V))
      ≤ Real.arccos (Real.cos (rdist (I := I) p x) * Real.cos (s * ‖V‖)
        + Real.sin (rdist (I := I) p x) * Real.sin (s * ‖V‖)
          * (Inner.inner ℝ ξ V / ‖V‖)) := by
  have hVpos : 0 < ‖V‖ := norm_pos_iff.mpr hV
  have hpx0 : rdist (I := I) p x = 0 := by
    rw [hpx, rdist, Manifold.riemannianEDist_self]
    simp
  have hL : rdist (I := I) p (GExp (cov := cov) hmet x (s • V)) = |s| * ‖V‖ := by
    rw [hpx, rdist, hmin, ENNReal.toReal_ofReal (by positivity)]
  have hR : Real.arccos (Real.cos (rdist (I := I) p x) * Real.cos (s * ‖V‖)
        + Real.sin (rdist (I := I) p x) * Real.sin (s * ‖V‖)
          * (Inner.inner ℝ ξ V / ‖V‖)) = |s| * ‖V‖ := by
    rw [hpx0]
    simp only [Real.cos_zero, Real.sin_zero, one_mul, zero_mul, add_zero]
    have habs : |s * ‖V‖| = |s| * ‖V‖ := by rw [abs_mul, abs_of_pos hVpos]
    rw [← Real.cos_abs (s * ‖V‖),
      Real.arccos_cos (abs_nonneg _) (by rw [habs]; exact le_of_lt hsπ), habs]
  rw [hL, hR]

end Geometric

theorem hinge_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [T2Space M] [CompactSpace M] [Nonempty M] [Nontrivial E]
    [PathConnectedSpace M] [RegularSpace M]
    (cov : CovariantDerivative I E (TangentSpace I (M := M))) [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (hpinch : QuarterPinched cov)
    (p x : M) (hπ : rdist (I := I) p x < Real.pi)
    (ξ : TangentSpace I x) (hξ : Inner.inner ℝ ξ ξ = 1)
    (hξp : GExp (cov := cov) hmet x (rdist (I := I) p x • ξ) = p)
    (V : TangentSpace I x) (hV : V ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, |s| < ε →
      rdist (I := I) p (GExp (cov := cov) hmet x (s • V)) ≤
        Real.arccos (Real.cos (rdist (I := I) p x) * Real.cos (s * ‖V‖)
          + Real.sin (rdist (I := I) p x) * Real.sin (s * ‖V‖)
            * (Inner.inner ℝ ξ V / ‖V‖)) := by
  classical
  have hVpos : 0 < ‖V‖ := norm_pos_iff.mpr hV
  have hξnorm : ‖ξ‖ = 1 := by
    have h : ‖ξ‖ ^ 2 = (1 : ℝ) := by
      rw [← real_inner_self_eq_norm_sq, hξ]
    nlinarith [norm_nonneg ξ, sq_nonneg (‖ξ‖ - 1)]
  have hd0 : 0 ≤ rdist (I := I) p x := ENNReal.toReal_nonneg
  -- local minimality of the ray `s ↦ GExp x (s • V)` in both time directions
  obtain ⟨ρ, hρ, hρmin⟩ := Submission.GlobalExp.exists_pos_riemannianEDist_GExp_smul
    (cov := cov) hmet htor x
  have hshort : ∀ s : ℝ, |s| < ρ / ‖V‖ →
      Manifold.riemannianEDist I x (GExp (cov := cov) hmet x (s • V))
        = ENNReal.ofReal (|s| * ‖V‖) := by
    intro s hs
    have hsρ : |s| * ‖V‖ < ρ := by
      rw [lt_div_iff₀ hVpos] at hs
      linarith
    by_cases hs0 : 0 ≤ s
    · have hsabs : |s| = s := abs_of_nonneg hs0
      have h2 : Manifold.riemannianEDist I x (GExp (cov := cov) hmet x (s • V))
          = ENNReal.ofReal (s * ‖V‖) := by
        have h3 := hρmin V hV s hs0 (by rwa [hsabs] at hsρ)
        simpa only [norm_smul, Real.norm_eq_abs, hsabs] using h3
      rw [hsabs]
      exact h2
    · have hsneg' : s < 0 := not_le.mp hs0
      have hsabs : |s| = -s := abs_of_neg hsneg'
      have h2 : Manifold.riemannianEDist I x (GExp (cov := cov) hmet x (s • V))
          = ENNReal.ofReal ((-s) * ‖V‖) := by
        have h3 := hρmin (-V) (neg_ne_zero.mpr hV) (-s) (by linarith) (by
          rw [norm_neg]
          rwa [hsabs] at hsρ)
        rw [show (-s) • (-V) = s • V by rw [smul_neg, neg_smul, neg_neg]] at h3
        simpa only [norm_smul, Real.norm_eq_abs, hsabs] using h3
      rw [hsabs]
      exact h2
  refine ⟨min (ρ / ‖V‖) ((Real.pi - rdist (I := I) p x) / (2 * ‖V‖)),
    lt_min (div_pos hρ hVpos) (div_pos (sub_pos.mpr hπ) (mul_pos two_pos hVpos)), ?_⟩
  intro s hs
  have hs1 : |s| < ρ / ‖V‖ := lt_of_lt_of_le hs (min_le_left _ _)
  have hs2 : |s| < (Real.pi - rdist (I := I) p x) / (2 * ‖V‖) :=
    lt_of_lt_of_le hs (min_le_right _ _)
  have hmshort : Manifold.riemannianEDist I x (GExp (cov := cov) hmet x (s • V))
      = ENNReal.ofReal (|s| * ‖V‖) := hshort s hs1
  -- `|s| ‖V‖ < π - d`
  have hsπ : |s| * ‖V‖ < Real.pi - rdist (I := I) p x := by
    rw [lt_div_iff₀ (mul_pos two_pos hVpos)] at hs2
    linarith
  rcases lt_trichotomy s 0 with hsneg | hszero | hspos
  · -- negative time
    rcases eq_or_lt_of_le hd0 with hd_eq | hd_pos
    · -- degenerate: `p = x`
      have hπ0 : |s| * ‖V‖ < Real.pi := by
        rw [← hd_eq, sub_zero] at hsπ
        exact hsπ
      exact rdist_GExp_le_self (cov := cov) (p := p) (x := x) (V := V) (ξ := ξ) (s := s) hmet
        (by rw [← hξp, ← hd_eq, zero_smul, GExp_zero]) hV hmshort hπ0
    · have hbw : ((-s) * ‖V‖) • (-((‖V‖)⁻¹ • V)) = s • V := by
        rw [smul_neg, smul_smul, ← neg_smul]
        congr 1
        rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt hVpos), mul_one, neg_neg]
      have hW : ‖(-((‖V‖)⁻¹ • V) : TangentSpace I x)‖ = 1 := by
        rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hVpos)]
        field_simp
      have hb : 0 < (-s) * ‖V‖ := mul_pos (neg_pos.mpr hsneg) hVpos
      have hminW : Manifold.riemannianEDist I x
          (GExp (cov := cov) hmet x (((-s) * ‖V‖) • (-((‖V‖)⁻¹ • V))))
          = ENNReal.ofReal ((-s) * ‖V‖) := by
        rw [hbw, hmshort, abs_of_neg hsneg]
      have hbd : rdist (I := I) p x + ((-s) * ‖V‖) < Real.pi := by
        rw [abs_of_neg hsneg] at hsπ
        linarith
      have hcomp := hinge_edist_le_model (cov := cov) hmet htor hpinch hξ hξp hd_pos hW hb
        hminW hbd
      rw [hbw] at hcomp
      calc rdist (I := I) p (GExp (cov := cov) hmet x (s • V))
          = (Manifold.riemannianEDist I p (GExp (cov := cov) hmet x (s • V))).toReal := by
            rw [rdist]
        _ ≤ (ENNReal.ofReal (modelDist1 (hingeAngle ξ (-((‖V‖)⁻¹ • V)))
              (rdist (I := I) p x) ((-s) * ‖V‖))).toReal :=
            ENNReal.toReal_mono ENNReal.ofReal_ne_top hcomp
        _ = modelDist1 (hingeAngle ξ (-((‖V‖)⁻¹ • V))) (rdist (I := I) p x) ((-s) * ‖V‖) :=
            ENNReal.toReal_ofReal (Real.arccos_nonneg _)
        _ = Real.arccos (Real.cos (rdist (I := I) p x) * Real.cos (s * ‖V‖)
              + Real.sin (rdist (I := I) p x) * Real.sin (s * ‖V‖)
                * (Inner.inner ℝ ξ V / ‖V‖)) :=
            modelDist1_hingeAngle_neg_inv_smul (x := x) hV hξnorm
  · -- zero time: both sides are `rdist p x`
    rw [hszero]
    rw [zero_smul, GExp_zero]
    simp only [mul_zero, Real.cos_zero, Real.sin_zero, mul_one, zero_mul, add_zero]
    exact le_of_eq (Real.arccos_cos hd0 (le_of_lt hπ)).symm
  · -- positive time
    rcases eq_or_lt_of_le hd0 with hd_eq | hd_pos
    · -- degenerate: `p = x`
      have hπ0 : |s| * ‖V‖ < Real.pi := by
        rw [← hd_eq, sub_zero] at hsπ
        exact hsπ
      exact rdist_GExp_le_self (cov := cov) (p := p) (x := x) (V := V) (ξ := ξ) (s := s) hmet
        (by rw [← hξp, ← hd_eq, zero_smul, GExp_zero]) hV hmshort hπ0
    · have hbw : (s * ‖V‖) • ((‖V‖)⁻¹ • V) = s • V := by
        rw [smul_smul]
        congr 1
        rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt hVpos), mul_one]
      have hW : ‖((‖V‖)⁻¹ • V : TangentSpace I x)‖ = 1 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hVpos)]
        field_simp
      have hb : 0 < s * ‖V‖ := mul_pos hspos hVpos
      have hminW : Manifold.riemannianEDist I x
          (GExp (cov := cov) hmet x ((s * ‖V‖) • ((‖V‖)⁻¹ • V)))
          = ENNReal.ofReal (s * ‖V‖) := by
        rw [hbw, hmshort, abs_of_pos hspos]
      have hbd : rdist (I := I) p x + s * ‖V‖ < Real.pi := by
        rw [abs_of_pos hspos] at hsπ
        linarith
      have hcomp := hinge_edist_le_model (cov := cov) hmet htor hpinch hξ hξp hd_pos hW hb
        hminW hbd
      rw [hbw] at hcomp
      calc rdist (I := I) p (GExp (cov := cov) hmet x (s • V))
          = (Manifold.riemannianEDist I p (GExp (cov := cov) hmet x (s • V))).toReal := by
            rw [rdist]
        _ ≤ (ENNReal.ofReal (modelDist1 (hingeAngle ξ ((‖V‖)⁻¹ • V))
              (rdist (I := I) p x) (s * ‖V‖))).toReal :=
            ENNReal.toReal_mono ENNReal.ofReal_ne_top hcomp
        _ = modelDist1 (hingeAngle ξ ((‖V‖)⁻¹ • V)) (rdist (I := I) p x) (s * ‖V‖) :=
            ENNReal.toReal_ofReal (Real.arccos_nonneg _)
        _ = Real.arccos (Real.cos (rdist (I := I) p x) * Real.cos (s * ‖V‖)
              + Real.sin (rdist (I := I) p x) * Real.sin (s * ‖V‖)
                * (Inner.inner ℝ ξ V / ‖V‖)) :=
            modelDist1_hingeAngle_inv_smul (x := x) hV hξnorm s

end Work.Diff.C
