import Submission.HingeLocal
import Submission.GlobalExp
import Submission.Minimising

set_option backward.isDefEq.respectTransparency.types false

/-!
# The hinge-comparison framework

This file sets up the language in which the *global* hinge comparison (Toponogov's theorem for
`sec ≥ 1`) is stated, and proves the local version in that language.

## Contents

* `modelDist1 θ a b` — the model distance of curvature `1` on the unit sphere:
  `arccos (cos a cos b + sin a sin b cos θ)`;
* `hingeAngle v w` — the angle (in `[0,π]`) between two unit tangent vectors, `arccos ⟪v,w⟫`;
* `HingeCompAt z v w a b` — the *hinge comparison* at the apex `z` for the two directions `v`, `w`
  and the two lengths `a`, `b`: `d(exp_z(a v), exp_z(b w)) ≤ modelDist1 (hingeAngle v w) a b`;
* `CompHolds z r` — the comparison holds at `z` for all hinges with `a + b < r` whose sides are
  minimising;
* `compHolds_of_local` — the local comparison (from `Submission.HingeLocal.edist_expMap_le_model`):
  for every point `z` there is `ρ > 0` with `CompHolds z ρ`.

## The globalisation (next step)

The classical *Key Lemma* (see `Submission/Roadmap.lean` §31) extends `CompHolds · ((2/3)l)` at all
points of a ball `B_l(p)` to `CompHolds p l`; iterating it (with the Archimedean property) gives the
comparison for hinges with `a + b < π`, which is what Grove–Shiohama's Step 2 uses.
-/

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal InnerProductSpace
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.ChartConnection
open Submission.Minimal
open Submission.ModelPath
open Submission.GlobalExp

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

namespace Submission.HingeGlobal

noncomputable section

variable [I.Boundaryless]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

/-- The model distance of curvature `1` between two points of the unit sphere at distances `a` and
`b` from the apex and enclosed angle `θ`. -/
def modelDist1 (θ a b : ℝ) : ℝ :=
  Real.arccos (Real.cos a * Real.cos b + Real.sin a * Real.sin b * Real.cos θ)

/-- The angle (in `[0, π]`) between two tangent vectors. -/
def hingeAngle {z : M} (v w : TangentSpace I z) : ℝ := Real.arccos (inner ℝ v w)

@[simp] lemma modelDist1_apply (θ a b : ℝ) :
    modelDist1 θ a b = Real.arccos (Real.cos a * Real.cos b + Real.sin a * Real.sin b * Real.cos θ) := by
  simp only [modelDist1]

@[simp] lemma hingeAngle_apply {z : M} (v w : TangentSpace I z) :
    hingeAngle v w = Real.arccos (inner ℝ v w) := by
  simp only [hingeAngle]

/-- The cosine of the hinge angle of two *unit* vectors is their inner product. -/
lemma cos_hingeAngle {z : M} {v w : TangentSpace I z} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    Real.cos (hingeAngle v w) = inner ℝ v w := by
  have h1 : -1 ≤ inner ℝ v w := by
    have h := abs_real_inner_le_norm v w
    rw [hv, hw, mul_one] at h
    exact neg_le_of_abs_le h
  have h2 : inner ℝ v w ≤ 1 := by
    have h := abs_real_inner_le_norm v w
    rw [hv, hw, mul_one] at h
    exact le_of_abs_le h
  rw [hingeAngle, Real.cos_arccos h1 h2]

/-- **The hinge comparison at the apex `z`**: the distance between the two endpoints of the hinge is
at most the model distance. -/
def HingeCompAt (cov : CovariantDerivative I E (TangentSpace I (M := M))) (z : M)
    (v w : TangentSpace I z) (a b : ℝ) : Prop :=
  Manifold.riemannianEDist I (expMap cov z (a • v)) (expMap cov z (b • w))
    ≤ ENNReal.ofReal (modelDist1 (hingeAngle v w) a b)

/-- **The hinge comparison holds at `z` for all hinges of size `< r`** (the sides being minimising):
this is the `Comparison` predicate of the Key Lemma (`Submission/Roadmap.lean` §31). -/
def CompHolds (cov : CovariantDerivative I E (TangentSpace I (M := M))) (z : M) (r : ℝ) : Prop :=
  ∀ (a b : ℝ) (v w : TangentSpace I z), 0 < a → 0 < b → a + b < r → ‖v‖ = 1 → ‖w‖ = 1 →
    Manifold.riemannianEDist I z (expMap cov z (a • v)) = ENNReal.ofReal a →
    Manifold.riemannianEDist I z (expMap cov z (b • w)) = ENNReal.ofReal b →
    HingeCompAt cov z v w a b

/-- **The local hinge comparison, in the `CompHolds` language.**  Every point has a positive radius
on which the hinge comparison holds.  This is `Submission.HingeLocal.edist_expMap_le_model`
rephrased; the hypothesis that the sides are minimising is part of `CompHolds` and is not needed for
the conclusion (it is simply discarded). -/
theorem compHolds_of_local [Nontrivial E]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (hpinch : QuarterPinched cov)
    (z : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ CompHolds (cov := cov) z ρ := by
  obtain ⟨ρ, hρ, h⟩ := Submission.HingeLocal.edist_expMap_le_model
    (cov := cov) hmet htor hpinch z
  refine ⟨ρ, hρ, fun a b v w ha hb hab hv hw _ _ => ?_⟩
  have haρ : a < ρ := by linarith
  have hbρ : b < ρ := by linarith
  have hmain := h a b v w ha haρ hb hbρ hv hw
  show Manifold.riemannianEDist I (expMap cov z (a • v)) (expMap cov z (b • w))
    ≤ ENNReal.ofReal (Real.arccos (Real.cos a * Real.cos b
        + Real.sin a * Real.sin b * Real.cos (hingeAngle (I := I) v w)))
  rw [cos_hingeAngle hv hw]
  exact hmain


/-- The model angle opposite the side `w` in a model triangle with sides `t`, `s`, `w`. -/
def modelAngle (w t s : ℝ) : ℝ :=
  Real.arccos ((Real.cos w - Real.cos t * Real.cos s) / (Real.sin t * Real.sin s))

/-- **The law of cosines (side form)**, for the model of curvature `1`: the model distance
determined by the angle `modelAngle w t s` and the sides `t`, `s` is `w` again. -/
lemma modelDist1_modelAngle {w t s : ℝ} (hw0 : 0 ≤ w) (hwπ : w ≤ Real.pi)
    (ht : 0 < t) (htπ : t < Real.pi) (hs : 0 < s) (hsπ : s < Real.pi)
    (hlo : |t - s| ≤ w) (hhi : t + s ≤ Real.pi) (hhw : w ≤ t + s) :
    modelDist1 (modelAngle w t s) t s = w := by
  have hsin : 0 < Real.sin t * Real.sin s :=
    mul_pos (Real.sin_pos_of_pos_of_lt_pi ht htπ) (Real.sin_pos_of_pos_of_lt_pi hs hsπ)
  have hup : (Real.cos w - Real.cos t * Real.cos s) / (Real.sin t * Real.sin s) ≤ 1 := by
    rw [div_le_one hsin]
    have h1 : Real.cos w ≤ Real.cos (t - s) := by
      have := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg (t - s)) hwπ hlo
      rwa [Real.cos_abs] at this
    rw [Real.cos_sub] at h1
    linarith
  have hlow : -1 ≤ (Real.cos w - Real.cos t * Real.cos s) / (Real.sin t * Real.sin s) := by
    rw [le_div_iff₀ hsin]
    have h1 : Real.cos (t + s) ≤ Real.cos w :=
      Real.cos_le_cos_of_nonneg_of_le_pi hw0 hhi hhw
    rw [Real.cos_add] at h1
    linarith
  have hst : Real.sin t ≠ 0 := ne_of_gt (Real.sin_pos_of_pos_of_lt_pi ht htπ)
  have hss : Real.sin s ≠ 0 := ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hs hsπ)
  have hcos : Real.cos (modelAngle w t s)
      = (Real.cos w - Real.cos t * Real.cos s) / (Real.sin t * Real.sin s) :=
    Real.cos_arccos hlow hup
  have harg : Real.cos t * Real.cos s + Real.sin t * Real.sin s * Real.cos (modelAngle w t s)
      = Real.cos w := by
    rw [hcos]
    field_simp
    ring
  rw [modelDist1, harg, Real.arccos_cos hw0 hwπ]

/-- **Monotonicity-injectivity of the model distance in the enclosed angle** (for sides in
`(0, π)`): the comparison of the model distances is equivalent to the comparison of the angles. -/
lemma modelDist1_le_iff {a b θ₁ θ₂ : ℝ} (ha : 0 < a) (haπ : a < Real.pi)
    (hb : 0 < b) (hbπ : b < Real.pi) (h₁ : θ₁ ∈ Set.Icc (0 : ℝ) Real.pi)
    (h₂ : θ₂ ∈ Set.Icc (0 : ℝ) Real.pi) :
    modelDist1 θ₁ a b ≤ modelDist1 θ₂ a b ↔ θ₁ ≤ θ₂ := by
  set c₁ : ℝ := Real.cos a * Real.cos b + Real.sin a * Real.sin b * Real.cos θ₁ with hc₁
  set c₂ : ℝ := Real.cos a * Real.cos b + Real.sin a * Real.sin b * Real.cos θ₂ with hc₂
  have hsin : 0 < Real.sin a * Real.sin b :=
    mul_pos (Real.sin_pos_of_pos_of_lt_pi ha haπ) (Real.sin_pos_of_pos_of_lt_pi hb hbπ)
  have hc1mem : c₁ ∈ Set.Icc (-1 : ℝ) 1 := by
    rw [hc₁]
    constructor
    · have h := Real.neg_one_le_cos (a + b)
      rw [Real.cos_add] at h
      nlinarith [hsin, Real.neg_one_le_cos θ₁]
    · have h := Real.cos_le_one (a - b)
      rw [Real.cos_sub] at h
      nlinarith [hsin, Real.cos_le_one θ₁]
  have hc2mem : c₂ ∈ Set.Icc (-1 : ℝ) 1 := by
    rw [hc₂]
    constructor
    · have h := Real.neg_one_le_cos (a + b)
      rw [Real.cos_add] at h
      nlinarith [hsin, Real.neg_one_le_cos θ₂]
    · have h := Real.cos_le_one (a - b)
      rw [Real.cos_sub] at h
      nlinarith [hsin, Real.cos_le_one θ₂]
  have hiff : Real.arccos c₁ ≤ Real.arccos c₂ ↔ c₂ ≤ c₁ :=
    (Real.strictAntiOn_arccos.le_iff_ge hc1mem hc2mem)
  have hcos : c₂ ≤ c₁ ↔ θ₁ ≤ θ₂ := by
    rw [hc₁, hc₂]
    constructor
    · intro h
      have h3 : Real.cos θ₂ ≤ Real.cos θ₁ := by nlinarith [hsin, h]
      exact (Real.strictAntiOn_cos.le_iff_ge h₂ h₁).mp h3
    · intro h
      have h3 : Real.cos θ₂ ≤ Real.cos θ₁ := (Real.strictAntiOn_cos.le_iff_ge h₂ h₁).mpr h
      nlinarith [hsin, h3]
  have hgoal : modelDist1 θ₁ a b = Real.arccos c₁ ∧ modelDist1 θ₂ a b = Real.arccos c₂ := by
    constructor <;> simp only [modelDist1, hc₁, hc₂]
  rw [hgoal.1, hgoal.2]
  exact hiff.trans hcos


/-- **Sub-arcs of a minimising `geodCurve` are minimising.**  This is the basic tool for splitting the
sides of a hinge when globalising the hinge comparison (`Submission/Roadmap.lean` §31). -/
lemma geodCurve_sub_arc_minimising [Nontrivial E] [CompactSpace M]
    (hmet : IsMetricCompatible cov) {T : ℝ} (hT : 0 ≤ T) {x : M} {ξ : TangentSpace I x}
    (hξ : ‖ξ‖ = 1)
    (hmin : Manifold.riemannianEDist I x
      ((geodCurve (cov := cov) hmet T hT x ξ hξ) T) = ENNReal.ofReal T)
    {a b : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) T) (hb : b ∈ Set.Icc (0 : ℝ) T) (hab : a ≤ b) :
    Manifold.riemannianEDist I ((geodCurve (cov := cov) hmet T hT x ξ hξ) a)
      ((geodCurve (cov := cov) hmet T hT x ξ hξ) b) = ENNReal.ofReal (b - a) := by
  obtain ⟨hG0, -, hsm, -, hsp⟩ := geodCurve_spec (cov := cov) hmet T hT x ξ hξ
  have hδ := geodDelta_pos (cov := cov) hmet
  have hIcc : Set.Icc (0 : ℝ) T ⊆
      Set.Ioo (-(geodDelta (cov := cov) hmet)) (T + geodDelta (cov := cov) hmet) := by
    intro t ht
    exact ⟨by linarith [ht.1, hδ], by linarith [ht.2, hδ]⟩
  have hC : CMDiff[Set.Icc (0 : ℝ) T] 1 (geodCurve (cov := cov) hmet T hT x ξ hξ) :=
    (hsm.mono hIcc).of_le (WithTop.coe_le_coe.mpr le_top)
  have hsp' : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ‖curveVelocity (I := I) (geodCurve (cov := cov) hmet T hT x ξ hξ) t‖ = 1 :=
    fun t ht => hsp t (hIcc ht)
  have hmin' : Manifold.riemannianEDist I
      ((geodCurve (cov := cov) hmet T hT x ξ hξ) 0)
      ((geodCurve (cov := cov) hmet T hT x ξ hξ) T) = ENNReal.ofReal T := by
    rw [hG0]; exact hmin
  exact Submission.Minimising.riemannianEDist_eq_ofReal_of_unit_speed_of_minimising
    (I := I) hT hC hsp' hmin' a ha b hb hab

end

end Submission.HingeGlobal
