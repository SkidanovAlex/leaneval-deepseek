import Submission.Work.RiemLib.ModelPath
import Submission.Work.RiemLib.ExpBound2

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The local hinge comparison (unconditional form)

This file removes the linear-independence hypothesis from
`Submission.ModelPath.edist_expMap_le_model_ind`.  When the two unit vectors `U`, `V` are linearly
dependent they differ by a sign, and the conclusion is the equality case of the triangle inequality:

* `V = U`: both points lie on the same geodesic ray, so their distance is `|r₁ - r₂|`; this is the
  chordal bound `Submission.ExpBound2.edist_expMap_le_chordal` applied to `r₁ • U` and `r₂ • U`;
* `V = -U`: the distance is at most `r₁ + r₂` by the triangle inequality through `x₀`
  (`Submission.ExpBound2.edist_zero_expMap_le`).

In both cases `arccos (cos r₁ cos r₂ ± sin r₁ sin r₂) = |r₁ ∓ r₂|`.

## Main result

* `edist_expMap_le_model` — the local hinge comparison without the linear independence hypothesis.
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
open Submission.ChartBounds
open Submission.Gauss
open Submission.Minimal
open Submission.ModelPath

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

namespace Submission.HingeLocal

noncomputable section

variable [I.Boundaryless]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

/-- `arccos (cos θ) = |θ|` for `θ ∈ [-π, π]`. -/
lemma arccos_cos_eq_abs {θ : ℝ} (h1 : -Real.pi ≤ θ) (h2 : θ ≤ Real.pi) :
    Real.arccos (Real.cos θ) = |θ| := by
  rcases lt_or_ge θ 0 with h | h
  · have h3 : 0 ≤ -θ := by linarith
    have h4 : -θ ≤ Real.pi := by linarith
    rw [abs_of_neg h, ← Real.cos_neg, Real.arccos_cos h3 h4]
  · rw [abs_of_nonneg h]; exact Real.arccos_cos h h2

/-- Two unit vectors that are proportional differ by a sign. -/
lemma eq_or_eq_neg_of_smul_of_units {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {U V : G} (_hU : ‖U‖ = 1) (hV : ‖V‖ = 1) (c : ℝ) (hc : |c| = 1) (h : V = c • U) :
    V = U ∨ V = -U := by
  rcases (abs_eq (show (0 : ℝ) ≤ 1 by norm_num)).mp hc with h1 | h1
  · exact Or.inl (by rw [h, h1, one_smul])
  · exact Or.inr (by rw [h, h1, neg_smul, one_smul])

/-- Two unit vectors of a normed space that are linearly dependent differ by a sign. -/
lemma eq_or_eq_neg_of_dependent {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {U V : G} (hU : ‖U‖ = 1) (hV : ‖V‖ = 1)
    (h : ∃ a b : ℝ, a • U + b • V = 0 ∧ (a ≠ 0 ∨ b ≠ 0)) : V = U ∨ V = -U := by
  obtain ⟨a, b, hab, hne⟩ := h
  have key : ∀ c : ℝ, V = c • U → V = U ∨ V = -U := by
    intro c hc
    have hnorm : |c| = 1 := by
      have h1 : ‖V‖ = ‖c • U‖ := by rw [hc]
      rw [hV, norm_smul, Real.norm_eq_abs, hU, mul_one] at h1
      linarith
    exact eq_or_eq_neg_of_smul_of_units hU hV c hnorm hc
  by_cases hb : b = 0
  · exfalso
    have ha : a ≠ 0 := by
      rcases hne with h' | h'
      · exact h'
      · exact absurd hb h'
    rw [hb, zero_smul, add_zero] at hab
    rcases smul_eq_zero.mp hab with h' | h'
    · exact ha h'
    · rw [h', norm_zero] at hU; norm_num at hU
  · have h2 : b • V = (-a) • U := by
      have h1 : b • V = -(a • U) := (add_eq_zero_iff_eq_neg).mp (by rw [add_comm]; exact hab)
      rw [h1, neg_smul]
    have h3 : b • ((-(a / b)) • U) = (-a) • U := by
      rw [smul_smul]
      congr 1
      field_simp
    have hVc : V = (-(a / b)) • U := by
      have h5 : b • V = b • ((-(a / b)) • U) := by rw [h2, h3]
      have h8 : b • (V - (-(a / b)) • U) = 0 := by rw [smul_sub, h5, sub_self]
      rcases smul_eq_zero.mp h8 with h' | h'
      · exact absurd h' hb
      · exact sub_eq_zero.mp h'
    exact key _ hVc

/-- **The local hinge comparison, unconditional form.**  There is `ρ > 0` such that for all unit
vectors `U`, `V` in `T_{x₀}M` and all `r₁, r₂ ∈ (0, ρ)`,
`d(exp_{x₀}(r₁ U), exp_{x₀}(r₂ V)) ≤ arccos (cos r₁ cos r₂ + sin r₁ sin r₂ ⟪U,V⟫)`. -/
theorem edist_expMap_le_model [Nontrivial E]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (hpinch : QuarterPinched cov)
    (x₀ : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ (r₁ r₂ : ℝ) (U V : TangentSpace I x₀),
      0 < r₁ → r₁ < ρ → 0 < r₂ → r₂ < ρ → ‖U‖ = 1 → ‖V‖ = 1 →
      Manifold.riemannianEDist I (expMap cov x₀ (r₁ • U)) (expMap cov x₀ (r₂ • V))
        ≤ ENNReal.ofReal (Real.arccos (Real.cos r₁ * Real.cos r₂
            + Real.sin r₁ * Real.sin r₂ * inner ℝ U V)) := by
  obtain ⟨ρi, hρi, hind⟩ := edist_expMap_le_model_ind (cov := cov) hmet htor hpinch x₀
  obtain ⟨ρc, hρc, hchord⟩ := Submission.ExpBound2.edist_expMap_le_chordal
    (cov := cov) hmet htor hpinch x₀
  obtain ⟨ρz, hρz, hzero⟩ := Submission.ExpBound2.edist_zero_expMap_le
    (cov := cov) hmet htor hpinch x₀
  refine ⟨min (min ρi ρc) (min ρz (Real.pi / 3)),
    lt_min (lt_min hρi hρc) (lt_min hρz (by linarith [Real.pi_pos])), ?_⟩
  intro r₁ r₂ U V hr1 hr1ρ hr2 hr2ρ hU hV
  have hr1i : r₁ < ρi := lt_of_lt_of_le hr1ρ (le_trans (min_le_left _ _) (min_le_left _ _))
  have hr2i : r₂ < ρi := lt_of_lt_of_le hr2ρ (le_trans (min_le_left _ _) (min_le_left _ _))
  have hr1c : r₁ < ρc := lt_of_lt_of_le hr1ρ (le_trans (min_le_left _ _) (min_le_right _ _))
  have hr2c : r₂ < ρc := lt_of_lt_of_le hr2ρ (le_trans (min_le_left _ _) (min_le_right _ _))
  have hr1z : r₁ < ρz := lt_of_lt_of_le hr1ρ (le_trans (min_le_right _ _) (min_le_left _ _))
  have hr2z : r₂ < ρz := lt_of_lt_of_le hr2ρ (le_trans (min_le_right _ _) (min_le_left _ _))
  have hr1pi : r₁ < Real.pi / 3 :=
    lt_of_lt_of_le hr1ρ (le_trans (min_le_right _ _) (min_le_right _ _))
  have hr2pi : r₂ < Real.pi / 3 :=
    lt_of_lt_of_le hr2ρ (le_trans (min_le_right _ _) (min_le_right _ _))
  have hsum : r₁ + r₂ ≤ Real.pi := by linarith [hr1pi, hr2pi, Real.pi_pos]
  have hsub : |r₁ - r₂| ≤ Real.pi := by
    rw [abs_le]; constructor <;> linarith [hr1pi, hr2pi, Real.pi_pos]
  by_cases hindep : ∀ a b : ℝ, a • U + b • V = 0 → a = 0 ∧ b = 0
  · exact hind r₁ r₂ U V hr1 hr1i hr2 hr2i hU hV hindep
  · have hdep : ∃ a b : ℝ, a • U + b • V = 0 ∧ (a ≠ 0 ∨ b ≠ 0) := by
      by_contra hcon
      push_neg at hcon
      exact hindep fun a b hab => hcon a b hab
    -- the norm of the radial chart data
    have hnorm : ∀ r : ℝ, 0 < r →
        Real.sqrt (chartGram (I := I) x₀ x₀ (r • U) (r • U)) = r := by
      intro r hr
      have h1 : chartGram (I := I) x₀ x₀ (r • U) (r • U) = r ^ 2 := by
        rw [Submission.ModelBound.chartGram_self_eq_norm_sq_fiber, norm_smul, Real.norm_eq_abs,
          hU, mul_one, sq_abs]
      rw [h1, Real.sqrt_sq_eq_abs, abs_of_nonneg hr.le]
    have hnormneg : ∀ r : ℝ, 0 < r →
        Real.sqrt (chartGram (I := I) x₀ x₀ (-(r • U)) (-(r • U))) = r := by
      intro r hr
      have h1 : chartGram (I := I) x₀ x₀ (-(r • U)) (-(r • U)) = r ^ 2 := by
        rw [Submission.ModelBound.chartGram_self_eq_norm_sq_fiber, norm_neg, norm_smul,
          Real.norm_eq_abs, hU, mul_one, sq_abs]
      rw [h1, Real.sqrt_sq_eq_abs, abs_of_nonneg hr.le]
    rcases eq_or_eq_neg_of_dependent hU hV hdep with hVU | hVU
    · -- `V = U`: one geodesic ray
      have hch := hchord (r₁ • U) (r₂ • U) (by rw [hnorm r₁ hr1]; exact hr1c)
        (by rw [hnorm r₂ hr2]; exact hr2c)
      have hval : Real.sqrt (chartGram (I := I) x₀ x₀ (r₂ • U - r₁ • U) (r₂ • U - r₁ • U))
          = |r₁ - r₂| := by
        have hdiff : r₂ • U - r₁ • U = (r₂ - r₁) • U := by module
        rw [hdiff, Submission.ModelBound.chartGram_self_eq_norm_sq_fiber, norm_smul,
          Real.norm_eq_abs, hU, mul_one, Real.sqrt_sq_eq_abs, abs_abs]
        exact abs_sub_comm _ _
      rw [hval] at hch
      have hUU : inner ℝ U U = 1 := by rw [real_inner_self_eq_norm_sq, hU]; norm_num
      have hrhs : Real.arccos (Real.cos r₁ * Real.cos r₂
          + Real.sin r₁ * Real.sin r₂ * inner ℝ U V) = |r₁ - r₂| := by
        rw [hVU, hUU, mul_one, ← Real.cos_sub]
        exact arccos_cos_eq_abs (abs_le.mp hsub).1 (abs_le.mp hsub).2
      rw [hrhs, hVU]
      exact hch
    · -- `V = -U`: triangle inequality through `x₀`
      have hUna : inner ℝ U (-U) = -1 := by
        rw [inner_neg_right, real_inner_self_eq_norm_sq, hU]; norm_num
      have hrhs : Real.arccos (Real.cos r₁ * Real.cos r₂
          + Real.sin r₁ * Real.sin r₂ * inner ℝ U V) = r₁ + r₂ := by
        rw [hVU, hUna]
        have h1 : Real.cos r₁ * Real.cos r₂ + Real.sin r₁ * Real.sin r₂ * (-1)
            = Real.cos (r₁ + r₂) := by rw [Real.cos_add]; ring
        rw [h1, Real.arccos_cos (by linarith) hsum]
      have htri := Manifold.riemannianEDist_triangle (I := I) (x := expMap cov x₀ (r₁ • U))
        (y := x₀) (z := expMap cov x₀ (-(r₂ • U)))
      have h1 : Manifold.riemannianEDist I x₀ (expMap cov x₀ (r₁ • U)) ≤ ENNReal.ofReal r₁ := by
        have h := hzero (r₁ • U) (by rw [hnorm r₁ hr1]; exact hr1z)
        simpa [hnorm r₁ hr1] using h
      have h2 : Manifold.riemannianEDist I x₀ (expMap cov x₀ (-(r₂ • U))) ≤ ENNReal.ofReal r₂ := by
        have h := hzero (-(r₂ • U)) (by rw [hnormneg r₂ hr2]; exact hr2z)
        simpa [hnormneg r₂ hr2] using h
      have h3 : Manifold.riemannianEDist I (expMap cov x₀ (r₁ • U)) (expMap cov x₀ (-(r₂ • U)))
          ≤ ENNReal.ofReal r₁ + ENNReal.ofReal r₂ := by
        refine htri.trans (add_le_add ?_ h2)
        rw [Manifold.riemannianEDist_comm]
        exact h1
      rw [hrhs, hVU, ENNReal.ofReal_add hr1.le hr2.le]
      convert h3 using 1
      rw [smul_neg]

end

end Submission.HingeLocal
