import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.PressureOn.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Set

namespace Work.FTS.PressureOn.Weyl

/-- **From the coordinatewise fundamental theorem of calculus to a Fréchet derivative.**

If the difference quotients of `q` along the three coordinate directions are the integrals
of the corresponding components of a *continuous* field `Φ`, then `q` is differentiable
everywhere with derivative `w ↦ ⟪Φ x, w⟫` (i.e. the linear functional `innerSL ℝ (Φ x)`).

The proof is the standard one: telescoping along the three coordinate directions expresses
`q (x + v) - q x` as a sum of three one-dimensional integrals, and continuity of `Φ` at `x`
makes each of them differ from the corresponding linear term by `o(‖v‖)`. -/
theorem hasFDerivAt_of_fTC
    (q : Work.FTS.PressureOn.R3 → ℝ)
    (Φ : Work.FTS.PressureOn.R3 → Work.FTS.PressureOn.R3) (hΦ : Continuous Φ)
    (hFTC : ∀ x : Work.FTS.PressureOn.R3, ∀ t : ℝ, ∀ i : Fin 3,
      q (x + t • FiniteTimeSingularity.e i) - q x
        = ∫ s in (0 : ℝ)..t, Φ (x + s • FiniteTimeSingularity.e i) i) :
    ∀ x, HasFDerivAt q (innerSL ℝ (Φ x)) x := by
  intro x
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  -- a modulus of continuity of `Φ` at `x`
  obtain ⟨δ, hδpos, hδ⟩ : ∃ δ > 0, ∀ z, ‖z - x‖ < δ → ‖Φ z - Φ x‖ < c / 3 := by
    obtain ⟨δ, hδpos, hδ⟩ := Metric.continuousAt_iff.mp hΦ.continuousAt (c / 3) (by linarith)
    exact ⟨δ, hδpos, fun z hz => by simpa [dist_eq_norm] using hδ hz⟩
  filter_upwards [Metric.ball_mem_nhds (0 : R3) (by linarith : (0 : ℝ) < δ / 3)] with v hv
  rw [Metric.mem_ball, dist_zero_right] at hv
  -- expansion of `v` in the standard orthonormal basis
  have hsum : (∑ i : Fin 3, v i • FiniteTimeSingularity.e i) = v := by
    trans (∑ i, ((EuclideanSpace.basisFun (Fin 3) ℝ).repr v).ofLp i
        • (EuclideanSpace.basisFun (Fin 3) ℝ) i : R3)
    · refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply]; rfl
    · exact OrthonormalBasis.sum_repr _ v
  have hv3 : v = v 0 • FiniteTimeSingularity.e 0 + v 1 • FiniteTimeSingularity.e 1
      + v 2 • FiniteTimeSingularity.e 2 := by
    conv_lhs => rw [← hsum]
    rw [Fin.sum_univ_three]
  have hin : ∀ a b : ℝ, inner ℝ a b = b * a := by intro a b; simp
  have hL : (innerSL ℝ (Φ x)) v = (Φ x) 2 * v 2 + (Φ x) 1 * v 1 + (Φ x) 0 * v 0 := by
    rw [innerSL_apply_apply, PiLp.inner_apply, Fin.sum_univ_three]
    simp only [hin]
    ring
  have hnormsq_le : ∀ i : Fin 3, |v i| ≤ ‖v‖ := fun i => by
    have h := PiLp.norm_apply_le (β := fun _ : Fin 3 => ℝ) v i
    simpa using h
  have henorm : ∀ i : Fin 3, ‖FiniteTimeSingularity.e i‖ = 1 := fun i => by
    rw [FiniteTimeSingularity.e, PiLp.toLp_single, PiLp.norm_single]; simp
  -- telescoping along the three coordinate directions
  have hQ : q (x + v) - q x
      = (∫ s in (0 : ℝ)..(v 2), Φ (x + v 0 • FiniteTimeSingularity.e 0
            + v 1 • FiniteTimeSingularity.e 1 + s • FiniteTimeSingularity.e 2) 2)
      + (∫ s in (0 : ℝ)..(v 1), Φ (x + v 0 • FiniteTimeSingularity.e 0
            + s • FiniteTimeSingularity.e 1) 1)
      + (∫ s in (0 : ℝ)..(v 0), Φ (x + s • FiniteTimeSingularity.e 0) 0) := by
    conv_lhs => rw [hv3]
    rw [show x + (v 0 • FiniteTimeSingularity.e 0 + v 1 • FiniteTimeSingularity.e 1
          + v 2 • FiniteTimeSingularity.e 2)
        = x + v 0 • FiniteTimeSingularity.e 0 + v 1 • FiniteTimeSingularity.e 1
          + v 2 • FiniteTimeSingularity.e 2 from by abel]
    have H0 := hFTC x (v 0) (0 : Fin 3)
    have H1 := hFTC (x + v 0 • FiniteTimeSingularity.e 0) (v 1) (1 : Fin 3)
    have H2 := hFTC (x + v 0 • FiniteTimeSingularity.e 0 + v 1 • FiniteTimeSingularity.e 1)
      (v 2) (2 : Fin 3)
    linarith [H0, H1, H2]
  -- the individual one-dimensional estimates
  have hterm : ∀ (y : R3) (k : Fin 3), ‖y - x‖ ≤ 2 * ‖v‖ →
      ‖(∫ s in (0 : ℝ)..(v k), Φ (y + s • FiniteTimeSingularity.e k) k)
          - (Φ x) k * v k‖ ≤ (c / 3) * |v k| := by
    intro y k hy
    have hcont : Continuous fun s : ℝ => Φ (y + s • FiniteTimeSingularity.e k) k :=
      (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) k).comp
        (hΦ.comp (continuous_const.add (continuous_id.smul continuous_const)))
    have hsub : (∫ s in (0 : ℝ)..(v k), Φ (y + s • FiniteTimeSingularity.e k) k)
          - (Φ x) k * v k
        = ∫ s in (0 : ℝ)..(v k), (Φ (y + s • FiniteTimeSingularity.e k) k - (Φ x) k) := by
      rw [intervalIntegral.integral_sub (hcont.intervalIntegrable 0 (v k))
          (continuous_const.intervalIntegrable 0 (v k)),
        intervalIntegral.integral_const, sub_zero, smul_eq_mul]
      ring
    rw [hsub]
    have hbound : ∀ s ∈ Set.uIoc (0 : ℝ) (v k),
        ‖Φ (y + s • FiniteTimeSingularity.e k) k - (Φ x) k‖ ≤ c / 3 := by
      intro s hs
      have hk := hnormsq_le k
      have hs1 : |s| ≤ |v k| := by
        have hmem : s ∈ Set.uIcc (0 : ℝ) (v k) := Set.uIoc_subset_uIcc hs
        rw [Set.mem_uIcc] at hmem
        rcases hmem with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [abs_of_nonneg h1, abs_of_nonneg (le_trans h1 h2)]
          exact h2
        · rw [abs_of_nonpos h2, abs_of_nonpos (le_trans h1 h2)]
          linarith
      have hs2 : ‖y + s • FiniteTimeSingularity.e k - x‖ < δ := by
        rw [show y + s • FiniteTimeSingularity.e k - x
            = (y - x) + s • FiniteTimeSingularity.e k from by abel]
        have hsk : ‖s • FiniteTimeSingularity.e k‖ = |s| := by
          rw [norm_smul, Real.norm_eq_abs, henorm k, mul_one]
        calc ‖(y - x) + s • FiniteTimeSingularity.e k‖
            ≤ ‖y - x‖ + ‖s • FiniteTimeSingularity.e k‖ := norm_add_le _ _
          _ ≤ 3 * ‖v‖ := by rw [hsk]; linarith
          _ < δ := by linarith
      have hΦz := hδ _ hs2
      calc ‖Φ (y + s • FiniteTimeSingularity.e k) k - (Φ x) k‖
          = ‖(Φ (y + s • FiniteTimeSingularity.e k) - Φ x) k‖ := by simp
        _ ≤ ‖Φ (y + s • FiniteTimeSingularity.e k) - Φ x‖ := by
              simpa using PiLp.norm_apply_le (Φ (y + s • FiniteTimeSingularity.e k) - Φ x) k
        _ ≤ c / 3 := le_of_lt hΦz
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := v k)
      (C := c / 3) hbound
    simpa using hb
  have e0 := hnormsq_le 0
  have e1 := hnormsq_le 1
  have e2 := hnormsq_le 2
  have ht2 := hterm (x + v 0 • FiniteTimeSingularity.e 0 + v 1 • FiniteTimeSingularity.e 1) 2 (by
      rw [show x + v 0 • FiniteTimeSingularity.e 0 + v 1 • FiniteTimeSingularity.e 1 - x
          = v 0 • FiniteTimeSingularity.e 0 + v 1 • FiniteTimeSingularity.e 1 from by abel]
      calc ‖v 0 • FiniteTimeSingularity.e 0 + v 1 • FiniteTimeSingularity.e 1‖
          ≤ ‖v 0 • FiniteTimeSingularity.e 0‖ + ‖v 1 • FiniteTimeSingularity.e 1‖ :=
            norm_add_le _ _
        _ = |v 0| + |v 1| := by
            rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, henorm 0, henorm 1]
            ring
        _ ≤ 2 * ‖v‖ := by linarith)
  have ht1 := hterm (x + v 0 • FiniteTimeSingularity.e 0) 1 (by
      rw [show x + v 0 • FiniteTimeSingularity.e 0 - x = v 0 • FiniteTimeSingularity.e 0 from
          by abel,
        norm_smul, Real.norm_eq_abs, henorm 0, mul_one]
      linarith [norm_nonneg v])
  have ht0 := hterm x 0 (by
      rw [sub_self, norm_zero]; linarith [norm_nonneg v])
  have hres : q (x + v) - q x - (innerSL ℝ (Φ x)) v
      = ((∫ s in (0 : ℝ)..(v 2), Φ (x + v 0 • FiniteTimeSingularity.e 0
            + v 1 • FiniteTimeSingularity.e 1 + s • FiniteTimeSingularity.e 2) 2)
          - (Φ x) 2 * v 2)
        + ((∫ s in (0 : ℝ)..(v 1), Φ (x + v 0 • FiniteTimeSingularity.e 0
            + s • FiniteTimeSingularity.e 1) 1) - (Φ x) 1 * v 1)
        + ((∫ s in (0 : ℝ)..(v 0), Φ (x + s • FiniteTimeSingularity.e 0) 0)
          - (Φ x) 0 * v 0) := by
    rw [hQ, hL]; ring
  set A2 : ℝ := (∫ s in (0 : ℝ)..(v 2), Φ (x + v 0 • FiniteTimeSingularity.e 0
            + v 1 • FiniteTimeSingularity.e 1 + s • FiniteTimeSingularity.e 2) 2)
          - (Φ x) 2 * v 2 with hA2
  set A1 : ℝ := (∫ s in (0 : ℝ)..(v 1), Φ (x + v 0 • FiniteTimeSingularity.e 0
            + s • FiniteTimeSingularity.e 1) 1) - (Φ x) 1 * v 1 with hA1
  set A0 : ℝ := (∫ s in (0 : ℝ)..(v 0), Φ (x + s • FiniteTimeSingularity.e 0) 0)
        - (Φ x) 0 * v 0 with hA0
  calc ‖q (x + v) - q x - (innerSL ℝ (Φ x)) v‖
      = ‖A2 + A1 + A0‖ := by rw [hres]
    _ ≤ ‖A2‖ + ‖A1‖ + ‖A0‖ := by
        linarith [norm_add_le (A2 + A1) A0, norm_add_le A2 A1]
    _ ≤ (c / 3) * |v 2| + (c / 3) * |v 1| + (c / 3) * |v 0| := by linarith [ht2, ht1, ht0]
    _ ≤ (c / 3) * (3 * ‖v‖) := by nlinarith [hc, e0, e1, e2, norm_nonneg v]
    _ = c * ‖v‖ := by ring

end Work.FTS.PressureOn.Weyl
