import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Submission.Work.FTS.StrongEps.JepsHkMem.Jker_comp_zShift_lt_top

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set

namespace Work.FTS.StrongEps.EpsE4Thr.GainDens

set_option maxHeartbeats 800000

/-- Continuity of the rescaled kernel from continuity of the density. -/
private theorem Jker_continuous_of_continuous {σ : ℝ × ℝ → ℝ} (hσc : Continuous σ) (ε : ℝ) :
    Continuous (Work.FTS.StrongEps.Jker σ ε) :=
  continuous_const.mul (hσc.comp (continuous_const_smul _))

/-- **The one-dimensional substitution `u = z * exp (-x)` on `[-ε, ε]`.**  For any
`G : ℝ → ℝ≥0∞` (no measurability needed) and `ε, z > 0`,

  `∫⁻ x in Icc (-ε) ε, G (z * exp (-x)) ≤ (exp ε / z) * ∫⁻ u in Ioi 0, G u`.

The constant is the inverse of the pointwise lower bound `z * exp (-ε)` of the stretching factor
`|d/dx (z exp (-x))| = z exp (-x)`. -/
private lemma lintegral_Icc_expNeg_le {G : ℝ → ENNReal} {ε z : ℝ} (_hε : 0 < ε) (hz : 0 < z) :
    (∫⁻ x in Set.Icc (-ε) ε, G (z * Real.exp (-x)))
      ≤ ENNReal.ofReal (Real.exp ε / z) * ∫⁻ u in Set.Ioi 0, G u := by
  have hzε : 0 < z * Real.exp (-ε) := mul_pos hz (Real.exp_pos _)
  -- the derivative of the substitution
  have hderiv : ∀ x ∈ Set.Icc (-ε) ε,
      HasDerivWithinAt (fun x : ℝ => z * Real.exp (-x)) (-(z * Real.exp (-x)))
        (Set.Icc (-ε) ε) x := by
    intro x _
    have h' : HasDerivAt (fun x : ℝ => Real.exp (-x)) (-Real.exp (-x)) x := by
      have h1 : HasDerivAt (fun x : ℝ => Real.exp (-x)) (Real.exp (-x) * (-1)) x :=
        (Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)
      simpa using h1
    have h2 : HasDerivAt (fun x : ℝ => z * Real.exp (-x)) (-(z * Real.exp (-x))) x := by
      have h3 := h'.const_mul z
      simpa using h3
    exact h2.hasDerivWithinAt
  -- the substitution is injective
  have hinj : Set.InjOn (fun x : ℝ => z * Real.exp (-x)) (Set.Icc (-ε) ε) := by
    intro x _ y _ hxy
    have hexp : Real.exp (-x) = Real.exp (-y) := mul_left_cancel₀ hz.ne' hxy
    have h2 : -x = -y := Real.exp_injective hexp
    linarith
  have hkey := MeasureTheory.lintegral_image_eq_lintegral_abs_deriv_mul
    (s := Set.Icc (-ε) ε) (f := fun x : ℝ => z * Real.exp (-x))
    (f' := fun x : ℝ => -(z * Real.exp (-x))) measurableSet_Icc hderiv hinj G
  have himage_sub : (fun x : ℝ => z * Real.exp (-x)) '' Set.Icc (-ε) ε ⊆ Set.Ioi 0 := by
    rintro u ⟨x, _, rfl⟩
    exact mul_pos hz (Real.exp_pos _)
  have hpt : ∀ x : ℝ, ENNReal.ofReal |(-(z * Real.exp (-x)))| * G (z * Real.exp (-x))
      = ENNReal.ofReal (z * Real.exp (-x)) * G (z * Real.exp (-x)) := by
    intro x
    rw [abs_neg, abs_of_pos (mul_pos hz (Real.exp_pos _))]
  have h1 : ENNReal.ofReal (z * Real.exp (-ε))
        * (∫⁻ x in Set.Icc (-ε) ε, G (z * Real.exp (-x)))
      ≤ ∫⁻ x in Set.Icc (-ε) ε,
          ENNReal.ofReal |(-(z * Real.exp (-x)))| * G (z * Real.exp (-x)) := by
    rw [← lintegral_const_mul' (ENNReal.ofReal (z * Real.exp (-ε)))
      (fun x => G (z * Real.exp (-x))) ENNReal.ofReal_ne_top]
    refine setLIntegral_mono' measurableSet_Icc ?_
    intro x hx
    rw [hpt x]
    refine mul_le_mul_of_nonneg_right ?_ zero_le
    exact ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith [hx.2])) hz.le)
  have h2 : (∫⁻ x in Set.Icc (-ε) ε,
        ENNReal.ofReal |(-(z * Real.exp (-x)))| * G (z * Real.exp (-x)))
      ≤ ∫⁻ u in Set.Ioi 0, G u := by
    rw [← hkey]
    exact lintegral_mono_set himage_sub
  have hfin' : ENNReal.ofReal (z * Real.exp (-ε))
        * (∫⁻ x in Set.Icc (-ε) ε, G (z * Real.exp (-x)))
      ≤ ∫⁻ u in Set.Ioi 0, G u := le_trans h1 h2
  have hne0 : ENNReal.ofReal (z * Real.exp (-ε)) ≠ 0 := by
    rw [ENNReal.ofReal_ne_zero_iff]; exact hzε
  have hneTop : ENNReal.ofReal (z * Real.exp (-ε)) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hstep : (∫⁻ x in Set.Icc (-ε) ε, G (z * Real.exp (-x)))
      ≤ (ENNReal.ofReal (z * Real.exp (-ε)))⁻¹ * ∫⁻ u in Set.Ioi 0, G u := by
    calc (∫⁻ x in Set.Icc (-ε) ε, G (z * Real.exp (-x)))
        = 1 * (∫⁻ x in Set.Icc (-ε) ε, G (z * Real.exp (-x))) := (one_mul _).symm
      _ = (ENNReal.ofReal (z * Real.exp (-ε)))⁻¹ * ENNReal.ofReal (z * Real.exp (-ε))
            * (∫⁻ x in Set.Icc (-ε) ε, G (z * Real.exp (-x))) := by
          rw [ENNReal.inv_mul_cancel hne0 hneTop]
      _ = (ENNReal.ofReal (z * Real.exp (-ε)))⁻¹ *
            (ENNReal.ofReal (z * Real.exp (-ε))
              * (∫⁻ x in Set.Icc (-ε) ε, G (z * Real.exp (-x)))) := by
          rw [mul_assoc]
      _ ≤ (ENNReal.ofReal (z * Real.exp (-ε)))⁻¹ * ∫⁻ u in Set.Ioi 0, G u :=
          mul_le_mul_of_nonneg_left hfin' zero_le
  have hreal : (z * Real.exp (-ε))⁻¹ = Real.exp ε / z := by
    rw [Real.exp_neg, mul_inv, inv_inv, div_eq_mul_inv, mul_comm]
  have hconst_eq : (ENNReal.ofReal (z * Real.exp (-ε)))⁻¹ = ENNReal.ofReal (Real.exp ε / z) := by
    rw [← ENNReal.ofReal_inv_of_pos hzε, hreal]
  rwa [hconst_eq] at hstep

/-- A point of `ℝ²` whose coordinate squares sum to at most `R²` (with `R ≥ 0`) lies in the closed
ball of radius `R`. -/
private lemma mem_closedBall_zero_of_sq_sum_le {x : ℝ × ℝ} {R : ℝ} (hR : 0 ≤ R)
    (h : x.1 ^ 2 + x.2 ^ 2 ≤ R ^ 2) : x ∈ Metric.closedBall (0 : ℝ × ℝ) R := by
  rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]
  have h1 : |x.1| ≤ R := by
    nlinarith [sq_abs x.1, sq_nonneg x.2, abs_nonneg x.1, sq_nonneg (|x.1| - R)]
  have h2 : |x.2| ≤ R := by
    nlinarith [sq_abs x.2, sq_nonneg x.1, abs_nonneg x.2, sq_nonneg (|x.2| - R)]
  simpa only [Real.norm_eq_abs] using max_le h1 h2

/-- **The shifted integral over the ball of radius `ε`.**  For any `G : ℝ → ℝ≥0∞` and
`ε, z > 0`,

  `∫⁻ p in ball 0 ε, G (z * exp (-(p.1))) ≤ (2ε exp ε / z) * ∫⁻ u in Ioi 0, G u`.

The ball is contained in the square `Icc (-ε) ε ×ˢ Icc (-ε) ε`; Tonelli's inequality turns the
`p₂`-integration into the length `2ε` of that interval, and the remaining one-dimensional integral
is controlled by `lintegral_Icc_expNeg_le`. -/
private lemma lintegral_closedBall_zShift_le {G : ℝ → ENNReal} {ε z : ℝ} (hε : 0 < ε)
    (hz : 0 < z) :
    (∫⁻ p in Metric.closedBall (0 : ℝ × ℝ) ε, G (z * Real.exp (-(p.1))))
      ≤ ENNReal.ofReal (2 * ε * (Real.exp ε / z)) * ∫⁻ u in Set.Ioi 0, G u := by
  set s : Set ℝ := Set.Icc (-ε) ε with hs
  set Φ : ℝ × ℝ → ENNReal := fun p => G (z * Real.exp (-(p.1))) with hΦ
  have hΦa : ∀ p : ℝ × ℝ, Φ p = G (z * Real.exp (-(p.1))) := fun p => rfl
  have hball_sub : Metric.closedBall (0 : ℝ × ℝ) ε ⊆ s ×ˢ s := by
    intro p hp
    rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def] at hp
    have hp' : max |p.1| |p.2| ≤ ε := by simpa only [Real.norm_eq_abs] using hp
    have h1 : |p.1| ≤ ε := le_trans (le_max_left _ _) hp'
    have h2 : |p.2| ≤ ε := le_trans (le_max_right _ _) hp'
    rw [hs]
    exact ⟨abs_le.mp h1, abs_le.mp h2⟩
  have hstep2 : (∫⁻ p in Metric.closedBall (0 : ℝ × ℝ) ε, Φ p) ≤ ∫⁻ p in s ×ˢ s, Φ p :=
    lintegral_mono_set hball_sub
  have hstep3 : (∫⁻ p in s ×ˢ s, Φ p)
      = ∫⁻ p, Φ p ∂((volume.restrict s).prod (volume.restrict s)) := by
    rw [Measure.volume_eq_prod ℝ ℝ, Measure.prod_restrict]
  have hstep4 : (∫⁻ p, Φ p ∂((volume.restrict s).prod (volume.restrict s)))
      ≤ ∫⁻ x in s, ∫⁻ y in s, Φ (x, y) := lintegral_prod_le Φ
  have hinner : ∀ x : ℝ, (∫⁻ y in s, Φ (x, y))
      = ENNReal.ofReal (2 * ε) * G (z * Real.exp (-x)) := by
    intro x
    have hpt : ∀ y : ℝ, Φ (x, y) = G (z * Real.exp (-x)) := by intro y; rw [hΦa]
    rw [show (∫⁻ y in s, Φ (x, y)) = ∫⁻ y in s, G (z * Real.exp (-x)) from
      lintegral_congr (fun y => hpt y)]
    rw [setLIntegral_const, hs, Real.volume_Icc]
    have : (ε : ℝ) - -ε = 2 * ε := by ring
    rw [this]
    exact mul_comm _ _
  have hstep5 : (∫⁻ x in s, ∫⁻ y in s, Φ (x, y))
      = ENNReal.ofReal (2 * ε) * ∫⁻ x in s, G (z * Real.exp (-x)) := by
    rw [show (∫⁻ x in s, ∫⁻ y in s, Φ (x, y))
        = ∫⁻ x in s, ENNReal.ofReal (2 * ε) * G (z * Real.exp (-x)) from
      lintegral_congr (fun x => hinner x)]
    exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have hstep6 : (∫⁻ x in s, G (z * Real.exp (-x)))
      ≤ ENNReal.ofReal (Real.exp ε / z) * ∫⁻ u in Set.Ioi 0, G u := by
    simpa only [hs] using lintegral_Icc_expNeg_le (G := G) hε hz
  calc (∫⁻ p in Metric.closedBall (0 : ℝ × ℝ) ε, G (z * Real.exp (-(p.1))))
      = (∫⁻ p in Metric.closedBall (0 : ℝ × ℝ) ε, Φ p) :=
        lintegral_congr (fun p => hΦa p)
    _ ≤ ∫⁻ p in s ×ˢ s, Φ p := hstep2
    _ = ∫⁻ p, Φ p ∂((volume.restrict s).prod (volume.restrict s)) := hstep3
    _ ≤ ∫⁻ x in s, ∫⁻ y in s, Φ (x, y) := hstep4
    _ = ENNReal.ofReal (2 * ε) * ∫⁻ x in s, G (z * Real.exp (-x)) := hstep5
    _ ≤ ENNReal.ofReal (2 * ε) * (ENNReal.ofReal (Real.exp ε / z) * ∫⁻ u in Set.Ioi 0, G u) :=
        mul_le_mul_right hstep6 _
    _ = ENNReal.ofReal (2 * ε * (Real.exp ε / z)) * ∫⁻ u in Set.Ioi 0, G u := by
        rw [ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 * ε by linarith), mul_assoc]

/-- namespace `Work.FTS.StrongEps.EpsE4Thr`, declaration name `Jker_comp_zShift_exp_lt_top`.
This is `JepsHkMem.Jker_comp_zShift_lt_top` with the kernel hypothesis weakened from `IsMollKernel`
to (nonneg, continuous, supported in the closed unit ball) and the extra bounded factor
`ENNReal.ofReal (Real.exp (δ(|p₁|+|p₂|)))`; the latter is `≤ Real.exp (2δε)` whenever
`Jker σ ε p ≠ 0` (support in the ball of radius `ε`), so it can be pulled out as a constant.
Template: `JepsHkMem/Jker_comp_zShift_lt_top.lean` (its private
`lintegral_Icc_expNeg_le` is the key one-dimensional substitution; note that the support
`σ q ≠ 0 → q.1^2 + q.2^2 ≤ 1` transfers to `Jker σ ε p ≠ 0 → p.1^2 + p.2^2 ≤ ε^2`). -/
theorem Jker_comp_zShift_exp_lt_top {σ : ℝ × ℝ → ℝ} (hσ0 : ∀ q : ℝ × ℝ, 0 ≤ σ q)
    (hσc : Continuous σ) (hσs : ∀ q : ℝ × ℝ, σ q ≠ 0 → q.1 ^ 2 + q.2 ^ 2 ≤ 1)
    {ε δ z : ℝ} (hε : 0 < ε) (hδ : 0 ≤ δ) (hz : 0 < z) {G : ℝ → ENNReal}
    (hmeas : AEMeasurable (fun p₁ : ℝ => G (z * Real.exp (-p₁))) MeasureTheory.volume)
    (hfin : (∫⁻ z' in Set.Ioi (0 : ℝ), G z') < ⊤) :
    (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Work.FTS.StrongEps.Jker σ ε p)
      * ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|)))
      * G (z * Real.exp (-(p.1)))) < ⊤ := by
  -- (1) the density is bounded by `M` on the whole plane (it vanishes off the unit ball)
  obtain ⟨Cb, hCb⟩ := (isCompact_closedBall (0 : ℝ × ℝ) 1).exists_bound_of_continuousOn
    hσc.continuousOn
  set M : ℝ := max Cb 0 with hMdef
  have hM0 : 0 ≤ M := le_max_right _ _
  have hMub : ∀ q : ℝ × ℝ, σ q ≤ M := by
    intro q
    by_cases hq : q ∈ Metric.closedBall (0 : ℝ × ℝ) 1
    · have h := hCb q hq
      rw [Real.norm_eq_abs] at h
      exact le_trans (le_abs_self _) (le_trans h (le_max_left _ _))
    · have hzero : σ q = 0 := by
        by_contra hne
        exact hq (mem_closedBall_zero_of_sq_sum_le zero_le_one (by simpa using hσs q hne))
      rw [hzero]
      exact hM0
  -- (2) the pointwise bound for the rescaled kernel
  set C : ℝ := (ε⁻¹) ^ 2 * M with hCdef
  have hC0 : 0 ≤ C := mul_nonneg (sq_nonneg _) hM0
  have hJub : ∀ p : ℝ × ℝ, Work.FTS.StrongEps.Jker σ ε p ≤ C := by
    intro p
    rw [Work.FTS.StrongEps.Jker, hCdef]
    exact mul_le_mul_of_nonneg_left (hMub _) (sq_nonneg _)
  -- (3) where `σ (ε⁻¹ • p)` does not vanish, `p` lies in the ball of radius `ε`
  have hcomp : ∀ p : ℝ × ℝ, σ (ε⁻¹ • p) ≠ 0 → |p.1| ≤ ε ∧ |p.2| ≤ ε := by
    intro p hp
    have hq : (ε⁻¹ • p).1 ^ 2 + (ε⁻¹ • p).2 ^ 2 ≤ (1 : ℝ) ^ 2 := by
      simpa using hσs (ε⁻¹ • p) hp
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at hq
    have hεinv : ε * ε⁻¹ = 1 := mul_inv_cancel₀ hε.ne'
    have key : ∀ a : ℝ, (ε⁻¹ * a) ^ 2 ≤ 1 → |a| ≤ ε := by
      intro a ha
      have h1 : |ε⁻¹ * a| ≤ 1 := by
        nlinarith [ha, abs_nonneg (ε⁻¹ * a), sq_abs (ε⁻¹ * a), sq_nonneg (|ε⁻¹ * a| - 1)]
      rw [abs_mul, abs_of_pos (inv_pos.mpr hε)] at h1
      calc |a| = ε * (ε⁻¹ * |a|) := by rw [← mul_assoc, hεinv, one_mul]
        _ ≤ ε * 1 := mul_le_mul_of_nonneg_left h1 hε.le
        _ = ε := mul_one ε
    exact ⟨key p.1 (by nlinarith [hq, sq_nonneg (ε⁻¹ * p.2)]),
      key p.2 (by nlinarith [hq, sq_nonneg (ε⁻¹ * p.1)])⟩
  have hball_of : ∀ p : ℝ × ℝ, σ (ε⁻¹ • p) ≠ 0 →
      p ∈ Metric.closedBall (0 : ℝ × ℝ) ε := by
    intro p hp
    obtain ⟨h1, h2⟩ := hcomp p hp
    rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]
    simpa only [Real.norm_eq_abs] using max_le h1 h2
  -- (4) the gain is bounded on the support of the rescaled kernel
  have hexp_ball : ∀ p : ℝ × ℝ, σ (ε⁻¹ • p) ≠ 0 →
      Real.exp (δ * (|p.1| + |p.2|)) ≤ Real.exp (δ * (2 * ε)) := by
    intro p hp
    obtain ⟨h1, h2⟩ := hcomp p hp
    refine Real.exp_le_exp.mpr ?_
    nlinarith [hδ, h1, h2, abs_nonneg p.1, abs_nonneg p.2]
  have hJker_nonneg : ∀ p : ℝ × ℝ, 0 ≤ Work.FTS.StrongEps.Jker σ ε p := by
    intro p
    rw [Work.FTS.StrongEps.Jker]
    exact mul_nonneg (sq_nonneg _) (hσ0 _)
  -- (5) the pointwise bound on the full density
  have hkey : ∀ p : ℝ × ℝ, ENNReal.ofReal (Work.FTS.StrongEps.Jker σ ε p)
        * ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|)))
      ≤ ENNReal.ofReal (C * Real.exp (δ * (2 * ε))) := by
    intro p
    rw [← ENNReal.ofReal_mul (hJker_nonneg p)]
    refine ENNReal.ofReal_le_ofReal ?_
    by_cases hp : σ (ε⁻¹ • p) = 0
    · have hz0 : Work.FTS.StrongEps.Jker σ ε p = 0 := by
        simp only [Work.FTS.StrongEps.Jker, hp, mul_zero]
      rw [hz0, zero_mul]
      exact mul_nonneg hC0 (Real.exp_pos _).le
    · exact mul_le_mul (hJub p) (hexp_ball p hp) (Real.exp_pos _).le hC0
  -- (6) reduce the `p`-integral to the ball
  have hpt : ∀ p : ℝ × ℝ, ENNReal.ofReal (Work.FTS.StrongEps.Jker σ ε p)
        * ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|)))
        * G (z * Real.exp (-(p.1)))
      ≤ ENNReal.ofReal (C * Real.exp (δ * (2 * ε)))
        * (Metric.closedBall (0 : ℝ × ℝ) ε).indicator
            (fun p : ℝ × ℝ => G (z * Real.exp (-(p.1)))) p := by
    intro p
    by_cases hp : p ∈ Metric.closedBall (0 : ℝ × ℝ) ε
    · rw [Set.indicator_of_mem hp]
      exact mul_le_mul_left (hkey p) _
    · rw [Set.indicator_of_notMem hp]
      have hz0 : σ (ε⁻¹ • p) = 0 := by
        by_contra hne
        exact hp (hball_of p hne)
      have hpz : Work.FTS.StrongEps.Jker σ ε p = 0 := by
        simp only [Work.FTS.StrongEps.Jker, hz0, mul_zero]
      rw [hpz, ENNReal.ofReal_zero, zero_mul, zero_mul]
      exact zero_le
  have hmain : (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Work.FTS.StrongEps.Jker σ ε p)
        * ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|)))
        * G (z * Real.exp (-(p.1))))
      ≤ ENNReal.ofReal (C * Real.exp (δ * (2 * ε)))
        * ∫⁻ p in Metric.closedBall (0 : ℝ × ℝ) ε, G (z * Real.exp (-(p.1))) := by
    calc (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Work.FTS.StrongEps.Jker σ ε p)
          * ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|)))
          * G (z * Real.exp (-(p.1))))
        ≤ ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (C * Real.exp (δ * (2 * ε)))
            * (Metric.closedBall (0 : ℝ × ℝ) ε).indicator
                (fun p : ℝ × ℝ => G (z * Real.exp (-(p.1)))) p := lintegral_mono hpt
      _ = ENNReal.ofReal (C * Real.exp (δ * (2 * ε)))
            * ∫⁻ p : ℝ × ℝ, (Metric.closedBall (0 : ℝ × ℝ) ε).indicator
                (fun p : ℝ × ℝ => G (z * Real.exp (-(p.1)))) p :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal (C * Real.exp (δ * (2 * ε)))
            * ∫⁻ p in Metric.closedBall (0 : ℝ × ℝ) ε, G (z * Real.exp (-(p.1))) := by
          rw [lintegral_indicator (Metric.isClosed_closedBall.measurableSet)]
  -- (7) finiteness
  have hfinK : ENNReal.ofReal (C * Real.exp (δ * (2 * ε)))
        * (ENNReal.ofReal (2 * ε * (Real.exp ε / z)) * ∫⁻ u in Set.Ioi 0, G u) < ⊤ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin)
  refine lt_of_le_of_lt ?_ hfinK
  exact le_trans hmain
    (mul_le_mul_right (lintegral_closedBall_zShift_le (G := G) hε hz) _)

end Work.FTS.StrongEps.EpsE4Thr.GainDens
