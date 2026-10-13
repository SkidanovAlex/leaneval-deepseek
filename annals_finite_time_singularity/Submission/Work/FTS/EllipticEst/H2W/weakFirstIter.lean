import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.Interval.Basic
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.Elliptic.DivSinDefs
import Submission.Work.FTS.EllipticEst.TT.SliceCoercDefs
import Submission.Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo
import Submission.Work.FTS.EllipticEst.H2W.weakSliceDerivBound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W

set_option autoImplicit false

/-- For `0 ≤ s ≤ 1`, `0 < γ` and `γ ≤ 2` one has `s ^ 2 * s ^ (-γ) ≤ 1`: it is the standard
comparison `s ^ (2 - γ) ≤ s ^ 0 = 1` (the case `s = 0` is trivial). -/
private lemma sq_mul_rpow_neg_le_one {s γ : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hγ0 : 0 < γ) (hγ2 : γ ≤ 2) : s ^ 2 * s ^ (-γ) ≤ 1 := by
  rcases eq_or_lt_of_le hs0 with h | h
  · rw [← h, Real.zero_rpow (show (-γ) ≠ 0 by linarith)]
    norm_num
  · rw [show s ^ 2 = s ^ (2 : ℝ) from (Real.rpow_two s).symm,
      ← Real.rpow_add h (2 : ℝ) (-γ), show (2 : ℝ) + -γ = 2 - γ by ring]
    calc s ^ (2 - γ) ≤ s ^ (0 : ℝ) := Real.rpow_le_rpow_of_exponent_ge h hs1 (by linarith)
      _ = 1 := Real.rpow_zero s

/-- **The first angular derivative is bounded by the second one, weakly.**

There is a universal constant `C` (quantified before `α` and `u`) such that for every
`α ∈ (0, 1/4]` and every `u : ℝ → ℝ` which is `C^∞` on `(0, π/2)`, continuous on
`[0, π/2]`, vanishes at both endpoints, and whose second derivative is `L²` for the
weight `sin(2θ)^{-η}` (`η = 99/100`), one has

`∫_{Iθ} (D_θu)² sin(2θ)^{-γ} ≤ C ∫_{Iθ} (u'')² sin(2θ)^{-η}`,  `γ = 1 + α/10`.

This is the *weak* (only two derivatives, no `Lzero1 u` term) form of the first-order
estimate of §H2.  Proof: pointwise `(D_θu)² sin(2θ)^{-γ} = (u')² sin(2θ)^{2-γ} ≤ (u')²`
because `2 - γ ≥ 0` and `sin(2θ) ≤ 1` on `Iθ`; and `(u')²` is bounded on `(0, π/2)` by
`A·B` with `A = ∫_{Iθ}(u'')² sin(2θ)^{-η}` and `B = ∫_{Iθ} sin(2θ)^η ≤ π/2`
(`weakSliceDerivBound`: Rolle for a zero of `u'`, Newton–Leibniz, then Cauchy–Schwarz).
Integrating gives `≤ (π/2)·A·B ≤ (π/2)²·A ≤ 4A` since `(π/2)² ≤ 4 < π²/4`... in fact
`(π/2)² ≤ 4` because `π < 4`. -/
theorem weakFirstIter : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (u : ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
    (∀ n : ℕ, ContDiffOn ℝ n u (Set.Ioo 0 (Real.pi / 2))) →
    ContinuousOn u Work.Spaces.Iθ → u 0 = 0 → u (Real.pi / 2) = 0 →
    MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun t => deriv u t) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ →
    (∫ θ in Work.Spaces.Iθ,
        (Work.Elliptic.Dth1Iter 1 u θ) ^ 2 * Work.FTS.EllipticEst.sGam α θ)
      ≤ C * (∫ θ in Work.Spaces.Iθ,
          (deriv (fun t => deriv u t) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
  refine ⟨4, by norm_num, ?_⟩
  intro α u hα hα4 hu hcont h0 h1 hint
  -- ## The exponents
  have hγpos : 0 < Work.Spaces.gam α := Work.Spaces.gam_pos hα
  have hγ2 : Work.Spaces.gam α ≤ 2 := by
    rw [Work.Spaces.gam]; linarith
  -- ## The two integrals
  set A : ℝ := ∫ θ in Work.Spaces.Iθ,
    (deriv (fun t => deriv u t) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ with hA
  set B : ℝ := ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (Work.Spaces.eta) with hB
  have hvol : (volume : Measure ℝ).real Work.Spaces.Iθ = Real.pi / 2 := by
    rw [MeasureTheory.measureReal_def,
      show (volume : Measure ℝ) Work.Spaces.Iθ = ENNReal.ofReal (Real.pi / 2) from by
        rw [show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (Real.pi / 2) from rfl, Real.volume_Icc,
          sub_zero],
      ENNReal.toReal_ofReal (by positivity)]
  -- ## `A ≥ 0`
  have hAnn : 0 ≤ A := by
    rw [hA]
    refine MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ hθ => ?_)
    exact mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.TT.sEta_nonneg hθ)
  -- ## `B ≤ π/2`
  have hBle : B ≤ Real.pi / 2 := by
    rw [hB]
    have hint1 : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ)) Work.Spaces.Iθ :=
      integrableOn_const (by
        rw [show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (Real.pi / 2) from rfl, Real.volume_Icc,
          sub_zero]
        exact ENNReal.ofReal_ne_top)
    have hle : (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (Work.Spaces.eta))
        ≤ (∫ _ in Work.Spaces.Iθ, (1 : ℝ)) := by
      refine integral_mono_of_nonneg ?_ hint1 ?_
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
        exact Real.rpow_nonneg (Work.FTS.EllipticEst.TT.sin_two_nonneg hθ) _
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
        have hs0 : 0 ≤ Real.sin (2 * θ) := Work.FTS.EllipticEst.TT.sin_two_nonneg hθ
        have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
        have heta : 0 ≤ Work.Spaces.eta := by rw [Work.Spaces.eta]; norm_num
        calc (Real.sin (2 * θ)) ^ (Work.Spaces.eta) ≤ (1 : ℝ) ^ (Work.Spaces.eta) :=
              Real.rpow_le_rpow hs0 hs1 heta
          _ = 1 := Real.one_rpow _
    calc (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (Work.Spaces.eta))
        ≤ (∫ _ in Work.Spaces.Iθ, (1 : ℝ)) := hle
      _ = Real.pi / 2 := by rw [MeasureTheory.setIntegral_const, hvol, smul_eq_mul]; norm_num
  -- ## The pointwise bound `(u')² ≤ A·B` on the open interval
  have hbound : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), (deriv u θ) ^ 2 ≤ A * B := by
    intro θ hθ
    have h := (weakSliceDerivBound u hu hcont h0 h1 hint).1 θ hθ
    simpa [hA, hB] using h
  -- ## The pointwise bound for the target integrand on the open interval
  have hpt_open : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      (Work.Elliptic.Dth1Iter 1 u θ) ^ 2 * Work.FTS.EllipticEst.sGam α θ
        ≤ A * (Real.pi / 2) := by
    intro θ hθ
    have hIθ : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    have hsq : (Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) ≤ 1 :=
      sq_mul_rpow_neg_le_one (Work.FTS.EllipticEst.TT.sin_two_nonneg hIθ)
        (Real.sin_le_one _) hγpos hγ2
    have hderiv : (Work.Elliptic.Dth1Iter 1 u θ) ^ 2 * Work.FTS.EllipticEst.sGam α θ
        ≤ (deriv u θ) ^ 2 := by
      simp only [Work.Elliptic.Dth1Iter_succ, Work.Elliptic.Dth1Iter_zero,
        Work.Elliptic.Dth1, Work.FTS.EllipticEst.sGam]
      rw [mul_pow]
      have hre : (Real.sin (2 * θ)) ^ 2 * (deriv u θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          = (deriv u θ) ^ 2
            * ((Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
        ring
      rw [hre]
      calc (deriv u θ) ^ 2
            * ((Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
          ≤ (deriv u θ) ^ 2 * 1 := mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
        _ = (deriv u θ) ^ 2 := by ring
    have h2 : (deriv u θ) ^ 2 ≤ A * B := hbound θ hθ
    have h3 : A * B ≤ A * (Real.pi / 2) := mul_le_mul_of_nonneg_left hBle hAnn
    linarith
  -- ## The same bound almost everywhere on `Iθ`
  have hae : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      (Work.Elliptic.Dth1Iter 1 u θ) ^ 2 * Work.FTS.EllipticEst.sGam α θ
        ≤ A * (Real.pi / 2) := by
    have h := Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo
      (p := fun θ => (Work.Elliptic.Dth1Iter 1 u θ) ^ 2 * Work.FTS.EllipticEst.sGam α θ
        ≤ A * (Real.pi / 2)) hpt_open
    simpa [Work.Spaces.Iθ] using h
  have hnn : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      0 ≤ (Work.Elliptic.Dth1Iter 1 u θ) ^ 2 * Work.FTS.EllipticEst.sGam α θ := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    exact mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.TT.sGam_nonneg α hθ)
  -- ## Integrating the comparison
  have hIntc : MeasureTheory.IntegrableOn (fun _ : ℝ => A * (Real.pi / 2))
      Work.Spaces.Iθ :=
    integrableOn_const (by
      rw [show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (Real.pi / 2) from rfl, Real.volume_Icc,
        sub_zero]
      exact ENNReal.ofReal_ne_top)
  have hmain := integral_mono_of_nonneg hnn hIntc hae
  have hconstval : (∫ _ in Work.Spaces.Iθ, (A * (Real.pi / 2)))
      = (Real.pi / 2) * (A * (Real.pi / 2)) := by
    rw [MeasureTheory.setIntegral_const, hvol, smul_eq_mul]
  rw [hconstval] at hmain
  -- ## Numerical comparison
  have hπ2 : (Real.pi / 2) ^ 2 ≤ 4 := by nlinarith [Real.pi_lt_four, Real.pi_pos]
  have hfin : (Real.pi / 2) * (A * (Real.pi / 2)) ≤ 4 * A := by
    have heq : (Real.pi / 2) * (A * (Real.pi / 2)) = (Real.pi / 2) ^ 2 * A := by ring
    rw [heq]
    exact mul_le_mul_of_nonneg_right hπ2 hAnn
  linarith [hmain, hfin]

end Work.FTS.EllipticEst.H2W
