import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.EllipticEst.Prop.angIbpWild

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.EllipticEst.Prop.mixedSlotInterpEta`

The mixed-slot interpolation at level `0`, with the **gamma weight** on the left and the **eta
weights** on the right:

`∫∫ (D_z∂_θG)² w² sin(2θ)^{2-γ} ≤ C (HkSq α 0 (D_z²G) + HkSq α 0 (∂_θ²G) + HkSq α 0 (D_zG))`,

for `G` smooth on the open quadrant, vanishing on the two angular boundary lines, and with the three
`ℋ⁰`-slots honest (`HkMem α 0`).

## Status and route

The statement is TRUE, but its proof is the *wild-class* two-integration-by-parts argument of the
paper's §Elliptic estimates, whose two analytic ingredients are the endpoint-flux analyses.  The
complete route, the obstacles (including two refuted candidate flux lemmas), and the delivered
companion lemmas are recorded in `NOTES_mixedSlotInterpEta.md` (same directory).  In short:

* `Work.FTS.EllipticEst.Prop.radialIbpWild` — **PROVED**, the radial IBP with the `w²` weight and the
  flux as an explicit hypothesis (`Submission/Work/FTS/EllipticEst/Prop/radialIbpWild.lean`);
* `Work.FTS.EllipticEst.Prop.angIbpWild` — **PROVED**, the angular IBP with the weight `sin(2θ)^p`,
  `p < 1`, and the endpoint flux as an explicit hypothesis
  (`Submission/Work/FTS/EllipticEst/Prop/angIbpWild.lean`; reviewed twice as correct);
* the *naive* hope that the two endpoint fluxes vanish under the target's hypotheses is **refuted**
  (notes file §5: counterexamples `g ≡ 1`, and bump families of height `x_n^{(1-p)/2}` at `x_n ↓ 0`), so
  the two identities cannot simply be applied slicewise;
* the remaining work is therefore the *case analysis* of the slices whose angular flux fails to vanish
  (flat/spiky slices: there the `cot²`-slot — hence the identity's slack term — degenerates, while the
  left-hand side is small) plus the `∫⁻`-level (junk-free) bookkeeping — see the notes file.

The two lemmas proved below are the elementary inputs of the final assembly (the weight comparison and
the weighted AM–GM closing step).
-/

namespace Work.FTS.EllipticEst.Prop

open scoped Real Topology
open MeasureTheory Filter

/-- **Weight comparison.**  On the angular interval the `γ`-weight `sin(2θ)^{2-γ}` is dominated by the
`η`-weight `sin(2θ)^{-η}` (both exponents are `≥ -η`, and `sin(2θ) ≤ 1`).  This is what allows all the
slot integrals appearing on the right-hand side of the interpolation (which carry the `η`-weight) to
dominate the `γ`-weighted quantities on the left. -/
theorem gam_weight_le_eta {α θ : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
  have hs0 : 0 ≤ Real.sin (2 * θ) := by
    rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
    exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos])
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  rcases hs0.eq_or_lt with h | h
  · rw [← h]
    have h1 : (0 : ℝ) ^ (2 - Work.Spaces.gam α) = 0 :=
      Real.zero_rpow (by rw [Work.Spaces.gam]; linarith)
    have h2 : (0 : ℝ) ^ (-(Work.Spaces.eta)) = 0 :=
      Real.zero_rpow (by linarith [Work.Spaces.eta_pos])
    rw [h1, h2]
  · have hlog : Real.log (Real.sin (2 * θ)) ≤ 0 := Real.log_nonpos h.le hs1
    have hcoef : 0 ≤ 2 - Work.Spaces.gam α + Work.Spaces.eta := by
      rw [Work.Spaces.gam, Work.Spaces.eta]; linarith
    have hkey : Real.log (Real.sin (2 * θ)) * (2 - Work.Spaces.gam α + Work.Spaces.eta) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hlog hcoef
    have hfac : (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
        = Real.exp (Real.log (Real.sin (2 * θ)) * (2 - Work.Spaces.gam α)) := by
      rw [Real.rpow_def_of_pos h]
    have hfac2 : (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        = Real.exp (Real.log (Real.sin (2 * θ)) * (-(Work.Spaces.eta))) := by
      rw [Real.rpow_def_of_pos h]
    rw [hfac, hfac2]
    refine Real.exp_le_exp.mpr ?_
    nlinarith [hkey]

/-- **The closing AM–GM step of the assembly.**  If the three honest slot values `dd`, `tt`, `d` give
the two pairings `√(dd·tt)` and `3√(d·tt)` (which is how the two integrations by parts produce the
right-hand side), then they are absorbed by `½dd + 2tt + (3/2)d`. -/
theorem amgm_three {dd tt d : ℝ} (hdd : 0 ≤ dd) (htt : 0 ≤ tt) (hd : 0 ≤ d) :
    Real.sqrt (dd * tt) + 3 * Real.sqrt (d * tt) ≤ dd / 2 + 2 * tt + (3 / 2) * d := by
  have h1 : Real.sqrt (dd * tt) ≤ (dd + tt) / 2 := by
    rw [Real.sqrt_mul hdd tt]
    nlinarith [sq_nonneg (Real.sqrt dd - Real.sqrt tt), Real.sq_sqrt hdd, Real.sq_sqrt htt]
  have h2 : 3 * Real.sqrt (d * tt) ≤ (3 / 2) * d + (3 / 2) * tt := by
    rw [Real.sqrt_mul hd tt]
    nlinarith [sq_nonneg (Real.sqrt d - Real.sqrt tt), Real.sq_sqrt hd, Real.sq_sqrt htt]
  linarith

/-- **The angular integration by parts with the weight `μ = sin(2θ)^{2-γ}`** (`γ > 1`), i.e. the
specialisation `p := 2 - γ` of the *proved* `Work.FTS.EllipticEst.Prop.angIbpWild`:

`∫ (f')² μ = -∫ f f'' μ - 2(2-γ) ∫ f² μ - 2(2-γ)(γ-1) ∫ f² cot²(2θ) μ`.

The point of the `γ`-weight (rather than the `η`-weight) is that **both coefficients of the
correction terms are negative**: `2 - γ > 0` and `γ - 1 > 0`.  Hence, whenever the identity
applies, `∫ (f')² μ ≤ -∫ f f'' μ` — the pairing that the *radial* integration by parts converts
into the good pairings `√(dd·tt)` and `3√(d·tt)` of the target. -/
theorem angIbpMu {γ : ℝ} (hγ : 1 < γ) (hγ2 : γ < 2) {f : ℝ → ℝ}
    (hsm : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)))
    (hI0 : IntegrableOn (fun θ => (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ)) Work.Spaces.Iθ)
    (hI1 : IntegrableOn (fun θ => (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ)) Work.Spaces.Iθ)
    (hI2 : IntegrableOn (fun θ => f θ * deriv (deriv f) θ * (Real.sin (2 * θ)) ^ (2 - γ))
      Work.Spaces.Iθ)
    (hI3 : IntegrableOn (fun θ => (f θ) ^ 2 * (Real.cot (2 * θ)) ^ 2
      * (Real.sin (2 * θ)) ^ (2 - γ)) Work.Spaces.Iθ)
    (hfl0 : Tendsto (fun θ => (Real.sin (2 * θ)) ^ (2 - γ)
      * (f θ * deriv f θ - (2 - γ) * Real.cot (2 * θ) * (f θ) ^ 2))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hfl1 : Tendsto (fun θ => (Real.sin (2 * θ)) ^ (2 - γ)
      * (f θ * deriv f θ - (2 - γ) * Real.cot (2 * θ) * (f θ) ^ 2))
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) :
    (∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ))
      = -(∫ θ in Work.Spaces.Iθ, f θ * deriv (deriv f) θ * (Real.sin (2 * θ)) ^ (2 - γ))
        - 2 * (2 - γ) * (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ))
        - 2 * (2 - γ) * (γ - 1) * (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * (Real.cot (2 * θ)) ^ 2
            * (Real.sin (2 * θ)) ^ (2 - γ)) := by
  have h := Work.FTS.EllipticEst.Prop.angIbpWild (p := 2 - γ) (by linarith) f hsm hI1 hI0 hI2 hI3
    hfl0 hfl1
  convert h using 2 <;> ring

/-- **The `γ`-weighted slice Agmon inequality.**  Under the hypotheses of `angIbpMu` (which is
exactly what the two flux conditions and the four integrabilities encode), the two correction
terms of the identity are *negative*, so

`∫ (f')² μ ≤ -∫ f f'' μ`. -/
theorem sliceAgmonMu {γ : ℝ} (hγ : 1 < γ) (hγ2 : γ < 2) {f : ℝ → ℝ}
    (hsm : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)))
    (hI0 : IntegrableOn (fun θ => (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ)) Work.Spaces.Iθ)
    (hI1 : IntegrableOn (fun θ => (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ)) Work.Spaces.Iθ)
    (hI2 : IntegrableOn (fun θ => f θ * deriv (deriv f) θ * (Real.sin (2 * θ)) ^ (2 - γ))
      Work.Spaces.Iθ)
    (hI3 : IntegrableOn (fun θ => (f θ) ^ 2 * (Real.cot (2 * θ)) ^ 2
      * (Real.sin (2 * θ)) ^ (2 - γ)) Work.Spaces.Iθ)
    (hfl0 : Tendsto (fun θ => (Real.sin (2 * θ)) ^ (2 - γ)
      * (f θ * deriv f θ - (2 - γ) * Real.cot (2 * θ) * (f θ) ^ 2))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hfl1 : Tendsto (fun θ => (Real.sin (2 * θ)) ^ (2 - γ)
      * (f θ * deriv f θ - (2 - γ) * Real.cot (2 * θ) * (f θ) ^ 2))
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) :
    (∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ))
      ≤ -(∫ θ in Work.Spaces.Iθ, f θ * deriv (deriv f) θ * (Real.sin (2 * θ)) ^ (2 - γ)) := by
  have h := angIbpMu hγ hγ2 hsm hI0 hI1 hI2 hI3 hfl0 hfl1
  have h2 : 0 ≤ ∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ) := by
    refine MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ hθ => ?_)
    refine mul_nonneg (sq_nonneg _) ?_
    exact Real.rpow_nonneg
      (Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩) _
  have h3 : 0 ≤ ∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * (Real.cot (2 * θ)) ^ 2
      * (Real.sin (2 * θ)) ^ (2 - γ) := by
    refine MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ hθ => ?_)
    refine mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) ?_
    exact Real.rpow_nonneg
      (Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩) _
  have hp : 0 ≤ 2 * (2 - γ) := by linarith
  have hp2 : 0 ≤ 2 * (2 - γ) * (γ - 1) := by nlinarith [hγ, hγ2]
  nlinarith [h, mul_nonneg hp h2, mul_nonneg hp2 h3]

theorem mixedSlotInterpEta : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (G : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.SmoothOpen G →
      (∀ z : ℝ, G z 0 = 0) → (∀ z : ℝ, G z (Real.pi / 2) = 0) →
      Work.Spaces.HkMem α 0 (Work.Spaces.DzIter 2 G) →
      Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 G) →
      Work.Spaces.HkMem α 0 (Work.Spaces.Dz G) →
      (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.Dz (Work.Spaces.pth G) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
            * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
        ≤ C * (Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 2 G)
            + Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 G)
            + Work.Spaces.HkSq α 0 (Work.Spaces.Dz G)) := by sorry

end Work.FTS.EllipticEst.Prop
