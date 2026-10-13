/-
Copyright: work module for the Elgindi finite-time singularity project.

# The `σ`-weighted slicewise *coercivity* of `Lzero1` in the weak class

For `σ θ = sEta θ = sin(2θ)^{-η}`, `η = 99/100`, and

`Lzero1 u = -u'' + (tan θ · u)' - 6u`   (the angular part of the Biot–Savart operator),

the target is

`∫_{Iθ} (f')²σ ≤ C (∫_{Iθ} Lzero1 f · f · σ + K ∫_{Iθ} f²σ)`

for some constants `C, K > 0` and *every* `f : ℝ → ℝ` with

* `f` of class `C²` on the **open** interval `(0, π/2)`,
* the two endpoint *limits* `f → 0` at `0⁺` and at `(π/2)⁻`,
* the honest integrability of `f²σ`, `(f'')²σ` and `Lzero1 f · f · σ` on `Iθ = [0, π/2]`.

This is the coercivity companion of `AngAWeak.aeSliceSigmaCoercive` (which gives the *lower*
bound `-(K₀ ∫f²σ) ≤ ∫Lzero1 f f σ` for the same class); it is the form in which the elliptic
estimates of the self-similar Euler chapter consume the `θ`-slice.

## The argument

The `σ`-weighted self-form identity of `Lzero1` (`Honest.honSliceIdentity`)

  `∫ Lzero1 f f σ = ∫ (f')²σ + ∫ hc - (η+6)∫f²σ - 2η(1+η)∫Hc`,

where `hc = f²σ(1-η)/(2cos²θ) ≥ 0` and `Hc = f² cos²(2θ) σ/sin²(2θ)`, together with the
`cos²(2θ)`-weighted Hardy inequality in the *honest* form
(`Honest.Step1G.HonHardyCosWeight`)

  `∫ Hc ≤ (1+η)^{-2} ∫ (f')²σ + C₀ ∫ f²σ`

gives, with `A = ∫(f')²σ`, `B = ∫f²σ`, `R = ∫Lzero1 f f σ`,

  `A = R - hc + (η+6)B + 2η(1+η)∫Hc ≤ R + (η+6)B + (2η/(1+η))A + 2η(1+η)C₀ B`,

hence `((1-η)/(1+η)) A ≤ R + K B` with `K = η + 6 + 2η(1+η)C₀`, i.e. the statement with
`C = (1+η)/(1-η) = 199` and `K = 6.99 + 3.94 C₀`.

The three auxiliary facts that reduce the hypotheses of the target to those of the two
ingredients above are all available in the workspace:

* `Honest.sliceInterp` — from the honesty of `f²σ` and `(f'')²σ` one gets the honesty of
  `(f')²σ` (needed as a hypothesis of the Hardy inequality and of the identity);
* `Honest.HonSliceDerivBdd`, `Honest.HonSliceAbsLe` — from the honesty of `(f'')²σ` and the two
  endpoint limits one gets `|f'| ≤ C`, `|f| ≤ C·min(θ, π/2-θ)`, hence (with
  `Honest.HonPrimitiveTendsto`) the vanishing of the boundary primitive of the identity;
* `Honest.HonAuxIntegrable` — the honesty of the two auxiliary integrands `hc`, `Hc`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.Honest.SliceIbpThetaHonest
import Submission.Work.FTS.EllipticEst.Honest.Step1G.HonHardyCosWeight
import Submission.Work.FTS.EllipticEst.AngAWeak.sliceIbpSigmaWeakFts
import Submission.Work.FTS.EllipticEst.Honest.slice_bdd_of_sq_mul_sEta
import Submission.Work.FTS.EllipticEst.Honest.sliceInterp
import Submission.Work.FTS.EllipticEst.Honest.HonSliceSigmaLower
import Submission.Work.FTS.EllipticEst.Honest.HonSliceDerivBdd
import Submission.Work.FTS.EllipticEst.Honest.HonSliceAbsLe
import Submission.Work.FTS.EllipticEst.Honest.HonPrimitiveTendsto
import Submission.Work.FTS.EllipticEst.Honest.HonAuxIntegrable
import Submission.Work.FTS.EllipticEst.StraightDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.AngAWeak

open MeasureTheory Set Filter
open scoped Real Topology

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Small pointwise facts -/

/-- `sEta θ = sin(2θ)^{-η} ≥ 0` on `Iθ`. -/
private theorem sEta_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.FTS.EllipticEst.sEta θ := by
  rw [Work.FTS.EllipticEst.sEta]
  refine Real.rpow_nonneg ?_ _
  rw [Work.Spaces.Iθ] at hθ
  exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
    (by linarith [hθ.2, Real.pi_pos])

/-- On the *open* interval, where `sin(2θ) > 0`, the singular integrand `Honest.honHc` is the
classical `f² cos²(2θ) sin(2θ)^{-(2+η)}`. -/
private theorem honHc_eq (η : ℝ) (f : ℝ → ℝ) {θ : ℝ} (hθ : θ ∈ Honest.Iθo) :
    Honest.honHc η f θ
      = (f θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + η)) := by
  have hQ : 0 < Real.sin (2 * θ) := Honest.sin_two_pos_of_Iθo hθ
  have hkey : (Real.sin (2 * θ)) ^ (-(2 + η))
      = (Real.sin (2 * θ)) ^ (-η) * ((Real.sin (2 * θ)) ^ 2)⁻¹ := by
    rw [show -(2 + η) = (-η) + (-(2 : ℝ)) by ring, Real.rpow_add hQ, Real.rpow_neg hQ.le 2]
    congr 1
    rw [Real.rpow_two, sq]
  rw [Honest.honHc, Honest.sig, hkey, div_eq_mul_inv]
  ring

/-! ## Translating the `Honest` integrands into the shapes of the target -/

/-- The integral over `Iθ` equals the integral over the open interval `(0, π/2)`. -/
private theorem int_Icc_eq_int_Ioo (g : ℝ → ℝ) :
    (∫ θ in Work.Spaces.Iθ, g θ) = ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), g θ :=
  Honest.integral_Icc_eq_integral_Ioo_hon g

/-- `∫ honLz = ∫ Lzero1 f · f · σ`. -/
private theorem int_honLz (f : ℝ → ℝ) :
    (∫ θ in Work.Spaces.Iθ, Honest.honLz Work.Spaces.eta f θ)
      = ∫ θ in Work.Spaces.Iθ,
          Work.FTS.EllipticEst.Lzero1 f θ * f θ * Work.FTS.EllipticEst.sEta θ :=
  setIntegral_congr_fun measurableSet_Icc (fun _ _ => rfl)

/-- `∫ honDu = ∫ (f')²σ`. -/
private theorem int_honDu (f : ℝ → ℝ) :
    (∫ θ in Work.Spaces.Iθ, Honest.honDu Work.Spaces.eta f θ)
      = ∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2 * Work.FTS.EllipticEst.sEta θ :=
  setIntegral_congr_fun measurableSet_Icc (fun _ _ => rfl)

/-- `∫ honU2 = ∫ f²σ`. -/
private theorem int_honU2 (f : ℝ → ℝ) :
    (∫ θ in Work.Spaces.Iθ, Honest.honU2 Work.Spaces.eta f θ)
      = ∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * Work.FTS.EllipticEst.sEta θ :=
  setIntegral_congr_fun measurableSet_Icc (fun _ _ => rfl)

/-- `∫ honCc = ∫ f²σ(1-η)/(2cos²θ)`. -/
private theorem int_honCc (f : ℝ → ℝ) :
    (∫ θ in Work.Spaces.Iθ, Honest.honCc Work.Spaces.eta f θ)
      = ∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
          * (1 / 2 * (1 - Work.Spaces.eta) / Real.cos θ ^ 2) :=
  setIntegral_congr_fun measurableSet_Icc (fun _ _ => rfl)

/-- `∫ honHc = ∫ f²cos²(2θ)sin(2θ)^{-(2+η)}` (the pointwise identity holds on the open
interval, which differs from `Iθ` by a null set). -/
private theorem int_honHc (f : ℝ → ℝ) :
    (∫ θ in Work.Spaces.Iθ, Honest.honHc Work.Spaces.eta f θ)
      = ∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * (Real.cos (2 * θ)) ^ 2
          * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta)) := by
  rw [int_Icc_eq_int_Ioo (Honest.honHc Work.Spaces.eta f),
      int_Icc_eq_int_Ioo (fun θ => (f θ) ^ 2 * (Real.cos (2 * θ)) ^ 2
          * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta)))]
  exact setIntegral_congr_fun measurableSet_Ioo (fun θ hθ => honHc_eq Work.Spaces.eta f hθ)

/-! ## The scalar core of the estimate -/

/-- The algebra of the estimate: the identity `R = A + hc - (η+6)B - 2η(1+η)W`, the Hardy
bound `W ≤ (1+η)^{-2}A + C₀B` and the positivity `0 ≤ hc` give
`A ≤ ((1+η)/(1-η))(R + K B)` with `K = η + 6 + 2η(1+η)C₀`. -/
private theorem arith_key {A R hc B W η C₀ : ℝ}
    (hid : R = (A + hc) - (η + 6) * B - 2 * η * (1 + η) * W)
    (hW : W ≤ (1 / (1 + η) ^ 2) * A + C₀ * B)
    (hhc : 0 ≤ hc) (hη0 : 0 ≤ η) (hη1 : η < 1) :
    A ≤ (1 + η) / (1 - η) * (R + ((η + 6) + 2 * η * (1 + η) * C₀) * B) := by
  have h2η : 0 ≤ 2 * η * (1 + η) := by nlinarith
  have h1η : (1 + η) ≠ 0 := by linarith
  have hW' := mul_le_mul_of_nonneg_left hW h2η
  have hexp : 2 * η * (1 + η) * ((1 / (1 + η) ^ 2) * A + C₀ * B)
      = (2 * η / (1 + η)) * A + 2 * η * (1 + η) * C₀ * B := by
    field_simp
  have hstep : A ≤ R + ((η + 6) + 2 * η * (1 + η) * C₀) * B + (2 * η / (1 + η)) * A := by
    nlinarith [hid, hW', hexp, hhc]
  have hs2 : 1 - 2 * η / (1 + η) = (1 - η) / (1 + η) := by
    field_simp
    ring
  have hpos : 0 < 1 - 2 * η / (1 + η) := by
    rw [hs2]
    exact div_pos (by linarith) (by linarith)
  have hmain : (1 - 2 * η / (1 + η)) * A ≤ R + ((η + 6) + 2 * η * (1 + η) * C₀) * B := by
    linarith [hstep]
  have hmain' : A * (1 - 2 * η / (1 + η)) ≤ R + ((η + 6) + 2 * η * (1 + η) * C₀) * B := by
    rw [mul_comm A]
    exact hmain
  have hfin := (le_div_iff₀ hpos).mpr hmain'
  rwa [show (R + ((η + 6) + 2 * η * (1 + η) * C₀) * B) / (1 - 2 * η / (1 + η))
      = (1 + η) / (1 - η) * (R + ((η + 6) + 2 * η * (1 + η) * C₀) * B) by
    rw [hs2]
    field_simp] at hfin

/-! ## The target -/

theorem aeSigmaSliceCoercive : ∃ C : ℝ, ∃ K : ℝ, 0 < C ∧ 0 < K ∧ ∀ f : ℝ → ℝ,
    ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)) →
    Filter.Tendsto f (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) →
    Filter.Tendsto f (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) →
    MeasureTheory.IntegrableOn (fun θ => (f θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ →
    MeasureTheory.IntegrableOn (fun θ => (deriv (fun t => deriv f t) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ →
    MeasureTheory.IntegrableOn (fun θ => Work.FTS.EllipticEst.Lzero1 f θ * f θ * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ →
    (∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      ≤ C * ((∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.Lzero1 f θ * f θ * Work.FTS.EllipticEst.sEta θ)
          + K * (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)) := by
  have hη0 : 0 ≤ Work.Spaces.eta := by norm_num [Work.Spaces.eta]
  have hη1 : Work.Spaces.eta < 1 := by norm_num [Work.Spaces.eta]
  obtain ⟨C₀, hC₀pos, hHardy⟩ :=
    Honest.Step1G.HonHardyCosWeight Work.Spaces.eta hη0 hη1
  refine ⟨(1 + Work.Spaces.eta) / (1 - Work.Spaces.eta),
    (Work.Spaces.eta + 6) + 2 * Work.Spaces.eta * (1 + Work.Spaces.eta) * C₀, ?_, ?_, ?_⟩
  · exact div_pos (by linarith) (by linarith)
  · have h1 : (0 : ℝ) < 1 + Work.Spaces.eta := by linarith
    have h2 : (0 : ℝ) ≤ 2 * Work.Spaces.eta * (1 + Work.Spaces.eta) * C₀ :=
      mul_nonneg (mul_nonneg (by linarith) h1.le) hC₀pos.le
    linarith [hη0, h2]
  · intro f hf h0 hπ hu2 hddu hlz
    -- the open interval is contained in `Iθ`
    have hIooSub : Set.Ioo (0 : ℝ) (Real.pi / 2) ⊆ Work.Spaces.Iθ :=
      fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩
    -- `(f')²σ` is honest, by the interpolation inequality
    obtain ⟨hdu, _⟩ := Honest.sliceInterp f hf hu2 hddu
    -- the pointwise bounds on `f` and `f'`, and the vanishing of the boundary primitive
    obtain ⟨C, hC0, hbd⟩ :=
      Honest.HonSliceDerivBdd Work.Spaces.eta hη0 f hf (hddu.mono_set hIooSub)
    obtain ⟨hb1, hb2⟩ := Honest.HonSliceAbsLe C hC0 f hf h0 hπ hbd
    have hlim := Honest.HonPrimitiveTendsto Work.Spaces.eta hη0 hη1 f C hC0 hb1 hb2 hbd
    have hcontO : ContinuousOn f Honest.Iθo := hf.continuousOn
    obtain ⟨hcc, hhc⟩ :=
      Honest.HonAuxIntegrable Work.Spaces.eta hη0 hη1 f C hC0 hcontO hb1 hb2
    -- honesty of the four integrands of the identity, on the open interval
    have hlz' : IntegrableOn (Honest.honLz Work.Spaces.eta f) Honest.Iθo :=
      hlz.mono_set hIooSub
    have hdu' : IntegrableOn (Honest.honDu Work.Spaces.eta f) Honest.Iθo :=
      hdu.mono_set hIooSub
    have hu2' : IntegrableOn (Honest.honU2 Work.Spaces.eta f) Honest.Iθo :=
      hu2.mono_set hIooSub
    -- the `σ`-weighted self-form identity of `Lzero1`
    have hid := Honest.honSliceIdentity Work.Spaces.eta hη0 hη1 f hf hlim hlz' hdu' hu2' hcc hhc
    rw [int_honLz, int_honDu, int_honCc, int_honU2, int_honHc] at hid
    -- the `cos²(2θ)`-weighted Hardy bound, in the shapes of the target
    have hH : (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * (Real.cos (2 * θ)) ^ 2
          * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta)))
        ≤ (1 / (1 + Work.Spaces.eta) ^ 2)
            * (∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
          + C₀ * (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
      have h := hHardy f hf h0 hπ (hu2.mono_set hIooSub) (hdu.mono_set hIooSub)
      rw [← int_Icc_eq_int_Ioo (fun θ => (f θ) ^ 2 * (Real.cos (2 * θ)) ^ 2
            * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta))),
          ← int_Icc_eq_int_Ioo (fun θ => (deriv f θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))),
          ← int_Icc_eq_int_Ioo (fun θ => (f θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))] at h
      rw [show (∫ θ in Work.Spaces.Iθ,
              (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
            = ∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2 * Work.FTS.EllipticEst.sEta θ from
          (setIntegral_congr_fun measurableSet_Icc (fun _ _ => rfl)).symm,
          show (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
            = ∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * Work.FTS.EllipticEst.sEta θ from
          (setIntegral_congr_fun measurableSet_Icc (fun _ _ => rfl)).symm] at h
      exact h
    -- the positive `sec²`-piece is nonnegative
    have hZ0 : 0 ≤ ∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
        * (1 / 2 * (1 - Work.Spaces.eta) / Real.cos θ ^ 2) := by
      refine integral_nonneg_of_ae ?_
      filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
      have hσ : 0 ≤ Work.FTS.EllipticEst.sEta θ := sEta_nonneg_Iθ hθ
      exact mul_nonneg (mul_nonneg (sq_nonneg _) hσ)
        (div_nonneg (by linarith [hη1]) (sq_nonneg _))
    exact arith_key hid hH hZ0 hη0 hη1

end Work.FTS.EllipticEst.AngAWeak
