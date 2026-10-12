import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.OneBodyKin.continuous_kinFT
import Submission.Work.OneBodyKin.integrable_mul_kinFT_re
import Submission.Work.OneBodyKin.kinFT_sub_smul
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.OneBodyKin.bsOneBody_eq_decomp`

The **mean-free decomposition of the one-body big-box kinetic form**: for `F(‖·‖) ∈ L¹(ℝ³)`,

    `⟨χ_u Q_{Λ(u)}ψ, F(√−Δ) χ_u Q_{Λ(u)}ψ⟩`
      `= ⟨χ_u ψ, F(√−Δ) χ_u ψ⟩`
        `− 2·m_u·⟨χ_u, F(√−Δ) χ_u ψ⟩`
        `+ m_u²·⟨χ_u, F(√−Δ) χ_u⟩`,

where `m_u = bsMean ℓ u ψ` is the box mean and `Q_{Λ(u)}ψ = ψ − m_u` the mean-free part.

This is the algebraic identity behind the three terms of the projected moving-box family form
(`Submission/Work/OneBodyKin/Defs.lean`, §"The three terms of the symbol"): with
`Q_uψ = ψ − m_u` expanded, self-adjointness gives the `u`-integrated family form
`bsFamilyForm` as the combination of `bsFamilyFormUnproj`, the cross form `bsPair`, and the
constant-state cross form `bsPair ℓ F u 1`.

## Proof

Everything is the pointwise-in-`p` computation.  Writing
`G = χ_u·ψ`, `Φ = χ_u`, `Q = χ_u·Q_uψ = G − m_u·Φ` (as complex-valued functions) and
`a = kinFT G`, `b = kinFT Φ`, `c = (m_u : ℂ)`, the `kinFT`-linearity (`kinFT_sub_smul`) turns the
`bsOneBody` integrand into `F‖p‖·‖a(p) − c·b(p)‖²`; the elementary complex identity
`‖a − c·b‖² = ‖a‖² − 2·Re(m_u)·Re(b·conj a) + Re(m_u)²·Re(b·conj b)` rewrites it term by term;
and the integral splits (`integral_add`/`integral_sub`/`integral_const_mul`) once each of the
three terms is shown integrable — which holds because `a`, `b` are bounded
(`‖kinFT g p‖ ≤ ∫‖g‖`) and `F(‖·‖) ∈ L¹` (`integrable_mul_kinFT_re`).  The three resulting
integrals are then exactly the definitions of `bsOneBodyUnproj`, `bsPair ℓ F u ψ` and
`bsPair ℓ F u 1`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal ContDiff

namespace Work.OneBodyKin

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

/-! ## Elementary API of the window `χ_u` -/

/-- The moving-box window `bsWin ℓ u = chiScale ℓ (· − ℓu)` is continuous. -/
private lemma continuous_bsWin {ℓ : ℝ} (u : ℝ³) : Continuous (Work.BSKinetic.bsWin ℓ u) := by
  unfold Work.BSKinetic.bsWin
  exact (chiScale_continuous ℓ).comp (continuous_id.sub continuous_const)

/-- The moving-box window `bsWin ℓ u` has compact support. -/
private lemma hasCompactSupport_bsWin {ℓ : ℝ} (hℓ : 0 < ℓ) (u : ℝ³) :
    HasCompactSupport (Work.BSKinetic.bsWin ℓ u) := by
  unfold Work.BSKinetic.bsWin
  exact (chiScale_hasCompactSupport (ne_of_gt hℓ)).comp_homeomorph (Homeomorph.subRight (ℓ • u))

/-- The complexified window `z ↦ (χ_u z : ℂ)` has compact support. -/
private lemma hasCompactSupport_bsWin_c {ℓ : ℝ} (hℓ : 0 < ℓ) (u : ℝ³) :
    HasCompactSupport (fun z : ℝ³ => (Work.BSKinetic.bsWin ℓ u z : ℂ)) := by
  have h := (hasCompactSupport_bsWin hℓ u).comp_left (g := (Complex.ofRealCLM : ℝ → ℂ)) (by simp)
  simpa [Function.comp_def] using h

/-- The complexified window `z ↦ (χ_u z : ℂ)` is integrable. -/
private lemma bsWin_integrable {ℓ : ℝ} (hℓ : 0 < ℓ) (u : ℝ³) :
    MeasureTheory.Integrable (fun z : ℝ³ => (Work.BSKinetic.bsWin ℓ u z : ℂ)) :=
  (Complex.continuous_ofReal.comp (continuous_bsWin u)).integrable_of_hasCompactSupport
    (hasCompactSupport_bsWin_c hℓ u)

/-- The windowed state `z ↦ χ_u(z)·ψ(z)` (complexified) is integrable. -/
private lemma bsWin_mul_integrable {ℓ : ℝ} (hℓ : 0 < ℓ) (u : ℝ³) {ψ : ℝ³ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) :
    MeasureTheory.Integrable (fun z : ℝ³ =>
      (Work.BSKinetic.bsWin ℓ u z : ℂ) * (ψ z : ℂ)) := by
  have hcont : Continuous (fun z : ℝ³ => (Work.BSKinetic.bsWin ℓ u z : ℂ) * (ψ z : ℂ)) :=
    (Complex.continuous_ofReal.comp (continuous_bsWin u)).mul
      (Complex.continuous_ofReal.comp hψ.continuous)
  have hsupport : HasCompactSupport
      (fun z : ℝ³ => (Work.BSKinetic.bsWin ℓ u z : ℂ) * (ψ z : ℂ)) :=
    (hasCompactSupport_bsWin_c hℓ u).mul_right
  exact hcont.integrable_of_hasCompactSupport hsupport

/-! ## The elementary complex identity -/

/-- `Re(z·conj z) = ‖z‖²`. -/
private lemma re_mul_star (z : ℂ) : (z * star z).re = ‖z‖^2 := by
  have h : z * star z = ((Complex.normSq z : ℝ) : ℂ) := Complex.mul_conj z
  rw [h, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

/-- The real-parameter expansion of the squared norm:
`‖x − (r:ℂ)·y‖² = ‖x‖² − 2r·Re(y·conj x) + r²·Re(y·conj y)`. -/
private lemma norm_sub_smul_sq (x y : ℂ) (r : ℝ) :
    ‖x - (r:ℂ)*y‖^2 = ‖x‖^2 - 2*r*(y * star x).re + r^2*(y*star y).re := by
  have h3 : (y * star y).re = Complex.normSq y := by
    have h : y * star y = ((Complex.normSq y : ℝ) : ℂ) := Complex.mul_conj y
    rw [h, Complex.ofReal_re]
  rw [h3, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  have h : x - (r:ℂ)*y = -((r:ℂ)*y - x) := by ring
  rw [h, Complex.normSq_neg, Complex.normSq_sub, Complex.normSq_mul, Complex.normSq_ofReal]
  rw [starRingEnd_apply]
  rw [show (↑r : ℂ) * y * star x = (↑r : ℂ) * (y * star x) from by ring]
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-! ## The main decomposition -/

theorem bsOneBody_eq_decomp {ℓ : ℝ} (hℓ : 0 < ℓ) {F : ℝ → ℝ}
    (hFi : MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) => F ‖p‖))
    (ψ : EuclideanSpace ℝ (Fin 3) → ℝ) (hψ : ContDiff ℝ (⊤ : ENat) ψ)
    (hcs : HasCompactSupport ψ) (u : EuclideanSpace ℝ (Fin 3)) :
    Work.BSKinetic.bsOneBody ℓ F u ψ
      = Work.BSKinetic.bsOneBodyUnproj ℓ F u ψ
        - 2 * (Work.BSKinetic.bsMean ℓ u ψ * Work.OneBodyKin.bsPair ℓ F u ψ)
        + (Work.BSKinetic.bsMean ℓ u ψ) ^ 2 * Work.OneBodyKin.bsPair ℓ F u (fun _ => 1) := by
  -- the complexified window `Φ`, the windowed state `G`, and the box mean `m`
  set Phi : ℝ³ → ℂ := fun z => (Work.BSKinetic.bsWin ℓ u z : ℂ) with hPhi
  set G : ℝ³ → ℂ := fun z => (Work.BSKinetic.bsWin ℓ u z : ℂ) * (ψ z : ℂ) with hG
  set m : ℝ := Work.BSKinetic.bsMean ℓ u ψ with hm
  have hPhi_int : MeasureTheory.Integrable Phi := by
    rw [hPhi]; exact bsWin_integrable hℓ u
  have hG_int : MeasureTheory.Integrable G := by
    rw [hG]; exact bsWin_mul_integrable hℓ u hψ hcs
  -- `Q_uψ` is `ψ − m`, so the `bsOneBody` state is `G − (m:ℂ)·Φ`
  have hQf : (fun z : ℝ³ => (Work.BSKinetic.bsWin ℓ u z : ℂ) *
        (Work.BSKinetic.bsQ ℓ u ψ z : ℂ)) = G - (m : ℂ) • Phi := by
    rw [hG, hPhi, hm]
    funext z
    simp only [Work.BSKinetic.bsQ, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Complex.ofReal_sub]
    ring
  -- pointwise `kinFT`-linearity
  have hkin : ∀ p : ℝ³,
      Submission.BoseGases.kinFT (fun z : ℝ³ => (Work.BSKinetic.bsWin ℓ u z : ℂ) *
          (Work.BSKinetic.bsQ ℓ u ψ z : ℂ)) p
        = Submission.BoseGases.kinFT G p - (m : ℂ) * Submission.BoseGases.kinFT Phi p := by
    intro p
    rw [hQf]
    exact Work.OneBodyKin.kinFT_sub_smul hG_int hPhi_int (m : ℂ) p
  -- step 1: unfold `bsOneBody` and apply the pointwise linearity
  have step1 : Work.BSKinetic.bsOneBody ℓ F u ψ
      = ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³, F ‖p‖ *
          ‖Submission.BoseGases.kinFT G p - (m : ℂ) * Submission.BoseGases.kinFT Phi p‖ ^ 2 := by
    unfold Work.BSKinetic.bsOneBody
    congr 1
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
    beta_reduce
    rw [hkin p]
  -- step 2: the elementary complex identity
  have step2 : (∫ p : ℝ³, F ‖p‖ *
        ‖Submission.BoseGases.kinFT G p - (m : ℂ) * Submission.BoseGases.kinFT Phi p‖ ^ 2)
      = ∫ p : ℝ³, F ‖p‖ * (‖Submission.BoseGases.kinFT G p‖ ^ 2
          - 2 * m * (Submission.BoseGases.kinFT Phi p *
              star (Submission.BoseGases.kinFT G p)).re
          + m ^ 2 * (Submission.BoseGases.kinFT Phi p *
              star (Submission.BoseGases.kinFT Phi p)).re) := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
    beta_reduce
    rw [norm_sub_smul_sq]
  -- step 3: distribute `F(‖p‖)` over the three terms
  have step3 : (∫ p : ℝ³, F ‖p‖ * (‖Submission.BoseGases.kinFT G p‖ ^ 2
          - 2 * m * (Submission.BoseGases.kinFT Phi p *
              star (Submission.BoseGases.kinFT G p)).re
          + m ^ 2 * (Submission.BoseGases.kinFT Phi p *
              star (Submission.BoseGases.kinFT Phi p)).re))
      = ∫ p : ℝ³, (F ‖p‖ * ‖Submission.BoseGases.kinFT G p‖ ^ 2
          - 2 * m * (F ‖p‖ * (Submission.BoseGases.kinFT Phi p *
              star (Submission.BoseGases.kinFT G p)).re)
          + m ^ 2 * (F ‖p‖ * (Submission.BoseGases.kinFT Phi p *
              star (Submission.BoseGases.kinFT Phi p)).re)) := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
    beta_reduce
    ring
  -- integrability of the three terms
  have hI1 : MeasureTheory.Integrable
      (fun p : ℝ³ => F ‖p‖ * ‖Submission.BoseGases.kinFT G p‖ ^ 2) := by
    refine (Work.OneBodyKin.integrable_mul_kinFT_re hFi hG_int hG_int).congr
      (Filter.Eventually.of_forall (fun p => ?_))
    beta_reduce
    rw [re_mul_star]
  have hI2 : MeasureTheory.Integrable
      (fun p : ℝ³ => F ‖p‖ * (Submission.BoseGases.kinFT Phi p *
        star (Submission.BoseGases.kinFT G p)).re) :=
    Work.OneBodyKin.integrable_mul_kinFT_re hFi hPhi_int hG_int
  have hI3 : MeasureTheory.Integrable
      (fun p : ℝ³ => F ‖p‖ * (Submission.BoseGases.kinFT Phi p *
        star (Submission.BoseGases.kinFT Phi p)).re) :=
    Work.OneBodyKin.integrable_mul_kinFT_re hFi hPhi_int hPhi_int
  -- step 4: split the integral
  have step4 : (∫ p : ℝ³, (F ‖p‖ * ‖Submission.BoseGases.kinFT G p‖ ^ 2
          - 2 * m * (F ‖p‖ * (Submission.BoseGases.kinFT Phi p *
              star (Submission.BoseGases.kinFT G p)).re)
          + m ^ 2 * (F ‖p‖ * (Submission.BoseGases.kinFT Phi p *
              star (Submission.BoseGases.kinFT Phi p)).re)))
      = (∫ p : ℝ³, F ‖p‖ * ‖Submission.BoseGases.kinFT G p‖ ^ 2)
        - 2 * m * (∫ p : ℝ³, F ‖p‖ * (Submission.BoseGases.kinFT Phi p *
            star (Submission.BoseGases.kinFT G p)).re)
        + m ^ 2 * (∫ p : ℝ³, F ‖p‖ * (Submission.BoseGases.kinFT Phi p *
            star (Submission.BoseGases.kinFT Phi p)).re) := by
    rw [show (∫ p : ℝ³, (F ‖p‖ * ‖Submission.BoseGases.kinFT G p‖ ^ 2
            - 2 * m * (F ‖p‖ * (Submission.BoseGases.kinFT Phi p *
                star (Submission.BoseGases.kinFT G p)).re)
            + m ^ 2 * (F ‖p‖ * (Submission.BoseGases.kinFT Phi p *
                star (Submission.BoseGases.kinFT Phi p)).re)))
          = ∫ p : ℝ³,
              ((fun p : ℝ³ => F ‖p‖ * ‖Submission.BoseGases.kinFT G p‖ ^ 2)
                - (fun p : ℝ³ => 2 * m * (F ‖p‖ * (Submission.BoseGases.kinFT Phi p *
                    star (Submission.BoseGases.kinFT G p)).re))) p
              + (fun p : ℝ³ => m ^ 2 * (F ‖p‖ * (Submission.BoseGases.kinFT Phi p *
                    star (Submission.BoseGases.kinFT Phi p)).re)) p
          from rfl]
    rw [MeasureTheory.integral_add (hI1.sub (hI2.const_mul (2 * m)))
      (hI3.const_mul (m ^ 2))]
    rw [show (∫ p : ℝ³,
              ((fun p : ℝ³ => F ‖p‖ * ‖Submission.BoseGases.kinFT G p‖ ^ 2)
                - (fun p : ℝ³ => 2 * m * (F ‖p‖ * (Submission.BoseGases.kinFT Phi p *
                    star (Submission.BoseGases.kinFT G p)).re))) p)
          = ∫ p : ℝ³,
              (fun p : ℝ³ => F ‖p‖ * ‖Submission.BoseGases.kinFT G p‖ ^ 2) p
              - (fun p : ℝ³ => 2 * m * (F ‖p‖ * (Submission.BoseGases.kinFT Phi p *
                    star (Submission.BoseGases.kinFT G p)).re)) p
          from rfl]
    rw [MeasureTheory.integral_sub hI1 (hI2.const_mul (2 * m))]
    rw [show (∫ p : ℝ³, (fun p : ℝ³ => 2 * m * (F ‖p‖ *
              (Submission.BoseGases.kinFT Phi p *
                star (Submission.BoseGases.kinFT G p)).re)) p)
          = ∫ p : ℝ³, 2 * m * (F ‖p‖ * (Submission.BoseGases.kinFT Phi p *
              star (Submission.BoseGases.kinFT G p)).re) from rfl]
    rw [MeasureTheory.integral_const_mul (2 * m)]
    rw [show (∫ p : ℝ³, (fun p : ℝ³ => m ^ 2 * (F ‖p‖ *
              (Submission.BoseGases.kinFT Phi p *
                star (Submission.BoseGases.kinFT Phi p)).re)) p)
          = ∫ p : ℝ³, m ^ 2 * (F ‖p‖ * (Submission.BoseGases.kinFT Phi p *
              star (Submission.BoseGases.kinFT Phi p)).re) from rfl]
    rw [MeasureTheory.integral_const_mul (m ^ 2)]

  -- the three integrals are the definitions
  have hU : Work.BSKinetic.bsOneBodyUnproj ℓ F u ψ
      = ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³, F ‖p‖ *
          ‖Submission.BoseGases.kinFT G p‖ ^ 2 := by
    unfold Work.BSKinetic.bsOneBodyUnproj
    rw [hG]
  have hP : Work.OneBodyKin.bsPair ℓ F u ψ
      = ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³, F ‖p‖ * (Submission.BoseGases.kinFT Phi p *
          star (Submission.BoseGases.kinFT G p)).re := by
    unfold Work.OneBodyKin.bsPair
    rw [hPhi, hG]
  have hone : (fun z : ℝ³ => (Work.BSKinetic.bsWin ℓ u z : ℂ) *
      (((fun _ => (1 : ℝ)) z : ℝ) : ℂ)) = Phi := by
    rw [hPhi]
    funext z
    simp
  have hP1 : Work.OneBodyKin.bsPair ℓ F u (fun _ => 1)
      = ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³, F ‖p‖ * (Submission.BoseGases.kinFT Phi p *
          star (Submission.BoseGases.kinFT Phi p)).re := by
    unfold Work.OneBodyKin.bsPair
    rw [hone]
  rw [step1, step2, step3, step4, hU, hP, hP1]
  ring

end Work.OneBodyKin
