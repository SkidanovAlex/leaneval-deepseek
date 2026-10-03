import Mathlib
import Submission.Work.Pert.Basic
import Submission.Work.Pert.Setup
import Submission.Work.Pert.MaxDom
import Submission.Work.Pert.AsmDefs
import Submission.Work.Pert.Gates
import Submission.Work.Fatou.Qreg.InjGeom
import Submission.Work.Interfaces.FatouNarrow
import Submission.Work.Interfaces.Fatou
import Submission.Work.PertU.pert_unpert
import Submission.Work.Pert.exists_fatouCoord_inv_tau0_phi
import Submission.Work.Pert.Eu_exists_center
import Submission.Work.Pert.CoordDefs
import Submission.Work.Pert.dev_deriv_on_Qc
import Submission.Work.Pert.Om_arc_subset_Qc
import Submission.Work.Pert.EuDevBounds
import Submission.Work.Pert.Gates
import Submission.Work.Fatou.Qreg.InjGeom
import Submission.Work.Pert.parab_germ_taylor_near0
import Submission.Work.Pert.jourA_subset_Qc_and_norm
import Submission.Work.Pert.tauC_lower_jourA
import Submission.Work.Pert.dev_rad_cross_le_a
import Submission.Work.Pert.vtilde_le_jourA
import Submission.Work.Pert.deltaU_arith
import Submission.Work.Pert.u_dev_le_of_nearOn_b
import Submission.Work.Pert.tauC_region_le
import Submission.Work.Pert.image_cover_centered

/-
## *** READ `NOTES_PertCoordClose_NEARON_ROUTE.md` FIRST (session 6) ***
## That note gives the route that works: `NearOn` with `L = closedBall 0 ρ`, `ρ` a FIXED constant
## (not ~1/η!) and `δ₀ = ρ/(32η)` forces `u` to be nearly constant on the region (Cauchy on `ball 0 ρ`),
## which bypasses the sharp `L¹ → |u'(0)-u(0)²|` bound that sessions 1-5 could not prove.
## The four delegated bricks and the remaining gaps (a sharper `u_dev_le_of_nearOn`, a lower bound
## `‖τ_f‖ ≥ 2‖σ‖`, the final arithmetic with margin ≈1.15) are listed in §3-§6 of that note.
##
## Reduction of the clause (working notes for the assembly; full account in
## `Submission/Work/Pert/NOTES_PertCoordClose_FINDINGS.md`, ROUTE2.md, ASM.md)

SEE `NOTES_PertCoordClose_ROUTE2.md` §1 (the reduced oscillation budget) and
`NOTES_PertCoordClose_ASM.md` (the piece-by-piece plan).

`Φm` is `Ψ + c` for a fixed base coordinate `Ψ` (from `hF.FatouExists` via `FatouUnique`), and
injectivity gives the unique preimage `ζ_w := Φm⁻¹ w ∈ Qm`; with `D := Ψ - id` one has the exact
identity `ζ_w - w = -(c + D(ζ_w))`.  Since `τ₀ (τC σ α ζ) = -u(0)(1 - e^{-2πiαζ})/(1 - e^{2πiα})`,
the sharp expansion `Work.Pert.tau0_tauC_close_sharp` gives
`‖τ₀(τC σ α ζ_w) - w‖ ≤ 2‖u(0)-1‖‖ζ_w‖ + 2π‖α‖‖ζ_w‖² + 1 + ‖ζ_w - w‖`,
so the clause is equivalent (up to `o(η)`) to: **the base deviation `D = Ψ - id` has oscillation
`≤ 2η/70` on the union of the two preimage regions** `R± = Φm⁻¹ (closedBall (±iη) (3η/10))`.

With `E_u := tau0 ∘ tauC σ α - id` one has EXACTLY `G - Φm = E_u - D - c`, so the whole clause is
`∃c, ∀ζ ∈ Φm⁻¹(discs) ∩ Qm, ‖E_u ζ - D ζ - c‖ ≤ η/70`.

`FatouDerivEstimate` gives `‖Φ' - 1/v‖ ≤ C₂/R` (`v = F - id`), whence `‖D'‖ ≲ ‖E_u'‖`-type
bounds and `diam D ≲ (‖λ/u₀‖)∫‖τ_f‖` with `λ = u'(0) - u(0)²`; the L¹ clause of
`NearTranslationL1` caps `‖λ/u₀‖ ≲ ξ₁/(62π)` (`Work.Pert.u_L1_deriv_bound`).
TRAP: do NOT try to prove the clause from the raw `NearTranslationL1` constant `1/32` by
integrating `|Φ′ − 1| ≤ 1/31` (that gives `≈ 2η/31 ≫ η/70`); use the reduction above.
-/

namespace Work.Pert

set_option maxHeartbeats 2000000

open MandelDim Complex Metric Set

noncomputable section

/-- The midpoint choice of the additive constant of the Fatou coordinate. -/
def constChoice (η : ℝ) (σ α : ℂ) (Ψ : ℂ → ℂ) : ℂ :=
  ((dev Ψ (Complex.I * (η : ℂ)) - Eu σ α (Complex.I * (η : ℂ)))
    + (dev Ψ (-(Complex.I * (η : ℂ))) - Eu σ α (-(Complex.I * (η : ℂ))))) / 2





end

/-- PERT (4.2.5), crux piece.  For every `η ≥ η₁` there is a neighbourhood of `f₀` such that every
admissible perturbation `(f, Df, ξ₁, rr, u, σ, α)` (the smallness hypotheses `hαη`, `hu0`, `hrr`
are DERIVED by the caller from `NearOn` + `small_of_nearOn` + the gate-point estimate for `rr`;
`hRe`/`h2ξ`/`hξ₁` are the caller's gate hypotheses) carries a Fatou coordinate `Φm` of
`F = liftF u σ α` on the gate `Qm ξ₁ α` whose image covers the two fattened discs
`closedBall (±iη) (3η/10)` and on which `τ₀ ∘ τ_f` is within `η/70` of the identity.

ROUTE (for the prover).  `pert_unpert` (module `Submission.Work.PertU.pert_unpert`, PROVED) gives the
unperturbed bound `‖τ₀ (d.φ w) − w‖ ≤ |η|/80` and `InjOn`/derivative data on `Dsm (±η)`; its proof
uses the fattening `Dsm ± ball 0 (η/10)` which contains `closedBall (±iη) (3η/10)`.  Combine with
the perturbed comparison `coordP ≈ d.φ` (the design's D3 / `Ksub_phi_close_v2`, i.e.
`FatouContinuity` of `hF` with the limit coordinate `Φ₀ = (τ₀ ∘ d.φ)⁻¹` — see
`Work.Pert.exists_fatouCoord_inv_tau0_phi` for the local ball form and `d.exhaust`/`d.φ_abel` for
the extension), the pinning `Φm(z₀) = Φ₀(z₀)` at one point, and the sequential-to-neighbourhood step
(`Work.Pert.tools.exists_subset_of_forall_seq`).  The COVERAGE clause follows from
`Work.Pert.image_cover_centered` applied around `ζ = Φ₀⁻¹ w` with a radius `r ≈ η/16`:
`Φm ζ ≈ w` within `r/4` and `closedBall ζ r ⊆ Qm ξ₁ α`.  Note the ξ₁-uniformity: every
`closedBall (±iη) (3η/10)` is contained in `Qm ξ₁ α` for ALL `0 < ξ₁ < η/2` (the minimum of
`|Im z| − Re z` on it is `η(1 − 3√2/10) ≈ 0.576η > ξ₁`), so one limit region
(`Qreg none (some (−η/2))`, whose
`NearTranslationL1` for the limit `F₀ = τ₀ ∘ f₀ ∘ τ₀` holds since `|w − 1| ≥ 32` there) serves all ξ₁.
The clause is stable: `τ₀ ∘ τ_f` differs from the identity on the discs by
`(u0−1)ζ − iβζ²/2` (`β = 2πα`, `hαη` ⟹ `βη ≤ 1/64`), whose variation over a disc is `≤ 0.012η`,
and the free additive constant of `Φm` absorbs the mean.
TRAP: do NOT try to prove the clause from the raw `NearTranslationL1` constant `1/32` by integrating
`|Φ′ − 1| ≤ 1/31` (that gives `≈ 2η/31 ≫ η/70`); use the limit-coordinate comparison above. -/
theorem PertCoordClose {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    (hF : MandelDim.FatouStatement) (hd : MandelDim.IsParabolicGerm f₀ D₀) :
    ∃ η₁ : ℝ, 0 < η₁ ∧ ∀ η : ℝ, η₁ ≤ η →
    ∃ L : Set ℂ, IsCompact L ∧ L ⊆ D₀ ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ∀ (f : ℂ → ℂ) (Df : Set ℂ) (ξ₁ rr : ℝ) (u : ℂ → ℂ) (σ α : ℂ),
        (hξ₁ : 0 < ξ₁) →
        (h2ξ : 2 * ξ₁ < η) →
        (hRe : η / 2 + 2 * ξ₁ < (1 / α).re) →
        (hαη : 2 * Real.pi * ‖α‖ * η ≤ 1 / 64) →
        (hu0 : ‖u 0 - 1‖ ≤ 1 / 1024) →
        (hrr : 1 / (4 * η) ≤ rr) →
        MandelDim.NearOn f₀ f Df L δ₀ → f 0 = 0 → MandelDim.InF1 (MandelDim.rotOf f) →
        α = MandelDim.rotOf f → 0 < rr →
        DifferentiableOn ℂ u (Metric.ball 0 rr) →
        (∀ z ∈ Metric.ball 0 rr, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2) →
        (∀ z ∈ Metric.ball 0 rr, f z = z + z * (z - σ) * u z) →
        1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α) →
        (∀ z ∈ Work.Pert.Qm ξ₁ α, Work.Pert.tauC σ α z ∈ Metric.ball 0 rr) →
        MandelDim.QAdm (some ((ξ₁ : ℂ) - 1 / α)) (some (-(ξ₁ : ℂ))) →
        MandelDim.NearTranslationL1 (Work.Pert.liftF u σ α) (Work.Pert.Qm ξ₁ α) →
        ∃ Φm : ℂ → ℂ,
          MandelDim.IsFatouCoordOn (Work.Pert.liftF u σ α) Φm (Work.Pert.Qm ξ₁ α) ∧
          (∀ w ∈ Metric.closedBall (Complex.I * (η : ℂ)) (3 * η / 10) ∪
                 Metric.closedBall (-(Complex.I * (η : ℂ))) (3 * η / 10),
            (∃ ζ ∈ Work.Pert.Qm ξ₁ α, Φm ζ = w) ∧
            (∀ ζ ∈ Work.Pert.Qm ξ₁ α, Φm ζ = w →
              ‖MandelDim.tau0 (Work.Pert.tauC σ α ζ) - w‖ ≤ η / 70)) := by
  classical
  obtain ⟨R₁, C₁, C₂, hR₁, hC₁, hC₂, hFDE⟩ := hF.2.2.2.2.1
  obtain ⟨ρ, B, hρpos, hρ1, hB0, hLsub, hf0b, hBρ⟩ :=
    parab_germ_taylor_near0 hd (show (0 : ℝ) < 1 / 1000000 by norm_num)
  refine ⟨max (max (max (10 ^ 8 * C₂) (10 ^ 4 * R₁)) (2000000 / ρ)) 100000000, ?_, ?_⟩
  · positivity
  intro η hη
  simp only [max_le_iff] at hη
  obtain ⟨⟨⟨hηC₂, hηR₁⟩, hηρ⟩, hηbig⟩ := hη
  have hηpos : (0 : ℝ) < η := by linarith
  have hη1 : (1 : ℝ) ≤ η := by linarith
  have hη32 : (32 : ℝ) ≤ η := by linarith
  have hη100 : (100 : ℝ) ≤ η := by linarith
  refine ⟨Metric.closedBall 0 ρ, isCompact_closedBall 0 ρ, hLsub, ρ / (32 * η), ?_, ?_⟩
  · positivity
  intro f Df ξ₁ rr u σ α hξ₁ h2ξ hRe hαη hu0 hrr hNear hf0 hInF1 hαeq hrrpos hu hbdd hform heq
    hτrr hQAdm hL1
  set zc : ℂ := Complex.I * (η : ℂ) with hzc
  -- ## elementary consequences of the hypotheses
  have hαne : α ≠ 0 := by
    intro h0
    rw [h0] at hRe
    simp at hRe
    linarith
  have hF1α : |α.im| < α.re := by rw [hαeq]; exact hInF1
  have h2πa : 2 * Real.pi * ‖α‖ ≤ 1 / 64 := by
    nlinarith [hαη, hη1, Real.pi_pos, norm_nonneg α]
  have hnorm_w : ‖2 * Real.pi * Complex.I * α‖ = 2 * Real.pi * ‖α‖ := by
    rw [norm_mul, norm_mul, norm_mul]
    rw [show ‖(2 : ℂ)‖ = 2 by norm_num,
        show ‖(Real.pi : ℂ)‖ = Real.pi by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos],
        Complex.norm_I, mul_one]
  have hw1 : ‖2 * Real.pi * Complex.I * α‖ ≤ 1 / 2 := by
    rw [hnorm_w]
    linarith
  have hu0n : (1023 : ℝ) / 1024 ≤ ‖u 0‖ := by
    have h1 : ‖(1 : ℂ) - u 0‖ = ‖u 0 - 1‖ := norm_sub_rev (1 : ℂ) (u 0)
    have h2 : ‖(1 : ℂ) - u 0‖ ≤ 1 / 1024 := by rw [h1]; exact hu0
    have h3 := norm_sub_norm_le (1 : ℂ) (u 0)
    rw [norm_one] at h3
    linarith only [h2, h3]
  have hu0pos : (0 : ℝ) < ‖u 0‖ := by linarith
  have hσu : σ * u 0 = 1 - Complex.exp (2 * Real.pi * Complex.I * α) := by
    rw [← heq]; ring
  have hwpos : 0 < ‖2 * Real.pi * Complex.I * α‖ := by
    rw [hnorm_w]
    have h : 0 < ‖α‖ := norm_pos_iff.mpr hαne
    positivity
  have hσne : σ ≠ 0 := by
    intro h0
    have hexp : Complex.exp (2 * Real.pi * Complex.I * α) = 1 := by
      have h2 := hσu
      rw [h0, zero_mul] at h2
      exact (sub_eq_zero.mp h2.symm).symm
    have hlow := Complex.norm_exp_sub_one_sub_id_le (x := 2 * Real.pi * Complex.I * α)
      (le_trans hw1 (by norm_num))
    have htri : ‖2 * Real.pi * Complex.I * α‖
        ≤ ‖Complex.exp (2 * Real.pi * Complex.I * α) - 1 - (2 * Real.pi * Complex.I * α)‖
          + ‖Complex.exp (2 * Real.pi * Complex.I * α) - 1‖ := by
      have hsub : (Complex.exp (2 * Real.pi * Complex.I * α) - 1 - (2 * Real.pi * Complex.I * α))
          - (Complex.exp (2 * Real.pi * Complex.I * α) - 1) = -(2 * Real.pi * Complex.I * α) := by
        ring
      calc ‖2 * Real.pi * Complex.I * α‖
          = ‖(Complex.exp (2 * Real.pi * Complex.I * α) - 1 - (2 * Real.pi * Complex.I * α))
              - (Complex.exp (2 * Real.pi * Complex.I * α) - 1)‖ := by rw [hsub, norm_neg]
        _ ≤ _ := norm_sub_le _ _
    have hzero : ‖Complex.exp (2 * Real.pi * Complex.I * α) - 1‖ = 0 := by
      rw [hexp]; simp
    nlinarith [htri, hlow, hzero, hwpos, hw1]
  -- ## the base Fatou coordinate `Ψ` of `F = liftF u σ α` on the gate, and its derivative estimate
  obtain ⟨Ψ, hΨ₀⟩ := hF.1 (some ((ξ₁ : ℂ) - 1 / α)) (some (-(ξ₁ : ℂ)))
    (Work.Pert.liftF u σ α) hQAdm hL1.1
  have hΨ : MandelDim.IsFatouCoordOn (Work.Pert.liftF u σ α) Ψ (Work.Pert.Qm ξ₁ α) := hΨ₀.1
  have hFDE' : ∀ (Φ v : ℂ → ℂ) (z₀ : ℂ) (R : ℝ), R₁ ≤ R →
      DifferentiableOn ℂ Φ (Metric.ball z₀ R) → Set.InjOn Φ (Metric.ball z₀ R) →
      DifferentiableOn ℂ v (Metric.ball z₀ R) → (∀ z ∈ Metric.ball z₀ R, ‖v z - 1‖ < 1 / 4) →
      (∀ z ∈ Metric.ball z₀ R, z + v z ∈ Metric.ball z₀ R → Φ (z + v z) = Φ z + 1) →
      ‖deriv Φ z₀ - 1 / v z₀‖ ≤ C₂ / R :=
    fun Φ v z₀ R hR a b c d e => (hFDE Φ v z₀ R hR a b c d e).2
  have hder := dev_deriv_on_Qc hηpos hR₁ hC₂ (by linarith) (by linarith) hFDE' hξ₁ h2ξ hRe hαη
    hαne hσne hrr hrrpos hu hbdd heq hτrr hQAdm hL1 hΨ
  -- ## the journey geometry
  have hJA := jourA_subset_Qc_and_norm hηpos hη100 hξ₁ h2ξ hRe hF1α hαη
  have hJc : ∀ ζ ∈ Work.Pert.JourA η, ζ ∈ Work.Pert.Qc η ξ₁ α := hJA.1
  have hJnorm : ∀ ζ ∈ Work.Pert.JourA η, 13 * η / 40 ≤ ‖ζ‖ ∧ ‖ζ‖ ≤ 3 * η := hJA.2
  have hOmJA : ∀ ζ ∈ Work.Pert.Om η, ζ ∈ Work.Pert.JourA η := fun ζ hζ => Or.inl (Or.inl hζ)
  have hOmQc : ∀ ζ ∈ Work.Pert.Om η, ζ ∈ Work.Pert.Qc η ξ₁ α := fun ζ hζ => hJc ζ (hOmJA ζ hζ)
  have hτm : ∀ ζ ∈ Work.Pert.JourA η, Work.Pert.tauC σ α ζ ∈ Metric.ball 0 rr :=
    fun ζ hζ => hτrr ζ (hJc ζ hζ).1
  have hvt : ∀ ζ ∈ Work.Pert.JourA η, ‖Work.Pert.liftF u σ α ζ - (ζ + 1)‖ ≤ 1 / 32 :=
    fun ζ hζ => (hL1.1.2 ζ (hJc ζ hζ).1).1
  have hρη : 2000000 ≤ ρ * η := by
    rw [div_le_iff₀ hρpos] at hηρ
    linarith
  have hτb : ∀ ζ ∈ Work.Pert.JourA η, ‖Work.Pert.tauC σ α ζ‖ ≤ 4 / η := by
    intro ζ hζ
    have h1 : ‖Work.Pert.tauC σ α ζ‖ ≤ 1.05 / ‖ζ‖ :=
      tauC_region_le hηpos hη100 hσne hαne hu0 hαη heq ζ (hJnorm ζ hζ).2
    have hζpos : 0 < ‖ζ‖ := by have := (hJnorm ζ hζ).1; linarith
    have h2 : (1.05 : ℝ) / ‖ζ‖ ≤ 4 / η := by
      rw [div_le_iff₀ hζpos, show (4 / η) * ‖ζ‖ = 4 * ‖ζ‖ / η by ring, le_div_iff₀ hηpos]
      nlinarith [(hJnorm ζ hζ).1]
    linarith
  have hτs8 : ∀ ζ ∈ Work.Pert.JourA η, ‖Work.Pert.tauC σ α ζ‖ ≤ 1 / 8 := by
    intro ζ hζ
    have h := hτb ζ hζ
    have h2 : (4 : ℝ) / η ≤ 1 / 8 := by
      rw [div_le_iff₀ hηpos]
      linarith
    linarith
  -- ## `δu`
  have hτρ2 : 4 / η ≤ ρ / 2 := by
    rw [div_le_iff₀ hηpos]
    nlinarith [hρη]
  have hρ4 : 0 < ρ - 4 / η := by linarith
  set δu : ℝ := (1 / 1024 + 2 * ((ρ / (32 * η) / ρ + B * ρ ^ 2) / (ρ - 4 / η))) * (1024 / 1023)
    with hδu
  have hδu0 : 0 ≤ δu := by
    rw [hδu]
    have h2 : 0 ≤ ρ / (32 * η) / ρ + B * ρ ^ 2 := by positivity
    have h3 : 0 ≤ (ρ / (32 * η) / ρ + B * ρ ^ 2) / (ρ - 4 / η) := div_nonneg h2 hρ4.le
    positivity
  have hδu1 : δu ≤ 1 / 1000 := by
    rw [hδu]
    exact deltaU_arith hηpos hρpos hρ1 hB0 hηρ hBρ
  -- ## the `u`-deviation and the `ṽ`-bound on the journey
  have hf0b' : ∀ z ∈ Metric.closedBall 0 ρ, ‖f₀ z - z - z ^ 2‖ ≤ B * ‖z‖ ^ 3 := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hz
    exact hf0b z hz
  have hub : ∀ ζ ∈ Work.Pert.JourA η, ‖u (Work.Pert.tauC σ α ζ) - u 0‖
      ≤ 1 / 1024 + 2 * ((ρ / (32 * η) / ρ + B * ρ ^ 2) / (ρ - ‖Work.Pert.tauC σ α ζ‖)) := by
    intro ζ hζ
    have hτin : Work.Pert.tauC σ α ζ ∈ Metric.ball 0 rr := hτm ζ hζ
    have hτlt : ‖Work.Pert.tauC σ α ζ‖ < ρ := by
      have h1 : ‖Work.Pert.tauC σ α ζ‖ ≤ 4 / η := hτb ζ hζ
      have h2 : 4 / η ≤ ρ / 2 := hτρ2
      linarith
    have h2σ : 2 * ‖σ‖ ≤ ‖Work.Pert.tauC σ α ζ‖ :=
      tauC_lower_jourA hηpos hσne hαne hu0 hαη heq ζ hζ
    exact u_dev_le_of_nearOn_b hρpos hσne hf0 hB0 hu hbdd hform hu0 hNear hf0b'
      (Work.Pert.tauC σ α ζ) hτlt hτin h2σ
  have hδuub : ∀ ζ ∈ Work.Pert.JourA η, ‖u (Work.Pert.tauC σ α ζ) - u 0‖ / ‖u 0‖ ≤ δu := by
    intro ζ hζ
    have h1 := hub ζ hζ
    have h2 : ‖Work.Pert.tauC σ α ζ‖ ≤ 4 / η := hτb ζ hζ
    have h3 : ρ - 4 / η ≤ ρ - ‖Work.Pert.tauC σ α ζ‖ := by linarith
    have h4 : 2 * ((ρ / (32 * η) / ρ + B * ρ ^ 2) / (ρ - ‖Work.Pert.tauC σ α ζ‖))
        ≤ 2 * ((ρ / (32 * η) / ρ + B * ρ ^ 2) / (ρ - 4 / η)) := by
      have hnum : 0 ≤ ρ / (32 * η) / ρ + B * ρ ^ 2 := by positivity
      exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left hnum hρ4 h3) (by norm_num)
    have h5 : ‖u (Work.Pert.tauC σ α ζ) - u 0‖
        ≤ 1 / 1024 + 2 * ((ρ / (32 * η) / ρ + B * ρ ^ 2) / (ρ - 4 / η)) := by linarith
    have hA : 0 ≤ 1 / 1024 + 2 * ((ρ / (32 * η) / ρ + B * ρ ^ 2) / (ρ - 4 / η)) := by positivity
    have hfac : 1 ≤ (1024 / 1023 : ℝ) * ‖u 0‖ := by nlinarith [hu0n]
    rw [div_le_iff₀ hu0pos, hδu]
    calc ‖u (Work.Pert.tauC σ α ζ) - u 0‖
        ≤ 1 / 1024 + 2 * ((ρ / (32 * η) / ρ + B * ρ ^ 2) / (ρ - 4 / η)) := h5
      _ ≤ (1 / 1024 + 2 * ((ρ / (32 * η) / ρ + B * ρ ^ 2) / (ρ - 4 / η)))
            * ((1024 / 1023) * ‖u 0‖) := le_mul_of_one_le_right hA hfac
      _ = (1 / 1024 + 2 * ((ρ / (32 * η) / ρ + B * ρ ^ 2) / (ρ - 4 / η)))
            * (1024 / 1023) * ‖u 0‖ := by ring
  have hvl : ∀ ζ ∈ Work.Pert.JourA η, ‖Work.Pert.liftF u σ α ζ - (ζ + 1)‖ ≤
      (3 / 2) * (‖Work.Pert.tauC σ α ζ‖ * ‖u (Work.Pert.tauC σ α ζ)‖ + δu) := by
    intro ζ hζ
    have h1 := vtilde_le_jourA (ξ₁ := ξ₁) hαne hσne hu0 heq h2πa hu hτm hτs8 hvt ζ hζ
    have h2 := hδuub ζ hζ
    linarith
  -- ## the oscillation bounds for `dev Ψ` and for `Eu`
  have hDr := dev_rad_cross_le_a hη100 hξ₁ h2ξ hδu0 hΨ hder (fun z hz => (hbdd z hz).2)
    hvt hJc hτm hτb hvl
  have hEu := EuDevBounds hηpos hη100 hσne hαne hu0 hαη heq
  obtain ⟨hEuA, hEuB, hEuC, hEuD⟩ := hEu
  obtain ⟨hDrA, hDrB, hDrC⟩ := hDr
  have hDrAc : ∀ ζ ∈ Metric.closedBall zc (13 * η / 40),
      ‖Work.Pert.dev Ψ ζ - Work.Pert.dev Ψ zc‖ ≤ (3 / 2 * δu + 1 / 3000) * η + 20 := by
    intro ζ hζ; rw [hzc]; exact hDrA ζ hζ
  have hDrBc : ∀ ζ ∈ Metric.closedBall (-zc) (13 * η / 40),
      ‖Work.Pert.dev Ψ ζ - Work.Pert.dev Ψ (-zc)‖ ≤ (3 / 2 * δu + 1 / 3000) * η + 20 := by
    intro ζ hζ; rw [hzc] at hζ ⊢; exact hDrB ζ hζ
  have hEuAc : ∀ ζ ∈ Metric.closedBall zc (13 * η / 40),
      ‖Eu σ α ζ - Eu σ α zc‖ ≤ η / 148 := by
    intro ζ hζ; rw [hzc] at hζ ⊢; exact hEuA ζ hζ
  have hEuBc : ∀ ζ ∈ Metric.closedBall (-zc) (13 * η / 40),
      ‖Eu σ α ζ - Eu σ α (-zc)‖ ≤ η / 148 := by
    intro ζ hζ; rw [hzc] at hζ ⊢; exact hEuB ζ hζ
  have hEuCc : ‖Eu σ α zc - Eu σ α (-zc)‖ ≤ η / 450 := by
    rw [hzc]
    simp only [Work.Pert.Eu]
    exact hEuC
  have hEuDc : ‖Eu σ α zc + Eu σ α (-zc)‖ ≤ η / 60 := by
    rw [hzc]
    simp only [Work.Pert.Eu]
    exact hEuD
  have hDrCc : ‖Work.Pert.dev Ψ zc - Work.Pert.dev Ψ (-zc)‖
      ≤ (5 * δu + 1 / 1000) * η + 100 := by
    rw [hzc]; simpa using hDrC
  -- ## the additive constant, the coordinate, and the derivative bound
  set cC : ℂ := ((Eu σ α zc - Work.Pert.dev Ψ zc)
    + (Eu σ α (-zc) - Work.Pert.dev Ψ (-zc))) / 2 with hcC
  have hΦm : MandelDim.IsFatouCoordOn (Work.Pert.liftF u σ α) (fun z => Ψ z + cC)
      (Work.Pert.Qm ξ₁ α) := by
    refine ⟨?_, ?_, ?_⟩
    · exact hΨ.1.add_const cC
    · intro x hx y hy hxy
      simp only at hxy
      exact hΨ.2.1 hx hy (add_right_cancel hxy)
    · intro z hz hFz
      change Ψ (Work.Pert.liftF u σ α z) + cC = Ψ z + cC + 1
      rw [hΨ.2.2 z hz hFz]; ring
  have hDiffAtOm : ∀ ζ ∈ Work.Pert.Om η, DifferentiableAt ℂ Ψ ζ := by
    intro ζ hζ
    have hQc := hOmQc ζ hζ
    exact (hΨ.1 ζ hQc.1).differentiableAt
      (Filter.mem_of_superset (Metric.ball_mem_nhds ζ (by positivity : (0 : ℝ) < η / 100))
        (fun z hz => hQc.2 (Metric.ball_subset_closedBall hz)))

  have hDiffAt : ∀ ζ ∈ Work.Pert.JourA η, DifferentiableAt ℂ Ψ ζ := by
    intro ζ hζ
    have hQc := hJc ζ hζ
    exact (hΨ.1 ζ hQc.1).differentiableAt
      (Filter.mem_of_superset (Metric.ball_mem_nhds ζ (by positivity : (0 : ℝ) < η / 100))
        (fun z hz => hQc.2 (Metric.ball_subset_closedBall hz)))
  have hDp : ∀ ζ ∈ Work.Pert.JourA η, ‖deriv (Work.Pert.dev Ψ) ζ‖ ≤ 1 / 400 := by
    intro ζ hζ
    have hQc := hJc ζ hζ
    have hdΨ : DifferentiableAt ℂ Ψ ζ := hDiffAt ζ hζ
    have hdev : deriv (Work.Pert.dev Ψ) ζ = deriv Ψ ζ - 1 := by
      change deriv (fun z => Ψ z - z) ζ = deriv Ψ ζ - 1
      exact (hdΨ.hasDerivAt.sub (hasDerivAt_id ζ)).deriv
    rw [hdev]
    have hderζ : ‖deriv Ψ ζ - 1 / (Work.Pert.liftF u σ α ζ - ζ)‖ ≤ 1 / 10000 := hder ζ hQc
    have hτs : ‖Work.Pert.tauC σ α ζ‖ ≤ 1 / 1000000 := by
      have h := hτb ζ hζ
      have h2 : (4 : ℝ) / η ≤ 1 / 1000000 := by
        rw [div_le_iff₀ hηpos]; linarith
      linarith
    have hvn : ‖Work.Pert.liftF u σ α ζ - ζ - 1‖ ≤ 1 / 500 := by
      have hvlζ := hvl ζ hζ
      have h1 : ‖Work.Pert.liftF u σ α ζ - (ζ + 1)‖
          = ‖Work.Pert.liftF u σ α ζ - ζ - 1‖ := by
        congr 1; ring
      rw [h1] at hvlζ
      have h2 : ‖u (Work.Pert.tauC σ α ζ)‖ ≤ 2 := (hbdd (Work.Pert.tauC σ α ζ) (hτm ζ hζ)).2
      have h4 : ‖Work.Pert.tauC σ α ζ‖ * ‖u (Work.Pert.tauC σ α ζ)‖
          ≤ (1 / 1000000) * 2 :=
        mul_le_mul hτs h2 (norm_nonneg _) (by norm_num)
      linarith only [hvlζ, h4, hδu1]
    have hlow : (31 : ℝ) / 32 ≤ ‖Work.Pert.liftF u σ α ζ - ζ‖ := by
      have h2 : (1 : ℝ) ≤ ‖Work.Pert.liftF u σ α ζ - ζ‖
          + ‖Work.Pert.liftF u σ α ζ - ζ - 1‖ := by
        have h3 : ‖(1 : ℂ)‖ = ‖(Work.Pert.liftF u σ α ζ - ζ)
            - (Work.Pert.liftF u σ α ζ - ζ - 1)‖ := by
          rw [show (Work.Pert.liftF u σ α ζ - ζ) - (Work.Pert.liftF u σ α ζ - ζ - 1) = (1 : ℂ)
            by ring]
        rw [norm_one] at h3
        calc (1 : ℝ) = ‖(Work.Pert.liftF u σ α ζ - ζ)
              - (Work.Pert.liftF u σ α ζ - ζ - 1)‖ := h3
          _ ≤ ‖Work.Pert.liftF u σ α ζ - ζ‖ + ‖Work.Pert.liftF u σ α ζ - ζ - 1‖ :=
              norm_sub_le _ _
      linarith only [h2, hvn]
    have h3 : ‖1 / (Work.Pert.liftF u σ α ζ - ζ) - 1‖ ≤ (32 / 31) * (1 / 500) := by
      have hxne : Work.Pert.liftF u σ α ζ - ζ ≠ 0 := by
        intro h0
        have h1 := hlow
        rw [h0, norm_zero] at h1
        norm_num at h1
      have h4 : 1 / (Work.Pert.liftF u σ α ζ - ζ) - 1
          = -(Work.Pert.liftF u σ α ζ - ζ - 1) / (Work.Pert.liftF u σ α ζ - ζ) := by
        field_simp
        ring
      rw [h4, norm_div, norm_neg]
      rw [div_le_iff₀ (by linarith only [hlow] :
        (0 : ℝ) < ‖Work.Pert.liftF u σ α ζ - ζ‖)]
      calc ‖Work.Pert.liftF u σ α ζ - ζ - 1‖ ≤ 1 / 500 := hvn
        _ ≤ (32 / 31) * (1 / 500) * (31 / 32) := by norm_num
        _ ≤ (32 / 31) * (1 / 500) * ‖Work.Pert.liftF u σ α ζ - ζ‖ :=
            mul_le_mul_of_nonneg_left hlow (by norm_num)
    have h5 : ‖deriv Ψ ζ - 1‖
        ≤ ‖deriv Ψ ζ - 1 / (Work.Pert.liftF u σ α ζ - ζ)‖
          + ‖1 / (Work.Pert.liftF u σ α ζ - ζ) - 1‖ := by
      have h6 : deriv Ψ ζ - 1 = (deriv Ψ ζ - 1 / (Work.Pert.liftF u σ α ζ - ζ))
          + (1 / (Work.Pert.liftF u σ α ζ - ζ) - 1) := by ring
      rw [h6]; exact norm_add_le _ _
    linarith only [hderζ, h3, h5]
  -- ## the clause
  refine ⟨fun z => Ψ z + cC, hΦm, ?_⟩
  have key : ∀ (c₀ : ℂ), (c₀ = zc ∨ c₀ = -zc) → ∀ w ∈ Metric.closedBall c₀ (3 * η / 10),
      (∃ ζ ∈ Work.Pert.Qm ξ₁ α, (fun z => Ψ z + cC) ζ = w) ∧
      (∀ ζ' ∈ Work.Pert.Qm ξ₁ α, (fun z => Ψ z + cC) ζ' = w →
        ‖MandelDim.tau0 (Work.Pert.tauC σ α ζ') - w‖ ≤ η / 70) := by
    intro c₀ hc₀ w hw
    have hw3 : ‖w - c₀‖ ≤ 3 * η / 10 := by
      rw [Metric.mem_closedBall, dist_eq_norm] at hw; exact hw
    have omOf : ∀ ζ : ℂ, ‖ζ - c₀‖ ≤ 13 * η / 40 → ζ ∈ Work.Pert.Om η := by
      intro ζ hζ
      rcases hc₀ with h | h
      · apply Or.inl
        rw [Metric.mem_closedBall, dist_eq_norm]
        rw [h, hzc] at hζ
        exact hζ
      · apply Or.inr
        rw [Metric.mem_closedBall, dist_eq_norm]
        rw [h, hzc] at hζ
        exact hζ
    have hw13 : ∀ c : ℂ, c = c₀ → w ∈ Metric.closedBall c (13 * η / 40) := by
      intro c hc
      rw [hc]
      exact Metric.closedBall_subset_closedBall
        (by linarith only [hηpos] : 3 * η / 10 ≤ 13 * η / 40) hw
    have hDc₀ : ‖Work.Pert.dev Ψ w - Work.Pert.dev Ψ c₀‖ ≤ (3 / 2 * δu + 1 / 3000) * η + 20 := by
      rcases hc₀ with h | h
      · rw [h]; exact hDrAc w (hw13 zc h.symm)
      · rw [h]; exact hDrBc w (hw13 (-zc) (by rw [h]))
    have hDx : ‖Work.Pert.dev Ψ c₀ - Work.Pert.dev Ψ (-c₀)‖ ≤ (5 * δu + 1 / 1000) * η + 100 := by
      rcases hc₀ with h | h
      · rw [h]; exact hDrCc
      · rw [h, neg_neg]; exact le_trans (le_of_eq (norm_sub_rev _ _)) hDrCc
    have hEux : ‖Eu σ α c₀ - Eu σ α (-c₀)‖ ≤ η / 450 := by
      rcases hc₀ with h | h
      · rw [h]; exact hEuCc
      · rw [h, neg_neg]; exact le_trans (le_of_eq (norm_sub_rev _ _)) hEuCc
    have hc₀C : cC = ((Eu σ α c₀ - Work.Pert.dev Ψ c₀)
        + (Eu σ α (-c₀) - Work.Pert.dev Ψ (-c₀))) / 2 := by
      rcases hc₀ with h | h
      · simpa [h] using hcC
      · rw [h]; simp only [neg_neg]; rw [hcC]; ring
    have hDwc : ‖Work.Pert.dev Ψ w + cC‖ ≤ 14 * η / 1000 := by
      have h7 : Work.Pert.dev Ψ w + cC
          = (Work.Pert.dev Ψ w - Work.Pert.dev Ψ c₀)
            + (Work.Pert.dev Ψ c₀ - Work.Pert.dev Ψ (-c₀)) / 2
            + (Eu σ α zc + Eu σ α (-zc)) / 2 := by
        rcases hc₀ with h | h
        · rw [h]; rw [hcC]; ring
        · rw [h]; simp only [neg_neg]; rw [hcC]; ring
      rw [h7]
      have h8 : ‖(Eu σ α zc + Eu σ α (-zc)) / 2‖ ≤ η / 120 := by
        rw [norm_div]; simp only [norm_ofNat]; linarith [hEuDc]
      have h9 : ‖(Work.Pert.dev Ψ c₀ - Work.Pert.dev Ψ (-c₀)) / 2‖
          ≤ ((5 * δu + 1 / 1000) * η + 100) / 2 := by
        rw [norm_div]; simp only [norm_ofNat]; linarith [hDx]
      have h11 : ((3 / 2 * δu + 1 / 3000) * η + 20)
          + ((5 * δu + 1 / 1000) * η + 100) / 2 + η / 120 ≤ 14 * η / 1000 := by
        have h12 : δu * η ≤ (1 / 1000 : ℝ) * η := mul_le_mul_of_nonneg_right hδu1 hηpos.le
        nlinarith only [h12, hηpos, hηbig]
      calc ‖(Work.Pert.dev Ψ w - Work.Pert.dev Ψ c₀)
            + (Work.Pert.dev Ψ c₀ - Work.Pert.dev Ψ (-c₀)) / 2
            + (Eu σ α zc + Eu σ α (-zc)) / 2‖
          ≤ ‖(Work.Pert.dev Ψ w - Work.Pert.dev Ψ c₀)
              + (Work.Pert.dev Ψ c₀ - Work.Pert.dev Ψ (-c₀)) / 2‖
            + ‖(Eu σ α zc + Eu σ α (-zc)) / 2‖ := norm_add_le _ _
        _ ≤ (‖Work.Pert.dev Ψ w - Work.Pert.dev Ψ c₀‖
              + ‖(Work.Pert.dev Ψ c₀ - Work.Pert.dev Ψ (-c₀)) / 2‖)
            + ‖(Eu σ α zc + Eu σ α (-zc)) / 2‖ := by
              linarith [norm_add_le (Work.Pert.dev Ψ w - Work.Pert.dev Ψ c₀)
                ((Work.Pert.dev Ψ c₀ - Work.Pert.dev Ψ (-c₀)) / 2)]
        _ ≤ 14 * η / 1000 := by linarith [hDc₀, h9, h8, h11]
    -- ## the covering argument
    set z₀ : ℂ := w - (Work.Pert.dev Ψ w + cC) with hz₀
    have htri₀ : ‖z₀ - c₀‖ ≤ ‖w - c₀‖ + ‖Work.Pert.dev Ψ w + cC‖ := by
      rw [hz₀]
      calc ‖w - (Work.Pert.dev Ψ w + cC) - c₀‖
          = ‖(w - c₀) - (Work.Pert.dev Ψ w + cC)‖ := by ring_nf
        _ ≤ ‖w - c₀‖ + ‖Work.Pert.dev Ψ w + cC‖ := norm_sub_le _ _
    have hz₀sh : ‖z₀ - c₀‖ ≤ 314 * η / 1000 := by
      linarith only [htri₀, hw3, hDwc, hηpos]
    have hz₀mem : z₀ ∈ Metric.closedBall c₀ (13 * η / 40) := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      linarith only [hz₀sh, hηpos]
    have hz₀Om : z₀ ∈ Work.Pert.Om η := by
      apply omOf
      have := hz₀mem
      rw [Metric.mem_closedBall, dist_eq_norm] at this
      exact this
    have hz₀Qc : z₀ ∈ Work.Pert.Qc η ξ₁ α := hJc z₀ (hOmJA z₀ hz₀Om)
    have hw13' : w ∈ Metric.closedBall c₀ (13 * η / 40) := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      linarith only [hw3, hηpos]
    have hseg : ∀ x ∈ segment ℝ w z₀, x ∈ Work.Pert.Om η := by
      intro x hx
      apply omOf
      have h1 : x ∈ Metric.closedBall c₀ (13 * η / 40) :=
        Convex.segment_subset (convex_closedBall c₀ (13 * η / 40)) hw13' hz₀mem hx
      rwa [Metric.mem_closedBall, dist_eq_norm] at h1
    have hMVT : ‖Work.Pert.dev Ψ z₀ - Work.Pert.dev Ψ w‖ ≤ (1 / 400) * ‖z₀ - w‖ := by
      refine Convex.norm_image_sub_le_of_norm_deriv_le ?_ ?_ (convex_segment w z₀)
        (left_mem_segment ℝ w z₀) (right_mem_segment ℝ w z₀)
      · intro x hx
        exact ((hDiffAt x (hOmJA x (hseg x hx))).sub differentiableAt_id)
      · intro x hx
        exact hDp x (hOmJA x (hseg x hx))
    have hdiff : ∀ ζ ∈ Metric.closedBall z₀ (η / 200),
        DifferentiableAt ℂ (fun z => Ψ z + cC) ζ := by
      intro ζ hζ
      have h1 : ‖ζ - z₀‖ ≤ η / 200 := by
        have := hζ; rw [Metric.mem_closedBall, dist_eq_norm] at this; exact this
      have h2 : ‖ζ - c₀‖ ≤ 13 * η / 40 := by
        have h3 : ‖ζ - c₀‖ ≤ ‖ζ - z₀‖ + ‖z₀ - c₀‖ := by
          calc ‖ζ - c₀‖ = ‖(ζ - z₀) + (z₀ - c₀)‖ := by ring_nf
            _ ≤ ‖ζ - z₀‖ + ‖z₀ - c₀‖ := norm_add_le _ _
        linarith only [h3, h1, hz₀sh, hηpos]
      exact (hDiffAt ζ (hOmJA ζ (omOf ζ h2))).add_const cC
    have hderΦ : ∀ ζ ∈ Metric.closedBall z₀ (η / 200),
        ‖deriv (fun z => Ψ z + cC) ζ - 1‖ ≤ 1 / 2 := by
      intro ζ hζ
      have h1 : ‖ζ - z₀‖ ≤ η / 200 := by
        have := hζ; rw [Metric.mem_closedBall, dist_eq_norm] at this; exact this
      have h2 : ‖ζ - c₀‖ ≤ 13 * η / 40 := by
        have h3 : ‖ζ - c₀‖ ≤ ‖ζ - z₀‖ + ‖z₀ - c₀‖ := by
          calc ‖ζ - c₀‖ = ‖(ζ - z₀) + (z₀ - c₀)‖ := by ring_nf
            _ ≤ ‖ζ - z₀‖ + ‖z₀ - c₀‖ := norm_add_le _ _
        linarith only [h3, h1, hz₀sh, hηpos]
      have hζJA : ζ ∈ Work.Pert.JourA η := hOmJA ζ (omOf ζ h2)
      have hd : deriv (fun z => Ψ z + cC) ζ = deriv Ψ ζ := by
        have h := ((hDiffAt ζ hζJA).hasDerivAt.add_const cC).deriv
        rw [h]
      rw [hd]
      have h3 : deriv (Work.Pert.dev Ψ) ζ = deriv Ψ ζ - 1 := by
        change deriv (fun z => Ψ z - z) ζ = deriv Ψ ζ - 1
        exact ((hDiffAt ζ hζJA).hasDerivAt.sub (hasDerivAt_id ζ)).deriv
      have h4 := hDp ζ hζJA
      rw [h3] at h4
      linarith
    have hcover := image_cover_centered (show (0 : ℝ) < η / 200 by positivity) hdiff hderΦ
    have hmem : w ∈ Metric.ball ((fun z => Ψ z + cC) z₀) ((η / 200) / 4) := by
      rw [Metric.mem_ball, dist_eq_norm]
      rw [norm_sub_rev w ((fun z => Ψ z + cC) z₀)]
      have h2 : ‖z₀ - w‖ = ‖Work.Pert.dev Ψ w + cC‖ := by
        rw [hz₀, show w - (Work.Pert.dev Ψ w + cC) - w = -(Work.Pert.dev Ψ w + cC) by ring,
          norm_neg]
      have h6 : ‖(fun z => Ψ z + cC) z₀ - w‖ = ‖Work.Pert.dev Ψ z₀ - Work.Pert.dev Ψ w‖ := by
        have h7 : (fun z => Ψ z + cC) z₀ - w = Work.Pert.dev Ψ z₀ - Work.Pert.dev Ψ w := by
          rw [hz₀]
          simp only [Work.Pert.dev]
          ring
        rw [h7]
      rw [h6]
      have h8 : (1 / 400 : ℝ) * ‖z₀ - w‖ ≤ (1 / 400) * (14 * η / 1000) := by
        rw [h2]; exact mul_le_mul_of_nonneg_left hDwc (by norm_num)
      have h9 : (1 / 400 : ℝ) * (14 * η / 1000) < (η / 200) / 4 := by
        nlinarith only [hηpos]
      linarith only [hMVT, h8, h9]
    obtain ⟨ζ, hζball, hζeq⟩ := hcover hmem
    have hζOm : ζ ∈ Work.Pert.Om η := by
      have h1 : ‖ζ - z₀‖ ≤ η / 200 := by
        have := hζball; rw [Metric.mem_closedBall, dist_eq_norm] at this; exact this
      apply omOf
      have h3 : ‖ζ - c₀‖ ≤ ‖ζ - z₀‖ + ‖z₀ - c₀‖ := by
        calc ‖ζ - c₀‖ = ‖(ζ - z₀) + (z₀ - c₀)‖ := by ring_nf
          _ ≤ ‖ζ - z₀‖ + ‖z₀ - c₀‖ := norm_add_le _ _
      linarith only [h3, h1, hz₀sh, hηpos]
    have hζQc : ζ ∈ Work.Pert.Qc η ξ₁ α := hJc ζ (hOmJA ζ hζOm)
    refine ⟨⟨ζ, hζQc.1, hζeq⟩, ?_⟩
    intro ζ' hζ'Qm hζ'eq
    have hEq : ζ' = ζ := hΦm.2.1 hζ'Qm hζQc.1 (by rw [hζ'eq, hζeq])
    subst ζ'
    have hkey2 : MandelDim.tau0 (Work.Pert.tauC σ α ζ) - w
        = (Eu σ α ζ - Eu σ α c₀) + (Eu σ α c₀ - Eu σ α (-c₀)) / 2
          - (Work.Pert.dev Ψ ζ - Work.Pert.dev Ψ c₀)
          - (Work.Pert.dev Ψ c₀ - Work.Pert.dev Ψ (-c₀)) / 2 := by
      have hw' : w = ζ + Work.Pert.dev Ψ ζ + cC := by
        rw [← hζeq]
        simp only [Work.Pert.dev]
        ring
      rw [hw', hc₀C]
      simp only [Work.Pert.Eu]
      ring
    rw [hkey2]
    -- bounds at `ζ`
    have hζc₀ : ‖ζ - c₀‖ ≤ 13 * η / 40 := by
      have h1 : ‖ζ - z₀‖ ≤ η / 200 := by
        have := hζball; rw [Metric.mem_closedBall, dist_eq_norm] at this; exact this
      have h3 : ‖ζ - c₀‖ ≤ ‖ζ - z₀‖ + ‖z₀ - c₀‖ := by
        calc ‖ζ - c₀‖ = ‖(ζ - z₀) + (z₀ - c₀)‖ := by ring_nf
          _ ≤ ‖ζ - z₀‖ + ‖z₀ - c₀‖ := norm_add_le _ _
      linarith only [h3, h1, hz₀sh, hηpos]
    have hζc₀' : ζ ∈ Metric.closedBall c₀ (13 * η / 40) := by
      rw [Metric.mem_closedBall, dist_eq_norm]; exact hζc₀
    have hE1 : ‖Eu σ α ζ - Eu σ α c₀‖ ≤ η / 148 := by
      rcases hc₀ with h | h
      · rw [h]; exact hEuAc ζ (by rw [← h]; exact hζc₀')
      · rw [h]; exact hEuBc ζ (by rw [← h]; exact hζc₀')
    have hD1 : ‖Work.Pert.dev Ψ ζ - Work.Pert.dev Ψ c₀‖
        ≤ (3 / 2 * δu + 1 / 3000) * η + 20 := by
      rcases hc₀ with h | h
      · rw [h]; exact hDrAc ζ (by rw [← h]; exact hζc₀')
      · rw [h]; exact hDrBc ζ (by rw [← h]; exact hζc₀')
    have hfin : η / 148 + η / 900 + ((3 / 2 * δu + 1 / 3000) * η + 20)
        + ((5 * δu + 1 / 1000) * η + 100) / 2 ≤ η / 70 := by
      have h12 : δu * η ≤ (1 / 1000 : ℝ) * η := mul_le_mul_of_nonneg_right hδu1 hηpos.le
      nlinarith [h12, hηpos]
    calc ‖(Eu σ α ζ - Eu σ α c₀) + (Eu σ α c₀ - Eu σ α (-c₀)) / 2
          - (Work.Pert.dev Ψ ζ - Work.Pert.dev Ψ c₀)
          - (Work.Pert.dev Ψ c₀ - Work.Pert.dev Ψ (-c₀)) / 2‖
        ≤ ‖Eu σ α ζ - Eu σ α c₀‖ + ‖(Eu σ α c₀ - Eu σ α (-c₀)) / 2‖
          + ‖Work.Pert.dev Ψ ζ - Work.Pert.dev Ψ c₀‖
          + ‖(Work.Pert.dev Ψ c₀ - Work.Pert.dev Ψ (-c₀)) / 2‖ := by
            have ha := norm_add_le (Eu σ α ζ - Eu σ α c₀) ((Eu σ α c₀ - Eu σ α (-c₀)) / 2)
            have hb := norm_sub_le ((Eu σ α ζ - Eu σ α c₀) + (Eu σ α c₀ - Eu σ α (-c₀)) / 2)
              (Work.Pert.dev Ψ ζ - Work.Pert.dev Ψ c₀)
            have hc := norm_sub_le ((Eu σ α ζ - Eu σ α c₀) + (Eu σ α c₀ - Eu σ α (-c₀)) / 2
              - (Work.Pert.dev Ψ ζ - Work.Pert.dev Ψ c₀))
              ((Work.Pert.dev Ψ c₀ - Work.Pert.dev Ψ (-c₀)) / 2)
            have hd := norm_div (Eu σ α c₀ - Eu σ α (-c₀)) 2
            have he := norm_div (Work.Pert.dev Ψ c₀ - Work.Pert.dev Ψ (-c₀)) 2
            simp only [norm_ofNat] at hd he
            linarith [ha, hb, hc, hd, he, norm_nonneg (Eu σ α ζ - Eu σ α c₀),
              norm_nonneg (Eu σ α c₀ - Eu σ α (-c₀)),
              norm_nonneg (Work.Pert.dev Ψ ζ - Work.Pert.dev Ψ c₀),
              norm_nonneg (Work.Pert.dev Ψ c₀ - Work.Pert.dev Ψ (-c₀))]
      _ ≤ η / 70 := by
        have h1 : ‖(Eu σ α c₀ - Eu σ α (-c₀)) / 2‖ ≤ η / 900 := by
          rw [norm_div]; simp only [norm_ofNat]; linarith [hEux]
        have h2 : ‖(Work.Pert.dev Ψ c₀ - Work.Pert.dev Ψ (-c₀)) / 2‖
            ≤ ((5 * δu + 1 / 1000) * η + 100) / 2 := by
          rw [norm_div]; simp only [norm_ofNat]; linarith [hDx]
        linarith [hE1, hD1, h1, h2, hfin]
  intro w hw
  rw [Set.mem_union] at hw
  exact hw.elim (key zc (Or.inl rfl) w) (key (-zc) (Or.inr rfl) w)


end Work.Pert
