import Mathlib
import Submission.Work.Lattice.MaxPhiAccounting

/-!
# The accounting inequality at a *prescribed* good time

`MaxPhiAccounting.phi_accounting_of_capacity_le` chooses its own good time internally.  The
assembly needs the same inequality at a fixed good time (the one at which the flag is built), so
this module re-runs the (short) transfer argument with `t`, `hdiff` and the good-time inequality
as parameters.

Module `Submission.Work.Extraction.AccountingFix`, namespace `Submission.AccountingFix`.
-/

noncomputable section
open Module exteriorPower InnerProductGeometry Real
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1200000

namespace Submission.AccountingFix

open Submission.ExteriorCoordinates
open Submission.MaxPhiAccounting
open Submission.AngularRanks
open Submission.AccountingOneSided
open Submission.ImageLattice
open Submission.Polygon

variable {d : ℕ}

/-- **The accounting inequality at a prescribed good time.**  For any capacity sequence `ω` with
`ω 0 = 0`, `ω N = ℓ` which dominates the effective positions of the slacked polygon at the good
time `t`,

    `Σ_{s<N} (ω (s+1) − ω s)·phiSlope_s ≤ ℓ(d−ℓ)/d`. -/
theorem accounting_at {ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) (A : ℝ)
    (g : RD d ≃ₗᵢ[ℝ] RD d) {t : ℝ}
    (hdiff : ∀ i : Fin d, DifferentiableAt ℝ
      (fun x => phiSlope (d := d) (imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d)) ℓ A x i.val) t)
    (hgood0 : -1 ≤ ∑ i : Fin d,
      phiSlope (d := d) (imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d)) ℓ A t i.val *
      deriv (fun x => phiSlope (d := d) (imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d)) ℓ A x
        i.val) t) :
    ∀ ω : ℕ → ℝ,
      ω 0 = 0 →
      ω (numBlocks d (phiPolygonT (d := d) (imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d)) ℓ A t)) =
        (ℓ : ℝ) →
      (∀ s ≤ numBlocks d (phiPolygonT (d := d)
          (imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d)) ℓ A t),
        effPos d ℓ
          (fun s => (blockStart d (phiPolygonT (d := d)
            (imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d)) ℓ A t) s : ℝ))
          (phiLevelDeriv (d := d) (imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d)) ℓ A t
            (blockStart d (phiPolygonT (d := d)
              (imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d)) ℓ A t))) s ≤ ω s) →
      (∑ s ∈ Finset.range (numBlocks d (phiPolygonT (d := d)
            (imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d)) ℓ A t)),
          (ω (s + 1) - ω s) *
            phiSlope (d := d) (imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d)) ℓ A t
              (blockStart d (phiPolygonT (d := d)
                (imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d)) ℓ A t) s))
        ≤ (ℓ : ℝ) * ((d : ℝ) - (ℓ : ℝ)) / (d : ℝ) := by
  intro ω hω0 hωR hle
  have hd0 : 0 < d := lt_of_lt_of_le hℓ0 (le_of_lt hℓd)
  set Λ₀ : Submodule ℤ (RD d) := imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d) with hΛ₀
  set c : ℕ → ℝ := phiPolygonT (d := d) Λ₀ ℓ A t with hc
  set jb : ℕ → ℕ := blockStart d c with hjb
  set jbR : ℕ → ℝ := fun s => ((jb s : ℕ) : ℝ) with hjbR
  set r : ℕ → ℝ := phiLevelDeriv (d := d) Λ₀ ℓ A t jb with hr
  set Λs : ℕ → ℝ := fun s => phiSlope (d := d) Λ₀ ℓ A t (jb s) with hΛs
  set cap : ℕ → ℝ := fun s => effPos d ℓ jbR r s with hcap
  have hcap0 : cap 0 = 0 := by
    rw [hcap]
    exact effPos_zero (d := d) (ℓ := ℓ) (by simp [hjbR, hjb, blockStart_zero])
      (by rw [hr, phiLevelDeriv, hjb, blockStart_zero]; simp)
  have hrR : r (numBlocks d c) = 0 := by
    rw [hr]
    exact phiLevelDeriv_top_eq_zero (d := d) hℓ0 hℓd A g hdiff
  have hcapR : cap (numBlocks d c) = (ℓ : ℝ) := by
    rw [hcap]
    exact effPos_top (d := d) (ℓ := ℓ) hℓ0 hℓd (by simp [hjbR, hjb, blockStart_numBlocks]) hrR
  have hstep : ∀ s, s + 2 ≤ numBlocks d c → Λs s ≤ Λs (s + 1) := by
    intro s hs
    have hslt : s + 1 < numBlocks d c := by omega
    have hjb1 : jb (s + 1) < d := by
      rw [hjb]
      exact blockStart_lt_numBlocks _ _ hslt
    have h1 : jb s ≤ jb (s + 1) := by
      rw [hjb]
      exact blockStart_mono d c s
    simp only [hΛs]
    exact phiSlope_mono (d := d) A g h1 (by omega)
  have h1 := Submission.MaxNormAccounting.sum_delta_mul_le_of_le_range (R := numBlocks d c)
    (ω := cap) (ω' := ω) (Λ := Λs) hcap0 hω0 (by rw [hcapR, hωR]) hle hstep
  have h2 : (∑ s ∈ Finset.range (numBlocks d c),
        (cap (s + 1) - cap s) * Λs s) ≤ (ℓ : ℝ) * ((d : ℝ) - (ℓ : ℝ)) / (d : ℝ) := by
    rw [hcap, hΛs, hjbR, hr]
    simpa [hΛ₀, hc, hjb] using phi_accounting_at (d := d) hℓ0 hℓd A g hdiff hgood0
  linarith [h1, h2]

end Submission.AccountingFix

end
