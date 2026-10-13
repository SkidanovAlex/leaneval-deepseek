import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS_RegExport.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Construction.Defs
import Submission.Work.FTS_RegExport.RXT.Defs
import Submission.Work.FTS_RegExport.RXT.Pullback
import Submission.Work.FTS_RegExport.RXT.Continuity
import Submission.Work.FTS_RegExport.RXT.Bounds
import Submission.Work.FTS_RegExport.RXT.cone_max_principle

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.transport_weighted_proved` — RX-T (the weighted characteristic
estimate of the transport operator of `(E)`).

The statement (`Producers.transport_weighted`, verbatim) is the pointwise weighted estimate

  `|u z θ τ| ≤ e^{K·S}·(K₀ + S·Kσ)·ω α z θ`

for a solution of `∂_τu + Vz·D_z u + Vθ·∂_θu + cs·u = σ` on the open quadrant with
`0 ≤ Vz ≤ M`, `|Vθ| ≤ M·sin 2θ`, `|cs| ≤ M`, `|σ| ≤ Kσ·ω` and data bounded by `K₀·ω` at `τ = 0`.

## The route (no characteristic ODE is used — and none is available)

The hypotheses give *no* regularity of `Vz, Vθ, cs, σ` in `τ` and only a *per-`τ`* Lipschitz
bound, so the classical characteristic flow cannot be constructed.  Instead one works with the
**cone maximum principle** (`RXT.cone_max_principle`): in the logarithmic coordinates of
`RXT.Defs` the domain becomes all of `ℝ²`, the transport coefficients become the bounded
quantities `a = Vz`, `b = 2Vθ/sin 2θ`, and the weight ratio `φ = u/ω` satisfies a transport
equation with `|a|,|b| ≤ 2M`, `|c| ≤ M(3+4α)`, `|f| ≤ Kσ`, `|φ(·,0)| ≤ K₀`.  The cone maximum
principle then gives `|φ| ≤ exp(2·M(3+4α)·τ)·(K₀ + τ·Kσ)`, which is the statement with
`K = 2M(3+4α)`.
-/

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS_RegExport.RXT

set_option autoImplicit false

set_option linter.unusedVariables false in
theorem transport_weighted_proved {α S M K₀ Kσ : ℝ} (hα : 0 < α) (hS : 0 < S)
    {u Vz Vθ cs σ : ℝ → ℝ → ℝ → ℝ}
    (hu : ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => u p.1 p.2.1 p.2.2)
      (Set.Ioi (0:ℝ) ×ˢ Set.Ioo (0:ℝ) (Real.pi / 2) ×ˢ Set.Icc (0:ℝ) S))
    (hEq : ∀ z θ τ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 < τ → τ ≤ S →
      HasDerivAt (fun s => u z θ s)
        (σ z θ τ - (Vz z θ τ * Work.Spaces.Dz (fun z θ => u z θ τ) z θ
          + Vθ z θ τ * Work.Spaces.pth (fun z θ => u z θ τ) z θ + cs z θ τ * u z θ τ)) τ)
    (hVz : ∀ z θ τ, 0 < z → 0 < θ → θ < Real.pi / 2 → τ ∈ Set.Icc 0 S →
      0 ≤ Vz z θ τ ∧ Vz z θ τ ≤ M)
    (hVθ : ∀ z θ τ, 0 < z → 0 < θ → θ < Real.pi / 2 → τ ∈ Set.Icc 0 S →
      |Vθ z θ τ| ≤ M * Real.sin (2 * θ))
    (hlip : ∀ τ ∈ Set.Icc 0 S, ∀ L₁ > 0, ∃ K : NNReal, LipschitzOnWith K
      (fun p : ℝ × ℝ => (Vz p.1 p.2 τ, Vθ p.1 p.2 τ)) (Set.Ioi L₁ ×ˢ Set.Ioo (0:ℝ) (Real.pi / 2)))
    (hcs : ∀ z θ τ, 0 < z → 0 < θ → θ < Real.pi / 2 → τ ∈ Set.Icc 0 S → |cs z θ τ| ≤ M)
    (hσ : ∀ z θ τ, 0 < z → 0 < θ → θ < Real.pi / 2 → τ ∈ Set.Icc 0 S →
      |σ z θ τ| ≤ Kσ * Work.FTS.RegExportIface.ω α z θ)
    (h0 : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |u z θ 0| ≤ K₀ * Work.FTS.RegExportIface.ω α z θ) :
    ∃ K : ℝ, ∀ z θ τ, 0 < z → 0 < θ → θ < Real.pi / 2 → τ ∈ Set.Icc 0 S →
      |u z θ τ| ≤ Real.exp (K * S) * (K₀ + S * Kσ) * Work.FTS.RegExportIface.ω α z θ := by
  -- ## the parameters are non-negative
  have hπ4 : (0:ℝ) < Real.pi / 4 := by linarith [Real.pi_pos]
  have hπ4' : Real.pi / 4 < Real.pi / 2 := by linarith [Real.pi_pos]
  have hτ0 : (0:ℝ) ∈ Set.Icc (0:ℝ) S := ⟨le_rfl, hS.le⟩
  have hω1 : 0 < Work.FTS.RegExportIface.ω α 1 (Real.pi / 4) :=
    (omega_facts α hα).1 1 (Real.pi / 4) one_pos hπ4 hπ4'
  have hvz1 := hVz 1 (Real.pi / 4) 0 one_pos hπ4 hπ4' hτ0
  have hM : 0 ≤ M := le_trans hvz1.1 hvz1.2
  have hK₀ : 0 ≤ K₀ := by
    have h := h0 1 (Real.pi / 4) one_pos hπ4 hπ4'
    have h2 : 0 ≤ K₀ * Work.FTS.RegExportIface.ω α 1 (Real.pi / 4) := le_trans (abs_nonneg _) h
    nlinarith [h2, hω1]
  have hKσ : 0 ≤ Kσ := by
    have h := hσ 1 (Real.pi / 4) 0 one_pos hπ4 hπ4' hτ0
    have h2 : 0 ≤ Kσ * Work.FTS.RegExportIface.ω α 1 (Real.pi / 4) := le_trans (abs_nonneg _) h
    nlinarith [h2, hω1]
  have hC0 : 0 ≤ M * (3 + 4 * α) := mul_nonneg hM (by linarith [hα.le])
  have hA0 : 0 ≤ 2 * M := by linarith
  -- ## the cone maximum principle on the pulled-back unknown
  refine ⟨2 * M * (3 + 4 * α), ?_⟩
  intro z θ τ hz hθ0 hθπ hτmem
  obtain ⟨s, hs⟩ := exists_exp z hz
  have hsz : cz s = z := hs
  obtain ⟨ψ, hψ⟩ := exists_arctan_exp θ hθ0 hθπ
  have hψθ : cth ψ = θ := hψ
  have hcone := cone_max_principle (φ := phi α u) (φs := dphi_s α u) (φψ := dphi_ψ α u)
    (a := trA Vz) (b := trB Vθ) (c := trC α Vz Vθ cs) (f := trF α σ)
    (T := S) (A := 2 * M) (C := M * (3 + 4 * α)) (F := Kσ) (K₀ := K₀)
    hS hA0 hC0 hKσ hK₀
    (phi_continuous hα hu) (dphi_s_continuous hα hS hu) (dphi_ψ_continuous hα hS hu)
    (fun s ψ τ hτ => phi_hasDerivAt_s hα hu s ψ τ hτ)
    (fun s ψ τ hτ => phi_hasDerivAt_ψ hα hu s ψ τ hτ)
    (fun s ψ τ hτ0' hτS => phi_hasDerivAt_τ hα hEq s ψ τ hτ0' hτS)
    (fun s ψ τ hτ0' hτS => le_trans (trA_bound hVz s ψ τ hτ0' hτS) (by linarith [hM]))
    (fun s ψ τ hτ0' hτS => trB_bound hVθ s ψ τ hτ0' hτS)
    (fun s ψ τ hτ0' hτS => trC_bound hα hVz hVθ hcs s ψ τ hτ0' hτS)
    (fun s ψ τ hτ0' hτS => trF_bound hα hσ s ψ τ hτ0' hτS)
    (phi_zero_bound hα h0)
  have hb := hcone s ψ τ hτmem
  -- ## pull the estimate back to `(z,θ,τ)`
  have hom : 0 < om α s ψ := om_pos hα
  have hphi : |phi α u s ψ τ| = |u (cz s) (cth ψ) τ| / om α s ψ := by
    rw [phi, abs_div, abs_of_pos hom]
  rw [hphi, div_le_iff₀ hom] at hb
  have hωeq : om α s ψ = Work.FTS.RegExportIface.ω α z θ := by
    show Work.FTS.RegExportIface.ω α (cz s) (cth ψ) = Work.FTS.RegExportIface.ω α z θ
    rw [hsz, hψθ]
  have hu'' : |u z θ τ| ≤ Work.FTS.RegExportIface.ω α z θ
      * (Real.exp (2 * (M * (3 + 4 * α)) * τ) * (K₀ + τ * Kσ)) := by
    rw [mul_comm] at hb
    rw [hωeq, hsz, hψθ] at hb
    exact hb
  -- ## monotonicity in `τ`
  have hω0 : 0 ≤ Work.FTS.RegExportIface.ω α z θ := by
    have h := (omega_facts α hα).1 z θ hz hθ0 hθπ
    exact h.le
  have hexp_le : Real.exp (2 * (M * (3 + 4 * α)) * τ)
      ≤ Real.exp ((2 * M * (3 + 4 * α)) * S) := by
    apply Real.exp_le_exp.mpr
    nlinarith [hτmem.2, hM, hα.le]
  have hsum_le : K₀ + τ * Kσ ≤ K₀ + S * Kσ := by nlinarith [hτmem.2, hKσ]
  have hsum0 : 0 ≤ K₀ + τ * Kσ := by nlinarith [hτmem.1, hK₀, hKσ]
  have hcoef : Real.exp (2 * (M * (3 + 4 * α)) * τ) * (K₀ + τ * Kσ)
      ≤ Real.exp ((2 * M * (3 + 4 * α)) * S) * (K₀ + S * Kσ) :=
    mul_le_mul hexp_le hsum_le hsum0 (Real.exp_pos _).le
  refine le_trans hu'' ?_
  calc Work.FTS.RegExportIface.ω α z θ
        * (Real.exp (2 * (M * (3 + 4 * α)) * τ) * (K₀ + τ * Kσ))
      ≤ Work.FTS.RegExportIface.ω α z θ
        * (Real.exp ((2 * M * (3 + 4 * α)) * S) * (K₀ + S * Kσ)) :=
        mul_le_mul_of_nonneg_left hcoef hω0
    _ = Real.exp ((2 * M * (3 + 4 * α)) * S) * (K₀ + S * Kσ)
        * Work.FTS.RegExportIface.ω α z θ := by ring

end Work.FTS_RegExport.RXT