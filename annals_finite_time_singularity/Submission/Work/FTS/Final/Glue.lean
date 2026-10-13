/-
# `Work.FTS.Final.Glue` — from the reconstruction's data to a blow-up at time `1`

This module is the *core* of the end-to-end wiring of FTS/Final.  Given

* the challenge exponent `α ∈ (0, 1/3]` with its profile exponent `pExp α = 3α`,
* a *family* `g`, a stream function `Φ`, an amplitude `A`, a companion `B` and a clock `C`,
* the uniform `ℋ⁴`-bound `Xn (pExp α) (slice g τ) ≤ C₀ (pExp α)²` and the pointwise sup bound
  `|g z θ τ| ≤ Cg · Xn (pExp α) (slice g τ)`,
* the amplitude normalisation `C.A = 2A`,
* the four analytic inputs of the physical bridge (the corrected regularity package `RegPkg'`, the
  meridian equation `MeridianEqOn`, the Biot–Savart identification `hid`, the two differentiability
  clauses `hΨ`, `hW`) and the pressure reconstruction,

it produces `Nonempty (Work.FTS.Top.BlowupAt ⟨α, _⟩ 1)`, i.e. a finite-time singularity of the
incompressible Euler equations in node N0's interface at time `T = 1`.

The proof is three steps, and it is here that the *interfaces* are checked:

1. **the smallness** `|g| ≤ 3α/200` from `hXn` and `hsup` by `hsmall_of_H4`
   (the audit's item 2; this is where the constants `Cg`, `C₀` and the smallness
   `α(600 Cg C₀) ≤ 1` enter);
2. **the firing** `Work.FTS.FireFix.blowupAtTop_of_regPkg'`, which needs the four analytic inputs
   *at the exact shapes* recorded here (note the sign `ω = −physOmega` and the stream function
   `merPsi (pExp α) A B Φ C`, which is FireFix's `merPsi α A B Φ C`), giving
   `Work.FTS.Top.BlowupAt ⟨α, _⟩ C.T`;
3. **the rescale** to time `1`: `Work.FTS.Top.blowupAt_one_of_blowupAt`, node N0.

The Biot–Savart input is *not* a hypothesis: it is the proved
`Work.FTS.BSSwirl.biotSavartSwirl`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.FTS.Final.Small
import Submission.Work.FTS.BSSwirl.Main

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology NNReal
open MeasureTheory Set Filter

namespace Work.FTS.Final

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

variable {α Cg C₀ : ℝ} {g Φ : Fam} {A B : ℝ → ℝ} {C : Work.FTS.Physical.PhysClock}

/-- **The firing with the smallness derived from the `ℋ⁴`-bound.**

The four analytic inputs are the *exact* hypotheses of
`Work.FTS.FireFix.blowupAtTop_of_regPkg'` (a `RegPkg'` per strip, the clock normalisation, the
meridian equation, the Biot–Savart identification, the pressure and the two differentiability
clauses of the meridian pair); the smallness `hsmall` is *not* a hypothesis here — it is derived
from the uniform `ℋ⁴`-bound and the sup bound by `hsmall_of_H4`. -/
theorem blowupAt_of_dyn_data {α Cg C₀ : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3) (hCg : 0 ≤ Cg)
    (hC₀ : 0 < C₀) (hs : α * (600 * Cg * C₀) ≤ 1)
    {g Φ : Fam} {A B : ℝ → ℝ} {C : Work.FTS.Physical.PhysClock}
    (hXn : ∀ τ : ℝ, 0 ≤ τ → Xn (Work.FTS.Regularity.pExp α) (slice g τ)
      ≤ C₀ * (Work.FTS.Regularity.pExp α) ^ 2)
    (hsup : ∀ τ : ℝ, 0 ≤ τ → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |g z θ τ| ≤ Cg * Xn (Work.FTS.Regularity.pExp α) (slice g τ))
    (hAeq : ∀ τ : ℝ, 0 ≤ τ → C.A τ = 2 * A τ)
    (hreg : ∀ S : ℝ, 0 < S → RegPkg' α S A B g)
    (hmer : MeridianEqOn (Work.FTS.Physical.merProfile α A B g C)
      (Work.FTS.MeridianDyn.merPsi (Work.FTS.Regularity.pExp α) A B Φ C) C.T)
    (hid : ∀ t ∈ Set.Ioo (0 : ℝ) C.T, ∀ x ∈ Uax,
      Work.FTS.Physical.physVel
        (fun x s => - Work.FTS.Physical.physOmega α A B g C x s) x t
        = Work.Cyl.psiField
            (fun r z => Work.FTS.MeridianDyn.merPsi (Work.FTS.Regularity.pExp α)
              A B Φ C r z t) x)
    (hΨ : ∀ t ∈ Set.Ioo (0 : ℝ) C.T, ∀ r z : ℝ, 0 < r → z ≠ 0 →
      ContDiffAt ℝ 3 (fun p : ℝ × ℝ =>
        Work.FTS.MeridianDyn.merPsi (Work.FTS.Regularity.pExp α) A B Φ C p.1 p.2 t) (r, z))
    (hW : ∀ t ∈ Set.Ioo (0 : ℝ) C.T, ∀ r z : ℝ, 0 < r → z ≠ 0 →
      Work.Cyl.DiffAt2 (fun r z =>
        Work.FTS.Physical.merProfile α A B g C r z t) r z)
    (hpress : PressureReconstructionOn ⟨α, hα.le⟩) :
    Nonempty (Work.FTS.Top.BlowupAt (⟨α, hα.le⟩ : ℝ≥0) 1) := by
  have hsmall := hsmall_of_H4 hα hα13 hCg hC₀ hs hXn hsup
  refine ⟨Work.FTS.Top.blowupAt_one_of_blowupAt
    (Work.FTS.FireFix.blowupAtTop_of_regPkg' (α := ⟨α, hα.le⟩) (A := A) (B := B) (g := g)
      (C := C) (Φ := Φ) hreg hAeq hsmall Work.FTS.BSSwirl.biotSavartSwirl hpress hmer hid
      hΨ hW)⟩

end Work.FTS.Final
