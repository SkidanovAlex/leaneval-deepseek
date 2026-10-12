import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Fourier.FourierTransform
import Submission.Work.SboxEB
import Submission.Work.SboxHomogeneity
import Submission.Work.SmallBoxA0.CorrSqrt
import Submission.Work.SmallBoxA0.kinPWord_smul
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `SmallBoxA0` — the `kinPWord` (FS `𝒯_B`) small-box energy and its data bundle

Why this module exists (SESSION-287, reviewer-directed).  The delivered block
bound `Submission.BoseGases.smallbox_block_bound` is stated for
`sboxE = kinWord + qLHSword` and carries the per-state Bogoliubov residual
`hBogF` — FS's `lm:appbogolubov` pairing payment on the *honest* position-space
kinetic `kinWord`.  §8 of the area README records that the corpus's PROVED D1
(`SmallBoxD1Final.lm_appbogolubov_pWord_holds`) cannot supply it, because D1's
word `kinPWord` is the χ-windowed mode sum and `kinPWord > kinWord` on
χ-core-supported states (`Work.SmallBoxA0.kinPWord_exceeds_kinWord`).

The fix is a MODEL choice: take the energy's kinetic word to be D1's word
`kinPWord` (FS's `Σ_i Q_iχ_i[√−Δ_i − c₀]₊²χ_iQ_i`, the spectral part of FS's
`𝒯_B` of eq:appTB).  Then D1 IS the Bogoliubov rung for the energy, and the
per-state assembly `Work.SmallBoxA0.state_block_bound_of_inputs_kinP` (already
proved) turns it into the block shape with **no residual hypothesis at all**.

This module defines the objects:

* `kinPEnergy n s μ w w1 c₀ Φ := kinPWord s c₀ Φ + qLHSword(N := n+1) s μ w w1 Φ`
  — the `kinPWord`-small-box energy (particle count `n+1`);
* `kinPeB n s μ v h c₀` — its `eB`-style infimum over `CSBox (n+1) s`;
* `d1C Ct := d1TargetC Ct chiR0 chiSup d1Ks` — D1's explicit constant;
* `kinPeta Ct R0 s c₀ v := (1 + d1C·(R0/s))·(1 + d1C·c₀·a v) − 1` — D1's loss
  factor `η`, determined by the data;
* `kinPBogErr Ct N s v := d1C·(a v)·((N+1)/s³)` — D1's `n₊`-coefficient;
* `kinPBracket Ct N s c₀ v` — D1's log/quartic/interior error bracket;
* `KinPBoxData` — the data bundle: the standing smallbox hypotheses, FS's
  `eq:appdellsassumption`-type regimes, and D1's own inputs.  **It carries no
  Bogoliubov residual field.**

The consumer-facing theorems live in
`Submission/Work/SmallBoxA0/KinPStateBound.lean` (per state) and
`Submission/Work/SmallBoxA0/KinPBlockBound.lean` (`eB`-level).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.SmallBoxA0

open Submission BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- **The `kinPWord`-small-box energy**: FS's small-box analysis energy with
D1's kinetic word instead of `kinWord`, TOGETHER WITH FS's `ε_T`-gap term
(`c_gap · Q_B`, i.e. `c_gap · n₊` — the `½ε_T(1+π⁻²)⁻¹(dℓ)⁻²Q_B` of eq:appTB,
whose corpus surrogate constant is `1/(36s²)`; the regime `1/(36s²) ≤ c_gap`
is the field `hcgap` below).  Particle count `n+1`. -/
noncomputable def kinPEnergy (n : ℕ) (s μ : ℝ) (w w1 : ℝ³ → ℝ³ → ℝ) (c₀ cgap : ℝ)
    (Φ : X (n + 1) → ℝ) : ℝ :=
  cgap * cnPlus s Φ + kinPWord s c₀ Φ + qLHSword (N := n + 1) s μ w w1 Φ

/-- **The `kinPWord`-small-box ground energy** (`eB`-style infimum). -/
noncomputable def kinPeB (n : ℕ) (s μ : ℝ) (v : ℝ³ → ℝ)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) (c₀ cgap : ℝ) : ℝ :=
  ⨅ Φ : CSBox (n + 1) s,
    kinPEnergy n s μ (wPairC s v) (wPairC s (g0 v h)) c₀ cgap (Φ : X (n + 1) → ℝ) /
      (∫ x in abox (n + 1) s, ((Φ : X (n + 1) → ℝ) x) ^ 2)

/-- **D1's explicit constant** (`SmallBoxD1Final.lm_appbogolubov_pWord_holds`'s
witness, exposed by `Work.SmallBoxA0.lm_appbogolubov_pWord_explicitC`). -/
noncomputable def d1C (Ct : ℝ) : ℝ := d1TargetC Ct chiR0 chiSup d1Ks

/-- **D1's loss factor**, as determined by the data:
`(1 + d1C·(R0/s))(1 + d1C·c₀·a v) = 1 + kinPeta`. -/
noncomputable def kinPeta (Ct R0 s c₀ : ℝ) (v : ℝ³ → ℝ) : ℝ :=
  (1 + d1C Ct * (R0 / s)) * (1 + d1C Ct * c₀ * (a v)) - 1

/-- **D1's `n₊`-coefficient** on a count-`N` state. -/
noncomputable def kinPBogErr (Ct : ℝ) (N : ℕ) (s : ℝ) (v : ℝ³ → ℝ) : ℝ :=
  d1C Ct * (a v) * (((N : ℝ) + 1) / s ^ 3)

/-- **D1's refined error bracket** (log + quartic + interior) on a count-`N`
state. -/
noncomputable def kinPBracket (Ct : ℝ) (N : ℕ) (s c₀ : ℝ) (v : ℝ³ → ℝ) : ℝ :=
  d1C Ct * ((a v) ^ 2 * c₀ * Real.log ((c₀ * (a v))⁻¹)
              * ((((N : ℝ) + 1) * ((N : ℝ) + 1)) / s ^ 3)
          + (a v) ^ 4 * (c₀ ^ 3)⁻¹ * ((((N : ℝ) + 1) / s ^ 3) ^ 3)
              * (((N : ℝ) + 1) / s ^ 3) * s ^ 3
          + (a v) * c₀ ^ 3 * (((N : ℝ) + 1) / s ^ 3) * s ^ 3)

/-- **The FS error shape** `Γ := (R0/s)² + K_B³(μ(av)³)^{1/2}`. -/
noncomputable def kinPGamma (R0 s K_B μ : ℝ) (v : ℝ³ → ℝ) : ℝ :=
  (R0 / s) ^ 2 + K_B ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ)

/-- **The data of the `kinPWord` block bound** (particle count `n+1`).  All the
Bogoliubov content is D1's: the fields are the standing smallbox hypotheses,
FS's regime assumptions (`eq:appdellsassumption`-type: `hbox`, `hη`,
`hbracket`, `hcorrreg`, `hchi`), and D1's own inputs (`hc0`, `hCt`, `hav`,
`hdil`, `hWfin`, `hNewton`).  There is NO Bogoliubov residual field. -/
structure KinPBoxData where
  n : ℕ
  s : ℝ
  μ : ℝ
  R0 : ℝ
  K_B : ℝ
  Ct : ℝ
  c₀ : ℝ
  /-- the `ε_T`-gap constant of the energy (FS eq:appTB's
  `½ε_T(1+π⁻²)⁻¹(dℓ)⁻²`); the regime `1/(36s²) ≤ cgap` is `hcgap`. -/
  cgap : ℝ
  v : ℝ³ → ℝ
  h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v
  hs : 0 < s
  hμ : 0 < μ
  hv_nonneg : 0 ≤ v
  hvrad : IsRadial v
  hv_memL1 : MemLp v 1
  hR0 : 0 < R0
  hv_supp : tsupport v ⊆ ball (0 : ℝ³) R0
  hRs : R0 ≤ s * chiR0
  hμs : 1 ≤ μ * s ^ 3
  hKB : 0 < K_B
  hCt : 0 ≤ Ct
  hc0 : 0 < c₀
  hav : 0 < a v
  /-- D1's dilute regime `2·c₀·(a v) ≤ 1`. -/
  hdil : 2 * c₀ * (a v) ≤ 1
  /-- D1's finiteness input (the Newtonian energy of `g₀ v h`). -/
  hWfin : MeasureTheory.Integrable (fun q : ℝ³ × ℝ³ =>
      wScaled s (g0 v h) q.1 * wScaled s (g0 v h) q.2 * (‖q.1 - q.2‖ : ℝ)⁻¹)
  /-- D1's sharp-mass (M1) input, with the Taylor constant `Ct`. -/
  hNewton : ((2 * Real.pi) ^ 3)⁻¹ * ∫ q : ℝ³,
      ((FourierTransform.fourier (fun x : ℝ³ => (wScaled s (g0 v h) x : ℂ))
          (((2 * Real.pi)⁻¹) • q)).re) ^ 2 / ‖q‖ ^ 2
    ≤ 2 * (1 + 6 * Ct * (R0 / s) ^ 2) * g0w0Mass (v := v) h
  /-- the block-count window (`C_n := 8`). -/
  hwin : (((n + 1 : ℕ) : ℝ)) / s ^ 3 ≤ 9 * μ
  /-- the `g₀`-mass bound (`SmallBoxA0.g0w0Mass_le_av`-shape). -/
  hD : g0w0Mass (v := v) h ≤ 8 * π * (a v)
  /-- **regime**: the total `n₊`-coefficient fits the `ε_T`-gap constant
  (`Work.SmallBoxA0.totNCoeff` + D1's `kinPBogErr ≤ cgap`). -/
  hbox : totNCoeff s μ v + kinPBogErr Ct n s v ≤ cgap
  /-- **regime**: D1's loss factor is dominated by `Γ`. -/
  hη : (1 / 2) * |kinPeta Ct R0 s c₀ v| * (8 * π * (a v))
        * (((((n + 1 : ℕ) : ℝ)) + 1) ^ 2) * (s ^ 3)⁻¹
      ≤ μ ^ 2 * (a v) * s ^ 3 * kinPGamma R0 s K_B μ v + μ * (a v)
  /-- **regime**: D1's error bracket fits the `(av)μ` budget. -/
  hbracket : kinPBracket Ct n s c₀ v ≤ (88 * π + 39) * (a v) * μ
  /-- **regime**: the AM–GM constant of the `Corr` residue fits `(av)μs⁴`. -/
  hcorrreg : 4 * ((32 * π * chiSup ^ 2 * ((((n + 1 : ℕ) : ℝ)) + 1)) * (a v)) ^ 2
      * (((n + 1 : ℕ) : ℝ)) ≤ π * (a v) * μ * s ^ 4
  /-- **regime**: the `ε_T`-gap constant dominates the box kinetic gap
  (`eq:appdellsassumption`-type: the box side is below the healing length). -/
  hcgap : 1 / (36 * s ^ 2) ≤ cgap
  /-- **regime**: the `χ`-version of the healing-length condition (used by the
  fully-excited `cS1 = 0` branch, `SmallBoxA0.qLHSword_zero_case`). -/
  hchi : (μ * (a v) * s ^ 2) * (1600 + 1850 * chiSup ^ 2) ≤ 1

/-- **Quadratic homogeneity of the `kinPWord`-energy**: `kinPEnergy(c•Φ) =
c²·kinPEnergy(Φ)`.  This is the hinge that lets the `kinPeB`-infimum over all
`CSBox` states collapse to the normalised one. -/
lemma kinPEnergy_smul {n : ℕ} {s μ : ℝ} (w w1 : ℝ³ → ℝ³ → ℝ) {c₀ cgap : ℝ}
    {Φ : X (n + 1) → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (c : ℝ) :
    kinPEnergy n s μ w w1 c₀ cgap (c • Φ)
      = (c ^ 2) * kinPEnergy n s μ w w1 c₀ cgap Φ := by
  unfold kinPEnergy
  rw [cnPlus_smul, kinPWord_smul, qLHSword_smul]
  ring

/-- **The data of the `kinPWord` block bound at a FIXED state**: the
`KinPBoxData` fields together with a smooth normalised `(n+1)`-particle state.
Like `KinPBoxData`, it carries **no Bogoliubov residual field**. -/
structure KinPStateData extends KinPBoxData where
  Φ : X (toKinPBoxData.n + 1) → ℝ
  hΦc : ContDiff ℝ ∞ Φ
  hnorm : (∫ x in abox (toKinPBoxData.n + 1) toKinPBoxData.s, (Φ x) ^ 2) = 1

end Work.SmallBoxA0
