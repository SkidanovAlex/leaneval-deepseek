import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.latDeficit_eq_regions_closed
import Submission.Work.BoseBoxFock.nu_tauTheta_eq_truncated
import Submission.Work.BoseBoxFock.tauPhiRowWindowHinge
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.windowedDeficitResidual_of_band` — the band/low-gain coupling form of the
windowed deficit residual

The node `Work.BoseBoxFock.windowedDeficitResidual` (`tauPhiRowWindowHinge.lean`) is the `hdef`
hypothesis of the proved `Work.BoseBoxFock.tauPhi_row_lattice_of_deficit`, and by the proved ledger
identity `ledger_eq_deficitForm_closed` it is *equivalent* to the canonical aliasing form

    (★)   2c·(R₁ − S₁) ≤ latDeficit ℓ c g + lowGain ℓ c g ,   R_j = tauContPow j g, S_j = tauLatPow ℓ j g .

This file formalises the decomposition of (★) into **two explicit payers** (ADDENDA 4–9 of
`FINDING_tauPhiRowWindowHinge.md`):

* `bandPayer ℓ c g = Σ_n ℓ⁻³·1_{c < ‖k_n‖ < 2c}·δ_c(‖k_n‖)·ν_n` — the *transition-band* profile
  deficit: region 1 of `latDeficit_eq_regions_closed` with `δ_c` written as `deficit c` (they
  agree on the band, `bandPayer_eq_region1`);
* `region2 ℓ c g = Σ_n ℓ⁻³·1_{‖k_n‖ ≥ 2c}·(c‖k_n‖ − (5/4+c₀)c²)·ν_n` — the quadratic tail of
  `latDeficit`, proved **nonnegative** here (`region2_nonneg`);
* `lowMlat/lowSlat1/lowSlat2` and `lowMcont/lowScont1/lowScont2` — the (truncated, `‖k_n‖ ≤ c`)
  lattice moments and their continuum counterparts, with
  `lowGain ℓ c g = c²(M_lat − M^c) − 2c(S₁^lat − R₁^c) + (S₂^lat − R₂^c)`
  (proved: `lowGain_eq_lowGain_split`, via the support-free `nuTauTheta_smooth`).

The **single** remaining inequality is

    `BandPlusLowGainGeHighDemand ℓ c g` :   `highDemand ℓ c g ≤ bandPlusLowGain ℓ c g` ,

    `bandPlusLowGain = bandPayer + c²·(M_lat − M^c) + (S₂^lat − R₂^c)` ,
    `highDemand      = 2c·[(R₁ − R₁^c) − (S₁ − S₁^lat)]` .

The result of this file is the reduction

    `BandPlusLowGainGeHighDemand ℓ c g`  ⟹  `windowedDeficitResidual ℓ c g`  ⟹
        (proved `tauPhi_row_lattice_of_deficit`)  ⟹  the closed-ball `tauPhi` row.

All inputs except the coupling inequality are proved: the region split
`latDeficit_eq_regions_closed`, the truncation identity in its support-free form
(`nuTauTheta_smooth`), the ledger identity `ledger_eq_deficitForm_closed`, and the nonnegativity of
the tail (`region2_nonneg`).  Note `tauPhi_row_lattice_of_deficit` needs no `cℓ ≥ 4π`; the only use
of `hcℓ` is that the coupling inequality is stated with it.

**Provenance and honest scope.**  `BandPlusLowGainGeHighDemand` is the statement of the node
`Submission/Work/BoseBoxFock/bandPlusLowGain_ge_highDemand.lean`
(`Work.BoseBoxFock.bandPlusLowGain_ge_highDemand`); this file is the formal assembly of that route.
The coupling inequality is *strictly stronger* than (★) — it drops the nonnegative tail `region2`
— so the reduction here is *one sufficient* route to the windowed residual, not a reformulation of
it.

⚠ **THE COUPLING INEQUALITY IS FALSE** (its holder declared it so, and the refutation was
reproduced here — see the `Prop`'s docstring and
`FINDING_windowedDeficitResidual_of_band.md` §4bis/§5).  So the assembly below is *vacuous as a
route to the row*; it is kept as the exact record of the reduction, and the equivalences it proves
(`bandPlusLowGain_sub_highDemand`, `bandPlusLowGainGeHighDemand_iff`,
`bandPlusLowGainGeHighDemand_iff_sharpAlias`) **transfer the refutation** to the sharp-alias form
`Alias(F_c) ≤ bandPayer` (see `Submission/Work/BoseBoxFock/fsKin_alias_equiv.lean`).  The node
`Work.BoseBoxFock.kinRow_lattice_tauPhi` does **not** use any of this: its crux rests on
`Work.BoseBoxFock.sharpShiftRow`.
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 0. Small bookkeeping lemmas -/

/-- `HasCompactSupport g` from a containment of the topological support in a closed ball (the class
of every node of this chapter). -/
private lemma hasCompactSupport_of_tsupport_subset_closedBall {ℓ : ℝ}
    {g : E3 → ℂ} (hgsupp : tsupport g ⊆ Metric.closedBall 0 (ℓ / 2)) :
    HasCompactSupport g :=
  (isCompact_closedBall (0 : E3) (ℓ / 2)).of_isClosed_subset (isClosed_tsupport g) hgsupp

/-- The `if`-form of a set integral is the set integral (for the measurable set `{‖p‖ ≤ c}`). -/
lemma integral_ite_eq_setIntegral {c : ℝ} {F : E3 → ℝ} :
    (∫ p : E3, (if ‖p‖ ≤ c then F p else 0))
      = ∫ p in {p : E3 | ‖p‖ ≤ c}, F p := by
  rw [← integral_indicator
    (measurableSet_le continuous_norm.measurable measurable_const) (f := F)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  simp only [Set.indicator_apply, Set.mem_setOf_eq]

/-! ## 1. The support-free truncation identity for the cap -/

/-- `Work.BoseBoxFock.nu_tauTheta_eq_truncated` without the support hypothesis on `g` (which its
proof never uses: the only summability input is `summable_trunc_weight`, a `ContDiff`+compact
support lemma).  Same proof, `hgsupp` deleted. -/
theorem nuTauTheta_smooth {ℓ c : ℝ} (hℓ : 0 < ℓ) (hc : 0 < c)
    {g : E3 → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g) (hgc : HasCompactSupport g) :
    (∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ * tauTheta c ‖kmomInt ℓ n‖
        * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2)
      - ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3,
          tauTheta c ‖p‖ * ‖Submission.BoseGases.kinFT g p‖ ^ 2
    = c ^ 2 * ((∑' n : Fin 3 → ℤ, if ‖kmomInt ℓ n‖ ≤ c then
                  (ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2
                else 0)
              - ((2 * Real.pi) ^ 3)⁻¹ * ∫ p in {p : E3 | ‖p‖ ≤ c},
                  ‖Submission.BoseGases.kinFT g p‖ ^ 2)
      - 2 * c * ((∑' n : Fin 3 → ℤ, if ‖kmomInt ℓ n‖ ≤ c then
                  (ℓ ^ 3)⁻¹ * ‖kmomInt ℓ n‖
                    * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2
                else 0)
              - ((2 * Real.pi) ^ 3)⁻¹ * ∫ p in {p : E3 | ‖p‖ ≤ c},
                  ‖p‖ * ‖Submission.BoseGases.kinFT g p‖ ^ 2)
      + ((∑' n : Fin 3 → ℤ, if ‖kmomInt ℓ n‖ ≤ c then
                  (ℓ ^ 3)⁻¹ * ‖kmomInt ℓ n‖ ^ 2
                    * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2
                else 0)
              - ((2 * Real.pi) ^ 3)⁻¹ * ∫ p in {p : E3 | ‖p‖ ≤ c},
                  ‖p‖ ^ 2 * ‖Submission.BoseGases.kinFT g p‖ ^ 2) := by
  have hA : Summable (fun n : Fin 3 → ℤ => if ‖kmomInt ℓ n‖ ≤ c then
      (ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2 else 0) := by
    simpa using summable_trunc_weight (ℓ := ℓ) (c := c) hℓ hg hgc 0
  have hB : Summable (fun n : Fin 3 → ℤ => if ‖kmomInt ℓ n‖ ≤ c then
      (ℓ ^ 3)⁻¹ * ‖kmomInt ℓ n‖ * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2
      else 0) := by
    simpa using summable_trunc_weight (ℓ := ℓ) (c := c) hℓ hg hgc 1
  have hC : Summable (fun n : Fin 3 → ℤ => if ‖kmomInt ℓ n‖ ≤ c then
      (ℓ ^ 3)⁻¹ * ‖kmomInt ℓ n‖ ^ 2 * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2
      else 0) := by
    simpa using summable_trunc_weight (ℓ := ℓ) (c := c) hℓ hg hgc 2
  have hsum : (∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ * tauTheta c ‖kmomInt ℓ n‖
        * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2)
      = c ^ 2 * (∑' n : Fin 3 → ℤ, if ‖kmomInt ℓ n‖ ≤ c then
                  (ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2
                else 0)
        - 2 * c * (∑' n : Fin 3 → ℤ, if ‖kmomInt ℓ n‖ ≤ c then
                  (ℓ ^ 3)⁻¹ * ‖kmomInt ℓ n‖
                    * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2
                else 0)
        + (∑' n : Fin 3 → ℤ, if ‖kmomInt ℓ n‖ ≤ c then
                  (ℓ ^ 3)⁻¹ * ‖kmomInt ℓ n‖ ^ 2
                    * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2
                else 0) := by
    have hcongr : (∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ * tauTheta c ‖kmomInt ℓ n‖
          * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2)
        = ∑' n : Fin 3 → ℤ,
            (c ^ 2 * (if ‖kmomInt ℓ n‖ ≤ c then
                  (ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2
                else 0)
              - 2 * c * (if ‖kmomInt ℓ n‖ ≤ c then
                  (ℓ ^ 3)⁻¹ * ‖kmomInt ℓ n‖
                    * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2
                else 0)
              + (if ‖kmomInt ℓ n‖ ≤ c then
                  (ℓ ^ 3)⁻¹ * ‖kmomInt ℓ n‖ ^ 2
                    * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2
                else 0)) :=
      tsum_congr (fun n : Fin 3 → ℤ => tauTheta_mul_ite ℓ c ‖kmomInt ℓ n‖
        (‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2))
    rw [hcongr]
    exact tsum_quad_split hA hB hC
  have hI : (∫ p : E3,
        tauTheta c ‖p‖ * ‖Submission.BoseGases.kinFT g p‖ ^ 2)
      = c ^ 2 * (∫ p in {p : E3 | ‖p‖ ≤ c},
                  ‖Submission.BoseGases.kinFT g p‖ ^ 2)
        - 2 * c * (∫ p in {p : E3 | ‖p‖ ≤ c},
                  ‖p‖ * ‖Submission.BoseGases.kinFT g p‖ ^ 2)
        + (∫ p in {p : E3 | ‖p‖ ≤ c},
                  ‖p‖ ^ 2 * ‖Submission.BoseGases.kinFT g p‖ ^ 2) :=
    integral_cap_split
      (G := fun p : E3 => ‖Submission.BoseGases.kinFT g p‖ ^ 2)
      (SqrtKin.kinFT_sq_integrable hg hgc)
      (SqrtKin.kinFT_weight_integrable hg hgc)
      (SqrtKin.kinFT_weight2_integrable hg hgc)
  rw [hsum, hI]
  ring

/-! ## 2. The named atoms of the reduction -/

/-- The **transition-band payer**: the region-1 sum of `latDeficit_eq_regions_closed` with the
profile deficit written as `deficit c`. -/
def bandPayer (ℓ c : ℝ) (g : E3 → ℂ) : ℝ :=
  ∑' n : Fin 3 → ℤ, (if c < ‖kmomInt ℓ n‖ ∧ ‖kmomInt ℓ n‖ < 2 * c then
      (ℓ ^ 3)⁻¹ * deficit c ‖kmomInt ℓ n‖
        * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2
    else (0 : ℝ))

/-- Region 1 of `latDeficit_eq_regions_closed` (the same sum with the explicit profile). -/
def region1 (ℓ c : ℝ) (g : E3 → ℂ) : ℝ :=
  ∑' n : Fin 3 → ℤ, (if c < ‖kmomInt ℓ n‖ ∧ ‖kmomInt ℓ n‖ < 2 * c then
      (ℓ ^ 3)⁻¹ * ((‖kmomInt ℓ n‖ - c) ^ 2 - c ^ 2 * tauPhi (‖kmomInt ℓ n‖ / c))
        * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2
    else (0 : ℝ))

/-- Region 2 of `latDeficit_eq_regions_closed`: the quadratic tail of the profile deficit. -/
def region2 (ℓ c : ℝ) (g : E3 → ℂ) : ℝ :=
  ∑' n : Fin 3 → ℤ, (if 2 * c ≤ ‖kmomInt ℓ n‖ then
      (ℓ ^ 3)⁻¹ * (c * ‖kmomInt ℓ n‖ - (5 / 4 + tauC0phi) * c ^ 2)
        * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2
    else (0 : ℝ))

/-- The truncated lattice mass `M_lat^{≤c}`. -/
def lowMlat (ℓ c : ℝ) (g : E3 → ℂ) : ℝ :=
  ∑' n : Fin 3 → ℤ, (if ‖kmomInt ℓ n‖ ≤ c then
      (ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2 else (0 : ℝ))

/-- The truncated continuum mass `M^{≤c}`, in `if` form. -/
def lowMcont (c : ℝ) (g : E3 → ℂ) : ℝ :=
  ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3,
    (if ‖p‖ ≤ c then ‖Submission.BoseGases.kinFT g p‖ ^ 2 else (0 : ℝ))

/-- The truncated continuum mass `M^{≤c}`, in set-integral form. -/
def lowMset (c : ℝ) (g : E3 → ℂ) : ℝ :=
  ((2 * Real.pi) ^ 3)⁻¹ * ∫ p in {p : E3 | ‖p‖ ≤ c},
    ‖Submission.BoseGases.kinFT g p‖ ^ 2

/-- The truncated lattice first moment `S₁^{lat,≤c}`. -/
def lowSlat1 (ℓ c : ℝ) (g : E3 → ℂ) : ℝ :=
  ∑' n : Fin 3 → ℤ, (if ‖kmomInt ℓ n‖ ≤ c then
      (ℓ ^ 3)⁻¹ * ‖kmomInt ℓ n‖ * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2
    else (0 : ℝ))

/-- The truncated continuum first moment `R₁^{≤c}`, in `if` form. -/
def lowScont1 (c : ℝ) (g : E3 → ℂ) : ℝ :=
  ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3,
    (if ‖p‖ ≤ c then ‖p‖ * ‖Submission.BoseGases.kinFT g p‖ ^ 2 else (0 : ℝ))

/-- The truncated continuum first moment `R₁^{≤c}`, in set-integral form. -/
def lowSset1 (c : ℝ) (g : E3 → ℂ) : ℝ :=
  ((2 * Real.pi) ^ 3)⁻¹ * ∫ p in {p : E3 | ‖p‖ ≤ c},
    ‖p‖ * ‖Submission.BoseGases.kinFT g p‖ ^ 2

/-- The truncated lattice second moment `S₂^{lat,≤c}`. -/
def lowSlat2 (ℓ c : ℝ) (g : E3 → ℂ) : ℝ :=
  ∑' n : Fin 3 → ℤ, (if ‖kmomInt ℓ n‖ ≤ c then
      (ℓ ^ 3)⁻¹ * ‖kmomInt ℓ n‖ ^ 2 * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2
    else (0 : ℝ))

/-- The truncated continuum second moment `R₂^{≤c}`, in `if` form. -/
def lowScont2 (c : ℝ) (g : E3 → ℂ) : ℝ :=
  ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3,
    (if ‖p‖ ≤ c then ‖p‖ ^ 2 * ‖Submission.BoseGases.kinFT g p‖ ^ 2 else (0 : ℝ))

/-- The truncated continuum second moment `R₂^{≤c}`, in set-integral form. -/
def lowSset2 (c : ℝ) (g : E3 → ℂ) : ℝ :=
  ((2 * Real.pi) ^ 3)⁻¹ * ∫ p in {p : E3 | ‖p‖ ≤ c},
    ‖p‖ ^ 2 * ‖Submission.BoseGases.kinFT g p‖ ^ 2

/-- The continuum mass `R₀ = (2π)⁻³∫ν`. -/
def kinZero (g : E3 → ℂ) : ℝ :=
  ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3, ‖Submission.BoseGases.kinFT g p‖ ^ 2

/-- The continuum first moment `R₁ = (2π)⁻³∫‖p‖ν`. -/
def kinFirstInt (g : E3 → ℂ) : ℝ :=
  ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3, ‖p‖ * ‖Submission.BoseGases.kinFT g p‖ ^ 2

/-- The lattice first moment `S₁ = Σ_n ℓ⁻³‖k_n‖ν_n`. -/
def latFirst (ℓ : ℝ) (g : E3 → ℂ) : ℝ :=
  ∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ * ‖kmomInt ℓ n‖
    * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2

/-- `L(Θ_c)`: the lattice form of the cap. -/
def latTheta (ℓ c : ℝ) (g : E3 → ℂ) : ℝ :=
  ∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ * tauTheta c ‖kmomInt ℓ n‖
    * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2

/-- `C(Θ_c)`: the continuum form of the cap. -/
def contTheta (c : ℝ) (g : E3 → ℂ) : ℝ :=
  ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3,
    tauTheta c ‖p‖ * ‖Submission.BoseGases.kinFT g p‖ ^ 2

/-- `Σ_n ℓ⁻³Ψ_c(‖k_n‖)ν_n`: the lattice content of the convexity defect `Ψ_c = ρ_c − τ̃_c`. -/
def psiSum (ℓ c : ℝ) (g : E3 → ℂ) : ℝ :=
  ∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ * tauPsi c ‖kmomInt ℓ n‖
    * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2

/-- The **high demand**: `2c·[(R₁ − R₁^≤c) − (S₁ − S₁^lat,≤c)]`. -/
def highDemand (ℓ c : ℝ) (g : E3 → ℂ) : ℝ :=
  2 * c * (tauContPow 1 g - lowScont1 c g - tauLatPow ℓ 1 g + lowSlat1 ℓ c g)

/-- The **band + nonlinear-low-gain payer**: `W + c²(M_lat^{≤c} − M^≤c) + (S₂^lat,≤c − R₂^≤c)`. -/
def bandPlusLowGain (ℓ c : ℝ) (g : E3 → ℂ) : ℝ :=
  bandPayer ℓ c g + c ^ 2 * (lowMlat ℓ c g - lowMcont c g)
    + (lowSlat2 ℓ c g - lowScont2 c g)

/-- **The coupling inequality** (the statement of `Work.BoseBoxFock.bandPlusLowGain_ge_highDemand`):
the band payer plus the nonlinear low gain dominates the high demand.

⚠ **REFUTED — this `Prop` is FALSE.**  Its holder
(`Submission/Work/BoseBoxFock/bandPlusLowGain_ge_highDemand.lean`) declared it false, and the
refutation was reproduced here (`FINDING_windowedDeficitResidual_of_band.md` §4bis/§5) on the
two-blob family `g(x) = env(‖x − a e₁‖) + env(‖x + a e₁‖)`, `env(r) = exp(−1/(1−(r/R)²))1_{r<R}`,
`ℓ = 1`, `c = 4π`, `R = 0.05`, `a = 0.45`: there `bandPlusLowGain − highDemand = W − Alias(F_c) < 0`
(`W ≈ 8.5·10⁻⁵`, `Alias(F_c) = L(F_c) − C(F_c) ≈ 2·10⁻³`; the holder's higher-resolution run gives
`≈ 2.3·10⁻⁴`, validated by the frame identity `L(1) = C(1)` to `4·10⁻¹²`).

The theorems of this file remain **true** (they are `⟸`/`⟺`-statements whose left-hand side is this
`Prop`); the *consequence* is that the sharp-alias inequality `Alias(F_c) ≤ bandPayer` is
**also false** (`Submission/Work/BoseBoxFock/fsKin_alias_equiv.lean`,
`bandPlusLowGainGeHighDemand_iff_sharpAlias'`): the band deficit does **not** repair the sharp
symbol's aliasing.  Do not build on this `Prop`, and do not re-file this route. -/
def BandPlusLowGainGeHighDemand (ℓ c : ℝ) (g : E3 → ℂ) : Prop :=
  highDemand ℓ c g ≤ bandPlusLowGain ℓ c g

/-! ## 3. Elementary facts about the atoms -/

/-- The region split of `latDeficit` (immediate from `latDeficit_eq_regions_closed`). -/
lemma latDeficit_eq_region1_add_region2 {ℓ c : ℝ} (hℓ : 0 < ℓ) (hc : 0 < c)
    {g : E3 → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g) (hgc : HasCompactSupport g) :
    latDeficit ℓ c g = region1 ℓ c g + region2 ℓ c g :=
  latDeficit_eq_regions_closed hℓ hc hg hgc

/-- On the band `c < r < 2c` the profile deficit is the explicit `(r−c)² − c²τ(r/c)`, so
`bandPayer = region1`. -/
lemma bandPayer_eq_region1 {ℓ c : ℝ} (hc : 0 < c) (g : E3 → ℂ) :
    bandPayer ℓ c g = region1 ℓ c g := by
  rw [bandPayer, region1]
  refine tsum_congr (fun n => ?_)
  by_cases h : c < ‖kmomInt ℓ n‖ ∧ ‖kmomInt ℓ n‖ < 2 * c
  · rw [if_pos h, if_pos h, deficit, max_eq_left (by linarith [h.1])]
  · rw [if_neg h, if_neg h]

/-- **Region 2 is nonnegative**: on `{‖k_n‖ ≥ 2c}` the weight is
`c‖k_n‖ − (5/4+c₀)c² ≥ (3/4 − c₀)c² ≥ 0` (`c₀ = tauC0phi ≤ 1/16`). -/
lemma region2_nonneg {ℓ c : ℝ} (hℓ : 0 < ℓ) (hc : 0 < c) (g : E3 → ℂ) :
    0 ≤ region2 ℓ c g := by
  rw [region2]
  refine tsum_nonneg fun n => ?_
  by_cases h : 2 * c ≤ ‖kmomInt ℓ n‖
  · rw [if_pos h]
    have hc0 : tauC0phi ≤ 1 / 16 := tauC0phi_le
    have hb : 0 ≤ c * ‖kmomInt ℓ n‖ - (5 / 4 + tauC0phi) * c ^ 2 := by
      have h1 : (2 : ℝ) * c ^ 2 ≤ c * ‖kmomInt ℓ n‖ := by
        have := mul_le_mul_of_nonneg_left h hc.le
        nlinarith [this]
      have h2 : (5 / 4 + tauC0phi) * c ^ 2 ≤ 2 * c ^ 2 := by nlinarith [hc0, sq_nonneg c]
      linarith
    exact mul_nonneg (mul_nonneg (by positivity) hb) (sq_nonneg _)
  · rw [if_neg h]

/-- `lowMcont = lowMset` (the `if`-form of a set integral). -/
lemma lowMcont_eq_lowMset {c : ℝ} (g : E3 → ℂ) : lowMcont c g = lowMset c g := by
  rw [lowMcont, lowMset]
  congr 1
  exact integral_ite_eq_setIntegral

/-- `lowScont1 = lowSset1`. -/
lemma lowScont1_eq_lowSset1 {c : ℝ} (g : E3 → ℂ) : lowScont1 c g = lowSset1 c g := by
  rw [lowScont1, lowSset1]
  congr 1
  exact integral_ite_eq_setIntegral

/-- `lowScont2 = lowSset2`. -/
lemma lowScont2_eq_lowSset2 {c : ℝ} (g : E3 → ℂ) : lowScont2 c g = lowSset2 c g := by
  rw [lowScont2, lowSset2]
  congr 1
  exact integral_ite_eq_setIntegral

/-- `tauContPow 1 = kinFirstInt` (definitional up to `pow_one`). -/
lemma tauContPow_one_eq_kinFirstInt (g : E3 → ℂ) : tauContPow 1 g = kinFirstInt g := by
  simp only [tauContPow, kinFirstInt, pow_one]

/-- `tauLatPow ℓ 1 = latFirst` (definitional up to `pow_one`). -/
lemma tauLatPow_one_eq_latFirst (ℓ : ℝ) (g : E3 → ℂ) : tauLatPow ℓ 1 g = latFirst ℓ g := by
  simp only [tauLatPow, latFirst, pow_one]

/-- **`lowGain` in the cap language**: `lowGain ℓ c g = L(Θ_c) − C(Θ_c)`
(`thetaSym c r = tauTheta c r`). -/
lemma lowGain_eq_lowGain_split {ℓ c : ℝ} (g : E3 → ℂ) :
    lowGain ℓ c g = latTheta ℓ c g - contTheta c g := by
  rw [lowGain, latTheta, contTheta]
  congr 1
  · exact tsum_congr (fun n => by rw [thetaSym_eq_tauTheta])
  · congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    simp only [thetaSym_eq_tauTheta]

/-- **The low-gain decomposition**: with `M_lat, M, S₁^lat, R₁, S₂^lat, R₂` the truncated
(`‖k_n‖ ≤ c`) moments,
`L(Θ_c) − C(Θ_c) = c²(M_lat − M) − 2c(S₁^lat − R₁) + (S₂^lat − R₂)`. -/
lemma lowGain_split_atoms {ℓ c : ℝ} (hℓ : 0 < ℓ) (hc : 0 < c)
    {g : E3 → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g) (hgc : HasCompactSupport g) :
    latTheta ℓ c g - contTheta c g
      = c ^ 2 * (lowMlat ℓ c g - lowMset c g)
        - 2 * c * (lowSlat1 ℓ c g - lowSset1 c g)
        + (lowSlat2 ℓ c g - lowSset2 c g) :=
  nuTauTheta_smooth hℓ hc hg hgc

/-- **The coupling inequality in the corpus's own atoms.**  Its left-minus-right side is
*exactly*

    `bandPlusLowGain − highDemand = bandPayer + lowGain − 2c·(R₁ − S₁)` ,

`R₁ = tauContPow 1 g`, `S₁ = tauLatPow ℓ 1 g`.  Hence

    `BandPlusLowGainGeHighDemand ℓ c g  ⟺  lowGain ℓ c g ≥ 2c·(R₁ − S₁) − bandPayer ℓ c g`
    `                                  ⟺  L(Θ_c) − C(Θ_c) + W ≥ 2c·D` ,  `W = bandPayer`, `D = R₁ − S₁`,

which is the residual `2cD ≤ latDeficit + lowGain` with the nonnegative tail `region2` dropped.
This is the *only* structural content of the coupling inequality: it exhibits it as "the cap's
lattice gain plus the band deficit pays twice the first-moment deficit". -/
lemma bandPlusLowGain_sub_highDemand {ℓ c : ℝ} (hℓ : 0 < ℓ) (hc : 0 < c)
    {g : E3 → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g) (hgc : HasCompactSupport g) :
    bandPlusLowGain ℓ c g - highDemand ℓ c g
      = bandPayer ℓ c g + lowGain ℓ c g - 2 * c * (tauContPow 1 g - tauLatPow ℓ 1 g) := by
  have hlg1 := lowGain_eq_lowGain_split (ℓ := ℓ) (c := c) g
  have hlg2 := lowGain_split_atoms hℓ hc hg hgc
  have hM := lowMcont_eq_lowMset (c := c) g
  have hs1 := lowScont1_eq_lowSset1 (c := c) g
  have hs2 := lowScont2_eq_lowSset2 (c := c) g
  rw [hlg1, hlg2, ← hM, ← hs1, ← hs2, bandPlusLowGain, highDemand]
  ring

/-- **The coupling inequality, in the equivalent `lowGain` form**:

    `BandPlusLowGainGeHighDemand ℓ c g  ⟺  2c·(R₁ − S₁) − W ≤ lowGain ℓ c g` ,

i.e. `⟺ L(Θ_c) − C(Θ_c) + W ≥ 2c·(R₁ − S₁)`.  Compare the corpus's residual `(★)`
(`2cD ≤ latDeficit + lowGain`): the coupling inequality is the *same* right-hand side with the
nonnegative tail `region2` of `latDeficit` dropped, i.e. it is the residual strengthened by
`−region2`. -/
lemma bandPlusLowGainGeHighDemand_iff {ℓ c : ℝ} (hℓ : 0 < ℓ) (hc : 0 < c)
    {g : E3 → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g) (hgc : HasCompactSupport g) :
    BandPlusLowGainGeHighDemand ℓ c g
      ↔ 2 * c * (tauContPow 1 g - tauLatPow ℓ 1 g) - bandPayer ℓ c g ≤ lowGain ℓ c g := by
  rw [BandPlusLowGainGeHighDemand, ← sub_nonneg, bandPlusLowGain_sub_highDemand hℓ hc hg hgc]
  constructor <;> intro h <;> linarith

/-- **The coupling inequality in the *sharp-row* vocabulary**: the aliasing of the *sharp* symbol
`fsKinCoeff c ‖·‖ = (‖·‖−c)₊²` is paid by the transition-band deficit `bandPayer`.

This is the spelling that puts the coupling inequality in the same family as the corpus's
`sharpShiftRow` (`L((·−λ)₊²) ≤ C((·−c)₊²)`) and its `deficitAlias_*` machinery — only with the
*same* parameter `c` on both sides and the band deficit as the repair.  It is stated relative to
the **sharp-aliasing identity** (proved/assumed as `hfs`):

    `L(fsKinCoeff c ‖·‖) − C(fsKinCoeff c ‖·‖) = 2c·(R₁ − S₁) − lowGain ℓ c g` ,

which follows from `F_c = (r−c)² − Θ_c` plus the two **proved** moment identities
`tauLatPow ℓ 0 g = tauContPow 0 g`, `tauLatPow ℓ 2 g = tauContPow 2 g`
(`Work.BoseBoxFock.tauAssembly`).  Verified numerically (`ScratchKRmine/fskin_id.py`). -/
lemma bandPlusLowGainGeHighDemand_iff_sharpAlias {ℓ c : ℝ} (hℓ : 0 < ℓ) (hc : 0 < c)
    {g : E3 → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g) (hgc : HasCompactSupport g)
    (hfs : (∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ * Submission.BoseGases.fsKinCoeff c ‖kmomInt ℓ n‖
              * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2)
            - ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3, Submission.BoseGases.fsKinCoeff c ‖p‖
                * ‖Submission.BoseGases.kinFT g p‖ ^ 2
          = 2 * c * (tauContPow 1 g - tauLatPow ℓ 1 g) - lowGain ℓ c g) :
    BandPlusLowGainGeHighDemand ℓ c g
      ↔ (∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ * Submission.BoseGases.fsKinCoeff c ‖kmomInt ℓ n‖
              * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2)
          - ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3, Submission.BoseGases.fsKinCoeff c ‖p‖
              * ‖Submission.BoseGases.kinFT g p‖ ^ 2
        ≤ bandPayer ℓ c g := by
  rw [bandPlusLowGainGeHighDemand_iff hℓ hc hg hgc]
  constructor <;> intro h <;> linarith

/-! ## 4. The assembly -/

/-- **The coupling inequality implies the windowed deficit residual.** -/
theorem windowedDeficitResidual_of_bandPlusLowGain {ℓ c : ℝ} (hℓ : 0 < ℓ) (hc : 0 < c)
    (hcℓ : 4 * Real.pi ≤ c * ℓ) {g : E3 → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g)
    (hgsupp : tsupport g ⊆ Metric.closedBall 0 (ℓ / 2))
    (hband : BandPlusLowGainGeHighDemand ℓ c g) :
    windowedDeficitResidual ℓ c g := by
  have hgc : HasCompactSupport g := hasCompactSupport_of_tsupport_subset_closedBall hgsupp
  -- the three proved identities, in atom form
  have hreg : latDeficit ℓ c g = region1 ℓ c g + region2 ℓ c g :=
    latDeficit_eq_region1_add_region2 hℓ hc hg hgc
  have hnu : latTheta ℓ c g - contTheta c g
      = c ^ 2 * (lowMlat ℓ c g - lowMset c g)
        - 2 * c * (lowSlat1 ℓ c g - lowSset1 c g)
        + (lowSlat2 ℓ c g - lowSset2 c g) :=
    lowGain_split_atoms hℓ hc hg hgc
  have hled : latDeficit ℓ c g + lowGain ℓ c g - 2 * c * (tauContPow 1 g - tauLatPow ℓ 1 g)
      = c * (3 * tauLatPow ℓ 1 g - 2 * tauContPow 1 g) + psiSum ℓ c g - contTheta c g
        - (5 / 4 + tauC0phi) * c ^ 2 * kinZero g :=
    ledger_eq_deficitForm_closed hℓ hc hg hgc hgsupp
  have hlg : lowGain ℓ c g = latTheta ℓ c g - contTheta c g := lowGain_eq_lowGain_split g
  -- the bridges
  have hM : lowMset c g = lowMcont c g := (lowMcont_eq_lowMset g).symm
  have hs1 : lowSset1 c g = lowScont1 c g := (lowScont1_eq_lowSset1 g).symm
  have hs2 : lowSset2 c g = lowScont2 c g := (lowScont2_eq_lowSset2 g).symm
  have hR : tauContPow 1 g = kinFirstInt g := tauContPow_one_eq_kinFirstInt g
  have hS : tauLatPow ℓ 1 g = latFirst ℓ g := tauLatPow_one_eq_latFirst ℓ g
  -- the coupling hypothesis, with the payer and the demand expanded
  have hb : 0 ≤ bandPlusLowGain ℓ c g - highDemand ℓ c g := sub_nonneg.mpr hband
  have hbp : bandPlusLowGain ℓ c g
      = region1 ℓ c g + c ^ 2 * (lowMlat ℓ c g - lowMcont c g)
        + (lowSlat2 ℓ c g - lowScont2 c g) := by
    show bandPayer ℓ c g + c ^ 2 * (lowMlat ℓ c g - lowMcont c g)
        + (lowSlat2 ℓ c g - lowScont2 c g) = _
    rw [bandPayer_eq_region1 hc]
  have hhd : highDemand ℓ c g
      = 2 * c * (kinFirstInt g - lowScont1 c g - latFirst ℓ g + lowSlat1 ℓ c g) := by
    show 2 * c * (tauContPow 1 g - lowScont1 c g - tauLatPow ℓ 1 g + lowSlat1 ℓ c g) = _
    rw [hR, hS]
  rw [hbp, hhd] at hb
  -- the scalar heart
  have hgoal : 0 ≤ c * (3 * latFirst ℓ g - 2 * kinFirstInt g) + psiSum ℓ c g
      - contTheta c g - (5 / 4 + tauC0phi) * c ^ 2 * kinZero g := by
    rw [hreg, hlg, hnu, hM, hs1, hs2, hR, hS] at hled
    have hnn : 0 ≤ region2 ℓ c g := region2_nonneg hℓ hc g
    linarith [hled, hb, hnn]
  exact sub_nonneg.mp hgoal

/-- **The closed-ball `tauPhi` row from the coupling inequality**
(the `cℓ ≥ 4π` hypothesis is used only through the coupling inequality). -/
theorem tauPhiRow_of_bandPlusLowGain {ℓ c : ℝ} (hℓ : 0 < ℓ) (hc : 0 < c)
    (hcℓ : 4 * Real.pi ≤ c * ℓ) {g : E3 → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g)
    (hgsupp : tsupport g ⊆ Metric.closedBall 0 (ℓ / 2))
    (hband : BandPlusLowGainGeHighDemand ℓ c g) :
    (∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ *
        (c ^ 2 * tauPhi (‖kmomInt ℓ n‖ / c)) *
        ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2)
      ≤ ((2 * Real.pi) ^ 3)⁻¹ *
        (∫ p : E3, Submission.BoseGases.fsKinCoeff c ‖p‖ *
          ‖Submission.BoseGases.kinFT g p‖ ^ 2) :=
  tauPhi_row_lattice_of_deficit hℓ hc hg
    (hasCompactSupport_of_tsupport_subset_closedBall hgsupp) hgsupp
    (windowedDeficitResidual_of_bandPlusLowGain hℓ hc hcℓ hg hgsupp hband)

end Work.BoseBoxFock
