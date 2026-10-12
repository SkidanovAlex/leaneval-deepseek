import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.CentredGap
import Submission.Work.FirstBoundQ4Free
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The kinetic lower bound (excited-particle gap) over the centred box

`CentredGap.centredGap` (corpus) already states the summed sector gap:
`cnPlus ℓ Φ ≤ 36·ℓ²·kinWord N ℓ Φ` for smooth `Φ` over the centred box
`abox N ℓ`.  This module restates it as the kinetic LOWER bound the
per-state energy assembly needs,

    kinWord N ℓ Φ ≥ (1/(36·ℓ²))·cnPlus ℓ Φ          (kinWord_gap_cnPlus)

and adds the absorption corollary used when combining with the potential
first bound `pot_first_bound_q4free` (whose `−μ·q2C0(a v)·cnPlus` term is
killed by the kinetic gap in the regime where the one-body error is below
the gap):

    μ·q2C0(a v)·cnPlus ℓ Φ ≤ kinWord N ℓ Φ            (kin_absorbs_onebody)
    whenever  μ·q2C0(a v) ≤ 1/(36·ℓ²)   and  a v ≥ 0, μ ≥ 0.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators

namespace Submission

open _root_.BoseGases
open _root_.BoseGases.CInfty0Box
set_option autoImplicit false

namespace BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- Kinetic lower bound from the summed sector gap:
`kinWord N ℓ Φ ≥ (1/(36·ℓ²))·cnPlus ℓ Φ`. -/
lemma kinWord_gap_cnPlus {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Φ : X N → ℝ}
    (hΦc : ContDiff ℝ ∞ Φ) :
    (1 / (36 * ℓ ^ 2)) * cnPlus ℓ Φ ≤ kinWord N ℓ Φ := by
  have hg := centredGap (N := N) (ℓ := ℓ) hℓ (Φ := Φ) hΦc   -- cnPlus ≤ 36·ℓ²·kinWord
  have hpos : 0 < (36 * ℓ ^ 2 : ℝ) := by positivity
  have hdiv : cnPlus ℓ Φ / (36 * ℓ ^ 2) ≤ kinWord N ℓ Φ :=
    (div_le_iff₀ hpos).mpr (by simpa [mul_comm] using hg)
  simpa [div_eq_mul_inv, mul_comm] using hdiv

/-- The one-body excited error is absorbed by the kinetic gap, in the regime
`μ·q2C0(a v) ≤ 1/(36·ℓ²)`: `μ·q2C0(a v)·cnPlus ℓ Φ ≤ kinWord N ℓ Φ`. -/
lemma kin_absorbs_onebody {N : ℕ} {ℓ μ : ℝ} (hℓ : 0 < ℓ) (hμ : 0 ≤ μ)
    {v : ℝ³ → ℝ} (hAv : 0 ≤ a v)
    (hgap : μ * q2C0 (a v) ≤ 1 / (36 * ℓ ^ 2)) {Φ : X N → ℝ}
    (hΦc : ContDiff ℝ ∞ Φ) :
    μ * q2C0 (a v) * cnPlus ℓ Φ ≤ kinWord N ℓ Φ := by
  have hg := kinWord_gap_cnPlus (N := N) (ℓ := ℓ) hℓ (Φ := Φ) hΦc
  have hq2nn : 0 ≤ μ * q2C0 (a v) := by
    dsimp [q2C0]
    have h : 0 ≤ q2C0 (a v) := by
      dsimp [q2C0]
      have h1 : 0 ≤ 8 * π * a v := by positivity
      exact mul_nonneg (mul_nonneg (sq_nonneg chiSup) (by norm_num : (0 : ℝ) ≤ 2)) h1
    exact mul_nonneg hμ h
  have hcn0 : 0 ≤ cnPlus ℓ Φ := cnPlus_nonneg
  calc
    μ * q2C0 (a v) * cnPlus ℓ Φ
        ≤ (1 / (36 * ℓ ^ 2)) * cnPlus ℓ Φ := by
            exact mul_le_mul_of_nonneg_right hgap hcn0
    _ ≤ kinWord N ℓ Φ := hg


/-- **The per-state first energy bound (kinetic + potential)**: for smooth
states over the centred box in the gap regime
`μ·q2C0(a v) ≤ 1/(36·ℓ²)`, the full sliding-box energy expectation satisfies

    kinWord N ℓ Φ + qLHSword(ℓ,μ,…) Φ ≥ q0RenVal − 5·qcrossC·(a v)·Xbig·J

(the kinetic gap absorbs the one-body `−μ·q2C0(a v)·cnPlus` error of
`pot_first_bound_q4free`). -/
lemma energy_first_bound {N : ℕ} {ℓ μ : ℝ} (hℓ : 0 < ℓ) (hμ : 0 ≤ μ)
    {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0)
    (hgap : μ * q2C0 (a v) ≤ 1 / (36 * ℓ ^ 2))
    {Φ : X N → ℝ} (hΦc : ContDiff ℝ ∞ Φ) :
    kinWord N ℓ Φ
        + qLHSword (N := N) ℓ μ (wPairC ℓ v) (wPairC ℓ (g0 v h)) Φ
      ≥ q0RenVal (N := N) (v := v) ℓ μ Φ
        - (5 * qcrossC) * (a v) * (((N : ℝ) ^ 2 / ℓ ^ 3) + μ ^ 2 * ℓ ^ 3) *
            (∫ x in abox N ℓ, (Φ x) ^ 2) := by
  have hAv : 0 ≤ a v := (av_bounds_weak hR hv_nonneg hvrad hv_supp h).1
  have hpot := pot_first_bound_q4free (N := N) (ℓ := ℓ) (μ := μ) hℓ hμ
    hv_nonneg hvrad hv_memL1 (R := R) hR hv_supp h hRℓ (Φ := Φ) hΦc.continuous
  have hkin := kin_absorbs_onebody (N := N) (ℓ := ℓ) (μ := μ) hℓ hμ hAv hgap (Φ := Φ) hΦc
  nlinarith




/-- **Per-scale gap-absorption against μ·(a v)·n₊** (the corpus per-sector
form of FS eq:appgapestimate: `𝒯_B ≥ C'μa·n₊` in the small-box regime):
whenever the kinetic gap constant dominates `Cgap·μ·(a v)` at scale `s`
(`Cgap·μ·(a v) ≤ 1/(36·s²)`), the kinetic energy absorbs the whole
excited-particle penalty:

    Cgap·μ·(a v)·cnPlus s Φ ≤ kinWord N s Φ .

This is the per-scale version of `kin_absorbs_onebody` with the
one-body-error constant replaced by the arbitrary (nonnegative) `Cgap`;
together with `Commons.Analysis.Real.gap_regime_sq_le` (the §4 regime
algebra `(dℓ)·C·√(μa) ≤ √ε_T ⟹ C²μa ≤ ε_T/(dℓ)²`) it replays the first step
of FS thm:smallbox's proof at any small-box scale `s`. -/
lemma kinWord_ge_mu_a_cnPlus {N : ℕ} {s μ : ℝ} (hs : 0 < s) (hμ : 0 ≤ μ)
    {v : ℝ³ → ℝ} (hAv : 0 ≤ a v) {Cgap : ℝ} (hCgap : 0 ≤ Cgap)
    (hreg : Cgap * μ * (a v) ≤ 1 / (36 * s ^ 2)) {Φ : X N → ℝ}
    (hΦc : ContDiff ℝ ∞ Φ) :
    Cgap * μ * (a v) * cnPlus s Φ ≤ kinWord N s Φ := by
  have hg := kinWord_gap_cnPlus (N := N) (ℓ := s) hs (Φ := Φ) hΦc
  have hnn : 0 ≤ Cgap * μ * (a v) := by
    exact mul_nonneg (mul_nonneg hCgap hμ) hAv
  have hcn0 : 0 ≤ cnPlus s Φ := cnPlus_nonneg
  calc
    Cgap * μ * (a v) * cnPlus s Φ
        ≤ (1 / (36 * s ^ 2)) * cnPlus s Φ := by
            exact mul_le_mul_of_nonneg_right hreg hcn0
    _ ≤ kinWord N s Φ := hg

end BoseGases

end Submission
