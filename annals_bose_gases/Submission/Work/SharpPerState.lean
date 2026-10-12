import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.FSGroupQ2
import Submission.Work.SmallBoxQ0
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# First count-universal per-state bound — the q4-free sharp chain

Clone of `FirstBoundQ4Free.pot_first_bound_q4free` (the skeleton:
`pot_q0_lower` splits `qLHS ≥ q0RenVal + q1+q2+q3+q4`, then per-word lower
bounds, net `q4word` coefficient `+1 − ¼ − ¼ = +½ ≥ 0` dropped via
`q4_nonneg`) with the coarse `qcrossC·Xbig` errors replaced by the sharp
`n₊`/`cS2`/`cS1`-linear mass forms:

    qLHSword(N,ℓ,μ,wPairC v,wPairC g0)Φ
      ≥ q0RenVal(N,v,ℓ,μ)Φ
        − C₂(ℓ³)⁻¹·(3·N̂·n₊ + cS2)          [q1_sharp_mass + q2_sharp_lower]
        − C₁(ℓ³)⁻¹·(7·cS2 + 18·N̂·n₊)      [q2_sharp_lower + q3_sharp_quarter]
        − μ·C₁·(cS1 + 2·n₊)

valid for ALL counts (no μ-window, no cnPlus-window).  Chosen branch,
`Continuous Φ`.
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

/-- **Per-state sharp potential bound** (count-universal, q4-free). -/
theorem pot_sharp_density {N : ℕ} {ℓ μ : ℝ} (hℓ : 0 < ℓ) (hμ : 0 ≤ μ)
    {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) {Φ : XN N → ℝ} (hΦc : Continuous Φ) :
    qLHSword (N := N) ℓ μ (wPairC ℓ v) (wPairC ℓ (g0 v h)) Φ ≥
      q0RenVal (N := N) (v := v) ℓ μ Φ
        - (fsqC2 (a v)) * (ℓ ^ 3)⁻¹ * (3 * ((N : ℝ) * cnPlus ℓ Φ) + cS2 ℓ Φ)
        - (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * (7 * cS2 ℓ Φ + 18 * ((N : ℝ) * cnPlus ℓ Φ))
        - μ * (fsqC1 (a v)) * (cS1 ℓ Φ + 2 * cnPlus ℓ Φ) := by
  classical
  have hpot := pot_q0_lower (N := N) (ℓ := ℓ) (μ := μ) hℓ hv_nonneg hvrad hv_memL1
    (R := R) hR hv_supp h hRℓ (Φ := Φ) hΦc
  have hq4nn : 0 ≤ q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ :=
    q4_nonneg (N := N) hℓ (wPairC_nonneg hv_nonneg ℓ)
  -- potsplit with the exact q4 word
  have hpot' : q0RenVal (N := N) (v := v) ℓ μ Φ
        + q1word (N := N) ℓ μ (wPairC ℓ (g0 v h)) (wPairC ℓ (g2 v h)) Φ
        + q2word (N := N) ℓ μ (wPairC ℓ (g0 v h)) (wPairC ℓ (g2 v h)) Φ
        + q3word (N := N) ℓ (wPairC ℓ (g0 v h)) Φ
        + q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ
      ≤ qLHSword (N := N) ℓ μ (wPairC ℓ v) (wPairC ℓ (g0 v h)) Φ := by
    simpa using hpot
  -- q1 ≥ −|q1| ≥ −[C₂(ℓ³)⁻¹(N̂n₊+cS2) + μC₁(cS1+n₊)]   (q1_sharp_mass)
  have h1lo : - ((fsqC2 (a v)) * (ℓ ^ 3)⁻¹ * (((N : ℝ) * cnPlus ℓ Φ) + cS2 ℓ Φ))
        - μ * (fsqC1 (a v)) * (cS1 ℓ Φ + cnPlus ℓ Φ)
        ≤ q1word (N := N) ℓ μ (wPairC ℓ (g0 v h)) (wPairC ℓ (g2 v h)) Φ := by
    have hb := q1_sharp_mass hℓ hμ hv_nonneg hvrad hR hv_supp h hRℓ hΦc
    have hb' : |q1word (N := N) ℓ μ (wPairC ℓ (g0 v h)) (wPairC ℓ (g2 v h)) Φ| ≤
        (fsqC2 (a v)) * (ℓ ^ 3)⁻¹ * (((N : ℝ) * cnPlus ℓ Φ) + cS2 ℓ Φ)
        + μ * (fsqC1 (a v)) * (cS1 ℓ Φ + cnPlus ℓ Φ) := hb
    have hneg := (abs_le.mp hb').1
    have hring : - ((fsqC2 (a v)) * (ℓ ^ 3)⁻¹ * (((N : ℝ) * cnPlus ℓ Φ) + cS2 ℓ Φ))
          - μ * (fsqC1 (a v)) * (cS1 ℓ Φ + cnPlus ℓ Φ)
        = - ((fsqC2 (a v)) * (ℓ ^ 3)⁻¹ * (((N : ℝ) * cnPlus ℓ Φ) + cS2 ℓ Φ)
            + μ * (fsqC1 (a v)) * (cS1 ℓ Φ + cnPlus ℓ Φ)) := by ring
    rwa [hring]
  -- q2 ≥ q2_sharp_lower
  have h2lo : - (fsqC2 (a v)) * (ℓ ^ 3)⁻¹ * (2 * ((N : ℝ) * cnPlus ℓ Φ))
        - (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * (4 * cS2 ℓ Φ + 3 * ((N : ℝ) * cnPlus ℓ Φ))
        - μ * (fsqC1 (a v)) * cnPlus ℓ Φ
        - (1 / 4) * q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ
        ≤ q2word (N := N) ℓ μ (wPairC ℓ (g0 v h)) (wPairC ℓ (g2 v h)) Φ := by
    exact q2_sharp_lower hℓ hμ hv_nonneg hvrad hv_memL1 hR hv_supp h hRℓ hΦc
  -- q3 ≥ −|q3| ≥ −[C₁(ℓ³)⁻¹(3cS2+15N̂n₊)] − ¼q4   (q3_sharp_quarter)
  have h3lo : - ((fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * (3 * cS2 ℓ Φ + 15 * ((N : ℝ) * cnPlus ℓ Φ)))
        - (1 / 4) * q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ
        ≤ q3word (N := N) ℓ (wPairC ℓ (g0 v h)) Φ := by
    have hb := q3_sharp_quarter hℓ hv_nonneg hvrad hv_memL1 hR hv_supp h hRℓ hΦc
    have hneg := (abs_le.mp hb).1
    have hring : - ((fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * (3 * cS2 ℓ Φ + 15 * ((N : ℝ) * cnPlus ℓ Φ)))
          - (1 / 4) * q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ
        = - ((fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * (3 * cS2 ℓ Φ + 15 * ((N : ℝ) * cnPlus ℓ Φ))
            + (1 / 4) * q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ) := by ring
    rwa [hring]
  -- assemble (q4-word coefficient +1 − ¼ − ¼ = +½ ≥ 0, dropped via hq4nn)
  nlinarith [hpot', h1lo, h2lo, h3lo, hq4nn]

/-- **Per-state small-box energy bound with the cS1-repulsion main term**
(kinWord dropped via `kinWord_nonneg`): for a NORMALISED state (`∫Φ² = 1`),

    E_s(Φ) := kinWord N ℓ Φ + qLHSword(N,ℓ,μ,wPairC v, wPairC g0) Φ
      ≥ (4πa/ℓ³)·(cS1 − μℓ³ − ½)² − 4πaμ²ℓ³·(1 + 1/(2μℓ³))²
        − C₂·(ℓ³)⁻¹·(3·N̂·n₊ + cS2) − C₁·(ℓ³)⁻¹·(7·cS2 + 18·N̂·n₊)
        − μ·C₁·(cS1 + 2·n₊)

valid for ALL counts (count-universal, no μ/cnPlus window). -/
theorem per_state_sharp {N : ℕ} {ℓ μ : ℝ} (hℓ : 0 < ℓ) (hμ : 0 < μ)
    {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) {Φ : XN N → ℝ} (hΦc : Continuous Φ)
    (hnorm : (∫ x in abox N ℓ, (Φ x) ^ 2) = 1) :
    (4 * π * (a v) / ℓ ^ 3) * (cS1 ℓ Φ - μ * ℓ ^ 3 - (1 / 2 : ℝ)) ^ 2
        - (4 * π * (a v)) * μ ^ 2 * ℓ ^ 3 * (1 + 1 / (2 * μ * ℓ ^ 3)) ^ 2
        - (fsqC2 (a v)) * (ℓ ^ 3)⁻¹ * (3 * ((N : ℝ) * cnPlus ℓ Φ) + cS2 ℓ Φ)
        - (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * (7 * cS2 ℓ Φ + 18 * ((N : ℝ) * cnPlus ℓ Φ))
        - μ * (fsqC1 (a v)) * (cS1 ℓ Φ + 2 * cnPlus ℓ Φ)
      ≤ kinWord N ℓ Φ + qLHSword (N := N) ℓ μ (wPairC ℓ v) (wPairC ℓ (g0 v h)) Φ := by
  have hpot := pot_sharp_density hℓ hμ.le hv_nonneg hvrad hv_memL1 hR hv_supp h hRℓ hΦc
  have hrep := q0RenVal_repulsion hR hv_nonneg hvrad hv_supp h hℓ hRℓ hμ hΦc hnorm
  have hknn : 0 ≤ kinWord N ℓ Φ := kinWord_nonneg N ℓ Φ
  nlinarith

/-- **u-form of `per_state_sharp`** (fixed count): substitute
`cS1 = N̂ − n₊` (`cS1_eq_nat_sub_cnPlus`) in the main square and split it via
`(1/2)X² − n₊² ≤ (X − n₊)²` (`X := N̂ − μℓ³ − ½`), giving the explicit
`n₊²`-remnant ready for the kinetic-gap absorption:

    E_s ≥ (4πa/ℓ³)·(1/2)·(N̂ − μℓ³ − ½)² − (4πa/ℓ³)·n₊²
          − 4πaμ²ℓ³(1+1/(2μℓ³))² − (mass + μ-one-body error blocks). -/
theorem per_state_sharp_u {N : ℕ} {ℓ μ : ℝ} (hℓ : 0 < ℓ) (hμ : 0 < μ)
    {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) {Φ : XN N → ℝ} (hΦc : Continuous Φ)
    (hnorm : (∫ x in abox N ℓ, (Φ x) ^ 2) = 1) :
    (4 * π * (a v) / ℓ ^ 3) * ((1 / 2 : ℝ) * ((N : ℝ) - μ * ℓ ^ 3 - (1 / 2 : ℝ)) ^ 2)
        - (4 * π * (a v) / ℓ ^ 3) * (cnPlus ℓ Φ) ^ 2
        - (4 * π * (a v)) * μ ^ 2 * ℓ ^ 3 * (1 + 1 / (2 * μ * ℓ ^ 3)) ^ 2
        - (fsqC2 (a v)) * (ℓ ^ 3)⁻¹ * (3 * ((N : ℝ) * cnPlus ℓ Φ) + cS2 ℓ Φ)
        - (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * (7 * cS2 ℓ Φ + 18 * ((N : ℝ) * cnPlus ℓ Φ))
        - μ * (fsqC1 (a v)) * (cS1 ℓ Φ + 2 * cnPlus ℓ Φ)
      ≤ kinWord N ℓ Φ + qLHSword (N := N) ℓ μ (wPairC ℓ v) (wPairC ℓ (g0 v h)) Φ := by
  have hE := per_state_sharp hℓ hμ hv_nonneg hvrad hv_memL1 hR hv_supp h hRℓ hΦc hnorm
  have hS := cS1_eq_nat_sub_cnPlus hℓ hΦc hnorm
  have hsq : (1 / 2 : ℝ) * ((N : ℝ) - μ * ℓ ^ 3 - (1 / 2 : ℝ)) ^ 2 - (cnPlus ℓ Φ) ^ 2
      ≤ (cS1 ℓ Φ - μ * ℓ ^ 3 - (1 / 2 : ℝ)) ^ 2 := by
    rw [hS]
    have hq : 0 ≤ ((((N : ℝ) - μ * ℓ ^ 3 - (1 / 2 : ℝ)) - 2 * cnPlus ℓ Φ) ^ 2) := sq_nonneg _
    nlinarith
  have hav : 0 ≤ a v := (av_bounds_weak hR hv_nonneg hvrad hv_supp h).1
  have hcoef : 0 ≤ 4 * π * (a v) / ℓ ^ 3 := div_nonneg (by positivity : 0 ≤ 4 * π * (a v))
    (pow_nonneg hℓ.le 3)
  have hmain : (4 * π * (a v) / ℓ ^ 3) *
        ((1 / 2 : ℝ) * ((N : ℝ) - μ * ℓ ^ 3 - (1 / 2 : ℝ)) ^ 2 - (cnPlus ℓ Φ) ^ 2)
      ≤ (4 * π * (a v) / ℓ ^ 3) * (cS1 ℓ Φ - μ * ℓ ^ 3 - (1 / 2 : ℝ)) ^ 2 :=
    mul_le_mul_of_nonneg_left hsq hcoef
  nlinarith

/-- **qLHS-only cS1-repulsion form** (no kinWord on the right, so the
kinetic-gap absorption can add `kinWord` on the left later): for NORMALISED Φ,

    qLHSword(N,ℓ,μ,wPairC v,wPairC g0)Φ
      ≥ (4πa/ℓ³)·(cS1 − μℓ³ − ½)² − 4πaμ²ℓ³(1+1/(2μℓ³))²
        − C₂·(ℓ³)⁻¹·(3·N̂·n₊ + cS2) − C₁·(ℓ³)⁻¹·(7·cS2 + 18·N̂·n₊)
        − μ·C₁·(cS1 + 2·n₊) . -/
theorem qLHS_sharp {N : ℕ} {ℓ μ : ℝ} (hℓ : 0 < ℓ) (hμ : 0 < μ)
    {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) {Φ : XN N → ℝ} (hΦc : Continuous Φ)
    (hnorm : (∫ x in abox N ℓ, (Φ x) ^ 2) = 1) :
    (4 * π * (a v) / ℓ ^ 3) * (cS1 ℓ Φ - μ * ℓ ^ 3 - (1 / 2 : ℝ)) ^ 2
        - (4 * π * (a v)) * μ ^ 2 * ℓ ^ 3 * (1 + 1 / (2 * μ * ℓ ^ 3)) ^ 2
        - (fsqC2 (a v)) * (ℓ ^ 3)⁻¹ * (3 * ((N : ℝ) * cnPlus ℓ Φ) + cS2 ℓ Φ)
        - (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * (7 * cS2 ℓ Φ + 18 * ((N : ℝ) * cnPlus ℓ Φ))
        - μ * (fsqC1 (a v)) * (cS1 ℓ Φ + 2 * cnPlus ℓ Φ)
      ≤ qLHSword (N := N) ℓ μ (wPairC ℓ v) (wPairC ℓ (g0 v h)) Φ := by
  have hpot := pot_sharp_density hℓ hμ.le hv_nonneg hvrad hv_memL1 hR hv_supp h hRℓ hΦc
  have hrep := q0RenVal_repulsion hR hv_nonneg hvrad hv_supp h hℓ hRℓ hμ hΦc hnorm
  nlinarith

/-- **qLHS-only u-form** (fixed count): substitute `cS1 = N̂ − n₊` and split
the square (`½X² − n₊² ≤ (X − n₊)²`), isolating the `n₊`-blocks on the
qLHS side so `kinWord` can absorb them. -/
theorem qLHS_sharp_u {N : ℕ} {ℓ μ : ℝ} (hℓ : 0 < ℓ) (hμ : 0 < μ)
    {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) {Φ : XN N → ℝ} (hΦc : Continuous Φ)
    (hnorm : (∫ x in abox N ℓ, (Φ x) ^ 2) = 1) :
    (4 * π * (a v) / ℓ ^ 3) * ((1 / 2 : ℝ) * ((N : ℝ) - μ * ℓ ^ 3 - (1 / 2 : ℝ)) ^ 2)
        - (4 * π * (a v) / ℓ ^ 3) * (cnPlus ℓ Φ) ^ 2
        - (4 * π * (a v)) * μ ^ 2 * ℓ ^ 3 * (1 + 1 / (2 * μ * ℓ ^ 3)) ^ 2
        - (fsqC2 (a v)) * (ℓ ^ 3)⁻¹ * (3 * ((N : ℝ) * cnPlus ℓ Φ) + cS2 ℓ Φ)
        - (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * (7 * cS2 ℓ Φ + 18 * ((N : ℝ) * cnPlus ℓ Φ))
        - μ * (fsqC1 (a v)) * (cS1 ℓ Φ + 2 * cnPlus ℓ Φ)
      ≤ qLHSword (N := N) ℓ μ (wPairC ℓ v) (wPairC ℓ (g0 v h)) Φ := by
  have hq := qLHS_sharp hℓ hμ hv_nonneg hvrad hv_memL1 hR hv_supp h hRℓ hΦc hnorm
  have hS := cS1_eq_nat_sub_cnPlus hℓ hΦc hnorm
  have hsq : (1 / 2 : ℝ) * ((N : ℝ) - μ * ℓ ^ 3 - (1 / 2 : ℝ)) ^ 2 - (cnPlus ℓ Φ) ^ 2
      ≤ (cS1 ℓ Φ - μ * ℓ ^ 3 - (1 / 2 : ℝ)) ^ 2 := by
    rw [hS]
    have hq' : 0 ≤ ((((N : ℝ) - μ * ℓ ^ 3 - (1 / 2 : ℝ)) - 2 * cnPlus ℓ Φ) ^ 2) := sq_nonneg _
    nlinarith
  have hav : 0 ≤ a v := (av_bounds_weak hR hv_nonneg hvrad hv_supp h).1
  have hcoef : 0 ≤ 4 * π * (a v) / ℓ ^ 3 := div_nonneg (by positivity : 0 ≤ 4 * π * (a v))
    (pow_nonneg hℓ.le 3)
  have hmain : (4 * π * (a v) / ℓ ^ 3) *
        ((1 / 2 : ℝ) * ((N : ℝ) - μ * ℓ ^ 3 - (1 / 2 : ℝ)) ^ 2 - (cnPlus ℓ Φ) ^ 2)
      ≤ (4 * π * (a v) / ℓ ^ 3) * (cS1 ℓ Φ - μ * ℓ ^ 3 - (1 / 2 : ℝ)) ^ 2 :=
    mul_le_mul_of_nonneg_left hsq hcoef
  nlinarith

set_option maxHeartbeats 1000000

/-- **Kinetic-gap absorption of the `n₊`-blocks** (from `qLHS_sharp_u`, so
`kinWord` is free to absorb): under `cnPlus ≤ B`, `N̂/ℓ³ ≤ U` and the sharp
gap regime `μ·C₁ + (4πa/ℓ³)·B + (3·C₂ + 18·C₁)·U ≤ 1/(36ℓ²)`,

    E_s ≥ (4πa/ℓ³)·½·(N̂−μℓ³−½)² − 4πaμ²ℓ³(1+1/(2μℓ³))²
          − (C₂+7·C₁)(ℓ³)⁻¹·cS2 − μ·C₁·N̂ . -/
theorem gap_absorb_sharp {N : ℕ} {ℓ μ : ℝ} (hℓ : 0 < ℓ) (hμ : 0 < μ)
    {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) {Φ : XN N → ℝ} (hΦc : ContDiff ℝ ∞ Φ)
    (hnorm : (∫ x in abox N ℓ, (Φ x) ^ 2) = 1)
    {B U : ℝ}
    (hwinP : cnPlus ℓ Φ ≤ B)
    (hucap : (N : ℝ) / ℓ ^ 3 ≤ U)
    (hreg : μ * (fsqC1 (a v)) + (4 * π * (a v) / ℓ ^ 3) * B
        + (3 * (fsqC2 (a v)) + 18 * (fsqC1 (a v))) * U ≤ 1 / (36 * ℓ ^ 2)) :
    (4 * π * (a v) / ℓ ^ 3) * ((1 / 2 : ℝ) * ((N : ℝ) - μ * ℓ ^ 3 - (1 / 2 : ℝ)) ^ 2)
        - (4 * π * (a v)) * μ ^ 2 * ℓ ^ 3 * (1 + 1 / (2 * μ * ℓ ^ 3)) ^ 2
        - ((fsqC2 (a v)) + 7 * (fsqC1 (a v))) * (ℓ ^ 3)⁻¹ * cS2 ℓ Φ
        - μ * (fsqC1 (a v)) * (N : ℝ)
      ≤ kinWord N ℓ Φ + qLHSword (N := N) ℓ μ (wPairC ℓ v) (wPairC ℓ (g0 v h)) Φ := by
  classical
  have hΦcc : Continuous Φ := hΦc.continuous
  have hq := qLHS_sharp_u hℓ hμ hv_nonneg hvrad hv_memL1 hR hv_supp h hRℓ hΦcc hnorm
  have hS := cS1_eq_nat_sub_cnPlus hℓ hΦcc hnorm
  have hmu : μ * (fsqC1 (a v)) * (cS1 ℓ Φ + 2 * cnPlus ℓ Φ)
      = μ * (fsqC1 (a v)) * ((N : ℝ) + cnPlus ℓ Φ) := by
    rw [hS]
    ring
  have hPnn : 0 ≤ cnPlus ℓ Φ := cnPlus_nonneg
  have hP2 : (cnPlus ℓ Φ) ^ 2 ≤ B * cnPlus ℓ Φ := by
    calc
      (cnPlus ℓ Φ) ^ 2 = cnPlus ℓ Φ * cnPlus ℓ Φ := by rw [pow_two]
      _ ≤ B * cnPlus ℓ Φ := mul_le_mul_of_nonneg_right hwinP hPnn
  have hNred : (ℓ ^ 3)⁻¹ * ((N : ℝ) * cnPlus ℓ Φ) ≤ U * cnPlus ℓ Φ := by
    have hq2 := mul_le_mul_of_nonneg_right hucap hPnn
    simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hq2
  have hav : 0 ≤ a v := (av_bounds_weak hR hv_nonneg hvrad hv_supp h).1
  have hC1nn : 0 ≤ fsqC1 (a v) := by dsimp [fsqC1]; positivity
  have hC2nn : 0 ≤ fsqC2 (a v) := by dsimp [fsqC2]; positivity
  have hcoef : 0 ≤ 4 * π * (a v) / ℓ ^ 3 := div_nonneg (by positivity : 0 ≤ 4 * π * (a v))
    (pow_nonneg hℓ.le 3)
  have hA1 : (4 * π * (a v) / ℓ ^ 3) * (cnPlus ℓ Φ) ^ 2
      ≤ (4 * π * (a v) / ℓ ^ 3) * (B * cnPlus ℓ Φ) :=
    mul_le_mul_of_nonneg_left hP2 hcoef
  have hA2a : (fsqC2 (a v)) * (ℓ ^ 3)⁻¹ * (3 * ((N : ℝ) * cnPlus ℓ Φ))
      ≤ 3 * (fsqC2 (a v)) * U * cnPlus ℓ Φ := by
    have hstep : (fsqC2 (a v)) * (ℓ ^ 3)⁻¹ * (3 * ((N : ℝ) * cnPlus ℓ Φ))
        = 3 * (fsqC2 (a v)) * ((ℓ ^ 3)⁻¹ * ((N : ℝ) * cnPlus ℓ Φ)) := by ring
    rw [hstep]
    simpa [mul_assoc] using (mul_le_mul_of_nonneg_left hNred
      (mul_nonneg (by norm_num : (0:ℝ) ≤ 3) hC2nn))
  have hA2b : (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * (18 * ((N : ℝ) * cnPlus ℓ Φ))
      ≤ 18 * (fsqC1 (a v)) * U * cnPlus ℓ Φ := by
    have hstep : (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * (18 * ((N : ℝ) * cnPlus ℓ Φ))
        = 18 * (fsqC1 (a v)) * ((ℓ ^ 3)⁻¹ * ((N : ℝ) * cnPlus ℓ Φ)) := by ring
    rw [hstep]
    simpa [mul_assoc] using (mul_le_mul_of_nonneg_left hNred
      (mul_nonneg (by norm_num : (0:ℝ) ≤ 18) hC1nn))
  have hlin : (4 * π * (a v) / ℓ ^ 3) * (B * cnPlus ℓ Φ)
        + 3 * (fsqC2 (a v)) * U * cnPlus ℓ Φ
        + 18 * (fsqC1 (a v)) * U * cnPlus ℓ Φ
        + μ * (fsqC1 (a v)) * cnPlus ℓ Φ
      ≤ (1 / (36 * ℓ ^ 2)) * cnPlus ℓ Φ := by
    have hregmul := mul_le_mul_of_nonneg_right hreg hPnn
    nlinarith
  have hAbs : (4 * π * (a v) / ℓ ^ 3) * (cnPlus ℓ Φ) ^ 2
        + (fsqC2 (a v)) * (ℓ ^ 3)⁻¹ * (3 * ((N : ℝ) * cnPlus ℓ Φ))
        + (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * (18 * ((N : ℝ) * cnPlus ℓ Φ))
        + μ * (fsqC1 (a v)) * cnPlus ℓ Φ
      ≤ kinWord N ℓ Φ := by
    have hg : (1 / (36 * ℓ ^ 2)) * cnPlus ℓ Φ ≤ kinWord N ℓ Φ :=
      kinWord_gap_cnPlus hℓ hΦc
    exact le_trans (by nlinarith [hA1, hA2a, hA2b, hlin]) hg
  -- E = kinWord + qLHS ≥ kinWord + (B0 − A) ≥ B0  (A ≤ kinWord)
  have hq' : (4 * π * (a v) / ℓ ^ 3) * ((1 / 2 : ℝ) * ((N : ℝ) - μ * ℓ ^ 3 - (1 / 2 : ℝ)) ^ 2)
        - (4 * π * (a v) / ℓ ^ 3) * (cnPlus ℓ Φ) ^ 2
        - (4 * π * (a v)) * μ ^ 2 * ℓ ^ 3 * (1 + 1 / (2 * μ * ℓ ^ 3)) ^ 2
        - (fsqC2 (a v)) * (ℓ ^ 3)⁻¹ * (3 * ((N : ℝ) * cnPlus ℓ Φ) + cS2 ℓ Φ)
        - (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * (7 * cS2 ℓ Φ + 18 * ((N : ℝ) * cnPlus ℓ Φ))
        - μ * (fsqC1 (a v)) * ((N : ℝ) + cnPlus ℓ Φ)
      ≤ qLHSword (N := N) ℓ μ (wPairC ℓ v) (wPairC ℓ (g0 v h)) Φ := by
    rwa [hmu] at hq
  nlinarith

/-- **Count-form of the condensate-pair mass**: for a NORMALISED state,
`cS2 ℓ Φ ≤ N̂²` (`cS2 ≤ N̂·cS1` and `cS1 ≤ N̂` at `∫Φ² = 1`) — the
`cS2`-condensate remainder of the count-only bound in pure count form. -/
lemma cS2_count_bound {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Φ : XN N → ℝ}
    (hΦc : Continuous Φ) (hnorm : (∫ x in abox N ℓ, (Φ x) ^ 2) = 1) :
    cS2 ℓ Φ ≤ (N : ℝ) ^ 2 := by
  have h1 := cS2_le_n_mul_cS1 hℓ hΦc
  have h2 := cS1_le_norm_sq hℓ hΦc
  have h3 : cS1 ℓ Φ ≤ (N : ℝ) := by
    calc
      cS1 ℓ Φ ≤ (N : ℝ) * (∫ x in abox N ℓ, (Φ x) ^ 2) := h2
      _ = (N : ℝ) := by rw [hnorm]; ring
  have hN : 0 ≤ (N : ℝ) := by positivity
  nlinarith

/-- **Count-only per-state bound** (from `gap_absorb_sharp`, `cS2`-remainder
in count form `≤ N̂²`): under the gap-regime hypotheses,

    E_s ≥ (4πa/ℓ³)·½·(N̂−μℓ³−½)² − 4πaμ²ℓ³(1+1/(2μℓ³))²
          − (C₂+7·C₁)·(N̂/ℓ³)²·ℓ³·?  (i.e. − (C₂+7C₁)(ℓ³)⁻¹·N̂²)
          − μ·C₁·N̂ . -/
theorem per_state_count_sharp {N : ℕ} {ℓ μ : ℝ} (hℓ : 0 < ℓ) (hμ : 0 < μ)
    {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) {Φ : XN N → ℝ} (hΦc : ContDiff ℝ ∞ Φ)
    (hnorm : (∫ x in abox N ℓ, (Φ x) ^ 2) = 1)
    {B U : ℝ}
    (hwinP : cnPlus ℓ Φ ≤ B)
    (hucap : (N : ℝ) / ℓ ^ 3 ≤ U)
    (hreg : μ * (fsqC1 (a v)) + (4 * π * (a v) / ℓ ^ 3) * B
        + (3 * (fsqC2 (a v)) + 18 * (fsqC1 (a v))) * U ≤ 1 / (36 * ℓ ^ 2)) :
    (4 * π * (a v) / ℓ ^ 3) * ((1 / 2 : ℝ) * ((N : ℝ) - μ * ℓ ^ 3 - (1 / 2 : ℝ)) ^ 2)
        - (4 * π * (a v)) * μ ^ 2 * ℓ ^ 3 * (1 + 1 / (2 * μ * ℓ ^ 3)) ^ 2
        - ((fsqC2 (a v)) + 7 * (fsqC1 (a v))) * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2
        - μ * (fsqC1 (a v)) * (N : ℝ)
      ≤ kinWord N ℓ Φ + qLHSword (N := N) ℓ μ (wPairC ℓ v) (wPairC ℓ (g0 v h)) Φ := by
  have hg := gap_absorb_sharp hℓ hμ hv_nonneg hvrad hv_memL1 hR hv_supp h hRℓ hΦc hnorm
    hwinP hucap hreg
  have hcS2 := cS2_count_bound hℓ hΦc.continuous hnorm
  have hCsum : 0 ≤ (fsqC2 (a v)) + 7 * (fsqC1 (a v)) := by
    have hav : 0 ≤ a v := (av_bounds_weak hR hv_nonneg hvrad hv_supp h).1
    have hC1nn : 0 ≤ fsqC1 (a v) := by dsimp [fsqC1]; positivity
    have hC2nn : 0 ≤ fsqC2 (a v) := by dsimp [fsqC2]; positivity
    nlinarith
  have hLinv : 0 ≤ (ℓ ^ 3)⁻¹ := by positivity
  have hN0 : 0 ≤ (N : ℝ) ^ 2 := sq_nonneg (N : ℝ)
  have hcs : - ((fsqC2 (a v)) + 7 * (fsqC1 (a v))) * (ℓ ^ 3)⁻¹ * cS2 ℓ Φ
      ≥ - ((fsqC2 (a v)) + 7 * (fsqC1 (a v))) * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 := by
    have hm := mul_le_mul_of_nonneg_left hcS2 (mul_nonneg hCsum hLinv)
    nlinarith
  nlinarith

/-- **Density-form count bound** (the A₀-pivot input): at density
`u := N̂/ℓ³` the count-form bound `per_state_count_sharp` reads

    E_s ≥ (2πa/ℓ³)·(ℓ³(u−μ) − ½)² − 4πaμ²ℓ³(1+1/(2μℓ³))²
          − (C₂+7·C₁)·u²·ℓ³ − μ·C₁·u·ℓ³ . -/
theorem per_state_u_form {N : ℕ} {ℓ μ u : ℝ} (hℓ : 0 < ℓ) (hμ : 0 < μ)
    {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) {Φ : XN N → ℝ} (hΦc : ContDiff ℝ ∞ Φ)
    (hnorm : (∫ x in abox N ℓ, (Φ x) ^ 2) = 1)
    {B U : ℝ}
    (hu : (N : ℝ) / ℓ ^ 3 = u)
    (hwinP : cnPlus ℓ Φ ≤ B)
    (hucap : (N : ℝ) / ℓ ^ 3 ≤ U)
    (hreg : μ * (fsqC1 (a v)) + (4 * π * (a v) / ℓ ^ 3) * B
        + (3 * (fsqC2 (a v)) + 18 * (fsqC1 (a v))) * U ≤ 1 / (36 * ℓ ^ 2)) :
    (2 * π * (a v) / ℓ ^ 3) * ((ℓ ^ 3 * (u - μ) - (1 / 2 : ℝ)) ^ 2)
        - (4 * π * (a v)) * μ ^ 2 * ℓ ^ 3 * (1 + 1 / (2 * μ * ℓ ^ 3)) ^ 2
        - ((fsqC2 (a v)) + 7 * (fsqC1 (a v))) * u ^ 2 * ℓ ^ 3
        - μ * (fsqC1 (a v)) * (u * ℓ ^ 3)
      ≤ kinWord N ℓ Φ + qLHSword (N := N) ℓ μ (wPairC ℓ v) (wPairC ℓ (g0 v h)) Φ := by
  have hg := per_state_count_sharp hℓ hμ hv_nonneg hvrad hv_memL1 hR hv_supp h hRℓ hΦc hnorm
    hwinP hucap hreg
  have hd : ℓ ^ 3 ≠ 0 := ne_of_gt (pow_pos hℓ 3)
  have hN : (N : ℝ) = u * ℓ ^ 3 := (div_eq_iff hd).mp hu
  have hmain : (2 * π * (a v) / ℓ ^ 3) * ((ℓ ^ 3 * (u - μ) - (1 / 2 : ℝ)) ^ 2)
      = (4 * π * (a v) / ℓ ^ 3) * ((1 / 2 : ℝ) * (((N : ℝ) - μ * ℓ ^ 3 - (1 / 2 : ℝ)) ^ 2)) := by
    rw [hN]
    ring
  rw [hmain]
  have hE1 : ((fsqC2 (a v)) + 7 * (fsqC1 (a v))) * u ^ 2 * ℓ ^ 3
      = ((fsqC2 (a v)) + 7 * (fsqC1 (a v))) * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 := by
    rw [hN]
    field_simp [hd]
  have hE2 : μ * (fsqC1 (a v)) * (u * ℓ ^ 3) = μ * (fsqC1 (a v)) * (N : ℝ) := by
    rw [hN]
  rw [hE1, hE2]
  exact hg

end BoseGases

end Submission
