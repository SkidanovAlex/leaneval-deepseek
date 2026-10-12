import ChallengeDeps
import Submission.Work.SmallBoxA0.PotSharp
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SmallBoxA0

open MeasureTheory Metric
open scoped Real
open Submission BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 4000000

/-- **The potential-side assembly (sharp form)**: `qLHSword` is at least the
block-bound main term `¼(x−μ)²·8π(av)ℓ³ − ½μ²·8π(av)ℓ³`, plus the `∬w₂`-excess
`½ℓ⁻³·D·cS2` (D := g0w0Mass), plus the `A₂ = q4PairWord` Bogolubov pairing,
minus the `n₊`-term with the explicit coefficient `potNCoeff` and the explicit
`Corr` residue of `q1_w1line_scalar_split`. -/
lemma pot_sharp_summary {N : ℕ} {ℓ μ : ℝ} (hℓ : 0 < ℓ) (hμ : 0 < μ) {v : ℝ³ → ℝ}
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) {Φ : X N → ℝ} (hΦc : Continuous Φ)
    (hnorm : (∫ x in abox N ℓ, (Φ x) ^ 2) = 1)
    (hwin : (N : ℝ) / ℓ ^ 3 ≤ 9 * μ) (hSc1 : 0 < cS1 ℓ Φ) :
    (1 / 4 : ℝ) * (((N : ℝ) / ℓ ^ 3) - μ) ^ 2 * (8 * π * (a v) * ℓ ^ 3)
      - (1 / 2 : ℝ) * μ ^ 2 * (8 * π * (a v) * ℓ ^ 3)
      + (1 / 2 : ℝ) * (ℓ ^ 3)⁻¹ * (g0w0Mass (v := v) h) * cS2 ℓ Φ
      + q4PairWord (ℓ := ℓ) (v := v) h (Φ := Φ)
      - potNCoeff μ (a v) * cnPlus ℓ Φ - 36 * π * (a v) * μ
      - 2 * (ℓ ^ 3)⁻¹ * (∑ i : Fin N, ∫ x in abox N ℓ,
          (aP ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ (g0 v h)) (x i)) *
            (∑ k : Fin N, aQ ℓ k (aQ ℓ i Φ) x))
    ≤ qLHSword (N := N) ℓ μ (wPairC ℓ v) (wPairC ℓ (g0 v h)) Φ := by
  classical
  -- ## Basic nonnegativity and window facts
  have hav : (0 : ℝ) ≤ a v := (av_bounds_weak hR hv_nonneg hvrad hv_supp h).1
  have hC1nn : (0 : ℝ) ≤ fsqC1 (a v) := by unfold fsqC1; positivity
  have hC2nn : (0 : ℝ) ≤ fsqC2 (a v) := by unfold fsqC2; positivity
  have hnn : (0 : ℝ) ≤ cnPlus ℓ Φ := cnPlus_nonneg
  have hS1nn : (0 : ℝ) ≤ cS1 ℓ Φ := cS1_nonneg
  have hwin' : (N : ℝ) * (ℓ ^ 3)⁻¹ ≤ 9 * μ := by
    simpa [div_eq_mul_inv] using hwin
  have hS : cS1 ℓ Φ = (N : ℝ) - cnPlus ℓ Φ := cS1_eq_nat_sub_cnPlus hℓ hΦc hnorm
  -- ## The two window conversions used on the `n₊`-blocks
  -- `(4·cS1/ℓ³) ≤ 36μ`  (from `cS1 ≤ N` and `N/ℓ³ ≤ 9μ`)
  have hSV : 4 * cS1 ℓ Φ / ℓ ^ 3 ≤ 36 * μ := by
    have hℓ3 : (0 : ℝ) < ℓ ^ 3 := by positivity
    have hle : 4 * cS1 ℓ Φ ≤ 4 * (N : ℝ) := by
      have := cS1_nonneg (N := N) (ℓ := ℓ) (Φ := Φ)
      linarith
    calc 4 * cS1 ℓ Φ / ℓ ^ 3 ≤ 4 * (N : ℝ) / ℓ ^ 3 :=
          div_le_div_of_nonneg_right hle (le_of_lt hℓ3)
      _ = 4 * ((N : ℝ) / ℓ ^ 3) := by ring
      _ ≤ 4 * (9 * μ) := by linarith [hwin]
      _ = 36 * μ := by ring
  -- ## The `qOneMass`-block in `n₊`-form
  have hJ1 : 4 * cS1 ℓ Φ / ℓ ^ 3 * qOneMass (ℓ := ℓ) (v := v) h (Φ := Φ)
      ≤ 36 * μ * fsqC1 (a v) * cnPlus ℓ Φ := by
    have hQ := qOneMass_le_fsqC1_mul_cnPlus (N := N) (ℓ := ℓ) (v := v)
      hℓ hv_nonneg hvrad hR hv_supp h hRℓ hΦc
    have h4S : (0 : ℝ) ≤ 4 * cS1 ℓ Φ / ℓ ^ 3 := by
      exact div_nonneg (by linarith [hS1nn]) (by positivity)
    have hstep1 : 4 * cS1 ℓ Φ / ℓ ^ 3 * qOneMass (ℓ := ℓ) (v := v) h (Φ := Φ)
        ≤ 4 * cS1 ℓ Φ / ℓ ^ 3 * (fsqC1 (a v) * cnPlus ℓ Φ) :=
      mul_le_mul_of_nonneg_left hQ h4S
    have hC1nnm : (0 : ℝ) ≤ fsqC1 (a v) * cnPlus ℓ Φ := mul_nonneg hC1nn hnn
    have hstep2 : 4 * cS1 ℓ Φ / ℓ ^ 3 * (fsqC1 (a v) * cnPlus ℓ Φ)
        ≤ 36 * μ * (fsqC1 (a v) * cnPlus ℓ Φ) :=
      mul_le_mul_of_nonneg_right hSV hC1nnm
    calc 4 * cS1 ℓ Φ / ℓ ^ 3 * qOneMass (ℓ := ℓ) (v := v) h (Φ := Φ)
        ≤ 4 * cS1 ℓ Φ / ℓ ^ 3 * (fsqC1 (a v) * cnPlus ℓ Φ) := hstep1
      _ ≤ 36 * μ * (fsqC1 (a v) * cnPlus ℓ Φ) := hstep2
      _ = 36 * μ * fsqC1 (a v) * cnPlus ℓ Φ := by ring
  -- ## The `6·C₁·ℓ⁻³·N̂·n₊`-block in `54μC₁n₊`-form
  have hJ2 : 6 * fsqC1 (a v) * (ℓ ^ 3)⁻¹ * (N : ℝ) * cnPlus ℓ Φ
      ≤ 54 * μ * fsqC1 (a v) * cnPlus ℓ Φ := by
    have hfac : (0 : ℝ) ≤ 6 * fsqC1 (a v) * cnPlus ℓ Φ := by positivity
    have hstep := mul_le_mul_of_nonneg_left hwin' hfac
    calc 6 * fsqC1 (a v) * (ℓ ^ 3)⁻¹ * (N : ℝ) * cnPlus ℓ Φ
        = 6 * fsqC1 (a v) * cnPlus ℓ Φ * ((N : ℝ) * (ℓ ^ 3)⁻¹) := by ring
      _ ≤ 6 * fsqC1 (a v) * cnPlus ℓ Φ * (9 * μ) := hstep
      _ = 54 * μ * fsqC1 (a v) * cnPlus ℓ Φ := by ring
  -- ## The `C₂·ℓ⁻³·N̂·n₊`-block in `9μC₂n₊`-form
  have hJ3 : fsqC2 (a v) * (ℓ ^ 3)⁻¹ * (N : ℝ) * cnPlus ℓ Φ
      ≤ 9 * μ * fsqC2 (a v) * cnPlus ℓ Φ := by
    have hfac : (0 : ℝ) ≤ fsqC2 (a v) * cnPlus ℓ Φ := by positivity
    have hstep := mul_le_mul_of_nonneg_left hwin' hfac
    calc fsqC2 (a v) * (ℓ ^ 3)⁻¹ * (N : ℝ) * cnPlus ℓ Φ
        = fsqC2 (a v) * cnPlus ℓ Φ * ((N : ℝ) * (ℓ ^ 3)⁻¹) := by ring
      _ ≤ fsqC2 (a v) * cnPlus ℓ Φ * (9 * μ) := hstep
      _ = 9 * μ * fsqC2 (a v) * cnPlus ℓ Φ := by ring
  -- ## The corpus ingredients
  have hq0 := q0word_sharp (N := N) (ℓ := ℓ) (μ := μ) (v := v) (R := R)
    hℓ hμ hv_nonneg hvrad hR hv_supp h hRℓ hΦc hnorm hwin
  have hq2 := q2word_sharp (N := N) (ℓ := ℓ) (μ := μ) (v := v) (R := R)
    hℓ (le_of_lt hμ) hv_nonneg hvrad hv_memL1 hR hv_supp h hRℓ hΦc
  have h134 := q1_q3_q4_mass (N := N) (ℓ := ℓ) (μ := μ) (v := v) (R := R)
    hℓ hv_nonneg hvrad hR hv_supp h hRℓ hv_memL1 hΦc
  have hsplit := q1_w1line_scalar_split (N := N) (ℓ := ℓ) (μ := μ) (v := v) (R := R)
    hℓ hv_nonneg hvrad hR hv_supp h hRℓ hΦc
  have hcs := q1_cross_w1_cs_fs (N := N) (ℓ := ℓ) (t := (N : ℝ) / ℓ ^ 3 - μ)
    (v := v) (R := R) hℓ hv_nonneg hvrad hv_memL1 hR hv_supp h hRℓ hΦc hSc1
  have hpot := qLHSword_a0_w2_form (N := N) (ℓ := ℓ) (μ := μ) (v := v) (R := R)
    hℓ hv_nonneg hvrad hv_memL1 hR hv_supp h hRℓ hΦc
  have hq0w := q0word_w2_mass_sub (N := N) (v := v) (R := R) (ℓ := ℓ)
    hR hv_nonneg hvrad hv_supp h hℓ hRℓ μ hΦc
  -- ## Assembly
  rw [← hq0w] at hpot
  rw [hsplit] at h134
  rw [hpot]
  simp only [potNCoeff]
  linarith [hq0, hq2, h134, hcs, hJ1, hJ2, hJ3]

end Work.SmallBoxA0
